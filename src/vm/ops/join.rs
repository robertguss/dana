//! Vectorized Hash Join for all 7 Dana join kinds (`InnerOne`, `InnerManyToOne`,
//! `InnerMany`, `LeftOne`, `LeftManyToOne`, `Semi`, `Anti`) with:
//! - O(N) hash-indexed cardinality verification preserving exact earliest `(i1, i2)`
//!   redacted diagnostics matching `Eval.lean` / `src/oracle/eval.rs`
//! - Zero-allocation columnar key probing, specialized non-null `Int` hash index,
//!   direct columnar batch gather (zero `TableRow` / `Val` boxing), and parallel
//!   left-batch probing via `std::thread::scope`.

use std::collections::{HashMap, HashSet};
use std::hash::BuildHasherDefault;

use crate::core::check::{build_joined_cols, resolve_join_pairs};
use crate::core::syntax::{BugKind, ColSpec, Ident, JoinKind, JoinOn, Suffixes, TableTy, TagSet};
use crate::oracle::value::{Bug, Val, format_diag_detail};
use crate::vm::batch::{Batch, Column, ColumnData, NullBitmap};
use crate::vm::key::{FastHasher, eq_col_cells, hash_row_key};
use crate::vm::ops::{OpErr, OpExecConfig, VmMode, VmTable};
use crate::vm::parallel::parallel_map_ref;

type FastMap<K, V> = HashMap<K, V, BuildHasherDefault<FastHasher>>;
type FastSet<K> = HashSet<K, BuildHasherDefault<FastHasher>>;

/// Compact coordinate pointing to a single row in a `Vec<Batch>`.
#[derive(Clone, Copy, Debug)]
struct RowRef {
    batch_idx: u32,
    row_idx: u16,
    global_idx: usize,
}

/// Right-side hash index with a zero-overhead specialization for single non-null `Int` keys.
enum RightIndex {
    /// Single non-null `Int` join key where `check_right_unique` applies (e.g., `InnerManyToOne`,
    /// `LeftManyToOne`, `InnerOne`, `LeftOne`, or `Semi`/`Anti`). Avoids `Vec<RowRef>` per key.
    SingleIntUnique {
        map: FastMap<i64, RowRef>,
        dup_keys: FastSet<i64>,
    },
    /// General composite / multi-match / nullable hash index.
    Generic(FastMap<u64, Vec<RowRef>>),
}

/// O(N) duplicate-key detector over columnar batches that returns the **exact**
/// duplicate pair `(i1, i2)` with minimum `i1` (and minimum `i2 > i1`), matching
/// `src/oracle/eval.rs:check_unique_join_keys` byte-for-byte!
fn check_unique_keys_columnar(
    batches: &[Batch],
    key_idxs: &[usize],
    key_tags: &TagSet,
) -> Option<Bug> {
    let mut table: FastMap<u64, Vec<RowRef>> = FastMap::default();
    let mut best_dup: Option<(usize, usize, RowRef)> = None;
    let mut recorded_first: FastSet<usize> = FastSet::default();

    let mut global_idx = 0usize;
    for (bi, b) in batches.iter().enumerate() {
        let active = b.active_indices();
        for &r_u16 in &active {
            let ri = usize::from(r_u16);
            let h = hash_row_key(&b.cols, key_idxs, ri);
            let bucket = table.entry(h).or_default();
            let mut found_first: Option<RowRef> = None;
            for &prev in bucket.iter() {
                let pb = &batches[prev.batch_idx as usize];
                let pri = usize::from(prev.row_idx);
                if key_idxs
                    .iter()
                    .all(|&ki| eq_col_cells(&pb.cols[ki], pri, &b.cols[ki], ri))
                {
                    found_first = Some(prev);
                    break;
                }
            }
            if let Some(prev) = found_first {
                if recorded_first.insert(prev.global_idx) {
                    let is_better = match best_dup {
                        None => true,
                        Some((best_i1, _, _)) => prev.global_idx < best_i1,
                    };
                    if is_better {
                        best_dup = Some((prev.global_idx, global_idx, prev));
                    }
                }
            } else {
                bucket.push(RowRef {
                    batch_idx: bi as u32,
                    row_idx: r_u16,
                    global_idx,
                });
            }
            global_idx += 1;
        }
    }

    let (i1, i2, rref) = best_dup?;
    let b = &batches[rref.batch_idx as usize];
    let ri = usize::from(rref.row_idx);
    let key_val = if key_idxs.len() == 1 {
        b.cols[key_idxs[0]].get_val(ri)
    } else {
        Val::Tuple(key_idxs.iter().map(|&ki| b.cols[ki].get_val(ri)).collect())
    };
    let rendered_key = format_diag_detail(key_tags, &key_val);
    Some(Bug {
        kind: BugKind::JoinCardinality,
        message: format!("duplicate key {rendered_key} (2 rows: {i1}, {i2})"),
    })
}

fn is_single_non_null_int_col(batches: &[Batch], col_idx: usize) -> bool {
    batches.iter().all(|b| {
        if b.is_empty() {
            return true;
        }
        let c = &b.cols[col_idx];
        c.validity.is_none() && matches!(c.data, ColumnData::Int(_))
    })
}

/// Build an immutable hash index over right batches, specializing single non-null `Int` keys
/// when at most one right match is needed per key.
fn build_right_index(
    right_batches: &[Batch],
    r_key_idxs: &[usize],
    single_match_only: bool,
) -> RightIndex {
    let total_r: usize = right_batches.iter().map(Batch::active_len).sum();
    if single_match_only
        && r_key_idxs.len() == 1
        && is_single_non_null_int_col(right_batches, r_key_idxs[0])
    {
        let rki = r_key_idxs[0];
        let mut map: FastMap<i64, RowRef> =
            FastMap::with_capacity_and_hasher(total_r, BuildHasherDefault::default());
        let mut dup_keys: FastSet<i64> = FastSet::default();
        let mut global_idx = 0usize;
        for (bi, b) in right_batches.iter().enumerate() {
            if b.is_empty() {
                continue;
            }
            if let ColumnData::Int(vals) = &b.cols[rki].data {
                match &b.selection {
                    None => {
                        for (ri, &k) in vals.iter().enumerate().take(b.len) {
                            let rr = RowRef {
                                batch_idx: bi as u32,
                                row_idx: ri as u16,
                                global_idx,
                            };
                            if map.insert(k, rr).is_some() {
                                dup_keys.insert(k);
                            }
                            global_idx += 1;
                        }
                    }
                    Some(sel) => {
                        for &r_u16 in sel {
                            let k = vals[usize::from(r_u16)];
                            let rr = RowRef {
                                batch_idx: bi as u32,
                                row_idx: r_u16,
                                global_idx,
                            };
                            if map.insert(k, rr).is_some() {
                                dup_keys.insert(k);
                            }
                            global_idx += 1;
                        }
                    }
                }
            }
        }
        return RightIndex::SingleIntUnique { map, dup_keys };
    }

    let mut index: FastMap<u64, Vec<RowRef>> =
        FastMap::with_capacity_and_hasher(total_r, BuildHasherDefault::default());
    let mut global_idx = 0usize;
    for (bi, b) in right_batches.iter().enumerate() {
        let active = b.active_indices();
        for &r_u16 in &active {
            let ri = usize::from(r_u16);
            let h = hash_row_key(&b.cols, r_key_idxs, ri);
            index.entry(h).or_default().push(RowRef {
                batch_idx: bi as u32,
                row_idx: r_u16,
                global_idx,
            });
            global_idx += 1;
        }
    }
    RightIndex::Generic(index)
}

fn wrap_opt_core(r_spec: &ColSpec, v: Val) -> Val {
    if r_spec.ty.is_option() {
        v
    } else {
        Val::OptSome(Box::new(v))
    }
}

fn wrap_opt_exec(v: Val) -> Val {
    match v {
        Val::OptNone | Val::OptSome(_) => v,
        other => Val::OptSome(Box::new(other)),
    }
}

/// Columnar right-side gather directly from `right_batches` into a single [`Column`]
/// with zero `Val` boxing for all primitive, decimal, float, temporal, text, and bytes columns.
fn gather_right_column(
    right_batches: &[Batch],
    right_col_spec: &ColSpec,
    rk_idx: usize,
    out_spec: ColSpec,
    r_refs: &[Option<RowRef>],
    is_left_outer: bool,
    is_core: bool,
) -> Column {
    let n = r_refs.len();
    if n == 0 {
        return Column::from_vals(out_spec, &[]);
    }

    // Find the first referenced right batch to determine uniform physical layout.
    let first_non_empty = right_batches.iter().find(|b| !b.is_empty());
    let Some(sample_b) = first_non_empty else {
        // Right side was empty (all `r_refs` are `None` for left outer join).
        let vals = vec![Val::OptNone; n];
        return Column::from_vals(out_spec, &vals);
    };
    let sample_col = &sample_b.cols[rk_idx];
    let sample_has_validity = sample_col.validity.is_some();
    let sample_disc = std::mem::discriminant(&sample_col.data);
    let uniform_typed = !matches!(
        sample_col.data,
        ColumnData::Generic(_) | ColumnData::Unit(_)
    ) && right_batches.iter().all(|b| {
        if b.is_empty() {
            return true;
        }
        let c = &b.cols[rk_idx];
        c.validity.is_some() == sample_has_validity
            && std::mem::discriminant(&c.data) == sample_disc
    });

    if !uniform_typed {
        let mut vals = Vec::with_capacity(n);
        for rr_opt in r_refs {
            match rr_opt {
                None => vals.push(Val::OptNone),
                Some(rr) => {
                    let v = right_batches[rr.batch_idx as usize].cols[rk_idx]
                        .get_val(usize::from(rr.row_idx));
                    vals.push(if is_left_outer {
                        if is_core {
                            wrap_opt_core(right_col_spec, v)
                        } else {
                            wrap_opt_exec(v)
                        }
                    } else {
                        v
                    });
                }
            }
        }
        return Column::from_vals(out_spec, &vals);
    }

    let need_validity = sample_has_validity || is_left_outer;
    let mut out_bm = if need_validity {
        Some(NullBitmap::with_capacity(n))
    } else {
        None
    };

    // Macro-free typed gather across uniform `ColumnData` variants.
    let data = match &sample_col.data {
        ColumnData::Bool(_) => {
            let mut out = Vec::with_capacity(n);
            for rr_opt in r_refs {
                match rr_opt {
                    None => {
                        if let Some(bm) = &mut out_bm {
                            bm.push(false);
                        }
                        out.push(0);
                    }
                    Some(rr) => {
                        let c = &right_batches[rr.batch_idx as usize].cols[rk_idx];
                        let r = usize::from(rr.row_idx);
                        if let Some(bm) = &mut out_bm {
                            bm.push(c.validity.as_ref().is_none_or(|rbm| rbm.is_valid(r)));
                        }
                        if let ColumnData::Bool(vs) = &c.data {
                            out.push(vs[r]);
                        }
                    }
                }
            }
            ColumnData::Bool(out)
        }
        ColumnData::Int(_) => {
            let mut out = Vec::with_capacity(n);
            for rr_opt in r_refs {
                match rr_opt {
                    None => {
                        if let Some(bm) = &mut out_bm {
                            bm.push(false);
                        }
                        out.push(0);
                    }
                    Some(rr) => {
                        let c = &right_batches[rr.batch_idx as usize].cols[rk_idx];
                        let r = usize::from(rr.row_idx);
                        if let Some(bm) = &mut out_bm {
                            bm.push(c.validity.as_ref().is_none_or(|rbm| rbm.is_valid(r)));
                        }
                        if let ColumnData::Int(vs) = &c.data {
                            out.push(vs[r]);
                        }
                    }
                }
            }
            ColumnData::Int(out)
        }
        ColumnData::Decimal(_) => {
            let mut out = Vec::with_capacity(n);
            for rr_opt in r_refs {
                match rr_opt {
                    None => {
                        if let Some(bm) = &mut out_bm {
                            bm.push(false);
                        }
                        out.push(0);
                    }
                    Some(rr) => {
                        let c = &right_batches[rr.batch_idx as usize].cols[rk_idx];
                        let r = usize::from(rr.row_idx);
                        if let Some(bm) = &mut out_bm {
                            bm.push(c.validity.as_ref().is_none_or(|rbm| rbm.is_valid(r)));
                        }
                        if let ColumnData::Decimal(vs) = &c.data {
                            out.push(vs[r]);
                        }
                    }
                }
            }
            ColumnData::Decimal(out)
        }
        ColumnData::Float(_) => {
            let mut out = Vec::with_capacity(n);
            for rr_opt in r_refs {
                match rr_opt {
                    None => {
                        if let Some(bm) = &mut out_bm {
                            bm.push(false);
                        }
                        out.push(0);
                    }
                    Some(rr) => {
                        let c = &right_batches[rr.batch_idx as usize].cols[rk_idx];
                        let r = usize::from(rr.row_idx);
                        if let Some(bm) = &mut out_bm {
                            bm.push(c.validity.as_ref().is_none_or(|rbm| rbm.is_valid(r)));
                        }
                        if let ColumnData::Float(vs) = &c.data {
                            out.push(vs[r]);
                        }
                    }
                }
            }
            ColumnData::Float(out)
        }
        ColumnData::Date(_) => {
            let mut out = Vec::with_capacity(n);
            for rr_opt in r_refs {
                match rr_opt {
                    None => {
                        if let Some(bm) = &mut out_bm {
                            bm.push(false);
                        }
                        out.push(0);
                    }
                    Some(rr) => {
                        let c = &right_batches[rr.batch_idx as usize].cols[rk_idx];
                        let r = usize::from(rr.row_idx);
                        if let Some(bm) = &mut out_bm {
                            bm.push(c.validity.as_ref().is_none_or(|rbm| rbm.is_valid(r)));
                        }
                        if let ColumnData::Date(vs) = &c.data {
                            out.push(vs[r]);
                        }
                    }
                }
            }
            ColumnData::Date(out)
        }
        ColumnData::Timestamp(_) => {
            let mut out = Vec::with_capacity(n);
            for rr_opt in r_refs {
                match rr_opt {
                    None => {
                        if let Some(bm) = &mut out_bm {
                            bm.push(false);
                        }
                        out.push(0);
                    }
                    Some(rr) => {
                        let c = &right_batches[rr.batch_idx as usize].cols[rk_idx];
                        let r = usize::from(rr.row_idx);
                        if let Some(bm) = &mut out_bm {
                            bm.push(c.validity.as_ref().is_none_or(|rbm| rbm.is_valid(r)));
                        }
                        if let ColumnData::Timestamp(vs) = &c.data {
                            out.push(vs[r]);
                        }
                    }
                }
            }
            ColumnData::Timestamp(out)
        }
        ColumnData::Duration(_) => {
            let mut out = Vec::with_capacity(n);
            for rr_opt in r_refs {
                match rr_opt {
                    None => {
                        if let Some(bm) = &mut out_bm {
                            bm.push(false);
                        }
                        out.push(0);
                    }
                    Some(rr) => {
                        let c = &right_batches[rr.batch_idx as usize].cols[rk_idx];
                        let r = usize::from(rr.row_idx);
                        if let Some(bm) = &mut out_bm {
                            bm.push(c.validity.as_ref().is_none_or(|rbm| rbm.is_valid(r)));
                        }
                        if let ColumnData::Duration(vs) = &c.data {
                            out.push(vs[r]);
                        }
                    }
                }
            }
            ColumnData::Duration(out)
        }
        ColumnData::Text { .. } => {
            let mut offsets = Vec::with_capacity(n + 1);
            let mut buf = Vec::with_capacity(n * 8);
            offsets.push(0);
            for rr_opt in r_refs {
                match rr_opt {
                    None => {
                        if let Some(bm) = &mut out_bm {
                            bm.push(false);
                        }
                        offsets.push(buf.len());
                    }
                    Some(rr) => {
                        let c = &right_batches[rr.batch_idx as usize].cols[rk_idx];
                        let r = usize::from(rr.row_idx);
                        let valid = c.validity.as_ref().is_none_or(|rbm| rbm.is_valid(r));
                        if let Some(bm) = &mut out_bm {
                            bm.push(valid);
                        }
                        if valid && let ColumnData::Text { offsets: ro, data } = &c.data {
                            buf.extend_from_slice(&data[ro[r]..ro[r + 1]]);
                        }
                        offsets.push(buf.len());
                    }
                }
            }
            ColumnData::Text { offsets, data: buf }
        }
        ColumnData::Bytes { .. } => {
            let mut offsets = Vec::with_capacity(n + 1);
            let mut buf = Vec::with_capacity(n * 8);
            offsets.push(0);
            for rr_opt in r_refs {
                match rr_opt {
                    None => {
                        if let Some(bm) = &mut out_bm {
                            bm.push(false);
                        }
                        offsets.push(buf.len());
                    }
                    Some(rr) => {
                        let c = &right_batches[rr.batch_idx as usize].cols[rk_idx];
                        let r = usize::from(rr.row_idx);
                        let valid = c.validity.as_ref().is_none_or(|rbm| rbm.is_valid(r));
                        if let Some(bm) = &mut out_bm {
                            bm.push(valid);
                        }
                        if valid && let ColumnData::Bytes { offsets: ro, data } = &c.data {
                            buf.extend_from_slice(&data[ro[r]..ro[r + 1]]);
                        }
                        offsets.push(buf.len());
                    }
                }
            }
            ColumnData::Bytes { offsets, data: buf }
        }
        ColumnData::Unit(_) | ColumnData::Generic(_) => ColumnData::Unit(n),
    };

    Column {
        spec: out_spec,
        data,
        validity: out_bm,
    }
}

/// Build one or more `batch_size`-capped columnar [`Batch`]es from left selection indices and
/// corresponding matched right [`RowRef`] coordinates without boxing any [`Val`].
#[expect(
    clippy::too_many_arguments,
    reason = "Columnar join batch gather avoids per-row TableRow/Val materialization"
)]
fn gather_joined_batches(
    lb: &Batch,
    right: &VmTable,
    r_keep_idxs: &[usize],
    out_cols: &[ColSpec],
    l_sel: &[u16],
    r_refs: &[Option<RowRef>],
    is_identity_left: bool,
    is_left_outer: bool,
    is_core: bool,
    batch_size: usize,
) -> Vec<Batch> {
    if l_sel.is_empty() {
        return Vec::new();
    }
    let chunk_cap = batch_size.max(1);
    let mut out_batches = Vec::with_capacity(l_sel.len().div_ceil(chunk_cap));
    let l_ncols = lb.cols.len();
    let total_ncols = l_ncols + r_keep_idxs.len();

    let mut pos = 0usize;
    while pos < l_sel.len() {
        let end = (pos + chunk_cap).min(l_sel.len());
        let l_chunk = &l_sel[pos..end];
        let r_chunk = &r_refs[pos..end];
        let whole_identity = is_identity_left && pos == 0 && end == l_sel.len();

        let mut cols = Vec::with_capacity(total_ncols);
        for (ci, out_spec) in out_cols.iter().enumerate().take(l_ncols) {
            let mut col = if whole_identity {
                lb.cols[ci].clone()
            } else {
                lb.cols[ci].select(l_chunk)
            };
            col.spec = out_spec.clone();
            cols.push(col);
        }
        for (ri_pos, &rk_idx) in r_keep_idxs.iter().enumerate() {
            let out_spec = out_cols[l_ncols + ri_pos].clone();
            cols.push(gather_right_column(
                &right.batches,
                &right.cols[rk_idx],
                rk_idx,
                out_spec,
                r_chunk,
                is_left_outer,
                is_core,
            ));
        }
        out_batches.push(Batch {
            cols,
            len: l_chunk.len(),
            selection: None,
            group_meta: None,
        });
        pos = end;
    }
    out_batches
}

/// Execute a vectorized Hash Join over two borrowed [`VmTable`]s.
pub fn op_hash_join(
    kind: JoinKind,
    left: &VmTable,
    right: &VmTable,
    on: &JoinOn,
    suffixes: &Suffixes,
    pc: &TagSet,
    cfg: &OpExecConfig,
) -> Result<VmTable, OpErr> {
    if cfg.mode == VmMode::CoreV01 {
        op_hash_join_core(kind, left, right, on, suffixes, pc, cfg)
    } else {
        op_hash_join_exec(kind, left, right, on, suffixes, cfg)
    }
}

fn op_hash_join_core(
    kind: JoinKind,
    left: &VmTable,
    right: &VmTable,
    on: &JoinOn,
    suffixes: &Suffixes,
    pc: &TagSet,
    cfg: &OpExecConfig,
) -> Result<VmTable, OpErr> {
    let l_tt = TableTy {
        cols: left.cols.clone(),
        ..TableTy::default()
    };
    let r_tt = TableTy {
        cols: right.cols.clone(),
        ..TableTy::default()
    };
    let (Ok(key_pairs), Ok(out_cols)) = (
        resolve_join_pairs(&l_tt, &r_tt, on),
        build_joined_cols(kind, &left.cols, &right.cols, on, suffixes),
    ) else {
        return Err(OpErr::Wrong);
    };

    let mut l_key_idxs = Vec::with_capacity(key_pairs.len());
    let mut r_key_idxs = Vec::with_capacity(key_pairs.len());
    for (lc, rc) in &key_pairs {
        l_key_idxs.push(left.find_col_idx(&lc.name).ok_or(OpErr::Wrong)?);
        r_key_idxs.push(right.find_col_idx(&rc.name).ok_or(OpErr::Wrong)?);
    }

    let key_tags =
        TagSet::union_owned(key_pairs.iter().map(|(lc, rc)| lc.tags.union(&rc.tags))).union(pc);

    // Upfront uniqueness checks (exact match with `src/oracle/eval.rs:check_unique_join_keys`).
    if matches!(kind, JoinKind::InnerOne | JoinKind::LeftOne)
        && let Some(bug) = check_unique_keys_columnar(&left.batches, &l_key_idxs, &key_tags)
    {
        return Err(OpErr::Stopped(bug));
    }
    let single_match_right = matches!(
        kind,
        JoinKind::InnerOne
            | JoinKind::LeftOne
            | JoinKind::InnerManyToOne
            | JoinKind::LeftManyToOne
            | JoinKind::Semi
            | JoinKind::Anti
    );
    if matches!(
        kind,
        JoinKind::InnerOne | JoinKind::LeftOne | JoinKind::InnerManyToOne | JoinKind::LeftManyToOne
    ) && let Some(bug) = check_unique_keys_columnar(&right.batches, &r_key_idxs, &key_tags)
    {
        return Err(OpErr::Stopped(bug));
    }

    let right_index = build_right_index(&right.batches, &r_key_idxs, single_match_right);
    let same_keys: &[Ident] = match on {
        JoinOn::SameKeys(ks) => ks,
        JoinOn::Pairs(_) => &[],
    };
    let r_keep_idxs: Vec<usize> = right
        .cols
        .iter()
        .enumerate()
        .filter(|(_, rc)| !same_keys.contains(&rc.name))
        .map(|(i, _)| i)
        .collect();
    let is_left_outer = matches!(kind, JoinKind::LeftOne | JoinKind::LeftManyToOne);
    let total_left = left.total_rows();
    let batch_size = cfg.batch_size;

    let probed_batches: Vec<Vec<Batch>> = parallel_map_ref(
        &left.batches,
        total_left,
        cfg.parallel_threshold_rows,
        cfg.max_threads,
        |lb| -> Result<Vec<Batch>, OpErr> {
            let active = lb.active_indices();
            if active.is_empty() {
                return Ok(Vec::new());
            }
            if matches!(kind, JoinKind::Semi | JoinKind::Anti) {
                let mut kept_sel = Vec::with_capacity(active.len());
                match &right_index {
                    RightIndex::SingleIntUnique { map, .. }
                        if l_key_idxs.len() == 1
                            && lb.cols[l_key_idxs[0]].validity.is_none()
                            && matches!(lb.cols[l_key_idxs[0]].data, ColumnData::Int(_)) =>
                    {
                        if let ColumnData::Int(lvals) = &lb.cols[l_key_idxs[0]].data {
                            for &l_u16 in &active {
                                let matched = map.contains_key(&lvals[usize::from(l_u16)]);
                                if (kind == JoinKind::Semi && matched)
                                    || (kind == JoinKind::Anti && !matched)
                                {
                                    kept_sel.push(l_u16);
                                }
                            }
                        }
                    }
                    RightIndex::SingleIntUnique { map, .. } => {
                        for &l_u16 in &active {
                            let lri = usize::from(l_u16);
                            let matched = match lb.cols[l_key_idxs[0]].get_val(lri) {
                                Val::Int(ref n) => n.to_i64().is_some_and(|k| map.contains_key(&k)),
                                _ => false,
                            };
                            if (kind == JoinKind::Semi && matched)
                                || (kind == JoinKind::Anti && !matched)
                            {
                                kept_sel.push(l_u16);
                            }
                        }
                    }
                    RightIndex::Generic(index) => {
                        for &l_u16 in &active {
                            let lri = usize::from(l_u16);
                            let h = hash_row_key(&lb.cols, &l_key_idxs, lri);
                            let matched = index.get(&h).is_some_and(|cands| {
                                cands.iter().any(|rr| {
                                    let rb = &right.batches[rr.batch_idx as usize];
                                    let rri = usize::from(rr.row_idx);
                                    l_key_idxs.iter().zip(&r_key_idxs).all(|(&lk, &rk)| {
                                        eq_col_cells(&lb.cols[lk], lri, &rb.cols[rk], rri)
                                    })
                                })
                            });
                            if (kind == JoinKind::Semi && matched)
                                || (kind == JoinKind::Anti && !matched)
                            {
                                kept_sel.push(l_u16);
                            }
                        }
                    }
                }
                if kept_sel.is_empty() {
                    return Ok(Vec::new());
                }
                let mut out_b = Batch {
                    cols: lb.cols.clone(),
                    len: lb.len,
                    selection: Some(kept_sel),
                    group_meta: None,
                }
                .compact();
                for (c, spec) in out_b.cols.iter_mut().zip(&out_cols) {
                    c.spec = spec.clone();
                }
                return Ok(vec![out_b]);
            }

            let mut l_sel: Vec<u16> = Vec::with_capacity(active.len());
            let mut r_refs: Vec<Option<RowRef>> = Vec::with_capacity(active.len());
            let mut is_identity = lb.selection.is_none();

            match &right_index {
                RightIndex::SingleIntUnique { map, .. }
                    if l_key_idxs.len() == 1
                        && lb.cols[l_key_idxs[0]].validity.is_none()
                        && matches!(lb.cols[l_key_idxs[0]].data, ColumnData::Int(_)) =>
                {
                    if let ColumnData::Int(lvals) = &lb.cols[l_key_idxs[0]].data {
                        for &l_u16 in &active {
                            let k = lvals[usize::from(l_u16)];
                            if let Some(&rr) = map.get(&k) {
                                if l_sel.len() != usize::from(l_u16) {
                                    is_identity = false;
                                }
                                l_sel.push(l_u16);
                                r_refs.push(Some(rr));
                            } else if is_left_outer {
                                if l_sel.len() != usize::from(l_u16) {
                                    is_identity = false;
                                }
                                l_sel.push(l_u16);
                                r_refs.push(None);
                            } else {
                                is_identity = false;
                            }
                        }
                    }
                }
                RightIndex::SingleIntUnique { map, .. } => {
                    for &l_u16 in &active {
                        let lri = usize::from(l_u16);
                        let hit = match lb.cols[l_key_idxs[0]].get_val(lri) {
                            Val::Int(ref n) => n.to_i64().and_then(|k| map.get(&k).copied()),
                            _ => None,
                        };
                        if let Some(rr) = hit {
                            if l_sel.len() != lri {
                                is_identity = false;
                            }
                            l_sel.push(l_u16);
                            r_refs.push(Some(rr));
                        } else if is_left_outer {
                            if l_sel.len() != lri {
                                is_identity = false;
                            }
                            l_sel.push(l_u16);
                            r_refs.push(None);
                        } else {
                            is_identity = false;
                        }
                    }
                }
                RightIndex::Generic(index) => {
                    for &l_u16 in &active {
                        let lri = usize::from(l_u16);
                        let h = hash_row_key(&lb.cols, &l_key_idxs, lri);
                        let mut matched_any = false;
                        if let Some(cands) = index.get(&h) {
                            for &rr in cands {
                                let rb = &right.batches[rr.batch_idx as usize];
                                let rri = usize::from(rr.row_idx);
                                let is_eq = l_key_idxs.iter().zip(&r_key_idxs).all(|(&lk, &rk)| {
                                    eq_col_cells(&lb.cols[lk], lri, &rb.cols[rk], rri)
                                });
                                if is_eq {
                                    matched_any = true;
                                    if l_sel.len() != lri {
                                        is_identity = false;
                                    }
                                    l_sel.push(l_u16);
                                    r_refs.push(Some(rr));
                                }
                            }
                        }
                        if !matched_any {
                            if is_left_outer {
                                if l_sel.len() != lri {
                                    is_identity = false;
                                }
                                l_sel.push(l_u16);
                                r_refs.push(None);
                            } else {
                                is_identity = false;
                            }
                        }
                    }
                }
            }
            if l_sel.len() != lb.len {
                is_identity = false;
            }
            Ok(gather_joined_batches(
                lb,
                right,
                &r_keep_idxs,
                &out_cols,
                &l_sel,
                &r_refs,
                is_identity,
                is_left_outer,
                true,
                batch_size,
            ))
        },
    )?;

    let batches = probed_batches.into_iter().flatten().collect();
    Ok(VmTable {
        cols: out_cols,
        batches,
    })
}

fn op_hash_join_exec(
    kind: JoinKind,
    left: &VmTable,
    right: &VmTable,
    on: &JoinOn,
    suffixes: &Suffixes,
    cfg: &OpExecConfig,
) -> Result<VmTable, OpErr> {
    let pairs: Vec<(usize, usize)> = match on {
        JoinOn::SameKeys(ks) => ks
            .iter()
            .filter_map(|k| Some((left.find_col_idx(k)?, right.find_col_idx(k)?)))
            .collect(),
        JoinOn::Pairs(ps) => ps
            .iter()
            .filter_map(|(lk, rk)| Some((left.find_col_idx(lk)?, right.find_col_idx(rk)?)))
            .collect(),
    };
    let l_key_idxs: Vec<usize> = pairs.iter().map(|&(l, _)| l).collect();
    let r_key_idxs: Vec<usize> = pairs.iter().map(|&(_, r)| r).collect();
    let single_match_right = !matches!(kind, JoinKind::InnerMany);
    let right_index = build_right_index(&right.batches, &r_key_idxs, single_match_right);

    if matches!(kind, JoinKind::Semi | JoinKind::Anti) {
        let out_cols = left.cols.clone();
        let total_left = left.total_rows();
        let probed: Vec<Option<Batch>> = parallel_map_ref(
            &left.batches,
            total_left,
            cfg.parallel_threshold_rows,
            cfg.max_threads,
            |lb| -> Result<Option<Batch>, OpErr> {
                let active = lb.active_indices();
                let mut kept = Vec::with_capacity(active.len());
                match &right_index {
                    RightIndex::SingleIntUnique { map, .. }
                        if l_key_idxs.len() == 1
                            && lb.cols[l_key_idxs[0]].validity.is_none()
                            && matches!(lb.cols[l_key_idxs[0]].data, ColumnData::Int(_)) =>
                    {
                        if let ColumnData::Int(lvals) = &lb.cols[l_key_idxs[0]].data {
                            for &l_u16 in &active {
                                let matched = map.contains_key(&lvals[usize::from(l_u16)]);
                                if (kind == JoinKind::Semi && matched)
                                    || (kind == JoinKind::Anti && !matched)
                                {
                                    kept.push(l_u16);
                                }
                            }
                        }
                    }
                    RightIndex::SingleIntUnique { map, .. } => {
                        for &l_u16 in &active {
                            let lri = usize::from(l_u16);
                            let matched = match lb.cols[l_key_idxs[0]].get_val(lri) {
                                Val::Int(ref n) => n.to_i64().is_some_and(|k| map.contains_key(&k)),
                                _ => false,
                            };
                            if (kind == JoinKind::Semi && matched)
                                || (kind == JoinKind::Anti && !matched)
                            {
                                kept.push(l_u16);
                            }
                        }
                    }
                    RightIndex::Generic(index) => {
                        for &l_u16 in &active {
                            let lri = usize::from(l_u16);
                            let h = hash_row_key(&lb.cols, &l_key_idxs, lri);
                            let matched = index.get(&h).is_some_and(|cands| {
                                cands.iter().any(|rr| {
                                    let rb = &right.batches[rr.batch_idx as usize];
                                    let rri = usize::from(rr.row_idx);
                                    l_key_idxs.iter().zip(&r_key_idxs).all(|(&lk, &rk)| {
                                        eq_col_cells(&lb.cols[lk], lri, &rb.cols[rk], rri)
                                    })
                                })
                            });
                            if (kind == JoinKind::Semi && matched)
                                || (kind == JoinKind::Anti && !matched)
                            {
                                kept.push(l_u16);
                            }
                        }
                    }
                }
                if kept.is_empty() {
                    Ok(None)
                } else {
                    Ok(Some(
                        Batch {
                            cols: lb.cols.clone(),
                            len: lb.len,
                            selection: Some(kept),
                            group_meta: lb.group_meta.clone(),
                        }
                        .compact(),
                    ))
                }
            },
        )?;
        return Ok(VmTable {
            cols: out_cols,
            batches: probed.into_iter().flatten().collect(),
        });
    }

    let is_left = matches!(kind, JoinKind::LeftOne | JoinKind::LeftManyToOne);
    let check_right_unique = matches!(
        kind,
        JoinKind::InnerOne | JoinKind::InnerManyToOne | JoinKind::LeftOne | JoinKind::LeftManyToOne
    );
    let check_left_unique = matches!(kind, JoinKind::InnerOne | JoinKind::LeftOne);

    let right_skip: Vec<usize> = match on {
        JoinOn::SameKeys(ks) => ks.iter().filter_map(|k| right.find_col_idx(k)).collect(),
        JoinOn::Pairs(_) => Vec::new(),
    };
    let left_names: HashSet<&str> = left.cols.iter().map(|c| c.name.as_str()).collect();
    let mut out_cols = Vec::new();
    for lc in &left.cols {
        let mut c = lc.clone();
        let collides = right
            .cols
            .iter()
            .enumerate()
            .any(|(ri, rc)| !right_skip.contains(&ri) && rc.name == c.name);
        if collides && let Some((ls, _)) = suffixes {
            c.name.push_str(ls);
        }
        out_cols.push(c);
    }
    let mut right_keep = Vec::new();
    for (ri, rc) in right.cols.iter().enumerate() {
        if right_skip.contains(&ri) {
            continue;
        }
        right_keep.push(ri);
        let mut c = rc.clone();
        if is_left {
            c.ty = crate::core::check::ensure_option_scalar(&c.ty);
        }
        if left_names.contains(c.name.as_str())
            && let Some((_, rs)) = suffixes
        {
            c.name.push_str(rs);
        }
        out_cols.push(c);
    }

    let batch_size = cfg.batch_size;

    // For `InnerOne`/`LeftOne`, track matched right row global indices to enforce 1:1.
    if check_left_unique {
        let mut matched_right_globals: FastSet<usize> = FastSet::default();
        let mut out_batches = Vec::new();
        for lb in &left.batches {
            let active = lb.active_indices();
            let mut l_sel = Vec::with_capacity(active.len());
            let mut r_refs = Vec::with_capacity(active.len());
            let mut is_identity = lb.selection.is_none();

            for &l_u16 in &active {
                let lri = usize::from(l_u16);
                let found: Option<RowRef> = match &right_index {
                    RightIndex::SingleIntUnique { map, dup_keys } => {
                        let key_opt = if lb.cols[l_key_idxs[0]].validity.is_none()
                            && let ColumnData::Int(lvals) = &lb.cols[l_key_idxs[0]].data
                        {
                            Some(lvals[lri])
                        } else if let Val::Int(ref n) = lb.cols[l_key_idxs[0]].get_val(lri) {
                            n.to_i64()
                        } else {
                            None
                        };
                        if let Some(k) = key_opt {
                            if !dup_keys.is_empty() && dup_keys.contains(&k) {
                                return Err(OpErr::Stopped(Bug {
                                    kind: BugKind::JoinCardinality,
                                    message:
                                        "join cardinality violated: multiple right rows matched key"
                                            .to_string(),
                                }));
                            }
                            map.get(&k).copied()
                        } else {
                            None
                        }
                    }
                    RightIndex::Generic(index) => {
                        let h = hash_row_key(&lb.cols, &l_key_idxs, lri);
                        let mut first_hit: Option<RowRef> = None;
                        if let Some(cands) = index.get(&h) {
                            for &rr in cands {
                                let rb = &right.batches[rr.batch_idx as usize];
                                let rri = usize::from(rr.row_idx);
                                if l_key_idxs.iter().zip(&r_key_idxs).all(|(&lk, &rk)| {
                                    eq_col_cells(&lb.cols[lk], lri, &rb.cols[rk], rri)
                                }) {
                                    if first_hit.is_some() {
                                        return Err(OpErr::Stopped(Bug {
                                            kind: BugKind::JoinCardinality,
                                            message:
                                                "join cardinality violated: multiple right rows matched key"
                                                    .to_string(),
                                        }));
                                    }
                                    first_hit = Some(rr);
                                }
                            }
                        }
                        first_hit
                    }
                };
                match found {
                    None => {
                        if is_left {
                            if l_sel.len() != lri {
                                is_identity = false;
                            }
                            l_sel.push(l_u16);
                            r_refs.push(None);
                        } else {
                            is_identity = false;
                        }
                    }
                    Some(rr) => {
                        if !matched_right_globals.insert(rr.global_idx) {
                            return Err(OpErr::Stopped(Bug {
                                kind: BugKind::JoinCardinality,
                                message:
                                    "1:1 join cardinality violated: multiple left rows matched same right row"
                                        .to_string(),
                            }));
                        }
                        if l_sel.len() != lri {
                            is_identity = false;
                        }
                        l_sel.push(l_u16);
                        r_refs.push(Some(rr));
                    }
                }
            }
            if l_sel.len() != lb.len {
                is_identity = false;
            }
            out_batches.extend(gather_joined_batches(
                lb,
                right,
                &right_keep,
                &out_cols,
                &l_sel,
                &r_refs,
                is_identity,
                is_left,
                false,
                batch_size,
            ));
        }
        return Ok(VmTable {
            batches: out_batches,
            cols: out_cols,
        });
    }

    // Parallel columnar probe & gather for `InnerMany`, `InnerManyToOne`, `LeftManyToOne`!
    let total_left = left.total_rows();
    let probed: Vec<Vec<Batch>> = parallel_map_ref(
        &left.batches,
        total_left,
        cfg.parallel_threshold_rows,
        cfg.max_threads,
        |lb| -> Result<Vec<Batch>, OpErr> {
            let active = lb.active_indices();
            if active.is_empty() {
                return Ok(Vec::new());
            }
            let mut l_sel = Vec::with_capacity(active.len());
            let mut r_refs = Vec::with_capacity(active.len());
            let mut is_identity = lb.selection.is_none();

            match &right_index {
                RightIndex::SingleIntUnique { map, dup_keys }
                    if l_key_idxs.len() == 1
                        && lb.cols[l_key_idxs[0]].validity.is_none()
                        && matches!(lb.cols[l_key_idxs[0]].data, ColumnData::Int(_)) =>
                {
                    if let ColumnData::Int(lvals) = &lb.cols[l_key_idxs[0]].data {
                        let has_dups = !dup_keys.is_empty();
                        for &l_u16 in &active {
                            let lri = usize::from(l_u16);
                            let k = lvals[lri];
                            if has_dups && dup_keys.contains(&k) {
                                return Err(OpErr::Stopped(Bug {
                                    kind: BugKind::JoinCardinality,
                                    message:
                                        "join cardinality violated: multiple right rows matched key"
                                            .to_string(),
                                }));
                            }
                            if let Some(&rr) = map.get(&k) {
                                if l_sel.len() != lri {
                                    is_identity = false;
                                }
                                l_sel.push(l_u16);
                                r_refs.push(Some(rr));
                            } else if is_left {
                                if l_sel.len() != lri {
                                    is_identity = false;
                                }
                                l_sel.push(l_u16);
                                r_refs.push(None);
                            } else {
                                is_identity = false;
                            }
                        }
                    }
                }
                RightIndex::SingleIntUnique { map, dup_keys } => {
                    let has_dups = !dup_keys.is_empty();
                    for &l_u16 in &active {
                        let lri = usize::from(l_u16);
                        let key_opt = match lb.cols[l_key_idxs[0]].get_val(lri) {
                            Val::Int(ref n) => n.to_i64(),
                            _ => None,
                        };
                        let hit = if let Some(k) = key_opt {
                            if has_dups && dup_keys.contains(&k) {
                                return Err(OpErr::Stopped(Bug {
                                    kind: BugKind::JoinCardinality,
                                    message:
                                        "join cardinality violated: multiple right rows matched key"
                                            .to_string(),
                                }));
                            }
                            map.get(&k).copied()
                        } else {
                            None
                        };
                        if let Some(rr) = hit {
                            if l_sel.len() != lri {
                                is_identity = false;
                            }
                            l_sel.push(l_u16);
                            r_refs.push(Some(rr));
                        } else if is_left {
                            if l_sel.len() != lri {
                                is_identity = false;
                            }
                            l_sel.push(l_u16);
                            r_refs.push(None);
                        } else {
                            is_identity = false;
                        }
                    }
                }
                RightIndex::Generic(index) => {
                    for &l_u16 in &active {
                        let lri = usize::from(l_u16);
                        let h = hash_row_key(&lb.cols, &l_key_idxs, lri);
                        if check_right_unique {
                            let mut first_hit: Option<RowRef> = None;
                            if let Some(cands) = index.get(&h) {
                                for &rr in cands {
                                    let rb = &right.batches[rr.batch_idx as usize];
                                    let rri = usize::from(rr.row_idx);
                                    if l_key_idxs.iter().zip(&r_key_idxs).all(|(&lk, &rk)| {
                                        eq_col_cells(&lb.cols[lk], lri, &rb.cols[rk], rri)
                                    }) {
                                        if first_hit.is_some() {
                                            return Err(OpErr::Stopped(Bug {
                                                kind: BugKind::JoinCardinality,
                                                message:
                                                    "join cardinality violated: multiple right rows matched key"
                                                        .to_string(),
                                            }));
                                        }
                                        first_hit = Some(rr);
                                    }
                                }
                            }
                            if let Some(rr) = first_hit {
                                if l_sel.len() != lri {
                                    is_identity = false;
                                }
                                l_sel.push(l_u16);
                                r_refs.push(Some(rr));
                            } else if is_left {
                                if l_sel.len() != lri {
                                    is_identity = false;
                                }
                                l_sel.push(l_u16);
                                r_refs.push(None);
                            } else {
                                is_identity = false;
                            }
                        } else {
                            let mut matched_any = false;
                            if let Some(cands) = index.get(&h) {
                                for &rr in cands {
                                    let rb = &right.batches[rr.batch_idx as usize];
                                    let rri = usize::from(rr.row_idx);
                                    if l_key_idxs.iter().zip(&r_key_idxs).all(|(&lk, &rk)| {
                                        eq_col_cells(&lb.cols[lk], lri, &rb.cols[rk], rri)
                                    }) {
                                        matched_any = true;
                                        if l_sel.len() != lri {
                                            is_identity = false;
                                        }
                                        l_sel.push(l_u16);
                                        r_refs.push(Some(rr));
                                    }
                                }
                            }
                            if !matched_any {
                                if is_left {
                                    if l_sel.len() != lri {
                                        is_identity = false;
                                    }
                                    l_sel.push(l_u16);
                                    r_refs.push(None);
                                } else {
                                    is_identity = false;
                                }
                            }
                        }
                    }
                }
            }
            if l_sel.len() != lb.len {
                is_identity = false;
            }
            Ok(gather_joined_batches(
                lb,
                right,
                &right_keep,
                &out_cols,
                &l_sel,
                &r_refs,
                is_identity,
                is_left,
                false,
                batch_size,
            ))
        },
    )?;

    Ok(VmTable {
        cols: out_cols,
        batches: probed.into_iter().flatten().collect(),
    })
}
