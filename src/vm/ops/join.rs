//! Vectorized Hash Join for all 7 Dana join kinds (`InnerOne`, `InnerManyToOne`,
//! `InnerMany`, `LeftOne`, `LeftManyToOne`, `Semi`, `Anti`) with:
//! - O(N) hash-indexed cardinality verification preserving exact earliest `(i1, i2)`
//!   redacted diagnostics matching `Eval.lean` / `src/oracle/eval.rs`
//! - Zero-allocation columnar key probing & parallel left-batch probing via `std::thread::scope`.

use std::collections::{HashMap, HashSet};

use crate::core::check::{build_joined_cols, resolve_join_pairs};
use crate::core::syntax::{BugKind, ColSpec, Ident, JoinKind, JoinOn, Suffixes, TableTy, TagSet};
use crate::oracle::value::{Bug, TableRow, Val, format_diag_detail};
use crate::vm::batch::{Batch, rows_to_batches};
use crate::vm::key::{eq_col_cells, hash_row_key};
use crate::vm::ops::{OpErr, OpExecConfig, VmMode, VmTable};
use crate::vm::parallel::parallel_map_ref;

/// Compact coordinate pointing to a single row in a `Vec<Batch>`.
#[derive(Clone, Copy, Debug)]
struct RowRef {
    batch_idx: u32,
    row_idx: u16,
    global_idx: usize,
}

/// O(N) duplicate-key detector over columnar batches that returns the **exact**
/// duplicate pair `(i1, i2)` with minimum `i1` (and minimum `i2 > i1`), matching
/// `src/oracle/eval.rs:check_unique_join_keys` byte-for-byte!
fn check_unique_keys_columnar(
    batches: &[Batch],
    key_idxs: &[usize],
    key_tags: &TagSet,
) -> Option<Bug> {
    // Map hash -> list of first-occurrence `RowRef`s (only one entry per distinct key!).
    let mut table: HashMap<u64, Vec<RowRef>> = HashMap::new();
    // Track best `(i1, i2, RowRef_of_i1)` minimizing `i1` (and for each `i1`, first `i2`).
    let mut best_dup: Option<(usize, usize, RowRef)> = None;
    let mut recorded_first: HashSet<usize> = HashSet::new();

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

/// Build an immutable hash index mapping key hash -> matching right `RowRef`s.
fn build_right_index(right_batches: &[Batch], r_key_idxs: &[usize]) -> HashMap<u64, Vec<RowRef>> {
    let total_r: usize = right_batches.iter().map(Batch::active_len).sum();
    let mut index: HashMap<u64, Vec<RowRef>> = HashMap::with_capacity(total_r);
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
    index
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

/// Execute a vectorized Hash Join over two [`VmTable`]s.
pub fn op_hash_join(
    kind: JoinKind,
    left: VmTable,
    right: VmTable,
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
    left: VmTable,
    right: VmTable,
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

    // Upfront uniqueness checks (exact match with `src/oracle/eval.rs:3574-3591`).
    if matches!(kind, JoinKind::InnerOne | JoinKind::LeftOne)
        && let Some(bug) = check_unique_keys_columnar(&left.batches, &l_key_idxs, &key_tags)
    {
        return Err(OpErr::Stopped(bug));
    }
    if matches!(
        kind,
        JoinKind::InnerOne | JoinKind::LeftOne | JoinKind::InnerManyToOne | JoinKind::LeftManyToOne
    ) && let Some(bug) = check_unique_keys_columnar(&right.batches, &r_key_idxs, &key_tags)
    {
        return Err(OpErr::Stopped(bug));
    }

    let right_index = build_right_index(&right.batches, &r_key_idxs);
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

    // Parallel probe across left batches!
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
                for &l_u16 in &active {
                    let lri = usize::from(l_u16);
                    let h = hash_row_key(&lb.cols, &l_key_idxs, lri);
                    let matched = right_index.get(&h).is_some_and(|cands| {
                        cands.iter().any(|rr| {
                            let rb = &right.batches[rr.batch_idx as usize];
                            let rri = usize::from(rr.row_idx);
                            l_key_idxs.iter().zip(&r_key_idxs).all(|(&lk, &rk)| {
                                eq_col_cells(&lb.cols[lk], lri, &rb.cols[rk], rri)
                            })
                        })
                    });
                    if (kind == JoinKind::Semi && matched) || (kind == JoinKind::Anti && !matched) {
                        kept_sel.push(l_u16);
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

            let mut out_rows = Vec::with_capacity(active.len());
            let l_ncols = lb.cols.len();
            let total_ncols = l_ncols + r_keep_idxs.len();
            for &l_u16 in &active {
                let lri = usize::from(l_u16);
                let h = hash_row_key(&lb.cols, &l_key_idxs, lri);
                let mut matched_any = false;
                if let Some(cands) = right_index.get(&h) {
                    for rr in cands {
                        let rb = &right.batches[rr.batch_idx as usize];
                        let rri = usize::from(rr.row_idx);
                        let is_eq = l_key_idxs
                            .iter()
                            .zip(&r_key_idxs)
                            .all(|(&lk, &rk)| eq_col_cells(&lb.cols[lk], lri, &rb.cols[rk], rri));
                        if is_eq {
                            matched_any = true;
                            let mut cells = Vec::with_capacity(total_ncols);
                            for c in &lb.cols {
                                cells.push(c.get_val(lri));
                            }
                            for &rk_idx in &r_keep_idxs {
                                let v = rb.cols[rk_idx].get_val(rri);
                                cells.push(if is_left_outer {
                                    wrap_opt_core(&right.cols[rk_idx], v)
                                } else {
                                    v
                                });
                            }
                            out_rows.push(TableRow {
                                cells,
                                group_meta: None,
                            });
                        }
                    }
                }
                if !matched_any && is_left_outer {
                    let mut cells = Vec::with_capacity(total_ncols);
                    for c in &lb.cols {
                        cells.push(c.get_val(lri));
                    }
                    cells.extend(std::iter::repeat_n(Val::OptNone, r_keep_idxs.len()));
                    out_rows.push(TableRow {
                        cells,
                        group_meta: None,
                    });
                }
            }
            Ok(rows_to_batches(&out_cols, &out_rows, batch_size))
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
    left: VmTable,
    right: VmTable,
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
    let right_index = build_right_index(&right.batches, &r_key_idxs);

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
                for &l_u16 in &active {
                    let lri = usize::from(l_u16);
                    let h = hash_row_key(&lb.cols, &l_key_idxs, lri);
                    let matched = right_index.get(&h).is_some_and(|cands| {
                        cands.iter().any(|rr| {
                            let rb = &right.batches[rr.batch_idx as usize];
                            let rri = usize::from(rr.row_idx);
                            l_key_idxs.iter().zip(&r_key_idxs).all(|(&lk, &rk)| {
                                eq_col_cells(&lb.cols[lk], lri, &rb.cols[rk], rri)
                            })
                        })
                    });
                    if (kind == JoinKind::Semi && matched) || (kind == JoinKind::Anti && !matched) {
                        kept.push(l_u16);
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

    // For `InnerOne`/`LeftOne`, track matched right row global indices to enforce 1:1.
    if check_left_unique {
        let mut matched_right_globals: HashSet<usize> = HashSet::new();
        let mut out_rows = Vec::new();
        for lb in &left.batches {
            for &l_u16 in &lb.active_indices() {
                let lri = usize::from(l_u16);
                let h = hash_row_key(&lb.cols, &l_key_idxs, lri);
                let mut matches = Vec::new();
                if let Some(cands) = right_index.get(&h) {
                    for &rr in cands {
                        let rb = &right.batches[rr.batch_idx as usize];
                        let rri = usize::from(rr.row_idx);
                        if l_key_idxs
                            .iter()
                            .zip(&r_key_idxs)
                            .all(|(&lk, &rk)| eq_col_cells(&lb.cols[lk], lri, &rb.cols[rk], rri))
                        {
                            matches.push(rr);
                        }
                    }
                }
                if check_right_unique && matches.len() > 1 {
                    return Err(OpErr::Stopped(Bug {
                        kind: BugKind::JoinCardinality,
                        message: "join cardinality violated: multiple right rows matched key"
                            .to_string(),
                    }));
                }
                if matches.is_empty() {
                    if is_left {
                        let mut cells: Vec<Val> = lb.cols.iter().map(|c| c.get_val(lri)).collect();
                        cells.extend(std::iter::repeat_n(Val::OptNone, right_keep.len()));
                        out_rows.push(TableRow {
                            cells,
                            group_meta: None,
                        });
                    }
                } else {
                    for rr in matches {
                        if !matched_right_globals.insert(rr.global_idx) {
                            return Err(OpErr::Stopped(Bug {
                                kind: BugKind::JoinCardinality,
                                message:
                                    "1:1 join cardinality violated: multiple left rows matched same right row"
                                        .to_string(),
                            }));
                        }
                        let rb = &right.batches[rr.batch_idx as usize];
                        let rri = usize::from(rr.row_idx);
                        let mut cells: Vec<Val> = lb.cols.iter().map(|c| c.get_val(lri)).collect();
                        for &rk_idx in &right_keep {
                            let rv = rb.cols[rk_idx].get_val(rri);
                            cells.push(if is_left { wrap_opt_exec(rv) } else { rv });
                        }
                        out_rows.push(TableRow {
                            cells,
                            group_meta: None,
                        });
                    }
                }
            }
        }
        return Ok(VmTable {
            batches: rows_to_batches(&out_cols, &out_rows, cfg.batch_size),
            cols: out_cols,
        });
    }

    // Parallel probe for `InnerMany`, `InnerManyToOne`, `LeftManyToOne`!
    let total_left = left.total_rows();
    let batch_size = cfg.batch_size;
    let probed: Vec<Vec<Batch>> = parallel_map_ref(
        &left.batches,
        total_left,
        cfg.parallel_threshold_rows,
        cfg.max_threads,
        |lb| -> Result<Vec<Batch>, OpErr> {
            let active = lb.active_indices();
            let mut out_rows = Vec::with_capacity(active.len());
            for &l_u16 in &active {
                let lri = usize::from(l_u16);
                let h = hash_row_key(&lb.cols, &l_key_idxs, lri);
                let mut matches = Vec::new();
                if let Some(cands) = right_index.get(&h) {
                    for &rr in cands {
                        let rb = &right.batches[rr.batch_idx as usize];
                        let rri = usize::from(rr.row_idx);
                        if l_key_idxs
                            .iter()
                            .zip(&r_key_idxs)
                            .all(|(&lk, &rk)| eq_col_cells(&lb.cols[lk], lri, &rb.cols[rk], rri))
                        {
                            matches.push(rr);
                        }
                    }
                }
                if check_right_unique && matches.len() > 1 {
                    return Err(OpErr::Stopped(Bug {
                        kind: BugKind::JoinCardinality,
                        message: "join cardinality violated: multiple right rows matched key"
                            .to_string(),
                    }));
                }
                if matches.is_empty() {
                    if is_left {
                        let mut cells: Vec<Val> = lb.cols.iter().map(|c| c.get_val(lri)).collect();
                        cells.extend(std::iter::repeat_n(Val::OptNone, right_keep.len()));
                        out_rows.push(TableRow {
                            cells,
                            group_meta: None,
                        });
                    }
                } else {
                    for rr in matches {
                        let rb = &right.batches[rr.batch_idx as usize];
                        let rri = usize::from(rr.row_idx);
                        let mut cells: Vec<Val> = lb.cols.iter().map(|c| c.get_val(lri)).collect();
                        for &rk_idx in &right_keep {
                            let rv = rb.cols[rk_idx].get_val(rri);
                            cells.push(if is_left { wrap_opt_exec(rv) } else { rv });
                        }
                        out_rows.push(TableRow {
                            cells,
                            group_meta: None,
                        });
                    }
                }
            }
            Ok(rows_to_batches(&out_cols, &out_rows, batch_size))
        },
    )?;

    Ok(VmTable {
        cols: out_cols,
        batches: probed.into_iter().flatten().collect(),
    })
}
