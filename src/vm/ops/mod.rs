//! Physical columnar batch operators covering all 21 Dana relational verbs.
//!
//! Includes:
//! - Streaming stateless batch ops (`Select`, `Drop`, `Rename`, `Filter` with
//!   selection-vector compaction, `Derive` + `BucketCol`, `Limit` early stop,
//!   `Union`, `Redact`, `Pseudonymize`) with deterministic parallel fan-out
//! - Hash join (`join.rs`) for all 7 `JoinKind`s with O(N) cardinality checks &
//!   parallel probe
//! - Hash aggregate & small-group suppression (`agg.rs`) for all 12 `AggOp`s &
//!   both `SuppressMode`s with parallel radix partitioning
//! - Sort, Hash Distinct, O(N log N) Window, FillGaps, PivotWider, Crosstab (`sort_win.rs`).

pub mod agg;
pub mod join;
pub mod sort_win;

use crate::core::syntax::{AggKind, ColSpec, Literal, ScalarTy, TagSet};
use crate::formats::crypto::hmac_sha256_pseudonym;
use crate::oracle::eval::{eval_literal, pseudonymize_token};
use crate::oracle::value::{Bug, TableVal, Val, val_lt};
use crate::runtime::ir::PseudonymizeMode;
use crate::vm::batch::{Batch, Column, ColumnData, batches_to_table, table_to_batches};
use crate::vm::expr::{RegVal, RowEvalErr, RowEvalHost, RowProgram, eval_row_program};
use crate::vm::parallel::parallel_map_batches;

/// Selects exact operational semantics:
/// - `CoreV01`: 100% bit-for-bit parity with `formal/DanaCore/Eval.lean` and `src/oracle/`.
/// - `ExecSurface`: 100% parity with Phase 2 surface runtime (`src/runtime/exec.rs`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum VmMode {
    CoreV01,
    ExecSurface,
}

/// Runtime configuration shared across physical operators.
#[derive(Clone, Copy, Debug)]
pub struct OpExecConfig {
    pub batch_size: usize,
    pub parallel_threshold_rows: usize,
    pub max_threads: Option<usize>,
    pub mode: VmMode,
    pub pseudonymize_mode: PseudonymizeMode,
}

/// Physical operator error: either a deterministic language `Stop(Bug)` or an internal error.
#[derive(Clone, Debug)]
pub enum OpErr {
    Stopped(Bug),
    Failed(String),
    Wrong,
}

impl From<RowEvalErr> for OpErr {
    fn from(e: RowEvalErr) -> Self {
        match e {
            RowEvalErr::Stopped { bug, .. } => Self::Stopped(bug),
            RowEvalErr::Failed(m) => Self::Failed(m),
        }
    }
}

/// Columnar table represented as authoritative schema metadata + stream of 2,048-row batches.
#[derive(Clone, Debug)]
pub struct VmTable {
    pub cols: Vec<ColSpec>,
    pub batches: Vec<Batch>,
}

impl VmTable {
    #[must_use]
    pub fn from_table_val(tv: &TableVal, batch_size: usize) -> Self {
        Self {
            cols: tv.cols.clone(),
            batches: table_to_batches(tv, batch_size),
        }
    }

    #[must_use]
    pub fn into_table_val(self) -> TableVal {
        batches_to_table(self.cols, &self.batches)
    }

    #[must_use]
    pub fn total_rows(&self) -> usize {
        self.batches.iter().map(Batch::active_len).sum()
    }

    #[must_use]
    pub fn find_col_idx(&self, name: &str) -> Option<usize> {
        self.cols.iter().position(|c| c.name == name)
    }
}

/// Pull-based streaming cursor over columnar batches (used for streaming pipelines and early `Limit`).
#[derive(Debug)]
pub struct BatchStream {
    cols: Vec<ColSpec>,
    batches: std::vec::IntoIter<Batch>,
}

impl BatchStream {
    #[must_use]
    pub fn from_table(tbl: VmTable) -> Self {
        Self {
            cols: tbl.cols,
            batches: tbl.batches.into_iter(),
        }
    }

    #[must_use]
    pub fn schema(&self) -> &[ColSpec] {
        &self.cols
    }

    pub fn next_batch(&mut self) -> Option<Batch> {
        self.batches.next()
    }

    #[must_use]
    pub fn collect_table(self) -> VmTable {
        VmTable {
            cols: self.cols,
            batches: self.batches.collect(),
        }
    }
}

fn reset_cols_raw(cols: Vec<ColSpec>, mode: VmMode) -> Vec<ColSpec> {
    if mode == VmMode::CoreV01 {
        cols.into_iter()
            .map(|c| ColSpec {
                agg_kind: AggKind::Raw,
                ..c
            })
            .collect()
    } else {
        cols
    }
}

fn clear_group_meta_if_core(b: &mut Batch, mode: VmMode) {
    if mode == VmMode::CoreV01 {
        b.group_meta = None;
    }
}

/// Zero-copy columnar `Select` projection.
pub fn op_select(tbl: VmTable, select_cols: &[String], mode: VmMode) -> Result<VmTable, OpErr> {
    let mut idxs = Vec::with_capacity(select_cols.len());
    let mut out_cols = Vec::with_capacity(select_cols.len());
    for name in select_cols {
        let Some(ci) = tbl.find_col_idx(name) else {
            return Err(if mode == VmMode::CoreV01 {
                OpErr::Wrong
            } else {
                OpErr::Failed(format!("select: missing col `{name}`"))
            });
        };
        idxs.push(ci);
        let mut spec = tbl.cols[ci].clone();
        if mode == VmMode::CoreV01 {
            spec.agg_kind = AggKind::Raw;
        }
        out_cols.push(spec);
    }

    let batches = tbl
        .batches
        .into_iter()
        .map(|mut b| {
            clear_group_meta_if_core(&mut b, mode);
            let cols = idxs
                .iter()
                .zip(&out_cols)
                .map(|(&ci, spec)| {
                    let mut c = b.cols[ci].clone();
                    c.spec = spec.clone();
                    c
                })
                .collect();
            Batch {
                cols,
                len: b.len,
                selection: b.selection,
                group_meta: b.group_meta,
            }
        })
        .collect();
    Ok(VmTable {
        cols: out_cols,
        batches,
    })
}

/// Zero-copy columnar `Drop`.
pub fn op_drop(tbl: VmTable, drop_cols: &[String], mode: VmMode) -> Result<VmTable, OpErr> {
    let keep: Vec<usize> = tbl
        .cols
        .iter()
        .enumerate()
        .filter(|(_, c)| !drop_cols.contains(&c.name))
        .map(|(i, _)| i)
        .collect();
    let out_cols: Vec<ColSpec> = keep
        .iter()
        .map(|&i| {
            let mut spec = tbl.cols[i].clone();
            if mode == VmMode::CoreV01 {
                spec.agg_kind = AggKind::Raw;
            }
            spec
        })
        .collect();

    let batches = tbl
        .batches
        .into_iter()
        .map(|mut b| {
            clear_group_meta_if_core(&mut b, mode);
            let cols = keep
                .iter()
                .zip(&out_cols)
                .map(|(&ci, spec)| {
                    let mut c = b.cols[ci].clone();
                    c.spec = spec.clone();
                    c
                })
                .collect();
            Batch {
                cols,
                len: b.len,
                selection: b.selection,
                group_meta: b.group_meta,
            }
        })
        .collect();
    Ok(VmTable {
        cols: out_cols,
        batches,
    })
}

/// Zero-copy columnar `Rename`.
/// - In `CoreV01`, `pairs` are `(new_name, old_name)` matching `Eval.lean`.
/// - In `ExecSurface`, `pairs` are `(old_name, new_name)` matching `src/runtime/exec.rs`.
#[must_use]
pub fn op_rename(tbl: VmTable, pairs: &[(String, String)], mode: VmMode) -> VmTable {
    let out_cols: Vec<ColSpec> = if mode == VmMode::CoreV01 {
        tbl.cols
            .into_iter()
            .map(|c| match pairs.iter().find(|(_, old_n)| *old_n == c.name) {
                Some((new_n, _)) => ColSpec {
                    name: new_n.clone(),
                    agg_kind: AggKind::Raw,
                    ..c
                },
                None => ColSpec {
                    agg_kind: AggKind::Raw,
                    ..c
                },
            })
            .collect()
    } else {
        let mut cols = tbl.cols;
        for (old_n, new_n) in pairs {
            if let Some(c) = cols.iter_mut().find(|c| c.name == *old_n) {
                c.name = new_n.clone();
            }
        }
        cols
    };

    let batches = tbl
        .batches
        .into_iter()
        .map(|mut b| {
            clear_group_meta_if_core(&mut b, mode);
            for (c, spec) in b.cols.iter_mut().zip(&out_cols) {
                c.spec = spec.clone();
            }
            b
        })
        .collect();
    VmTable {
        cols: out_cols,
        batches,
    }
}

/// Vectorized `Filter` with selection-vector filtering, adaptive compaction when
/// selectivity drops below 50%, and deterministic parallel batch execution.
pub fn op_filter(
    tbl: VmTable,
    pred: &RowProgram,
    host: &dyn RowEvalHost,
    cfg: &OpExecConfig,
) -> Result<VmTable, OpErr> {
    let out_cols = reset_cols_raw(tbl.cols, cfg.mode);
    let total_rows = tbl.batches.iter().map(Batch::active_len).sum();
    let mode = cfg.mode;

    let filtered = parallel_map_batches(
        tbl.batches,
        total_rows,
        cfg.parallel_threshold_rows,
        cfg.max_threads,
        |mut batch| -> Result<Option<Batch>, OpErr> {
            clear_group_meta_if_core(&mut batch, mode);
            if batch.is_empty() {
                return Ok(None);
            }
            let active = batch.active_indices();
            let reg = eval_row_program(pred, &batch, host)?;
            let mut next_sel = Vec::with_capacity(active.len());
            match reg {
                RegVal::Bool(bs) => {
                    for &l in &active {
                        if bs[usize::from(l)] != 0 {
                            next_sel.push(l);
                        }
                    }
                }
                RegVal::Broadcast(Val::Bool(true)) => next_sel = active,
                RegVal::Broadcast(Val::Bool(false)) => {}
                RegVal::Generic(vs) => {
                    for &l in &active {
                        match vs.get(usize::from(l)) {
                            Some(Val::Bool(true)) => next_sel.push(l),
                            Some(Val::Bool(false)) => {}
                            _ => {
                                return Err(if mode == VmMode::CoreV01 {
                                    OpErr::Wrong
                                } else {
                                    OpErr::Failed("filter predicate returned non-Bool".to_string())
                                });
                            }
                        }
                    }
                }
                _ => {
                    return Err(if mode == VmMode::CoreV01 {
                        OpErr::Wrong
                    } else {
                        OpErr::Failed("filter predicate returned non-Bool".to_string())
                    });
                }
            }
            if next_sel.is_empty() {
                return Ok(None);
            }
            let sel_len = next_sel.len();
            if sel_len == batch.len && batch.selection.is_none() {
                // 100% selectivity — zero work!
            } else {
                batch.selection = Some(next_sel);
                if sel_len * 2 < batch.len {
                    batch = batch.compact();
                }
            }
            if mode == VmMode::CoreV01 {
                for c in &mut batch.cols {
                    c.spec.agg_kind = AggKind::Raw;
                }
            }
            Ok(Some(batch))
        },
    )?;

    let batches: Vec<Batch> = filtered.into_iter().flatten().collect();
    Ok(VmTable {
        cols: out_cols,
        batches,
    })
}

/// Vectorized `Derive` column expression step (appends or overwrites `target_spec`),
/// executing across batches in parallel when `total_rows >= parallel_threshold_rows`.
pub fn op_derive_col_expr(
    tbl: VmTable,
    target_spec: ColSpec,
    rp: &RowProgram,
    host: &dyn RowEvalHost,
    cfg: &OpExecConfig,
) -> Result<VmTable, OpErr> {
    let mut out_cols = reset_cols_raw(tbl.cols, cfg.mode);
    let existing_idx = out_cols.iter().position(|c| c.name == target_spec.name);
    match existing_idx {
        Some(idx) => out_cols[idx] = target_spec.clone(),
        None => out_cols.push(target_spec.clone()),
    }
    let total_rows = tbl.batches.iter().map(Batch::active_len).sum();
    let mode = cfg.mode;

    let batches = parallel_map_batches(
        tbl.batches,
        total_rows,
        cfg.parallel_threshold_rows,
        cfg.max_threads,
        |mut batch| -> Result<Batch, OpErr> {
            clear_group_meta_if_core(&mut batch, mode);
            if batch.is_empty() {
                let empty_col = Column::from_vals(target_spec.clone(), &[]);
                match existing_idx {
                    Some(idx) => batch.cols[idx] = empty_col,
                    None => batch.cols.push(empty_col),
                }
                return Ok(batch);
            }
            let reg = eval_row_program(rp, &batch, host)?;
            let new_col = reg.into_column(target_spec.clone(), batch.len);
            if mode == VmMode::CoreV01 {
                for c in &mut batch.cols {
                    c.spec.agg_kind = AggKind::Raw;
                }
            }
            match existing_idx {
                Some(idx) => batch.cols[idx] = new_col,
                None => batch.cols.push(new_col),
            }
            Ok(batch)
        },
    )?;
    Ok(VmTable {
        cols: out_cols,
        batches,
    })
}

/// Vectorized `BucketCol` derive step (`bucket(.source, cuts: [...], labels: [...])`).
pub fn op_derive_bucket(
    tbl: VmTable,
    name: &str,
    source: &str,
    cuts: &[Literal],
    labels: &[String],
    target_spec_override: Option<ColSpec>,
    cfg: &OpExecConfig,
) -> Result<VmTable, OpErr> {
    let mut out_cols = reset_cols_raw(tbl.cols, cfg.mode);
    let Some(src_idx) = out_cols.iter().position(|c| c.name == source) else {
        return Err(if cfg.mode == VmMode::CoreV01 {
            OpErr::Wrong
        } else {
            OpErr::Failed(format!("bucket: missing col `{source}`"))
        });
    };
    if labels.len() != cuts.len() + 1 && cfg.mode == VmMode::CoreV01 {
        return Err(OpErr::Wrong);
    }
    let target_spec = target_spec_override.unwrap_or_else(|| ColSpec {
        name: name.to_string(),
        ty: ScalarTy::Text,
        tags: out_cols[src_idx].tags.clone(),
        bucketed: true,
        agg_kind: AggKind::Raw,
    });
    let existing_idx = out_cols.iter().position(|c| c.name == name);
    match existing_idx {
        Some(idx) => out_cols[idx] = target_spec.clone(),
        None => out_cols.push(target_spec.clone()),
    }
    let cut_vals: Vec<Val> = cuts.iter().map(eval_literal).collect();
    let total_rows = tbl.batches.iter().map(Batch::active_len).sum();
    let mode = cfg.mode;

    let batches = parallel_map_batches(
        tbl.batches,
        total_rows,
        cfg.parallel_threshold_rows,
        cfg.max_threads,
        |mut batch| -> Result<Batch, OpErr> {
            clear_group_meta_if_core(&mut batch, mode);
            let mut offsets = Vec::with_capacity(batch.len + 1);
            let mut data = Vec::new();
            offsets.push(0);
            let src_col = &batch.cols[src_idx];
            // Fast path for non-null Int/Decimal/Float columns.
            match &src_col.data {
                ColumnData::Int(vs)
                    if src_col.validity.is_none()
                        && cut_vals
                            .iter()
                            .all(|v| matches!(v, Val::Int(x) if x.to_i64().is_some())) =>
                {
                    let icuts: Vec<i64> = cut_vals
                        .iter()
                        .filter_map(|v| match v {
                            Val::Int(x) => x.to_i64(),
                            _ => None,
                        })
                        .collect();
                    for &v in vs {
                        let mut bidx = icuts.len();
                        for (ci, &cv) in icuts.iter().enumerate() {
                            if v < cv {
                                bidx = ci;
                                break;
                            }
                        }
                        if let Some(lbl) = labels.get(bidx) {
                            data.extend_from_slice(lbl.as_bytes());
                        }
                        offsets.push(data.len());
                    }
                }
                ColumnData::Decimal(vs)
                    if src_col.validity.is_none()
                        && cut_vals
                            .iter()
                            .all(|v| matches!(v, Val::Decimal(x) if x.to_i128().is_some())) =>
                {
                    let dcuts: Vec<i128> = cut_vals
                        .iter()
                        .filter_map(|v| match v {
                            Val::Decimal(x) => x.to_i128(),
                            _ => None,
                        })
                        .collect();
                    for &v in vs {
                        let mut bidx = dcuts.len();
                        for (ci, &cv) in dcuts.iter().enumerate() {
                            if v < cv {
                                bidx = ci;
                                break;
                            }
                        }
                        if let Some(lbl) = labels.get(bidx) {
                            data.extend_from_slice(lbl.as_bytes());
                        }
                        offsets.push(data.len());
                    }
                }
                _ => {
                    for r in 0..batch.len {
                        let v = src_col.get_val(r);
                        let mut bidx = cut_vals.len();
                        for (ci, cv) in cut_vals.iter().enumerate() {
                            if val_lt(&v, cv) {
                                bidx = ci;
                                break;
                            }
                        }
                        if let Some(lbl) = labels.get(bidx) {
                            data.extend_from_slice(lbl.as_bytes());
                        }
                        offsets.push(data.len());
                    }
                }
            }
            let new_col = Column {
                spec: target_spec.clone(),
                data: ColumnData::Text { offsets, data },
                validity: None,
            };
            if mode == VmMode::CoreV01 {
                for c in &mut batch.cols {
                    c.spec.agg_kind = AggKind::Raw;
                }
            }
            match existing_idx {
                Some(idx) => batch.cols[idx] = new_col,
                None => batch.cols.push(new_col),
            }
            Ok(batch)
        },
    )?;

    Ok(VmTable {
        cols: out_cols,
        batches,
    })
}

/// Early-terminating columnar `Limit(n)`.
#[must_use]
pub fn op_limit(tbl: VmTable, limit: usize, mode: VmMode) -> VmTable {
    let out_cols = reset_cols_raw(tbl.cols, mode);
    let mut rem = limit;
    let mut out_batches = Vec::new();
    let mut stream = BatchStream {
        cols: out_cols.clone(),
        batches: tbl.batches.into_iter(),
    };
    while rem > 0 {
        let Some(mut b) = stream.next_batch() else {
            break;
        };
        clear_group_meta_if_core(&mut b, mode);
        let active = b.active_len();
        if active == 0 {
            continue;
        }
        if active <= rem {
            if mode == VmMode::CoreV01 {
                for c in &mut b.cols {
                    c.spec.agg_kind = AggKind::Raw;
                }
            }
            rem -= active;
            out_batches.push(b);
        } else {
            let mut sliced = b.take_first(rem);
            if mode == VmMode::CoreV01 {
                for c in &mut sliced.cols {
                    c.spec.agg_kind = AggKind::Raw;
                }
            }
            out_batches.push(sliced);
            break;
        }
    }
    VmTable {
        cols: out_cols,
        batches: out_batches,
    }
}

/// Columnar `Union` concatenating batches from `left` followed by `right`.
pub fn op_union(left: VmTable, right: VmTable, mode: VmMode) -> Result<VmTable, OpErr> {
    let out_cols = if mode == VmMode::CoreV01 {
        crate::core::check::merge_union_cols(&left.cols, &right.cols).ok_or(OpErr::Wrong)?
    } else {
        left.cols
    };
    let mut batches = Vec::with_capacity(left.batches.len() + right.batches.len());
    for mut b in left.batches.into_iter().chain(right.batches) {
        clear_group_meta_if_core(&mut b, mode);
        for (c, spec) in b.cols.iter_mut().zip(&out_cols) {
            c.spec = spec.clone();
        }
        batches.push(b);
    }
    Ok(VmTable {
        cols: out_cols,
        batches,
    })
}

/// Columnar `Redact(col, replacement)`.
pub fn op_redact(
    tbl: VmTable,
    col: &str,
    replacement: &str,
    pc: &TagSet,
    cfg: &OpExecConfig,
) -> Result<VmTable, OpErr> {
    let mode = cfg.mode;
    let Some(c_idx) = tbl.find_col_idx(col) else {
        if mode == VmMode::CoreV01 {
            return Err(OpErr::Wrong);
        }
        return Ok(tbl);
    };
    let out_cols: Vec<ColSpec> = tbl
        .cols
        .into_iter()
        .enumerate()
        .map(|(i, c)| {
            if i == c_idx {
                ColSpec {
                    ty: ScalarTy::Text,
                    tags: if mode == VmMode::CoreV01 {
                        pc.clone()
                    } else {
                        TagSet::empty()
                    },
                    bucketed: false,
                    agg_kind: if mode == VmMode::CoreV01 {
                        AggKind::Raw
                    } else {
                        c.agg_kind
                    },
                    ..c
                }
            } else if mode == VmMode::CoreV01 {
                ColSpec {
                    agg_kind: AggKind::Raw,
                    ..c
                }
            } else {
                c
            }
        })
        .collect();

    let total_rows = tbl.batches.iter().map(Batch::active_len).sum();
    let rep_bytes = replacement.as_bytes();
    let new_spec = out_cols[c_idx].clone();

    let batches = parallel_map_batches(
        tbl.batches,
        total_rows,
        cfg.parallel_threshold_rows,
        cfg.max_threads,
        |mut batch| -> Result<Batch, OpErr> {
            clear_group_meta_if_core(&mut batch, mode);
            let mut offsets = Vec::with_capacity(batch.len + 1);
            let mut data = Vec::with_capacity(batch.len * rep_bytes.len());
            offsets.push(0);
            for _ in 0..batch.len {
                data.extend_from_slice(rep_bytes);
                offsets.push(data.len());
            }
            batch.cols[c_idx] = Column {
                spec: new_spec.clone(),
                data: ColumnData::Text { offsets, data },
                validity: None,
            };
            if mode == VmMode::CoreV01 {
                for (c, spec) in batch.cols.iter_mut().zip(&out_cols) {
                    c.spec = spec.clone();
                }
            }
            Ok(batch)
        },
    )?;

    Ok(VmTable {
        cols: out_cols,
        batches,
    })
}

/// Vectorized parallel `Pseudonymize(col, secret)`.
pub fn op_pseudonymize(
    tbl: VmTable,
    col: &str,
    key_material: &str,
    pc: &TagSet,
    cfg: &OpExecConfig,
) -> Result<VmTable, OpErr> {
    let mode = cfg.mode;
    let Some(c_idx) = tbl.find_col_idx(col) else {
        if mode == VmMode::CoreV01 {
            return Err(OpErr::Wrong);
        }
        return Ok(tbl);
    };
    let out_cols: Vec<ColSpec> = tbl
        .cols
        .into_iter()
        .enumerate()
        .map(|(i, c)| {
            if i == c_idx {
                ColSpec {
                    ty: ScalarTy::Text,
                    tags: if mode == VmMode::CoreV01 {
                        c.tags.remove("pii").union(pc)
                    } else {
                        c.tags.remove("pii")
                    },
                    bucketed: false,
                    agg_kind: if mode == VmMode::CoreV01 {
                        AggKind::Raw
                    } else {
                        c.agg_kind
                    },
                    ..c
                }
            } else if mode == VmMode::CoreV01 {
                ColSpec {
                    agg_kind: AggKind::Raw,
                    ..c
                }
            } else {
                c
            }
        })
        .collect();

    let total_rows = tbl.batches.iter().map(Batch::active_len).sum();
    let pmode = if mode == VmMode::CoreV01 {
        PseudonymizeMode::CoreV01Fnv1a
    } else {
        cfg.pseudonymize_mode
    };
    let new_spec = out_cols[c_idx].clone();

    let batches = parallel_map_batches(
        tbl.batches,
        total_rows,
        cfg.parallel_threshold_rows,
        cfg.max_threads,
        |mut batch| -> Result<Batch, OpErr> {
            clear_group_meta_if_core(&mut batch, mode);
            let mut offsets = Vec::with_capacity(batch.len + 1);
            let mut data = Vec::with_capacity(batch.len * 36);
            offsets.push(0);
            for r in 0..batch.len {
                let v = batch.cols[c_idx].get_val(r);
                let tok = match pmode {
                    PseudonymizeMode::CoreV01Fnv1a => pseudonymize_token(key_material, &v),
                    PseudonymizeMode::HmacSha256 => {
                        hmac_sha256_pseudonym(key_material.as_bytes(), &v)
                    }
                };
                data.extend_from_slice(tok.as_bytes());
                offsets.push(data.len());
            }
            batch.cols[c_idx] = Column {
                spec: new_spec.clone(),
                data: ColumnData::Text { offsets, data },
                validity: None,
            };
            if mode == VmMode::CoreV01 {
                for (c, spec) in batch.cols.iter_mut().zip(&out_cols) {
                    c.spec = spec.clone();
                }
            }
            Ok(batch)
        },
    )?;

    Ok(VmTable {
        cols: out_cols,
        batches,
    })
}

/// Columnar `GroupBy` metadata tagger (marks `AggKind::GroupKey` in `CoreV01`).
#[must_use]
pub fn op_group_by(tbl: VmTable, keys: &[String], mode: VmMode) -> VmTable {
    if mode != VmMode::CoreV01 {
        return tbl;
    }
    let out_cols: Vec<ColSpec> = tbl
        .cols
        .into_iter()
        .map(|c| {
            let agg_kind = if keys.contains(&c.name) {
                AggKind::GroupKey
            } else {
                AggKind::Raw
            };
            ColSpec { agg_kind, ..c }
        })
        .collect();
    let batches = tbl
        .batches
        .into_iter()
        .map(|mut b| {
            b.group_meta = None;
            for (c, spec) in b.cols.iter_mut().zip(&out_cols) {
                c.spec = spec.clone();
            }
            b
        })
        .collect();
    VmTable {
        cols: out_cols,
        batches,
    }
}
