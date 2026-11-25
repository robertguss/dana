//! Columnar `Sort`, O(N) Hash `Distinct`, O(N log N) Hash-Partitioned `Window`
//! (all 6 `WindowFn`s), `FillGaps`, `PivotWider`, and `Crosstab`.

use std::cmp::Ordering;
use std::collections::{HashMap, HashSet};

use crate::core::bigint::{BigInt, INT64_MAX};
use crate::core::check::apply_window_item;
use crate::core::syntax::{
    AggKind, BugKind, ColSpec, Float64, Ident, Literal, ScalarTy, SortDir, TagSet, WindowFn,
    WindowItem,
};
use crate::oracle::eval::eval_literal;
use crate::oracle::value::{
    Bug, TableRow, Val, render_decimal, render_public_val, unwrap_numeric_float, val_cmp, val_eq,
    val_list_cmp, val_lt, val_to_float,
};
use crate::vm::batch::{Batch, rows_to_batches};
use crate::vm::key::{KeyTuple, eq_col_cells, hash_row_key};
use crate::vm::ops::{OpErr, OpExecConfig, VmMode, VmTable};

/// Stable deterministic `Sort` over columnar batches using zero-allocation columnar
/// key comparisons (`cmp_col_cells`) on `(batch_idx, row_idx)` coordinates!
#[must_use]
pub fn op_sort(tbl: VmTable, keys: &[(Ident, SortDir)], cfg: &OpExecConfig) -> VmTable {
    let mode = cfg.mode;
    let out_cols: Vec<ColSpec> = if mode == VmMode::CoreV01 {
        tbl.cols
            .iter()
            .map(|c| ColSpec {
                agg_kind: AggKind::Raw,
                ..c.clone()
            })
            .collect()
    } else {
        tbl.cols.clone()
    };

    let key_specs: Vec<(usize, SortDir)> = keys
        .iter()
        .filter_map(|(k, d)| tbl.find_col_idx(k).map(|i| (i, *d)))
        .collect();

    let total_rows = tbl.total_rows();
    if total_rows <= 1 || key_specs.is_empty() {
        let batches = tbl
            .batches
            .into_iter()
            .map(|mut b| {
                if mode == VmMode::CoreV01 {
                    b.group_meta = None;
                    for (c, spec) in b.cols.iter_mut().zip(&out_cols) {
                        c.spec = spec.clone();
                    }
                }
                b
            })
            .collect();
        return VmTable {
            cols: out_cols,
            batches,
        };
    }

    let mut coords: Vec<(u32, u16)> = Vec::with_capacity(total_rows);
    for (bi, b) in tbl.batches.iter().enumerate() {
        for &r_u16 in &b.active_indices() {
            coords.push((bi as u32, r_u16));
        }
    }

    // Rust's `slice::sort_by` is guaranteed stable (drift/timsort), matching `insertion_sort_by`!
    coords.sort_by(|&(ba, ra), &(bb, rb)| {
        let batch_a = &tbl.batches[ba as usize];
        let batch_b = &tbl.batches[bb as usize];
        let ria = usize::from(ra);
        let rib = usize::from(rb);
        for &(ci, dir) in &key_specs {
            let ord = crate::vm::key::cmp_col_cells(&batch_a.cols[ci], ria, &batch_b.cols[ci], rib);
            let directed = match dir {
                SortDir::Asc => ord,
                SortDir::Desc => ord.reverse(),
            };
            if directed != Ordering::Equal {
                return directed;
            }
        }
        Ordering::Equal
    });

    let mut out_rows = Vec::with_capacity(total_rows);
    for (bi, r_u16) in coords {
        let b = &tbl.batches[bi as usize];
        let ri = usize::from(r_u16);
        let cells = b.cols.iter().map(|c| c.get_val(ri)).collect();
        let group_meta = if mode == VmMode::CoreV01 {
            None
        } else {
            b.group_meta.as_ref().and_then(|gm| gm.get(ri).copied())
        };
        out_rows.push(TableRow { cells, group_meta });
    }
    VmTable {
        batches: rows_to_batches(&out_cols, &out_rows, cfg.batch_size),
        cols: out_cols,
    }
}

/// O(N) Hash `Distinct` preserving first-seen row order with zero-allocation key probes.
pub fn op_distinct(tbl: VmTable, cols: &[Ident], cfg: &OpExecConfig) -> Result<VmTable, OpErr> {
    let mode = cfg.mode;
    let out_cols: Vec<ColSpec> = if mode == VmMode::CoreV01 {
        tbl.cols
            .iter()
            .map(|c| ColSpec {
                agg_kind: AggKind::Raw,
                ..c.clone()
            })
            .collect()
    } else {
        tbl.cols.clone()
    };

    let key_idxs: Vec<usize> = if cols.is_empty() {
        (0..tbl.cols.len()).collect()
    } else {
        let mut idxs = Vec::with_capacity(cols.len());
        for c in cols {
            match tbl.find_col_idx(c) {
                Some(i) => idxs.push(i),
                None if mode == VmMode::CoreV01 => return Err(OpErr::Wrong),
                None => {}
            }
        }
        idxs
    };

    let mut seen: HashMap<u64, Vec<(u32, u16)>> = HashMap::new();
    let mut out_batches = Vec::with_capacity(tbl.batches.len());
    for (bi, b) in tbl.batches.iter().enumerate() {
        let active = b.active_indices();
        let mut kept = Vec::with_capacity(active.len());
        for &r_u16 in &active {
            let ri = usize::from(r_u16);
            let h = hash_row_key(&b.cols, &key_idxs, ri);
            let bucket = seen.entry(h).or_default();
            let dup = bucket.iter().any(|&(pbi, pri_u16)| {
                let pb = &tbl.batches[pbi as usize];
                let pri = usize::from(pri_u16);
                key_idxs
                    .iter()
                    .all(|&ki| eq_col_cells(&pb.cols[ki], pri, &b.cols[ki], ri))
            });
            if !dup {
                bucket.push((bi as u32, r_u16));
                kept.push(r_u16);
            }
        }
        if !kept.is_empty() {
            let mut nb = Batch {
                cols: b.cols.clone(),
                len: b.len,
                selection: Some(kept),
                group_meta: if mode == VmMode::CoreV01 {
                    None
                } else {
                    b.group_meta.clone()
                },
            }
            .compact();
            if mode == VmMode::CoreV01 {
                for (c, spec) in nb.cols.iter_mut().zip(&out_cols) {
                    c.spec = spec.clone();
                }
            }
            out_batches.push(nb);
        }
    }

    Ok(VmTable {
        cols: out_cols,
        batches: out_batches,
    })
}

fn clamp_int64_usize(n: usize) -> BigInt {
    let i = BigInt::from(n);
    if i.in_int64_range() {
        i
    } else {
        BigInt::from(INT64_MAX)
    }
}

fn default_val_for_scalar(ty: &ScalarTy) -> Val {
    match ty {
        ScalarTy::Unit => Val::Unit,
        ScalarTy::Bool => Val::Bool(false),
        ScalarTy::Int => Val::Int(BigInt::ZERO),
        ScalarTy::Decimal => Val::Decimal(BigInt::ZERO),
        ScalarTy::Float => Val::Float(Float64::ZERO),
        ScalarTy::Text => Val::Text(String::new()),
        ScalarTy::Bytes => Val::Bytes(Vec::new()),
        ScalarTy::Date => Val::Date(BigInt::ZERO),
        ScalarTy::Timestamp => Val::Timestamp(BigInt::ZERO),
        ScalarTy::Duration => Val::Duration(BigInt::ZERO),
        ScalarTy::Data(name) => Val::Ctor {
            type_name: name.clone(),
            ctor_name: String::new(),
            fields: Vec::new(),
        },
        ScalarTy::Option(_) => Val::OptNone,
    }
}

fn unwrap_opt_ref(v: &Val) -> Option<&Val> {
    match v {
        Val::OptNone => None,
        Val::OptSome(inner) => Some(inner.as_ref()),
        other => Some(other),
    }
}

/// O(N log N) Hash-Partitioned `Window` supporting all 6 `WindowFn`s
/// (`RowNumber`, `Rank`, `Lag`, `Lead`, `RunningSum`, `RollingMean`).
pub fn op_window(
    tbl: VmTable,
    items: &[WindowItem],
    final_out_cols: Option<Vec<ColSpec>>,
    cfg: &OpExecConfig,
) -> Result<VmTable, OpErr> {
    let mode = cfg.mode;
    let mut tv = tbl.into_table_val();
    if mode == VmMode::CoreV01 {
        for c in &mut tv.cols {
            c.agg_kind = AggKind::Raw;
        }
        for r in &mut tv.rows {
            r.group_meta = None;
        }
    }

    for item in items {
        let next_cols = if mode == VmMode::CoreV01 {
            apply_window_item(&tv.cols, &TagSet::empty(), item).map_err(|_| OpErr::Wrong)?
        } else {
            let mut cs = tv.cols.clone();
            cs.push(ColSpec {
                name: item.name.clone(),
                ty: ScalarTy::Unit,
                tags: TagSet::empty(),
                bucketed: false,
                agg_kind: AggKind::Raw,
            });
            cs
        };
        let target_ty = next_cols
            .iter()
            .find(|c| c.name == item.name)
            .map(|c| c.ty.clone())
            .unwrap_or(ScalarTy::Unit);
        let existing_idx = if mode == VmMode::CoreV01 {
            tv.cols.iter().position(|c| c.name == item.name)
        } else {
            None
        };

        let over_idxs: Vec<usize> = item
            .over
            .iter()
            .map(|c| {
                tv.cols.iter().position(|cs| cs.name == *c).ok_or_else(|| {
                    if mode == VmMode::CoreV01 {
                        OpErr::Wrong
                    } else {
                        OpErr::Failed(format!("window: missing over col `{c}`"))
                    }
                })
            })
            .collect::<Result<_, _>>()?;
        let order_specs: Vec<(usize, SortDir)> = item
            .order
            .iter()
            .filter_map(|(c, d)| tv.cols.iter().position(|cs| cs.name == *c).map(|i| (i, *d)))
            .collect();

        // Hash-partition row indices by `over` keys in O(N)!
        let mut part_map: HashMap<KeyTuple, usize> = HashMap::new();
        let mut parts: Vec<Vec<usize>> = Vec::new();
        for (ridx, row) in tv.rows.iter().enumerate() {
            let kv: Vec<Val> = over_idxs.iter().map(|&i| row.cells[i].clone()).collect();
            let kt = KeyTuple::new(kv);
            if let Some(&p) = part_map.get(&kt) {
                parts[p].push(ridx);
            } else {
                let p = parts.len();
                part_map.insert(kt, p);
                parts.push(vec![ridx]);
            }
        }

        let mut results = vec![Val::OptNone; tv.rows.len()];
        for mut ridxs in parts {
            if !order_specs.is_empty() {
                ridxs.sort_by(|&ia, &ib| {
                    for &(cidx, dir) in &order_specs {
                        let o = val_cmp(&tv.rows[ia].cells[cidx], &tv.rows[ib].cells[cidx]);
                        let d = match dir {
                            SortDir::Asc => o,
                            SortDir::Desc => o.reverse(),
                        };
                        if d != Ordering::Equal {
                            return d;
                        }
                    }
                    Ordering::Equal
                });
            }

            match &item.win_fn {
                WindowFn::RowNumber => {
                    for (pos, &ridx) in ridxs.iter().enumerate() {
                        results[ridx] = Val::Int(clamp_int64_usize(pos + 1));
                    }
                }
                WindowFn::Rank { col } => {
                    let Some(cidx) = tv.cols.iter().position(|c| c.name == *col) else {
                        return Err(if mode == VmMode::CoreV01 {
                            OpErr::Wrong
                        } else {
                            OpErr::Failed(format!("rank: missing col `{col}`"))
                        });
                    };
                    for (pos, &ridx) in ridxs.iter().enumerate() {
                        let cur = &tv.rows[ridx].cells[cidx];
                        let strictly_less = ridxs[..pos]
                            .iter()
                            .filter(|&&prev| val_lt(&tv.rows[prev].cells[cidx], cur))
                            .count();
                        results[ridx] = Val::Int(clamp_int64_usize(strictly_less + 1));
                    }
                }
                WindowFn::Lag { col, offset } => {
                    let Some(cidx) = tv.cols.iter().position(|c| c.name == *col) else {
                        return Err(if mode == VmMode::CoreV01 {
                            OpErr::Wrong
                        } else {
                            OpErr::Failed(format!("lag: missing col `{col}`"))
                        });
                    };
                    let col_is_opt = tv.cols[cidx].ty.is_option();
                    let off_opt = if mode == VmMode::CoreV01 {
                        offset.to_usize()
                    } else {
                        Some(offset.to_u64().unwrap_or(1) as usize)
                    };
                    for (pos, &ridx) in ridxs.iter().enumerate() {
                        results[ridx] = match off_opt {
                            Some(off) if pos >= off => {
                                let prev = tv.rows[ridxs[pos - off]].cells[cidx].clone();
                                if mode == VmMode::CoreV01 {
                                    if col_is_opt {
                                        prev
                                    } else {
                                        Val::OptSome(Box::new(prev))
                                    }
                                } else {
                                    match prev {
                                        Val::OptNone | Val::OptSome(_) => prev,
                                        other => Val::OptSome(Box::new(other)),
                                    }
                                }
                            }
                            _ => Val::OptNone,
                        };
                    }
                }
                WindowFn::Lead { col, offset } => {
                    let Some(cidx) = tv.cols.iter().position(|c| c.name == *col) else {
                        return Err(if mode == VmMode::CoreV01 {
                            OpErr::Wrong
                        } else {
                            OpErr::Failed(format!("lead: missing col `{col}`"))
                        });
                    };
                    let col_is_opt = tv.cols[cidx].ty.is_option();
                    let off_opt = if mode == VmMode::CoreV01 {
                        offset.to_usize()
                    } else {
                        Some(offset.to_u64().unwrap_or(1) as usize)
                    };
                    for (pos, &ridx) in ridxs.iter().enumerate() {
                        results[ridx] = match off_opt.and_then(|off| pos.checked_add(off)) {
                            Some(next_pos) if next_pos < ridxs.len() => {
                                let next_v = tv.rows[ridxs[next_pos]].cells[cidx].clone();
                                if mode == VmMode::CoreV01 {
                                    if col_is_opt {
                                        next_v
                                    } else {
                                        Val::OptSome(Box::new(next_v))
                                    }
                                } else {
                                    match next_v {
                                        Val::OptNone | Val::OptSome(_) => next_v,
                                        other => Val::OptSome(Box::new(other)),
                                    }
                                }
                            }
                            _ => Val::OptNone,
                        };
                    }
                }
                WindowFn::RunningSum { col } => {
                    let Some(cidx) = tv.cols.iter().position(|c| c.name == *col) else {
                        return Err(if mode == VmMode::CoreV01 {
                            OpErr::Wrong
                        } else {
                            OpErr::Failed(format!("running_sum: missing col `{col}`"))
                        });
                    };
                    if mode == VmMode::CoreV01 {
                        // Exact parity with `Eval.lean` / `src/oracle/eval.rs:1578-1589`.
                        let mut prefix_non_null: Vec<Val> = Vec::with_capacity(ridxs.len());
                        for &ridx in &ridxs {
                            if let Some(iv) = unwrap_opt_ref(&tv.rows[ridx].cells[cidx]) {
                                prefix_non_null.push(iv.clone());
                            }
                            let val = compute_core_running_sum(&target_ty, &prefix_non_null);
                            results[ridx] = val;
                        }
                    } else {
                        let mut acc_int: Option<BigInt> = None;
                        let mut acc_dec: Option<BigInt> = None;
                        let mut acc_flt: Option<f64> = None;
                        for &ridx in &ridxs {
                            if let Some(iv) = unwrap_opt_ref(&tv.rows[ridx].cells[cidx]) {
                                match iv {
                                    Val::Int(n) => {
                                        let next =
                                            acc_int.as_ref().map_or_else(|| n.clone(), |a| a + n);
                                        if !next.in_int64_range() {
                                            return Err(OpErr::Stopped(Bug {
                                                kind: BugKind::IntOverflow,
                                                message: "sum Int64 overflow".to_string(),
                                            }));
                                        }
                                        acc_int = Some(next);
                                    }
                                    Val::Decimal(d) => {
                                        let next =
                                            acc_dec.as_ref().map_or_else(|| d.clone(), |a| a + d);
                                        if !next.in_decimal_range() {
                                            return Err(OpErr::Stopped(Bug {
                                                kind: BugKind::DecimalOverflow,
                                                message: "sum Decimal overflow".to_string(),
                                            }));
                                        }
                                        acc_dec = Some(next);
                                    }
                                    Val::Float(f) => {
                                        acc_flt = Some(acc_flt.unwrap_or(0.0) + f.to_f64());
                                    }
                                    _ => {
                                        return Err(OpErr::Failed(
                                            "sum on non-numeric column".to_string(),
                                        ));
                                    }
                                }
                            }
                            results[ridx] = if let Some(ref i) = acc_int {
                                Val::Int(i.clone())
                            } else if let Some(ref d) = acc_dec {
                                Val::Decimal(d.clone())
                            } else if let Some(f) = acc_flt {
                                Val::Float(Float64::from_f64(f))
                            } else {
                                Val::Int(BigInt::ZERO)
                            };
                        }
                    }
                }
                WindowFn::RollingMean { col, window_size } => {
                    let Some(cidx) = tv.cols.iter().position(|c| c.name == *col) else {
                        return Err(if mode == VmMode::CoreV01 {
                            OpErr::Wrong
                        } else {
                            OpErr::Failed(format!("rolling_mean: missing col `{col}`"))
                        });
                    };
                    let w_sz = if mode == VmMode::CoreV01 {
                        window_size.to_usize_saturating()
                    } else {
                        window_size.to_u64().unwrap_or(1).max(1) as usize
                    };
                    for (pos, &ridx) in ridxs.iter().enumerate() {
                        let end = pos + 1;
                        let start = end.saturating_sub(w_sz);
                        let floats: Vec<f64> = ridxs[start..end]
                            .iter()
                            .filter_map(|&i| {
                                if mode == VmMode::CoreV01 {
                                    unwrap_numeric_float(&tv.rows[i].cells[cidx])
                                } else {
                                    unwrap_opt_ref(&tv.rows[i].cells[cidx])
                                        .and_then(val_to_f64_exec)
                                }
                            })
                            .collect();
                        results[ridx] = if floats.is_empty() {
                            Val::OptNone
                        } else {
                            let total = floats.iter().copied().fold(0.0_f64, |acc, x| acc + x);
                            Val::OptSome(Box::new(Val::Float(Float64::from_f64(
                                total / (floats.len() as f64),
                            ))))
                        };
                    }
                }
            }
        }

        match existing_idx {
            Some(idx) => {
                for (row, val) in tv.rows.iter_mut().zip(results) {
                    row.cells[idx] = val;
                }
            }
            None => {
                for (row, val) in tv.rows.iter_mut().zip(results) {
                    row.cells.push(val);
                }
            }
        }
        tv.cols = next_cols;
    }

    let out_cols = final_out_cols.unwrap_or(tv.cols);
    Ok(VmTable {
        batches: rows_to_batches(&out_cols, &tv.rows, cfg.batch_size),
        cols: out_cols,
    })
}

fn compute_core_running_sum(target_ty: &ScalarTy, prefix_non_null: &[Val]) -> Val {
    let mut sorted = prefix_non_null.to_vec();
    sorted.sort_by(val_cmp);
    match target_ty {
        ScalarTy::Int => {
            let mut acc = 0i64;
            for v in sorted.iter().rev() {
                let Val::Int(n) = v else {
                    return default_val_for_scalar(target_ty);
                };
                let Some(x) = n.to_i64() else {
                    return default_val_for_scalar(target_ty);
                };
                match x.checked_add(acc) {
                    Some(next) => acc = next,
                    None => return default_val_for_scalar(target_ty),
                }
            }
            Val::Int(BigInt::from(acc))
        }
        ScalarTy::Decimal => {
            let mut acc = 0i128;
            for v in sorted.iter().rev() {
                let Val::Decimal(d) = v else {
                    return default_val_for_scalar(target_ty);
                };
                let Some(x) = d.to_i128() else {
                    return default_val_for_scalar(target_ty);
                };
                match crate::vm::decimal::dec_add(x, acc) {
                    Some(next) => acc = next,
                    None => return default_val_for_scalar(target_ty),
                }
            }
            Val::Decimal(BigInt::from(acc))
        }
        ScalarTy::Float => {
            let total = sorted.iter().fold(0.0_f64, |acc, v| match val_to_float(v) {
                Some(x) => acc + x,
                None => acc,
            });
            Val::Float(Float64::from_f64(total))
        }
        _ => default_val_for_scalar(target_ty),
    }
}

fn val_to_f64_exec(v: &Val) -> Option<f64> {
    match v {
        Val::Float(f) => Some(f.to_f64()),
        Val::Int(n) => n.to_i64().map(|x| x as f64),
        Val::Decimal(d) => render_decimal(d).parse::<f64>().ok(),
        _ => None,
    }
}

/// Columnar `FillGaps`:
/// - `CoreV01`: sorts by `(over..., col)` matching `Eval.lean` / `src/oracle/eval.rs`.
/// - `ExecSurface`: synthesizes missing timestamp/date rows at `step_micros` intervals matching `src/runtime/exec.rs`.
pub fn op_fill_gaps(
    tbl: VmTable,
    col: &str,
    step_micros: &BigInt,
    over: &[Ident],
    fill: &[(Ident, Literal)],
    final_out_cols: Option<Vec<ColSpec>>,
    cfg: &OpExecConfig,
) -> Result<VmTable, OpErr> {
    if cfg.mode == VmMode::CoreV01 {
        let mut sort_spec: Vec<(Ident, SortDir)> =
            over.iter().map(|k| (k.clone(), SortDir::Asc)).collect();
        sort_spec.push((col.to_string(), SortDir::Asc));
        let mut sorted = op_sort(tbl, &sort_spec, cfg);
        if let Some(cols) = final_out_cols {
            sorted.cols = cols;
        }
        return Ok(sorted);
    }

    let step = step_micros.to_i64().unwrap_or(1);
    let tv = tbl.into_table_val();
    let Some(t_idx) = tv.cols.iter().position(|c| c.name == col) else {
        return Err(OpErr::Failed(format!("fill_gaps: missing col `{col}`")));
    };
    if step <= 0 || tv.rows.is_empty() {
        return Ok(VmTable {
            batches: rows_to_batches(&tv.cols, &tv.rows, cfg.batch_size),
            cols: tv.cols,
        });
    }
    let over_idxs: Vec<usize> = over
        .iter()
        .filter_map(|c| tv.cols.iter().position(|cs| cs.name == *c))
        .collect();
    let fill_map: HashMap<&str, Val> = fill
        .iter()
        .map(|(k, l)| (k.as_str(), eval_literal(l)))
        .collect();

    let mut groups: Vec<(Vec<Val>, Vec<&TableRow>)> = Vec::new();
    let mut g_map: HashMap<KeyTuple, usize> = HashMap::new();
    for r in &tv.rows {
        let key: Vec<Val> = over_idxs.iter().map(|&i| r.cells[i].clone()).collect();
        let kt = KeyTuple::new(key.clone());
        if let Some(&slot) = g_map.get(&kt) {
            groups[slot].1.push(r);
        } else {
            let slot = groups.len();
            g_map.insert(kt, slot);
            groups.push((key, vec![r]));
        }
    }

    let mut out_rows = Vec::new();
    for (gkey, grows) in groups {
        let ts_vals: Vec<i64> = grows
            .iter()
            .filter_map(|r| match &r.cells[t_idx] {
                Val::Timestamp(t) => t.to_i64(),
                Val::Date(d) => d.to_i64(),
                _ => None,
            })
            .collect();
        let (Some(&min_t), Some(&max_t)) = (ts_vals.iter().min(), ts_vals.iter().max()) else {
            for r in grows {
                out_rows.push(r.clone());
            }
            continue;
        };
        let is_date = matches!(grows[0].cells[t_idx], Val::Date(_));
        let mut by_t: HashMap<i64, &TableRow> = HashMap::with_capacity(grows.len());
        for r in &grows {
            let tv_i = match &r.cells[t_idx] {
                Val::Timestamp(t) | Val::Date(t) => t.to_i64(),
                _ => None,
            };
            if let Some(ti) = tv_i {
                by_t.entry(ti).or_insert(r);
            }
        }
        let mut cur = min_t;
        while cur <= max_t {
            if let Some(existing) = by_t.get(&cur) {
                out_rows.push((*existing).clone());
            } else {
                let t_val = if is_date {
                    Val::Date(BigInt::from(cur))
                } else {
                    Val::Timestamp(BigInt::from(cur))
                };
                let mut cells = Vec::with_capacity(tv.cols.len());
                for (ci, cs) in tv.cols.iter().enumerate() {
                    if ci == t_idx {
                        cells.push(t_val.clone());
                    } else if let Some(pos) = over_idxs.iter().position(|&oi| oi == ci) {
                        cells.push(gkey[pos].clone());
                    } else if let Some(fv) = fill_map.get(cs.name.as_str()) {
                        cells.push(fv.clone());
                    } else {
                        cells.push(Val::OptNone);
                    }
                }
                out_rows.push(TableRow {
                    cells,
                    group_meta: None,
                });
            }
            match cur.checked_add(step) {
                Some(n) => cur = n,
                None => break,
            }
        }
    }

    Ok(VmTable {
        batches: rows_to_batches(&tv.cols, &out_rows, cfg.batch_size),
        cols: tv.cols,
    })
}

fn format_display_val_pivot(v: &Val) -> String {
    match v {
        Val::Text(s) => s.clone(),
        Val::Date(d) => d
            .to_i64()
            .map_or_else(|| d.to_string(), crate::formats::time::format_iso_date),
        Val::Timestamp(ts) => ts.to_i64().map_or_else(
            || ts.to_string(),
            crate::formats::time::format_iso_timestamp,
        ),
        Val::Decimal(d) => render_decimal(d),
        Val::Float(f) => format!("{}", f.to_f64()),
        Val::OptNone => "none".to_string(),
        Val::OptSome(inner) => format_display_val_pivot(inner),
        other => render_public_val(other),
    }
}

/// Hash-indexed `PivotWider` (O(N) instead of O(N^2)).
pub fn op_pivot_wider(
    tbl: VmTable,
    names_from: &str,
    values_from: &str,
    static_cols: &[Ident],
    fill: &Literal,
    final_out_cols: Option<Vec<ColSpec>>,
    cfg: &OpExecConfig,
) -> Result<VmTable, OpErr> {
    let mode = cfg.mode;
    let tv = tbl.into_table_val();
    let (Some(n_idx), Some(v_idx)) = (
        tv.cols.iter().position(|c| c.name == names_from),
        tv.cols.iter().position(|c| c.name == values_from),
    ) else {
        return Err(if mode == VmMode::CoreV01 {
            OpErr::Wrong
        } else {
            OpErr::Failed("pivot_wider: missing names_from/values_from".to_string())
        });
    };

    let key_idxs: Vec<usize> = (0..tv.cols.len())
        .filter(|&i| i != n_idx && i != v_idx)
        .collect();
    let out_cols = final_out_cols.unwrap_or_else(|| {
        let mut cs: Vec<ColSpec> = key_idxs.iter().map(|&i| tv.cols[i].clone()).collect();
        let val_spec = tv.cols[v_idx].clone();
        for sc in static_cols {
            cs.push(ColSpec {
                name: sc.clone(),
                ty: val_spec.ty.clone(),
                tags: val_spec.tags.clone(),
                bucketed: false,
                agg_kind: AggKind::Raw,
            });
        }
        cs
    });

    let fill_val = eval_literal(fill);
    let col_pos_map: HashMap<&str, usize> = static_cols
        .iter()
        .enumerate()
        .map(|(i, s)| (s.as_str(), i))
        .collect();

    let mut groups: Vec<(KeyTuple, Vec<Option<Val>>)> = Vec::new();
    let mut g_map: HashMap<KeyTuple, usize> = HashMap::new();

    for r in &tv.rows {
        let kv: Vec<Val> = key_idxs.iter().map(|&i| r.cells[i].clone()).collect();
        let kt = KeyTuple::new(kv);
        let slot = if let Some(&s) = g_map.get(&kt) {
            s
        } else {
            let s = groups.len();
            g_map.insert(kt.clone(), s);
            groups.push((kt, vec![None; static_cols.len()]));
            s
        };
        if mode == VmMode::CoreV01 {
            // CoreV01 matches first occurrence (`find`) and strictly checks `Val::Text`.
            if let Val::Text(col_name) = &r.cells[n_idx]
                && let Some(&pos) = col_pos_map.get(col_name.as_str())
                && groups[slot].1[pos].is_none()
            {
                groups[slot].1[pos] = Some(r.cells[v_idx].clone());
            }
        } else {
            // ExecSurface overwrites with last occurrence and formats display string.
            let col_name = format_display_val_pivot(&r.cells[n_idx]);
            if let Some(&pos) = col_pos_map.get(col_name.as_str()) {
                groups[slot].1[pos] = Some(r.cells[v_idx].clone());
            }
        }
    }

    if mode == VmMode::CoreV01 {
        groups.sort_by(|a, b| val_list_cmp(&a.0.vals, &b.0.vals));
    }

    let out_rows: Vec<TableRow> = groups
        .into_iter()
        .map(|(kt, vals)| {
            let mut cells = kt.vals;
            for v in vals {
                cells.push(v.unwrap_or_else(|| fill_val.clone()));
            }
            TableRow {
                cells,
                group_meta: None,
            }
        })
        .collect();

    Ok(VmTable {
        batches: rows_to_batches(&out_cols, &out_rows, cfg.batch_size),
        cols: out_cols,
    })
}

fn coerce_pivot_cell(val: Val, target: &ScalarTy) -> Val {
    match (&val, target) {
        (Val::OptNone, ScalarTy::Option(_)) => Val::OptNone,
        (Val::OptSome(inner), ScalarTy::Option(t)) => {
            Val::OptSome(Box::new(coerce_pivot_cell(inner.as_ref().clone(), t)))
        }
        (_, ScalarTy::Option(t)) => Val::OptSome(Box::new(coerce_pivot_cell(val, t))),
        (Val::Int(n), ScalarTy::Decimal) => {
            Val::Decimal(n * &crate::core::bigint::BigInt::from(crate::core::bigint::DEC_SCALE))
        }
        (Val::Int(n), ScalarTy::Float) => Val::Float(crate::core::syntax::Float64::from_f64(
            n.to_i64().unwrap_or(0) as f64,
        )),
        (Val::Decimal(d), ScalarTy::Float) => Val::Float(crate::core::syntax::Float64::from_f64(
            render_decimal(d).parse::<f64>().unwrap_or(0.0),
        )),
        _ => val,
    }
}

/// Columnar `PivotLonger` unpivoting `cols` into `(names_to, values_to)` with exact
/// scalar type coercion and sensitivity tag propagation.
pub fn op_pivot_longer(
    tbl: VmTable,
    cols: &[Ident],
    names_to: &str,
    values_to: &str,
    value_ty: &ScalarTy,
    value_tags: &crate::core::syntax::TagSet,
    cfg: &OpExecConfig,
) -> Result<VmTable, OpErr> {
    let tv = tbl.into_table_val();
    let mut melt_idxs = Vec::with_capacity(cols.len());
    let mut eff_val_tags = value_tags.clone();
    for cn in cols {
        let Some(idx) = tv.cols.iter().position(|c| &c.name == cn) else {
            return Err(OpErr::Failed(format!(
                "pivot_longer: missing column `{cn}`"
            )));
        };
        eff_val_tags = eff_val_tags.union(&tv.cols[idx].tags);
        melt_idxs.push(idx);
    }
    let id_idxs: Vec<usize> = (0..tv.cols.len())
        .filter(|i| !melt_idxs.contains(i))
        .collect();

    let mut out_cols: Vec<ColSpec> = id_idxs
        .iter()
        .map(|&i| ColSpec {
            agg_kind: AggKind::Raw,
            ..tv.cols[i].clone()
        })
        .collect();
    out_cols.push(ColSpec {
        name: names_to.to_string(),
        ty: ScalarTy::Text,
        tags: crate::core::syntax::TagSet::empty(),
        bucketed: false,
        agg_kind: AggKind::Raw,
    });
    out_cols.push(ColSpec {
        name: values_to.to_string(),
        ty: value_ty.clone(),
        tags: eff_val_tags,
        bucketed: false,
        agg_kind: AggKind::Raw,
    });

    let mut out_rows = Vec::with_capacity(tv.rows.len().saturating_mul(cols.len()));
    for r in &tv.rows {
        let base_ids: Vec<Val> = id_idxs.iter().map(|&i| r.cells[i].clone()).collect();
        for (cn, &mi) in cols.iter().zip(&melt_idxs) {
            let mut cells = Vec::with_capacity(base_ids.len() + 2);
            cells.extend(base_ids.iter().cloned());
            cells.push(Val::Text(cn.clone()));
            cells.push(coerce_pivot_cell(r.cells[mi].clone(), value_ty));
            out_rows.push(TableRow {
                cells,
                group_meta: None,
            });
        }
    }

    Ok(VmTable {
        batches: rows_to_batches(&out_cols, &out_rows, cfg.batch_size),
        cols: out_cols,
    })
}

/// Hash-indexed `Crosstab` returning `Val::DynTable`.
pub fn op_crosstab(
    tbl: VmTable,
    rows_col: &str,
    cols_col: &str,
    values_col: &str,
    fill: &Literal,
    cfg: &OpExecConfig,
) -> Result<Val, OpErr> {
    let mode = cfg.mode;
    let tv = tbl.into_table_val();
    let (Some(ri), Some(ci), Some(vi)) = (
        tv.cols.iter().position(|c| c.name == rows_col),
        tv.cols.iter().position(|c| c.name == cols_col),
        tv.cols.iter().position(|c| c.name == values_col),
    ) else {
        return Err(if mode == VmMode::CoreV01 {
            OpErr::Wrong
        } else {
            OpErr::Failed("crosstab: missing columns".to_string())
        });
    };

    let fill_val = eval_literal(fill);
    if mode == VmMode::CoreV01 {
        let mut r_keys: Vec<Val> = Vec::new();
        let mut r_seen = HashSet::new();
        let mut c_keys: Vec<Val> = Vec::new();
        let mut c_seen = HashSet::new();
        let mut cell_map: HashMap<KeyTuple, Val> = HashMap::new();

        for r in &tv.rows {
            let rv = r.cells[ri].clone();
            let cv = r.cells[ci].clone();
            let r_sk = crate::vm::key::SingleKey::new(rv.clone());
            if r_seen.insert(r_sk) {
                r_keys.push(rv.clone());
            }
            let c_sk = crate::vm::key::SingleKey::new(cv.clone());
            if c_seen.insert(c_sk) {
                c_keys.push(cv.clone());
            }
            let pair_key = KeyTuple::new(vec![rv, cv]);
            cell_map
                .entry(pair_key)
                .or_insert_with(|| r.cells[vi].clone());
        }
        r_keys.sort_by(val_cmp);
        c_keys.sort_by(val_cmp);

        let mut headers = Vec::with_capacity(c_keys.len() + 1);
        headers.push(rows_col.to_string());
        headers.extend(c_keys.iter().map(render_public_val));

        let mut matrix = Vec::with_capacity(r_keys.len());
        for rk in &r_keys {
            let mut row = Vec::with_capacity(c_keys.len() + 1);
            row.push(rk.clone());
            for ck in &c_keys {
                let k = KeyTuple::new(vec![rk.clone(), ck.clone()]);
                row.push(
                    cell_map
                        .get(&k)
                        .cloned()
                        .unwrap_or_else(|| fill_val.clone()),
                );
            }
            matrix.push(row);
        }
        Ok(Val::DynTable {
            headers,
            rows: matrix,
        })
    } else {
        let mut dyn_cols: Vec<String> = Vec::new();
        let mut col_set: HashSet<String> = HashSet::new();
        let mut r_keys: Vec<Val> = Vec::new();
        let mut r_seen = HashSet::new();
        let mut cell_map: HashMap<(crate::vm::key::SingleKey, String), Val> = HashMap::new();

        for r in &tv.rows {
            let rv = r.cells[ri].clone();
            let cname = format_display_val_pivot(&r.cells[ci]);
            if col_set.insert(cname.clone()) {
                dyn_cols.push(cname.clone());
            }
            let r_sk = crate::vm::key::SingleKey::new(rv.clone());
            if r_seen.insert(r_sk.clone()) {
                r_keys.push(rv);
            }
            cell_map
                .entry((r_sk, cname))
                .or_insert_with(|| r.cells[vi].clone());
        }
        dyn_cols.sort();
        r_keys.sort_by(val_cmp);

        let mut headers = vec![rows_col.to_string()];
        headers.extend(dyn_cols.iter().cloned());

        let mut out_rows = Vec::with_capacity(r_keys.len());
        for rk in r_keys {
            let r_sk = crate::vm::key::SingleKey::new(rk.clone());
            let mut cells = vec![rk];
            for dc in &dyn_cols {
                cells.push(
                    cell_map
                        .get(&(r_sk.clone(), dc.clone()))
                        .cloned()
                        .unwrap_or_else(|| fill_val.clone()),
                );
            }
            out_rows.push(cells);
        }
        Ok(Val::DynTable {
            headers,
            rows: out_rows,
        })
    }
}

const _: fn(&Val, &Val) -> bool = val_eq;
