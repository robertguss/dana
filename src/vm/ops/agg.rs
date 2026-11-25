//! Vectorized Hash Aggregate (`GroupBy` + `Summarize`) across all 12 `AggOp`s and
//! small-group suppression (`SuppressSmallGroups` in `Drop` and `MaskComplementary` modes).
//!
//! Features:
//! - Zero-copy bare-column aggregate arguments (`AggArgSource::BatchCol`) and parallel
//!   computed expression evaluation across batches via `std::thread::scope`
//! - O(1)-memory unboxed streaming accumulators for `Count`, `CountDistinct(Int)`,
//!   `Sum(Int/Decimal/Float)`, `Mean(Int/Decimal/Float)`, `Min`, `Max`, `First`, `Last`
//!   with automatic exact sorted-sum fallback on extreme near-overflow values
//! - Zero-allocation columnar group lookup (`hash_row_key` + `eq_col_cells` against group
//!   exemplars) and deterministic radix hash partitioning for multi-core grouped aggregations
//! - Exact bit-for-bit parity with `Eval.lean` / `src/oracle/eval.rs` in `CoreV01` mode and
//!   `src/runtime/exec.rs` in `ExecSurface` mode.

use std::cmp::Ordering;
use std::collections::{HashMap, HashSet};
use std::hash::BuildHasherDefault;

use crate::core::bigint::{BigInt, DEC_MAX, DEC_MIN, DEC_SCALE};
use crate::core::syntax::{
    AggKind, AggOp, BugKind, ColSpec, Float64, Ident, ScalarTy, SuppressMode, TagSet,
};
use crate::oracle::eval::{
    mean_sorted_floats, median_sorted_floats, percentile_sorted_floats, stddev_sorted_floats,
    variance_sorted_floats,
};
use crate::oracle::value::{
    Bug, GroupMeta, TableRow, Val, render_decimal, val_cmp, val_eq, val_list_cmp, val_list_eq,
    val_list_lt, val_to_float,
};
use crate::runtime::ir::ExecAggOp;
use crate::vm::batch::{Batch, Column, ColumnData, rows_to_batches};
use crate::vm::expr::{RowEvalHost, RowInstr, RowProgram, eval_row_program};
use crate::vm::key::{FastHasher, KeyTuple, SingleKey, eq_col_cells, hash_row_key};
use crate::vm::ops::{OpErr, OpExecConfig, VmMode, VmTable};
use crate::vm::parallel::{parallel_map_batches, parallel_map_ref, resolve_thread_count};

type FastMap<K, V> = HashMap<K, V, BuildHasherDefault<FastHasher>>;
type FastSet<K> = HashSet<K, BuildHasherDefault<FastHasher>>;

/// Compiled specification for a single aggregate item inside `Summarize`.
#[derive(Debug)]
pub struct CompiledAgg {
    pub name: Ident,
    pub op: ExecAggOp,
    pub out_spec: ColSpec,
    pub arg_prog: Option<RowProgram>,
}

type GroupRowOut = (KeyTuple, usize, TableRow);
type GroupPartErr = (KeyTuple, usize, OpErr);
type PartAggResult = Result<Vec<GroupRowOut>, GroupPartErr>;

/// Detected uniform physical column type across all non-empty batches for one aggregate argument.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum AggColKind {
    Int,
    Decimal,
    Float,
    Other,
}

/// Distinct-key tracker for `SuppressSmallGroups(distinct_by: ...)`.
enum DistinctTracker {
    Int(FastSet<i64>),
    Generic(FastSet<SingleKey>),
}

impl DistinctTracker {
    fn new(kind: AggColKind) -> Self {
        if kind == AggColKind::Int {
            Self::Int(FastSet::default())
        } else {
            Self::Generic(FastSet::default())
        }
    }

    #[inline]
    fn push_cell(&mut self, col: &Column, row: usize) {
        if col.validity.as_ref().is_some_and(|bm| !bm.is_valid(row)) {
            return;
        }
        match (self, &col.data) {
            (Self::Int(set), ColumnData::Int(vs)) => {
                set.insert(vs[row]);
            }
            (Self::Generic(set), _) => {
                let v = col.get_val(row);
                if let Some(inner) = unwrap_opt_owned(v) {
                    set.insert(SingleKey::new(inner));
                }
            }
            (Self::Int(_), _) => {}
        }
    }

    fn len(&self) -> usize {
        match self {
            Self::Int(s) => s.len(),
            Self::Generic(s) => s.len(),
        }
    }
}

/// Fast per-group streaming accumulator for one aggregate column.
enum AggAcc {
    Count(usize),
    CountIf(usize),
    CountDistinctInt(FastSet<i64>),
    CountDistinct(FastSet<SingleKey>),
    /// `CoreV01` O(1) fast Int sum tracking `pos_sum` and `neg_sum` magnitudes separately.
    /// If either exceeds safe no-intermediate-overflow bounds, switches to sorted fallback
    /// matching `Eval.lean`!
    SumInt {
        pos_sum: u128,
        neg_sum: u128,
        overflow_buf: Option<Vec<i64>>,
    },
    /// `CoreV01` O(1) fast Decimal sum tracking positive/negative `u128` sums separately.
    SumDec {
        pos_sum: u128,
        neg_sum: u128,
        overflow_buf: Option<Vec<i128>>,
    },
    /// `ExecSurface` O(1) unboxed Int sum (zero `Val` / `BigInt` boxing).
    ExecSumInt {
        sum: i128,
        overflow: Option<BigInt>,
        seen_any: bool,
    },
    /// `ExecSurface` O(1) unboxed Decimal sum (zero `Val` / `BigInt` boxing).
    ExecSumDec {
        sum: i128,
        overflow: Option<BigInt>,
        seen_any: bool,
    },
    /// `ExecSurface` O(1) unboxed Float sum preserving exact left-to-right row order.
    ExecSumFloat {
        sum: f64,
        seen_any: bool,
    },
    /// `ExecSurface` O(1) unboxed Float/Int mean preserving exact left-to-right row order.
    ExecMeanFloat {
        sum: f64,
        count: usize,
    },
    /// `ExecSurface` O(1) unboxed Decimal mean with exact truncating division.
    ExecMeanDec {
        sum: i128,
        overflow: Option<BigInt>,
        count: usize,
    },
    /// Generic value collector (`CoreV01` float sum/mean/median/var/stddev/pct, `ExecSurface`
    /// median/var/stddev/pct, or heterogeneous columns).
    CollectVals(Vec<Val>),
    Min(Option<Val>),
    Max(Option<Val>),
    FirstCore(Option<Val>),
    LastCore(Option<Val>),
    FirstExec {
        set: bool,
        val: Option<Val>,
    },
    LastExec(Option<Val>),
}

impl AggAcc {
    fn new(op: ExecAggOp, out_ty: &ScalarTy, col_kind: AggColKind, mode: VmMode) -> Self {
        let cop = match op {
            ExecAggOp::CountIf => return Self::CountIf(0),
            ExecAggOp::Core(c) => c,
        };
        match cop {
            AggOp::Count => Self::Count(0),
            AggOp::CountDistinct => {
                if col_kind == AggColKind::Int {
                    Self::CountDistinctInt(FastSet::default())
                } else {
                    Self::CountDistinct(FastSet::default())
                }
            }
            AggOp::Sum if mode == VmMode::CoreV01 => match out_ty {
                ScalarTy::Int => Self::SumInt {
                    pos_sum: 0,
                    neg_sum: 0,
                    overflow_buf: None,
                },
                ScalarTy::Decimal => Self::SumDec {
                    pos_sum: 0,
                    neg_sum: 0,
                    overflow_buf: None,
                },
                _ => Self::CollectVals(Vec::new()),
            },
            AggOp::Sum => match col_kind {
                AggColKind::Int => Self::ExecSumInt {
                    sum: 0,
                    overflow: None,
                    seen_any: false,
                },
                AggColKind::Decimal => Self::ExecSumDec {
                    sum: 0,
                    overflow: None,
                    seen_any: false,
                },
                AggColKind::Float => Self::ExecSumFloat {
                    sum: 0.0,
                    seen_any: false,
                },
                AggColKind::Other => Self::CollectVals(Vec::new()),
            },
            AggOp::Mean if mode == VmMode::ExecSurface => match col_kind {
                AggColKind::Float | AggColKind::Int => Self::ExecMeanFloat { sum: 0.0, count: 0 },
                AggColKind::Decimal => Self::ExecMeanDec {
                    sum: 0,
                    overflow: None,
                    count: 0,
                },
                AggColKind::Other => Self::CollectVals(Vec::new()),
            },
            AggOp::Min => Self::Min(None),
            AggOp::Max => Self::Max(None),
            AggOp::First => {
                if mode == VmMode::CoreV01 {
                    Self::FirstCore(None)
                } else {
                    Self::FirstExec {
                        set: false,
                        val: None,
                    }
                }
            }
            AggOp::Last => {
                if mode == VmMode::CoreV01 {
                    Self::LastCore(None)
                } else {
                    Self::LastExec(None)
                }
            }
            AggOp::Mean
            | AggOp::Median
            | AggOp::Variance
            | AggOp::Stddev
            | AggOp::Percentile(_) => Self::CollectVals(Vec::new()),
        }
    }

    #[inline]
    fn push_int_fast(&mut self, v: i64) {
        match self {
            Self::SumInt {
                pos_sum,
                neg_sum,
                overflow_buf,
            } => {
                if let Some(buf) = overflow_buf {
                    buf.push(v);
                    return;
                }
                if v >= 0 {
                    *pos_sum = pos_sum.saturating_add(v as u128);
                } else {
                    *neg_sum = neg_sum.saturating_add(v.unsigned_abs() as u128);
                }
            }
            Self::ExecSumInt {
                sum,
                overflow,
                seen_any,
            } => {
                *seen_any = true;
                if let Some(big) = overflow {
                    *big = &*big + &BigInt::from(v);
                } else if let Some(next) = sum.checked_add(i128::from(v)) {
                    *sum = next;
                } else {
                    *overflow = Some(&BigInt::from(*sum) + &BigInt::from(v));
                }
            }
            Self::ExecMeanFloat { sum, count } => {
                *sum += v as f64;
                *count += 1;
            }
            Self::CountDistinctInt(set) => {
                set.insert(v);
            }
            _ => {}
        }
    }

    #[inline]
    fn push_dec_fast(&mut self, v: i128) {
        match self {
            Self::SumDec {
                pos_sum,
                neg_sum,
                overflow_buf,
            } => {
                if let Some(buf) = overflow_buf {
                    buf.push(v);
                    return;
                }
                if v >= 0 {
                    *pos_sum = pos_sum.saturating_add(v as u128);
                } else {
                    *neg_sum = neg_sum.saturating_add(v.unsigned_abs());
                }
            }
            Self::ExecSumDec {
                sum,
                overflow,
                seen_any,
            } => {
                *seen_any = true;
                if let Some(big) = overflow {
                    *big = &*big + &BigInt::from(v);
                } else if let Some(next) = sum.checked_add(v) {
                    *sum = next;
                } else {
                    *overflow = Some(&BigInt::from(*sum) + &BigInt::from(v));
                }
            }
            Self::ExecMeanDec {
                sum,
                overflow,
                count,
            } => {
                *count += 1;
                if let Some(big) = overflow {
                    *big = &*big + &BigInt::from(v);
                } else if let Some(next) = sum.checked_add(v) {
                    *sum = next;
                } else {
                    *overflow = Some(&BigInt::from(*sum) + &BigInt::from(v));
                }
            }
            _ => {}
        }
    }

    #[inline]
    fn push_float_fast(&mut self, v: f64) {
        match self {
            Self::ExecSumFloat { sum, seen_any } => {
                *seen_any = true;
                *sum += v;
            }
            Self::ExecMeanFloat { sum, count } => {
                *sum += v;
                *count += 1;
            }
            _ => {}
        }
    }

    fn push_val(&mut self, v: Val) {
        match self {
            Self::Count(n) => *n += 1,
            Self::CountIf(n) => {
                if matches!(unwrap_opt_owned(v), Some(Val::Bool(true))) {
                    *n += 1;
                }
            }
            Self::CountDistinctInt(set) => {
                if let Some(Val::Int(ref n)) = unwrap_opt_owned(v)
                    && let Some(x) = n.to_i64()
                {
                    set.insert(x);
                }
            }
            Self::CountDistinct(set) => {
                if let Some(inner) = unwrap_opt_owned(v) {
                    set.insert(SingleKey::new(inner));
                }
            }
            Self::SumInt { .. } | Self::ExecSumInt { .. } => {
                if let Some(Val::Int(ref n)) = unwrap_opt_owned(v)
                    && let Some(x) = n.to_i64()
                {
                    self.push_int_fast(x);
                }
            }
            Self::SumDec { .. } | Self::ExecSumDec { .. } | Self::ExecMeanDec { .. } => {
                if let Some(Val::Decimal(ref d)) = unwrap_opt_owned(v)
                    && let Some(x) = d.to_i128()
                {
                    self.push_dec_fast(x);
                }
            }
            Self::ExecSumFloat { .. } => {
                if let Some(Val::Float(f)) = unwrap_opt_owned(v) {
                    self.push_float_fast(f.to_f64());
                }
            }
            Self::ExecMeanFloat { .. } => {
                if let Some(inner) = unwrap_opt_owned(v)
                    && let Some(x) = val_to_f64_exec(&inner)
                {
                    self.push_float_fast(x);
                }
            }
            Self::CollectVals(vs) => {
                if let Some(inner) = unwrap_opt_owned(v) {
                    vs.push(inner);
                }
            }
            Self::Min(cur) => {
                if let Some(inner) = unwrap_opt_owned(v) {
                    match cur {
                        None => *cur = Some(inner),
                        Some(prev) if val_cmp(&inner, prev) == Ordering::Less => *cur = Some(inner),
                        Some(_) => {}
                    }
                }
            }
            Self::Max(cur) => {
                if let Some(inner) = unwrap_opt_owned(v) {
                    match cur {
                        None => *cur = Some(inner),
                        Some(prev) if val_cmp(&inner, prev) == Ordering::Greater => {
                            *cur = Some(inner);
                        }
                        Some(_) => {}
                    }
                }
            }
            Self::FirstCore(cur) => {
                if cur.is_none()
                    && let Some(inner) = unwrap_opt_owned(v)
                {
                    *cur = Some(inner);
                }
            }
            Self::LastCore(cur) => {
                if let Some(inner) = unwrap_opt_owned(v) {
                    *cur = Some(inner);
                }
            }
            Self::FirstExec { set, val } => {
                if !*set {
                    *set = true;
                    *val = unwrap_opt_owned(v);
                }
            }
            Self::LastExec(cur) => {
                *cur = unwrap_opt_owned(v);
            }
        }
    }

    fn finalize(
        self,
        op: ExecAggOp,
        out_ty: &ScalarTy,
        mode: VmMode,
        group_row_count: usize,
        fallback_raw_vals: Option<&[Val]>,
    ) -> Result<Val, OpErr> {
        match self {
            Self::Count(n) | Self::CountIf(n) => checked_int_usize(n),
            Self::CountDistinctInt(set) => checked_int_usize(set.len()),
            Self::CountDistinct(set) => checked_int_usize(set.len()),
            Self::SumInt {
                pos_sum,
                neg_sum,
                overflow_buf,
            } => {
                let max_pos = i64::MAX as u128;
                let max_neg = (i64::MAX as u128) + 1;
                if overflow_buf.is_none() && pos_sum <= max_pos && neg_sum <= max_neg {
                    let net = (pos_sum as i128) - (neg_sum as i128);
                    if let Ok(v) = i64::try_from(net) {
                        return Ok(Val::Int(BigInt::from(v)));
                    }
                }
                // Exact sorted right-to-left check matching `Eval.lean:sumSortedInts`.
                let mut xs: Vec<i64> = if let Some(buf) = overflow_buf {
                    buf
                } else if let Some(raw) = fallback_raw_vals {
                    raw.iter()
                        .filter_map(|v| match unwrap_opt_ref(v) {
                            Some(Val::Int(n)) => n.to_i64(),
                            _ => None,
                        })
                        .collect()
                } else {
                    Vec::new()
                };
                xs.sort_unstable();
                let mut acc = 0i64;
                for &x in xs.iter().rev() {
                    acc = x.checked_add(acc).ok_or_else(|| {
                        OpErr::Stopped(Bug {
                            kind: BugKind::IntOverflow,
                            message: "Int64 arithmetic overflow".to_string(),
                        })
                    })?;
                }
                Ok(Val::Int(BigInt::from(acc)))
            }
            Self::SumDec {
                pos_sum,
                neg_sum,
                overflow_buf,
            } => {
                let max_dec = DEC_MAX as u128;
                if overflow_buf.is_none() && pos_sum <= max_dec && neg_sum <= max_dec {
                    let net = (pos_sum as i128) - (neg_sum as i128);
                    return Ok(Val::Decimal(BigInt::from(net)));
                }
                let mut xs: Vec<i128> = if let Some(buf) = overflow_buf {
                    buf
                } else if let Some(raw) = fallback_raw_vals {
                    raw.iter()
                        .filter_map(|v| match unwrap_opt_ref(v) {
                            Some(Val::Decimal(d)) => d.to_i128(),
                            _ => None,
                        })
                        .collect()
                } else {
                    Vec::new()
                };
                xs.sort_unstable();
                let mut acc = 0i128;
                for &x in xs.iter().rev() {
                    acc = crate::vm::decimal::dec_add(x, acc).ok_or_else(|| {
                        OpErr::Stopped(Bug {
                            kind: BugKind::DecimalOverflow,
                            message: "Decimal arithmetic overflow".to_string(),
                        })
                    })?;
                }
                Ok(Val::Decimal(BigInt::from(acc)))
            }
            Self::ExecSumInt {
                sum,
                overflow,
                seen_any,
            } => {
                if !seen_any {
                    return Ok(Val::Int(BigInt::ZERO));
                }
                if let Some(big) = overflow {
                    if big.in_int64_range() {
                        Ok(Val::Int(big))
                    } else {
                        Err(OpErr::Stopped(Bug {
                            kind: BugKind::IntOverflow,
                            message: "sum Int64 overflow".to_string(),
                        }))
                    }
                } else if let Ok(v) = i64::try_from(sum) {
                    Ok(Val::Int(BigInt::from(v)))
                } else {
                    Err(OpErr::Stopped(Bug {
                        kind: BugKind::IntOverflow,
                        message: "sum Int64 overflow".to_string(),
                    }))
                }
            }
            Self::ExecSumDec {
                sum,
                overflow,
                seen_any,
            } => {
                if !seen_any {
                    return Ok(Val::Int(BigInt::ZERO));
                }
                if let Some(big) = overflow {
                    if big.in_decimal_range() {
                        Ok(Val::Decimal(big))
                    } else {
                        Err(OpErr::Stopped(Bug {
                            kind: BugKind::DecimalOverflow,
                            message: "sum Decimal overflow".to_string(),
                        }))
                    }
                } else if (DEC_MIN..=DEC_MAX).contains(&sum) {
                    Ok(Val::Decimal(BigInt::from(sum)))
                } else {
                    Err(OpErr::Stopped(Bug {
                        kind: BugKind::DecimalOverflow,
                        message: "sum Decimal overflow".to_string(),
                    }))
                }
            }
            Self::ExecSumFloat { sum, seen_any } => {
                if !seen_any {
                    Ok(Val::Int(BigInt::ZERO))
                } else {
                    Ok(Val::Float(Float64::from_f64(sum)))
                }
            }
            Self::ExecMeanFloat { sum, count } => {
                if count == 0 {
                    Ok(Val::OptNone)
                } else {
                    Ok(Val::OptSome(Box::new(Val::Float(Float64::from_f64(
                        sum / (count as f64),
                    )))))
                }
            }
            Self::ExecMeanDec {
                sum,
                overflow,
                count,
            } => {
                if count == 0 {
                    return Ok(Val::OptNone);
                }
                let q = if let Some(big) = overflow {
                    let denom = BigInt::from(count);
                    if big.is_negative() {
                        -big.abs().div_euclid(&denom).unwrap_or(BigInt::ZERO)
                    } else {
                        big.div_euclid(&denom).unwrap_or(BigInt::ZERO)
                    }
                } else {
                    BigInt::from(sum / (count as i128))
                };
                Ok(Val::OptSome(Box::new(Val::Decimal(q))))
            }
            Self::Min(opt)
            | Self::Max(opt)
            | Self::FirstCore(opt)
            | Self::LastCore(opt)
            | Self::FirstExec { val: opt, .. }
            | Self::LastExec(opt) => Ok(match opt {
                Some(v) => Val::OptSome(Box::new(v)),
                None => Val::OptNone,
            }),
            Self::CollectVals(mut non_null) => match op {
                ExecAggOp::Core(cop) => {
                    if mode == VmMode::CoreV01 {
                        finalize_core_vals(cop, out_ty, &mut non_null)
                    } else {
                        finalize_exec_vals(cop, &non_null, group_row_count)
                    }
                }
                ExecAggOp::CountIf => Err(OpErr::Wrong),
            },
        }
    }
}

fn checked_int_usize(n: usize) -> Result<Val, OpErr> {
    let b = BigInt::from(n);
    if b.in_int64_range() {
        Ok(Val::Int(b))
    } else {
        Err(OpErr::Stopped(Bug {
            kind: BugKind::IntOverflow,
            message: "Int64 arithmetic overflow".to_string(),
        }))
    }
}

fn unwrap_opt_owned(mut v: Val) -> Option<Val> {
    match &mut v {
        Val::OptNone => None,
        Val::OptSome(inner) => Some(std::mem::take(inner.as_mut())),
        _ => Some(v),
    }
}

fn unwrap_opt_ref(v: &Val) -> Option<&Val> {
    match v {
        Val::OptNone => None,
        Val::OptSome(inner) => Some(inner.as_ref()),
        other => Some(other),
    }
}

fn finalize_core_vals(op: AggOp, out_ty: &ScalarTy, non_null: &mut [Val]) -> Result<Val, OpErr> {
    non_null.sort_by(val_cmp);
    match op {
        AggOp::Sum => match out_ty {
            ScalarTy::Float => {
                let total = non_null
                    .iter()
                    .fold(0.0_f64, |acc, v| match val_to_float(v) {
                        Some(x) => acc + x,
                        None => acc,
                    });
                Ok(Val::Float(Float64::from_f64(total)))
            }
            _ => Err(OpErr::Wrong),
        },
        AggOp::Mean => {
            if non_null.is_empty() {
                return Ok(Val::OptNone);
            }
            match out_ty {
                ScalarTy::Option(inner) if **inner == ScalarTy::Decimal => {
                    let mut acc = 0i128;
                    for v in non_null.iter().rev() {
                        let Val::Decimal(d) = v else {
                            return Err(OpErr::Wrong);
                        };
                        let x = d.to_i128().ok_or(OpErr::Wrong)?;
                        acc = crate::vm::decimal::dec_add(x, acc).ok_or_else(|| {
                            OpErr::Stopped(Bug {
                                kind: BugKind::DecimalOverflow,
                                message: "Decimal arithmetic overflow".to_string(),
                            })
                        })?;
                    }
                    let avg = BigInt::from(acc)
                        .div_euclid(&BigInt::from(non_null.len()))
                        .unwrap_or(BigInt::ZERO);
                    if avg.in_decimal_range() {
                        Ok(Val::OptSome(Box::new(Val::Decimal(avg))))
                    } else {
                        Err(OpErr::Stopped(Bug {
                            kind: BugKind::DecimalOverflow,
                            message: "Decimal overflow in mean".to_string(),
                        }))
                    }
                }
                ScalarTy::Option(inner) if **inner == ScalarTy::Float => Ok(Val::OptSome(
                    Box::new(Val::Float(mean_sorted_floats(non_null))),
                )),
                _ => Err(OpErr::Wrong),
            }
        }
        AggOp::Median => {
            if non_null.is_empty() {
                return Ok(Val::OptNone);
            }
            match out_ty {
                ScalarTy::Option(inner) if **inner == ScalarTy::Decimal => {
                    let mid = non_null.len() / 2;
                    if non_null.len() % 2 == 1 {
                        match non_null.get(mid) {
                            Some(Val::Decimal(d)) => {
                                Ok(Val::OptSome(Box::new(Val::Decimal(d.clone()))))
                            }
                            _ => Err(OpErr::Wrong),
                        }
                    } else {
                        match (non_null.get(mid - 1), non_null.get(mid)) {
                            (Some(Val::Decimal(lo)), Some(Val::Decimal(hi))) => {
                                let two = BigInt::from(2i64);
                                let avg = (lo + hi).div_euclid(&two).unwrap_or(BigInt::ZERO);
                                if avg.in_decimal_range() {
                                    Ok(Val::OptSome(Box::new(Val::Decimal(avg))))
                                } else {
                                    Err(OpErr::Stopped(Bug {
                                        kind: BugKind::DecimalOverflow,
                                        message: "Decimal overflow in median".to_string(),
                                    }))
                                }
                            }
                            _ => Err(OpErr::Wrong),
                        }
                    }
                }
                ScalarTy::Option(inner) if **inner == ScalarTy::Float => Ok(Val::OptSome(
                    Box::new(Val::Float(median_sorted_floats(non_null))),
                )),
                _ => Err(OpErr::Wrong),
            }
        }
        AggOp::Variance => {
            if non_null.is_empty() {
                Ok(Val::OptNone)
            } else {
                Ok(Val::OptSome(Box::new(Val::Float(variance_sorted_floats(
                    non_null,
                )))))
            }
        }
        AggOp::Stddev => {
            if non_null.is_empty() {
                Ok(Val::OptNone)
            } else {
                Ok(Val::OptSome(Box::new(Val::Float(stddev_sorted_floats(
                    non_null,
                )))))
            }
        }
        AggOp::Percentile(p) => {
            if non_null.is_empty() {
                Ok(Val::OptNone)
            } else {
                Ok(Val::OptSome(Box::new(Val::Float(
                    percentile_sorted_floats(p, non_null),
                ))))
            }
        }
        _ => Err(OpErr::Wrong),
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

fn finalize_exec_vals(op: AggOp, non_null: &[Val], _row_count: usize) -> Result<Val, OpErr> {
    match op {
        AggOp::Sum => {
            if non_null.is_empty() {
                return Ok(Val::Int(BigInt::ZERO));
            }
            match &non_null[0] {
                Val::Int(_) => {
                    let mut acc = BigInt::ZERO;
                    for v in non_null {
                        if let Val::Int(n) = v {
                            acc = &acc + n;
                        }
                    }
                    if acc.in_int64_range() {
                        Ok(Val::Int(acc))
                    } else {
                        Err(OpErr::Stopped(Bug {
                            kind: BugKind::IntOverflow,
                            message: "sum Int64 overflow".to_string(),
                        }))
                    }
                }
                Val::Decimal(_) => {
                    let mut acc = BigInt::ZERO;
                    for v in non_null {
                        if let Val::Decimal(d) = v {
                            acc = &acc + d;
                        }
                    }
                    if acc.in_decimal_range() {
                        Ok(Val::Decimal(acc))
                    } else {
                        Err(OpErr::Stopped(Bug {
                            kind: BugKind::DecimalOverflow,
                            message: "sum Decimal overflow".to_string(),
                        }))
                    }
                }
                Val::Float(_) => {
                    let s: f64 = non_null
                        .iter()
                        .filter_map(|v| match v {
                            Val::Float(f) => Some(f.to_f64()),
                            _ => None,
                        })
                        .sum();
                    Ok(Val::Float(Float64::from_f64(s)))
                }
                _ => Err(OpErr::Failed("sum on non-numeric column".to_string())),
            }
        }
        AggOp::Mean => {
            if non_null.is_empty() {
                return Ok(Val::OptNone);
            }
            match &non_null[0] {
                Val::Decimal(_) => {
                    let mut acc = BigInt::ZERO;
                    for v in non_null {
                        if let Val::Decimal(d) = v {
                            acc = &acc + d;
                        }
                    }
                    let q = if acc.is_negative() {
                        -acc.abs()
                            .div_euclid(&BigInt::from(non_null.len()))
                            .unwrap_or(BigInt::ZERO)
                    } else {
                        acc.div_euclid(&BigInt::from(non_null.len()))
                            .unwrap_or(BigInt::ZERO)
                    };
                    Ok(Val::OptSome(Box::new(Val::Decimal(q))))
                }
                _ => {
                    let fs: Vec<f64> = non_null.iter().filter_map(val_to_f64_exec).collect();
                    let m = fs.iter().sum::<f64>() / (fs.len() as f64);
                    Ok(Val::OptSome(Box::new(Val::Float(Float64::from_f64(m)))))
                }
            }
        }
        AggOp::Stddev | AggOp::Variance => {
            if non_null.len() < 2 {
                return Ok(Val::OptNone);
            }
            let fs: Vec<f64> = non_null.iter().filter_map(val_to_f64_exec).collect();
            let mean = fs.iter().sum::<f64>() / (fs.len() as f64);
            let var =
                fs.iter().map(|&x| (x - mean) * (x - mean)).sum::<f64>() / ((fs.len() - 1) as f64);
            let res = if matches!(op, AggOp::Stddev) {
                var.sqrt()
            } else {
                var
            };
            Ok(Val::OptSome(Box::new(Val::Float(Float64::from_f64(res)))))
        }
        AggOp::Median | AggOp::Percentile(_) => {
            if non_null.is_empty() {
                return Ok(Val::OptNone);
            }
            let mut fs: Vec<f64> = non_null.iter().filter_map(val_to_f64_exec).collect();
            fs.sort_by(|a, b| a.total_cmp(b));
            let q = match op {
                AggOp::Percentile(f) => f.to_f64().clamp(0.0, 1.0),
                _ => 0.5,
            };
            let pos = q * ((fs.len() - 1) as f64);
            let lo = pos.floor() as usize;
            let hi = pos.ceil() as usize;
            let frac = pos - (lo as f64);
            let interp = fs[lo] * (1.0 - frac) + fs[hi] * frac;
            Ok(Val::OptSome(Box::new(Val::Float(Float64::from_f64(
                interp,
            )))))
        }
        _ => Err(OpErr::Failed(format!("unsupported agg `{op:?}`"))),
    }
}

/// Source for one aggregate argument inside a batch — avoids cloning bare column inputs!
enum AggArgSource {
    None,
    BatchCol(usize),
    Computed(Column),
}

/// Per-batch evaluated aggregate inputs.
struct EvalBatchAggInputs {
    batch: Batch,
    arg_cols: Vec<AggArgSource>,
    arg_errors: Vec<Option<(usize, OpErr)>>,
}

impl EvalBatchAggInputs {
    #[inline]
    fn arg_col(&self, ai: usize) -> Option<&Column> {
        match &self.arg_cols[ai] {
            AggArgSource::None => None,
            AggArgSource::BatchCol(ci) => Some(&self.batch.cols[*ci]),
            AggArgSource::Computed(col) => Some(col),
        }
    }
}

fn eval_batch_agg_args(
    batch: Batch,
    aggs: &[CompiledAgg],
    host: &dyn RowEvalHost,
) -> Result<EvalBatchAggInputs, OpErr> {
    let mut arg_cols = Vec::with_capacity(aggs.len());
    let mut arg_errors = Vec::with_capacity(aggs.len());
    for a in aggs {
        match &a.arg_prog {
            None => {
                arg_cols.push(AggArgSource::None);
                arg_errors.push(None);
            }
            Some(rp) => {
                // Zero-copy fast path for bare column references (`sum(.col)`, `mean(.col)`).
                if let [RowInstr::LoadCol { dst, name }] = rp.instrs.as_slice()
                    && *dst == rp.result_reg
                    && let Some(ci) = batch.find_col_idx(name)
                {
                    arg_cols.push(AggArgSource::BatchCol(ci));
                    arg_errors.push(None);
                    continue;
                }
                match eval_row_program(rp, &batch, host) {
                    Ok(reg) => {
                        arg_cols.push(AggArgSource::Computed(
                            reg.into_column(ColSpec::default(), batch.len),
                        ));
                        arg_errors.push(None);
                    }
                    Err(err) => {
                        let lane = match &err {
                            crate::vm::expr::RowEvalErr::Stopped { lane, .. } => *lane,
                            crate::vm::expr::RowEvalErr::Failed(_) => 0,
                        };
                        arg_cols.push(AggArgSource::None);
                        arg_errors.push(Some((lane, OpErr::from(err))));
                    }
                }
            }
        }
    }
    Ok(EvalBatchAggInputs {
        batch,
        arg_cols,
        arg_errors,
    })
}

fn col_data_agg_kind(data: &ColumnData) -> AggColKind {
    match data {
        ColumnData::Int(_) => AggColKind::Int,
        ColumnData::Decimal(_) => AggColKind::Decimal,
        ColumnData::Float(_) => AggColKind::Float,
        _ => AggColKind::Other,
    }
}

fn detect_agg_col_kinds(evaluated: &[EvalBatchAggInputs], n_aggs: usize) -> Vec<AggColKind> {
    let mut kinds = Vec::with_capacity(n_aggs);
    for ai in 0..n_aggs {
        let mut unified: Option<AggColKind> = None;
        for eb in evaluated {
            if eb.batch.is_empty() {
                continue;
            }
            let Some(col) = eb.arg_col(ai) else {
                unified = Some(AggColKind::Other);
                break;
            };
            let k = col_data_agg_kind(&col.data);
            match unified {
                None => unified = Some(k),
                Some(prev) if prev == k => {}
                Some(_) => {
                    unified = Some(AggColKind::Other);
                    break;
                }
            }
        }
        kinds.push(unified.unwrap_or(AggColKind::Other));
    }
    kinds
}

fn detect_batch_col_kind(evaluated: &[EvalBatchAggInputs], col_idx: usize) -> AggColKind {
    let mut unified: Option<AggColKind> = None;
    for eb in evaluated {
        if eb.batch.is_empty() {
            continue;
        }
        let k = col_data_agg_kind(&eb.batch.cols[col_idx].data);
        match unified {
            None => unified = Some(k),
            Some(prev) if prev == k => {}
            Some(_) => return AggColKind::Other,
        }
    }
    unified.unwrap_or(AggColKind::Other)
}

/// Group-level state inside a radix partition.
struct GroupState {
    key: KeyTuple,
    exemplar_bi: u32,
    exemplar_ri: u16,
    first_seen_order: usize,
    row_count: usize,
    distinct_tracker: Option<DistinctTracker>,
    accs: Vec<AggAcc>,
    /// Retained only if an Int/Dec sum enters near-overflow fallback.
    fallback_vals: Vec<Option<Vec<Val>>>,
}

/// Execute vectorized Hash Aggregate (`Summarize` over an optional `GroupBy`).
///
/// Uses parallel arg evaluation + deterministic radix hash partitioning across worker
/// threads when `total_rows >= parallel_threshold_rows`!
pub fn op_hash_aggregate(
    tbl: VmTable,
    group_keys: &[Ident],
    aggs: &[CompiledAgg],
    distinct_key: Option<&str>,
    out_cols: Vec<ColSpec>,
    host: &dyn RowEvalHost,
    cfg: &OpExecConfig,
) -> Result<VmTable, OpErr> {
    let mode = cfg.mode;
    let mut g_idxs = Vec::with_capacity(group_keys.len());
    for k in group_keys {
        let Some(ci) = tbl.find_col_idx(k) else {
            return Err(if mode == VmMode::CoreV01 {
                OpErr::Wrong
            } else {
                OpErr::Failed(format!("summarize: missing group key `{k}`"))
            });
        };
        g_idxs.push(ci);
    }
    let dk_idx = distinct_key.and_then(|dk| tbl.find_col_idx(dk));
    let total_rows = tbl.total_rows();

    // Empty-input ungrouped aggregation produces 1 summary row (matching both oracle & exec.rs).
    if total_rows == 0 && group_keys.is_empty() {
        if mode == VmMode::ExecSurface && aggs.is_empty() {
            return Ok(VmTable {
                cols: out_cols,
                batches: Vec::new(),
            });
        }
        let mut cells = Vec::with_capacity(aggs.len());
        for a in aggs {
            let acc = AggAcc::new(a.op, &a.out_spec.ty, AggColKind::Other, mode);
            cells.push(acc.finalize(a.op, &a.out_spec.ty, mode, 0, None)?);
        }
        let row = TableRow {
            cells,
            group_meta: Some(GroupMeta {
                row_count: 0,
                distinct_count: dk_idx.map(|_| 0),
            }),
        };
        return Ok(VmTable {
            batches: rows_to_batches(&out_cols, &[row], cfg.batch_size),
            cols: out_cols,
        });
    }
    if total_rows == 0 {
        return Ok(VmTable {
            cols: out_cols,
            batches: Vec::new(),
        });
    }

    // Stage 1: Evaluate all aggregate argument expressions per batch (parallel!).
    let evaluated = parallel_map_batches(
        tbl.batches,
        total_rows,
        cfg.parallel_threshold_rows,
        cfg.max_threads,
        |b| eval_batch_agg_args(b, aggs, host),
    )?;

    // Check if ANY batch had an argument evaluation error. If so, fall back to exact
    // deterministic group-sorted / first-seen per-row stop resolution so the reported
    // `Bug` matches the oracle 100% identically even across unsorted groups!
    let any_arg_err = evaluated
        .iter()
        .any(|eb| eb.arg_errors.iter().any(Option::is_some));
    if any_arg_err {
        return resolve_agg_with_arg_errors(&evaluated, &g_idxs, aggs, host, mode);
    }

    let arg_col_kinds = detect_agg_col_kinds(&evaluated, aggs.len());
    let dk_kind = dk_idx.map_or(AggColKind::Other, |ci| {
        detect_batch_col_kind(&evaluated, ci)
    });

    // Check if we can use the fast streaming ungrouped path (0 group keys).
    if group_keys.is_empty() {
        let mut accs: Vec<AggAcc> = aggs
            .iter()
            .zip(&arg_col_kinds)
            .map(|(a, &ck)| AggAcc::new(a.op, &a.out_spec.ty, ck, mode))
            .collect();
        let mut distinct_tracker = dk_idx.map(|_| DistinctTracker::new(dk_kind));
        let mut row_count = 0usize;

        for eb in &evaluated {
            let active = eb.batch.active_indices();
            row_count += active.len();
            if let (Some(didx), Some(dt)) = (dk_idx, &mut distinct_tracker) {
                let dcol = &eb.batch.cols[didx];
                for &r_u16 in &active {
                    dt.push_cell(dcol, usize::from(r_u16));
                }
            }
            for (ai, acc) in accs.iter_mut().enumerate() {
                feed_agg_column_slice(acc, eb.arg_col(ai), &active);
            }
        }

        let mut cells = Vec::with_capacity(aggs.len());
        for (ai, (a, acc)) in aggs.iter().zip(accs).enumerate() {
            let needs_fallback = matches!(
                acc,
                AggAcc::SumInt { pos_sum, neg_sum, .. }
                    if pos_sum > i64::MAX as u128 || neg_sum > (i64::MAX as u128) + 1
            ) || matches!(
                acc,
                AggAcc::SumDec { pos_sum, neg_sum, .. }
                    if pos_sum > DEC_MAX as u128 || neg_sum > DEC_MAX as u128
            );
            let fb = if needs_fallback {
                let mut vs = Vec::with_capacity(row_count);
                for eb in &evaluated {
                    if let Some(col) = eb.arg_col(ai) {
                        for &r_u16 in &eb.batch.active_indices() {
                            vs.push(col.get_val(usize::from(r_u16)));
                        }
                    }
                }
                Some(vs)
            } else {
                None
            };
            cells.push(acc.finalize(a.op, &a.out_spec.ty, mode, row_count, fb.as_deref())?);
        }
        let row = TableRow {
            cells,
            group_meta: Some(GroupMeta {
                row_count,
                distinct_count: distinct_tracker.map(|d| d.len()),
            }),
        };
        return Ok(VmTable {
            batches: rows_to_batches(&out_cols, &[row], cfg.batch_size),
            cols: out_cols,
        });
    }

    // Stage 2: Grouped Hash Aggregation with Radix Partitioning for Parallel Multi-Core Execution!
    let n_threads = resolve_thread_count(cfg.max_threads);
    let use_parallel =
        n_threads > 1 && total_rows >= cfg.parallel_threshold_rows && evaluated.len() >= 2;
    let num_parts = if use_parallel {
        n_threads.next_power_of_two().clamp(2, 16)
    } else {
        1
    };
    let part_mask = num_parts - 1;

    // Partition `(batch_idx, row_u16, global_row_order, key_hash)` into `num_parts` radix buckets.
    // Note: each bucket preserves exact global row order (so `First` / `Last` / float sum are 100% deterministic!).
    let cap_per_part = (total_rows / num_parts).saturating_add(64);
    let mut part_rows: Vec<Vec<(u32, u16, usize, u64)>> = (0..num_parts)
        .map(|_| Vec::with_capacity(cap_per_part))
        .collect();
    let mut global_order = 0usize;
    for (bi, eb) in evaluated.iter().enumerate() {
        let active = eb.batch.active_indices();
        for &r_u16 in &active {
            let ri = usize::from(r_u16);
            let h = hash_row_key(&eb.batch.cols, &g_idxs, ri);
            let p = (h as usize) & part_mask;
            part_rows[p].push((bi as u32, r_u16, global_order, h));
            global_order += 1;
        }
    }

    // Stage 3: Aggregate each radix partition independently (in parallel via `std::thread::scope`!).
    let part_results: Vec<PartAggResult> = parallel_map_ref(
        &part_rows,
        total_rows,
        cfg.parallel_threshold_rows,
        cfg.max_threads,
        |rows_in_part| -> Result<PartAggResult, OpErr> {
            Ok(aggregate_partition(
                rows_in_part,
                &evaluated,
                &g_idxs,
                dk_idx,
                dk_kind,
                aggs,
                &arg_col_kinds,
                mode,
            ))
        },
    )?;

    // Merge partition outputs & pick earliest deterministic stop if any partition overflowed.
    let mut earliest_err: Option<(KeyTuple, usize, OpErr)> = None;
    let mut all_groups: Vec<(KeyTuple, usize, TableRow)> = Vec::new();
    for pr in part_results {
        match pr {
            Ok(gs) => all_groups.extend(gs),
            Err((ekey, eorder, err)) => {
                let replace = match &earliest_err {
                    None => true,
                    Some((prev_key, prev_ord, _)) => {
                        if mode == VmMode::CoreV01 {
                            val_list_cmp(&ekey.vals, &prev_key.vals) == Ordering::Less
                        } else {
                            eorder < *prev_ord
                        }
                    }
                };
                if replace {
                    earliest_err = Some((ekey, eorder, err));
                }
            }
        }
    }
    if let Some((_, _, err)) = earliest_err {
        return Err(err);
    }

    // Deterministic output group ordering:
    // - `CoreV01`: sorted ascending by group key (`val_list_cmp`, matching `Eval.lean`)
    // - `ExecSurface`: first-seen order (`first_seen_order`, matching `src/runtime/exec.rs`).
    if mode == VmMode::CoreV01 {
        all_groups.sort_by(|a, b| val_list_cmp(&a.0.vals, &b.0.vals));
    } else {
        all_groups.sort_by_key(|g| g.1);
    }

    let out_rows: Vec<TableRow> = all_groups.into_iter().map(|(_, _, r)| r).collect();
    Ok(VmTable {
        batches: rows_to_batches(&out_cols, &out_rows, cfg.batch_size),
        cols: out_cols,
    })
}

#[expect(
    clippy::too_many_arguments,
    reason = "Partition worker receives pre-evaluated columnar batches, key indices, and detected column types"
)]
fn aggregate_partition(
    rows_in_part: &[(u32, u16, usize, u64)],
    evaluated: &[EvalBatchAggInputs],
    g_idxs: &[usize],
    dk_idx: Option<usize>,
    dk_kind: AggColKind,
    aggs: &[CompiledAgg],
    arg_col_kinds: &[AggColKind],
    mode: VmMode,
) -> PartAggResult {
    // Zero-allocation group lookup: hash -> candidate group indices compared directly via
    // `eq_col_cells` against each group's stored exemplar `(exemplar_bi, exemplar_ri)`.
    let mut group_buckets: FastMap<u64, Vec<usize>> = FastMap::default();
    let mut groups: Vec<GroupState> = Vec::new();

    for &(bi_u32, r_u16, g_ord, h) in rows_in_part {
        let bi = bi_u32 as usize;
        let ri = usize::from(r_u16);
        let eb = &evaluated[bi];

        let mut found_slot: Option<usize> = None;
        if let Some(cands) = group_buckets.get(&h) {
            for &slot in cands {
                let g = &groups[slot];
                let ex_eb = &evaluated[g.exemplar_bi as usize];
                let ex_ri = usize::from(g.exemplar_ri);
                if g_idxs
                    .iter()
                    .all(|&ci| eq_col_cells(&ex_eb.batch.cols[ci], ex_ri, &eb.batch.cols[ci], ri))
                {
                    found_slot = Some(slot);
                    break;
                }
            }
        }

        let g_slot = if let Some(slot) = found_slot {
            slot
        } else {
            let slot = groups.len();
            let key_vals: Vec<Val> = g_idxs
                .iter()
                .map(|&ci| eb.batch.cols[ci].get_val(ri))
                .collect();
            let kt = KeyTuple {
                vals: key_vals,
                hash: h,
            };
            group_buckets.entry(h).or_default().push(slot);
            groups.push(GroupState {
                key: kt,
                exemplar_bi: bi_u32,
                exemplar_ri: r_u16,
                first_seen_order: g_ord,
                row_count: 0,
                distinct_tracker: dk_idx.map(|_| DistinctTracker::new(dk_kind)),
                accs: aggs
                    .iter()
                    .zip(arg_col_kinds)
                    .map(|(a, &ck)| AggAcc::new(a.op, &a.out_spec.ty, ck, mode))
                    .collect(),
                fallback_vals: vec![None; aggs.len()],
            });
            slot
        };

        let g = &mut groups[g_slot];
        g.row_count += 1;
        if let (Some(didx), Some(dt)) = (dk_idx, &mut g.distinct_tracker) {
            dt.push_cell(&eb.batch.cols[didx], ri);
        }
        for (ai, acc) in g.accs.iter_mut().enumerate() {
            match eb.arg_col(ai) {
                None => acc.push_val(Val::Unit),
                Some(col) => feed_agg_single_cell(acc, col, ri),
            }
        }
    }

    // Sort groups inside this partition by canonical order BEFORE finalizing so if multiple
    // groups in this partition overflow, we return the earliest group's error!
    if mode == VmMode::CoreV01 {
        groups.sort_by(|a, b| val_list_cmp(&a.key.vals, &b.key.vals));
    }

    // Check if any group needs exact overflow-fallback values for `SumInt`/`SumDec`.
    let any_need_fb = groups.iter().any(|g| {
        g.accs.iter().any(|acc| {
            matches!(
                acc,
                AggAcc::SumInt { pos_sum, neg_sum, .. }
                    if *pos_sum > i64::MAX as u128 || *neg_sum > (i64::MAX as u128) + 1
            ) || matches!(
                acc,
                AggAcc::SumDec { pos_sum, neg_sum, .. }
                    if *pos_sum > DEC_MAX as u128 || *neg_sum > DEC_MAX as u128
            )
        })
    });
    if any_need_fb {
        let mut sorted_map: FastMap<KeyTuple, usize> =
            FastMap::with_capacity_and_hasher(groups.len(), BuildHasherDefault::default());
        for (idx, g) in groups.iter().enumerate() {
            sorted_map.insert(g.key.clone(), idx);
        }
        for &(bi_u32, r_u16, _, _) in rows_in_part {
            let eb = &evaluated[bi_u32 as usize];
            let ri = usize::from(r_u16);
            let kv: Vec<Val> = g_idxs
                .iter()
                .map(|&ci| eb.batch.cols[ci].get_val(ri))
                .collect();
            if let Some(&idx) = sorted_map.get(&KeyTuple::new(kv)) {
                let g = &mut groups[idx];
                for ai in 0..aggs.len() {
                    if let Some(col) = eb.arg_col(ai) {
                        g.fallback_vals[ai]
                            .get_or_insert_with(Vec::new)
                            .push(col.get_val(ri));
                    }
                }
            }
        }
    }

    let mut out = Vec::with_capacity(groups.len());
    for g in groups {
        let mut cells = g.key.vals.clone();
        for (ai, (a, acc)) in aggs.iter().zip(g.accs).enumerate() {
            match acc.finalize(
                a.op,
                &a.out_spec.ty,
                mode,
                g.row_count,
                g.fallback_vals[ai].as_deref(),
            ) {
                Ok(v) => cells.push(v),
                Err(e) => return Err((g.key, g.first_seen_order, e)),
            }
        }
        let gm = GroupMeta {
            row_count: g.row_count,
            distinct_count: g.distinct_tracker.map(|d| d.len()),
        };
        out.push((
            g.key,
            g.first_seen_order,
            TableRow {
                cells,
                group_meta: Some(gm),
            },
        ));
    }
    Ok(out)
}

#[inline]
fn feed_agg_single_cell(acc: &mut AggAcc, col: &Column, row: usize) {
    match acc {
        AggAcc::Count(n) => {
            *n += 1;
        }
        AggAcc::CountIf(n) => match &col.data {
            ColumnData::Bool(vs) => {
                if !col.validity.as_ref().is_some_and(|bm| !bm.is_valid(row)) && vs[row] != 0 {
                    *n += 1;
                }
            }
            _ => acc.push_val(col.get_val(row)),
        },
        AggAcc::CountDistinctInt(_) | AggAcc::SumInt { .. } | AggAcc::ExecSumInt { .. } => {
            if col.validity.as_ref().is_some_and(|bm| !bm.is_valid(row)) {
                return;
            }
            if let ColumnData::Int(vs) = &col.data {
                acc.push_int_fast(vs[row]);
            } else {
                acc.push_val(col.get_val(row));
            }
        }
        AggAcc::SumDec { .. } | AggAcc::ExecSumDec { .. } | AggAcc::ExecMeanDec { .. } => {
            if col.validity.as_ref().is_some_and(|bm| !bm.is_valid(row)) {
                return;
            }
            if let ColumnData::Decimal(vs) = &col.data {
                acc.push_dec_fast(vs[row]);
            } else {
                acc.push_val(col.get_val(row));
            }
        }
        AggAcc::ExecSumFloat { .. } => {
            if col.validity.as_ref().is_some_and(|bm| !bm.is_valid(row)) {
                return;
            }
            if let ColumnData::Float(vs) = &col.data {
                acc.push_float_fast(f64::from_bits(vs[row]));
            } else {
                acc.push_val(col.get_val(row));
            }
        }
        AggAcc::ExecMeanFloat { .. } => {
            if col.validity.as_ref().is_some_and(|bm| !bm.is_valid(row)) {
                return;
            }
            match &col.data {
                ColumnData::Float(vs) => acc.push_float_fast(f64::from_bits(vs[row])),
                ColumnData::Int(vs) => acc.push_int_fast(vs[row]),
                _ => acc.push_val(col.get_val(row)),
            }
        }
        _ => acc.push_val(col.get_val(row)),
    }
}

fn feed_agg_column_slice(acc: &mut AggAcc, col_opt: Option<&Column>, active: &[u16]) {
    let Some(col) = col_opt else {
        if let AggAcc::Count(n) = acc {
            *n += active.len();
        }
        return;
    };
    match (acc, &col.data, &col.validity) {
        (AggAcc::Count(n), _, _) => *n += active.len(),
        (AggAcc::CountIf(n), ColumnData::Bool(vs), None) => {
            for &l in active {
                if vs[usize::from(l)] != 0 {
                    *n += 1;
                }
            }
        }
        (AggAcc::CountIf(n), ColumnData::Bool(vs), Some(bm)) => {
            for &l in active {
                let r = usize::from(l);
                if bm.is_valid(r) && vs[r] != 0 {
                    *n += 1;
                }
            }
        }
        (
            acc @ (AggAcc::SumInt { .. }
            | AggAcc::ExecSumInt { .. }
            | AggAcc::CountDistinctInt(_)
            | AggAcc::ExecMeanFloat { .. }),
            ColumnData::Int(vs),
            None,
        ) => {
            for &l in active {
                acc.push_int_fast(vs[usize::from(l)]);
            }
        }
        (
            acc @ (AggAcc::SumInt { .. }
            | AggAcc::ExecSumInt { .. }
            | AggAcc::CountDistinctInt(_)
            | AggAcc::ExecMeanFloat { .. }),
            ColumnData::Int(vs),
            Some(bm),
        ) => {
            for &l in active {
                let r = usize::from(l);
                if bm.is_valid(r) {
                    acc.push_int_fast(vs[r]);
                }
            }
        }
        (
            acc @ (AggAcc::SumDec { .. } | AggAcc::ExecSumDec { .. } | AggAcc::ExecMeanDec { .. }),
            ColumnData::Decimal(vs),
            None,
        ) => {
            for &l in active {
                acc.push_dec_fast(vs[usize::from(l)]);
            }
        }
        (
            acc @ (AggAcc::SumDec { .. } | AggAcc::ExecSumDec { .. } | AggAcc::ExecMeanDec { .. }),
            ColumnData::Decimal(vs),
            Some(bm),
        ) => {
            for &l in active {
                let r = usize::from(l);
                if bm.is_valid(r) {
                    acc.push_dec_fast(vs[r]);
                }
            }
        }
        (
            acc @ (AggAcc::ExecSumFloat { .. } | AggAcc::ExecMeanFloat { .. }),
            ColumnData::Float(vs),
            None,
        ) => {
            for &l in active {
                acc.push_float_fast(f64::from_bits(vs[usize::from(l)]));
            }
        }
        (
            acc @ (AggAcc::ExecSumFloat { .. } | AggAcc::ExecMeanFloat { .. }),
            ColumnData::Float(vs),
            Some(bm),
        ) => {
            for &l in active {
                let r = usize::from(l);
                if bm.is_valid(r) {
                    acc.push_float_fast(f64::from_bits(vs[r]));
                }
            }
        }
        (acc, _, _) => {
            for &l in active {
                acc.push_val(col.get_val(usize::from(l)));
            }
        }
    }
}

/// Rare slow path invoked ONLY when an aggregate's row expression trapped on at least one row.
/// Evaluates groups in exact oracle order (`sorted_keys` for `CoreV01`, first-seen for `ExecSurface`)
/// so the exact earliest-group, earliest-agg, earliest-row `Bug` is reported identically to the oracle.
fn resolve_agg_with_arg_errors(
    evaluated: &[EvalBatchAggInputs],
    g_idxs: &[usize],
    aggs: &[CompiledAgg],
    host: &dyn RowEvalHost,
    mode: VmMode,
) -> Result<VmTable, OpErr> {
    let mut group_order: Vec<(KeyTuple, Vec<(usize, u16)>)> = Vec::new();
    let mut g_map: HashMap<KeyTuple, usize> = HashMap::new();
    for (bi, eb) in evaluated.iter().enumerate() {
        for &r_u16 in &eb.batch.active_indices() {
            let ri = usize::from(r_u16);
            let kv: Vec<Val> = g_idxs
                .iter()
                .map(|&ci| eb.batch.cols[ci].get_val(ri))
                .collect();
            let kt = KeyTuple::new(kv);
            if let Some(&slot) = g_map.get(&kt) {
                group_order[slot].1.push((bi, r_u16));
            } else {
                let slot = group_order.len();
                g_map.insert(kt.clone(), slot);
                group_order.push((kt, vec![(bi, r_u16)]));
            }
        }
    }
    if mode == VmMode::CoreV01 {
        group_order.sort_by(|a, b| val_list_cmp(&a.0.vals, &b.0.vals));
    }

    for (_, rows) in &group_order {
        for a in aggs {
            let Some(rp) = &a.arg_prog else { continue };
            for &(bi, r_u16) in rows {
                let single_row_batch = Batch {
                    cols: evaluated[bi].batch.cols.clone(),
                    len: evaluated[bi].batch.len,
                    selection: Some(vec![r_u16]),
                    group_meta: None,
                };
                eval_row_program(rp, &single_row_batch, host)?;
            }
        }
    }
    Err(OpErr::Failed(
        "aggregate argument error unexpectedly disappeared on re-evaluation".to_string(),
    ))
}

// ===========================================================================
// `SuppressSmallGroups` (Drop & MaskComplementary)
// ===========================================================================

fn suppress_group_size(distinct_by: &Option<Ident>, gm: Option<GroupMeta>, mode: VmMode) -> usize {
    match (distinct_by, gm) {
        (Some(_), Some(m)) => {
            if mode == VmMode::CoreV01 {
                m.distinct_count.unwrap_or(0)
            } else {
                m.distinct_count.unwrap_or(m.row_count)
            }
        }
        (None, Some(m)) => m.row_count,
        (_, None) => 0,
    }
}

/// Columnar `SuppressSmallGroups` supporting both `SuppressMode::Drop` and
/// `SuppressMode::MaskComplementary` (secondary cell suppression of the smallest
/// surviving group whenever `sum(small_groups) < min_k`).
#[must_use]
pub fn op_suppress_small_groups(
    tbl: VmTable,
    min_k: &BigInt,
    distinct_by: &Option<Ident>,
    suppress_mode: SuppressMode,
    pc: &TagSet,
    cfg: &OpExecConfig,
) -> VmTable {
    let vm_mode = cfg.mode;
    let out_cols: Vec<ColSpec> = tbl
        .cols
        .iter()
        .map(|c| {
            let orig_kind = c.agg_kind;
            let base = if vm_mode == VmMode::CoreV01 {
                match orig_kind {
                    AggKind::GroupKey => {
                        if c.bucketed {
                            ColSpec {
                                tags: pc.clone(),
                                agg_kind: AggKind::Raw,
                                ..c.clone()
                            }
                        } else {
                            ColSpec {
                                agg_kind: AggKind::Raw,
                                ..c.clone()
                            }
                        }
                    }
                    AggKind::Blending => ColSpec {
                        tags: pc.clone(),
                        agg_kind: AggKind::Raw,
                        ..c.clone()
                    },
                    AggKind::NonBlending | AggKind::Raw => ColSpec {
                        agg_kind: AggKind::Raw,
                        ..c.clone()
                    },
                }
            } else {
                c.clone()
            };
            match (suppress_mode, orig_kind) {
                (SuppressMode::MaskComplementary, AggKind::Blending | AggKind::NonBlending) => {
                    ColSpec {
                        ty: crate::core::check::ensure_option_scalar(&base.ty),
                        bucketed: false,
                        ..base
                    }
                }
                _ => base,
            }
        })
        .collect();

    let orig_cols = tbl.cols.clone();
    let tv = tbl.into_table_val();

    match suppress_mode {
        SuppressMode::Drop => {
            let kept: Vec<TableRow> = tv
                .rows
                .into_iter()
                .filter(|r| {
                    BigInt::from(suppress_group_size(distinct_by, r.group_meta, vm_mode)) >= *min_k
                })
                .map(|r| TableRow {
                    cells: r.cells,
                    group_meta: None,
                })
                .collect();
            VmTable {
                batches: rows_to_batches(&out_cols, &kept, cfg.batch_size),
                cols: out_cols,
            }
        }
        SuppressMode::MaskComplementary => {
            let key_idxs: Vec<usize> = orig_cols
                .iter()
                .enumerate()
                .filter(|(_, c)| c.agg_kind == AggKind::GroupKey)
                .map(|(i, _)| i)
                .collect();

            let mut has_small = false;
            let mut small_sum = BigInt::ZERO;
            for r in &tv.rows {
                let sz = BigInt::from(suppress_group_size(distinct_by, r.group_meta, vm_mode));
                if sz < *min_k {
                    has_small = true;
                    small_sum = &small_sum + &sz;
                }
            }

            let comp_key: Option<Vec<Val>> = if has_small && small_sum < *min_k {
                let mut valid: Vec<&TableRow> = tv
                    .rows
                    .iter()
                    .filter(|r| {
                        BigInt::from(suppress_group_size(distinct_by, r.group_meta, vm_mode))
                            >= *min_k
                    })
                    .collect();
                valid.sort_by(|a, b| {
                    let sa = suppress_group_size(distinct_by, a.group_meta, vm_mode);
                    let sb = suppress_group_size(distinct_by, b.group_meta, vm_mode);
                    sa.cmp(&sb).then_with(|| {
                        let ka: Vec<Val> = key_idxs.iter().map(|&i| a.cells[i].clone()).collect();
                        let kb: Vec<Val> = key_idxs.iter().map(|&i| b.cells[i].clone()).collect();
                        if val_list_lt(&ka, &kb) {
                            Ordering::Less
                        } else if val_list_lt(&kb, &ka) {
                            Ordering::Greater
                        } else {
                            Ordering::Equal
                        }
                    })
                });
                valid
                    .first()
                    .map(|r| key_idxs.iter().map(|&i| r.cells[i].clone()).collect())
            } else {
                None
            };

            let out_rows: Vec<TableRow> = tv
                .rows
                .iter()
                .map(|r| {
                    let sz = BigInt::from(suppress_group_size(distinct_by, r.group_meta, vm_mode));
                    let rk: Vec<Val> = key_idxs.iter().map(|&i| r.cells[i].clone()).collect();
                    let should_mask =
                        sz < *min_k || comp_key.as_ref().is_some_and(|ck| val_list_eq(&rk, ck));
                    let cells = orig_cols
                        .iter()
                        .zip(&r.cells)
                        .map(|(c, v)| {
                            if matches!(c.agg_kind, AggKind::Blending | AggKind::NonBlending) {
                                if should_mask {
                                    Val::OptNone
                                } else if vm_mode == VmMode::CoreV01 {
                                    if c.ty.is_option() {
                                        v.clone()
                                    } else {
                                        Val::OptSome(Box::new(v.clone()))
                                    }
                                } else {
                                    match v {
                                        Val::OptNone | Val::OptSome(_) => v.clone(),
                                        other => Val::OptSome(Box::new(other.clone())),
                                    }
                                }
                            } else {
                                v.clone()
                            }
                        })
                        .collect();
                    TableRow {
                        cells,
                        group_meta: None,
                    }
                })
                .collect();

            VmTable {
                batches: rows_to_batches(&out_cols, &out_rows, cfg.batch_size),
                cols: out_cols,
            }
        }
    }
}

const _: (i128, fn(&Val, &Val) -> bool) = (DEC_SCALE, val_eq);
