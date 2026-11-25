//! Deterministic fuel-indexed big-step evaluator for Dana Core IR v0.1.
//!
//! Mirrors `formal/DanaCore/Eval.lean` byte-for-byte, including:
//! - Euclidean integer division/modulo (`BigInt::div_euclid` / `rem_euclid`),
//! - Canonical IEEE-754 NaN bits (`0x7ff8_0000_0000_0000`) & scaled stats,
//! - FNV-1a 64-bit Unicode-scalar pseudonymization (`ps_<16-hex>`),
//! - Upfront `--allow-export` runtime gate and runtime path confinement,
//! - Complementary small-group suppression (`MaskComplementary`),
//! - Exact fuel-decrement parity with Lean `Eval.lean`.

use std::collections::HashMap;
use std::fmt;
use std::sync::Arc;

use crate::core::bigint::{BigInt, DEC_SCALE, INT64_MAX};
use crate::core::check::{
    PlanTy, apply_derive_item_arc, apply_window_item, build_joined_cols, check_expr_arc,
    check_plan_arc, check_program, infer_jump_pc_arc, is_safe_relative_path, join_confined_path,
    merge_union_cols, quarantine_bad_row_table_ty, resolve_join_pairs,
};
use crate::core::stack::with_large_stack;
use crate::core::syntax::{
    AggItem, AggKind, AggOp, BugKind, CaseArm, ColSpec, DeriveItem, Expr, Float64, HostOp, Ident,
    JoinKind, JoinOn, LTy, Literal, Plan, PrimOp, Program, RowExpr, ScalarTy, SortDir,
    SuppressMode, TableTy, TagSet, Ty, WindowFn, WindowItem,
};
use crate::oracle::value::{
    Bug, CapHandle, ChartVal, EnvEntry, EnvList, GroupMeta, ProfileColSummary, ProfileVal,
    ReportVal, TableRow, TableVal, Val, dedup_adjacent_by, format_diag_detail, insertion_sort_by,
    redact_tags, render_decimal, render_public_val, repr_bug_kind, repr_scalar_ty,
    unwrap_numeric_float, val_eq, val_list_eq, val_list_lt, val_lt, val_to_float,
};
use crate::oracle::world::{
    ExecReport, FakeConsoleState, FakeDBState, FakeFilesState, FakeHttpsState, Outcome,
    StoredTable, World, extract_report,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RuntimeError {
    pub message: String,
}

impl RuntimeError {
    #[must_use]
    pub fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
        }
    }
}

impl fmt::Display for RuntimeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.message)
    }
}

impl std::error::Error for RuntimeError {}

#[derive(Clone, Debug)]
pub enum PrimResult {
    Ok(Val),
    Stopped(Bug),
    OutOfFuel,
    Wrong,
}

// ---------------------------------------------------------------------------
// Pure Literal, Scalar & Primitive Evaluation
// ---------------------------------------------------------------------------

#[must_use]
pub fn eval_literal(lit: &Literal) -> Val {
    match lit {
        Literal::Unit => Val::Unit,
        Literal::Bool(b) => Val::Bool(*b),
        Literal::Int(n) => Val::Int(n.clone()),
        Literal::Decimal(d) => Val::Decimal(d.clone()),
        Literal::Float(f) => Val::Float(*f),
        Literal::Text(s) => Val::Text(s.clone()),
        Literal::Bytes(bs) => Val::Bytes(bs.clone()),
        Literal::Date(d) => Val::Date(d.clone()),
        Literal::Timestamp(ts) => Val::Timestamp(ts.clone()),
        Literal::Duration(dur) => Val::Duration(dur.clone()),
        Literal::NoneLit(_) => Val::OptNone,
    }
}

fn checked_int(n: BigInt) -> PrimResult {
    if n.in_int64_range() {
        PrimResult::Ok(Val::Int(n))
    } else {
        PrimResult::Stopped(Bug {
            kind: BugKind::IntOverflow,
            message: "Int64 arithmetic overflow".to_string(),
        })
    }
}

fn checked_decimal(d: BigInt) -> PrimResult {
    if d.in_decimal_range() {
        PrimResult::Ok(Val::Decimal(d))
    } else {
        PrimResult::Stopped(Bug {
            kind: BugKind::DecimalOverflow,
            message: "Decimal arithmetic overflow".to_string(),
        })
    }
}

fn is_ascii_space(c: char) -> bool {
    matches!(c, ' ' | '\t' | '\n' | '\r')
}

fn trim_ascii_string(s: &str) -> String {
    s.trim_matches(is_ascii_space).to_string()
}

/// Truncate proleptic Gregorian days since `1970-01-01` to the 1st of its month,
/// matching `Eval.lean:dateTruncMonthDays` with Euclidean division.
#[must_use]
pub fn date_trunc_month_days(days: &BigInt) -> BigInt {
    let c_719468 = BigInt::from(719_468i64);
    let c_146097 = BigInt::from(146_097i64);
    let c_146096 = BigInt::from(146_096i64);
    let c_1460 = BigInt::from(1_460i64);
    let c_36524 = BigInt::from(36_524i64);
    let c_365 = BigInt::from(365i64);
    let c_4 = BigInt::from(4i64);
    let c_100 = BigInt::from(100i64);
    let c_5 = BigInt::from(5i64);
    let c_2 = BigInt::from(2i64);
    let c_153 = BigInt::from(153i64);

    let div = |a: &BigInt, b: &BigInt| a.div_euclid(b).unwrap_or(BigInt::ZERO);

    let z = days + &c_719468;
    let era = if !z.is_negative() {
        div(&z, &c_146097)
    } else {
        div(&(&z - &c_146096), &c_146097)
    };
    let doe = &z - &(&era * &c_146097);
    let yoe_num = &(&(&doe - &div(&doe, &c_1460)) + &div(&doe, &c_36524)) - &div(&doe, &c_146096);
    let yoe = div(&yoe_num, &c_365);
    let doy_sub = &(&(&c_365 * &yoe) + &div(&yoe, &c_4)) - &div(&yoe, &c_100);
    let doy = &doe - &doy_sub;
    let mp = div(&(&(&c_5 * &doy) + &c_2), &c_153);
    let dom0 = &doy - &div(&(&(&c_153 * &mp) + &c_2), &c_5);
    days - &dom0
}

fn lookup_col_idx<'a>(cols: &'a [ColSpec], name: &str) -> Option<(usize, &'a ColSpec)> {
    cols.iter().enumerate().find(|(_, c)| c.name == name)
}

fn project_col_cells<'a>(tv: &'a TableVal, col_name: &str) -> Option<(&'a ColSpec, Vec<Val>)> {
    let (idx, c_spec) = lookup_col_idx(&tv.cols, col_name)?;
    let mut vals = Vec::with_capacity(tv.rows.len());
    for r in &tv.rows {
        vals.push(r.cells.get(idx)?.clone());
    }
    Some((c_spec, vals))
}

fn build_profile_col(tv: &TableVal, idx: usize, c: &ColSpec) -> Option<ProfileColSummary> {
    let mut cells = Vec::with_capacity(tv.rows.len());
    for r in &tv.rows {
        cells.push(r.cells.get(idx)?.clone());
    }
    let non_null: Vec<Val> = cells
        .iter()
        .filter_map(|v| match v {
            Val::OptNone => None,
            Val::OptSome(inner) => Some(inner.as_ref().clone()),
            other => Some(other.clone()),
        })
        .collect();
    let null_count = cells.len() - non_null.len();
    let sorted = insertion_sort_by(&non_null, val_lt);
    let distinct_vals = dedup_adjacent_by(&sorted, val_eq);
    let (min_display, max_display) = if !c.tags.is_empty() {
        let r = redact_tags(&c.tags);
        (Some(r.clone()), Some(r))
    } else {
        match (sorted.first(), sorted.last()) {
            (Some(mn), Some(mx)) => (Some(render_public_val(mn)), Some(render_public_val(mx))),
            _ => (None, None),
        }
    };
    Some(ProfileColSummary {
        col_name: c.name.clone(),
        ty_name: repr_scalar_ty(&c.ty),
        row_count: cells.len(),
        null_count,
        distinct_count: distinct_vals.len(),
        min_display,
        max_display,
        ..ProfileColSummary::default()
    })
}

fn build_profile_cols(tv: &TableVal) -> Option<Vec<ProfileColSummary>> {
    tv.cols
        .iter()
        .enumerate()
        .map(|(idx, c)| build_profile_col(tv, idx, c))
        .collect()
}

fn extract_pair_vals(
    cols: &[ColSpec],
    col_x: &str,
    col_y: &str,
    rows: &[TableRow],
) -> Option<Vec<Vec<Val>>> {
    let (idx_x, _) = lookup_col_idx(cols, col_x)?;
    let (idx_y, _) = lookup_col_idx(cols, col_y)?;
    let pairs = rows
        .iter()
        .filter_map(|r| match (r.cells.get(idx_x), r.cells.get(idx_y)) {
            (Some(vx), Some(vy)) => match (vx, vy) {
                (Val::OptNone, _) | (_, Val::OptNone) => None,
                (Val::OptSome(ux), Val::OptSome(uy)) => {
                    Some(vec![ux.as_ref().clone(), uy.as_ref().clone()])
                }
                (Val::OptSome(ux), uy) => Some(vec![ux.as_ref().clone(), uy.clone()]),
                (ux, Val::OptSome(uy)) => Some(vec![ux.clone(), uy.as_ref().clone()]),
                (ux, uy) => Some(vec![ux.clone(), uy.clone()]),
            },
            _ => None,
        })
        .collect();
    Some(pairs)
}

fn pairs_to_floats(sorted_pairs: &[Vec<Val>]) -> Vec<(f64, f64)> {
    sorted_pairs
        .iter()
        .filter_map(|pair| match pair.as_slice() {
            [vx, vy] => match (val_to_float(vx), val_to_float(vy)) {
                (Some(x), Some(y)) => Some((x, y)),
                _ => None,
            },
            _ => None,
        })
        .collect()
}

#[must_use]
pub fn mean_of_floats(xs: &[f64]) -> f64 {
    let n = xs.len() as f64;
    let total = xs.iter().copied().fold(0.0_f64, |acc, x| acc + x);
    if total.is_infinite() {
        xs.iter().copied().fold(0.0_f64, |acc, x| acc + x / n)
    } else {
        total / n
    }
}

#[must_use]
pub fn compute_stats_corr(sorted_pairs: &[Vec<Val>]) -> Option<Float64> {
    let pts = pairs_to_floats(sorted_pairs);
    if pts.len() < 2
        || pts
            .iter()
            .any(|&(x, y)| x.is_nan() || x.is_infinite() || y.is_nan() || y.is_infinite())
    {
        return None;
    }
    let xs: Vec<f64> = pts.iter().map(|&(x, _)| x).collect();
    let ys: Vec<f64> = pts.iter().map(|&(_, y)| y).collect();
    let mean_x = mean_of_floats(&xs);
    let mean_y = mean_of_floats(&ys);
    if mean_x.is_nan() || mean_x.is_infinite() || mean_y.is_nan() || mean_y.is_infinite() {
        return None;
    }
    let scale_x = pts.iter().fold(0.0_f64, |acc, &(x, _)| {
        let a = (x - mean_x).abs();
        if a > acc { a } else { acc }
    });
    let scale_y = pts.iter().fold(0.0_f64, |acc, &(_, y)| {
        let a = (y - mean_y).abs();
        if a > acc { a } else { acc }
    });
    if scale_x == 0.0 || scale_y == 0.0 || scale_x.is_infinite() || scale_y.is_infinite() {
        return None;
    }
    let u_sxx = pts.iter().fold(0.0_f64, |acc, &(x, _)| {
        let u = (x - mean_x) / scale_x;
        acc + u * u
    });
    let u_syy = pts.iter().fold(0.0_f64, |acc, &(_, y)| {
        let u = (y - mean_y) / scale_y;
        acc + u * u
    });
    let u_sxy = pts.iter().fold(0.0_f64, |acc, &(x, y)| {
        acc + ((x - mean_x) / scale_x) * ((y - mean_y) / scale_y)
    });
    let denom = u_sxx.sqrt() * u_syy.sqrt();
    if denom == 0.0 || denom.is_nan() {
        None
    } else {
        Some(Float64::from_f64(u_sxy / denom))
    }
}

#[must_use]
pub fn compute_stats_linreg(sorted_pairs: &[Vec<Val>]) -> Option<(Float64, Float64, Float64)> {
    let pts = pairs_to_floats(sorted_pairs);
    if pts.len() < 2
        || pts
            .iter()
            .any(|&(x, y)| x.is_nan() || x.is_infinite() || y.is_nan() || y.is_infinite())
    {
        return None;
    }
    let xs: Vec<f64> = pts.iter().map(|&(x, _)| x).collect();
    let ys: Vec<f64> = pts.iter().map(|&(_, y)| y).collect();
    let mean_x = mean_of_floats(&xs);
    let mean_y = mean_of_floats(&ys);
    if mean_x.is_nan() || mean_x.is_infinite() || mean_y.is_nan() || mean_y.is_infinite() {
        return None;
    }
    let scale_x = pts.iter().fold(0.0_f64, |acc, &(x, _)| {
        let a = (x - mean_x).abs();
        if a > acc { a } else { acc }
    });
    let scale_y = pts.iter().fold(0.0_f64, |acc, &(_, y)| {
        let a = (y - mean_y).abs();
        if a > acc { a } else { acc }
    });
    if scale_x == 0.0 || scale_x.is_infinite() {
        return None;
    }
    if scale_y == 0.0 {
        return Some((
            Float64::ZERO,
            Float64::from_f64(mean_y),
            Float64::from_f64(1.0),
        ));
    }
    if scale_y.is_infinite() {
        return None;
    }
    let u_sxx = pts.iter().fold(0.0_f64, |acc, &(x, _)| {
        let u = (x - mean_x) / scale_x;
        acc + u * u
    });
    let u_syy = pts.iter().fold(0.0_f64, |acc, &(_, y)| {
        let u = (y - mean_y) / scale_y;
        acc + u * u
    });
    let u_sxy = pts.iter().fold(0.0_f64, |acc, &(x, y)| {
        acc + ((x - mean_x) / scale_x) * ((y - mean_y) / scale_y)
    });
    if u_sxx == 0.0 {
        return None;
    }
    let slope = (u_sxy / u_sxx) * (scale_y / scale_x);
    let intercept = mean_y - slope * mean_x;
    let r2 = if u_syy == 0.0 {
        1.0
    } else {
        (u_sxy * u_sxy) / (u_sxx * u_syy)
    };
    Some((
        Float64::from_f64(slope),
        Float64::from_f64(intercept),
        Float64::from_f64(r2),
    ))
}

#[must_use]
pub fn eval_prim_op(op: &PrimOp, args: &[Val]) -> PrimResult {
    match (op, args) {
        (PrimOp::SomeVal(_), [v]) => PrimResult::Ok(Val::OptSome(Box::new(v.clone()))),
        (PrimOp::IsSome, [Val::OptNone]) => PrimResult::Ok(Val::Bool(false)),
        (PrimOp::IsSome, [Val::OptSome(_)]) => PrimResult::Ok(Val::Bool(true)),
        (PrimOp::IsNone, [Val::OptNone]) => PrimResult::Ok(Val::Bool(true)),
        (PrimOp::IsNone, [Val::OptSome(_)]) => PrimResult::Ok(Val::Bool(false)),
        (PrimOp::UnwrapOr, [Val::OptNone, def_v]) => PrimResult::Ok(def_v.clone()),
        (PrimOp::UnwrapOr, [Val::OptSome(v), _]) => PrimResult::Ok(v.as_ref().clone()),
        (PrimOp::UnwrapBang, [Val::OptSome(v)]) => PrimResult::Ok(v.as_ref().clone()),
        (PrimOp::UnwrapBang, [Val::OptNone]) => PrimResult::Stopped(Bug {
            kind: BugKind::UnwrapNone,
            message: "unwrapped none value".to_string(),
        }),
        (PrimOp::OkVal(_), [v]) => PrimResult::Ok(Val::ResOk(Box::new(v.clone()))),
        (PrimOp::ErrVal(_), [e]) => PrimResult::Ok(Val::ResErr(Box::new(e.clone()))),
        (PrimOp::AddInt, [Val::Int(a), Val::Int(b)]) => checked_int(a + b),
        (PrimOp::SubInt, [Val::Int(a), Val::Int(b)]) => checked_int(a - b),
        (PrimOp::MulInt, [Val::Int(a), Val::Int(b)]) => checked_int(a * b),
        (PrimOp::DivInt, [Val::Int(a), Val::Int(b)]) => match a.div_euclid(b) {
            Some(q) => checked_int(q),
            None => PrimResult::Stopped(Bug {
                kind: BugKind::DivByZero,
                message: "integer division by zero".to_string(),
            }),
        },
        (PrimOp::ModInt, [Val::Int(a), Val::Int(b)]) => match a.rem_euclid(b) {
            Some(r) => checked_int(r),
            None => PrimResult::Stopped(Bug {
                kind: BugKind::DivByZero,
                message: "integer modulo by zero".to_string(),
            }),
        },
        (PrimOp::NegInt, [Val::Int(a)]) => checked_int(-a),
        (PrimOp::AddDec, [Val::Decimal(a), Val::Decimal(b)]) => checked_decimal(a + b),
        (PrimOp::SubDec, [Val::Decimal(a), Val::Decimal(b)]) => checked_decimal(a - b),
        (PrimOp::MulDec, [Val::Decimal(a), Val::Decimal(b)]) => {
            let scale = BigInt::from(DEC_SCALE);
            let q = (a * b).div_euclid(&scale).unwrap_or(BigInt::ZERO);
            checked_decimal(q)
        }
        (PrimOp::DivDec, [Val::Decimal(a), Val::Decimal(b)]) => {
            let scale = BigInt::from(DEC_SCALE);
            match (a * &scale).div_euclid(b) {
                Some(q) => checked_decimal(q),
                None => PrimResult::Stopped(Bug {
                    kind: BugKind::DivByZero,
                    message: "decimal division by zero".to_string(),
                }),
            }
        }
        (PrimOp::NegDec, [Val::Decimal(a)]) => checked_decimal(-a),
        (PrimOp::IntToDec, [Val::Int(n)]) => checked_decimal(n * &BigInt::from(DEC_SCALE)),
        (PrimOp::BoolToDec, [Val::Bool(b)]) => PrimResult::Ok(Val::Decimal(if *b {
            BigInt::from(DEC_SCALE)
        } else {
            BigInt::ZERO
        })),
        (PrimOp::Eq, [a, b]) => PrimResult::Ok(Val::Bool(val_eq(a, b))),
        (PrimOp::Ne, [a, b]) => PrimResult::Ok(Val::Bool(!val_eq(a, b))),
        (PrimOp::Lt, [a, b]) => PrimResult::Ok(Val::Bool(val_lt(a, b))),
        (PrimOp::Le, [a, b]) => PrimResult::Ok(Val::Bool(val_lt(a, b) || val_eq(a, b))),
        (PrimOp::Gt, [a, b]) => PrimResult::Ok(Val::Bool(val_lt(b, a))),
        (PrimOp::Ge, [a, b]) => PrimResult::Ok(Val::Bool(val_lt(b, a) || val_eq(a, b))),
        (PrimOp::NotBool, [Val::Bool(a)]) => PrimResult::Ok(Val::Bool(!a)),
        (PrimOp::AndBool, [Val::Bool(a), Val::Bool(b)]) => PrimResult::Ok(Val::Bool(*a && *b)),
        (PrimOp::OrBool, [Val::Bool(a), Val::Bool(b)]) => PrimResult::Ok(Val::Bool(*a || *b)),
        (PrimOp::ConcatText, [Val::Text(a), Val::Text(b)]) => {
            PrimResult::Ok(Val::Text(format!("{a}{b}")))
        }
        (PrimOp::ContainsText, [Val::Text(a), Val::Text(b)]) => {
            PrimResult::Ok(Val::Bool(a.contains(b.as_str())))
        }
        (PrimOp::TrimText, [Val::Text(a)]) => PrimResult::Ok(Val::Text(trim_ascii_string(a))),
        (PrimOp::LowerAsciiText, [Val::Text(a)]) => {
            PrimResult::Ok(Val::Text(a.to_ascii_lowercase()))
        }
        (PrimOp::EmptyText, [Val::Text(a)]) => PrimResult::Ok(Val::Bool(a.is_empty())),
        (PrimOp::IntToText, [Val::Int(n)]) => PrimResult::Ok(Val::Text(n.to_string())),
        (PrimOp::DecToText, [Val::Decimal(d)]) => PrimResult::Ok(Val::Text(render_decimal(d))),
        (PrimOp::DateTruncMonth, [Val::Date(d)]) => {
            PrimResult::Ok(Val::Date(date_trunc_month_days(d)))
        }
        (PrimOp::AddDuration, [Val::Timestamp(ts), Val::Duration(dur)]) => {
            PrimResult::Ok(Val::Timestamp(ts + dur))
        }
        (PrimOp::DiffTimestamp, [Val::Timestamp(t1), Val::Timestamp(t2)]) => {
            PrimResult::Ok(Val::Duration(t1 - t2))
        }
        (PrimOp::ListLit(_), elems) => PrimResult::Ok(Val::List(elems.to_vec())),
        (PrimOp::ListLen, [Val::List(elems)]) => checked_int(BigInt::from(elems.len())),
        (PrimOp::ListEmpty, [Val::List(elems)]) => PrimResult::Ok(Val::Bool(elems.is_empty())),
        (PrimOp::ListAppend, [Val::List(elems), item]) => {
            let mut out = elems.clone();
            out.push(item.clone());
            PrimResult::Ok(Val::List(out))
        }
        (PrimOp::ListConcat, [Val::List(nested)]) => {
            let mut flat = Vec::new();
            for item in nested {
                if let Val::List(xs) = item {
                    flat.extend_from_slice(xs);
                } else {
                    return PrimResult::Wrong;
                }
            }
            PrimResult::Ok(Val::List(flat))
        }
        (PrimOp::MapLit { .. }, kv_args) => {
            if !kv_args.len().is_multiple_of(2) {
                return PrimResult::Wrong;
            }
            let pairs = kv_args
                .chunks_exact(2)
                .map(|c| (c[0].clone(), c[1].clone()))
                .collect();
            PrimResult::Ok(Val::Map(pairs))
        }
        (PrimOp::MapGet, [Val::Map(pairs), q_key]) => {
            match pairs.iter().find(|(k, _)| val_eq(k, q_key)) {
                Some((_, v)) => PrimResult::Ok(Val::OptSome(Box::new(v.clone()))),
                None => PrimResult::Ok(Val::OptNone),
            }
        }
        (PrimOp::TableCount, [Val::Table(tv)]) => checked_int(BigInt::from(tv.rows.len())),
        (PrimOp::TableConcat(schema), [Val::List(tbls)]) => {
            let out_cols = schema
                .cols
                .iter()
                .map(|c| ColSpec {
                    agg_kind: AggKind::Raw,
                    ..c.clone()
                })
                .collect();
            let mut all_rows = Vec::new();
            for item in tbls {
                if let Val::Table(tv) = item {
                    all_rows.extend(tv.rows.iter().map(|r| TableRow {
                        cells: r.cells.clone(),
                        group_meta: None,
                    }));
                } else {
                    return PrimResult::Wrong;
                }
            }
            PrimResult::Ok(Val::Table(TableVal {
                cols: out_cols,
                rows: all_rows,
            }))
        }
        (PrimOp::TableProfile, [Val::Table(tv)]) => match build_profile_cols(tv) {
            Some(cols) => PrimResult::Ok(Val::Profile(ProfileVal { cols })),
            None => PrimResult::Wrong,
        },
        (PrimOp::StatsCorr { col_x, col_y }, [Val::Table(tv)]) => {
            match extract_pair_vals(&tv.cols, col_x, col_y, &tv.rows) {
                Some(raw_pairs) => {
                    let sorted_pairs = insertion_sort_by(&raw_pairs, |a, b| val_list_lt(a, b));
                    match compute_stats_corr(&sorted_pairs) {
                        None => PrimResult::Ok(Val::OptNone),
                        Some(r) => PrimResult::Ok(Val::OptSome(Box::new(Val::Float(r)))),
                    }
                }
                None => PrimResult::Wrong,
            }
        }
        (PrimOp::StatsLinReg { col_x, col_y }, [Val::Table(tv)]) => {
            match extract_pair_vals(&tv.cols, col_x, col_y, &tv.rows) {
                Some(raw_pairs) => {
                    let sorted_pairs = insertion_sort_by(&raw_pairs, |a, b| val_list_lt(a, b));
                    match compute_stats_linreg(&sorted_pairs) {
                        Some((slope, intercept, r2)) => PrimResult::Ok(Val::LinearModel {
                            slope,
                            intercept,
                            r2,
                        }),
                        None => PrimResult::Stopped(Bug {
                            kind: BugKind::DivByZero,
                            message: "degenerate linear regression: fewer than 2 points, non-finite inputs, or zero variance in x".to_string(),
                        }),
                    }
                }
                None => PrimResult::Wrong,
            }
        }
        (PrimOp::StatsTTest { col_x, col_y }, [Val::Table(tv)]) => {
            match (
                lookup_col_idx(&tv.cols, col_x),
                lookup_col_idx(&tv.cols, col_y),
            ) {
                (Some(_), Some(_)) => PrimResult::Stopped(Bug {
                    kind: BugKind::OutsideBoundary,
                    message: "outside boundary: statsTTest is outside the Lean Core oracle"
                        .to_string(),
                }),
                _ => PrimResult::Wrong,
            }
        }
        (PrimOp::ChartMake { kind, cols, title }, [Val::Table(tv)]) => {
            let mut series = Vec::with_capacity(cols.len());
            for cn in cols {
                let Some((_, vals)) = project_col_cells(tv, cn) else {
                    return PrimResult::Wrong;
                };
                series.push(vals);
            }
            PrimResult::Ok(Val::Chart(Box::new(ChartVal {
                kind: *kind,
                title: title.clone(),
                col_names: cols.clone(),
                series,
                ..ChartVal::default()
            })))
        }
        (PrimOp::ReportNew, [Val::Text(title)]) => {
            PrimResult::Ok(Val::Report(Box::new(ReportVal {
                title: title.clone(),
                summaries: Vec::new(),
                charts: Vec::new(),
                tables: Vec::new(),
            })))
        }
        (PrimOp::ReportAddSummary, [Val::Report(rv), Val::Text(s)]) => {
            let mut out = rv.as_ref().clone();
            out.summaries.push(s.clone());
            PrimResult::Ok(Val::Report(Box::new(out)))
        }
        (PrimOp::ReportAddChart, [Val::Report(rv), Val::Chart(cv)]) => {
            let mut out = rv.as_ref().clone();
            out.charts.push(cv.as_ref().clone());
            PrimResult::Ok(Val::Report(Box::new(out)))
        }
        (PrimOp::ReportAddTable, [Val::Report(rv), Val::Table(tv)]) => {
            let mut out = rv.as_ref().clone();
            let headers = tv.cols.iter().map(|c| c.name.clone()).collect();
            let raw_rows = tv.rows.iter().map(|r| r.cells.clone()).collect();
            out.tables.push((headers, raw_rows));
            PrimResult::Ok(Val::Report(Box::new(out)))
        }
        _ => PrimResult::Wrong,
    }
}

// ---------------------------------------------------------------------------
// Pseudonymization & Host Capability Execution
// ---------------------------------------------------------------------------

/// FNV-1a 64-bit hash over Unicode scalar values (`char`), matching `Eval.lean:fnv1a64`.
#[must_use]
pub fn fnv1a64(s: &str) -> u64 {
    let mut hash: u64 = 14_695_981_039_346_656_037;
    for c in s.chars() {
        hash = (hash ^ u64::from(c as u32)).wrapping_mul(1_099_511_628_211);
    }
    hash
}

#[must_use]
pub fn pseudonymize_token(secret_material: &str, v: &Val) -> String {
    let h = fnv1a64(&format!("{secret_material}:{}", render_public_val(v)));
    format!("ps_{h:016x}")
}

fn check_runtime_export_gate(h: CapHandle, allows: &TagSet, w: &World) -> Option<Bug> {
    match h {
        CapHandle::Fake(_) => None,
        CapHandle::Real => {
            if allows.is_empty() || allows.is_subset(&w.runtime_allow_export) {
                None
            } else {
                Some(Bug {
                    kind: BugKind::ExportGateDenied,
                    message:
                        "runtime --allow-export authorization required for sensitive external sink"
                            .to_string(),
                })
            }
        }
    }
}

fn render_table_text(tv: &TableVal) -> String {
    let hdr = tv
        .cols
        .iter()
        .map(|c| c.name.as_str())
        .collect::<Vec<_>>()
        .join(" | ");
    let mut lines = Vec::with_capacity(tv.rows.len() + 1);
    lines.push(hdr);
    for r in &tv.rows {
        let cells: Vec<String> = r.cells.iter().map(render_public_val).collect();
        lines.push(cells.join(" | "));
    }
    lines.join("\n")
}

fn render_report_html(rv: &ReportVal) -> String {
    format!(
        "<html><h1>{}</h1><p>{}</p><!-- charts:{} tables:{} --></html>",
        rv.title,
        rv.summaries.join("</p><p>"),
        rv.charts.len(),
        rv.tables.len()
    )
}

fn eval_host_op(prog: &Program, op: &HostOp, args: &[Val], mut w: World) -> Outcome {
    match (op, args) {
        (HostOp::ArgsGet, [Val::CapArgs]) => {
            let vals = w.args.iter().cloned().map(Val::Text).collect();
            Outcome::Ok(Val::List(vals), w)
        }
        (HostOp::ClockNow, [Val::CapClock]) => {
            let ts = w.clock_micros.clone();
            Outcome::Ok(Val::Timestamp(ts), w)
        }
        (HostOp::ConsolePrint, [Val::CapConsole { handle: h, allows }, Val::Text(msg)]) => {
            if let Some(bug) = check_runtime_export_gate(*h, allows, &w) {
                return Outcome::Stopped(bug, w);
            }
            match *h {
                CapHandle::Real => w.stdout.push(msg.clone()),
                CapHandle::Fake(id) => {
                    if let Some(fc) = w.fake_consoles.get_mut(id) {
                        fc.stdout.push(msg.clone());
                    }
                }
            }
            Outcome::Ok(Val::Unit, w)
        }
        (HostOp::ConsoleError, [Val::CapConsole { handle: h, allows }, Val::Text(msg)]) => {
            if let Some(bug) = check_runtime_export_gate(*h, allows, &w) {
                return Outcome::Stopped(bug, w);
            }
            match *h {
                CapHandle::Real => w.stderr.push(msg.clone()),
                CapHandle::Fake(id) => {
                    if let Some(fc) = w.fake_consoles.get_mut(id) {
                        fc.stderr.push(msg.clone());
                    }
                }
            }
            Outcome::Ok(Val::Unit, w)
        }
        (HostOp::ConsolePrintTable, [Val::CapConsole { handle: h, allows }, Val::Table(tv)]) => {
            if let Some(bug) = check_runtime_export_gate(*h, allows, &w) {
                return Outcome::Stopped(bug, w);
            }
            let line = render_table_text(tv);
            match *h {
                CapHandle::Real => w.stdout.push(line),
                CapHandle::Fake(id) => {
                    if let Some(fc) = w.fake_consoles.get_mut(id) {
                        fc.stdout.push(line);
                    }
                }
            }
            Outcome::Ok(Val::Unit, w)
        }
        (HostOp::ReadCsv(schema_name), [Val::CapReadFiles(_), Val::Text(path)]) => {
            let Some(s_decl) = prog.find_schema(schema_name) else {
                return Outcome::Wrong;
            };
            let bad_tt = quarantine_bad_row_table_ty(&s_decl.schema);
            match w.real_csv_fixtures.iter().find(|(p, _, _)| p == path) {
                Some((_, good_tv, bad_tv)) => {
                    let good_tys: Vec<&ScalarTy> = good_tv.cols.iter().map(|c| &c.ty).collect();
                    let decl_tys: Vec<&ScalarTy> =
                        s_decl.schema.cols.iter().map(|c| &c.ty).collect();
                    let bad_tys: Vec<&ScalarTy> = bad_tv.cols.iter().map(|c| &c.ty).collect();
                    let decl_bad_tys: Vec<&ScalarTy> = bad_tt.cols.iter().map(|c| &c.ty).collect();
                    if good_tys == decl_tys && bad_tys == decl_bad_tys {
                        let g_tv = TableVal {
                            cols: s_decl.schema.cols.clone(),
                            rows: good_tv.rows.clone(),
                        };
                        let b_tv = TableVal {
                            cols: bad_tt.cols,
                            rows: bad_tv.rows.clone(),
                        };
                        Outcome::Ok(
                            Val::ResOk(Box::new(Val::Tuple(vec![
                                Val::Table(g_tv),
                                Val::Table(b_tv),
                            ]))),
                            w,
                        )
                    } else {
                        Outcome::Ok(
                            Val::ResErr(Box::new(Val::Text(format!(
                                "CSV fixture schema mismatch at '{path}'"
                            )))),
                            w,
                        )
                    }
                }
                None => {
                    let empty_good = TableVal {
                        cols: s_decl.schema.cols.clone(),
                        rows: Vec::new(),
                    };
                    let empty_bad = TableVal {
                        cols: bad_tt.cols,
                        rows: Vec::new(),
                    };
                    Outcome::Ok(
                        Val::ResOk(Box::new(Val::Tuple(vec![
                            Val::Table(empty_good),
                            Val::Table(empty_bad),
                        ]))),
                        w,
                    )
                }
            }
        }
        (
            HostOp::WriteFile,
            [
                Val::CapWriteFiles {
                    handle: h,
                    root,
                    allows,
                },
                Val::Text(rel_path),
                Val::Text(content),
            ],
        ) => {
            if let Some(bug) = check_runtime_export_gate(*h, allows, &w) {
                return Outcome::Stopped(bug, w);
            }
            if !is_safe_relative_path(rel_path) {
                return Outcome::Ok(
                    Val::ResErr(Box::new(Val::Text(format!(
                        "invalid relative export path '{rel_path}'"
                    )))),
                    w,
                );
            }
            let full_path = join_confined_path(root, rel_path);
            match *h {
                CapHandle::Real => w.written_files.push((full_path, content.clone())),
                CapHandle::Fake(id) => {
                    if let Some(ff) = w.fake_files.get_mut(id) {
                        ff.files.push((full_path, content.clone()));
                    }
                }
            }
            Outcome::Ok(Val::ResOk(Box::new(Val::Unit)), w)
        }
        (
            HostOp::WriteReportHtml,
            [
                Val::CapWriteFiles {
                    handle: h,
                    root,
                    allows,
                },
                Val::Text(rel_path),
                Val::Report(rv),
            ],
        ) => {
            if let Some(bug) = check_runtime_export_gate(*h, allows, &w) {
                return Outcome::Stopped(bug, w);
            }
            if !is_safe_relative_path(rel_path) {
                return Outcome::Ok(
                    Val::ResErr(Box::new(Val::Text(format!(
                        "invalid relative export path '{rel_path}'"
                    )))),
                    w,
                );
            }
            let full_path = join_confined_path(root, rel_path);
            let html = render_report_html(rv);
            match *h {
                CapHandle::Real => w.written_files.push((full_path, html)),
                CapHandle::Fake(id) => {
                    if let Some(ff) = w.fake_files.get_mut(id) {
                        ff.files.push((full_path, html));
                    }
                }
            }
            Outcome::Ok(Val::ResOk(Box::new(Val::Unit)), w)
        }
        (
            HostOp::WriteTable,
            [
                Val::CapWriteTable {
                    handle: h,
                    db,
                    table_name: tbl,
                },
                Val::Table(src_tv),
            ],
        ) => {
            let col_names: Vec<Ident> = src_tv.cols.iter().map(|c| c.name.clone()).collect();
            let raw_rows: Vec<Vec<Val>> = src_tv.rows.iter().map(|r| r.cells.clone()).collect();
            match checked_int(BigInt::from(raw_rows.len())) {
                PrimResult::Ok(cnt_val) => {
                    if matches!(*h, CapHandle::Real) {
                        w.written_tables
                            .push((db.clone(), tbl.clone(), col_names, raw_rows));
                    }
                    Outcome::Ok(Val::ResOk(Box::new(cnt_val)), w)
                }
                PrimResult::Stopped(bug) => Outcome::Stopped(bug, w),
                PrimResult::OutOfFuel | PrimResult::Wrong => Outcome::Wrong,
            }
        }
        (HostOp::DeclassifyApprove(_), [Val::CapDeclassify(_), v, Val::Text(_)]) => {
            Outcome::Ok(v.clone(), w)
        }
        (HostOp::RawSqlQuery { .. }, [Val::CapRawReadDB(_), Val::Text(_)]) => Outcome::Stopped(
            Bug {
                kind: BugKind::OutsideBoundary,
                message: "outside boundary: live SQL wire query".to_string(),
            },
            w,
        ),
        (
            HostOp::HttpsGetJson,
            [
                Val::CapHttpsAllow {
                    handle: h, allows, ..
                },
                Val::Text(url),
            ],
        ) => match *h {
            CapHandle::Real => Outcome::Stopped(
                Bug {
                    kind: BugKind::OutsideBoundary,
                    message: "outside boundary: live HTTPS socket".to_string(),
                },
                w,
            ),
            CapHandle::Fake(id) => {
                if let Some(bug) = check_runtime_export_gate(*h, allows, &w) {
                    return Outcome::Stopped(bug, w);
                }
                if let Some(fh) = w.fake_https.get_mut(id) {
                    fh.requests.push(url.clone());
                    let found = fh
                        .responses
                        .iter()
                        .find(|(u, _)| u == url)
                        .map(|(_, body)| body.clone());
                    match found {
                        Some(body) => Outcome::Ok(Val::ResOk(Box::new(Val::Text(body))), w),
                        None => Outcome::Ok(
                            Val::ResErr(Box::new(Val::Text("404 Not Found".to_string()))),
                            w,
                        ),
                    }
                } else {
                    Outcome::Ok(
                        Val::ResErr(Box::new(Val::Text("invalid fake https handle".to_string()))),
                        w,
                    )
                }
            }
        },
        (HostOp::ReadParquet(_), [Val::CapReadFiles(h), Val::Text(_)]) => match *h {
            CapHandle::Real => Outcome::Stopped(
                Bug {
                    kind: BugKind::OutsideBoundary,
                    message: "outside boundary: binary Parquet decoder".to_string(),
                },
                w,
            ),
            CapHandle::Fake(_) => Outcome::Ok(
                Val::ResErr(Box::new(Val::Text(
                    "in-memory Parquet fixture not found".to_string(),
                ))),
                w,
            ),
        },
        (
            HostOp::WriteParquet,
            [
                Val::CapWriteFiles {
                    handle: h,
                    root,
                    allows,
                },
                Val::Text(rel_path),
                Val::Table(src_tv),
            ],
        ) => {
            if let Some(bug) = check_runtime_export_gate(*h, allows, &w) {
                return Outcome::Stopped(bug, w);
            }
            if !is_safe_relative_path(rel_path) {
                return Outcome::Ok(
                    Val::ResErr(Box::new(Val::Text(format!(
                        "invalid relative export path '{rel_path}'"
                    )))),
                    w,
                );
            }
            match *h {
                CapHandle::Real => Outcome::Stopped(
                    Bug {
                        kind: BugKind::OutsideBoundary,
                        message: "outside boundary: binary Parquet encoder".to_string(),
                    },
                    w,
                ),
                CapHandle::Fake(id) => {
                    let full_path = join_confined_path(root, rel_path);
                    let repr_content = render_table_text(src_tv);
                    if let Some(ff) = w.fake_files.get_mut(id) {
                        ff.files.push((full_path, repr_content));
                    }
                    Outcome::Ok(Val::ResOk(Box::new(Val::Unit)), w)
                }
            }
        }
        (
            HostOp::WriteXlsx,
            [
                Val::CapWriteFiles {
                    handle: h,
                    root,
                    allows,
                },
                Val::Text(rel_path),
                Val::Table(src_tv),
            ],
        ) => {
            if let Some(bug) = check_runtime_export_gate(*h, allows, &w) {
                return Outcome::Stopped(bug, w);
            }
            if !is_safe_relative_path(rel_path) {
                return Outcome::Ok(
                    Val::ResErr(Box::new(Val::Text(format!(
                        "invalid relative export path '{rel_path}'"
                    )))),
                    w,
                );
            }
            match *h {
                CapHandle::Real => Outcome::Stopped(
                    Bug {
                        kind: BugKind::OutsideBoundary,
                        message: "outside boundary: binary XLSX encoder".to_string(),
                    },
                    w,
                ),
                CapHandle::Fake(id) => {
                    let full_path = join_confined_path(root, rel_path);
                    let repr_content = render_table_text(src_tv);
                    if let Some(ff) = w.fake_files.get_mut(id) {
                        ff.files.push((full_path, repr_content));
                    }
                    Outcome::Ok(Val::ResOk(Box::new(Val::Unit)), w)
                }
            }
        }
        (HostOp::FakeConsole(allows), []) => {
            let id = w.fake_consoles.len();
            w.fake_consoles.push(FakeConsoleState::default());
            Outcome::Ok(
                Val::CapConsole {
                    handle: CapHandle::Fake(id),
                    allows: allows.clone(),
                },
                w,
            )
        }
        (HostOp::FakeFiles(allows), []) => {
            let id = w.fake_files.len();
            w.fake_files.push(FakeFilesState::default());
            Outcome::Ok(
                Val::CapWriteFiles {
                    handle: CapHandle::Fake(id),
                    root: "mem://".to_string(),
                    allows: allows.clone(),
                },
                w,
            )
        }
        (HostOp::FakeDB(db), []) => {
            let id = w.fake_dbs.len();
            w.fake_dbs.push(FakeDBState {
                db: db.clone(),
                tables: Vec::new(),
            });
            Outcome::Ok(
                Val::CapReadDB {
                    handle: CapHandle::Fake(id),
                    db: db.clone(),
                },
                w,
            )
        }
        (HostOp::FakeHttps { host, allows }, []) => {
            let id = w.fake_https.len();
            w.fake_https.push(FakeHttpsState {
                host: host.clone(),
                responses: Vec::new(),
                requests: Vec::new(),
            });
            Outcome::Ok(
                Val::CapHttpsAllow {
                    handle: CapHandle::Fake(id),
                    host: host.clone(),
                    allows: allows.clone(),
                },
                w,
            )
        }
        (HostOp::FakeSecret(name), [Val::Text(secret_val)]) => {
            let id = w.fake_secrets.len();
            w.fake_secrets.push(secret_val.clone());
            Outcome::Ok(
                Val::CapSecret {
                    handle: CapHandle::Fake(id),
                    name: name.clone(),
                },
                w,
            )
        }
        _ => Outcome::Wrong,
    }
}

// ---------------------------------------------------------------------------
// Pure Relational Operators Evaluation Helpers
// ---------------------------------------------------------------------------

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

fn wrap_into_option_val(s_ty: &ScalarTy, v: Val) -> Val {
    match s_ty {
        ScalarTy::Option(_) => v,
        _ => Val::OptSome(Box::new(v)),
    }
}

fn eval_bucket_cell(v: &Val, cuts: &[Val], labels: &[String]) -> Option<Val> {
    if labels.len() != cuts.len() + 1 {
        return None;
    }
    for (cut, lbl) in cuts.iter().zip(labels) {
        if val_lt(v, cut) {
            return Some(Val::Text(lbl.clone()));
        }
    }
    labels.last().map(|l| Val::Text(l.clone()))
}

/// Right-to-left checked integer sum matching `Eval.lean:sumSortedInts`.
fn sum_sorted_ints(sorted: &[Val]) -> PrimResult {
    let mut acc = BigInt::ZERO;
    for v in sorted.iter().rev() {
        let Val::Int(x) = v else {
            return PrimResult::Wrong;
        };
        match checked_int(x + &acc) {
            PrimResult::Ok(Val::Int(ref next)) => acc = next.clone(),
            PrimResult::Ok(_) => return PrimResult::Wrong,
            other => return other,
        }
    }
    PrimResult::Ok(Val::Int(acc))
}

/// Right-to-left checked decimal sum matching `Eval.lean:sumSortedDecimals`.
fn sum_sorted_decimals(sorted: &[Val]) -> PrimResult {
    let mut acc = BigInt::ZERO;
    for v in sorted.iter().rev() {
        let Val::Decimal(x) = v else {
            return PrimResult::Wrong;
        };
        match checked_decimal(x + &acc) {
            PrimResult::Ok(Val::Decimal(ref next)) => acc = next.clone(),
            PrimResult::Ok(_) => return PrimResult::Wrong,
            other => return other,
        }
    }
    PrimResult::Ok(Val::Decimal(acc))
}

fn sum_sorted_floats(sorted: &[Val]) -> Float64 {
    let total = sorted.iter().fold(0.0_f64, |acc, v| match val_to_float(v) {
        Some(x) => acc + x,
        None => acc,
    });
    Float64::from_f64(total)
}

#[must_use]
pub fn mean_sorted_floats(sorted: &[Val]) -> Float64 {
    let xs: Vec<f64> = sorted.iter().filter_map(val_to_float).collect();
    if xs.is_empty() {
        Float64::ZERO
    } else {
        Float64::from_f64(mean_of_floats(&xs))
    }
}

#[must_use]
pub fn median_sorted_floats(sorted: &[Val]) -> Float64 {
    let xs: Vec<f64> = sorted.iter().filter_map(val_to_float).collect();
    if xs.is_empty() {
        return Float64::ZERO;
    }
    let n = xs.len();
    let mid = n / 2;
    if n % 2 == 1 {
        Float64::from_f64(xs.get(mid).copied().unwrap_or(0.0))
    } else {
        let lo = xs.get(mid - 1).copied().unwrap_or(0.0);
        let hi = xs.get(mid).copied().unwrap_or(0.0);
        Float64::from_f64((lo / 2.0) + (hi / 2.0))
    }
}

#[must_use]
pub fn variance_sorted_floats(sorted: &[Val]) -> Float64 {
    let xs: Vec<f64> = sorted.iter().filter_map(val_to_float).collect();
    if xs.is_empty() {
        return Float64::ZERO;
    }
    let n = xs.len() as f64;
    let mean = mean_of_floats(&xs);
    let sum_sq = xs.iter().copied().fold(0.0_f64, |acc, x| {
        let d = x - mean;
        acc + d * d
    });
    Float64::from_f64(sum_sq / n)
}

#[must_use]
pub fn stddev_sorted_floats(sorted: &[Val]) -> Float64 {
    let xs: Vec<f64> = sorted.iter().filter_map(val_to_float).collect();
    if xs.is_empty() {
        return Float64::ZERO;
    }
    if xs.iter().any(|&x| x.is_nan() || x.is_infinite()) {
        return Float64::from_f64(variance_sorted_floats(sorted).to_f64().sqrt());
    }
    let n = xs.len() as f64;
    let mean = mean_of_floats(&xs);
    if mean.is_nan() || mean.is_infinite() {
        return Float64::from_f64(variance_sorted_floats(sorted).to_f64().sqrt());
    }
    let scale = xs.iter().copied().fold(0.0_f64, |acc, x| {
        let a = (x - mean).abs();
        if a > acc { a } else { acc }
    });
    if scale == 0.0 {
        Float64::ZERO
    } else if scale.is_infinite() {
        Float64::from_f64(variance_sorted_floats(sorted).to_f64().sqrt())
    } else {
        let u_sum_sq = xs.iter().copied().fold(0.0_f64, |acc, x| {
            let u = (x - mean) / scale;
            acc + u * u
        });
        Float64::from_f64(scale * (u_sum_sq / n).sqrt())
    }
}

#[must_use]
pub fn percentile_sorted_floats(p: Float64, sorted: &[Val]) -> Float64 {
    let xs: Vec<f64> = sorted.iter().filter_map(val_to_float).collect();
    if xs.is_empty() {
        return Float64::ZERO;
    }
    let n = xs.len();
    let p_val = p.to_f64();
    if p_val <= 0.0 || n == 1 {
        return Float64::from_f64(xs.first().copied().unwrap_or(0.0));
    }
    if p_val >= 1.0 {
        return Float64::from_f64(xs.get(n - 1).copied().unwrap_or(0.0));
    }
    let pos = p_val * ((n - 1) as f64);
    let lo_u64 = pos as u64;
    let lo = usize::try_from(lo_u64).unwrap_or(usize::MAX).min(n - 1);
    let hi = (lo + 1).min(n - 1);
    let frac = pos - (lo as f64);
    let vlo = xs.get(lo).copied().unwrap_or(0.0);
    let vhi = xs.get(hi).copied().unwrap_or(0.0);
    if vlo == vhi {
        Float64::from_f64(vlo)
    } else {
        Float64::from_f64((1.0 - frac) * vlo + frac * vhi)
    }
}

fn eval_agg_clean(op: AggOp, out_ty: &ScalarTy, raw_vals: &[Val]) -> PrimResult {
    let non_null: Vec<Val> = raw_vals
        .iter()
        .filter_map(|v| match v {
            Val::OptNone => None,
            Val::OptSome(inner) => Some(inner.as_ref().clone()),
            other => Some(other.clone()),
        })
        .collect();
    let sorted = insertion_sort_by(&non_null, val_lt);
    match op {
        AggOp::Count => checked_int(BigInt::from(raw_vals.len())),
        AggOp::CountDistinct => {
            let dedup = dedup_adjacent_by(&sorted, val_eq);
            checked_int(BigInt::from(dedup.len()))
        }
        AggOp::Sum => match out_ty {
            ScalarTy::Int => sum_sorted_ints(&sorted),
            ScalarTy::Decimal => sum_sorted_decimals(&sorted),
            ScalarTy::Float => PrimResult::Ok(Val::Float(sum_sorted_floats(&sorted))),
            _ => PrimResult::Wrong,
        },
        AggOp::Mean => {
            if sorted.is_empty() {
                return PrimResult::Ok(Val::OptNone);
            }
            match out_ty {
                ScalarTy::Option(inner) if **inner == ScalarTy::Decimal => {
                    match sum_sorted_decimals(&sorted) {
                        PrimResult::Ok(Val::Decimal(ref total)) => {
                            let len = BigInt::from(sorted.len());
                            let avg = total.div_euclid(&len).unwrap_or(BigInt::ZERO);
                            if avg.in_decimal_range() {
                                PrimResult::Ok(Val::OptSome(Box::new(Val::Decimal(avg))))
                            } else {
                                PrimResult::Stopped(Bug {
                                    kind: BugKind::DecimalOverflow,
                                    message: "Decimal overflow in mean".to_string(),
                                })
                            }
                        }
                        PrimResult::Ok(_) => PrimResult::Wrong,
                        other => other,
                    }
                }
                ScalarTy::Option(inner) if **inner == ScalarTy::Float => PrimResult::Ok(
                    Val::OptSome(Box::new(Val::Float(mean_sorted_floats(&sorted)))),
                ),
                _ => PrimResult::Wrong,
            }
        }
        AggOp::Median => {
            if sorted.is_empty() {
                return PrimResult::Ok(Val::OptNone);
            }
            match out_ty {
                ScalarTy::Option(inner) if **inner == ScalarTy::Decimal => {
                    let mid = sorted.len() / 2;
                    if sorted.len() % 2 == 1 {
                        match sorted.get(mid) {
                            Some(Val::Decimal(d)) => {
                                PrimResult::Ok(Val::OptSome(Box::new(Val::Decimal(d.clone()))))
                            }
                            _ => PrimResult::Wrong,
                        }
                    } else {
                        match (sorted.get(mid - 1), sorted.get(mid)) {
                            (Some(Val::Decimal(lo)), Some(Val::Decimal(hi))) => {
                                let two = BigInt::from(2i64);
                                let avg = (lo + hi).div_euclid(&two).unwrap_or(BigInt::ZERO);
                                if avg.in_decimal_range() {
                                    PrimResult::Ok(Val::OptSome(Box::new(Val::Decimal(avg))))
                                } else {
                                    PrimResult::Stopped(Bug {
                                        kind: BugKind::DecimalOverflow,
                                        message: "Decimal overflow in median".to_string(),
                                    })
                                }
                            }
                            _ => PrimResult::Wrong,
                        }
                    }
                }
                ScalarTy::Option(inner) if **inner == ScalarTy::Float => PrimResult::Ok(
                    Val::OptSome(Box::new(Val::Float(median_sorted_floats(&sorted)))),
                ),
                _ => PrimResult::Wrong,
            }
        }
        AggOp::Variance => {
            if sorted.is_empty() {
                PrimResult::Ok(Val::OptNone)
            } else {
                PrimResult::Ok(Val::OptSome(Box::new(Val::Float(variance_sorted_floats(
                    &sorted,
                )))))
            }
        }
        AggOp::Stddev => {
            if sorted.is_empty() {
                PrimResult::Ok(Val::OptNone)
            } else {
                PrimResult::Ok(Val::OptSome(Box::new(Val::Float(stddev_sorted_floats(
                    &sorted,
                )))))
            }
        }
        AggOp::Percentile(p) => {
            if sorted.is_empty() {
                PrimResult::Ok(Val::OptNone)
            } else {
                PrimResult::Ok(Val::OptSome(Box::new(Val::Float(
                    percentile_sorted_floats(p, &sorted),
                ))))
            }
        }
        AggOp::Min => match sorted.first() {
            None => PrimResult::Ok(Val::OptNone),
            Some(v) => PrimResult::Ok(Val::OptSome(Box::new(v.clone()))),
        },
        AggOp::Max => match sorted.last() {
            None => PrimResult::Ok(Val::OptNone),
            Some(v) => PrimResult::Ok(Val::OptSome(Box::new(v.clone()))),
        },
        AggOp::First => match non_null.first() {
            None => PrimResult::Ok(Val::OptNone),
            Some(v) => PrimResult::Ok(Val::OptSome(Box::new(v.clone()))),
        },
        AggOp::Last => match non_null.last() {
            None => PrimResult::Ok(Val::OptNone),
            Some(v) => PrimResult::Ok(Val::OptSome(Box::new(v.clone()))),
        },
    }
}

fn extract_key_vals(cols: &[ColSpec], key_names: &[Ident], row: &TableRow) -> Option<Vec<Val>> {
    let mut out = Vec::with_capacity(key_names.len());
    for k in key_names {
        let (idx, _) = lookup_col_idx(cols, k)?;
        out.push(row.cells.get(idx)?.clone());
    }
    Some(out)
}

fn extract_all_rows_key_vals(
    cols: &[ColSpec],
    key_names: &[Ident],
    rows: &[TableRow],
) -> Option<Vec<Vec<Val>>> {
    rows.iter()
        .map(|r| extract_key_vals(cols, key_names, r))
        .collect()
}

fn project_rows_by_indices(idxs: &[usize], rows: &[TableRow]) -> Option<Vec<TableRow>> {
    let mut out = Vec::with_capacity(rows.len());
    for r in rows {
        let mut cells = Vec::with_capacity(idxs.len());
        for &i in idxs {
            cells.push(r.cells.get(i)?.clone());
        }
        out.push(TableRow {
            cells,
            group_meta: None,
        });
    }
    Some(out)
}

fn row_lt_by_keys(
    cols: &[ColSpec],
    keys: &[(Ident, SortDir)],
    r1: &TableRow,
    r2: &TableRow,
) -> bool {
    for (k, dir) in keys {
        let Some((idx, _)) = lookup_col_idx(cols, k) else {
            return false;
        };
        let (Some(v1), Some(v2)) = (r1.cells.get(idx), r2.cells.get(idx)) else {
            return false;
        };
        match dir {
            SortDir::Asc => {
                if val_lt(v1, v2) {
                    return true;
                }
                if val_lt(v2, v1) {
                    return false;
                }
            }
            SortDir::Desc => {
                if val_lt(v2, v1) {
                    return true;
                }
                if val_lt(v1, v2) {
                    return false;
                }
            }
        }
    }
    false
}

fn check_unique_join_keys(
    cols: &[ColSpec],
    key_names: &[Ident],
    key_tags: &TagSet,
    rows: &[TableRow],
) -> Option<Bug> {
    for (i1, r1) in rows.iter().enumerate() {
        let kv1 = extract_key_vals(cols, key_names, r1)?;
        for (offset, r2) in rows[i1 + 1..].iter().enumerate() {
            if let Some(kv2) = extract_key_vals(cols, key_names, r2)
                && val_list_eq(&kv1, &kv2)
            {
                let i2 = i1 + 1 + offset;
                let key_val = if kv1.len() == 1 {
                    kv1.into_iter().next().unwrap_or(Val::Unit)
                } else {
                    Val::Tuple(kv1)
                };
                let rendered_key = format_diag_detail(key_tags, &key_val);
                return Some(Bug {
                    kind: BugKind::JoinCardinality,
                    message: format!("duplicate key {rendered_key} (2 rows: {i1}, {i2})"),
                });
            }
        }
    }
    None
}

fn clamp_int64_usize(n: usize) -> BigInt {
    let i = BigInt::from(n);
    if i.in_int64_range() {
        i
    } else {
        BigInt::from(INT64_MAX)
    }
}

fn eval_window_compute_cell(
    cols: &[ColSpec],
    item: &WindowItem,
    target_ty: &ScalarTy,
    part_rows: &[TableRow],
    pos_in_part: usize,
) -> Option<Val> {
    match &item.win_fn {
        WindowFn::RowNumber => Some(Val::Int(clamp_int64_usize(pos_in_part + 1))),
        WindowFn::Rank { col } => {
            let (c_idx, _) = lookup_col_idx(cols, col)?;
            let Some(cur_row) = part_rows.get(pos_in_part) else {
                return Some(Val::Int(BigInt::one()));
            };
            let Some(cur_val) = cur_row.cells.get(c_idx) else {
                return Some(Val::Int(BigInt::one()));
            };
            let strictly_less = part_rows[..pos_in_part]
                .iter()
                .filter(|pr| pr.cells.get(c_idx).is_some_and(|pv| val_lt(pv, cur_val)))
                .count();
            Some(Val::Int(clamp_int64_usize(strictly_less + 1)))
        }
        WindowFn::Lag { col, offset } => {
            let (c_idx, c_spec) = lookup_col_idx(cols, col)?;
            let Some(off) = offset.to_usize() else {
                return Some(Val::OptNone);
            };
            if pos_in_part < off {
                Some(Val::OptNone)
            } else {
                match part_rows
                    .get(pos_in_part - off)
                    .and_then(|r| r.cells.get(c_idx))
                {
                    None => Some(Val::OptNone),
                    Some(prev_val) => Some(wrap_into_option_val(&c_spec.ty, prev_val.clone())),
                }
            }
        }
        WindowFn::Lead { col, offset } => {
            let (c_idx, c_spec) = lookup_col_idx(cols, col)?;
            let Some(off) = offset.to_usize() else {
                return Some(Val::OptNone);
            };
            let Some(next_idx) = pos_in_part.checked_add(off) else {
                return Some(Val::OptNone);
            };
            match part_rows.get(next_idx).and_then(|r| r.cells.get(c_idx)) {
                None => Some(Val::OptNone),
                Some(next_val) => Some(wrap_into_option_val(&c_spec.ty, next_val.clone())),
            }
        }
        WindowFn::RunningSum { col } => {
            let (c_idx, _) = lookup_col_idx(cols, col)?;
            let end = (pos_in_part + 1).min(part_rows.len());
            let vals: Vec<Val> = part_rows[..end]
                .iter()
                .filter_map(|pr| pr.cells.get(c_idx).cloned())
                .collect();
            match eval_agg_clean(AggOp::Sum, target_ty, &vals) {
                PrimResult::Ok(v) => Some(v),
                _ => Some(default_val_for_scalar(target_ty)),
            }
        }
        WindowFn::RollingMean { col, window_size } => {
            let (c_idx, _) = lookup_col_idx(cols, col)?;
            let end = (pos_in_part + 1).min(part_rows.len());
            let w_sz = window_size.to_usize_saturating();
            let start_idx = (pos_in_part + 1).saturating_sub(w_sz);
            let floats: Vec<f64> = part_rows[start_idx.min(end)..end]
                .iter()
                .filter_map(|pr| pr.cells.get(c_idx).and_then(unwrap_numeric_float))
                .collect();
            if floats.is_empty() {
                Some(Val::OptNone)
            } else {
                let total = floats.iter().copied().fold(0.0_f64, |acc, x| acc + x);
                Some(Val::OptSome(Box::new(Val::Float(Float64::from_f64(
                    total / (floats.len() as f64),
                )))))
            }
        }
    }
}

fn eval_window_on_table(
    tv: &TableVal,
    item: &WindowItem,
    out_cols: Vec<ColSpec>,
) -> Option<TableVal> {
    let target_col_spec = out_cols.iter().find(|c| c.name == item.name)?;
    let existing_idx = lookup_col_idx(&tv.cols, &item.name).map(|(i, _)| i);
    let indexed_rows: Vec<(TableRow, usize)> = tv
        .rows
        .iter()
        .cloned()
        .enumerate()
        .map(|(i, r)| (r, i))
        .collect();
    let sorted_indexed = if item.order.is_empty() {
        indexed_rows.clone()
    } else {
        insertion_sort_by(&indexed_rows, |a, b| {
            row_lt_by_keys(&tv.cols, &item.order, &a.0, &b.0)
        })
    };
    let mut new_rows = Vec::with_capacity(indexed_rows.len());
    for (row, orig_idx) in &indexed_rows {
        let my_key = extract_key_vals(&tv.cols, &item.over, row)?;
        let part_indexed: Vec<&(TableRow, usize)> = sorted_indexed
            .iter()
            .filter(|(r2, _)| {
                extract_key_vals(&tv.cols, &item.over, r2)
                    .is_some_and(|k2| val_list_eq(&my_key, &k2))
            })
            .collect();
        let pos_in_part = part_indexed
            .iter()
            .position(|(_, i2)| *i2 == *orig_idx)
            .unwrap_or(0);
        let part_rows: Vec<TableRow> = part_indexed.iter().map(|(r, _)| r.clone()).collect();
        let w_val =
            eval_window_compute_cell(&tv.cols, item, &target_col_spec.ty, &part_rows, pos_in_part)?;
        let mut new_cells = row.cells.clone();
        match existing_idx {
            Some(idx) => {
                if let Some(slot) = new_cells.get_mut(idx) {
                    *slot = w_val;
                }
            }
            None => new_cells.push(w_val),
        }
        new_rows.push(TableRow {
            cells: new_cells,
            group_meta: None,
        });
    }
    Some(TableVal {
        cols: out_cols,
        rows: new_rows,
    })
}

fn eval_window_items(mut cur_tv: TableVal, items: &[WindowItem]) -> Option<TableVal> {
    for it in items {
        let next_cols = apply_window_item(&cur_tv.cols, &TagSet::empty(), it).ok()?;
        cur_tv = eval_window_on_table(&cur_tv, it, next_cols)?;
    }
    Some(cur_tv)
}

fn dedup_table_rows(
    cols: &[ColSpec],
    key_names: &[Ident],
    rows: &[TableRow],
) -> Option<Vec<TableRow>> {
    let mut seen: Vec<Vec<Val>> = Vec::new();
    let mut out = Vec::new();
    for r in rows {
        let kv = extract_key_vals(cols, key_names, r)?;
        if !seen.iter().any(|sk| val_list_eq(sk, &kv)) {
            seen.push(kv);
            out.push(TableRow {
                cells: r.cells.clone(),
                group_meta: None,
            });
        }
    }
    Some(out)
}

struct JoinExecCtx<'a> {
    kind: JoinKind,
    l_cols: &'a [ColSpec],
    r_cols: &'a [ColSpec],
    l_key_names: &'a [Ident],
    r_key_names: &'a [Ident],
    r_keep_idxs: &'a [(&'a ColSpec, usize)],
    is_left_outer: bool,
}

fn join_table_rows(
    ctx: &JoinExecCtx<'_>,
    r_rows: &[TableRow],
    l_rows: &[TableRow],
) -> Option<Vec<TableRow>> {
    let mut out = Vec::new();
    for l_row in l_rows {
        let lkv = extract_key_vals(ctx.l_cols, ctx.l_key_names, l_row)?;
        let matching_r: Vec<&TableRow> = r_rows
            .iter()
            .filter(|r_row| {
                extract_key_vals(ctx.r_cols, ctx.r_key_names, r_row)
                    .is_some_and(|rkv| val_list_eq(&lkv, &rkv))
            })
            .collect();
        match ctx.kind {
            JoinKind::Semi => {
                if !matching_r.is_empty() {
                    out.push(TableRow {
                        cells: l_row.cells.clone(),
                        group_meta: None,
                    });
                }
            }
            JoinKind::Anti => {
                if matching_r.is_empty() {
                    out.push(TableRow {
                        cells: l_row.cells.clone(),
                        group_meta: None,
                    });
                }
            }
            _ => {
                if matching_r.is_empty() {
                    if ctx.is_left_outer {
                        let mut cells = l_row.cells.clone();
                        cells.extend(std::iter::repeat_n(Val::OptNone, ctx.r_keep_idxs.len()));
                        out.push(TableRow {
                            cells,
                            group_meta: None,
                        });
                    }
                } else {
                    for mr in matching_r {
                        let mut cells = l_row.cells.clone();
                        for &(rc, idx) in ctx.r_keep_idxs {
                            let cell = mr.cells.get(idx)?.clone();
                            cells.push(if ctx.is_left_outer {
                                wrap_into_option_val(&rc.ty, cell)
                            } else {
                                cell
                            });
                        }
                        out.push(TableRow {
                            cells,
                            group_meta: None,
                        });
                    }
                }
            }
        }
    }
    Some(out)
}

fn suppress_group_size(distinct_by: &Option<Ident>, r: &TableRow) -> usize {
    match r.group_meta {
        None => 0,
        Some(gm) => match distinct_by {
            None => gm.row_count,
            Some(_) => gm.distinct_count.unwrap_or(0),
        },
    }
}

fn extract_group_key_cells(cols: &[ColSpec], cells: &[Val]) -> Vec<Val> {
    cols.iter()
        .zip(cells)
        .filter(|(c, _)| c.agg_kind == AggKind::GroupKey)
        .map(|(_, v)| v.clone())
        .collect()
}

fn suppress_row_lt(
    cols: &[ColSpec],
    distinct_by: &Option<Ident>,
    a: &TableRow,
    b: &TableRow,
) -> bool {
    let sa = suppress_group_size(distinct_by, a);
    let sb = suppress_group_size(distinct_by, b);
    if sa < sb {
        true
    } else if sb < sa {
        false
    } else {
        let ka = extract_group_key_cells(cols, &a.cells);
        let kb = extract_group_key_cells(cols, &b.cells);
        val_list_lt(&ka, &kb)
    }
}

fn mask_agg_cells(cols: &[ColSpec], cells: &[Val]) -> Vec<Val> {
    cols.iter()
        .zip(cells)
        .map(|(c, v)| match c.agg_kind {
            AggKind::Blending | AggKind::NonBlending => Val::OptNone,
            AggKind::GroupKey | AggKind::Raw => v.clone(),
        })
        .collect()
}

fn wrap_agg_cells(cols: &[ColSpec], cells: &[Val]) -> Vec<Val> {
    cols.iter()
        .zip(cells)
        .map(|(c, v)| match c.agg_kind {
            AggKind::Blending | AggKind::NonBlending => wrap_into_option_val(&c.ty, v.clone()),
            AggKind::GroupKey | AggKind::Raw => v.clone(),
        })
        .collect()
}

// ---------------------------------------------------------------------------
// Case Matching & Sequential Evaluation Helpers
// ---------------------------------------------------------------------------

fn match_case_val(
    prog: &Program,
    scrut_val: &Val,
    scrut_lty: &LTy,
    arm_pc: &TagSet,
) -> Option<(Ident, Vec<(LTy, Val)>)> {
    let s_tags = scrut_lty.effective_tags().union(arm_pc);
    match (&scrut_lty.ty, scrut_val) {
        (Ty::Bool, Val::Bool(true)) => Some(("true".to_string(), Vec::new())),
        (Ty::Bool, Val::Bool(false)) => Some(("false".to_string(), Vec::new())),
        (Ty::Option(_), Val::OptNone) => Some(("None".to_string(), Vec::new())),
        (Ty::Option(inner), Val::OptSome(u)) => Some((
            "Some".to_string(),
            vec![(LTy::new(inner.as_ref().clone(), s_tags), u.as_ref().clone())],
        )),
        (Ty::Result { ok_ty, .. }, Val::ResOk(u)) => Some((
            "Ok".to_string(),
            vec![(LTy::new(ok_ty.as_ref().clone(), s_tags), u.as_ref().clone())],
        )),
        (Ty::Result { err_ty, .. }, Val::ResErr(e)) => Some((
            "Error".to_string(),
            vec![(
                LTy::new(err_ty.as_ref().clone(), s_tags),
                e.as_ref().clone(),
            )],
        )),
        (
            Ty::Data(d_name),
            Val::Ctor {
                type_name: v_type,
                ctor_name: c_name,
                fields,
            },
        ) => {
            if d_name != v_type {
                return None;
            }
            let d_decl = prog.find_data(d_name)?;
            let c_decl = d_decl.ctors.iter().find(|c| c.name == *c_name)?;
            if fields.len() == c_decl.fields.len() {
                let bound = c_decl
                    .fields
                    .iter()
                    .map(|f| f.add_tags(&s_tags))
                    .zip(fields.iter().cloned())
                    .collect();
                Some((c_name.clone(), bound))
            } else {
                None
            }
        }
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// Stack-Lean Internal Evaluation Step (100% Iterative Heap Stack)
// ---------------------------------------------------------------------------

/// Internal evaluation result that threads `World` by `&mut World` rather than
/// returning a ~400-byte `World` by value on every stack frame.
enum EvalStep {
    Ok(Val),
    Stopped(Bug),
    Failed(String),
    Jumped(Ident, Vec<Val>),
    Wrong,
    OutOfFuel,
}

impl EvalStep {
    fn into_outcome(self, world: World) -> Outcome {
        match self {
            Self::Ok(v) => Outcome::Ok(v, world),
            Self::Stopped(b) => Outcome::Stopped(b, world),
            Self::Failed(m) => Outcome::Failed(m, world),
            Self::Jumped(l, vs) => Outcome::Jumped(l, vs, world),
            Self::Wrong => Outcome::Wrong,
            Self::OutOfFuel => Outcome::OutOfFuel,
        }
    }
}

fn eval_host_step(prog: &Program, op: &HostOp, vs: &[Val], world: &mut World) -> EvalStep {
    let owned_w = std::mem::take(world);
    match eval_host_op(prog, op, vs, owned_w) {
        Outcome::Ok(v, w1) => {
            *world = w1;
            EvalStep::Ok(v)
        }
        Outcome::Stopped(b, w1) => {
            *world = w1;
            EvalStep::Stopped(b)
        }
        Outcome::Failed(m, w1) => {
            *world = w1;
            EvalStep::Failed(m)
        }
        Outcome::Jumped(l, jv, w1) => {
            *world = w1;
            EvalStep::Jumped(l, jv)
        }
        Outcome::Wrong => EvalStep::Wrong,
        Outcome::OutOfFuel => EvalStep::OutOfFuel,
    }
}

fn derive_item_target_name(item: &DeriveItem) -> &str {
    match item {
        DeriveItem::ColExpr { name, .. } | DeriveItem::BucketCol { name, .. } => name,
    }
}

fn eval_derive_cell(
    fuel: usize,
    prog: &Program,
    env: &EnvList,
    cur_cols: &[ColSpec],
    row: &TableRow,
    item: &DeriveItem,
) -> PrimResult {
    match item {
        DeriveItem::ColExpr { expr, .. } => {
            eval_row_expr_inner(fuel, prog, env, cur_cols, row, expr)
        }
        DeriveItem::BucketCol {
            source,
            cuts,
            labels,
            ..
        } => {
            let Some((s_idx, _)) = lookup_col_idx(cur_cols, source) else {
                return PrimResult::Wrong;
            };
            let Some(s_val) = row.cells.get(s_idx) else {
                return PrimResult::Wrong;
            };
            let cut_vals: Vec<Val> = cuts.iter().map(eval_literal).collect();
            match eval_bucket_cell(s_val, &cut_vals, labels) {
                Some(b_val) => PrimResult::Ok(b_val),
                None => PrimResult::Wrong,
            }
        }
    }
}

fn eval_derive_items(
    fuel: usize,
    prog: &Program,
    env: &EnvList,
    mut cur_tv: TableVal,
    items: &[DeriveItem],
) -> EvalStep {
    for item in items {
        let Ok(next_cols) = apply_derive_item_arc(prog, env.as_arc_ty_env(), &cur_tv.cols, item)
        else {
            return EvalStep::Wrong;
        };
        let existing_idx =
            lookup_col_idx(&cur_tv.cols, derive_item_target_name(item)).map(|(i, _)| i);
        let mut next_rows = Vec::with_capacity(cur_tv.rows.len());
        for r in &cur_tv.rows {
            match eval_derive_cell(fuel, prog, env, &cur_tv.cols, r, item) {
                PrimResult::Ok(new_cell) => {
                    let mut new_cells = r.cells.clone();
                    match existing_idx {
                        Some(idx) => {
                            if let Some(slot) = new_cells.get_mut(idx) {
                                *slot = new_cell;
                            }
                        }
                        None => new_cells.push(new_cell),
                    }
                    next_rows.push(TableRow {
                        cells: new_cells,
                        group_meta: None,
                    });
                }
                PrimResult::Stopped(b) => return EvalStep::Stopped(b),
                PrimResult::OutOfFuel => return EvalStep::OutOfFuel,
                PrimResult::Wrong => return EvalStep::Wrong,
            }
        }
        cur_tv = TableVal {
            cols: next_cols,
            rows: next_rows,
        };
    }
    EvalStep::Ok(Val::Table(cur_tv))
}

// ---------------------------------------------------------------------------
// Fuel-Indexed Mutual Big-Step Evaluator (`eval_row_expr`, `eval`, `eval_plan`)
// ---------------------------------------------------------------------------

#[must_use]
pub fn eval_row_expr(
    fuel: usize,
    prog: &Program,
    env: &[EnvEntry],
    cols: &[ColSpec],
    row: &TableRow,
    re: &RowExpr,
) -> PrimResult {
    with_large_stack(|| {
        let env_list = EnvList::from_slice(env);
        eval_row_expr_inner(fuel, prog, &env_list, cols, row, re)
    })
}

enum RowSeqKind<'a> {
    Prim(&'a PrimOp),
    CallPure {
        fn_name: &'a Ident,
        call_fuel: usize,
    },
}

enum RowFrame<'a> {
    Seq {
        remaining: &'a [RowExpr],
        list_fuel: usize,
        vals: Vec<Val>,
        kind: RowSeqKind<'a>,
    },
    IfCond {
        fuel_next: usize,
        then_br: &'a RowExpr,
        else_br: &'a RowExpr,
    },
    CoalesceOpt {
        fuel_next: usize,
        default_expr: &'a RowExpr,
    },
}

fn eval_row_expr_finish_seq(prog: &Program, vals: Vec<Val>, kind: RowSeqKind<'_>) -> PrimResult {
    match kind {
        RowSeqKind::Prim(op) => eval_prim_op(op, &vals),
        RowSeqKind::CallPure { fn_name, call_fuel } => {
            let Some(f_decl) = prog.find_fun(fn_name) else {
                return PrimResult::Wrong;
            };
            if vals.len() != f_decl.params.len() {
                return PrimResult::Wrong;
            }
            let call_entries: Vec<EnvEntry> = f_decl
                .params
                .iter()
                .zip(vals)
                .rev()
                .map(|((p_name, p_lty), v)| EnvEntry {
                    name: p_name.clone(),
                    lty: p_lty.clone(),
                    val: v,
                })
                .collect();
            let call_env = EnvList::from_vec(call_entries);
            let mut isolated_world = World::default();
            match eval_inner(
                call_fuel,
                prog,
                &call_env,
                &TagSet::empty(),
                &mut isolated_world,
                &f_decl.body,
            ) {
                EvalStep::Ok(v) => PrimResult::Ok(v),
                EvalStep::Stopped(b) => PrimResult::Stopped(b),
                EvalStep::Failed(m) => PrimResult::Stopped(Bug {
                    kind: BugKind::PromiseViolation,
                    message: m,
                }),
                EvalStep::OutOfFuel => PrimResult::OutOfFuel,
                EvalStep::Jumped(_, _) | EvalStep::Wrong => PrimResult::Wrong,
            }
        }
    }
}

fn eval_row_expr_inner(
    init_fuel: usize,
    prog: &Program,
    env: &EnvList,
    cols: &[ColSpec],
    row: &TableRow,
    init_re: &RowExpr,
) -> PrimResult {
    let mut frames: Vec<RowFrame<'_>> = Vec::new();
    let mut cur_target: Option<(usize, &RowExpr)> = Some((init_fuel, init_re));
    let mut cur_res: Option<PrimResult> = None;

    loop {
        if let Some((fuel, re)) = cur_target.take() {
            let Some(fuel_next) = fuel.checked_sub(1) else {
                return PrimResult::OutOfFuel;
            };
            match re {
                RowExpr::Lit(v) => cur_res = Some(PrimResult::Ok(eval_literal(v))),
                RowExpr::Col(name) => {
                    cur_res = Some(match lookup_col_idx(cols, name) {
                        Some((idx, _)) => match row.cells.get(idx) {
                            Some(cell) => PrimResult::Ok(cell.clone()),
                            None => PrimResult::Wrong,
                        },
                        None => PrimResult::Wrong,
                    });
                }
                RowExpr::OuterVar(name) => {
                    cur_res = Some(match env.lookup(name) {
                        Some((_, v)) => PrimResult::Ok(v.clone()),
                        None => PrimResult::Wrong,
                    });
                }
                RowExpr::ConstRef(name) => {
                    cur_res = Some(match prog.find_const(name) {
                        Some(c_decl) => PrimResult::Ok(eval_literal(&c_decl.value)),
                        None => PrimResult::Wrong,
                    });
                }
                RowExpr::Prim { op, args } => {
                    if let Some((first, rest)) = args.split_first() {
                        let Some(elem_fuel) = fuel_next.checked_sub(1) else {
                            return PrimResult::OutOfFuel;
                        };
                        frames.push(RowFrame::Seq {
                            remaining: rest,
                            list_fuel: elem_fuel,
                            vals: Vec::with_capacity(args.len()),
                            kind: RowSeqKind::Prim(op),
                        });
                        cur_target = Some((elem_fuel, first));
                    } else {
                        cur_res = Some(eval_prim_op(op, &[]));
                    }
                }
                RowExpr::IfE {
                    cond,
                    then_br,
                    else_br,
                } => {
                    frames.push(RowFrame::IfCond {
                        fuel_next,
                        then_br,
                        else_br,
                    });
                    cur_target = Some((fuel_next, cond));
                }
                RowExpr::Coalesce {
                    opt_expr,
                    default_expr,
                } => {
                    frames.push(RowFrame::CoalesceOpt {
                        fuel_next,
                        default_expr,
                    });
                    cur_target = Some((fuel_next, opt_expr));
                }
                RowExpr::CallPure { fn_name, args } => {
                    if let Some((first, rest)) = args.split_first() {
                        let Some(elem_fuel) = fuel_next.checked_sub(1) else {
                            return PrimResult::OutOfFuel;
                        };
                        frames.push(RowFrame::Seq {
                            remaining: rest,
                            list_fuel: elem_fuel,
                            vals: Vec::with_capacity(args.len()),
                            kind: RowSeqKind::CallPure {
                                fn_name,
                                call_fuel: fuel_next,
                            },
                        });
                        cur_target = Some((elem_fuel, first));
                    } else {
                        cur_res = Some(eval_row_expr_finish_seq(
                            prog,
                            Vec::new(),
                            RowSeqKind::CallPure {
                                fn_name,
                                call_fuel: fuel_next,
                            },
                        ));
                    }
                }
            }
            continue;
        }

        let Some(res) = cur_res.take() else {
            unreachable!("either cur_target or cur_res is populated");
        };
        let v = match res {
            PrimResult::Ok(v) => v,
            other => return other,
        };
        let Some(frame) = frames.pop() else {
            return PrimResult::Ok(v);
        };
        match frame {
            RowFrame::Seq {
                remaining,
                list_fuel,
                mut vals,
                kind,
            } => {
                vals.push(v);
                if let Some((next_re, rest)) = remaining.split_first() {
                    let Some(next_elem_fuel) = list_fuel.checked_sub(1) else {
                        return PrimResult::OutOfFuel;
                    };
                    frames.push(RowFrame::Seq {
                        remaining: rest,
                        list_fuel: next_elem_fuel,
                        vals,
                        kind,
                    });
                    cur_target = Some((next_elem_fuel, next_re));
                } else {
                    cur_res = Some(eval_row_expr_finish_seq(prog, vals, kind));
                }
            }
            RowFrame::IfCond {
                fuel_next,
                then_br,
                else_br,
            } => match v {
                Val::Bool(true) => cur_target = Some((fuel_next, then_br)),
                Val::Bool(false) => cur_target = Some((fuel_next, else_br)),
                _ => return PrimResult::Wrong,
            },
            RowFrame::CoalesceOpt {
                fuel_next,
                default_expr,
            } => {
                let mut v = v;
                match &mut v {
                    Val::OptNone => cur_target = Some((fuel_next, default_expr)),
                    Val::OptSome(inner) => {
                        cur_res = Some(PrimResult::Ok(std::mem::take(inner.as_mut())));
                    }
                    _ => return PrimResult::Wrong,
                }
            }
        }
    }
}

#[must_use]
pub fn eval(
    fuel: usize,
    prog: &Program,
    env: &[EnvEntry],
    pc: &TagSet,
    mut world: World,
    expr: &Expr,
) -> Outcome {
    with_large_stack(|| {
        let env_list = EnvList::from_slice(env);
        let step = eval_inner(fuel, prog, &env_list, pc, &mut world, expr);
        step.into_outcome(world)
    })
}

#[must_use]
pub fn eval_plan(
    fuel: usize,
    prog: &Program,
    env: &[EnvEntry],
    pc: &TagSet,
    mut world: World,
    plan: &Plan,
) -> Outcome {
    with_large_stack(|| {
        let env_list = EnvList::from_slice(env);
        let step = eval_plan_inner(fuel, prog, &env_list, pc, &mut world, plan);
        step.into_outcome(world)
    })
}

enum EvalTarget<'a> {
    Expr {
        fuel: usize,
        env: EnvList,
        pc: TagSet,
        expr: &'a Expr,
    },
    Plan {
        fuel: usize,
        env: EnvList,
        pc: TagSet,
        plan: &'a Plan,
    },
}

enum SeqKind<'a> {
    Prim(&'a PrimOp),
    Host(&'a HostOp),
    Tuple,
    Ctor(&'a Ident, &'a Ident),
    Jump(&'a Ident),
    Call(&'a Ident),
    App {
        params: Vec<(Ident, LTy)>,
        fn_pc: TagSet,
        body: Arc<Expr>,
        captured_env: EnvList,
    },
}

enum EvalFrame<'a> {
    LetBound {
        fuel_next: usize,
        name: &'a Ident,
        decl_lty: &'a LTy,
        env: EnvList,
        pc: TagSet,
        body: &'a Expr,
    },
    IfCond {
        fuel_next: usize,
        env: EnvList,
        br_pc: TagSet,
        then_br: &'a Expr,
        else_br: &'a Expr,
    },
    CaseScrut {
        fuel_next: usize,
        env: EnvList,
        scrut_lty: LTy,
        arm_pc: TagSet,
        arms: &'a [CaseArm],
    },
    AppFn {
        fuel_next: usize,
        env: EnvList,
        pc: TagSet,
        args: &'a [Expr],
    },
    Seq {
        fuel_next: usize,
        env: EnvList,
        pc: TagSet,
        remaining: &'a [Expr],
        vals: Vec<Val>,
        kind: SeqKind<'a>,
    },
    CallBoundary,
    JoinCatch {
        fuel_next: usize,
        base_env: EnvList,
        label: &'a Ident,
        params: &'a [(Ident, LTy)],
        join_pc: TagSet,
        rhs: &'a Expr,
    },
    Proj {
        idx: &'a BigInt,
    },
    StopDetail {
        kind: BugKind,
        eff_tags: TagSet,
    },
    FailMsg,
    PlanSourceExpr,
    PlanSourceDB {
        table_name: &'a Ident,
        schema: &'a TableTy,
    },
    PlanJoinLeft {
        fuel_next: usize,
        env: EnvList,
        pc: TagSet,
        kind: JoinKind,
        right: &'a Plan,
        on: &'a JoinOn,
        suffixes: &'a Option<(String, String)>,
    },
    PlanJoinRight {
        pc: TagSet,
        kind: JoinKind,
        l_tv: TableVal,
        on: &'a JoinOn,
        suffixes: &'a Option<(String, String)>,
    },
    PlanUnionLeft {
        fuel_next: usize,
        env: EnvList,
        pc: TagSet,
        right: &'a Plan,
    },
    PlanUnionRight {
        l_tv: TableVal,
    },
    PlanPseudoInput {
        fuel_next: usize,
        env: EnvList,
        pc: TagSet,
        col: &'a Ident,
        secret: &'a Expr,
    },
    PlanPseudoSecret {
        pc: TagSet,
        col: &'a Ident,
        tv: TableVal,
    },
    PlanUnary {
        fuel_next: usize,
        env: EnvList,
        pc: TagSet,
        stage: &'a Plan,
    },
    PlanCheckedUnary {
        fuel_next: usize,
        env: EnvList,
        stage: &'a Plan,
        out_tt: TableTy,
    },
}

fn eval_inner(
    fuel: usize,
    prog: &Program,
    env: &EnvList,
    pc: &TagSet,
    world: &mut World,
    expr: &Expr,
) -> EvalStep {
    eval_ir_iter(
        prog,
        world,
        EvalTarget::Expr {
            fuel,
            env: env.clone(),
            pc: pc.clone(),
            expr,
        },
    )
}

fn eval_plan_inner(
    fuel: usize,
    prog: &Program,
    env: &EnvList,
    pc: &TagSet,
    world: &mut World,
    plan: &Plan,
) -> EvalStep {
    eval_ir_iter(
        prog,
        world,
        EvalTarget::Plan {
            fuel,
            env: env.clone(),
            pc: pc.clone(),
            plan,
        },
    )
}

fn finish_eval_seq<'a>(
    prog: &'a Program,
    world: &mut World,
    lam_bodies: &HashMap<usize, &'a Expr>,
    frames: &mut Vec<EvalFrame<'a>>,
    fuel_next: usize,
    vals: Vec<Val>,
    kind: SeqKind<'a>,
) -> (Option<EvalTarget<'a>>, Option<EvalStep>) {
    match kind {
        SeqKind::Prim(op) => {
            let step = match eval_prim_op(op, &vals) {
                PrimResult::Ok(v) => EvalStep::Ok(v),
                PrimResult::Stopped(b) => EvalStep::Stopped(b),
                PrimResult::OutOfFuel => EvalStep::OutOfFuel,
                PrimResult::Wrong => EvalStep::Wrong,
            };
            (None, Some(step))
        }
        SeqKind::Host(op) => (None, Some(eval_host_step(prog, op, &vals, world))),
        SeqKind::Tuple => (None, Some(EvalStep::Ok(Val::Tuple(vals)))),
        SeqKind::Ctor(type_name, ctor_name) => (
            None,
            Some(EvalStep::Ok(Val::Ctor {
                type_name: type_name.clone(),
                ctor_name: ctor_name.clone(),
                fields: vals,
            })),
        ),
        SeqKind::Jump(label) => (None, Some(EvalStep::Jumped(label.clone(), vals))),
        SeqKind::Call(fn_name) => {
            let Some(f_decl) = prog.find_fun(fn_name) else {
                return (None, Some(EvalStep::Wrong));
            };
            if vals.len() != f_decl.params.len() {
                return (None, Some(EvalStep::Wrong));
            }
            let call_entries: Vec<EnvEntry> = f_decl
                .params
                .iter()
                .zip(vals)
                .rev()
                .map(|((p_name, p_lty), a_val)| EnvEntry {
                    name: p_name.clone(),
                    lty: p_lty.clone(),
                    val: a_val,
                })
                .collect();
            let call_env = EnvList::from_vec(call_entries);
            if !matches!(frames.last(), Some(EvalFrame::CallBoundary)) {
                frames.push(EvalFrame::CallBoundary);
            }
            (
                Some(EvalTarget::Expr {
                    fuel: fuel_next,
                    env: call_env,
                    pc: f_decl.pc.clone(),
                    expr: &f_decl.body,
                }),
                None,
            )
        }
        SeqKind::App {
            params,
            fn_pc,
            body,
            captured_env,
        } => {
            if vals.len() != params.len() {
                return (None, Some(EvalStep::Wrong));
            }
            let arg_entries: Vec<EnvEntry> = params
                .into_iter()
                .zip(vals)
                .map(|((p_name, p_lty), a_val)| EnvEntry {
                    name: p_name,
                    lty: p_lty,
                    val: a_val,
                })
                .collect();
            let call_env = captured_env.prepend_entries(arg_entries);
            if let Some(&body_ref) = lam_bodies.get(&(Arc::as_ptr(&body) as usize)) {
                if !matches!(frames.last(), Some(EvalFrame::CallBoundary)) {
                    frames.push(EvalFrame::CallBoundary);
                }
                (
                    Some(EvalTarget::Expr {
                        fuel: fuel_next,
                        env: call_env,
                        pc: fn_pc,
                        expr: body_ref,
                    }),
                    None,
                )
            } else {
                let step = match eval_inner(fuel_next, prog, &call_env, &fn_pc, world, &body) {
                    EvalStep::Jumped(_, _) => EvalStep::Wrong,
                    other => other,
                };
                (None, Some(step))
            }
        }
    }
}

struct SeqStart<'a> {
    fuel_next: usize,
    env: EnvList,
    pc: TagSet,
    args: &'a [Expr],
    kind: SeqKind<'a>,
}

fn start_eval_seq<'a>(
    prog: &'a Program,
    world: &mut World,
    lam_bodies: &HashMap<usize, &'a Expr>,
    frames: &mut Vec<EvalFrame<'a>>,
    req: SeqStart<'a>,
) -> (Option<EvalTarget<'a>>, Option<EvalStep>) {
    if let Some((first, rest)) = req.args.split_first() {
        frames.push(EvalFrame::Seq {
            fuel_next: req.fuel_next,
            env: req.env.clone(),
            pc: req.pc.clone(),
            remaining: rest,
            vals: Vec::with_capacity(req.args.len()),
            kind: req.kind,
        });
        (
            Some(EvalTarget::Expr {
                fuel: req.fuel_next,
                env: req.env,
                pc: req.pc,
                expr: first,
            }),
            None,
        )
    } else {
        finish_eval_seq(
            prog,
            world,
            lam_bodies,
            frames,
            req.fuel_next,
            Vec::new(),
            req.kind,
        )
    }
}

fn eval_ir_iter<'a>(prog: &'a Program, world: &mut World, init_target: EvalTarget<'a>) -> EvalStep {
    let mut frames: Vec<EvalFrame<'a>> = Vec::new();
    let mut lam_bodies: HashMap<usize, &'a Expr> = HashMap::new();
    let mut cur_target: Option<EvalTarget<'a>> = Some(init_target);
    let mut cur_step: Option<EvalStep> = None;

    loop {
        if let Some(target) = cur_target.take() {
            match target {
                EvalTarget::Expr {
                    fuel,
                    env,
                    pc,
                    expr,
                } => {
                    let Some(fuel_next) = fuel.checked_sub(1) else {
                        return EvalStep::OutOfFuel;
                    };
                    match expr {
                        Expr::Lit(v) => cur_step = Some(EvalStep::Ok(eval_literal(v))),
                        Expr::Var(name) => {
                            cur_step = Some(match env.lookup(name) {
                                Some((_, v)) => EvalStep::Ok(v.clone()),
                                None => EvalStep::Wrong,
                            });
                        }
                        Expr::ConstRef(name) => {
                            cur_step = Some(match prog.find_const(name) {
                                Some(c_decl) => EvalStep::Ok(eval_literal(&c_decl.value)),
                                None => EvalStep::Wrong,
                            });
                        }
                        Expr::LetE {
                            name,
                            lty: decl_lty,
                            bound,
                            body,
                        } => {
                            frames.push(EvalFrame::LetBound {
                                fuel_next,
                                name,
                                decl_lty,
                                env: env.clone(),
                                pc: pc.clone(),
                                body,
                            });
                            cur_target = Some(EvalTarget::Expr {
                                fuel: fuel_next,
                                env,
                                pc,
                                expr: bound,
                            });
                        }
                        Expr::IfE {
                            cond,
                            then_br,
                            else_br,
                        } => {
                            let cond_tags =
                                check_expr_arc(prog, env.as_arc_ty_env(), &pc, true, cond, false)
                                    .map(|c_lty| c_lty.tags)
                                    .unwrap_or_default();
                            let br_pc = if cond_tags.is_empty() {
                                pc.clone()
                            } else {
                                pc.union(&cond_tags)
                            };
                            frames.push(EvalFrame::IfCond {
                                fuel_next,
                                env: env.clone(),
                                br_pc,
                                then_br,
                                else_br,
                            });
                            cur_target = Some(EvalTarget::Expr {
                                fuel: fuel_next,
                                env,
                                pc,
                                expr: cond,
                            });
                        }
                        Expr::CaseE { scrut, arms } => {
                            let Ok(scrut_lty) =
                                check_expr_arc(prog, env.as_arc_ty_env(), &pc, true, scrut, false)
                            else {
                                return EvalStep::Wrong;
                            };
                            let arm_pc = pc.union(&scrut_lty.effective_tags());
                            frames.push(EvalFrame::CaseScrut {
                                fuel_next,
                                env: env.clone(),
                                scrut_lty,
                                arm_pc,
                                arms,
                            });
                            cur_target = Some(EvalTarget::Expr {
                                fuel: fuel_next,
                                env,
                                pc,
                                expr: scrut,
                            });
                        }
                        Expr::Lam {
                            params,
                            pc: fn_pc,
                            ret: ret_lty,
                            body,
                        } => {
                            lam_bodies.insert(Arc::as_ptr(body) as usize, &**body);
                            cur_step = Some(EvalStep::Ok(Val::Closure(Box::new(
                                crate::oracle::value::ClosureVal {
                                    params: params.clone(),
                                    fn_pc: fn_pc.clone(),
                                    ret_lty: ret_lty.clone(),
                                    body: Arc::clone(body),
                                    captured_env: env,
                                },
                            ))));
                        }
                        Expr::App { fn_expr, args } => {
                            frames.push(EvalFrame::AppFn {
                                fuel_next,
                                env: env.clone(),
                                pc: pc.clone(),
                                args,
                            });
                            cur_target = Some(EvalTarget::Expr {
                                fuel: fuel_next,
                                env,
                                pc,
                                expr: fn_expr,
                            });
                        }
                        Expr::Call { fn_name, args } => {
                            let (t, s) = start_eval_seq(
                                prog,
                                world,
                                &lam_bodies,
                                &mut frames,
                                SeqStart {
                                    fuel_next,
                                    env,
                                    pc,
                                    args,
                                    kind: SeqKind::Call(fn_name),
                                },
                            );
                            cur_target = t;
                            cur_step = s;
                        }
                        Expr::Join {
                            label,
                            params,
                            rhs,
                            body,
                        } => {
                            let t_env = env.as_arc_ty_env();
                            let guess1 =
                                pc.union(&infer_jump_pc_arc(prog, label, t_env, &pc, body));
                            let rhs_t_env = t_env.extend_slice(params);
                            let join_pc = guess1
                                .union(&infer_jump_pc_arc(prog, label, &rhs_t_env, &guess1, rhs));
                            frames.push(EvalFrame::JoinCatch {
                                fuel_next,
                                base_env: env.clone(),
                                label,
                                params,
                                join_pc,
                                rhs,
                            });
                            cur_target = Some(EvalTarget::Expr {
                                fuel: fuel_next,
                                env,
                                pc,
                                expr: body,
                            });
                        }
                        Expr::Jump { label, args } => {
                            let (t, s) = start_eval_seq(
                                prog,
                                world,
                                &lam_bodies,
                                &mut frames,
                                SeqStart {
                                    fuel_next,
                                    env,
                                    pc,
                                    args,
                                    kind: SeqKind::Jump(label),
                                },
                            );
                            cur_target = t;
                            cur_step = s;
                        }
                        Expr::Tuple(elems) => {
                            let (t, s) = start_eval_seq(
                                prog,
                                world,
                                &lam_bodies,
                                &mut frames,
                                SeqStart {
                                    fuel_next,
                                    env,
                                    pc,
                                    args: elems,
                                    kind: SeqKind::Tuple,
                                },
                            );
                            cur_target = t;
                            cur_step = s;
                        }
                        Expr::Proj { tup, idx } => {
                            frames.push(EvalFrame::Proj { idx });
                            cur_target = Some(EvalTarget::Expr {
                                fuel: fuel_next,
                                env,
                                pc,
                                expr: tup,
                            });
                        }
                        Expr::Ctor {
                            type_name,
                            ctor_name,
                            args,
                        } => {
                            let (t, s) = start_eval_seq(
                                prog,
                                world,
                                &lam_bodies,
                                &mut frames,
                                SeqStart {
                                    fuel_next,
                                    env,
                                    pc,
                                    args,
                                    kind: SeqKind::Ctor(type_name, ctor_name),
                                },
                            );
                            cur_target = t;
                            cur_step = s;
                        }
                        Expr::TableLit { schema, rows } => {
                            let tv_rows = rows
                                .iter()
                                .map(|rl| TableRow {
                                    cells: rl.cells.iter().map(eval_literal).collect(),
                                    group_meta: None,
                                })
                                .collect();
                            cur_step = Some(EvalStep::Ok(Val::Table(TableVal {
                                cols: schema.cols.clone(),
                                rows: tv_rows,
                            })));
                        }
                        Expr::Prim { op, args } => {
                            let (t, s) = start_eval_seq(
                                prog,
                                world,
                                &lam_bodies,
                                &mut frames,
                                SeqStart {
                                    fuel_next,
                                    env,
                                    pc,
                                    args,
                                    kind: SeqKind::Prim(op),
                                },
                            );
                            cur_target = t;
                            cur_step = s;
                        }
                        Expr::Rel(plan) => {
                            cur_target = Some(EvalTarget::Plan {
                                fuel: fuel_next,
                                env,
                                pc,
                                plan,
                            });
                        }
                        Expr::Host { op, args } => {
                            let (t, s) = start_eval_seq(
                                prog,
                                world,
                                &lam_bodies,
                                &mut frames,
                                SeqStart {
                                    fuel_next,
                                    env,
                                    pc,
                                    args,
                                    kind: SeqKind::Host(op),
                                },
                            );
                            cur_target = t;
                            cur_step = s;
                        }
                        Expr::Stop { kind, detail } => match detail {
                            None => {
                                cur_step = Some(EvalStep::Stopped(Bug {
                                    kind: *kind,
                                    message: repr_bug_kind(*kind).to_string(),
                                }));
                            }
                            Some(d_expr) => {
                                let Ok(d_lty) = check_expr_arc(
                                    prog,
                                    env.as_arc_ty_env(),
                                    &pc,
                                    true,
                                    d_expr,
                                    false,
                                ) else {
                                    return EvalStep::Wrong;
                                };
                                let eff_tags = d_lty.effective_tags().union(&pc);
                                frames.push(EvalFrame::StopDetail {
                                    kind: *kind,
                                    eff_tags,
                                });
                                cur_target = Some(EvalTarget::Expr {
                                    fuel: fuel_next,
                                    env,
                                    pc,
                                    expr: d_expr,
                                });
                            }
                        },
                        Expr::Fail(msg_expr) => {
                            frames.push(EvalFrame::FailMsg);
                            cur_target = Some(EvalTarget::Expr {
                                fuel: fuel_next,
                                env,
                                pc,
                                expr: msg_expr,
                            });
                        }
                    }
                }
                EvalTarget::Plan {
                    fuel,
                    env,
                    pc,
                    plan,
                } => {
                    let Some(fuel_next) = fuel.checked_sub(1) else {
                        return EvalStep::OutOfFuel;
                    };
                    match plan {
                        Plan::SourceExpr(e) => {
                            frames.push(EvalFrame::PlanSourceExpr);
                            cur_target = Some(EvalTarget::Expr {
                                fuel: fuel_next,
                                env,
                                pc,
                                expr: e,
                            });
                        }
                        Plan::SourceDB {
                            cap,
                            table_name,
                            schema,
                        } => {
                            frames.push(EvalFrame::PlanSourceDB { table_name, schema });
                            cur_target = Some(EvalTarget::Expr {
                                fuel: fuel_next,
                                env,
                                pc,
                                expr: cap,
                            });
                        }
                        Plan::Join {
                            kind,
                            left,
                            right,
                            on,
                            suffixes,
                        } => {
                            frames.push(EvalFrame::PlanJoinLeft {
                                fuel_next,
                                env: env.clone(),
                                pc: pc.clone(),
                                kind: *kind,
                                right,
                                on,
                                suffixes,
                            });
                            cur_target = Some(EvalTarget::Plan {
                                fuel: fuel_next,
                                env,
                                pc,
                                plan: left,
                            });
                        }
                        Plan::Union { left, right } => {
                            frames.push(EvalFrame::PlanUnionLeft {
                                fuel_next,
                                env: env.clone(),
                                pc: pc.clone(),
                                right,
                            });
                            cur_target = Some(EvalTarget::Plan {
                                fuel: fuel_next,
                                env,
                                pc,
                                plan: left,
                            });
                        }
                        Plan::Pseudonymize { input, col, secret } => {
                            frames.push(EvalFrame::PlanPseudoInput {
                                fuel_next,
                                env: env.clone(),
                                pc: pc.clone(),
                                col,
                                secret,
                            });
                            cur_target = Some(EvalTarget::Plan {
                                fuel: fuel_next,
                                env,
                                pc,
                                plan: input,
                            });
                        }
                        Plan::Summarize { input, .. }
                        | Plan::Window { input, .. }
                        | Plan::FillGaps { input, .. }
                        | Plan::PivotWider { input, .. } => {
                            let Ok(PlanTy::Table(out_tt)) =
                                check_plan_arc(prog, env.as_arc_ty_env(), &pc, true, plan, false)
                            else {
                                return EvalStep::Wrong;
                            };
                            frames.push(EvalFrame::PlanCheckedUnary {
                                fuel_next,
                                env: env.clone(),
                                stage: plan,
                                out_tt,
                            });
                            cur_target = Some(EvalTarget::Plan {
                                fuel: fuel_next,
                                env,
                                pc,
                                plan: input,
                            });
                        }
                        Plan::Select { input, .. }
                        | Plan::Drop { input, .. }
                        | Plan::Rename { input, .. }
                        | Plan::Derive { input, .. }
                        | Plan::Filter { input, .. }
                        | Plan::Distinct { input, .. }
                        | Plan::Sort { input, .. }
                        | Plan::Limit { input, .. }
                        | Plan::GroupBy { input, .. }
                        | Plan::SuppressSmallGroups { input, .. }
                        | Plan::Crosstab { input, .. }
                        | Plan::Redact { input, .. } => {
                            frames.push(EvalFrame::PlanUnary {
                                fuel_next,
                                env: env.clone(),
                                pc: pc.clone(),
                                stage: plan,
                            });
                            cur_target = Some(EvalTarget::Plan {
                                fuel: fuel_next,
                                env,
                                pc,
                                plan: input,
                            });
                        }
                    }
                }
            }
            continue;
        }

        let Some(step) = cur_step.take() else {
            unreachable!("either cur_target or cur_step is populated");
        };
        match step {
            EvalStep::Stopped(_) | EvalStep::Failed(_) | EvalStep::Wrong | EvalStep::OutOfFuel => {
                return step;
            }
            EvalStep::Jumped(lbl, mut j_vals) => {
                let mut caught = false;
                while let Some(frame) = frames.pop() {
                    match frame {
                        EvalFrame::CallBoundary => return EvalStep::Wrong,
                        EvalFrame::JoinCatch {
                            fuel_next,
                            base_env,
                            label,
                            params,
                            join_pc,
                            rhs,
                        } if lbl == *label => {
                            if j_vals.len() != params.len() {
                                return EvalStep::Wrong;
                            }
                            let Some(loop_fuel_next) = fuel_next.checked_sub(1) else {
                                return EvalStep::OutOfFuel;
                            };
                            let entries: Vec<EnvEntry> = params
                                .iter()
                                .zip(std::mem::take(&mut j_vals))
                                .map(|((p_name, p_lty), j_val)| EnvEntry {
                                    name: p_name.clone(),
                                    lty: p_lty.clone(),
                                    val: j_val,
                                })
                                .collect();
                            let next_env = base_env.prepend_entries(entries);
                            frames.push(EvalFrame::JoinCatch {
                                fuel_next: loop_fuel_next,
                                base_env,
                                label,
                                params,
                                join_pc: join_pc.clone(),
                                rhs,
                            });
                            cur_target = Some(EvalTarget::Expr {
                                fuel: loop_fuel_next,
                                env: next_env,
                                pc: join_pc,
                                expr: rhs,
                            });
                            caught = true;
                            break;
                        }
                        _ => {}
                    }
                }
                if !caught {
                    return EvalStep::Jumped(lbl, j_vals);
                }
            }
            EvalStep::Ok(v) => {
                let Some(frame) = frames.pop() else {
                    return EvalStep::Ok(v);
                };
                match frame {
                    EvalFrame::CallBoundary | EvalFrame::JoinCatch { .. } => {
                        cur_step = Some(EvalStep::Ok(v));
                    }
                    EvalFrame::LetBound {
                        fuel_next,
                        name,
                        decl_lty,
                        env,
                        pc,
                        body,
                    } => {
                        let next_env = EnvList::cons(
                            EnvEntry {
                                name: name.clone(),
                                lty: decl_lty.add_tags(&pc),
                                val: v,
                            },
                            env,
                        );
                        cur_target = Some(EvalTarget::Expr {
                            fuel: fuel_next,
                            env: next_env,
                            pc,
                            expr: body,
                        });
                    }
                    EvalFrame::IfCond {
                        fuel_next,
                        env,
                        br_pc,
                        then_br,
                        else_br,
                    } => match v {
                        Val::Bool(true) => {
                            cur_target = Some(EvalTarget::Expr {
                                fuel: fuel_next,
                                env,
                                pc: br_pc,
                                expr: then_br,
                            });
                        }
                        Val::Bool(false) => {
                            cur_target = Some(EvalTarget::Expr {
                                fuel: fuel_next,
                                env,
                                pc: br_pc,
                                expr: else_br,
                            });
                        }
                        _ => return EvalStep::Wrong,
                    },
                    EvalFrame::CaseScrut {
                        fuel_next,
                        env,
                        scrut_lty,
                        arm_pc,
                        arms,
                    } => {
                        let Some((c_name, typed_vals)) =
                            match_case_val(prog, &v, &scrut_lty, &arm_pc)
                        else {
                            return EvalStep::Wrong;
                        };
                        let Some(arm) = arms.iter().find(|a| a.ctor == c_name) else {
                            return EvalStep::Wrong;
                        };
                        if arm.binders.len() != typed_vals.len() {
                            return EvalStep::Wrong;
                        }
                        let arm_entries: Vec<EnvEntry> = arm
                            .binders
                            .iter()
                            .zip(typed_vals)
                            .map(|(b_name, (b_lty, b_val))| EnvEntry {
                                name: b_name.clone(),
                                lty: b_lty,
                                val: b_val,
                            })
                            .collect();
                        let next_env = env.prepend_entries(arm_entries);
                        cur_target = Some(EvalTarget::Expr {
                            fuel: fuel_next,
                            env: next_env,
                            pc: arm_pc,
                            expr: &arm.body,
                        });
                    }
                    EvalFrame::AppFn {
                        fuel_next,
                        env,
                        pc,
                        args,
                    } => {
                        let mut fn_val = v;
                        let Val::Closure(cl) = &mut fn_val else {
                            return EvalStep::Wrong;
                        };
                        let kind = SeqKind::App {
                            params: std::mem::take(&mut cl.params),
                            fn_pc: std::mem::take(&mut cl.fn_pc),
                            body: Arc::clone(&cl.body),
                            captured_env: std::mem::take(&mut cl.captured_env),
                        };
                        let (t, s) = start_eval_seq(
                            prog,
                            world,
                            &lam_bodies,
                            &mut frames,
                            SeqStart {
                                fuel_next,
                                env,
                                pc,
                                args,
                                kind,
                            },
                        );
                        cur_target = t;
                        cur_step = s;
                    }
                    EvalFrame::Seq {
                        fuel_next,
                        env,
                        pc,
                        remaining,
                        mut vals,
                        kind,
                    } => {
                        vals.push(v);
                        if let Some((next_e, rest)) = remaining.split_first() {
                            frames.push(EvalFrame::Seq {
                                fuel_next,
                                env: env.clone(),
                                pc: pc.clone(),
                                remaining: rest,
                                vals,
                                kind,
                            });
                            cur_target = Some(EvalTarget::Expr {
                                fuel: fuel_next,
                                env,
                                pc,
                                expr: next_e,
                            });
                        } else {
                            let (t, s) = finish_eval_seq(
                                prog,
                                world,
                                &lam_bodies,
                                &mut frames,
                                fuel_next,
                                vals,
                                kind,
                            );
                            cur_target = t;
                            cur_step = s;
                        }
                    }
                    EvalFrame::Proj { idx } => match v {
                        Val::Tuple(ref vs) => match idx.to_usize().and_then(|i| vs.get(i)) {
                            Some(item) => cur_step = Some(EvalStep::Ok(item.clone())),
                            None => return EvalStep::Wrong,
                        },
                        _ => return EvalStep::Wrong,
                    },
                    EvalFrame::StopDetail { kind, eff_tags } => {
                        let msg = format!(
                            "{}: {}",
                            repr_bug_kind(kind),
                            format_diag_detail(&eff_tags, &v)
                        );
                        return EvalStep::Stopped(Bug { kind, message: msg });
                    }
                    EvalFrame::FailMsg => {
                        let mut v = v;
                        match &mut v {
                            Val::Text(s) => return EvalStep::Failed(std::mem::take(s)),
                            _ => return EvalStep::Wrong,
                        }
                    }
                    EvalFrame::PlanSourceExpr => {
                        if matches!(v, Val::Table(_)) {
                            cur_step = Some(EvalStep::Ok(v));
                        } else {
                            return EvalStep::Wrong;
                        }
                    }
                    EvalFrame::PlanSourceDB { table_name, schema } => match v {
                        Val::CapReadDB { handle: h, ref db } => {
                            let stored: Option<&StoredTable> = match h {
                                CapHandle::Real => world
                                    .real_db_tables
                                    .iter()
                                    .find(|st| st.db == *db && st.table_name == *table_name),
                                CapHandle::Fake(id) => world.fake_dbs.get(id).and_then(|fdb| {
                                    fdb.tables.iter().find(|st| st.table_name == *table_name)
                                }),
                            };
                            cur_step = Some(match stored {
                                Some(st) => {
                                    let st_tys: Vec<&ScalarTy> =
                                        st.schema.cols.iter().map(|c| &c.ty).collect();
                                    let decl_tys: Vec<&ScalarTy> =
                                        schema.cols.iter().map(|c| &c.ty).collect();
                                    if st_tys == decl_tys {
                                        let rows = st
                                            .rows
                                            .iter()
                                            .map(|cs| TableRow {
                                                cells: cs.clone(),
                                                group_meta: None,
                                            })
                                            .collect();
                                        EvalStep::Ok(Val::Table(TableVal {
                                            cols: schema.cols.clone(),
                                            rows,
                                        }))
                                    } else {
                                        EvalStep::Stopped(Bug {
                                            kind: BugKind::SchemaConstraint,
                                            message: format!(
                                                "schema drift on table '{table_name}'"
                                            ),
                                        })
                                    }
                                }
                                None => EvalStep::Ok(Val::Table(TableVal {
                                    cols: schema.cols.clone(),
                                    rows: Vec::new(),
                                })),
                            });
                        }
                        _ => return EvalStep::Wrong,
                    },
                    EvalFrame::PlanJoinLeft {
                        fuel_next,
                        env,
                        pc,
                        kind,
                        right,
                        on,
                        suffixes,
                    } => {
                        let Some(l_tv) = v.into_table() else {
                            return EvalStep::Wrong;
                        };
                        frames.push(EvalFrame::PlanJoinRight {
                            pc: pc.clone(),
                            kind,
                            l_tv,
                            on,
                            suffixes,
                        });
                        cur_target = Some(EvalTarget::Plan {
                            fuel: fuel_next,
                            env,
                            pc,
                            plan: right,
                        });
                    }
                    EvalFrame::PlanJoinRight {
                        pc,
                        kind,
                        l_tv,
                        on,
                        suffixes,
                    } => {
                        let Some(r_tv) = v.into_table() else {
                            return EvalStep::Wrong;
                        };
                        cur_step = Some(eval_plan_join_finish(&pc, kind, l_tv, r_tv, on, suffixes));
                    }
                    EvalFrame::PlanUnionLeft {
                        fuel_next,
                        env,
                        pc,
                        right,
                    } => {
                        let Some(l_tv) = v.into_table() else {
                            return EvalStep::Wrong;
                        };
                        frames.push(EvalFrame::PlanUnionRight { l_tv });
                        cur_target = Some(EvalTarget::Plan {
                            fuel: fuel_next,
                            env,
                            pc,
                            plan: right,
                        });
                    }
                    EvalFrame::PlanUnionRight { l_tv } => {
                        let Some(r_tv) = v.into_table() else {
                            return EvalStep::Wrong;
                        };
                        cur_step = Some(match merge_union_cols(&l_tv.cols, &r_tv.cols) {
                            Some(out_cols) => {
                                let out_rows = l_tv
                                    .rows
                                    .into_iter()
                                    .chain(r_tv.rows)
                                    .map(|r| TableRow {
                                        cells: r.cells,
                                        group_meta: None,
                                    })
                                    .collect();
                                EvalStep::Ok(Val::Table(TableVal {
                                    cols: out_cols,
                                    rows: out_rows,
                                }))
                            }
                            None => EvalStep::Wrong,
                        });
                    }
                    EvalFrame::PlanPseudoInput {
                        fuel_next,
                        env,
                        pc,
                        col,
                        secret,
                    } => {
                        let Some(tv) = v.into_table() else {
                            return EvalStep::Wrong;
                        };
                        frames.push(EvalFrame::PlanPseudoSecret {
                            pc: pc.clone(),
                            col,
                            tv,
                        });
                        cur_target = Some(EvalTarget::Expr {
                            fuel: fuel_next,
                            env,
                            pc,
                            expr: secret,
                        });
                    }
                    EvalFrame::PlanPseudoSecret { pc, col, tv } => {
                        cur_step = Some(eval_plan_pseudo_finish(&pc, col, tv, &v, world));
                    }
                    EvalFrame::PlanUnary {
                        fuel_next,
                        env,
                        pc,
                        stage,
                    } => {
                        cur_step = Some(eval_plan_unary_step(fuel_next, prog, &env, &pc, stage, v));
                    }
                    EvalFrame::PlanCheckedUnary {
                        fuel_next,
                        env,
                        stage,
                        out_tt,
                    } => {
                        cur_step = Some(eval_plan_checked_unary_step(
                            fuel_next, prog, &env, stage, out_tt, v,
                        ));
                    }
                }
            }
        }
    }
}

fn eval_plan_join_finish(
    pc: &TagSet,
    kind: JoinKind,
    l_tv: TableVal,
    r_tv: TableVal,
    on: &JoinOn,
    suffixes: &Option<(String, String)>,
) -> EvalStep {
    let l_tt = TableTy {
        cols: l_tv.cols.clone(),
        ..TableTy::default()
    };
    let r_tt = TableTy {
        cols: r_tv.cols.clone(),
        ..TableTy::default()
    };
    let (Ok(key_pairs), Ok(joined_cols)) = (
        resolve_join_pairs(&l_tt, &r_tt, on),
        build_joined_cols(kind, &l_tv.cols, &r_tv.cols, on, suffixes),
    ) else {
        return EvalStep::Wrong;
    };
    let l_key_names: Vec<Ident> = key_pairs.iter().map(|(lc, _)| lc.name.clone()).collect();
    let r_key_names: Vec<Ident> = key_pairs.iter().map(|(_, rc)| rc.name.clone()).collect();
    let key_tags =
        TagSet::union_owned(key_pairs.iter().map(|(lc, rc)| lc.tags.union(&rc.tags))).union(pc);
    let left_dup_bug = match kind {
        JoinKind::InnerOne | JoinKind::LeftOne => {
            check_unique_join_keys(&l_tv.cols, &l_key_names, &key_tags, &l_tv.rows)
        }
        _ => None,
    };
    let right_dup_bug = match kind {
        JoinKind::InnerOne
        | JoinKind::LeftOne
        | JoinKind::InnerManyToOne
        | JoinKind::LeftManyToOne => {
            check_unique_join_keys(&r_tv.cols, &r_key_names, &key_tags, &r_tv.rows)
        }
        JoinKind::InnerMany | JoinKind::Semi | JoinKind::Anti => None,
    };
    if let Some(bug) = left_dup_bug.or(right_dup_bug) {
        return EvalStep::Stopped(bug);
    }
    let same_key_names: &[Ident] = match on {
        JoinOn::SameKeys(ks) => ks,
        JoinOn::Pairs(_) => &[],
    };
    let r_keep_idxs: Vec<(&ColSpec, usize)> = r_tv
        .cols
        .iter()
        .enumerate()
        .filter(|(_, rc)| !same_key_names.contains(&rc.name))
        .map(|(i, rc)| (rc, i))
        .collect();
    let is_left_outer = matches!(kind, JoinKind::LeftOne | JoinKind::LeftManyToOne);
    let join_ctx = JoinExecCtx {
        kind,
        l_cols: &l_tv.cols,
        r_cols: &r_tv.cols,
        l_key_names: &l_key_names,
        r_key_names: &r_key_names,
        r_keep_idxs: &r_keep_idxs,
        is_left_outer,
    };
    match join_table_rows(&join_ctx, &r_tv.rows, &l_tv.rows) {
        Some(out_rows) => EvalStep::Ok(Val::Table(TableVal {
            cols: joined_cols,
            rows: out_rows,
        })),
        None => EvalStep::Wrong,
    }
}

fn eval_plan_pseudo_finish(
    pc: &TagSet,
    col: &Ident,
    tv: TableVal,
    sec_val: &Val,
    world: &World,
) -> EvalStep {
    let Val::CapSecret {
        handle: h,
        name: s_name,
    } = sec_val
    else {
        return EvalStep::Wrong;
    };
    let Some((c_idx, _)) = lookup_col_idx(&tv.cols, col) else {
        return EvalStep::Wrong;
    };
    let key_mat: String = match *h {
        CapHandle::Real => world
            .real_secrets
            .iter()
            .find(|(n, _)| n == s_name)
            .map_or_else(|| s_name.clone(), |(_, sv)| sv.clone()),
        CapHandle::Fake(id) => world
            .fake_secrets
            .get(id)
            .cloned()
            .unwrap_or_else(|| s_name.clone()),
    };
    let out_cols = tv
        .cols
        .into_iter()
        .map(|c| {
            if c.name == *col {
                ColSpec {
                    ty: ScalarTy::Text,
                    tags: c.tags.remove("pii").union(pc),
                    bucketed: false,
                    agg_kind: AggKind::Raw,
                    ..c
                }
            } else {
                ColSpec {
                    agg_kind: AggKind::Raw,
                    ..c
                }
            }
        })
        .collect();
    let mut out_rows = Vec::with_capacity(tv.rows.len());
    for mut r in tv.rows {
        let Some(orig_val) = r.cells.get(c_idx) else {
            return EvalStep::Wrong;
        };
        let tok = Val::Text(pseudonymize_token(&key_mat, orig_val));
        if let Some(slot) = r.cells.get_mut(c_idx) {
            *slot = tok;
        }
        out_rows.push(TableRow {
            cells: r.cells,
            group_meta: None,
        });
    }
    EvalStep::Ok(Val::Table(TableVal {
        cols: out_cols,
        rows: out_rows,
    }))
}

fn eval_plan_unary_step(
    fuel_next: usize,
    prog: &Program,
    env: &EnvList,
    pc: &TagSet,
    stage: &Plan,
    in_val: Val,
) -> EvalStep {
    let Some(tv) = in_val.into_table() else {
        return EvalStep::Wrong;
    };
    match stage {
        Plan::Select { cols, .. } => {
            let idx_specs: Vec<(usize, &ColSpec)> = cols
                .iter()
                .filter_map(|cn| lookup_col_idx(&tv.cols, cn))
                .collect();
            if idx_specs.len() != cols.len() {
                return EvalStep::Wrong;
            }
            let out_cols = idx_specs
                .iter()
                .map(|(_, c)| ColSpec {
                    agg_kind: AggKind::Raw,
                    ..(*c).clone()
                })
                .collect();
            let idxs: Vec<usize> = idx_specs.iter().map(|(i, _)| *i).collect();
            match project_rows_by_indices(&idxs, &tv.rows) {
                Some(out_rows) => EvalStep::Ok(Val::Table(TableVal {
                    cols: out_cols,
                    rows: out_rows,
                })),
                None => EvalStep::Wrong,
            }
        }
        Plan::Drop { cols, .. } => {
            let keep: Vec<(usize, &ColSpec)> = tv
                .cols
                .iter()
                .enumerate()
                .filter(|(_, c)| !cols.contains(&c.name))
                .collect();
            let out_cols = keep
                .iter()
                .map(|(_, c)| ColSpec {
                    agg_kind: AggKind::Raw,
                    ..(*c).clone()
                })
                .collect();
            let idxs: Vec<usize> = keep.iter().map(|(i, _)| *i).collect();
            match project_rows_by_indices(&idxs, &tv.rows) {
                Some(out_rows) => EvalStep::Ok(Val::Table(TableVal {
                    cols: out_cols,
                    rows: out_rows,
                })),
                None => EvalStep::Wrong,
            }
        }
        Plan::Rename { pairs, .. } => {
            let out_cols = tv
                .cols
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
                .collect();
            let out_rows = tv
                .rows
                .into_iter()
                .map(|r| TableRow {
                    cells: r.cells,
                    group_meta: None,
                })
                .collect();
            EvalStep::Ok(Val::Table(TableVal {
                cols: out_cols,
                rows: out_rows,
            }))
        }
        Plan::Derive { items, .. } => {
            let init_tv = TableVal {
                cols: tv
                    .cols
                    .into_iter()
                    .map(|c| ColSpec {
                        agg_kind: AggKind::Raw,
                        ..c
                    })
                    .collect(),
                rows: tv
                    .rows
                    .into_iter()
                    .map(|r| TableRow {
                        cells: r.cells,
                        group_meta: None,
                    })
                    .collect(),
            };
            eval_derive_items(fuel_next, prog, env, init_tv, items)
        }
        Plan::Filter { pred, .. } => {
            let out_cols = tv
                .cols
                .iter()
                .map(|c| ColSpec {
                    agg_kind: AggKind::Raw,
                    ..c.clone()
                })
                .collect();
            let mut kept = Vec::new();
            for r in &tv.rows {
                match eval_row_expr_inner(fuel_next, prog, env, &tv.cols, r, pred) {
                    PrimResult::Ok(Val::Bool(true)) => kept.push(TableRow {
                        cells: r.cells.clone(),
                        group_meta: None,
                    }),
                    PrimResult::Ok(Val::Bool(false)) => {}
                    PrimResult::Ok(_) => return EvalStep::Wrong,
                    PrimResult::Stopped(b) => return EvalStep::Stopped(b),
                    PrimResult::OutOfFuel => return EvalStep::OutOfFuel,
                    PrimResult::Wrong => return EvalStep::Wrong,
                }
            }
            EvalStep::Ok(Val::Table(TableVal {
                cols: out_cols,
                rows: kept,
            }))
        }
        Plan::Distinct { cols, .. } => {
            let key_names: Vec<Ident> = if cols.is_empty() {
                tv.cols.iter().map(|c| c.name.clone()).collect()
            } else {
                cols.clone()
            };
            let out_cols = tv
                .cols
                .iter()
                .map(|c| ColSpec {
                    agg_kind: AggKind::Raw,
                    ..c.clone()
                })
                .collect();
            match dedup_table_rows(&tv.cols, &key_names, &tv.rows) {
                Some(out_rows) => EvalStep::Ok(Val::Table(TableVal {
                    cols: out_cols,
                    rows: out_rows,
                })),
                None => EvalStep::Wrong,
            }
        }
        Plan::Sort { keys, .. } => {
            let out_cols = tv
                .cols
                .iter()
                .map(|c| ColSpec {
                    agg_kind: AggKind::Raw,
                    ..c.clone()
                })
                .collect();
            let clean_rows: Vec<TableRow> = tv
                .rows
                .into_iter()
                .map(|r| TableRow {
                    cells: r.cells,
                    group_meta: None,
                })
                .collect();
            let sorted =
                insertion_sort_by(&clean_rows, |a, b| row_lt_by_keys(&tv.cols, keys, a, b));
            EvalStep::Ok(Val::Table(TableVal {
                cols: out_cols,
                rows: sorted,
            }))
        }
        Plan::Limit { n, .. } => {
            let out_cols = tv
                .cols
                .into_iter()
                .map(|c| ColSpec {
                    agg_kind: AggKind::Raw,
                    ..c
                })
                .collect();
            let limit = n.to_usize_saturating();
            let taken = tv
                .rows
                .into_iter()
                .take(limit)
                .map(|r| TableRow {
                    cells: r.cells,
                    group_meta: None,
                })
                .collect();
            EvalStep::Ok(Val::Table(TableVal {
                cols: out_cols,
                rows: taken,
            }))
        }
        Plan::GroupBy { keys, .. } => {
            let out_cols = tv
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
            let out_rows = tv
                .rows
                .into_iter()
                .map(|r| TableRow {
                    cells: r.cells,
                    group_meta: None,
                })
                .collect();
            EvalStep::Ok(Val::Table(TableVal {
                cols: out_cols,
                rows: out_rows,
            }))
        }
        Plan::SuppressSmallGroups {
            min_k,
            distinct_by,
            mode,
            ..
        } => {
            let out_cols = tv
                .cols
                .iter()
                .map(|c| {
                    let orig_kind = c.agg_kind;
                    let base = match orig_kind {
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
                    };
                    match (mode, orig_kind) {
                        (
                            SuppressMode::MaskComplementary,
                            AggKind::Blending | AggKind::NonBlending,
                        ) => ColSpec {
                            ty: crate::core::check::ensure_option_scalar(&base.ty),
                            bucketed: false,
                            ..base
                        },
                        _ => base,
                    }
                })
                .collect();
            match mode {
                SuppressMode::Drop => {
                    let kept = tv
                        .rows
                        .into_iter()
                        .filter(|r| BigInt::from(suppress_group_size(distinct_by, r)) >= *min_k)
                        .map(|r| TableRow {
                            cells: r.cells,
                            group_meta: None,
                        })
                        .collect();
                    EvalStep::Ok(Val::Table(TableVal {
                        cols: out_cols,
                        rows: kept,
                    }))
                }
                SuppressMode::MaskComplementary => {
                    let small_rows: Vec<&TableRow> = tv
                        .rows
                        .iter()
                        .filter(|r| BigInt::from(suppress_group_size(distinct_by, r)) < *min_k)
                        .collect();
                    let small_sum: BigInt = small_rows
                        .iter()
                        .map(|r| BigInt::from(suppress_group_size(distinct_by, r)))
                        .fold(BigInt::zero(), |acc, x| acc + x);
                    let valid_rows: Vec<TableRow> = tv
                        .rows
                        .iter()
                        .filter(|r| BigInt::from(suppress_group_size(distinct_by, r)) >= *min_k)
                        .cloned()
                        .collect();
                    let comp_key: Option<Vec<Val>> = if !small_rows.is_empty() && small_sum < *min_k
                    {
                        let sorted_valid = insertion_sort_by(&valid_rows, |a, b| {
                            suppress_row_lt(&tv.cols, distinct_by, a, b)
                        });
                        sorted_valid
                            .first()
                            .map(|r| extract_group_key_cells(&tv.cols, &r.cells))
                    } else {
                        None
                    };
                    let out_rows = tv
                        .rows
                        .iter()
                        .map(|r| {
                            let should_mask = BigInt::from(suppress_group_size(distinct_by, r))
                                < *min_k
                                || comp_key.as_ref().is_some_and(|ck| {
                                    val_list_eq(&extract_group_key_cells(&tv.cols, &r.cells), ck)
                                });
                            let cells = if should_mask {
                                mask_agg_cells(&tv.cols, &r.cells)
                            } else {
                                wrap_agg_cells(&tv.cols, &r.cells)
                            };
                            TableRow {
                                cells,
                                group_meta: None,
                            }
                        })
                        .collect();
                    EvalStep::Ok(Val::Table(TableVal {
                        cols: out_cols,
                        rows: out_rows,
                    }))
                }
            }
        }
        Plan::Crosstab {
            rows_col,
            cols_col,
            values_col,
            fill,
            ..
        } => {
            let (Some((r_idx, _)), Some((c_idx, _)), Some((v_idx, _))) = (
                lookup_col_idx(&tv.cols, rows_col),
                lookup_col_idx(&tv.cols, cols_col),
                lookup_col_idx(&tv.cols, values_col),
            ) else {
                return EvalStep::Wrong;
            };
            let fill_val = eval_literal(fill);
            let raw_r: Vec<Val> = tv
                .rows
                .iter()
                .filter_map(|r| r.cells.get(r_idx).cloned())
                .collect();
            let raw_c: Vec<Val> = tv
                .rows
                .iter()
                .filter_map(|r| r.cells.get(c_idx).cloned())
                .collect();
            let r_keys = dedup_adjacent_by(&insertion_sort_by(&raw_r, val_lt), val_eq);
            let c_keys = dedup_adjacent_by(&insertion_sort_by(&raw_c, val_lt), val_eq);
            let mut headers = Vec::with_capacity(c_keys.len() + 1);
            headers.push(rows_col.clone());
            headers.extend(c_keys.iter().map(render_public_val));
            let matrix = r_keys
                .iter()
                .map(|rk| {
                    let mut row = Vec::with_capacity(c_keys.len() + 1);
                    row.push(rk.clone());
                    for ck in &c_keys {
                        let found = tv.rows.iter().find(|r| {
                            matches!(
                                (r.cells.get(r_idx), r.cells.get(c_idx)),
                                (Some(rv), Some(cv)) if val_eq(rv, rk) && val_eq(cv, ck)
                            )
                        });
                        let cell = found
                            .and_then(|mr| mr.cells.get(v_idx).cloned())
                            .unwrap_or_else(|| fill_val.clone());
                        row.push(cell);
                    }
                    row
                })
                .collect();
            EvalStep::Ok(Val::DynTable {
                headers,
                rows: matrix,
            })
        }
        Plan::Redact {
            col, replacement, ..
        } => {
            let Some((c_idx, _)) = lookup_col_idx(&tv.cols, col) else {
                return EvalStep::Wrong;
            };
            let out_cols = tv
                .cols
                .into_iter()
                .map(|c| {
                    if c.name == *col {
                        ColSpec {
                            ty: ScalarTy::Text,
                            tags: pc.clone(),
                            bucketed: false,
                            agg_kind: AggKind::Raw,
                            ..c
                        }
                    } else {
                        ColSpec {
                            agg_kind: AggKind::Raw,
                            ..c
                        }
                    }
                })
                .collect();
            let out_rows = tv
                .rows
                .into_iter()
                .map(|mut r| {
                    if let Some(slot) = r.cells.get_mut(c_idx) {
                        *slot = Val::Text(replacement.clone());
                    }
                    TableRow {
                        cells: r.cells,
                        group_meta: None,
                    }
                })
                .collect();
            EvalStep::Ok(Val::Table(TableVal {
                cols: out_cols,
                rows: out_rows,
            }))
        }
        _ => EvalStep::Wrong,
    }
}

fn eval_plan_checked_unary_step(
    fuel_next: usize,
    prog: &Program,
    env: &EnvList,
    stage: &Plan,
    out_tt: TableTy,
    in_val: Val,
) -> EvalStep {
    let Some(tv) = in_val.into_table() else {
        return EvalStep::Wrong;
    };
    match stage {
        Plan::Summarize {
            aggs, distinct_key, ..
        } => {
            let group_keys: Vec<Ident> = tv
                .cols
                .iter()
                .filter(|c| c.agg_kind == AggKind::GroupKey)
                .map(|c| c.name.clone())
                .collect();
            let key_cols_len = tv
                .cols
                .iter()
                .filter(|c| group_keys.contains(&c.name))
                .count();
            let agg_start = key_cols_len.min(out_tt.cols.len());
            if out_tt.cols.len() - agg_start != aggs.len() {
                return EvalStep::Wrong;
            }
            let Some(raw_keys) = extract_all_rows_key_vals(&tv.cols, &group_keys, &tv.rows) else {
                return EvalStep::Wrong;
            };
            let sorted_keys = if group_keys.is_empty() && tv.rows.is_empty() {
                vec![Vec::new()]
            } else {
                let sorted = insertion_sort_by(&raw_keys, |a, b| val_list_lt(a, b));
                dedup_adjacent_by(&sorted, |a, b| val_list_eq(a, b))
            };
            let dk_idx = distinct_key
                .as_deref()
                .and_then(|dk| lookup_col_idx(&tv.cols, dk).map(|(i, _)| i));
            eval_summarize_groups(
                fuel_next,
                prog,
                env,
                &tv,
                &group_keys,
                distinct_key,
                dk_idx,
                aggs,
                agg_start,
                out_tt.cols,
                &sorted_keys,
            )
        }
        Plan::Window { items, .. } => {
            let init_tv = TableVal {
                cols: tv
                    .cols
                    .into_iter()
                    .map(|c| ColSpec {
                        agg_kind: AggKind::Raw,
                        ..c
                    })
                    .collect(),
                rows: tv
                    .rows
                    .into_iter()
                    .map(|r| TableRow {
                        cells: r.cells,
                        group_meta: None,
                    })
                    .collect(),
            };
            match eval_window_items(init_tv, items) {
                Some(win_tv) => EvalStep::Ok(Val::Table(TableVal {
                    cols: out_tt.cols,
                    rows: win_tv.rows,
                })),
                None => EvalStep::Wrong,
            }
        }
        Plan::FillGaps { col, over, .. } => {
            let mut sort_spec: Vec<(Ident, SortDir)> =
                over.iter().map(|k| (k.clone(), SortDir::Asc)).collect();
            sort_spec.push((col.clone(), SortDir::Asc));
            let clean_rows: Vec<TableRow> = tv
                .rows
                .into_iter()
                .map(|r| TableRow {
                    cells: r.cells,
                    group_meta: None,
                })
                .collect();
            let sorted = insertion_sort_by(&clean_rows, |a, b| {
                row_lt_by_keys(&tv.cols, &sort_spec, a, b)
            });
            EvalStep::Ok(Val::Table(TableVal {
                cols: out_tt.cols,
                rows: sorted,
            }))
        }
        Plan::PivotWider {
            names_from,
            values_from,
            static_cols,
            fill,
            ..
        } => {
            let (Some((n_idx, _)), Some((v_idx, _))) = (
                lookup_col_idx(&tv.cols, names_from),
                lookup_col_idx(&tv.cols, values_from),
            ) else {
                return EvalStep::Wrong;
            };
            let id_names: Vec<Ident> = tv
                .cols
                .iter()
                .filter(|c| c.name != *names_from && c.name != *values_from)
                .map(|c| c.name.clone())
                .collect();
            let fill_val = eval_literal(fill);
            let Some(raw_ids) = extract_all_rows_key_vals(&tv.cols, &id_names, &tv.rows) else {
                return EvalStep::Wrong;
            };
            let unique_ids = dedup_adjacent_by(
                &insertion_sort_by(&raw_ids, |a, b| val_list_lt(a, b)),
                |a, b| val_list_eq(a, b),
            );
            let out_rows = unique_ids
                .into_iter()
                .map(|id_key| {
                    let p_rows: Vec<&TableRow> = tv
                        .rows
                        .iter()
                        .filter(|r| {
                            extract_key_vals(&tv.cols, &id_names, r)
                                .is_some_and(|kv| val_list_eq(&kv, &id_key))
                        })
                        .collect();
                    let mut cells = id_key;
                    for sc in static_cols {
                        let found = p_rows
                            .iter()
                            .find(|r| matches!(r.cells.get(n_idx), Some(Val::Text(s)) if s == sc));
                        let cell = found
                            .and_then(|mr| mr.cells.get(v_idx).cloned())
                            .unwrap_or_else(|| fill_val.clone());
                        cells.push(cell);
                    }
                    TableRow {
                        cells,
                        group_meta: None,
                    }
                })
                .collect();
            EvalStep::Ok(Val::Table(TableVal {
                cols: out_tt.cols,
                rows: out_rows,
            }))
        }
        _ => EvalStep::Wrong,
    }
}

#[expect(
    clippy::too_many_arguments,
    reason = "Matches formal/DanaCore/Eval.lean:evalSummarizeGroups parameter list 1-to-1"
)]
fn eval_summarize_groups(
    fuel: usize,
    prog: &Program,
    env: &EnvList,
    tv: &TableVal,
    group_keys: &[Ident],
    distinct_key: &Option<Ident>,
    dk_idx: Option<usize>,
    aggs: &[AggItem],
    agg_start: usize,
    out_cols: Vec<ColSpec>,
    sorted_keys: &[Vec<Val>],
) -> EvalStep {
    let agg_cols = &out_cols[agg_start..];
    let mut out_rows = Vec::with_capacity(sorted_keys.len());
    for g_key in sorted_keys {
        let g_rows: Vec<&TableRow> = if group_keys.is_empty() {
            tv.rows.iter().collect()
        } else {
            tv.rows
                .iter()
                .filter(|r| {
                    extract_key_vals(&tv.cols, group_keys, r)
                        .is_some_and(|kv| val_list_eq(&kv, g_key))
                })
                .collect()
        };
        let dist_count = match (distinct_key, dk_idx) {
            (Some(_), Some(d_idx)) => {
                let d_vals: Vec<Val> = g_rows
                    .iter()
                    .filter_map(|r| match r.cells.get(d_idx) {
                        None | Some(Val::OptNone) => None,
                        Some(Val::OptSome(inner)) => Some(inner.as_ref().clone()),
                        Some(v) => Some(v.clone()),
                    })
                    .collect();
                let sorted = insertion_sort_by(&d_vals, val_lt);
                Some(dedup_adjacent_by(&sorted, val_eq).len())
            }
            _ => None,
        };
        let mut agg_cells = Vec::with_capacity(aggs.len());
        for (a_item, a_spec) in aggs.iter().zip(agg_cols) {
            let arg_vals: Vec<Val> = match &a_item.arg {
                None => vec![Val::Unit; g_rows.len()],
                Some(re) => {
                    let mut vals = Vec::with_capacity(g_rows.len());
                    for gr in &g_rows {
                        match eval_row_expr_inner(fuel, prog, env, &tv.cols, gr, re) {
                            PrimResult::Ok(cv) => vals.push(cv),
                            PrimResult::Stopped(b) => return EvalStep::Stopped(b),
                            PrimResult::OutOfFuel => return EvalStep::OutOfFuel,
                            PrimResult::Wrong => return EvalStep::Wrong,
                        }
                    }
                    vals
                }
            };
            match eval_agg_clean(a_item.op, &a_spec.ty, &arg_vals) {
                PrimResult::Ok(agg_cell) => agg_cells.push(agg_cell),
                PrimResult::Stopped(b) => return EvalStep::Stopped(b),
                PrimResult::OutOfFuel => return EvalStep::OutOfFuel,
                PrimResult::Wrong => return EvalStep::Wrong,
            }
        }
        let mut cells = g_key.clone();
        cells.extend(agg_cells);
        out_rows.push(TableRow {
            cells,
            group_meta: Some(GroupMeta {
                row_count: g_rows.len(),
                distinct_count: dist_count,
            }),
        });
    }
    EvalStep::Ok(Val::Table(TableVal {
        cols: out_cols,
        rows: out_rows,
    }))
}

// ---------------------------------------------------------------------------
// Top-Level Entry Runner (`run_program`)
// ---------------------------------------------------------------------------

fn build_entry_cap_val(ty: &Ty) -> Option<Val> {
    match ty {
        Ty::Args => Some(Val::CapArgs),
        Ty::Clock => Some(Val::CapClock),
        Ty::Console(allows) => Some(Val::CapConsole {
            handle: CapHandle::Real,
            allows: allows.clone(),
        }),
        Ty::ReadFiles => Some(Val::CapReadFiles(CapHandle::Real)),
        Ty::WriteFiles { root, allows } => Some(Val::CapWriteFiles {
            handle: CapHandle::Real,
            root: root.clone(),
            allows: allows.clone(),
        }),
        Ty::ReadDB(db) => Some(Val::CapReadDB {
            handle: CapHandle::Real,
            db: db.clone(),
        }),
        Ty::WriteTable { db, table_name, .. } => Some(Val::CapWriteTable {
            handle: CapHandle::Real,
            db: db.clone(),
            table_name: table_name.clone(),
        }),
        Ty::RawReadDB(db) => Some(Val::CapRawReadDB(db.clone())),
        Ty::HttpsAllow { host, allows } => Some(Val::CapHttpsAllow {
            handle: CapHandle::Real,
            host: host.clone(),
            allows: allows.clone(),
        }),
        Ty::Secret(name) => Some(Val::CapSecret {
            handle: CapHandle::Real,
            name: name.clone(),
        }),
        Ty::Declassify(allows) => Some(Val::CapDeclassify(allows.clone())),
        _ => None,
    }
}

fn entry_cap_required_export_tags(ty: &Ty) -> TagSet {
    match ty {
        Ty::Console(allows) | Ty::WriteFiles { allows, .. } | Ty::HttpsAllow { allows, .. } => {
            allows.clone()
        }
        _ => TagSet::empty(),
    }
}

fn check_entry_export_gate(params: &[(Ident, LTy)], w: &World) -> Option<Bug> {
    let req = TagSet::union_owned(
        params
            .iter()
            .map(|(_, l)| entry_cap_required_export_tags(&l.ty)),
    );
    if req.is_empty() || req.is_subset(&w.runtime_allow_export) {
        None
    } else {
        Some(Bug {
            kind: BugKind::ExportGateDenied,
            message: "runtime --allow-export authorization required for sensitive external sink"
                .to_string(),
        })
    }
}

/// Typecheck and evaluate `prog.entry` (or return ok unit report if `entry = None`).
pub fn run_program(
    fuel: usize,
    prog: &Program,
    init_world: World,
) -> Result<ExecReport, RuntimeError> {
    with_large_stack(|| run_program_inner(fuel, prog, init_world))
}

fn run_program_inner(
    fuel: usize,
    prog: &Program,
    mut init_world: World,
) -> Result<ExecReport, RuntimeError> {
    check_program(prog).map_err(|e| RuntimeError::new(e.message))?;
    let Some(main_name) = &prog.entry else {
        return extract_report(Outcome::Ok(Val::Unit, init_world))
            .ok_or_else(|| RuntimeError::new("internal error extracting empty report"));
    };
    let Some(main_fn) = prog.find_fun(main_name) else {
        return Err(RuntimeError::new(format!("entry '{main_name}' not found")));
    };
    let mut init_env = EnvList::default();
    for (p_name, p_lty) in &main_fn.params {
        let Some(cap_val) = build_entry_cap_val(&p_lty.ty) else {
            return Err(RuntimeError::new("entry has non-capability parameters"));
        };
        init_env = EnvList::cons(
            EnvEntry {
                name: p_name.clone(),
                lty: p_lty.clone(),
                val: cap_val,
            },
            init_env,
        );
    }
    if let Some(bug) = check_entry_export_gate(&main_fn.params, &init_world) {
        return extract_report(Outcome::Stopped(bug, init_world))
            .ok_or_else(|| RuntimeError::new("unable to extract report"));
    }
    let step = eval_inner(
        fuel,
        prog,
        &init_env,
        &TagSet::empty(),
        &mut init_world,
        &main_fn.body,
    );
    let out = step.into_outcome(init_world);
    match out {
        Outcome::OutOfFuel => Err(RuntimeError::new("execution exhausted fuel")),
        Outcome::Wrong => Err(RuntimeError::new(
            "internal soundness violation: stuck state",
        )),
        Outcome::Jumped(lbl, _, _) => Err(RuntimeError::new(format!(
            "internal soundness violation: uncaught jump '{lbl}'"
        ))),
        other => extract_report(other).ok_or_else(|| RuntimeError::new("unable to extract report")),
    }
}
