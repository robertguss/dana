//! Unboxed cell representation and pre-compiled `FastColConstraint` evaluator for
//! zero-allocation schema `where` validation during streaming CSV and columnar Parquet ingestion.
//!
//! Covers common unboxed predicates (`not .empty?`, `.empty?`, `. > k`, `. >= k`, `. < k`,
//! `. <= k`, `. == k`, `. != k`, `.contains("...")`, and arbitrary boolean `and`/`or`/`not`
//! combinations across `Bool`, `Int`, `Decimal(i128)`, `Float`, `Text`, `Date`, `Timestamp`,
//! and `Duration`) with transparent fallback to the general `ExecRowExpr` evaluator for custom
//! predicates.

use std::cmp::Ordering;

use crate::core::bigint::BigInt;
use crate::core::syntax::{Float64, Literal, PrimOp, ScalarTy};
use crate::oracle::value::{Val, float_order_key};
use crate::runtime::ir::{ExecPrimOp, ExecRowExpr};
use crate::vm::batch::{Column, ColumnData};

/// Zero-allocation unboxed cell used by streaming columnar CSV ingestion.
#[derive(Clone, Copy, Debug)]
pub enum UnboxedCell<'a> {
    Null,
    Unit,
    Bool(bool),
    Int(i64),
    Decimal(i128),
    /// Canonical IEEE-754 binary64 bit pattern (`Float64::bits`).
    Float(u64),
    Text(&'a str),
    Bytes(&'a [u8]),
    Date(i64),
    Timestamp(i64),
    Duration(i64),
}

impl UnboxedCell<'_> {
    /// Materialize this unboxed cell into a boxed [`Val`] (used ONLY on fallback custom constraints).
    #[must_use]
    pub fn to_val(self) -> Val {
        match self {
            Self::Null => Val::OptNone,
            Self::Unit => Val::Unit,
            Self::Bool(b) => Val::Bool(b),
            Self::Int(n) => Val::Int(BigInt::from(n)),
            Self::Decimal(d) => Val::Decimal(BigInt::from(d)),
            Self::Float(bits) => Val::Float(Float64::from_bits(bits)),
            Self::Text(s) => Val::Text(s.to_string()),
            Self::Bytes(bs) => Val::Bytes(bs.to_vec()),
            Self::Date(d) => Val::Date(BigInt::from(d)),
            Self::Timestamp(t) => Val::Timestamp(BigInt::from(t)),
            Self::Duration(d) => Val::Duration(BigInt::from(d)),
        }
    }
}

/// Comparison operator for unboxed column constraints.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CmpOp {
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

impl CmpOp {
    #[inline]
    #[must_use]
    const fn flip(self) -> Self {
        match self {
            Self::Eq => Self::Eq,
            Self::Ne => Self::Ne,
            Self::Lt => Self::Gt,
            Self::Le => Self::Ge,
            Self::Gt => Self::Lt,
            Self::Ge => Self::Le,
        }
    }

    #[inline]
    #[must_use]
    const fn eval_ord(self, ord: Ordering) -> bool {
        match self {
            Self::Eq => matches!(ord, Ordering::Equal),
            Self::Ne => !matches!(ord, Ordering::Equal),
            Self::Lt => matches!(ord, Ordering::Less),
            Self::Le => matches!(ord, Ordering::Less | Ordering::Equal),
            Self::Gt => matches!(ord, Ordering::Greater),
            Self::Ge => matches!(ord, Ordering::Greater | Ordering::Equal),
        }
    }
}

/// Pre-compiled per-column schema `where` constraint.
#[derive(Clone, Debug)]
pub enum FastColConstraint {
    /// No `where` constraint on this column (always passes).
    AlwaysTrue,
    /// Constant boolean literal.
    Const(bool),
    /// `not .empty?` on `Text`.
    TextNotEmpty,
    /// `.empty?` on `Text`.
    TextEmpty,
    /// `.contains(needle)` on `Text`.
    TextContains(String),
    /// Text comparison against a constant string.
    TextCmp(CmpOp, String),
    /// Bool equality / ordering against a constant bool.
    BoolCmp(CmpOp, bool),
    /// Self is directly a `Bool` (`where .`).
    BoolSelf,
    /// `Int` comparison against `i64`.
    IntCmp(CmpOp, i64),
    /// Combined inclusive/exclusive range on `Int`: `lo <= . && . <= hi` (common `tier >= 1 and tier <= 3`).
    IntRangeInclusive(i64, i64),
    /// `Decimal` comparison against `i128` (`10^-18`-scaled).
    DecCmp(CmpOp, i128),
    /// Combined inclusive range on `Decimal`.
    DecRangeInclusive(i128, i128),
    /// `Float` comparison using canonical IEEE-754 `float_order_key` (100% identical to `val_eq`/`val_lt`!).
    FloatCmp(CmpOp, u64),
    /// Combined inclusive range on `Float` (precomputed `float_order_key` bounds).
    FloatRangeInclusive(u64, u64),
    /// `Date` comparison against `i64` days.
    DateCmp(CmpOp, i64),
    /// `Timestamp` comparison against `i64` micros.
    TimestampCmp(CmpOp, i64),
    /// `Duration` comparison against `i64` micros.
    DurationCmp(CmpOp, i64),
    /// Logical negation.
    Not(Box<FastColConstraint>),
    /// Logical conjunction.
    And(Box<FastColConstraint>, Box<FastColConstraint>),
    /// Logical disjunction.
    Or(Box<FastColConstraint>, Box<FastColConstraint>),
    /// Arbitrary expression requiring the general `eval_schema_constraint` fallback.
    Fallback,
}

impl FastColConstraint {
    /// Compile an optional `ExecRowExpr` (with self column `"__self"`) into a [`FastColConstraint`].
    #[must_use]
    pub fn compile<F>(expr: Option<&ExecRowExpr>, col_ty: &ScalarTy, lookup_const: &F) -> Self
    where
        F: Fn(&str) -> Option<Literal>,
    {
        let Some(re) = expr else {
            return Self::AlwaysTrue;
        };
        let inner_ty = match col_ty {
            ScalarTy::Option(inner) => inner.as_ref(),
            other => other,
        };
        if inner_ty.is_option() {
            return Self::Fallback;
        }
        Self::compile_expr(re, inner_ty, lookup_const)
    }

    fn compile_expr<F>(re: &ExecRowExpr, inner_ty: &ScalarTy, lookup_const: &F) -> Self
    where
        F: Fn(&str) -> Option<Literal>,
    {
        match re {
            ExecRowExpr::Lit(Literal::Bool(b)) => Self::Const(*b),
            ExecRowExpr::Col(name) if name == "__self" && *inner_ty == ScalarTy::Bool => {
                Self::BoolSelf
            }
            ExecRowExpr::Prim { op, args } => match (op, args.as_slice()) {
                (ExecPrimOp::Core(PrimOp::NotBool), [inner]) => {
                    let sub = Self::compile_expr(inner, inner_ty, lookup_const);
                    match sub {
                        Self::Fallback => Self::Fallback,
                        Self::Const(b) => Self::Const(!b),
                        Self::TextEmpty => Self::TextNotEmpty,
                        Self::TextNotEmpty => Self::TextEmpty,
                        other => Self::Not(Box::new(other)),
                    }
                }
                (ExecPrimOp::Core(PrimOp::AndBool), [lhs, rhs]) => {
                    let a = Self::compile_expr(lhs, inner_ty, lookup_const);
                    let b = Self::compile_expr(rhs, inner_ty, lookup_const);
                    match (a, b) {
                        (Self::Fallback, _) | (_, Self::Fallback) => Self::Fallback,
                        (Self::IntCmp(CmpOp::Ge, lo), Self::IntCmp(CmpOp::Le, hi))
                        | (Self::IntCmp(CmpOp::Le, hi), Self::IntCmp(CmpOp::Ge, lo)) => {
                            Self::IntRangeInclusive(lo, hi)
                        }
                        (Self::DecCmp(CmpOp::Ge, lo), Self::DecCmp(CmpOp::Le, hi))
                        | (Self::DecCmp(CmpOp::Le, hi), Self::DecCmp(CmpOp::Ge, lo)) => {
                            Self::DecRangeInclusive(lo, hi)
                        }
                        (Self::FloatCmp(CmpOp::Ge, lo), Self::FloatCmp(CmpOp::Le, hi))
                        | (Self::FloatCmp(CmpOp::Le, hi), Self::FloatCmp(CmpOp::Ge, lo)) => {
                            Self::FloatRangeInclusive(lo, hi)
                        }
                        (x, y) => Self::And(Box::new(x), Box::new(y)),
                    }
                }
                (ExecPrimOp::Core(PrimOp::OrBool), [lhs, rhs]) => {
                    let a = Self::compile_expr(lhs, inner_ty, lookup_const);
                    let b = Self::compile_expr(rhs, inner_ty, lookup_const);
                    if matches!(a, Self::Fallback) || matches!(b, Self::Fallback) {
                        Self::Fallback
                    } else {
                        Self::Or(Box::new(a), Box::new(b))
                    }
                }
                (ExecPrimOp::Core(PrimOp::EmptyText), [arg])
                    if is_self_col(arg) && *inner_ty == ScalarTy::Text =>
                {
                    Self::TextEmpty
                }
                (ExecPrimOp::Core(PrimOp::ContainsText), [hay, needle])
                    if is_self_col(hay) && *inner_ty == ScalarTy::Text =>
                {
                    if let Some(Literal::Text(s)) = eval_const_lit(needle, lookup_const) {
                        Self::TextContains(s)
                    } else {
                        Self::Fallback
                    }
                }
                (ExecPrimOp::Core(cop), [lhs, rhs]) => {
                    let cmp = match cop {
                        PrimOp::Eq => CmpOp::Eq,
                        PrimOp::Ne => CmpOp::Ne,
                        PrimOp::Lt => CmpOp::Lt,
                        PrimOp::Le => CmpOp::Le,
                        PrimOp::Gt => CmpOp::Gt,
                        PrimOp::Ge => CmpOp::Ge,
                        _ => return Self::Fallback,
                    };
                    if is_self_col(lhs) {
                        if let Some(lit) = eval_const_lit(rhs, lookup_const) {
                            return compile_cmp_lit(cmp, &lit, inner_ty);
                        }
                    } else if is_self_col(rhs)
                        && let Some(lit) = eval_const_lit(lhs, lookup_const)
                    {
                        return compile_cmp_lit(cmp.flip(), &lit, inner_ty);
                    }
                    Self::Fallback
                }
                _ => Self::Fallback,
            },
            _ => Self::Fallback,
        }
    }

    /// Returns `true` if no constraint needs to be checked for this column.
    #[inline]
    #[must_use]
    pub const fn is_always_true(&self) -> bool {
        matches!(self, Self::AlwaysTrue)
    }

    /// Evaluate this compiled constraint against a non-null [`UnboxedCell`].
    /// Returns `Some(passed)` on the fast path, or `None` when [`Self::Fallback`] is required.
    #[inline]
    #[must_use]
    pub fn eval_unboxed(&self, cell: UnboxedCell<'_>) -> Option<bool> {
        match self {
            Self::AlwaysTrue => Some(true),
            Self::Const(b) => Some(*b),
            Self::TextNotEmpty => match cell {
                UnboxedCell::Text(s) => Some(!s.is_empty()),
                _ => None,
            },
            Self::TextEmpty => match cell {
                UnboxedCell::Text(s) => Some(s.is_empty()),
                _ => None,
            },
            Self::TextContains(needle) => match cell {
                UnboxedCell::Text(s) => Some(s.contains(needle.as_str())),
                _ => None,
            },
            Self::TextCmp(op, rhs) => match cell {
                UnboxedCell::Text(s) => Some(op.eval_ord(s.cmp(rhs.as_str()))),
                _ => None,
            },
            Self::BoolSelf => match cell {
                UnboxedCell::Bool(b) => Some(b),
                _ => None,
            },
            Self::BoolCmp(op, rhs) => match cell {
                UnboxedCell::Bool(b) => Some(op.eval_ord(b.cmp(rhs))),
                _ => None,
            },
            Self::IntCmp(op, rhs) => match cell {
                UnboxedCell::Int(n) => Some(op.eval_ord(n.cmp(rhs))),
                _ => None,
            },
            Self::IntRangeInclusive(lo, hi) => match cell {
                UnboxedCell::Int(n) => Some(n >= *lo && n <= *hi),
                _ => None,
            },
            Self::DecCmp(op, rhs) => match cell {
                UnboxedCell::Decimal(d) => Some(op.eval_ord(d.cmp(rhs))),
                _ => None,
            },
            Self::DecRangeInclusive(lo, hi) => match cell {
                UnboxedCell::Decimal(d) => Some(d >= *lo && d <= *hi),
                _ => None,
            },
            Self::FloatCmp(op, rhs_key) => match cell {
                UnboxedCell::Float(bits) => {
                    let k = float_order_key(Float64::from_bits(bits));
                    Some(op.eval_ord(k.cmp(rhs_key)))
                }
                _ => None,
            },
            Self::FloatRangeInclusive(lo_key, hi_key) => match cell {
                UnboxedCell::Float(bits) => {
                    let k = float_order_key(Float64::from_bits(bits));
                    Some(k >= *lo_key && k <= *hi_key)
                }
                _ => None,
            },
            Self::DateCmp(op, rhs) => match cell {
                UnboxedCell::Date(d) => Some(op.eval_ord(d.cmp(rhs))),
                _ => None,
            },
            Self::TimestampCmp(op, rhs) => match cell {
                UnboxedCell::Timestamp(t) => Some(op.eval_ord(t.cmp(rhs))),
                _ => None,
            },
            Self::DurationCmp(op, rhs) => match cell {
                UnboxedCell::Duration(d) => Some(op.eval_ord(d.cmp(rhs))),
                _ => None,
            },
            Self::Not(inner) => inner.eval_unboxed(cell).map(|b| !b),
            Self::And(a, b) => match a.eval_unboxed(cell) {
                Some(false) => Some(false),
                Some(true) => b.eval_unboxed(cell),
                None => None,
            },
            Self::Or(a, b) => match a.eval_unboxed(cell) {
                Some(true) => Some(true),
                Some(false) => b.eval_unboxed(cell),
                None => None,
            },
            Self::Fallback => None,
        }
    }

    /// Vectorized scan over a [`Column`] up to row `limit`, returning the 0-based index of the
    /// FIRST row whose non-null value violates this constraint, or `None` if all pass.
    pub fn find_first_violation<F>(
        &self,
        col: &Column,
        limit: usize,
        mut fallback: F,
    ) -> Option<usize>
    where
        F: FnMut(&Val) -> bool,
    {
        if self.is_always_true() || limit == 0 {
            return None;
        }
        let n = limit.min(col.len());
        let validity = col.validity.as_ref();

        // Tight specialized loops for the most frequent numeric/text predicates with no nulls.
        if validity.is_none() {
            match (self, &col.data) {
                (Self::IntCmp(op, rhs), ColumnData::Int(vs)) => {
                    return vs[..n].iter().position(|v| !op.eval_ord(v.cmp(rhs)));
                }
                (Self::IntRangeInclusive(lo, hi), ColumnData::Int(vs)) => {
                    return vs[..n].iter().position(|&v| v < *lo || v > *hi);
                }
                (Self::DecCmp(op, rhs), ColumnData::Decimal(vs)) => {
                    return vs[..n].iter().position(|v| !op.eval_ord(v.cmp(rhs)));
                }
                (Self::DecRangeInclusive(lo, hi), ColumnData::Decimal(vs)) => {
                    return vs[..n].iter().position(|&v| v < *lo || v > *hi);
                }
                (Self::FloatCmp(op, rhs_key), ColumnData::Float(vs)) => {
                    return vs[..n].iter().position(|&bits| {
                        let k = float_order_key(Float64::from_bits(bits));
                        !op.eval_ord(k.cmp(rhs_key))
                    });
                }
                (Self::FloatRangeInclusive(lo_key, hi_key), ColumnData::Float(vs)) => {
                    return vs[..n].iter().position(|&bits| {
                        let k = float_order_key(Float64::from_bits(bits));
                        k < *lo_key || k > *hi_key
                    });
                }
                (Self::TextNotEmpty, ColumnData::Text { offsets, .. }) => {
                    return (0..n).find(|&i| offsets[i] == offsets[i + 1]);
                }
                _ => {}
            }
        }

        for r in 0..n {
            if let Some(bm) = validity
                && !bm.is_valid(r)
            {
                continue;
            }
            if !matches!(self, Self::Fallback)
                && let Some(cell) = column_data_unboxed_at(&col.data, r)
                && let Some(ok) = self.eval_unboxed(cell)
            {
                if !ok {
                    return Some(r);
                }
                continue;
            }
            let raw_val = col.data.get_raw_val(r);
            let inner = match &raw_val {
                Val::OptNone => continue,
                Val::OptSome(v) => v.as_ref(),
                other => other,
            };
            if !fallback(inner) {
                return Some(r);
            }
        }
        None
    }
}

#[inline]
fn column_data_unboxed_at(data: &ColumnData, row: usize) -> Option<UnboxedCell<'_>> {
    match data {
        ColumnData::Unit(_) => Some(UnboxedCell::Unit),
        ColumnData::Bool(v) => Some(UnboxedCell::Bool(v[row] != 0)),
        ColumnData::Int(v) => Some(UnboxedCell::Int(v[row])),
        ColumnData::Decimal(v) => Some(UnboxedCell::Decimal(v[row])),
        ColumnData::Float(v) => Some(UnboxedCell::Float(v[row])),
        ColumnData::Text { .. } => data.text_at(row).map(UnboxedCell::Text),
        ColumnData::Bytes { .. } => data.bytes_at(row).map(UnboxedCell::Bytes),
        ColumnData::Date(v) => Some(UnboxedCell::Date(v[row])),
        ColumnData::Timestamp(v) => Some(UnboxedCell::Timestamp(v[row])),
        ColumnData::Duration(v) => Some(UnboxedCell::Duration(v[row])),
        ColumnData::Generic(_) => None,
    }
}

fn is_self_col(e: &ExecRowExpr) -> bool {
    matches!(e, ExecRowExpr::Col(name) if name == "__self")
}

fn eval_const_lit<F>(e: &ExecRowExpr, lookup_const: &F) -> Option<Literal>
where
    F: Fn(&str) -> Option<Literal>,
{
    match e {
        ExecRowExpr::Lit(l) => Some(l.clone()),
        ExecRowExpr::ConstRef(name) => lookup_const(name),
        ExecRowExpr::Prim { op, args } => match (op, args.as_slice()) {
            (ExecPrimOp::Core(PrimOp::NegInt), [inner]) => {
                if let Some(Literal::Int(n)) = eval_const_lit(inner, lookup_const) {
                    let neg = -n;
                    if neg.in_int64_range() {
                        return Some(Literal::Int(neg));
                    }
                }
                None
            }
            (ExecPrimOp::Core(PrimOp::NegDec), [inner]) => {
                if let Some(Literal::Decimal(d)) = eval_const_lit(inner, lookup_const) {
                    let neg = -d;
                    if neg.in_decimal_range() {
                        return Some(Literal::Decimal(neg));
                    }
                }
                None
            }
            (ExecPrimOp::NegFloat, [inner]) => {
                if let Some(Literal::Float(f)) = eval_const_lit(inner, lookup_const) {
                    return Some(Literal::Float(Float64::from_f64(-f.to_f64())));
                }
                None
            }
            (ExecPrimOp::Core(PrimOp::IntToDec), [inner]) => {
                if let Some(Literal::Int(n)) = eval_const_lit(inner, lookup_const) {
                    let scaled = &n * &BigInt::from(crate::core::bigint::DEC_SCALE);
                    if scaled.in_decimal_range() {
                        return Some(Literal::Decimal(scaled));
                    }
                }
                None
            }
            (ExecPrimOp::IntToFloat, [inner]) => {
                if let Some(Literal::Int(n)) = eval_const_lit(inner, lookup_const)
                    && let Some(i) = n.to_i64()
                {
                    return Some(Literal::Float(Float64::from_f64(i as f64)));
                }
                None
            }
            _ => None,
        },
        _ => None,
    }
}

fn compile_cmp_lit(op: CmpOp, lit: &Literal, inner_ty: &ScalarTy) -> FastColConstraint {
    match (inner_ty, lit) {
        (ScalarTy::Int, Literal::Int(n)) => n.to_i64().map_or(FastColConstraint::Fallback, |v| {
            FastColConstraint::IntCmp(op, v)
        }),
        (ScalarTy::Decimal, Literal::Decimal(d)) => {
            d.to_i128().map_or(FastColConstraint::Fallback, |v| {
                FastColConstraint::DecCmp(op, v)
            })
        }
        (ScalarTy::Float, Literal::Float(f)) => {
            FastColConstraint::FloatCmp(op, float_order_key(*f))
        }
        (ScalarTy::Text, Literal::Text(s)) => FastColConstraint::TextCmp(op, s.clone()),
        (ScalarTy::Bool, Literal::Bool(b)) => FastColConstraint::BoolCmp(op, *b),
        (ScalarTy::Date, Literal::Date(d)) => d.to_i64().map_or(FastColConstraint::Fallback, |v| {
            FastColConstraint::DateCmp(op, v)
        }),
        (ScalarTy::Timestamp, Literal::Timestamp(t)) => {
            t.to_i64().map_or(FastColConstraint::Fallback, |v| {
                FastColConstraint::TimestampCmp(op, v)
            })
        }
        (ScalarTy::Duration, Literal::Duration(d)) => {
            d.to_i64().map_or(FastColConstraint::Fallback, |v| {
                FastColConstraint::DurationCmp(op, v)
            })
        }
        _ => FastColConstraint::Fallback,
    }
}
