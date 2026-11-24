//! Deterministic seeded synthetic data generator (`dana fake`).
//!
//! Uses a zero-crate `SplitMix64` -> `Xoshiro256StarStar` PRNG to generate constraint-satisfying
//! synthetic rows for any Dana [`CompiledSchema`], honoring column types, `T?` nullability,
//! `where` clauses (inclusive/exclusive bounds on `Int`/`Decimal`/`Float`, exact sub-cent
//! `Decimal` ranges, `==` / `!=`, `and`, `not .empty?`, `.contains?(...)`), and safe placeholders
//! for sensitivity-tagged columns.

use std::io::{self, Write};

use crate::core::bigint::{BigInt, DEC_MIN, DEC_SCALE};
use crate::core::syntax::{ColSpec, Float64, Literal, PrimOp, ScalarTy};
use crate::formats::csv::{push_csv_escaped, render_csv_cell};
use crate::formats::json::{push_dana_val_as_json, push_json_string};
use crate::formats::time::{MICROS_PER_DAY, days_from_civil};
use crate::oracle::eval::eval_literal;
use crate::oracle::value::{TableRow, TableVal, Val, val_eq};
use crate::runtime::ir::{CompiledSchema, ExecPrimOp, ExecRowExpr};

/// Output serialization format for `dana fake`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FakeFormat {
    Csv,
    Tsv,
    Jsonl,
}

/// Zero-crate deterministic `Xoshiro256**` PRNG seeded via `SplitMix64`.
#[derive(Clone, Debug)]
pub struct DeterministicRng {
    s: [u64; 4],
}

impl DeterministicRng {
    #[must_use]
    pub fn seed_from_u64(mut seed: u64) -> Self {
        let mut next_sm = || {
            seed = seed.wrapping_add(0x9e37_79b9_7f4a_7c15);
            let mut z = seed;
            z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
            z ^ (z >> 31)
        };
        Self {
            s: [next_sm(), next_sm(), next_sm(), next_sm()],
        }
    }

    #[must_use]
    pub fn next_u64(&mut self) -> u64 {
        let result = self.s[1].wrapping_mul(5).rotate_left(7).wrapping_mul(9);
        let t = self.s[1] << 17;
        self.s[2] ^= self.s[0];
        self.s[3] ^= self.s[1];
        self.s[1] ^= self.s[2];
        self.s[0] ^= self.s[3];
        self.s[2] ^= t;
        self.s[3] = self.s[3].rotate_left(45);
        result
    }

    #[must_use]
    pub fn range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        if hi <= lo {
            return lo;
        }
        let span = (i128::from(hi) - i128::from(lo) + 1) as u128;
        let offset = (u128::from(self.next_u64()) % span) as i128;
        (i128::from(lo) + offset) as i64
    }

    #[must_use]
    pub fn range_i128(&mut self, lo: i128, hi: i128) -> i128 {
        if hi <= lo {
            return lo;
        }
        let span_u = hi.abs_diff(lo).saturating_add(1);
        let r = (u128::from(self.next_u64()) << 64) | u128::from(self.next_u64());
        let off = if span_u == 0 { r } else { r % span_u };
        lo.wrapping_add_unsigned(off)
    }

    #[must_use]
    pub fn unit_f64(&mut self) -> f64 {
        // 53 bits of uniform mantissa in [0.0, 1.0).
        ((self.next_u64() >> 11) as f64) * (1.0 / ((1u64 << 53) as f64))
    }
}

#[derive(Clone, Debug, Default)]
struct ColumnHints {
    min_int: Option<i64>,
    max_int: Option<i64>,
    /// Exact 10^-18-scaled decimal bounds (preserves sub-cent constraints such as `< 0.005`).
    min_dec: Option<i128>,
    max_dec: Option<i128>,
    /// Float bounds with strict-inequality flags `(bound, is_strict)`.
    min_float: Option<(f64, bool)>,
    max_float: Option<(f64, bool)>,
    eq_val: Option<Val>,
    not_equal: Vec<Val>,
    must_contain: Option<String>,
    non_empty: bool,
}

fn extract_hints(re: Option<&ExecRowExpr>) -> ColumnHints {
    let mut hints = ColumnHints::default();
    let Some(expr) = re else {
        return hints;
    };
    let mut stack = vec![expr];
    while let Some(cur) = stack.pop() {
        if let ExecRowExpr::Prim { op, args } = cur {
            match (op, args.as_slice()) {
                (ExecPrimOp::Core(PrimOp::AndBool), [a, b]) => {
                    stack.push(a);
                    stack.push(b);
                }
                (
                    ExecPrimOp::Core(PrimOp::NotBool),
                    [
                        ExecRowExpr::Prim {
                            op: ExecPrimOp::Core(PrimOp::EmptyText),
                            ..
                        },
                    ],
                ) => {
                    hints.non_empty = true;
                }
                (
                    ExecPrimOp::Core(PrimOp::ContainsText),
                    [_, ExecRowExpr::Lit(Literal::Text(sub))],
                ) => {
                    hints.must_contain = Some(sub.clone());
                }
                (ExecPrimOp::Core(PrimOp::Eq), [ExecRowExpr::Col(_), ExecRowExpr::Lit(lit)])
                | (ExecPrimOp::Core(PrimOp::Eq), [ExecRowExpr::Lit(lit), ExecRowExpr::Col(_)]) => {
                    hints.eq_val = Some(eval_literal(lit));
                }
                (ExecPrimOp::Core(PrimOp::Ne), [ExecRowExpr::Col(_), ExecRowExpr::Lit(lit)])
                | (ExecPrimOp::Core(PrimOp::Ne), [ExecRowExpr::Lit(lit), ExecRowExpr::Col(_)]) => {
                    hints.not_equal.push(eval_literal(lit));
                }
                (ExecPrimOp::Core(PrimOp::Gt), [ExecRowExpr::Col(_), ExecRowExpr::Lit(lit)])
                | (ExecPrimOp::Core(PrimOp::Lt), [ExecRowExpr::Lit(lit), ExecRowExpr::Col(_)]) => {
                    apply_lower_hint(&mut hints, lit, true);
                }
                (ExecPrimOp::Core(PrimOp::Ge), [ExecRowExpr::Col(_), ExecRowExpr::Lit(lit)])
                | (ExecPrimOp::Core(PrimOp::Le), [ExecRowExpr::Lit(lit), ExecRowExpr::Col(_)]) => {
                    apply_lower_hint(&mut hints, lit, false);
                }
                (ExecPrimOp::Core(PrimOp::Lt), [ExecRowExpr::Col(_), ExecRowExpr::Lit(lit)])
                | (ExecPrimOp::Core(PrimOp::Gt), [ExecRowExpr::Lit(lit), ExecRowExpr::Col(_)]) => {
                    apply_upper_hint(&mut hints, lit, true);
                }
                (ExecPrimOp::Core(PrimOp::Le), [ExecRowExpr::Col(_), ExecRowExpr::Lit(lit)])
                | (ExecPrimOp::Core(PrimOp::Ge), [ExecRowExpr::Lit(lit), ExecRowExpr::Col(_)]) => {
                    apply_upper_hint(&mut hints, lit, false);
                }
                _ => {}
            }
        }
    }
    hints
}

fn literal_to_dec_i128(lit: &Literal) -> Option<i128> {
    match lit {
        Literal::Int(n) => n
            .to_i64()
            .and_then(|v| i128::from(v).checked_mul(DEC_SCALE)),
        Literal::Decimal(d) => d.to_i128(),
        Literal::Float(f) => {
            let fv = f.to_f64();
            if fv.is_finite() {
                Some((fv * (DEC_SCALE as f64)).round() as i128)
            } else {
                None
            }
        }
        _ => None,
    }
}

fn literal_to_f64(lit: &Literal) -> Option<f64> {
    match lit {
        Literal::Int(n) => n.to_i64().map(|v| v as f64),
        Literal::Decimal(d) => d.to_i128().map(|v| (v as f64) / (DEC_SCALE as f64)),
        Literal::Float(f) => {
            let fv = f.to_f64();
            if fv.is_finite() { Some(fv) } else { None }
        }
        _ => None,
    }
}

fn apply_lower_hint(hints: &mut ColumnHints, lit: &Literal, strict: bool) {
    if let Literal::Int(n) = lit
        && let Some(v) = n.to_i64()
    {
        let bound = if strict { v.saturating_add(1) } else { v };
        hints.min_int = Some(hints.min_int.map_or(bound, |p| p.max(bound)));
    }
    if let Some(d) = literal_to_dec_i128(lit) {
        let bound = if strict {
            d.saturating_add(1)
        } else {
            d.max(DEC_MIN)
        };
        hints.min_dec = Some(hints.min_dec.map_or(bound, |p| p.max(bound)));
    }
    if let Some(f) = literal_to_f64(lit) {
        let replace = match hints.min_float {
            None => true,
            Some((prev, prev_s)) => f > prev || (f == prev && strict && !prev_s),
        };
        if replace {
            hints.min_float = Some((f, strict));
        }
    }
}

fn apply_upper_hint(hints: &mut ColumnHints, lit: &Literal, strict: bool) {
    if let Literal::Int(n) = lit
        && let Some(v) = n.to_i64()
    {
        let bound = if strict { v.saturating_sub(1) } else { v };
        hints.max_int = Some(hints.max_int.map_or(bound, |p| p.min(bound)));
    }
    if let Some(d) = literal_to_dec_i128(lit) {
        let bound = if strict {
            d.saturating_sub(1).max(DEC_MIN)
        } else {
            d.max(DEC_MIN)
        };
        hints.max_dec = Some(hints.max_dec.map_or(bound, |p| p.min(bound)));
    }
    if let Some(f) = literal_to_f64(lit) {
        let replace = match hints.max_float {
            None => true,
            Some((prev, prev_s)) => f < prev || (f == prev && strict && !prev_s),
        };
        if replace {
            hints.max_float = Some((f, strict));
        }
    }
}

fn value_violates_not_equal(v: &Val, hints: &ColumnHints) -> bool {
    hints.not_equal.iter().any(|bad| val_eq(v, bad))
}

fn gen_scalar_val(
    rng: &mut DeterministicRng,
    col: &ColSpec,
    ty: &ScalarTy,
    hints: &ColumnHints,
    row_idx: usize,
) -> Val {
    if let ScalarTy::Option(inner) = ty {
        return if rng.next_u64().is_multiple_of(10) {
            Val::OptNone
        } else {
            Val::OptSome(Box::new(gen_scalar_val(rng, col, inner, hints, row_idx)))
        };
    }

    if let Some(eq) = &hints.eq_val {
        return eq.clone();
    }

    // Generate with bounded retry loop to avoid `!=` forbidden values.
    let mut candidate = gen_non_opt_once(rng, col, ty, hints, row_idx);
    for attempt in 1..64usize {
        if !value_violates_not_equal(&candidate, hints) {
            break;
        }
        candidate = gen_non_opt_once(rng, col, ty, hints, row_idx.wrapping_add(attempt));
    }
    candidate
}

fn gen_non_opt_once(
    rng: &mut DeterministicRng,
    col: &ColSpec,
    ty: &ScalarTy,
    hints: &ColumnHints,
    row_idx: usize,
) -> Val {
    match ty {
        ScalarTy::Option(inner) => gen_non_opt_once(rng, col, inner, hints, row_idx),
        ScalarTy::Bool => Val::Bool(rng.next_u64() & 1 == 1),
        ScalarTy::Int => {
            let (lo, hi) = match (hints.min_int, hints.max_int) {
                (Some(l), Some(h)) => (l, h),
                (Some(l), None) => (l, l.saturating_add(9_999)),
                (None, Some(h)) => (h.saturating_sub(9_999), h),
                (None, None) => (1, 10_000),
            };
            Val::Int(BigInt::from(rng.range_i64(lo, hi)))
        }
        ScalarTy::Decimal => {
            let default_span = 500i128 * DEC_SCALE;
            let (lo, hi) = match (hints.min_dec, hints.max_dec) {
                (Some(l), Some(h)) => (l, h),
                (Some(l), None) => (l, l.saturating_add(default_span)),
                (None, Some(h)) => {
                    let span = if h > 0 {
                        h.min(default_span)
                    } else {
                        default_span
                    };
                    (h.saturating_sub(span).max(DEC_MIN), h)
                }
                (None, None) => (DEC_SCALE, 500i128 * DEC_SCALE),
            };
            // Prefer clean cent-aligned values when the interval is wide enough to contain multiple cents;
            // otherwise sample exact 10^-18 sub-cent units within `[lo, hi]`.
            let cent = DEC_SCALE / 100;
            let lo_cents = lo.div_euclid(cent) + i128::from(lo.rem_euclid(cent) != 0);
            let hi_cents = hi.div_euclid(cent);
            let scaled = if hi_cents >= lo_cents {
                let c = rng.range_i128(lo_cents, hi_cents);
                c * cent
            } else {
                rng.range_i128(lo, hi)
            };
            Val::Decimal(BigInt::from(scaled))
        }
        ScalarTy::Float => {
            let (mut lo, lo_strict, mut hi, hi_strict) = match (hints.min_float, hints.max_float) {
                (Some((l, ls)), Some((h, hs))) => (l, ls, h, hs),
                (Some((l, ls)), None) => (l, ls, l + 100.0, false),
                (None, Some((h, hs))) => {
                    let span = if h > 0.0 { h.min(100.0) } else { 100.0 };
                    (h - span, false, h, hs)
                }
                (None, None) => (0.0, false, 100.0, false),
            };
            if lo > hi {
                std::mem::swap(&mut lo, &mut hi);
            }
            let t = if lo_strict || hi_strict {
                0.05 + rng.unit_f64() * 0.90
            } else {
                rng.unit_f64()
            };
            let mut v = lo + t * (hi - lo);
            if lo_strict && v <= lo {
                v = lo + (hi - lo) * 0.5;
            }
            if hi_strict && v >= hi {
                v = lo + (hi - lo) * 0.5;
            }
            // Round to 4 decimal places only if rounding still respects the bounds.
            let rounded = (v * 10_000.0).round() / 10_000.0;
            let fits_lo = if lo_strict {
                rounded > lo
            } else {
                rounded >= lo
            };
            let fits_hi = if hi_strict {
                rounded < hi
            } else {
                rounded <= hi
            };
            let final_f = if fits_lo && fits_hi { rounded } else { v };
            Val::Float(Float64::from_f64(final_f))
        }
        ScalarTy::Date => {
            let base = days_from_civil(2025, 1, 1);
            let offset = rng.range_i64(0, 729);
            Val::Date(BigInt::from(base + offset))
        }
        ScalarTy::Timestamp => {
            let base_days = days_from_civil(2025, 1, 1);
            let day_off = rng.range_i64(0, 729);
            let sec_off = rng.range_i64(0, 86_399);
            let us = (base_days + day_off) * MICROS_PER_DAY + sec_off * 1_000_000;
            Val::Timestamp(BigInt::from(us))
        }
        ScalarTy::Duration => {
            let secs = rng.range_i64(1, 3_600);
            Val::Duration(BigInt::from(secs * 1_000_000))
        }
        ScalarTy::Text => gen_text_val(rng, col, hints, row_idx),
        ScalarTy::Bytes => Val::Bytes(format!("bytes_{row_idx}").into_bytes()),
        ScalarTy::Unit | ScalarTy::Data(_) => Val::Unit,
    }
}

fn gen_text_val(
    rng: &mut DeterministicRng,
    col: &ColSpec,
    hints: &ColumnHints,
    row_idx: usize,
) -> Val {
    let lower = col.name.to_ascii_lowercase();
    if hints.must_contain.as_deref() == Some("@") || lower.contains("email") {
        let id = rng.range_i64(1, 999_999);
        return Val::Text(format!("synthetic_{row_idx}_{id}@example.invalid"));
    }
    if let Some(sub) = &hints.must_contain {
        return Val::Text(format!("{}_{sub}_{row_idx}", col.name));
    }
    if !col.tags.is_empty() {
        return Val::Text(format!("synthetic_{}_{}", col.name, row_idx + 1));
    }
    const CATEGORIES: &[&str] = &["food", "rent", "travel", "supplies", "utilities", "books"];
    const DEPTS: &[&str] = &["theology", "history", "counseling", "library", "admissions"];
    const STATUSES: &[&str] = &["active", "pending", "complete", "archived"];
    let pick = (rng.next_u64() as usize) % CATEGORIES.len();
    if lower.contains("cat") {
        Val::Text(CATEGORIES[pick].to_string())
    } else if lower.contains("dept") || lower.contains("program") {
        Val::Text(DEPTS[pick % DEPTS.len()].to_string())
    } else if lower.contains("status") || lower.contains("state") {
        Val::Text(STATUSES[pick % STATUSES.len()].to_string())
    } else {
        Val::Text(format!("{}_{}", col.name, (rng.next_u64() % 20) + 1))
    }
}

/// Generate a synthetic [`TableVal`] of `rows` rows deterministically for `schema`.
#[must_use]
pub fn generate_fake_table(schema: &CompiledSchema, rows: usize, seed: u64) -> TableVal {
    let mut rng = DeterministicRng::seed_from_u64(seed);
    let hints: Vec<ColumnHints> = schema
        .decl
        .schema
        .cols
        .iter()
        .enumerate()
        .map(|(i, _)| extract_hints(schema.constraints.get(i).and_then(Option::as_ref)))
        .collect();
    let mut out_rows = Vec::with_capacity(rows);
    for r in 0..rows {
        let mut cells = Vec::with_capacity(schema.decl.schema.cols.len());
        for (ci, col) in schema.decl.schema.cols.iter().enumerate() {
            cells.push(gen_scalar_val(&mut rng, col, &col.ty, &hints[ci], r));
        }
        out_rows.push(TableRow {
            cells,
            group_meta: None,
        });
    }
    TableVal {
        cols: schema.decl.schema.cols.clone(),
        rows: out_rows,
    }
}

/// Stream `rows` deterministic synthetic rows directly to `writer` without materializing all rows in RAM.
///
/// # Errors
/// Returns any underlying I/O error.
pub fn write_fake_rows<W: Write>(
    writer: &mut W,
    schema: &CompiledSchema,
    rows: usize,
    seed: u64,
    format: FakeFormat,
) -> io::Result<()> {
    let mut rng = DeterministicRng::seed_from_u64(seed);
    let cols = &schema.decl.schema.cols;
    let hints: Vec<ColumnHints> = cols
        .iter()
        .enumerate()
        .map(|(i, _)| extract_hints(schema.constraints.get(i).and_then(Option::as_ref)))
        .collect();

    let mut line = String::new();
    match format {
        FakeFormat::Csv | FakeFormat::Tsv => {
            let delim = if format == FakeFormat::Tsv {
                b'\t'
            } else {
                b','
            };
            for (i, c) in cols.iter().enumerate() {
                if i > 0 {
                    line.push(delim as char);
                }
                push_csv_escaped(&mut line, &c.name, delim);
            }
            line.push('\n');
            writer.write_all(line.as_bytes())?;

            for r in 0..rows {
                line.clear();
                for (ci, col) in cols.iter().enumerate() {
                    if ci > 0 {
                        line.push(delim as char);
                    }
                    let val = gen_scalar_val(&mut rng, col, &col.ty, &hints[ci], r);
                    let rendered = render_csv_cell(&val);
                    push_csv_escaped(&mut line, &rendered, delim);
                }
                line.push('\n');
                writer.write_all(line.as_bytes())?;
            }
        }
        FakeFormat::Jsonl => {
            for r in 0..rows {
                line.clear();
                line.push('{');
                for (ci, col) in cols.iter().enumerate() {
                    if ci > 0 {
                        line.push(',');
                    }
                    let val = gen_scalar_val(&mut rng, col, &col.ty, &hints[ci], r);
                    push_json_string(&mut line, &col.name);
                    line.push(':');
                    push_dana_val_as_json(&mut line, &val);
                }
                line.push_str("}\n");
                writer.write_all(line.as_bytes())?;
            }
        }
    }
    Ok(())
}
