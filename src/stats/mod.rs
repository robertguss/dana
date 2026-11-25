//! Zero-dependency statistical analytics engine and privacy-safe dataset profiler.
//!
//! Provides exact numerical routines for:
//! - Pearson `r` and tie-aware Spearman `rho` rank correlation
//! - Ordinary least squares (OLS) simple linear regression and prediction
//! - Two-sample Welch t-test with Welch-Satterthwaite degrees of freedom and
//!   regularized incomplete beta two-tailed p-values
//! - Pearson chi-square tests of independence (contingency table) and goodness-of-fit
//!   with regularized upper incomplete gamma p-values
//! - Z-score and interquartile range (IQR) outlier flagging with privacy tag propagation
//! - Privacy-redacted dataset profiling (`profile.rs`).

pub mod profile;

use std::collections::HashMap;

use crate::core::syntax::{AggKind, ColSpec, ScalarTy, TagSet};
use crate::oracle::value::{TableRow, TableVal, Val, unwrap_numeric_float};
use crate::vm::key::SingleKey;

/// Result of a simple OLS linear regression `y = slope * x + intercept`.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct LinearRegressionResult {
    pub slope: f64,
    pub intercept: f64,
    pub r_squared: f64,
}

impl LinearRegressionResult {
    /// Predict `y` at a given `x` using the fitted linear model.
    #[must_use]
    pub fn predict(&self, x: f64) -> f64 {
        self.slope * x + self.intercept
    }
}

/// Result of a two-sample Welch t-test.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct WelchTTestResult {
    pub t_stat: f64,
    pub df: f64,
    pub p_value: f64,
}

/// Result of a Pearson chi-square test (independence or goodness-of-fit).
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct ChiSquareResult {
    pub stat: f64,
    pub df: f64,
    pub p_value: f64,
}

/// Supported outlier detection methods for `Stats.outliers`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum OutlierMethod {
    /// Flag rows where `|x - mean| / sample_stddev >= threshold`.
    ZScore,
    /// Flag rows where `x < q1 - k * iqr || x > q3 + k * iqr`.
    Iqr,
}

// ---------------------------------------------------------------------------
// Core Numerical Utilities & Special Functions
// ---------------------------------------------------------------------------

/// Numerically stable arithmetic mean of a non-empty finite slice.
#[must_use]
pub fn mean_f64(xs: &[f64]) -> Option<f64> {
    if xs.is_empty() || xs.iter().any(|x| !x.is_finite()) {
        return None;
    }
    let n = xs.len() as f64;
    let total = xs.iter().copied().fold(0.0_f64, |acc, x| acc + x);
    let m = if total.is_infinite() {
        xs.iter().copied().fold(0.0_f64, |acc, x| acc + x / n)
    } else {
        total / n
    };
    m.is_finite().then_some(m)
}

/// Linearly interpolated quantile (`p` in `[0.0, 1.0]`, R-7 / NumPy convention) on an
/// already ascending-sorted finite slice.
#[must_use]
pub fn quantile_sorted(sorted: &[f64], p: f64) -> Option<f64> {
    if sorted.is_empty() || !p.is_finite() {
        return None;
    }
    let q = p.clamp(0.0, 1.0);
    let pos = q * ((sorted.len() - 1) as f64);
    let lo = pos.floor() as usize;
    let hi = pos.ceil() as usize;
    let frac = pos - (lo as f64);
    Some(sorted[lo] * (1.0 - frac) + sorted[hi] * frac)
}

/// Sample standard deviation (denominator `n - 1`) via scaled two-pass sum of squares.
#[must_use]
pub fn sample_stddev(xs: &[f64]) -> Option<f64> {
    if xs.len() < 2 {
        return None;
    }
    let mean = mean_f64(xs)?;
    let scale = xs.iter().fold(0.0_f64, |acc, &x| acc.max((x - mean).abs()));
    if !scale.is_finite() {
        return None;
    }
    if scale == 0.0 {
        return Some(0.0);
    }
    let sum_sq = xs.iter().fold(0.0_f64, |acc, &x| {
        let u = (x - mean) / scale;
        acc + u * u
    });
    let var = (sum_sq / ((xs.len() - 1) as f64)) * scale * scale;
    Some(var.sqrt())
}

/// Lanczos approximation for `ln(Gamma(z))` for all `z > 0`.
#[must_use]
pub fn ln_gamma(z: f64) -> f64 {
    const COEFFS: [f64; 9] = [
        0.999_999_999_999_809_9,
        676.520_368_121_885_1,
        -1_259.139_216_722_402_8,
        771.323_428_777_653_1,
        -176.615_029_162_140_6,
        12.507_343_278_686_905,
        -0.138_571_095_265_720_12,
        9.984_369_578_019_572e-6,
        1.505_632_735_149_311_6e-7,
    ];
    if z <= 0.0 || !z.is_finite() {
        return f64::NAN;
    }
    if z < 0.5 {
        let pi = std::f64::consts::PI;
        return pi.ln() - (pi * z).sin().abs().ln() - ln_gamma(1.0 - z);
    }
    let z_shift = z - 1.0;
    let mut x = COEFFS[0];
    for (i, &c) in COEFFS.iter().enumerate().skip(1) {
        x += c / (z_shift + i as f64);
    }
    let t = z_shift + 7.5;
    0.5 * (2.0 * std::f64::consts::PI).ln() + (z_shift + 0.5) * t.ln() - t + x.ln()
}

/// Regularized incomplete beta function `I_x(a, b)` via modified Lentz continued fraction.
#[must_use]
pub fn reg_incomplete_beta(a: f64, b: f64, x: f64) -> f64 {
    if !a.is_finite() || !b.is_finite() || !x.is_finite() || a <= 0.0 || b <= 0.0 {
        return f64::NAN;
    }
    if x <= 0.0 {
        return 0.0;
    }
    if x >= 1.0 {
        return 1.0;
    }
    let log_bt = ln_gamma(a + b) - ln_gamma(a) - ln_gamma(b) + a * x.ln() + b * (1.0 - x).ln();
    let bt = log_bt.exp();
    if x < (a + 1.0) / (a + b + 2.0) {
        (bt * beta_cf(a, b, x) / a).clamp(0.0, 1.0)
    } else {
        (1.0 - bt * beta_cf(b, a, 1.0 - x) / b).clamp(0.0, 1.0)
    }
}

fn beta_cf(a: f64, b: f64, x: f64) -> f64 {
    const FPMIN: f64 = 1e-30;
    const EPS: f64 = 1e-14;
    let qab = a + b;
    let qap = a + 1.0;
    let qam = a - 1.0;
    let mut c = 1.0_f64;
    let mut d = 1.0 - qab * x / qap;
    if d.abs() < FPMIN {
        d = FPMIN;
    }
    d = 1.0 / d;
    let mut h = d;
    for m in 1..=300 {
        let mf = f64::from(m);
        let m2 = 2.0 * mf;
        let aa = mf * (b - mf) * x / ((qam + m2) * (a + m2));
        d = 1.0 + aa * d;
        if d.abs() < FPMIN {
            d = FPMIN;
        }
        c = 1.0 + aa / c;
        if c.abs() < FPMIN {
            c = FPMIN;
        }
        d = 1.0 / d;
        h *= d * c;
        let aa2 = -(a + mf) * (qab + mf) * x / ((a + m2) * (qap + m2));
        d = 1.0 + aa2 * d;
        if d.abs() < FPMIN {
            d = FPMIN;
        }
        c = 1.0 + aa2 / c;
        if c.abs() < FPMIN {
            c = FPMIN;
        }
        d = 1.0 / d;
        let del = d * c;
        h *= del;
        if (del - 1.0).abs() < EPS {
            break;
        }
    }
    h
}

/// Two-tailed Student-t p-value via `I_{df / (df + t^2)}(df / 2, 1/2)`.
#[must_use]
pub fn student_t_two_tailed_p(t_abs: f64, df: f64) -> f64 {
    if !t_abs.is_finite() || !df.is_finite() || df <= 0.0 {
        return f64::NAN;
    }
    if t_abs == 0.0 {
        return 1.0;
    }
    let x = df / (df + t_abs * t_abs);
    reg_incomplete_beta(df * 0.5, 0.5, x).clamp(0.0, 1.0)
}

/// Regularized upper incomplete gamma `Q(a, x) = Gamma(a, x) / Gamma(a)` using the
/// series expansion for `x < a + 1` and modified Lentz continued fraction for `x >= a + 1`.
#[must_use]
pub fn reg_upper_incomplete_gamma(a: f64, x: f64) -> f64 {
    const EPS: f64 = 1e-14;
    const FPMIN: f64 = 1e-30;

    if !a.is_finite() || !x.is_finite() || a <= 0.0 || x < 0.0 {
        return f64::NAN;
    }
    if x == 0.0 {
        return 1.0;
    }
    let gln = ln_gamma(a);
    let log_prefactor = -x + a * x.ln() - gln;

    if x < a + 1.0 {
        // Series representation for lower incomplete gamma P(a, x).
        let mut ap = a;
        let mut del = 1.0 / a;
        let mut sum = del;
        for _ in 0..500 {
            ap += 1.0;
            del *= x / ap;
            sum += del;
            if del.abs() < sum.abs() * EPS {
                break;
            }
        }
        let p = (sum * log_prefactor.exp()).clamp(0.0, 1.0);
        (1.0 - p).clamp(0.0, 1.0)
    } else {
        // Modified Lentz continued fraction for upper incomplete gamma Q(a, x).
        let mut b = x + 1.0 - a;
        let mut c = 1.0 / FPMIN;
        let mut d = 1.0 / b;
        let mut h = d;
        for i in 1..=500 {
            let fi = f64::from(i);
            let an = -fi * (fi - a);
            b += 2.0;
            d = an * d + b;
            if d.abs() < FPMIN {
                d = FPMIN;
            }
            c = b + an / c;
            if c.abs() < FPMIN {
                c = FPMIN;
            }
            d = 1.0 / d;
            let del = d * c;
            h *= del;
            if (del - 1.0).abs() < EPS {
                break;
            }
        }
        (log_prefactor.exp() * h).clamp(0.0, 1.0)
    }
}

/// Upper-tail chi-square p-value `P(Chi^2_df >= chi2) = Q(df / 2, chi2 / 2)`.
#[must_use]
pub fn chi_square_p_value(chi2: f64, df: f64) -> f64 {
    if !chi2.is_finite() || !df.is_finite() || df <= 0.0 || chi2 < 0.0 {
        return f64::NAN;
    }
    reg_upper_incomplete_gamma(df * 0.5, chi2 * 0.5)
}

// ---------------------------------------------------------------------------
// Correlation (Pearson & Tie-Aware Spearman)
// ---------------------------------------------------------------------------

/// Compute exact Pearson sample correlation coefficient `r` in `[-1.0, 1.0]`.
#[must_use]
pub fn pearson_corr(xs: &[f64], ys: &[f64]) -> Option<f64> {
    if xs.len() != ys.len()
        || xs.len() < 2
        || xs.iter().any(|x| !x.is_finite())
        || ys.iter().any(|y| !y.is_finite())
    {
        return None;
    }
    let mean_x = mean_f64(xs)?;
    let mean_y = mean_f64(ys)?;
    let scale_x = xs
        .iter()
        .fold(0.0_f64, |acc, &x| acc.max((x - mean_x).abs()));
    let scale_y = ys
        .iter()
        .fold(0.0_f64, |acc, &y| acc.max((y - mean_y).abs()));
    if scale_x == 0.0 || scale_y == 0.0 || !scale_x.is_finite() || !scale_y.is_finite() {
        return None;
    }
    let mut u_sxx = 0.0_f64;
    let mut u_syy = 0.0_f64;
    let mut u_sxy = 0.0_f64;
    for (&x, &y) in xs.iter().zip(ys) {
        let ux = (x - mean_x) / scale_x;
        let uy = (y - mean_y) / scale_y;
        u_sxx += ux * ux;
        u_syy += uy * uy;
        u_sxy += ux * uy;
    }
    let denom = u_sxx.sqrt() * u_syy.sqrt();
    if denom == 0.0 || !denom.is_finite() {
        None
    } else {
        Some((u_sxy / denom).clamp(-1.0, 1.0))
    }
}

/// Assign 1-based average ranks with exact tie handling.
fn average_ranks(xs: &[f64]) -> Vec<f64> {
    let n = xs.len();
    let mut order: Vec<usize> = (0..n).collect();
    order.sort_by(|&a, &b| xs[a].total_cmp(&xs[b]));
    let mut ranks = vec![0.0_f64; n];
    let mut i = 0usize;
    while i < n {
        let mut j = i + 1;
        while j < n && xs[order[j]] == xs[order[i]] {
            j += 1;
        }
        // 1-based positions are (i + 1)..=j; average is (i + 1 + j) / 2.
        let avg_rank = ((i + 1 + j) as f64) * 0.5;
        for &idx in &order[i..j] {
            ranks[idx] = avg_rank;
        }
        i = j;
    }
    ranks
}

/// Compute exact Spearman rank correlation coefficient `rho` with exact average-rank ties.
#[must_use]
pub fn spearman_corr(xs: &[f64], ys: &[f64]) -> Option<f64> {
    if xs.len() != ys.len()
        || xs.len() < 2
        || xs.iter().any(|x| !x.is_finite())
        || ys.iter().any(|y| !y.is_finite())
    {
        return None;
    }
    let rx = average_ranks(xs);
    let ry = average_ranks(ys);
    pearson_corr(&rx, &ry)
}

// ---------------------------------------------------------------------------
// OLS Simple Linear Regression
// ---------------------------------------------------------------------------

/// Compute exact simple OLS linear regression `y = slope * x + intercept` and `R^2`.
#[must_use]
pub fn linear_regression(xs: &[f64], ys: &[f64]) -> Option<LinearRegressionResult> {
    if xs.len() != ys.len()
        || xs.len() < 2
        || xs.iter().any(|x| !x.is_finite())
        || ys.iter().any(|y| !y.is_finite())
    {
        return None;
    }
    let mean_x = mean_f64(xs)?;
    let mean_y = mean_f64(ys)?;
    let scale_x = xs
        .iter()
        .fold(0.0_f64, |acc, &x| acc.max((x - mean_x).abs()));
    let scale_y = ys
        .iter()
        .fold(0.0_f64, |acc, &y| acc.max((y - mean_y).abs()));
    if scale_x == 0.0 || !scale_x.is_finite() {
        return None;
    }
    if scale_y == 0.0 {
        return Some(LinearRegressionResult {
            slope: 0.0,
            intercept: mean_y,
            r_squared: 1.0,
        });
    }
    if !scale_y.is_finite() {
        return None;
    }
    let mut u_sxx = 0.0_f64;
    let mut u_syy = 0.0_f64;
    let mut u_sxy = 0.0_f64;
    for (&x, &y) in xs.iter().zip(ys) {
        let ux = (x - mean_x) / scale_x;
        let uy = (y - mean_y) / scale_y;
        u_sxx += ux * ux;
        u_syy += uy * uy;
        u_sxy += ux * uy;
    }
    if u_sxx == 0.0 {
        return None;
    }
    let slope = (u_sxy / u_sxx) * (scale_y / scale_x);
    let intercept = mean_y - slope * mean_x;
    let r_squared = if u_syy == 0.0 {
        1.0
    } else {
        ((u_sxy * u_sxy) / (u_sxx * u_syy)).clamp(0.0, 1.0)
    };
    Some(LinearRegressionResult {
        slope,
        intercept,
        r_squared,
    })
}

// ---------------------------------------------------------------------------
// Two-Sample Welch t-Test
// ---------------------------------------------------------------------------

/// Compute an exact two-sample Welch t-test (unequal variances) with Welch-Satterthwaite
/// degrees of freedom and exact two-tailed Student-t p-value.
#[must_use]
pub fn welch_t_test(xa: &[f64], xb: &[f64]) -> Option<WelchTTestResult> {
    if xa.len() < 2
        || xb.len() < 2
        || xa.iter().any(|x| !x.is_finite())
        || xb.iter().any(|x| !x.is_finite())
    {
        return None;
    }
    let na = xa.len() as f64;
    let nb = xb.len() as f64;
    let ma = mean_f64(xa)?;
    let mb = mean_f64(xb)?;
    let va = xa.iter().map(|&x| (x - ma) * (x - ma)).sum::<f64>() / (na - 1.0);
    let vb = xb.iter().map(|&x| (x - mb) * (x - mb)).sum::<f64>() / (nb - 1.0);
    let se2 = va / na + vb / nb;
    if se2 == 0.0 {
        return if (ma - mb).abs() == 0.0 {
            Some(WelchTTestResult {
                t_stat: 0.0,
                df: na + nb - 2.0,
                p_value: 1.0,
            })
        } else {
            Some(WelchTTestResult {
                t_stat: (ma - mb).signum() * f64::INFINITY,
                df: na + nb - 2.0,
                p_value: 0.0,
            })
        };
    }
    let t_stat = (ma - mb) / se2.sqrt();
    let df_num = se2 * se2;
    let df_den = (va / na).powi(2) / (na - 1.0) + (vb / nb).powi(2) / (nb - 1.0);
    let df = if df_den > 0.0 {
        df_num / df_den
    } else {
        na + nb - 2.0
    };
    let p_value = student_t_two_tailed_p(t_stat.abs(), df);
    Some(WelchTTestResult {
        t_stat,
        df,
        p_value,
    })
}

// ---------------------------------------------------------------------------
// Chi-Square Tests (Independence & Goodness-of-Fit)
// ---------------------------------------------------------------------------

/// Compute Pearson chi-square test of independence on an `r x c` observed contingency table.
#[must_use]
pub fn chi_square_contingency(observed: &[Vec<usize>]) -> Option<ChiSquareResult> {
    let r = observed.len();
    let c = observed.first().map_or(0, Vec::len);
    if r < 2 || c < 2 || observed.iter().any(|row| row.len() != c) {
        return None;
    }
    let mut row_sums = vec![0usize; r];
    let mut col_sums = vec![0usize; c];
    let mut total = 0usize;
    for (i, row) in observed.iter().enumerate() {
        for (j, &cnt) in row.iter().enumerate() {
            row_sums[i] += cnt;
            col_sums[j] += cnt;
            total += cnt;
        }
    }
    if total == 0 || row_sums.contains(&0) || col_sums.contains(&0) {
        return None;
    }
    let n = total as f64;
    let mut chi2 = 0.0_f64;
    for (i, row) in observed.iter().enumerate() {
        for (j, &cnt) in row.iter().enumerate() {
            let expected = (row_sums[i] as f64) * (col_sums[j] as f64) / n;
            let diff = (cnt as f64) - expected;
            chi2 += (diff * diff) / expected;
        }
    }
    let df = ((r - 1) * (c - 1)) as f64;
    let p_value = chi_square_p_value(chi2, df);
    Some(ChiSquareResult {
        stat: chi2,
        df,
        p_value,
    })
}

/// Compute Pearson chi-square goodness-of-fit test on `(observed, expected)` slices.
#[must_use]
pub fn chi_square_gof(observed: &[f64], expected: &[f64]) -> Option<ChiSquareResult> {
    if observed.len() != expected.len() || observed.len() < 2 {
        return None;
    }
    let mut chi2 = 0.0_f64;
    for (&o, &e) in observed.iter().zip(expected) {
        if !o.is_finite() || !e.is_finite() || o < 0.0 || e <= 0.0 {
            return None;
        }
        let diff = o - e;
        chi2 += (diff * diff) / e;
    }
    let df = (observed.len() - 1) as f64;
    let p_value = chi_square_p_value(chi2, df);
    Some(ChiSquareResult {
        stat: chi2,
        df,
        p_value,
    })
}

// ---------------------------------------------------------------------------
// Table Wrappers
// ---------------------------------------------------------------------------

fn extract_numeric_pairs(
    tv: &TableVal,
    col_x: &str,
    col_y: &str,
) -> Result<(Vec<f64>, Vec<f64>), String> {
    let ix = tv
        .cols
        .iter()
        .position(|c| c.name == col_x)
        .ok_or_else(|| format!("missing column `{col_x}`"))?;
    let iy = tv
        .cols
        .iter()
        .position(|c| c.name == col_y)
        .ok_or_else(|| format!("missing column `{col_y}`"))?;
    let mut xs = Vec::new();
    let mut ys = Vec::new();
    for r in &tv.rows {
        if let (Some(vx), Some(vy)) = (r.cells.get(ix), r.cells.get(iy))
            && let (Some(x), Some(y)) = (unwrap_numeric_float(vx), unwrap_numeric_float(vy))
            && x.is_finite()
            && y.is_finite()
        {
            xs.push(x);
            ys.push(y);
        }
    }
    Ok((xs, ys))
}

/// Extract numeric column values from `tv`, skipping nulls.
pub fn extract_numeric_col(tv: &TableVal, col: &str) -> Result<Vec<f64>, String> {
    let idx = tv
        .cols
        .iter()
        .position(|c| c.name == col)
        .ok_or_else(|| format!("missing column `{col}`"))?;
    let vals = tv
        .rows
        .iter()
        .filter_map(|r| r.cells.get(idx).and_then(unwrap_numeric_float))
        .filter(|x| x.is_finite())
        .collect();
    Ok(vals)
}

/// Table wrapper for Pearson correlation.
pub fn pearson_corr_table(tv: &TableVal, col_x: &str, col_y: &str) -> Result<Option<f64>, String> {
    let (xs, ys) = extract_numeric_pairs(tv, col_x, col_y)?;
    Ok(pearson_corr(&xs, &ys))
}

/// Table wrapper for Spearman rank correlation.
pub fn spearman_corr_table(tv: &TableVal, col_x: &str, col_y: &str) -> Result<Option<f64>, String> {
    let (xs, ys) = extract_numeric_pairs(tv, col_x, col_y)?;
    Ok(spearman_corr(&xs, &ys))
}

/// Table wrapper for OLS simple linear regression.
pub fn linear_regression_table(
    tv: &TableVal,
    col_x: &str,
    col_y: &str,
) -> Result<Option<LinearRegressionResult>, String> {
    let (xs, ys) = extract_numeric_pairs(tv, col_x, col_y)?;
    Ok(linear_regression(&xs, &ys))
}

/// Table wrapper for two-sample Welch t-test.
pub fn welch_t_test_tables(
    a: &TableVal,
    b: &TableVal,
    col: &str,
) -> Result<Option<WelchTTestResult>, String> {
    let xa = extract_numeric_col(a, col)?;
    let xb = extract_numeric_col(b, col)?;
    Ok(welch_t_test(&xa, &xb))
}

fn unwrap_non_null_val(v: &Val) -> Option<&Val> {
    match v {
        Val::OptNone => None,
        Val::OptSome(inner) => Some(inner.as_ref()),
        other => Some(other),
    }
}

/// Table wrapper for Pearson chi-square test of independence over two categorical columns.
pub fn chi_square_independence_table(
    tv: &TableVal,
    col_x: &str,
    col_y: &str,
) -> Result<Option<ChiSquareResult>, String> {
    let ix = tv
        .cols
        .iter()
        .position(|c| c.name == col_x)
        .ok_or_else(|| format!("Stats.chi_square: missing column `{col_x}`"))?;
    let iy = tv
        .cols
        .iter()
        .position(|c| c.name == col_y)
        .ok_or_else(|| format!("Stats.chi_square: missing column `{col_y}`"))?;

    let mut x_ids: HashMap<SingleKey, usize> = HashMap::new();
    let mut y_ids: HashMap<SingleKey, usize> = HashMap::new();
    let mut pairs: Vec<(usize, usize)> = Vec::new();

    for r in &tv.rows {
        let Some(vx) = r.cells.get(ix).and_then(unwrap_non_null_val) else {
            continue;
        };
        let Some(vy) = r.cells.get(iy).and_then(unwrap_non_null_val) else {
            continue;
        };
        let kx = SingleKey::new(vx.clone());
        let next_x = x_ids.len();
        let xi = *x_ids.entry(kx).or_insert(next_x);
        let ky = SingleKey::new(vy.clone());
        let next_y = y_ids.len();
        let yi = *y_ids.entry(ky).or_insert(next_y);
        pairs.push((xi, yi));
    }

    let r_cnt = x_ids.len();
    let c_cnt = y_ids.len();
    if r_cnt < 2 || c_cnt < 2 {
        return Ok(None);
    }
    let mut counts = vec![vec![0usize; c_cnt]; r_cnt];
    for (xi, yi) in pairs {
        counts[xi][yi] += 1;
    }
    Ok(chi_square_contingency(&counts))
}

/// Table wrapper for Pearson chi-square goodness-of-fit test over `(observed, expected)` columns.
pub fn chi_square_gof_table(
    tv: &TableVal,
    observed_col: &str,
    expected_col: &str,
) -> Result<Option<ChiSquareResult>, String> {
    let (obs, exp) = extract_numeric_pairs(tv, observed_col, expected_col)
        .map_err(|e| format!("Stats.chi_square: {e}"))?;
    Ok(chi_square_gof(&obs, &exp))
}

/// Flag outlier rows in `tv` on `col` using `:zscore` or `:iqr`, appending a `Bool`
/// column named `flag_col` stamped with `flag_tags` (union with runtime column tags).
pub fn detect_outliers_table(
    tv: &TableVal,
    col: &str,
    method: OutlierMethod,
    threshold: f64,
    flag_col: &str,
    flag_tags: &TagSet,
) -> Result<TableVal, String> {
    let idx = tv
        .cols
        .iter()
        .position(|c| c.name == col)
        .ok_or_else(|| format!("Stats.outliers: missing column `{col}`"))?;

    let non_null_vals: Vec<f64> = tv
        .rows
        .iter()
        .filter_map(|r| r.cells.get(idx).and_then(unwrap_numeric_float))
        .filter(|x| x.is_finite())
        .collect();

    let flags: Vec<bool> = if non_null_vals.len() < 2 || !threshold.is_finite() {
        vec![false; tv.rows.len()]
    } else {
        match method {
            OutlierMethod::ZScore => {
                let mean = mean_f64(&non_null_vals);
                let sd = sample_stddev(&non_null_vals);
                match (mean, sd) {
                    (Some(mu), Some(s)) if s > 0.0 && s.is_finite() => tv
                        .rows
                        .iter()
                        .map(|r| {
                            r.cells
                                .get(idx)
                                .and_then(unwrap_numeric_float)
                                .is_some_and(|x| x.is_finite() && ((x - mu).abs() / s) >= threshold)
                        })
                        .collect(),
                    _ => vec![false; tv.rows.len()],
                }
            }
            OutlierMethod::Iqr => {
                let mut sorted = non_null_vals;
                sorted.sort_by(f64::total_cmp);
                match (
                    quantile_sorted(&sorted, 0.25),
                    quantile_sorted(&sorted, 0.75),
                ) {
                    (Some(q1), Some(q3)) => {
                        let iqr = q3 - q1;
                        let lo = q1 - threshold * iqr;
                        let hi = q3 + threshold * iqr;
                        tv.rows
                            .iter()
                            .map(|r| {
                                r.cells
                                    .get(idx)
                                    .and_then(unwrap_numeric_float)
                                    .is_some_and(|x| x.is_finite() && (x < lo || x > hi))
                            })
                            .collect()
                    }
                    _ => vec![false; tv.rows.len()],
                }
            }
        }
    };

    let mut out_cols = tv.cols.clone();
    let eff_tags = tv.cols[idx].tags.union(flag_tags);
    out_cols.push(ColSpec {
        name: flag_col.to_string(),
        ty: ScalarTy::Bool,
        tags: eff_tags,
        bucketed: false,
        agg_kind: AggKind::Raw,
    });

    let out_rows = tv
        .rows
        .iter()
        .zip(flags)
        .map(|(r, is_outlier)| {
            let mut cells = r.cells.clone();
            cells.push(Val::Bool(is_outlier));
            TableRow {
                cells,
                group_meta: r.group_meta,
            }
        })
        .collect();

    Ok(TableVal {
        cols: out_cols,
        rows: out_rows,
    })
}
