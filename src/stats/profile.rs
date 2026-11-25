//! Privacy-safe dataset profiler (`table.profile()` & `console.print_profile`).
//!
//! - Public columns (both column tags and table `row_tags` empty): computes `null_pct`,
//!   `distinct_count`, numeric stats (`mean`, `stddev`, `min`, `p25`, `median`, `p75`, `max`),
//!   an 8-bin Unicode sparkline (`▁▂▃▄▅▆▇█`), and top-3 categorical values.
//! - Sensitive / tagged columns (non-empty column tags OR non-empty table `row_tags`):
//!   strictly redacts ALL value-derived statistics to `[REDACTED:<sorted,tags>]`, exposing
//!   only structural counts (`row_count`, `null_count`, `distinct_count`).

use std::collections::{HashMap, HashSet};
use std::fmt::Write as _;

use crate::core::syntax::{Float64, Ident, ScalarTy, TagSet};
use crate::formats::time::{format_iso_date, format_iso_timestamp};
use crate::oracle::value::{
    ProfileColSummary, ProfileVal, TableVal, Val, render_decimal, render_public_val,
    unwrap_numeric_float, val_lt,
};
use crate::stats::{mean_f64, quantile_sorted, sample_stddev};
use crate::vm::key::SingleKey;

const SPARK_BLOCKS: [char; 8] = ['▁', '▂', '▃', '▄', '▅', '▆', '▇', '█'];

/// Format a [`ScalarTy`] into a concise human-readable type name (e.g. `Float?`, `Int`).
#[must_use]
pub fn format_scalar_ty_name(ty: &ScalarTy) -> String {
    match ty {
        ScalarTy::Unit => "Unit".to_string(),
        ScalarTy::Bool => "Bool".to_string(),
        ScalarTy::Int => "Int".to_string(),
        ScalarTy::Decimal => "Decimal".to_string(),
        ScalarTy::Float => "Float".to_string(),
        ScalarTy::Text => "Text".to_string(),
        ScalarTy::Bytes => "Bytes".to_string(),
        ScalarTy::Date => "Date".to_string(),
        ScalarTy::Timestamp => "Timestamp".to_string(),
        ScalarTy::Duration => "Duration".to_string(),
        ScalarTy::Data(name) => name.clone(),
        ScalarTy::Option(inner) => format!("{}?", format_scalar_ty_name(inner)),
    }
}

fn is_numeric_scalar_ty(ty: &ScalarTy) -> bool {
    match ty {
        ScalarTy::Int | ScalarTy::Decimal | ScalarTy::Float => true,
        ScalarTy::Option(inner) => is_numeric_scalar_ty(inner),
        _ => false,
    }
}

fn display_public_cell(v: &Val) -> String {
    match v {
        Val::Text(s) => s.clone(),
        Val::Date(d) => d.to_i64().map_or_else(|| d.to_string(), format_iso_date),
        Val::Timestamp(ts) => ts
            .to_i64()
            .map_or_else(|| ts.to_string(), format_iso_timestamp),
        Val::Decimal(d) => render_decimal(d),
        Val::Float(f) => format_compact_num(f.to_f64()),
        Val::OptNone => "none".to_string(),
        Val::OptSome(inner) => display_public_cell(inner),
        other => render_public_val(other),
    }
}

fn format_compact_num(x: f64) -> String {
    if !x.is_finite() {
        return format!("{x}");
    }
    if x == 0.0 {
        return "0".to_string();
    }
    let abs = x.abs();
    if (abs - abs.round()).abs() < 1e-9 && abs < 1e12 {
        format!("{:.0}", x)
    } else if !(1e-3..1e7).contains(&abs) {
        format!("{x:.2e}")
    } else {
        let s = format!("{x:.3}");
        s.trim_end_matches('0').trim_end_matches('.').to_string()
    }
}

/// Build an 8-bin Unicode histogram sparkline (`▁▂▃▄▅▆▇█`) from sorted finite values.
#[must_use]
pub fn build_sparkline(sorted: &[f64]) -> Option<String> {
    if sorted.is_empty() {
        return None;
    }
    let min_v = sorted[0];
    let max_v = sorted[sorted.len() - 1];
    let span = max_v - min_v;
    let mut bins = [0usize; 8];
    if span <= 0.0 || !span.is_finite() {
        bins[3] = sorted.len();
    } else {
        for &x in sorted {
            let norm = ((x - min_v) / span).clamp(0.0, 1.0);
            let b = ((norm * 8.0).floor() as usize).min(7);
            bins[b] += 1;
        }
    }
    let max_bin = bins.iter().copied().max().unwrap_or(0);
    if max_bin == 0 {
        return None;
    }
    let mut out = String::with_capacity(8 * 3);
    for count in bins {
        let level = if count == 0 {
            0
        } else {
            (((count as f64) / (max_bin as f64) * 7.0).round() as usize).min(7)
        };
        out.push(SPARK_BLOCKS[level]);
    }
    Some(out)
}

/// Compute a privacy-safe [`ProfileVal`] for `tv`.
///
/// Any column whose runtime `ColSpec.tags`, `static_col_tags` entry, OR `table_row_tags`
/// is non-empty has ALL value-derived statistics strictly redacted to `[REDACTED:...]`.
#[must_use]
pub fn profile_table(
    tv: &TableVal,
    table_row_tags: &TagSet,
    static_col_tags: &[(Ident, TagSet)],
) -> ProfileVal {
    let mut cols = Vec::with_capacity(tv.cols.len());

    for (idx, c) in tv.cols.iter().enumerate() {
        let row_count = tv.rows.len();
        let mut null_count = 0usize;
        let mut non_null: Vec<&Val> = Vec::new();
        let mut distinct_set: HashSet<SingleKey> = HashSet::new();

        for r in &tv.rows {
            match r.cells.get(idx) {
                None | Some(Val::OptNone) => null_count += 1,
                Some(Val::OptSome(inner)) => {
                    let v = inner.as_ref();
                    distinct_set.insert(SingleKey::new(v.clone()));
                    non_null.push(v);
                }
                Some(other) => {
                    distinct_set.insert(SingleKey::new(other.clone()));
                    non_null.push(other);
                }
            }
        }

        let distinct_count = distinct_set.len();
        let null_pct = if row_count == 0 {
            0.0
        } else {
            (null_count as f64) * 100.0 / (row_count as f64)
        };

        let mut eff_tags = c.tags.union(table_row_tags);
        if let Some((_, st)) = static_col_tags.iter().find(|(name, _)| name == &c.name) {
            eff_tags = eff_tags.union(st);
        }

        if !eff_tags.is_empty() {
            let mut tags_vec: Vec<String> = eff_tags.elems().to_vec();
            tags_vec.sort();
            tags_vec.dedup();
            let marker = format!("[REDACTED:{}]", tags_vec.join(","));
            cols.push(ProfileColSummary {
                col_name: c.name.clone(),
                ty_name: format_scalar_ty_name(&c.ty),
                row_count,
                null_count,
                distinct_count,
                min_display: Some(marker.clone()),
                max_display: Some(marker),
                null_pct: Float64::from_f64(null_pct),
                mean: None,
                stddev: None,
                min: None,
                p25: None,
                median: None,
                p75: None,
                max: None,
                sparkline: None,
                top_values: Vec::new(),
                redacted_tags: tags_vec,
            });
            continue;
        }

        // Public column: compute full numeric or categorical statistics.
        let mut mean_val = None;
        let mut stddev_val = None;
        let mut min_val = None;
        let mut p25_val = None;
        let mut median_val = None;
        let mut p75_val = None;
        let mut max_val = None;
        let mut sparkline = None;
        let mut top_values = Vec::new();
        let mut min_display = None;
        let mut max_display = None;

        if is_numeric_scalar_ty(&c.ty) {
            let mut nums: Vec<f64> = non_null
                .iter()
                .filter_map(|v| unwrap_numeric_float(v))
                .filter(|x| x.is_finite())
                .collect();
            if !nums.is_empty() {
                nums.sort_by(f64::total_cmp);
                let mn = nums[0];
                let mx = nums[nums.len() - 1];
                min_val = Some(Float64::from_f64(mn));
                max_val = Some(Float64::from_f64(mx));
                min_display = Some(format_compact_num(mn));
                max_display = Some(format_compact_num(mx));
                mean_val = mean_f64(&nums).map(Float64::from_f64);
                stddev_val = sample_stddev(&nums).map(Float64::from_f64);
                p25_val = quantile_sorted(&nums, 0.25).map(Float64::from_f64);
                median_val = quantile_sorted(&nums, 0.50).map(Float64::from_f64);
                p75_val = quantile_sorted(&nums, 0.75).map(Float64::from_f64);
                sparkline = build_sparkline(&nums);
            }
        } else {
            let mut freq: HashMap<String, usize> = HashMap::new();
            let mut min_v: Option<&Val> = None;
            let mut max_v: Option<&Val> = None;
            for &v in &non_null {
                *freq.entry(display_public_cell(v)).or_insert(0) += 1;
                if min_v.is_none_or(|cur| val_lt(v, cur)) {
                    min_v = Some(v);
                }
                if max_v.is_none_or(|cur| val_lt(cur, v)) {
                    max_v = Some(v);
                }
            }
            min_display = min_v.map(display_public_cell);
            max_display = max_v.map(display_public_cell);
            let mut items: Vec<(String, usize)> = freq.into_iter().collect();
            items.sort_by(|a, b| b.1.cmp(&a.1).then_with(|| a.0.cmp(&b.0)));
            items.truncate(3);
            top_values = items;
        }

        cols.push(ProfileColSummary {
            col_name: c.name.clone(),
            ty_name: format_scalar_ty_name(&c.ty),
            row_count,
            null_count,
            distinct_count,
            min_display,
            max_display,
            null_pct: Float64::from_f64(null_pct),
            mean: mean_val,
            stddev: stddev_val,
            min: min_val,
            p25: p25_val,
            median: median_val,
            p75: p75_val,
            max: max_val,
            sparkline,
            top_values,
            redacted_tags: Vec::new(),
        });
    }

    ProfileVal { cols }
}

fn col_summary_text(c: &ProfileColSummary) -> String {
    if !c.redacted_tags.is_empty() {
        return format!("[REDACTED:{}]", c.redacted_tags.join(","));
    }
    if let (Some(mean), Some(mn), Some(med), Some(mx)) = (c.mean, c.min, c.median, c.max) {
        let mut s = format!("mean={}", format_compact_num(mean.to_f64()));
        if let Some(sd) = c.stddev {
            let _ = write!(s, " sd={}", format_compact_num(sd.to_f64()));
        }
        let _ = write!(s, " min={}", format_compact_num(mn.to_f64()));
        if let Some(p25) = c.p25 {
            let _ = write!(s, " p25={}", format_compact_num(p25.to_f64()));
        }
        let _ = write!(s, " med={}", format_compact_num(med.to_f64()));
        if let Some(p75) = c.p75 {
            let _ = write!(s, " p75={}", format_compact_num(p75.to_f64()));
        }
        let _ = write!(s, " max={}", format_compact_num(mx.to_f64()));
        return s;
    }
    if !c.top_values.is_empty() {
        let joined: Vec<String> = c
            .top_values
            .iter()
            .map(|(v, cnt)| format!("\"{v}\" ({cnt})"))
            .collect();
        return format!("top: {}", joined.join(", "));
    }
    if let (Some(mn), Some(mx)) = (&c.min_display, &c.max_display) {
        if mn == mx {
            return mn.clone();
        }
        return format!("{mn} .. {mx}");
    }
    "(empty)".to_string()
}

/// Render a [`ProfileVal`] as an aligned terminal table with types, null %, distinct count,
/// summary stats/top values, and 8-bin sparklines (or `[REDACTED:...]`).
#[must_use]
pub fn render_profile_terminal(profile: &ProfileVal) -> String {
    if profile.cols.is_empty() {
        return "Dataset Profile: (0 columns)".to_string();
    }
    let headers = [
        "Column",
        "Type",
        "Null %",
        "Distinct",
        "Summary",
        "Sparkline",
    ];
    let mut rows: Vec<[String; 6]> = Vec::with_capacity(profile.cols.len());
    let mut widths = [
        headers[0].len(),
        headers[1].len(),
        headers[2].len(),
        headers[3].len(),
        headers[4].len(),
        headers[5].len(),
    ];

    let total_rows = profile.cols.first().map_or(0, |c| c.row_count);
    for c in &profile.cols {
        let null_str = format!("{:.1}% ({})", c.null_pct.to_f64(), c.null_count);
        let dist_str = c.distinct_count.to_string();
        let summary = col_summary_text(c);
        let spark = if !c.redacted_tags.is_empty() {
            "-".to_string()
        } else {
            c.sparkline.clone().unwrap_or_else(|| "-".to_string())
        };
        let row = [
            c.col_name.clone(),
            c.ty_name.clone(),
            null_str,
            dist_str,
            summary,
            spark,
        ];
        for (i, cell) in row.iter().enumerate() {
            widths[i] = widths[i].max(cell.chars().count());
        }
        rows.push(row);
    }

    let mut out = String::new();
    let _ = writeln!(
        out,
        "Dataset Profile ({total_rows} rows, {} cols)",
        profile.cols.len()
    );
    out.push('|');
    for (i, h) in headers.iter().enumerate() {
        let w = widths[i];
        let _ = write!(out, " {h:<w$} |");
    }
    out.push('\n');
    out.push('|');
    for &w in &widths {
        out.push(' ');
        for _ in 0..w {
            out.push('-');
        }
        out.push_str(" |");
    }
    for row in rows {
        out.push('\n');
        out.push('|');
        for (i, cell) in row.iter().enumerate() {
            let pad = widths[i].saturating_sub(cell.chars().count());
            out.push(' ');
            out.push_str(cell);
            for _ in 0..pad {
                out.push(' ');
            }
            out.push_str(" |");
        }
    }
    out
}
