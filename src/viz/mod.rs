//! Zero-dependency chart and report rendering engine (`svg`, `terminal`, `report`).

pub mod report;
pub mod svg;
pub mod terminal;

use crate::formats::time::{format_iso_date, format_iso_timestamp};
use crate::oracle::value::{
    ChartVal, Val, render_decimal, render_public_val, unwrap_numeric_float,
};

/// Accessible 8-color chart palette (high-contrast, colorblind-friendly).
pub const PALETTE: [&str; 8] = [
    "#2563eb", "#ea580c", "#059669", "#9333ea", "#dc2626", "#0891b2", "#ca8a04", "#db2777",
];

/// Strictly escape text for XML/SVG/HTML text nodes and attribute values.
#[must_use]
pub fn xml_escape(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for ch in s.chars() {
        match ch {
            '&' => out.push_str("&amp;"),
            '<' => out.push_str("&lt;"),
            '>' => out.push_str("&gt;"),
            '"' => out.push_str("&quot;"),
            '\'' => out.push_str("&#39;"),
            other => out.push(other),
        }
    }
    out
}

/// Sanitize an `f64` coordinate so SVG output NEVER emits `NaN` or `inf`.
#[must_use]
pub fn safe_coord(v: f64) -> f64 {
    if v.is_finite() { v } else { 0.0 }
}

/// Format an `f64` coordinate cleanly with 2 decimal places, guaranteed finite.
#[must_use]
pub fn fmt_coord(v: f64) -> String {
    format!("{:.2}", safe_coord(v))
}

/// Format a runtime value for axis labels, legends, and report table cells.
#[must_use]
pub fn format_chart_val(v: &Val) -> String {
    match v {
        Val::Text(s) => s.clone(),
        Val::Date(d) => d.to_i64().map_or_else(|| d.to_string(), format_iso_date),
        Val::Timestamp(ts) => ts
            .to_i64()
            .map_or_else(|| ts.to_string(), format_iso_timestamp),
        Val::Decimal(d) => render_decimal(d),
        Val::Float(f) => format_tick_num(f.to_f64()),
        Val::OptNone => "none".to_string(),
        Val::OptSome(inner) => format_chart_val(inner),
        other => render_public_val(other),
    }
}

/// Format a tick / axis number concisely without ugly floating noise.
#[must_use]
pub fn format_tick_num(x: f64) -> String {
    if !x.is_finite() {
        return "0".to_string();
    }
    if x.abs() < 1e-12 {
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

/// Truncate a label cleanly on UTF-8 character boundaries with an ellipsis.
#[must_use]
pub fn truncate_label(s: &str, max_chars: usize) -> String {
    let count = s.chars().count();
    if count <= max_chars || max_chars < 2 {
        return s.to_string();
    }
    let mut out: String = s.chars().take(max_chars - 1).collect();
    out.push('…');
    out
}

/// Extract numeric value from `Val`, also supporting `Date` (days) and `Timestamp` (micros)
/// when plotting temporal axes.
#[must_use]
pub fn val_to_axis_f64(v: &Val) -> Option<f64> {
    match v {
        Val::OptNone => None,
        Val::OptSome(inner) => val_to_axis_f64(inner),
        Val::Date(d) => Some(d.to_f64()),
        Val::Timestamp(ts) => Some(ts.to_f64()),
        other => unwrap_numeric_float(other),
    }
}

/// Look up a named series inside a [`ChartVal`].
#[must_use]
pub fn chart_series_by_name<'a>(chart: &'a ChartVal, name: &str) -> Option<&'a [Val]> {
    let idx = chart.col_names.iter().position(|c| c == name)?;
    chart.series.get(idx).map(Vec::as_slice)
}

/// Resolve `(x_name, x_series)` using explicit metadata or Core IR positional fallback.
#[must_use]
pub fn resolve_x_col(chart: &ChartVal) -> Option<(&str, &[Val])> {
    if let Some(name) = chart.x_col.as_deref() {
        return chart_series_by_name(chart, name).map(|s| (name, s));
    }
    let name = chart.col_names.first()?;
    chart.series.first().map(|s| (name.as_str(), s.as_slice()))
}

/// Resolve `(y_name, y_series)` using explicit metadata or Core IR positional fallback.
#[must_use]
pub fn resolve_y_col(chart: &ChartVal) -> Option<(&str, &[Val])> {
    if let Some(name) = chart.y_col.as_deref() {
        return chart_series_by_name(chart, name).map(|s| (name, s));
    }
    let name = chart.col_names.get(1)?;
    chart.series.get(1).map(|s| (name.as_str(), s.as_slice()))
}

/// Resolve optional `(color_name, color_series)`.
#[must_use]
pub fn resolve_color_col(chart: &ChartVal) -> Option<(&str, &[Val])> {
    if let Some(name) = chart.color_col.as_deref() {
        return chart_series_by_name(chart, name).map(|s| (name, s));
    }
    if chart.x_col.is_none() && chart.y_col.is_none() && chart.value_col.is_none() {
        let name = chart.col_names.get(2)?;
        return chart.series.get(2).map(|s| (name.as_str(), s.as_slice()));
    }
    None
}

/// Resolve `(value_name, value_series)` for heatmaps.
#[must_use]
pub fn resolve_value_col(chart: &ChartVal) -> Option<(&str, &[Val])> {
    if let Some(name) = chart.value_col.as_deref() {
        return chart_series_by_name(chart, name).map(|s| (name, s));
    }
    let name = chart.col_names.get(2)?;
    chart.series.get(2).map(|s| (name.as_str(), s.as_slice()))
}

/// Compute nice axis bounds `(nice_min, nice_max, ticks)` for a data range `[min_v, max_v]`.
#[must_use]
pub fn nice_axis(min_v: f64, max_v: f64, target_ticks: usize) -> (f64, f64, Vec<f64>) {
    let target = target_ticks.clamp(2, 12) as f64;
    if !min_v.is_finite() || !max_v.is_finite() {
        return (0.0, 1.0, vec![0.0, 0.5, 1.0]);
    }
    let (lo, hi) = if (max_v - min_v).abs() < 1e-12 {
        if min_v.abs() < 1e-12 {
            (0.0, 1.0)
        } else {
            let pad = (min_v.abs() * 0.2).max(1.0);
            (min_v - pad, max_v + pad)
        }
    } else if min_v < max_v {
        (min_v, max_v)
    } else {
        (max_v, min_v)
    };

    let raw_step = (hi - lo) / target;
    let mag = 10.0_f64.powf(raw_step.log10().floor());
    let norm = raw_step / mag;
    let nice_norm = if norm <= 1.0 {
        1.0
    } else if norm <= 2.0 {
        2.0
    } else if norm <= 2.5 {
        2.5
    } else if norm <= 5.0 {
        5.0
    } else {
        10.0
    };
    let step = nice_norm * mag;
    if !step.is_finite() || step <= 0.0 {
        return (lo, hi, vec![lo, hi]);
    }
    let nice_min = (lo / step).floor() * step;
    let nice_max = (hi / step).ceil() * step;
    let mut ticks = Vec::new();
    let mut cur = nice_min;
    for _ in 0..32 {
        if cur > nice_max + step * 0.25 {
            break;
        }
        ticks.push(if cur.abs() < step * 1e-9 { 0.0 } else { cur });
        cur += step;
    }
    if ticks.len() < 2 {
        ticks = vec![nice_min, nice_max];
    }
    (nice_min, nice_max, ticks)
}

/// Linearly map `val` from `[dom_min, dom_max]` into `[out_min, out_max]` safely (never `NaN`).
#[must_use]
pub fn map_linear(val: f64, dom_min: f64, dom_max: f64, out_min: f64, out_max: f64) -> f64 {
    let span = dom_max - dom_min;
    if !val.is_finite() || !span.is_finite() || span.abs() < 1e-15 {
        return safe_coord((out_min + out_max) * 0.5);
    }
    let t = (val - dom_min) / span;
    safe_coord(out_min + t * (out_max - out_min))
}
