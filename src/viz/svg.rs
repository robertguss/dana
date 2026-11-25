//! Zero-dependency standalone SVG chart renderer covering all 5 Dana `ChartKind`s:
//! `Bar`, `Line`, `Scatter` (with optional OLS trendline overlay), `Histogram`, and `Heatmap`.

use std::collections::HashMap;
use std::fmt::Write as _;

use crate::core::syntax::ChartKind;
use crate::oracle::value::{ChartVal, Val, unwrap_numeric_float, val_cmp};
use crate::viz::{
    PALETTE, fmt_coord, format_chart_val, format_tick_num, map_linear, nice_axis,
    resolve_color_col, resolve_value_col, resolve_x_col, resolve_y_col, truncate_label,
    val_to_axis_f64, xml_escape,
};

const WIDTH: f64 = 800.0;
const HEIGHT: f64 = 480.0;

/// Render a [`ChartVal`] into a self-contained `<svg xmlns="http://www.w3.org/2000/svg" ...>` string.
#[must_use]
pub fn render_chart_svg(chart: &ChartVal) -> String {
    match chart.kind {
        ChartKind::Bar => render_bar_svg(chart),
        ChartKind::Line => render_line_svg(chart),
        ChartKind::Scatter => render_scatter_svg(chart),
        ChartKind::Histogram => render_histogram_svg(chart),
        ChartKind::Heatmap => render_heatmap_svg(chart),
    }
}

fn svg_open(out: &mut String, title: &str) {
    let _ = writeln!(
        out,
        "<svg xmlns=\"http://www.w3.org/2000/svg\" viewBox=\"0 0 800 480\" width=\"800\" height=\"480\" role=\"img\" aria-label=\"{}\">",
        xml_escape(title)
    );
    out.push_str(
        "  <style>\n\
         \x20   text { font-family: -apple-system, BlinkMacSystemFont, \"Segoe UI\", Roboto, sans-serif; fill: #1f2937; }\n\
         \x20   .chart-title { font-size: 16px; font-weight: 600; fill: #111827; }\n\
         \x20   .axis-label { font-size: 12px; font-weight: 500; fill: #374151; }\n\
         \x20   .tick-label { font-size: 11px; fill: #4b5563; }\n\
         \x20   .legend-label { font-size: 11px; fill: #374151; }\n\
         \x20   .grid { stroke: #e5e7eb; stroke-width: 1; }\n\
         \x20   .axis { stroke: #9ca3af; stroke-width: 1.2; }\n\
         \x20   .trendline { stroke: #111827; stroke-width: 2; stroke-dasharray: 6,4; }\n\
         \x20 </style>\n",
    );
    out.push_str(
        "  <rect x=\"0\" y=\"0\" width=\"800\" height=\"480\" rx=\"8\" fill=\"#ffffff\" stroke=\"#e5e7eb\" stroke-width=\"1\" />\n",
    );
    if !title.is_empty() {
        let _ = writeln!(
            out,
            "  <text x=\"400\" y=\"30\" text-anchor=\"middle\" class=\"chart-title\">{}</text>",
            xml_escape(title)
        );
    }
}

fn render_empty_svg(title: &str, subtitle: &str) -> String {
    let mut out = String::new();
    svg_open(&mut out, title);
    let _ = writeln!(
        out,
        "  <text x=\"400\" y=\"245\" text-anchor=\"middle\" class=\"axis-label\">{}</text>",
        xml_escape(subtitle)
    );
    out.push_str("</svg>\n");
    out
}

fn render_legend(out: &mut String, labels: &[String], x_start: f64, y_start: f64) {
    let mut y = y_start;
    for (idx, lbl) in labels.iter().enumerate() {
        let color = PALETTE[idx % PALETTE.len()];
        let _ = writeln!(
            out,
            "  <rect x=\"{}\" y=\"{}\" width=\"11\" height=\"11\" rx=\"2\" fill=\"{color}\" />",
            fmt_coord(x_start),
            fmt_coord(y - 9.0)
        );
        let _ = writeln!(
            out,
            "  <text x=\"{}\" y=\"{}\" class=\"legend-label\">{}</text>",
            fmt_coord(x_start + 16.0),
            fmt_coord(y),
            xml_escape(&truncate_label(lbl, 16))
        );
        y += 18.0;
        if y > HEIGHT - 40.0 {
            break;
        }
    }
}

#[derive(Clone, Copy)]
struct PlotBox {
    left: f64,
    right: f64,
    top: f64,
    bottom: f64,
}

fn draw_y_axis(
    out: &mut String,
    area: PlotBox,
    y_min: f64,
    y_max: f64,
    ticks: &[f64],
    y_label: &str,
) {
    for &t in ticks {
        let py = map_linear(t, y_min, y_max, area.bottom, area.top);
        let _ = writeln!(
            out,
            "  <line x1=\"{}\" y1=\"{}\" x2=\"{}\" y2=\"{}\" class=\"grid\" />",
            fmt_coord(area.left),
            fmt_coord(py),
            fmt_coord(area.right),
            fmt_coord(py)
        );
        let _ = writeln!(
            out,
            "  <text x=\"{}\" y=\"{}\" text-anchor=\"end\" dominant-baseline=\"middle\" class=\"tick-label\">{}</text>",
            fmt_coord(area.left - 8.0),
            fmt_coord(py),
            xml_escape(&format_tick_num(t))
        );
    }
    let _ = writeln!(
        out,
        "  <line x1=\"{}\" y1=\"{}\" x2=\"{}\" y2=\"{}\" class=\"axis\" />",
        fmt_coord(area.left),
        fmt_coord(area.top),
        fmt_coord(area.left),
        fmt_coord(area.bottom)
    );
    let _ = writeln!(
        out,
        "  <line x1=\"{}\" y1=\"{}\" x2=\"{}\" y2=\"{}\" class=\"axis\" />",
        fmt_coord(area.left),
        fmt_coord(area.bottom),
        fmt_coord(area.right),
        fmt_coord(area.bottom)
    );
    if !y_label.is_empty() {
        let mid_y = (area.top + area.bottom) * 0.5;
        let _ = writeln!(
            out,
            "  <text x=\"20\" y=\"{}\" text-anchor=\"middle\" transform=\"rotate(-90 20 {})\" class=\"axis-label\">{}</text>",
            fmt_coord(mid_y),
            fmt_coord(mid_y),
            xml_escape(y_label)
        );
    }
}

fn draw_x_axis_label(out: &mut String, plot_l: f64, plot_r: f64, label: &str) {
    if !label.is_empty() {
        let _ = writeln!(
            out,
            "  <text x=\"{}\" y=\"{}\" text-anchor=\"middle\" class=\"axis-label\">{}</text>",
            fmt_coord((plot_l + plot_r) * 0.5),
            fmt_coord(HEIGHT - 14.0),
            xml_escape(label)
        );
    }
}

// ---------------------------------------------------------------------------
// 1. Bar Chart (Single & Grouped by Color)
// ---------------------------------------------------------------------------

fn render_bar_svg(chart: &ChartVal) -> String {
    let title = if chart.title.is_empty() {
        "Bar Chart"
    } else {
        chart.title.as_str()
    };
    let (Some((x_name, x_vals)), Some((y_name, y_vals))) =
        (resolve_x_col(chart), resolve_y_col(chart))
    else {
        return render_empty_svg(title, "No data available");
    };
    let color_col = resolve_color_col(chart);
    let n = x_vals.len().min(y_vals.len());
    if n == 0 {
        return render_empty_svg(title, "No data available");
    }

    let mut categories: Vec<String> = Vec::new();
    let mut series_names: Vec<String> = Vec::new();
    let mut values: HashMap<(usize, usize), f64> = HashMap::new();
    let mut y_min = 0.0_f64;
    let mut y_max = 0.0_f64;
    let mut has_point = false;

    for i in 0..n {
        let Some(yv) = unwrap_numeric_float(&y_vals[i]).filter(|v| v.is_finite()) else {
            continue;
        };
        let cat = format_chart_val(&x_vals[i]);
        let ci = if let Some(pos) = categories.iter().position(|c| c == &cat) {
            pos
        } else {
            categories.push(cat);
            categories.len() - 1
        };
        let sname = color_col
            .and_then(|(_, cs)| cs.get(i))
            .map_or_else(|| y_name.to_string(), format_chart_val);
        let si = if let Some(pos) = series_names.iter().position(|s| s == &sname) {
            pos
        } else {
            series_names.push(sname);
            series_names.len() - 1
        };
        values.insert((ci, si), yv);
        y_min = y_min.min(yv);
        y_max = y_max.max(yv);
        has_point = true;
    }

    if !has_point || categories.is_empty() {
        return render_empty_svg(title, "No numeric data available");
    }

    let show_legend = color_col.is_some() && !series_names.is_empty();
    let plot_l = 74.0;
    let plot_r = if show_legend {
        WIDTH - 145.0
    } else {
        WIDTH - 28.0
    };
    let plot_t = 54.0;
    let plot_b = HEIGHT - 76.0;
    let (dom_min, dom_max, ticks) = nice_axis(y_min, y_max, 5);
    let zero_y = map_linear(0.0, dom_min, dom_max, plot_b, plot_t).clamp(plot_t, plot_b);

    let mut out = String::new();
    svg_open(&mut out, title);
    draw_y_axis(
        &mut out,
        PlotBox {
            left: plot_l,
            right: plot_r,
            top: plot_t,
            bottom: plot_b,
        },
        dom_min,
        dom_max,
        &ticks,
        y_name,
    );

    let cat_count = categories.len();
    let ser_count = series_names.len().max(1);
    let group_w = (plot_r - plot_l) / (cat_count as f64);
    let inner_w = group_w * 0.76;
    let bar_w = (inner_w / (ser_count as f64)).max(2.0);
    let max_x_ticks = 12usize;
    let label_step = cat_count.div_ceil(max_x_ticks).max(1);

    for (ci, cat) in categories.iter().enumerate() {
        let group_x = plot_l + (ci as f64) * group_w + (group_w - inner_w) * 0.5;
        for (si, sname) in series_names.iter().enumerate() {
            if let Some(&yv) = values.get(&(ci, si)) {
                let bx = group_x + (si as f64) * bar_w;
                let py = map_linear(yv, dom_min, dom_max, plot_b, plot_t);
                let top = py.min(zero_y);
                let h = (py - zero_y).abs().max(1.0);
                let color = PALETTE[si % PALETTE.len()];
                let _ = writeln!(
                    out,
                    "  <rect x=\"{}\" y=\"{}\" width=\"{}\" height=\"{}\" rx=\"2\" fill=\"{color}\"><title>{} / {}: {}</title></rect>",
                    fmt_coord(bx),
                    fmt_coord(top),
                    fmt_coord((bar_w - 1.5).max(1.5)),
                    fmt_coord(h),
                    xml_escape(cat),
                    xml_escape(sname),
                    xml_escape(&format_tick_num(yv))
                );
            }
        }
        if ci % label_step == 0 {
            let cx = plot_l + ((ci as f64) + 0.5) * group_w;
            let _ = writeln!(
                out,
                "  <text x=\"{}\" y=\"{}\" text-anchor=\"middle\" class=\"tick-label\">{}</text>",
                fmt_coord(cx),
                fmt_coord(plot_b + 18.0),
                xml_escape(&truncate_label(cat, 14))
            );
        }
    }

    draw_x_axis_label(&mut out, plot_l, plot_r, x_name);
    if show_legend {
        render_legend(&mut out, &series_names, plot_r + 16.0, plot_t + 14.0);
    }
    out.push_str("</svg>\n");
    out
}

// ---------------------------------------------------------------------------
// 2. Line Chart (Numeric, Temporal, or Categorical X; Multi-Series by Color)
// ---------------------------------------------------------------------------

#[derive(Clone)]
struct LinePoint {
    x_num: f64,
    x_label: String,
    y_num: f64,
}

fn render_line_svg(chart: &ChartVal) -> String {
    let title = if chart.title.is_empty() {
        "Line Chart"
    } else {
        chart.title.as_str()
    };
    let (Some((x_name, x_vals)), Some((y_name, y_vals))) =
        (resolve_x_col(chart), resolve_y_col(chart))
    else {
        return render_empty_svg(title, "No data available");
    };
    let color_col = resolve_color_col(chart);
    let n = x_vals.len().min(y_vals.len());
    if n == 0 {
        return render_empty_svg(title, "No data available");
    }

    // Determine whether X is numeric/temporal or categorical.
    let mut all_x_numeric = true;
    let mut x_categories: Vec<String> = Vec::new();
    for v in &x_vals[..n] {
        if val_to_axis_f64(v).is_none() {
            all_x_numeric = false;
        }
        let lbl = format_chart_val(v);
        if !x_categories.contains(&lbl) {
            x_categories.push(lbl);
        }
    }

    let mut series_names: Vec<String> = Vec::new();
    let mut series_pts: Vec<Vec<LinePoint>> = Vec::new();
    let mut x_min = f64::INFINITY;
    let mut x_max = f64::NEG_INFINITY;
    let mut y_min = f64::INFINITY;
    let mut y_max = f64::NEG_INFINITY;

    for i in 0..n {
        let Some(yv) = unwrap_numeric_float(&y_vals[i]).filter(|v| v.is_finite()) else {
            continue;
        };
        let x_lbl = format_chart_val(&x_vals[i]);
        let xv = if all_x_numeric {
            match val_to_axis_f64(&x_vals[i]) {
                Some(v) if v.is_finite() => v,
                _ => continue,
            }
        } else {
            x_categories.iter().position(|c| c == &x_lbl).unwrap_or(0) as f64
        };
        let sname = color_col
            .and_then(|(_, cs)| cs.get(i))
            .map_or_else(|| y_name.to_string(), format_chart_val);
        let si = if let Some(pos) = series_names.iter().position(|s| s == &sname) {
            pos
        } else {
            series_names.push(sname);
            series_pts.push(Vec::new());
            series_names.len() - 1
        };
        x_min = x_min.min(xv);
        x_max = x_max.max(xv);
        y_min = y_min.min(yv);
        y_max = y_max.max(yv);
        series_pts[si].push(LinePoint {
            x_num: xv,
            x_label: x_lbl,
            y_num: yv,
        });
    }

    if series_pts.iter().all(Vec::is_empty) {
        return render_empty_svg(title, "No numeric data available");
    }

    let show_legend = color_col.is_some() && !series_names.is_empty();
    let plot_l = 74.0;
    let plot_r = if show_legend {
        WIDTH - 145.0
    } else {
        WIDTH - 28.0
    };
    let plot_t = 54.0;
    let plot_b = HEIGHT - 76.0;
    let (y_dom_min, y_dom_max, y_ticks) = nice_axis(y_min, y_max, 5);

    let mut out = String::new();
    svg_open(&mut out, title);
    draw_y_axis(
        &mut out,
        PlotBox {
            left: plot_l,
            right: plot_r,
            top: plot_t,
            bottom: plot_b,
        },
        y_dom_min,
        y_dom_max,
        &y_ticks,
        y_name,
    );

    // X axis ticks (using actual formatted labels for dates/timestamps/categories).
    let mut x_pairs: Vec<(f64, String)> = Vec::new();
    for pts in &series_pts {
        for pt in pts {
            if !x_pairs.iter().any(|(xv, _)| (*xv - pt.x_num).abs() < 1e-12) {
                x_pairs.push((pt.x_num, pt.x_label.clone()));
            }
        }
    }
    x_pairs.sort_by(|a, b| a.0.total_cmp(&b.0));
    let tick_step = x_pairs.len().div_ceil(6).max(1);
    for (idx, (xv, lbl)) in x_pairs.iter().enumerate() {
        if idx % tick_step == 0 || idx + 1 == x_pairs.len() {
            let px = map_linear(*xv, x_min, x_max, plot_l + 12.0, plot_r - 12.0);
            let _ = writeln!(
                out,
                "  <line x1=\"{}\" y1=\"{}\" x2=\"{}\" y2=\"{}\" class=\"grid\" />",
                fmt_coord(px),
                fmt_coord(plot_t),
                fmt_coord(px),
                fmt_coord(plot_b)
            );
            let _ = writeln!(
                out,
                "  <text x=\"{}\" y=\"{}\" text-anchor=\"middle\" class=\"tick-label\">{}</text>",
                fmt_coord(px),
                fmt_coord(plot_b + 18.0),
                xml_escape(&truncate_label(lbl, 14))
            );
        }
    }

    for (si, pts) in series_pts.iter().enumerate() {
        if pts.is_empty() {
            continue;
        }
        let color = PALETTE[si % PALETTE.len()];
        let mut poly = String::new();
        for (pi, pt) in pts.iter().enumerate() {
            let px = map_linear(pt.x_num, x_min, x_max, plot_l + 12.0, plot_r - 12.0);
            let py = map_linear(pt.y_num, y_dom_min, y_dom_max, plot_b, plot_t);
            if pi > 0 {
                poly.push(' ');
            }
            let _ = write!(poly, "{},{}", fmt_coord(px), fmt_coord(py));
        }
        if pts.len() >= 2 {
            let _ = writeln!(
                out,
                "  <polyline fill=\"none\" stroke=\"{color}\" stroke-width=\"2.2\" points=\"{poly}\" />"
            );
        }
        for pt in pts {
            let px = map_linear(pt.x_num, x_min, x_max, plot_l + 12.0, plot_r - 12.0);
            let py = map_linear(pt.y_num, y_dom_min, y_dom_max, plot_b, plot_t);
            let _ = writeln!(
                out,
                "  <circle cx=\"{}\" cy=\"{}\" r=\"3.5\" fill=\"{color}\"><title>{}: ({}, {})</title></circle>",
                fmt_coord(px),
                fmt_coord(py),
                xml_escape(&series_names[si]),
                xml_escape(&pt.x_label),
                xml_escape(&format_tick_num(pt.y_num))
            );
        }
    }

    draw_x_axis_label(&mut out, plot_l, plot_r, x_name);
    if show_legend {
        render_legend(&mut out, &series_names, plot_r + 16.0, plot_t + 14.0);
    }
    out.push_str("</svg>\n");
    out
}

// ---------------------------------------------------------------------------
// 3. Scatter Plot (with Optional OLS Trendline Overlay)
// ---------------------------------------------------------------------------

fn render_scatter_svg(chart: &ChartVal) -> String {
    let title = if chart.title.is_empty() {
        "Scatter Plot"
    } else {
        chart.title.as_str()
    };
    let (Some((x_name, x_vals)), Some((y_name, y_vals))) =
        (resolve_x_col(chart), resolve_y_col(chart))
    else {
        return render_empty_svg(title, "No data available");
    };
    let color_col = resolve_color_col(chart);
    let n = x_vals.len().min(y_vals.len());
    if n == 0 {
        return render_empty_svg(title, "No data available");
    }

    let mut groups: Vec<String> = Vec::new();
    let mut points: Vec<(f64, f64, usize)> = Vec::new();
    let mut x_min = f64::INFINITY;
    let mut x_max = f64::NEG_INFINITY;
    let mut y_min = f64::INFINITY;
    let mut y_max = f64::NEG_INFINITY;

    for i in 0..n {
        let (Some(xv), Some(yv)) = (
            unwrap_numeric_float(&x_vals[i]).filter(|v| v.is_finite()),
            unwrap_numeric_float(&y_vals[i]).filter(|v| v.is_finite()),
        ) else {
            continue;
        };
        let gname = color_col
            .and_then(|(_, cs)| cs.get(i))
            .map_or_else(|| "data".to_string(), format_chart_val);
        let gi = if let Some(pos) = groups.iter().position(|g| g == &gname) {
            pos
        } else {
            groups.push(gname);
            groups.len() - 1
        };
        x_min = x_min.min(xv);
        x_max = x_max.max(xv);
        y_min = y_min.min(yv);
        y_max = y_max.max(yv);
        points.push((xv, yv, gi));
    }

    if points.is_empty() {
        return render_empty_svg(title, "No numeric data available");
    }

    // Include trendline endpoints in Y domain when present.
    if let Some((slope, intercept, r2)) = chart.trendline
        && slope.is_finite()
        && intercept.is_finite()
        && r2.is_finite()
    {
        let ty1 = slope * x_min + intercept;
        let ty2 = slope * x_max + intercept;
        if ty1.is_finite() && ty2.is_finite() {
            y_min = y_min.min(ty1).min(ty2);
            y_max = y_max.max(ty1).max(ty2);
        }
    }

    let show_legend = color_col.is_some() && !groups.is_empty();
    let plot_l = 74.0;
    let plot_r = if show_legend {
        WIDTH - 145.0
    } else {
        WIDTH - 28.0
    };
    let plot_t = if chart.trendline.is_some() {
        64.0
    } else {
        54.0
    };
    let plot_b = HEIGHT - 72.0;
    let (x_dom_min, x_dom_max, x_ticks) = nice_axis(x_min, x_max, 6);
    let (y_dom_min, y_dom_max, y_ticks) = nice_axis(y_min, y_max, 5);

    let mut out = String::new();
    svg_open(&mut out, title);

    if let Some((slope, intercept, r2)) = chart.trendline
        && slope.is_finite()
        && intercept.is_finite()
        && r2.is_finite()
    {
        let sign = if intercept >= 0.0 { "+" } else { "-" };
        let eq = format!(
            "OLS: y = {:.4}x {sign} {:.3} (R² = {:.3})",
            slope,
            intercept.abs(),
            r2
        );
        let _ = writeln!(
            out,
            "  <text x=\"400\" y=\"48\" text-anchor=\"middle\" class=\"tick-label\">{}</text>",
            xml_escape(&eq)
        );
    }

    draw_y_axis(
        &mut out,
        PlotBox {
            left: plot_l,
            right: plot_r,
            top: plot_t,
            bottom: plot_b,
        },
        y_dom_min,
        y_dom_max,
        &y_ticks,
        y_name,
    );

    for &t in &x_ticks {
        let px = map_linear(t, x_dom_min, x_dom_max, plot_l, plot_r);
        let _ = writeln!(
            out,
            "  <line x1=\"{}\" y1=\"{}\" x2=\"{}\" y2=\"{}\" class=\"grid\" />",
            fmt_coord(px),
            fmt_coord(plot_t),
            fmt_coord(px),
            fmt_coord(plot_b)
        );
        let _ = writeln!(
            out,
            "  <text x=\"{}\" y=\"{}\" text-anchor=\"middle\" class=\"tick-label\">{}</text>",
            fmt_coord(px),
            fmt_coord(plot_b + 18.0),
            xml_escape(&format_tick_num(t))
        );
    }

    for &(xv, yv, gi) in &points {
        let px = map_linear(xv, x_dom_min, x_dom_max, plot_l, plot_r);
        let py = map_linear(yv, y_dom_min, y_dom_max, plot_b, plot_t);
        let color = PALETTE[gi % PALETTE.len()];
        let _ = writeln!(
            out,
            "  <circle cx=\"{}\" cy=\"{}\" r=\"4.5\" fill=\"{color}\" fill-opacity=\"0.82\"><title>{}: ({}, {})</title></circle>",
            fmt_coord(px),
            fmt_coord(py),
            xml_escape(&groups[gi]),
            xml_escape(&format_tick_num(xv)),
            xml_escape(&format_tick_num(yv))
        );
    }

    if let Some((slope, intercept, r2)) = chart.trendline
        && slope.is_finite()
        && intercept.is_finite()
        && r2.is_finite()
    {
        let lx1 = x_min;
        let lx2 = x_max;
        let ly1 = slope * lx1 + intercept;
        let ly2 = slope * lx2 + intercept;
        if ly1.is_finite() && ly2.is_finite() {
            let px1 = map_linear(lx1, x_dom_min, x_dom_max, plot_l, plot_r);
            let py1 = map_linear(ly1, y_dom_min, y_dom_max, plot_b, plot_t).clamp(plot_t, plot_b);
            let px2 = map_linear(lx2, x_dom_min, x_dom_max, plot_l, plot_r);
            let py2 = map_linear(ly2, y_dom_min, y_dom_max, plot_b, plot_t).clamp(plot_t, plot_b);
            let _ = writeln!(
                out,
                "  <line x1=\"{}\" y1=\"{}\" x2=\"{}\" y2=\"{}\" class=\"trendline\" />",
                fmt_coord(px1),
                fmt_coord(py1),
                fmt_coord(px2),
                fmt_coord(py2)
            );
        }
    }

    draw_x_axis_label(&mut out, plot_l, plot_r, x_name);
    if show_legend {
        render_legend(&mut out, &groups, plot_r + 16.0, plot_t + 14.0);
    }
    out.push_str("</svg>\n");
    out
}

// ---------------------------------------------------------------------------
// 4. Histogram (Sturges Default or Explicit Bins)
// ---------------------------------------------------------------------------

/// Compute histogram bin edges and counts `(edges, counts)` safely for finite values.
#[must_use]
pub fn compute_histogram_bins(
    vals: &[f64],
    requested_bins: Option<usize>,
) -> (Vec<f64>, Vec<usize>) {
    if vals.is_empty() {
        return (Vec::new(), Vec::new());
    }
    let min_v = vals.iter().copied().fold(f64::INFINITY, f64::min);
    let max_v = vals.iter().copied().fold(f64::NEG_INFINITY, f64::max);
    if !min_v.is_finite() || !max_v.is_finite() {
        return (Vec::new(), Vec::new());
    }
    let span = max_v - min_v;
    if span <= 0.0 {
        let half = (min_v.abs() * 0.1).max(0.5);
        return (vec![min_v - half, max_v + half], vec![vals.len()]);
    }
    let num_bins = requested_bins
        .unwrap_or_else(|| ((vals.len() as f64).log2().ceil() as usize + 1).clamp(1, 30))
        .clamp(1, 200);
    let step = span / (num_bins as f64);
    let mut edges = Vec::with_capacity(num_bins + 1);
    for i in 0..=num_bins {
        edges.push(min_v + (i as f64) * step);
    }
    let mut counts = vec![0usize; num_bins];
    for &x in vals {
        let b = (((x - min_v) / span) * (num_bins as f64)).floor() as usize;
        counts[b.min(num_bins - 1)] += 1;
    }
    (edges, counts)
}

fn render_histogram_svg(chart: &ChartVal) -> String {
    let title = if chart.title.is_empty() {
        "Histogram"
    } else {
        chart.title.as_str()
    };
    let Some((x_name, x_vals)) = resolve_x_col(chart).or_else(|| resolve_y_col(chart)) else {
        return render_empty_svg(title, "No data available");
    };
    let nums: Vec<f64> = x_vals
        .iter()
        .filter_map(unwrap_numeric_float)
        .filter(|v| v.is_finite())
        .collect();
    if nums.is_empty() {
        return render_empty_svg(title, "No numeric data available");
    }

    let (edges, counts) = compute_histogram_bins(&nums, chart.bins);
    if counts.is_empty() || edges.len() < 2 {
        return render_empty_svg(title, "No numeric data available");
    }
    let max_count = counts.iter().copied().max().unwrap_or(1) as f64;
    let (y_min, y_max, y_ticks) = nice_axis(0.0, max_count, 5);
    let plot_l = 74.0;
    let plot_r = WIDTH - 28.0;
    let plot_t = 54.0;
    let plot_b = HEIGHT - 72.0;

    let mut out = String::new();
    svg_open(&mut out, title);
    draw_y_axis(
        &mut out,
        PlotBox {
            left: plot_l,
            right: plot_r,
            top: plot_t,
            bottom: plot_b,
        },
        y_min,
        y_max,
        &y_ticks,
        "Count",
    );

    let dom_x_min = edges[0];
    let dom_x_max = edges[edges.len() - 1];
    for (i, &cnt) in counts.iter().enumerate() {
        let x0 = map_linear(edges[i], dom_x_min, dom_x_max, plot_l, plot_r);
        let x1 = map_linear(edges[i + 1], dom_x_min, dom_x_max, plot_l, plot_r);
        let py = map_linear(cnt as f64, y_min, y_max, plot_b, plot_t);
        let w = (x1 - x0 - 1.5).max(1.5);
        let h = (plot_b - py).max(0.0);
        let _ = writeln!(
            out,
            "  <rect x=\"{}\" y=\"{}\" width=\"{}\" height=\"{}\" rx=\"1\" fill=\"{}\"><title>[{}, {}]: {cnt}</title></rect>",
            fmt_coord(x0 + 0.75),
            fmt_coord(py),
            fmt_coord(w),
            fmt_coord(h),
            PALETTE[0],
            xml_escape(&format_tick_num(edges[i])),
            xml_escape(&format_tick_num(edges[i + 1]))
        );
    }

    let edge_step = edges.len().div_ceil(7).max(1);
    for (idx, &edge) in edges.iter().enumerate() {
        if idx % edge_step == 0 || idx + 1 == edges.len() {
            let px = map_linear(edge, dom_x_min, dom_x_max, plot_l, plot_r);
            let _ = writeln!(
                out,
                "  <text x=\"{}\" y=\"{}\" text-anchor=\"middle\" class=\"tick-label\">{}</text>",
                fmt_coord(px),
                fmt_coord(plot_b + 18.0),
                xml_escape(&format_tick_num(edge))
            );
        }
    }

    draw_x_axis_label(&mut out, plot_l, plot_r, x_name);
    out.push_str("</svg>\n");
    out
}

// ---------------------------------------------------------------------------
// 5. Heatmap (2D Grid + Color Ramp + Cell Labels + Color-Bar Legend)
// ---------------------------------------------------------------------------

fn heatmap_color(t: f64) -> (String, &'static str) {
    let t = if t.is_finite() {
        t.clamp(0.0, 1.0)
    } else {
        0.5
    };
    // Smooth 3-stop blue ramp: #eff6ff -> #3b82f6 -> #1e3a8a
    let (r, g, b) = if t < 0.5 {
        let u = t * 2.0;
        (
            239.0 + u * (59.0 - 239.0),
            246.0 + u * (130.0 - 246.0),
            255.0 + u * (246.0 - 255.0),
        )
    } else {
        let u = (t - 0.5) * 2.0;
        (
            59.0 + u * (30.0 - 59.0),
            130.0 + u * (58.0 - 130.0),
            246.0 + u * (138.0 - 246.0),
        )
    };
    let text_fill = if t > 0.55 { "#ffffff" } else { "#111827" };
    (
        format!(
            "#{:02x}{:02x}{:02x}",
            r.round().clamp(0.0, 255.0) as u8,
            g.round().clamp(0.0, 255.0) as u8,
            b.round().clamp(0.0, 255.0) as u8
        ),
        text_fill,
    )
}

fn sorted_unique_vals(vals: &[Val]) -> Vec<(Val, String)> {
    let mut uniq: Vec<Val> = Vec::new();
    for v in vals {
        if !uniq.iter().any(|u| crate::oracle::value::val_eq(u, v)) {
            uniq.push(v.clone());
        }
    }
    uniq.sort_by(val_cmp);
    uniq.into_iter()
        .map(|v| {
            let lbl = format_chart_val(&v);
            (v, lbl)
        })
        .collect()
}

fn render_heatmap_svg(chart: &ChartVal) -> String {
    let title = if chart.title.is_empty() {
        "Heatmap"
    } else {
        chart.title.as_str()
    };
    let (Some((x_name, x_vals)), Some((y_name, y_vals)), Some((v_name, v_vals))) = (
        resolve_x_col(chart),
        resolve_y_col(chart),
        resolve_value_col(chart),
    ) else {
        return render_empty_svg(title, "No data available");
    };
    let n = x_vals.len().min(y_vals.len()).min(v_vals.len());
    if n == 0 {
        return render_empty_svg(title, "No data available");
    }

    let x_cats = sorted_unique_vals(&x_vals[..n]);
    let y_cats = sorted_unique_vals(&y_vals[..n]);
    if x_cats.is_empty() || y_cats.is_empty() {
        return render_empty_svg(title, "No data available");
    }

    let mut grid: HashMap<(usize, usize), f64> = HashMap::new();
    let mut v_min = f64::INFINITY;
    let mut v_max = f64::NEG_INFINITY;
    for i in 0..n {
        let Some(vv) = unwrap_numeric_float(&v_vals[i]).filter(|v| v.is_finite()) else {
            continue;
        };
        let xi = x_cats
            .iter()
            .position(|(u, _)| crate::oracle::value::val_eq(u, &x_vals[i]));
        let yi = y_cats
            .iter()
            .position(|(u, _)| crate::oracle::value::val_eq(u, &y_vals[i]));
        if let (Some(xi), Some(yi)) = (xi, yi) {
            grid.insert((xi, yi), vv);
            v_min = v_min.min(vv);
            v_max = v_max.max(vv);
        }
    }
    if grid.is_empty() {
        return render_empty_svg(title, "No numeric heatmap values");
    }

    let plot_l = 104.0;
    let plot_r = WIDTH - 102.0;
    let plot_t = 56.0;
    let plot_b = HEIGHT - 72.0;
    let cell_w = (plot_r - plot_l) / (x_cats.len() as f64);
    let cell_h = (plot_b - plot_t) / (y_cats.len() as f64);
    let show_cell_text = cell_w >= 26.0 && cell_h >= 16.0;
    let span = v_max - v_min;

    let mut out = String::new();
    svg_open(&mut out, title);

    for (yi, (_, y_lbl)) in y_cats.iter().enumerate() {
        let py = plot_t + (yi as f64) * cell_h;
        for (xi, (_, x_lbl)) in x_cats.iter().enumerate() {
            let px = plot_l + (xi as f64) * cell_w;
            if let Some(&vv) = grid.get(&(xi, yi)) {
                let t = if span.abs() < 1e-12 {
                    0.5
                } else {
                    (vv - v_min) / span
                };
                let (bg, fg) = heatmap_color(t);
                let _ = writeln!(
                    out,
                    "  <rect x=\"{}\" y=\"{}\" width=\"{}\" height=\"{}\" fill=\"{bg}\" stroke=\"#ffffff\" stroke-width=\"1\"><title>{} x {}: {}</title></rect>",
                    fmt_coord(px),
                    fmt_coord(py),
                    fmt_coord(cell_w),
                    fmt_coord(cell_h),
                    xml_escape(y_lbl),
                    xml_escape(x_lbl),
                    xml_escape(&format_tick_num(vv))
                );
                if show_cell_text {
                    let _ = writeln!(
                        out,
                        "  <text x=\"{}\" y=\"{}\" text-anchor=\"middle\" dominant-baseline=\"middle\" font-size=\"10\" fill=\"{fg}\">{}</text>",
                        fmt_coord(px + cell_w * 0.5),
                        fmt_coord(py + cell_h * 0.5),
                        xml_escape(&format_tick_num(vv))
                    );
                }
            } else {
                let _ = writeln!(
                    out,
                    "  <rect x=\"{}\" y=\"{}\" width=\"{}\" height=\"{}\" fill=\"#f3f4f6\" stroke=\"#ffffff\" stroke-width=\"1\" />",
                    fmt_coord(px),
                    fmt_coord(py),
                    fmt_coord(cell_w),
                    fmt_coord(cell_h)
                );
            }
        }
        let _ = writeln!(
            out,
            "  <text x=\"{}\" y=\"{}\" text-anchor=\"end\" dominant-baseline=\"middle\" class=\"tick-label\">{}</text>",
            fmt_coord(plot_l - 8.0),
            fmt_coord(py + cell_h * 0.5),
            xml_escape(&truncate_label(y_lbl, 12))
        );
    }

    let x_step = x_cats.len().div_ceil(14).max(1);
    for (xi, (_, x_lbl)) in x_cats.iter().enumerate() {
        if xi % x_step == 0 {
            let cx = plot_l + ((xi as f64) + 0.5) * cell_w;
            let _ = writeln!(
                out,
                "  <text x=\"{}\" y=\"{}\" text-anchor=\"middle\" class=\"tick-label\">{}</text>",
                fmt_coord(cx),
                fmt_coord(plot_b + 18.0),
                xml_escape(&truncate_label(x_lbl, 10))
            );
        }
    }

    // Color-bar legend on the right.
    let bar_x = plot_r + 20.0;
    let bar_w = 16.0;
    let steps = 24usize;
    let seg_h = (plot_b - plot_t) / (steps as f64);
    for s in 0..steps {
        let t = 1.0 - (s as f64) / ((steps - 1) as f64);
        let (bg, _) = heatmap_color(t);
        let _ = writeln!(
            out,
            "  <rect x=\"{}\" y=\"{}\" width=\"{}\" height=\"{}\" fill=\"{bg}\" />",
            fmt_coord(bar_x),
            fmt_coord(plot_t + (s as f64) * seg_h),
            fmt_coord(bar_w),
            fmt_coord(seg_h + 0.5)
        );
    }
    let _ = writeln!(
        out,
        "  <rect x=\"{}\" y=\"{}\" width=\"{}\" height=\"{}\" fill=\"none\" stroke=\"#9ca3af\" stroke-width=\"1\" />",
        fmt_coord(bar_x),
        fmt_coord(plot_t),
        fmt_coord(bar_w),
        fmt_coord(plot_b - plot_t)
    );
    let _ = writeln!(
        out,
        "  <text x=\"{}\" y=\"{}\" class=\"tick-label\">{}</text>",
        fmt_coord(bar_x + bar_w + 6.0),
        fmt_coord(plot_t + 9.0),
        xml_escape(&format_tick_num(v_max))
    );
    let _ = writeln!(
        out,
        "  <text x=\"{}\" y=\"{}\" class=\"tick-label\">{}</text>",
        fmt_coord(bar_x + bar_w + 6.0),
        fmt_coord(plot_b),
        xml_escape(&format_tick_num(v_min))
    );
    let _ = writeln!(
        out,
        "  <text x=\"{}\" y=\"{}\" class=\"legend-label\">{}</text>",
        fmt_coord(bar_x),
        fmt_coord(plot_t - 10.0),
        xml_escape(&truncate_label(v_name, 12))
    );

    draw_x_axis_label(&mut out, plot_l, plot_r, x_name);
    let mid_y = (plot_t + plot_b) * 0.5;
    let _ = writeln!(
        out,
        "  <text x=\"18\" y=\"{}\" text-anchor=\"middle\" transform=\"rotate(-90 18 {})\" class=\"axis-label\">{}</text>",
        fmt_coord(mid_y),
        fmt_coord(mid_y),
        xml_escape(y_name)
    );
    out.push_str("</svg>\n");
    out
}
