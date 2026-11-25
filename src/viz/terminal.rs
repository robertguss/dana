//! Zero-dependency Unicode terminal chart renderer covering all 5 Dana `ChartKind`s,
//! wired into `console.print_chart(chart)`.

use std::collections::HashMap;
use std::fmt::Write as _;

use crate::core::syntax::ChartKind;
use crate::oracle::value::{ChartVal, Val, unwrap_numeric_float, val_cmp, val_eq};
use crate::viz::svg::compute_histogram_bins;
use crate::viz::{
    format_chart_val, format_tick_num, resolve_color_col, resolve_value_col, resolve_x_col,
    resolve_y_col, truncate_label, val_to_axis_f64,
};

const SERIES_GLYPHS: [char; 6] = ['●', '◆', '▲', '■', '★', '✦'];
const HEAT_SHADES: [char; 4] = ['░', '▒', '▓', '█'];

/// Render a [`ChartVal`] as a clean Unicode terminal chart.
#[must_use]
pub fn render_chart_terminal(chart: &ChartVal) -> String {
    match chart.kind {
        ChartKind::Bar => render_bar_terminal(chart),
        ChartKind::Line => render_line_terminal(chart),
        ChartKind::Scatter => render_scatter_terminal(chart),
        ChartKind::Histogram => render_histogram_terminal(chart),
        ChartKind::Heatmap => render_heatmap_terminal(chart),
    }
}

fn bar_blocks(ratio: f64, width: usize) -> String {
    const PARTIALS: [char; 8] = [' ', '▏', '▎', '▍', '▌', '▋', '▊', '▉'];
    let clamped = if ratio.is_finite() {
        ratio.clamp(0.0, 1.0)
    } else {
        0.0
    };
    let eighths = (clamped * ((width * 8) as f64)).round() as usize;
    let full = eighths / 8;
    let rem = eighths % 8;
    let mut s = String::with_capacity(width * 3);
    for _ in 0..full {
        s.push('█');
    }
    if rem > 0 && full < width {
        s.push(PARTIALS[rem]);
    }
    if s.is_empty() && clamped > 0.0 {
        s.push('▏');
    }
    s
}

fn render_bar_terminal(chart: &ChartVal) -> String {
    let title = if chart.title.is_empty() {
        "Bar Chart"
    } else {
        chart.title.as_str()
    };
    let mut out = format!("=== {title} [Bar] ===\n");
    let (Some((_, x_vals)), Some((_, y_vals))) = (resolve_x_col(chart), resolve_y_col(chart))
    else {
        out.push_str("(no data)");
        return out;
    };
    let color_col = resolve_color_col(chart);
    let n = x_vals.len().min(y_vals.len());
    let mut entries: Vec<(String, f64)> = Vec::new();
    let mut max_abs = 0.0_f64;
    for i in 0..n {
        let Some(yv) = unwrap_numeric_float(&y_vals[i]).filter(|v| v.is_finite()) else {
            continue;
        };
        let label = match color_col.and_then(|(_, cs)| cs.get(i)) {
            Some(c) => format!("{} [{}]", format_chart_val(&x_vals[i]), format_chart_val(c)),
            None => format_chart_val(&x_vals[i]),
        };
        max_abs = max_abs.max(yv.abs());
        entries.push((truncate_label(&label, 28), yv));
    }
    if entries.is_empty() {
        out.push_str("(no numeric data)");
        return out;
    }
    let lbl_w = entries
        .iter()
        .map(|(l, _)| l.chars().count())
        .max()
        .unwrap_or(4);
    for (lbl, yv) in entries {
        let ratio = if max_abs > 0.0 {
            yv.abs() / max_abs
        } else {
            0.0
        };
        let bar = bar_blocks(ratio, 36);
        let pad = lbl_w.saturating_sub(lbl.chars().count());
        let _ = writeln!(
            out,
            "{lbl}{} │ {bar:<36} {}",
            " ".repeat(pad),
            format_tick_num(yv)
        );
    }
    out.trim_end_matches('\n').to_string()
}

fn render_xy_grid_terminal(
    title: &str,
    kind_label: &str,
    points: &[(f64, f64, usize)],
    groups: &[String],
    x_first_lbl: &str,
    x_last_lbl: &str,
    trendline: Option<(f64, f64, f64)>,
) -> String {
    const ROWS: usize = 12;
    const COLS: usize = 52;
    let mut out = format!("=== {title} [{kind_label}] ===\n");
    if points.is_empty() {
        out.push_str("(no numeric data)");
        return out;
    }

    let mut x_min = f64::INFINITY;
    let mut x_max = f64::NEG_INFINITY;
    let mut y_min = f64::INFINITY;
    let mut y_max = f64::NEG_INFINITY;
    for &(x, y, _) in points {
        x_min = x_min.min(x);
        x_max = x_max.max(x);
        y_min = y_min.min(y);
        y_max = y_max.max(y);
    }

    let mut grid = vec![vec![' '; COLS]; ROWS];
    let x_span = x_max - x_min;
    let y_span = y_max - y_min;
    for &(x, y, gi) in points {
        let cx = if x_span.abs() < 1e-12 {
            COLS / 2
        } else {
            (((x - x_min) / x_span) * ((COLS - 1) as f64))
                .round()
                .clamp(0.0, (COLS - 1) as f64) as usize
        };
        let cy_inv = if y_span.abs() < 1e-12 {
            ROWS / 2
        } else {
            (((y - y_min) / y_span) * ((ROWS - 1) as f64))
                .round()
                .clamp(0.0, (ROWS - 1) as f64) as usize
        };
        let r = (ROWS - 1).saturating_sub(cy_inv);
        grid[r][cx] = SERIES_GLYPHS[gi % SERIES_GLYPHS.len()];
    }

    let y_max_s = format_tick_num(y_max);
    let y_min_s = format_tick_num(y_min);
    let y_w = y_max_s.len().max(y_min_s.len()).max(6);
    for (ri, row) in grid.iter().enumerate() {
        let prefix = if ri == 0 {
            format!("{y_max_s:>y_w$}")
        } else if ri + 1 == ROWS {
            format!("{y_min_s:>y_w$}")
        } else {
            " ".repeat(y_w)
        };
        let line: String = row.iter().collect();
        let _ = writeln!(out, "{prefix} │{line}");
    }
    let _ = writeln!(out, "{} └{}", " ".repeat(y_w), "─".repeat(COLS));
    let left = truncate_label(x_first_lbl, 22);
    let right = truncate_label(x_last_lbl, 22);
    let gap = COLS.saturating_sub(left.chars().count() + right.chars().count());
    let _ = writeln!(out, "{}  {left}{}{right}", " ".repeat(y_w), " ".repeat(gap));

    if !groups.is_empty() {
        let legend: Vec<String> = groups
            .iter()
            .enumerate()
            .map(|(i, g)| format!("{} {g}", SERIES_GLYPHS[i % SERIES_GLYPHS.len()]))
            .collect();
        let _ = writeln!(out, "Legend: {}", legend.join("   "));
    }
    if let Some((slope, intercept, r2)) = trendline
        && slope.is_finite()
        && intercept.is_finite()
        && r2.is_finite()
    {
        let sign = if intercept >= 0.0 { "+" } else { "-" };
        let _ = writeln!(
            out,
            "OLS: y = {:.4}x {sign} {:.3} (R² = {:.3})",
            slope,
            intercept.abs(),
            r2
        );
    }
    out.trim_end_matches('\n').to_string()
}

fn render_line_terminal(chart: &ChartVal) -> String {
    let title = if chart.title.is_empty() {
        "Line Chart"
    } else {
        chart.title.as_str()
    };
    let (Some((_, x_vals)), Some((y_name, y_vals))) = (resolve_x_col(chart), resolve_y_col(chart))
    else {
        return format!("=== {title} [Line] ===\n(no data)");
    };
    let color_col = resolve_color_col(chart);
    let n = x_vals.len().min(y_vals.len());
    let all_x_num = x_vals[..n].iter().all(|v| val_to_axis_f64(v).is_some());
    let mut x_cats: Vec<String> = Vec::new();
    let mut groups: Vec<String> = Vec::new();
    let mut pts: Vec<(f64, f64, usize)> = Vec::new();
    let mut x_labels: Vec<(f64, String)> = Vec::new();

    for i in 0..n {
        let Some(yv) = unwrap_numeric_float(&y_vals[i]).filter(|v| v.is_finite()) else {
            continue;
        };
        let xl = format_chart_val(&x_vals[i]);
        let xv = if all_x_num {
            match val_to_axis_f64(&x_vals[i]) {
                Some(v) if v.is_finite() => v,
                _ => continue,
            }
        } else {
            if let Some(pos) = x_cats.iter().position(|c| c == &xl) {
                pos as f64
            } else {
                x_cats.push(xl.clone());
                (x_cats.len() - 1) as f64
            }
        };
        let g = color_col
            .and_then(|(_, cs)| cs.get(i))
            .map_or_else(|| y_name.to_string(), format_chart_val);
        let gi = if let Some(pos) = groups.iter().position(|s| s == &g) {
            pos
        } else {
            groups.push(g);
            groups.len() - 1
        };
        pts.push((xv, yv, gi));
        x_labels.push((xv, xl));
    }
    x_labels.sort_by(|a, b| a.0.total_cmp(&b.0));
    let first_l = x_labels.first().map_or("", |(_, s)| s.as_str());
    let last_l = x_labels.last().map_or("", |(_, s)| s.as_str());
    render_xy_grid_terminal(title, "Line", &pts, &groups, first_l, last_l, None)
}

fn render_scatter_terminal(chart: &ChartVal) -> String {
    let title = if chart.title.is_empty() {
        "Scatter Plot"
    } else {
        chart.title.as_str()
    };
    let (Some((_, x_vals)), Some((_, y_vals))) = (resolve_x_col(chart), resolve_y_col(chart))
    else {
        return format!("=== {title} [Scatter] ===\n(no data)");
    };
    let color_col = resolve_color_col(chart);
    let n = x_vals.len().min(y_vals.len());
    let mut groups: Vec<String> = Vec::new();
    let mut pts: Vec<(f64, f64, usize)> = Vec::new();
    let mut x_min = f64::INFINITY;
    let mut x_max = f64::NEG_INFINITY;

    for i in 0..n {
        let (Some(xv), Some(yv)) = (
            unwrap_numeric_float(&x_vals[i]).filter(|v| v.is_finite()),
            unwrap_numeric_float(&y_vals[i]).filter(|v| v.is_finite()),
        ) else {
            continue;
        };
        let g = color_col
            .and_then(|(_, cs)| cs.get(i))
            .map_or_else(|| "data".to_string(), format_chart_val);
        let gi = if let Some(pos) = groups.iter().position(|s| s == &g) {
            pos
        } else {
            groups.push(g);
            groups.len() - 1
        };
        x_min = x_min.min(xv);
        x_max = x_max.max(xv);
        pts.push((xv, yv, gi));
    }
    let first_l = if x_min.is_finite() {
        format_tick_num(x_min)
    } else {
        String::new()
    };
    let last_l = if x_max.is_finite() {
        format_tick_num(x_max)
    } else {
        String::new()
    };
    render_xy_grid_terminal(
        title,
        "Scatter",
        &pts,
        &groups,
        &first_l,
        &last_l,
        chart.trendline,
    )
}

fn render_histogram_terminal(chart: &ChartVal) -> String {
    let title = if chart.title.is_empty() {
        "Histogram"
    } else {
        chart.title.as_str()
    };
    let mut out = format!("=== {title} [Histogram] ===\n");
    let Some((_, x_vals)) = resolve_x_col(chart).or_else(|| resolve_y_col(chart)) else {
        out.push_str("(no data)");
        return out;
    };
    let nums: Vec<f64> = x_vals
        .iter()
        .filter_map(unwrap_numeric_float)
        .filter(|v| v.is_finite())
        .collect();
    let (edges, counts) = compute_histogram_bins(&nums, chart.bins);
    if counts.is_empty() || edges.len() < 2 {
        out.push_str("(no numeric data)");
        return out;
    }
    let max_c = counts.iter().copied().max().unwrap_or(1) as f64;
    let labels: Vec<String> = (0..counts.len())
        .map(|i| {
            format!(
                "[{}, {}]",
                format_tick_num(edges[i]),
                format_tick_num(edges[i + 1])
            )
        })
        .collect();
    let lbl_w = labels.iter().map(|s| s.chars().count()).max().unwrap_or(8);
    for (lbl, &cnt) in labels.iter().zip(&counts) {
        let bar = bar_blocks((cnt as f64) / max_c, 36);
        let pad = lbl_w.saturating_sub(lbl.chars().count());
        let _ = writeln!(out, "{lbl}{} │ {bar:<36} {cnt}", " ".repeat(pad));
    }
    out.trim_end_matches('\n').to_string()
}

fn render_heatmap_terminal(chart: &ChartVal) -> String {
    let title = if chart.title.is_empty() {
        "Heatmap"
    } else {
        chart.title.as_str()
    };
    let mut out = format!("=== {title} [Heatmap] ===\n");
    let (Some((_, x_vals)), Some((_, y_vals)), Some((_, v_vals))) = (
        resolve_x_col(chart),
        resolve_y_col(chart),
        resolve_value_col(chart),
    ) else {
        out.push_str("(no data)");
        return out;
    };
    let n = x_vals.len().min(y_vals.len()).min(v_vals.len());
    if n == 0 {
        out.push_str("(no data)");
        return out;
    }
    let mut x_cats: Vec<Val> = Vec::new();
    let mut y_cats: Vec<Val> = Vec::new();
    for v in &x_vals[..n] {
        if !x_cats.iter().any(|u| val_eq(u, v)) {
            x_cats.push(v.clone());
        }
    }
    for v in &y_vals[..n] {
        if !y_cats.iter().any(|u| val_eq(u, v)) {
            y_cats.push(v.clone());
        }
    }
    x_cats.sort_by(val_cmp);
    y_cats.sort_by(val_cmp);

    let mut grid: HashMap<(usize, usize), f64> = HashMap::new();
    let mut v_min = f64::INFINITY;
    let mut v_max = f64::NEG_INFINITY;
    for i in 0..n {
        if let Some(vv) = unwrap_numeric_float(&v_vals[i]).filter(|v| v.is_finite())
            && let (Some(xi), Some(yi)) = (
                x_cats.iter().position(|u| val_eq(u, &x_vals[i])),
                y_cats.iter().position(|u| val_eq(u, &y_vals[i])),
            )
        {
            grid.insert((xi, yi), vv);
            v_min = v_min.min(vv);
            v_max = v_max.max(vv);
        }
    }
    if grid.is_empty() {
        out.push_str("(no numeric data)");
        return out;
    }
    let y_labels: Vec<String> = y_cats
        .iter()
        .map(|v| truncate_label(&format_chart_val(v), 12))
        .collect();
    let x_labels: Vec<String> = x_cats
        .iter()
        .map(|v| truncate_label(&format_chart_val(v), 8))
        .collect();
    let y_w = y_labels
        .iter()
        .map(|s| s.chars().count())
        .max()
        .unwrap_or(6);
    let _ = write!(out, "{} │", " ".repeat(y_w));
    for xl in &x_labels {
        let _ = write!(out, " {xl:>8}");
    }
    out.push('\n');
    let span = v_max - v_min;
    for (yi, yl) in y_labels.iter().enumerate() {
        let pad = y_w.saturating_sub(yl.chars().count());
        let _ = write!(out, "{yl}{} │", " ".repeat(pad));
        for xi in 0..x_labels.len() {
            if let Some(&vv) = grid.get(&(xi, yi)) {
                let t = if span.abs() < 1e-12 {
                    0.5
                } else {
                    ((vv - v_min) / span).clamp(0.0, 1.0)
                };
                let shade = HEAT_SHADES[((t * 3.0).round() as usize).min(3)];
                let cell = format!("{shade}{}", format_tick_num(vv));
                let _ = write!(out, " {cell:>8}");
            } else {
                out.push_str("        -");
            }
        }
        out.push('\n');
    }
    out.trim_end_matches('\n').to_string()
}
