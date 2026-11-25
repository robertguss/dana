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
use std::hash::BuildHasherDefault;

use crate::core::bigint::DEC_SCALE;
use crate::core::syntax::{ColSpec, Float64, Ident, ScalarTy, TagSet};
use crate::formats::time::{format_iso_date, format_iso_timestamp};
use crate::oracle::value::{
    ProfileColSummary, ProfileVal, TableVal, Val, float_order_key, render_decimal,
    render_decimal_i128_into, render_public_val, unwrap_numeric_float, val_lt,
};
use crate::stats::{mean_f64, quantile_sorted, sample_stddev};
use crate::vm::batch::{Batch, ColumnData};
use crate::vm::key::{FastHasher, SingleKey};
use crate::vm::ops::VmTable;

type FastMap<K, V> = HashMap<K, V, BuildHasherDefault<FastHasher>>;
type FastSet<K> = HashSet<K, BuildHasherDefault<FastHasher>>;

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

// ---------------------------------------------------------------------------
// Direct Columnar Profiler over `&VmTable` (Zero `TableVal` Materialization)
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, PartialEq, Eq)]
enum UniformColKind {
    Bool,
    Int,
    Decimal,
    Float,
    Text,
    Date,
    Timestamp,
    Duration,
    Mixed,
}

fn detect_uniform_col_kind(batches: &[Batch], col_idx: usize) -> UniformColKind {
    let mut found: Option<UniformColKind> = None;
    for b in batches {
        if b.is_empty() {
            continue;
        }
        let k = match &b.cols[col_idx].data {
            ColumnData::Bool(_) => UniformColKind::Bool,
            ColumnData::Int(_) => UniformColKind::Int,
            ColumnData::Decimal(_) => UniformColKind::Decimal,
            ColumnData::Float(_) => UniformColKind::Float,
            ColumnData::Text { .. } => UniformColKind::Text,
            ColumnData::Date(_) => UniformColKind::Date,
            ColumnData::Timestamp(_) => UniformColKind::Timestamp,
            ColumnData::Duration(_) => UniformColKind::Duration,
            ColumnData::Unit(_) | ColumnData::Bytes { .. } | ColumnData::Generic(_) => {
                return UniformColKind::Mixed;
            }
        };
        match found {
            None => found = Some(k),
            Some(prev) if prev == k => {}
            Some(_) => return UniformColKind::Mixed,
        }
    }
    found.unwrap_or(UniformColKind::Mixed)
}

#[inline]
fn count_distinct_sorted<T: PartialEq>(sorted: &[T]) -> usize {
    if sorted.is_empty() {
        return 0;
    }
    let mut distinct = 1usize;
    for w in sorted.windows(2) {
        if w[0] != w[1] {
            distinct += 1;
        }
    }
    distinct
}

fn count_nulls_and_distinct_vm_col(
    batches: &[Batch],
    col_idx: usize,
    kind: UniformColKind,
    total_rows: usize,
) -> (usize, usize) {
    let mut null_count = 0usize;
    match kind {
        UniformColKind::Bool => {
            let mut saw_false = false;
            let mut saw_true = false;
            for b in batches {
                let c = &b.cols[col_idx];
                if let ColumnData::Bool(vs) = &c.data {
                    for &r_u16 in &b.active_indices() {
                        let r = usize::from(r_u16);
                        if c.validity.as_ref().is_some_and(|bm| !bm.is_valid(r)) {
                            null_count += 1;
                        } else if vs[r] != 0 {
                            saw_true = true;
                        } else {
                            saw_false = true;
                        }
                    }
                }
            }
            (null_count, usize::from(saw_false) + usize::from(saw_true))
        }
        UniformColKind::Int
        | UniformColKind::Date
        | UniformColKind::Timestamp
        | UniformColKind::Duration => {
            let mut vals = Vec::with_capacity(total_rows);
            for b in batches {
                let c = &b.cols[col_idx];
                let slice: &[i64] = match &c.data {
                    ColumnData::Int(v)
                    | ColumnData::Date(v)
                    | ColumnData::Timestamp(v)
                    | ColumnData::Duration(v) => v,
                    _ => continue,
                };
                for &r_u16 in &b.active_indices() {
                    let r = usize::from(r_u16);
                    if c.validity.as_ref().is_some_and(|bm| !bm.is_valid(r)) {
                        null_count += 1;
                    } else {
                        vals.push(slice[r]);
                    }
                }
            }
            vals.sort_unstable();
            (null_count, count_distinct_sorted(&vals))
        }
        UniformColKind::Decimal => {
            let mut vals = Vec::with_capacity(total_rows);
            for b in batches {
                let c = &b.cols[col_idx];
                if let ColumnData::Decimal(vs) = &c.data {
                    for &r_u16 in &b.active_indices() {
                        let r = usize::from(r_u16);
                        if c.validity.as_ref().is_some_and(|bm| !bm.is_valid(r)) {
                            null_count += 1;
                        } else {
                            vals.push(vs[r]);
                        }
                    }
                }
            }
            vals.sort_unstable();
            (null_count, count_distinct_sorted(&vals))
        }
        UniformColKind::Float => {
            let mut vals = Vec::with_capacity(total_rows);
            for b in batches {
                let c = &b.cols[col_idx];
                if let ColumnData::Float(vs) = &c.data {
                    for &r_u16 in &b.active_indices() {
                        let r = usize::from(r_u16);
                        if c.validity.as_ref().is_some_and(|bm| !bm.is_valid(r)) {
                            null_count += 1;
                        } else {
                            vals.push(vs[r]);
                        }
                    }
                }
            }
            vals.sort_unstable();
            (null_count, count_distinct_sorted(&vals))
        }
        UniformColKind::Text => {
            let mut set: FastSet<&[u8]> = FastSet::default();
            for b in batches {
                let c = &b.cols[col_idx];
                if let ColumnData::Text { offsets, data } = &c.data {
                    for &r_u16 in &b.active_indices() {
                        let r = usize::from(r_u16);
                        if c.validity.as_ref().is_some_and(|bm| !bm.is_valid(r)) {
                            null_count += 1;
                        } else {
                            set.insert(&data[offsets[r]..offsets[r + 1]]);
                        }
                    }
                }
            }
            (null_count, set.len())
        }
        UniformColKind::Mixed => {
            let mut set: FastSet<SingleKey> = FastSet::default();
            for b in batches {
                let c = &b.cols[col_idx];
                for &r_u16 in &b.active_indices() {
                    let v = c.get_val(usize::from(r_u16));
                    match &v {
                        Val::OptNone => null_count += 1,
                        Val::OptSome(inner) => {
                            set.insert(SingleKey::new(inner.as_ref().clone()));
                        }
                        other => {
                            set.insert(SingleKey::new(other.clone()));
                        }
                    }
                }
            }
            (null_count, set.len())
        }
    }
}

fn profile_single_vm_col(
    batches: &[Batch],
    col_idx: usize,
    c: &ColSpec,
    total_rows: usize,
    table_row_tags: &TagSet,
    static_col_tags: &[(Ident, TagSet)],
) -> ProfileColSummary {
    let mut eff_tags = c.tags.union(table_row_tags);
    if let Some((_, st)) = static_col_tags.iter().find(|(name, _)| name == &c.name) {
        eff_tags = eff_tags.union(st);
    }

    let kind = detect_uniform_col_kind(batches, col_idx);

    if !eff_tags.is_empty() {
        let (null_count, distinct_count) =
            count_nulls_and_distinct_vm_col(batches, col_idx, kind, total_rows);
        let null_pct = if total_rows == 0 {
            0.0
        } else {
            (null_count as f64) * 100.0 / (total_rows as f64)
        };
        let mut tags_vec: Vec<String> = eff_tags.elems().to_vec();
        tags_vec.sort();
        tags_vec.dedup();
        let marker = format!("[REDACTED:{}]", tags_vec.join(","));
        return ProfileColSummary {
            col_name: c.name.clone(),
            ty_name: format_scalar_ty_name(&c.ty),
            row_count: total_rows,
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
        };
    }

    // Public column: match `profile_table` branch selection (`is_numeric_scalar_ty(&c.ty)`) 100%.
    let mut null_count = 0usize;
    let distinct_count;
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
        let mut nums: Vec<f64> = Vec::with_capacity(total_rows);
        match kind {
            UniformColKind::Int => {
                let mut raw = Vec::with_capacity(total_rows);
                for b in batches {
                    let col = &b.cols[col_idx];
                    if let ColumnData::Int(vs) = &col.data {
                        for &r_u16 in &b.active_indices() {
                            let r = usize::from(r_u16);
                            if col.validity.as_ref().is_some_and(|bm| !bm.is_valid(r)) {
                                null_count += 1;
                            } else {
                                raw.push(vs[r]);
                            }
                        }
                    }
                }
                raw.sort_unstable();
                distinct_count = count_distinct_sorted(&raw);
                nums.extend(raw.into_iter().map(|x| x as f64));
            }
            UniformColKind::Decimal => {
                let mut raw = Vec::with_capacity(total_rows);
                for b in batches {
                    let col = &b.cols[col_idx];
                    if let ColumnData::Decimal(vs) = &col.data {
                        for &r_u16 in &b.active_indices() {
                            let r = usize::from(r_u16);
                            if col.validity.as_ref().is_some_and(|bm| !bm.is_valid(r)) {
                                null_count += 1;
                            } else {
                                raw.push(vs[r]);
                            }
                        }
                    }
                }
                raw.sort_unstable();
                distinct_count = count_distinct_sorted(&raw);
                let scale_f = DEC_SCALE as f64;
                nums.extend(
                    raw.into_iter()
                        .map(|d| (d as f64) / scale_f)
                        .filter(|x| x.is_finite()),
                );
            }
            UniformColKind::Float => {
                let mut raw_bits = Vec::with_capacity(total_rows);
                for b in batches {
                    let col = &b.cols[col_idx];
                    if let ColumnData::Float(vs) = &col.data {
                        for &r_u16 in &b.active_indices() {
                            let r = usize::from(r_u16);
                            if col.validity.as_ref().is_some_and(|bm| !bm.is_valid(r)) {
                                null_count += 1;
                            } else {
                                let bits = vs[r];
                                raw_bits.push(bits);
                                let f = f64::from_bits(bits);
                                if f.is_finite() {
                                    nums.push(f);
                                }
                            }
                        }
                    }
                }
                raw_bits.sort_unstable();
                distinct_count = count_distinct_sorted(&raw_bits);
                nums.sort_by(f64::total_cmp);
            }
            _ => {
                let mut set: FastSet<SingleKey> = FastSet::default();
                for b in batches {
                    let col = &b.cols[col_idx];
                    for &r_u16 in &b.active_indices() {
                        let v = col.get_val(usize::from(r_u16));
                        match &v {
                            Val::OptNone => null_count += 1,
                            Val::OptSome(inner) => {
                                if let Some(f) = unwrap_numeric_float(inner)
                                    && f.is_finite()
                                {
                                    nums.push(f);
                                }
                                set.insert(SingleKey::new(inner.as_ref().clone()));
                            }
                            other => {
                                if let Some(f) = unwrap_numeric_float(other)
                                    && f.is_finite()
                                {
                                    nums.push(f);
                                }
                                set.insert(SingleKey::new(other.clone()));
                            }
                        }
                    }
                }
                distinct_count = set.len();
                nums.sort_by(f64::total_cmp);
            }
        }

        if !nums.is_empty() {
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
        match kind {
            UniformColKind::Text => {
                let mut freq: FastMap<&[u8], usize> = FastMap::default();
                let mut min_b: Option<&[u8]> = None;
                let mut max_b: Option<&[u8]> = None;
                for b in batches {
                    let col = &b.cols[col_idx];
                    if let ColumnData::Text { offsets, data } = &col.data {
                        for &r_u16 in &b.active_indices() {
                            let r = usize::from(r_u16);
                            if col.validity.as_ref().is_some_and(|bm| !bm.is_valid(r)) {
                                null_count += 1;
                            } else {
                                let slice = &data[offsets[r]..offsets[r + 1]];
                                *freq.entry(slice).or_insert(0) += 1;
                                if min_b.is_none_or(|cur| slice < cur) {
                                    min_b = Some(slice);
                                }
                                if max_b.is_none_or(|cur| cur < slice) {
                                    max_b = Some(slice);
                                }
                            }
                        }
                    }
                }
                distinct_count = freq.len();
                min_display = min_b.map(|bs| String::from_utf8_lossy(bs).into_owned());
                max_display = max_b.map(|bs| String::from_utf8_lossy(bs).into_owned());
                let mut items: Vec<(String, usize)> = freq
                    .into_iter()
                    .map(|(bs, cnt)| (String::from_utf8_lossy(bs).into_owned(), cnt))
                    .collect();
                items.sort_by(|a, b| b.1.cmp(&a.1).then_with(|| a.0.cmp(&b.0)));
                items.truncate(3);
                top_values = items;
            }
            UniformColKind::Bool => {
                let mut cnt_false = 0usize;
                let mut cnt_true = 0usize;
                for b in batches {
                    let col = &b.cols[col_idx];
                    if let ColumnData::Bool(vs) = &col.data {
                        for &r_u16 in &b.active_indices() {
                            let r = usize::from(r_u16);
                            if col.validity.as_ref().is_some_and(|bm| !bm.is_valid(r)) {
                                null_count += 1;
                            } else if vs[r] != 0 {
                                cnt_true += 1;
                            } else {
                                cnt_false += 1;
                            }
                        }
                    }
                }
                distinct_count = usize::from(cnt_false > 0) + usize::from(cnt_true > 0);
                if cnt_false > 0 {
                    min_display = Some("false".to_string());
                } else if cnt_true > 0 {
                    min_display = Some("true".to_string());
                }
                if cnt_true > 0 {
                    max_display = Some("true".to_string());
                } else if cnt_false > 0 {
                    max_display = Some("false".to_string());
                }
                let mut items = Vec::with_capacity(2);
                if cnt_false > 0 {
                    items.push(("false".to_string(), cnt_false));
                }
                if cnt_true > 0 {
                    items.push(("true".to_string(), cnt_true));
                }
                items.sort_by(|a, b| b.1.cmp(&a.1).then_with(|| a.0.cmp(&b.0)));
                top_values = items;
            }
            UniformColKind::Float => {
                let mut bit_freq: FastMap<u64, usize> = FastMap::default();
                let mut min_bits: Option<u64> = None;
                let mut max_bits: Option<u64> = None;
                for b in batches {
                    let col = &b.cols[col_idx];
                    if let ColumnData::Float(vs) = &col.data {
                        for &r_u16 in &b.active_indices() {
                            let r = usize::from(r_u16);
                            if col.validity.as_ref().is_some_and(|bm| !bm.is_valid(r)) {
                                null_count += 1;
                            } else {
                                let bits = vs[r];
                                *bit_freq.entry(bits).or_insert(0) += 1;
                                let key = float_order_key(Float64::from_bits(bits));
                                if min_bits.is_none_or(|cur| {
                                    key < float_order_key(Float64::from_bits(cur))
                                }) {
                                    min_bits = Some(bits);
                                }
                                if max_bits.is_none_or(|cur| {
                                    float_order_key(Float64::from_bits(cur)) < key
                                }) {
                                    max_bits = Some(bits);
                                }
                            }
                        }
                    }
                }
                distinct_count = bit_freq.len();
                min_display = min_bits.map(|b| format_compact_num(f64::from_bits(b)));
                max_display = max_bits.map(|b| format_compact_num(f64::from_bits(b)));
                let mut str_freq: FastMap<String, usize> = FastMap::default();
                for (bits, cnt) in bit_freq {
                    *str_freq
                        .entry(format_compact_num(f64::from_bits(bits)))
                        .or_insert(0) += cnt;
                }
                let mut items: Vec<(String, usize)> = str_freq.into_iter().collect();
                items.sort_by(|a, b| b.1.cmp(&a.1).then_with(|| a.0.cmp(&b.0)));
                items.truncate(3);
                top_values = items;
            }
            UniformColKind::Int
            | UniformColKind::Date
            | UniformColKind::Timestamp
            | UniformColKind::Duration => {
                let mut int_freq: FastMap<i64, usize> = FastMap::default();
                let mut min_i: Option<i64> = None;
                let mut max_i: Option<i64> = None;
                for b in batches {
                    let col = &b.cols[col_idx];
                    let slice: &[i64] = match &col.data {
                        ColumnData::Int(v)
                        | ColumnData::Date(v)
                        | ColumnData::Timestamp(v)
                        | ColumnData::Duration(v) => v,
                        _ => continue,
                    };
                    for &r_u16 in &b.active_indices() {
                        let r = usize::from(r_u16);
                        if col.validity.as_ref().is_some_and(|bm| !bm.is_valid(r)) {
                            null_count += 1;
                        } else {
                            let x = slice[r];
                            *int_freq.entry(x).or_insert(0) += 1;
                            if min_i.is_none_or(|cur| x < cur) {
                                min_i = Some(x);
                            }
                            if max_i.is_none_or(|cur| cur < x) {
                                max_i = Some(x);
                            }
                        }
                    }
                }
                distinct_count = int_freq.len();
                let fmt_i = |x: i64| -> String {
                    match kind {
                        UniformColKind::Date => format_iso_date(x),
                        UniformColKind::Timestamp => format_iso_timestamp(x),
                        UniformColKind::Duration => format!("duration({x})"),
                        _ => x.to_string(),
                    }
                };
                min_display = min_i.map(fmt_i);
                max_display = max_i.map(fmt_i);
                let mut items: Vec<(String, usize)> = int_freq
                    .into_iter()
                    .map(|(x, cnt)| (fmt_i(x), cnt))
                    .collect();
                items.sort_by(|a, b| b.1.cmp(&a.1).then_with(|| a.0.cmp(&b.0)));
                items.truncate(3);
                top_values = items;
            }
            UniformColKind::Decimal => {
                let mut dec_freq: FastMap<i128, usize> = FastMap::default();
                let mut min_d: Option<i128> = None;
                let mut max_d: Option<i128> = None;
                for b in batches {
                    let col = &b.cols[col_idx];
                    if let ColumnData::Decimal(vs) = &col.data {
                        for &r_u16 in &b.active_indices() {
                            let r = usize::from(r_u16);
                            if col.validity.as_ref().is_some_and(|bm| !bm.is_valid(r)) {
                                null_count += 1;
                            } else {
                                let d = vs[r];
                                *dec_freq.entry(d).or_insert(0) += 1;
                                if min_d.is_none_or(|cur| d < cur) {
                                    min_d = Some(d);
                                }
                                if max_d.is_none_or(|cur| cur < d) {
                                    max_d = Some(d);
                                }
                            }
                        }
                    }
                }
                distinct_count = dec_freq.len();
                let fmt_d = |d: i128| -> String {
                    let mut s = String::with_capacity(24);
                    render_decimal_i128_into(&mut s, d);
                    s
                };
                min_display = min_d.map(fmt_d);
                max_display = max_d.map(fmt_d);
                let mut items: Vec<(String, usize)> = dec_freq
                    .into_iter()
                    .map(|(d, cnt)| (fmt_d(d), cnt))
                    .collect();
                items.sort_by(|a, b| b.1.cmp(&a.1).then_with(|| a.0.cmp(&b.0)));
                items.truncate(3);
                top_values = items;
            }
            UniformColKind::Mixed => {
                let mut distinct_set: FastSet<SingleKey> = FastSet::default();
                let mut freq: FastMap<String, usize> = FastMap::default();
                let mut min_v: Option<Val> = None;
                let mut max_v: Option<Val> = None;
                for b in batches {
                    let col = &b.cols[col_idx];
                    for &r_u16 in &b.active_indices() {
                        let raw = col.get_val(usize::from(r_u16));
                        let inner = match &raw {
                            Val::OptNone => {
                                null_count += 1;
                                continue;
                            }
                            Val::OptSome(u) => u.as_ref().clone(),
                            other => other.clone(),
                        };
                        *freq.entry(display_public_cell(&inner)).or_insert(0) += 1;
                        if min_v.as_ref().is_none_or(|cur| val_lt(&inner, cur)) {
                            min_v = Some(inner.clone());
                        }
                        if max_v.as_ref().is_none_or(|cur| val_lt(cur, &inner)) {
                            max_v = Some(inner.clone());
                        }
                        distinct_set.insert(SingleKey::new(inner));
                    }
                }
                distinct_count = distinct_set.len();
                min_display = min_v.as_ref().map(display_public_cell);
                max_display = max_v.as_ref().map(display_public_cell);
                let mut items: Vec<(String, usize)> = freq.into_iter().collect();
                items.sort_by(|a, b| b.1.cmp(&a.1).then_with(|| a.0.cmp(&b.0)));
                items.truncate(3);
                top_values = items;
            }
        }
    }

    let null_pct = if total_rows == 0 {
        0.0
    } else {
        (null_count as f64) * 100.0 / (total_rows as f64)
    };

    ProfileColSummary {
        col_name: c.name.clone(),
        ty_name: format_scalar_ty_name(&c.ty),
        row_count: total_rows,
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
    }
}

/// Compute a privacy-safe [`ProfileVal`] directly over a columnar [`VmTable`] without
/// materializing [`TableVal`], parallelizing across columns on large tables via
/// `std::thread::scope`. Matches [`profile_table`] 100% identically, including strict
/// `[REDACTED:<sorted,tags>]` protection for tagged columns and `table_row_tags`.
#[must_use]
pub fn profile_vm_table(
    vm: &VmTable,
    table_row_tags: &TagSet,
    static_col_tags: &[(Ident, TagSet)],
) -> ProfileVal {
    let total_rows = vm.total_rows();
    let ncols = vm.cols.len();
    if ncols == 0 {
        return ProfileVal { cols: Vec::new() };
    }

    let cols = if total_rows >= 8_192 && ncols >= 2 {
        std::thread::scope(|s| {
            let handles: Vec<_> = vm
                .cols
                .iter()
                .enumerate()
                .map(|(col_idx, spec)| {
                    s.spawn(move || {
                        profile_single_vm_col(
                            &vm.batches,
                            col_idx,
                            spec,
                            total_rows,
                            table_row_tags,
                            static_col_tags,
                        )
                    })
                })
                .collect();
            let mut out = Vec::with_capacity(ncols);
            for (idx, h) in handles.into_iter().enumerate() {
                let summary = h.join().unwrap_or_else(|_| {
                    profile_single_vm_col(
                        &vm.batches,
                        idx,
                        &vm.cols[idx],
                        total_rows,
                        table_row_tags,
                        static_col_tags,
                    )
                });
                out.push(summary);
            }
            out
        })
    } else {
        vm.cols
            .iter()
            .enumerate()
            .map(|(col_idx, spec)| {
                profile_single_vm_col(
                    &vm.batches,
                    col_idx,
                    spec,
                    total_rows,
                    table_row_tags,
                    static_col_tags,
                )
            })
            .collect()
    };

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
