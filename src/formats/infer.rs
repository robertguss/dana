//! Streaming type-lattice schema inference for `dana infer-schema`.
//!
//! Reads CSV, TSV, or JSONL (including transparent `.gz` and `.zst` decompression) and infers
//! a canonical Dana `schema` declaration over the join semilattice:
//! `Empty -> Bool | Int -> Decimal -> Float | Date | Timestamp -> Text`
//! while tracking nullability (`T?`) and conservative PII column-name hints.

use std::collections::HashSet;
use std::fmt::Write as _;
use std::io::{BufReader, Read};
use std::path::Path;

use crate::core::syntax::{AggKind, ColSpec, ScalarTy, TableTy, TagSet};
use crate::formats::compress::{open_auto_decoded_file, strip_compression_ext};
use crate::formats::csv::{CsvBatchReader, parse_csv_cell};
use crate::formats::json::{JsonValue, JsonlBatchReader, json_value_to_dana, parse_json};
use crate::formats::time::{parse_decimal_bigint_strict, parse_iso_date, parse_iso_timestamp};
use crate::oracle::value::{TableRow, TableVal, Val};

/// Input data format for schema inference.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum InferFormat {
    Csv,
    Tsv,
    Jsonl,
}

impl InferFormat {
    /// Detect input format from path extension (stripping `.gz`/`.zst` first).
    #[must_use]
    pub fn from_path(path: &str) -> Self {
        let inner = strip_compression_ext(path).to_ascii_lowercase();
        if inner.ends_with(".tsv") {
            Self::Tsv
        } else if inner.ends_with(".jsonl") || inner.ends_with(".ndjson") {
            Self::Jsonl
        } else {
            Self::Csv
        }
    }
}

/// Inferred column type along the Dana scalar inference lattice.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum InferredTy {
    Empty,
    Bool,
    Int,
    Decimal,
    Float,
    Date,
    Timestamp,
    Bytes,
    Text,
}

impl InferredTy {
    #[must_use]
    pub fn join(self, other: Self) -> Self {
        if self == Self::Empty {
            return other;
        }
        if other == Self::Empty || self == other {
            return self;
        }
        match (self, other) {
            (Self::Int, Self::Decimal) | (Self::Decimal, Self::Int) => Self::Decimal,
            (Self::Int | Self::Decimal, Self::Float) | (Self::Float, Self::Int | Self::Decimal) => {
                Self::Float
            }
            (Self::Date, Self::Timestamp) | (Self::Timestamp, Self::Date) => Self::Timestamp,
            _ => Self::Text,
        }
    }

    #[must_use]
    pub const fn dana_name(self) -> &'static str {
        match self {
            Self::Empty | Self::Text => "Text",
            Self::Bool => "Bool",
            Self::Int => "Int",
            Self::Decimal => "Decimal",
            Self::Float => "Float",
            Self::Date => "Date",
            Self::Timestamp => "Timestamp",
            Self::Bytes => "Bytes",
        }
    }

    /// Convert to a Dana [`ScalarTy`], wrapping in [`ScalarTy::Option`] when `nullable` is `true`.
    #[must_use]
    pub fn to_scalar_ty(self, nullable: bool) -> ScalarTy {
        let base = match self {
            Self::Empty | Self::Text => ScalarTy::Text,
            Self::Bool => ScalarTy::Bool,
            Self::Int => ScalarTy::Int,
            Self::Decimal => ScalarTy::Decimal,
            Self::Float => ScalarTy::Float,
            Self::Date => ScalarTy::Date,
            Self::Timestamp => ScalarTy::Timestamp,
            Self::Bytes => ScalarTy::Bytes,
        };
        if nullable {
            ScalarTy::Option(Box::new(base))
        } else {
            base
        }
    }
}

/// Statistics and inferred type for a single column.
#[derive(Clone, Debug)]
pub struct InferredColumn {
    pub name: String,
    pub ty: InferredTy,
    pub nullable: bool,
    pub non_null_count: usize,
    pub pii_hint: bool,
}

/// Full inferred schema summary.
#[derive(Clone, Debug)]
pub struct InferredSchema {
    pub name: String,
    pub rows_sampled: usize,
    pub cols: Vec<InferredColumn>,
}

impl InferredSchema {
    /// Render canonical formatted Dana `schema <Name> ... end` source code.
    #[must_use]
    pub fn render_dana(&self) -> String {
        let mut out = String::new();
        let _ = writeln!(out, "schema {}", self.name);
        for c in &self.cols {
            let opt = if c.nullable { "?" } else { "" };
            let tag = if c.pii_hint { " [pii]" } else { "" };
            let _ = writeln!(out, "  {}: {}{opt}{tag}", c.name, c.ty.dana_name());
        }
        out.push_str("end\n");
        out
    }

    /// Build an untagged [`TableTy`] suitable for `untyped` REPL exploration.
    #[must_use]
    pub fn to_public_table_ty(&self) -> TableTy {
        TableTy {
            cols: self
                .cols
                .iter()
                .map(|c| ColSpec {
                    name: c.name.clone(),
                    ty: c.ty.to_scalar_ty(c.nullable),
                    tags: TagSet::empty(),
                    bucketed: false,
                    agg_kind: AggKind::Raw,
                })
                .collect(),
            ..TableTy::default()
        }
    }
}

fn has_leading_zero_int(s: &str) -> bool {
    let digits = s
        .strip_prefix('-')
        .or_else(|| s.strip_prefix('+'))
        .unwrap_or(s);
    digits.len() > 1 && digits.starts_with('0') && digits.bytes().all(|b| b.is_ascii_digit())
}

/// Classify a raw text cell along the Dana scalar inference lattice (`None` for empty/null).
#[must_use]
pub fn classify_text_cell(raw: &str) -> Option<InferredTy> {
    let trimmed = raw.trim();
    if trimmed.is_empty() {
        return None;
    }
    let lower = trimmed.to_ascii_lowercase();
    if matches!(lower.as_str(), "true" | "false") {
        return Some(InferredTy::Bool);
    }
    if parse_iso_date(trimmed).is_ok() {
        return Some(InferredTy::Date);
    }
    if parse_iso_timestamp(trimmed).is_ok() {
        return Some(InferredTy::Timestamp);
    }
    // Preserve leading-zero codes (e.g. ZIP codes `00123`) as Text rather than Int.
    if has_leading_zero_int(trimmed) {
        return Some(InferredTy::Text);
    }
    if trimmed.parse::<i64>().is_ok() {
        return Some(InferredTy::Int);
    }
    if parse_decimal_bigint_strict(trimmed).is_ok() {
        return Some(InferredTy::Decimal);
    }
    if let Ok(f) = trimmed.parse::<f64>()
        && f.is_finite()
    {
        return Some(InferredTy::Float);
    }
    Some(InferredTy::Text)
}

fn classify_json_value(v: &JsonValue) -> Option<InferredTy> {
    match v {
        JsonValue::Null => None,
        JsonValue::Bool(_) => Some(InferredTy::Bool),
        JsonValue::Number(raw) => {
            if raw.parse::<i64>().is_ok() {
                Some(InferredTy::Int)
            } else if parse_decimal_bigint_strict(raw).is_ok() {
                Some(InferredTy::Decimal)
            } else {
                Some(InferredTy::Float)
            }
        }
        JsonValue::Str(s) => {
            if parse_iso_date(s).is_ok() {
                Some(InferredTy::Date)
            } else if parse_iso_timestamp(s).is_ok() {
                Some(InferredTy::Timestamp)
            } else {
                Some(InferredTy::Text)
            }
        }
        JsonValue::Array(_) | JsonValue::Object(_) => Some(InferredTy::Text),
    }
}

fn is_dana_keyword(name: &str) -> bool {
    matches!(
        name,
        "module"
            | "expose"
            | "use"
            | "tag"
            | "schema"
            | "struct"
            | "enum"
            | "const"
            | "fn"
            | "var"
            | "if"
            | "else"
            | "case"
            | "for"
            | "in"
            | "while"
            | "break"
            | "continue"
            | "return"
            | "try"
            | "and"
            | "or"
            | "not"
            | "is"
            | "true"
            | "false"
            | "none"
            | "stop"
            | "promise"
            | "examples"
            | "test"
            | "assert"
            | "table"
            | "where"
            | "end"
            | "as"
    )
}

/// Sanitize an arbitrary column header into a valid lowercase Dana identifier.
#[must_use]
pub fn sanitize_col_name(raw: &str, idx: usize) -> String {
    let mut s = String::new();
    for ch in raw.trim().chars() {
        if ch.is_ascii_alphanumeric() {
            s.push(ch.to_ascii_lowercase());
        } else if matches!(ch, '_' | '-' | ' ' | '.') && !s.ends_with('_') {
            s.push('_');
        }
    }
    let trimmed = s.trim_matches('_');
    if trimmed.is_empty() || trimmed.as_bytes()[0].is_ascii_digit() {
        format!("col_{}", idx + 1)
    } else if is_dana_keyword(trimmed) {
        format!("{trimmed}_col")
    } else {
        trimmed.to_string()
    }
}

/// Heuristic check for column names that typically hold personally identifiable information.
#[must_use]
pub fn looks_like_pii_column(name: &str) -> bool {
    let lower = name.to_ascii_lowercase();
    const PATTERNS: &[&str] = &[
        "email",
        "ssn",
        "phone",
        "mobile",
        "student_id",
        "patient_id",
        "donor_id",
        "user_id",
        "first_name",
        "last_name",
        "full_name",
        "dob",
        "birth",
        "address",
        "street",
        "passport",
        "credit_card",
        "ip_address",
    ];
    lower == "name" || PATTERNS.iter().any(|p| lower.contains(p))
}

/// Infer a [`InferredSchema`] from a streaming reader up to `sample_rows` rows.
///
/// # Errors
/// Returns an error string on I/O, UTF-8, or empty/unparseable file errors.
pub fn infer_schema_from_reader<R: Read>(
    reader: R,
    schema_name: &str,
    format: InferFormat,
    sample_rows: usize,
) -> Result<InferredSchema, String> {
    let limit = sample_rows.max(1);
    match format {
        InferFormat::Csv | InferFormat::Tsv => {
            let delim = if format == InferFormat::Tsv {
                b'\t'
            } else {
                b','
            };
            let mut csv_r = CsvBatchReader::new(BufReader::new(reader), delim);
            let Some(header) = csv_r.next_record().map_err(|e| e.to_string())? else {
                return Err("cannot infer schema from empty CSV/TSV file".to_string());
            };
            let mut seen_names = HashSet::new();
            let mut cols: Vec<InferredColumn> = header
                .fields
                .iter()
                .enumerate()
                .map(|(i, raw)| {
                    let mut name = sanitize_col_name(raw, i);
                    while !seen_names.insert(name.clone()) {
                        name.push('_');
                    }
                    InferredColumn {
                        pii_hint: looks_like_pii_column(&name),
                        name,
                        ty: InferredTy::Empty,
                        nullable: false,
                        non_null_count: 0,
                    }
                })
                .collect();

            if header.fields.len() == 1 {
                csv_r.set_preserve_empty_lines(true);
            }
            let mut rows_sampled = 0usize;
            while rows_sampled < limit {
                let batch = csv_r
                    .next_batch((limit - rows_sampled).min(2048))
                    .map_err(|e| e.to_string())?;
                if batch.is_empty() {
                    break;
                }
                for rec in batch {
                    rows_sampled += 1;
                    for (ci, col) in cols.iter_mut().enumerate() {
                        match rec.fields.get(ci).and_then(|s| classify_text_cell(s)) {
                            None => col.nullable = true,
                            Some(t) => {
                                col.ty = col.ty.join(t);
                                col.non_null_count += 1;
                            }
                        }
                    }
                }
            }
            Ok(InferredSchema {
                name: schema_name.to_string(),
                rows_sampled,
                cols,
            })
        }
        InferFormat::Jsonl => {
            let mut jl_r = JsonlBatchReader::new(BufReader::new(reader));
            let mut cols: Vec<InferredColumn> = Vec::new();
            let mut rows_sampled = 0usize;

            while rows_sampled < limit {
                let batch = jl_r
                    .next_batch((limit - rows_sampled).min(2048))
                    .map_err(|e| e.to_string())?;
                if batch.is_empty() {
                    break;
                }
                for line in batch {
                    let Ok(val) = parse_json(&line.raw_line) else {
                        continue;
                    };
                    let Some(entries) = val.as_object() else {
                        continue;
                    };
                    rows_sampled += 1;
                    let mut present = vec![false; cols.len()];
                    for (k, v) in entries {
                        let name = sanitize_col_name(k, cols.len());
                        let pos = if let Some(idx) = cols.iter().position(|c| c.name == name) {
                            idx
                        } else {
                            let idx = cols.len();
                            cols.push(InferredColumn {
                                pii_hint: looks_like_pii_column(&name),
                                name,
                                ty: InferredTy::Empty,
                                nullable: rows_sampled > 1,
                                non_null_count: 0,
                            });
                            present.push(false);
                            idx
                        };
                        present[pos] = true;
                        match classify_json_value(v) {
                            None => cols[pos].nullable = true,
                            Some(t) => {
                                cols[pos].ty = cols[pos].ty.join(t);
                                cols[pos].non_null_count += 1;
                            }
                        }
                    }
                    for (idx, seen) in present.into_iter().enumerate() {
                        if !seen {
                            cols[idx].nullable = true;
                        }
                    }
                }
            }
            if cols.is_empty() {
                return Err("cannot infer schema from empty or invalid JSONL file".to_string());
            }
            Ok(InferredSchema {
                name: schema_name.to_string(),
                rows_sampled,
                cols,
            })
        }
    }
}

/// Infer a schema directly from a file path (transparently supporting `.gz` and `.zst`).
///
/// # Errors
/// Returns an error string if the file cannot be opened, decompressed, or inferred.
pub fn infer_schema_from_file(
    path: &Path,
    schema_name: &str,
    format_override: Option<InferFormat>,
    sample_rows: usize,
) -> Result<InferredSchema, String> {
    let reader = open_auto_decoded_file(path).map_err(|e| format!("{}: {e}", path.display()))?;
    let format = format_override.unwrap_or_else(|| InferFormat::from_path(&path.to_string_lossy()));
    infer_schema_from_reader(reader, schema_name, format, sample_rows)
}

/// Derive a `CapCase` Dana schema identifier from a file path stem.
#[must_use]
pub fn default_schema_name_from_path(path: &Path) -> String {
    let raw = path.to_string_lossy();
    let stripped = strip_compression_ext(&raw);
    let stem = Path::new(stripped)
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or("Record");
    let mut out = String::new();
    for part in stem.split(|c: char| !c.is_ascii_alphanumeric()) {
        let mut chars = part.chars();
        if let Some(first) = chars.next() {
            out.push(first.to_ascii_uppercase());
            for ch in chars {
                out.push(ch.to_ascii_lowercase());
            }
        }
    }
    if out.is_empty() || !out.as_bytes()[0].is_ascii_uppercase() {
        "Record".to_string()
    } else {
        out
    }
}

/// Read a CSV or TSV file without a pre-declared schema (used by REPL `untyped.read_csv`).
///
/// Infers column names and Dana scalar types across all rows, then materializes a typed
/// [`TableVal`] using those inferred column specs.
///
/// # Errors
/// Returns an error string on I/O, decompression, or empty/malformed CSV errors.
pub fn read_csv_file_untyped(
    path: &Path,
    schema_name: &str,
    delimiter_override: Option<u8>,
) -> Result<(InferredSchema, TableVal), String> {
    let fmt = match delimiter_override {
        Some(b'\t') => InferFormat::Tsv,
        Some(_) => InferFormat::Csv,
        None => InferFormat::from_path(&path.to_string_lossy()),
    };
    let delim = delimiter_override.unwrap_or(if fmt == InferFormat::Tsv { b'\t' } else { b',' });
    let reader = open_auto_decoded_file(path).map_err(|e| format!("{}: {e}", path.display()))?;
    let mut csv_r = CsvBatchReader::new(BufReader::new(reader), delim);
    let Some(header) = csv_r.next_record().map_err(|e| e.to_string())? else {
        return Err(format!("cannot read empty CSV file `{}`", path.display()));
    };
    let mut seen_names = HashSet::new();
    let mut cols: Vec<InferredColumn> = header
        .fields
        .iter()
        .enumerate()
        .map(|(i, raw)| {
            let mut name = sanitize_col_name(raw, i);
            while !seen_names.insert(name.clone()) {
                name.push('_');
            }
            InferredColumn {
                pii_hint: looks_like_pii_column(&name),
                name,
                ty: InferredTy::Empty,
                nullable: false,
                non_null_count: 0,
            }
        })
        .collect();
    if header.fields.len() == 1 {
        csv_r.set_preserve_empty_lines(true);
    }

    let mut raw_rows: Vec<Vec<String>> = Vec::new();
    loop {
        let batch = csv_r.next_batch(2048).map_err(|e| e.to_string())?;
        if batch.is_empty() {
            break;
        }
        for rec in batch {
            for (ci, col) in cols.iter_mut().enumerate() {
                match rec.fields.get(ci).and_then(|s| classify_text_cell(s)) {
                    None => col.nullable = true,
                    Some(t) => {
                        col.ty = col.ty.join(t);
                        col.non_null_count += 1;
                    }
                }
            }
            raw_rows.push(rec.fields);
        }
    }

    let inferred = InferredSchema {
        name: schema_name.to_string(),
        rows_sampled: raw_rows.len(),
        cols,
    };
    let table_ty = inferred.to_public_table_ty();
    let mut rows = Vec::with_capacity(raw_rows.len());
    for raw in raw_rows {
        let mut cells = Vec::with_capacity(table_ty.cols.len());
        for (ci, col) in table_ty.cols.iter().enumerate() {
            let cell_str = raw.get(ci).map_or("", String::as_str);
            let val = parse_csv_cell(cell_str, &col.ty).unwrap_or_else(|_| {
                if col.ty.is_option() && cell_str.trim().is_empty() {
                    Val::OptNone
                } else if col.ty.is_option() {
                    Val::OptSome(Box::new(Val::Text(cell_str.to_string())))
                } else {
                    Val::Text(cell_str.to_string())
                }
            });
            cells.push(val);
        }
        rows.push(TableRow {
            cells,
            group_meta: None,
        });
    }
    Ok((
        inferred,
        TableVal {
            cols: table_ty.cols,
            rows,
        },
    ))
}

/// Read a JSONL/NDJSON file without a pre-declared schema (used by REPL `untyped.read_jsonl`).
///
/// Supports plain, `.gz`, and `.zst` transparently.
///
/// # Errors
/// Returns an error string on I/O, decompression, or empty/unparseable JSONL files.
pub fn read_jsonl_file_untyped(
    path: &Path,
    schema_name: &str,
) -> Result<(InferredSchema, TableVal), String> {
    let reader = open_auto_decoded_file(path).map_err(|e| format!("{}: {e}", path.display()))?;
    let mut jl_r = JsonlBatchReader::new(BufReader::new(reader));
    let mut cols: Vec<InferredColumn> = Vec::new();
    let mut parsed_objs: Vec<Vec<(String, JsonValue)>> = Vec::new();

    loop {
        let batch = jl_r.next_batch(2048).map_err(|e| e.to_string())?;
        if batch.is_empty() {
            break;
        }
        for line in batch {
            let Ok(val) = parse_json(&line.raw_line) else {
                continue;
            };
            let Some(entries) = val.as_object() else {
                continue;
            };
            let row_idx = parsed_objs.len();
            let mut present = vec![false; cols.len()];
            let mut normed = Vec::with_capacity(entries.len());
            for (k, v) in entries {
                let name = sanitize_col_name(k, cols.len());
                let pos = if let Some(idx) = cols.iter().position(|c| c.name == name) {
                    idx
                } else {
                    let idx = cols.len();
                    cols.push(InferredColumn {
                        pii_hint: looks_like_pii_column(&name),
                        name: name.clone(),
                        ty: InferredTy::Empty,
                        nullable: row_idx > 0,
                        non_null_count: 0,
                    });
                    present.push(false);
                    idx
                };
                present[pos] = true;
                match classify_json_value(v) {
                    None => cols[pos].nullable = true,
                    Some(t) => {
                        cols[pos].ty = cols[pos].ty.join(t);
                        cols[pos].non_null_count += 1;
                    }
                }
                normed.push((name, v.clone()));
            }
            for (idx, seen) in present.into_iter().enumerate() {
                if !seen {
                    cols[idx].nullable = true;
                }
            }
            parsed_objs.push(normed);
        }
    }

    if cols.is_empty() {
        return Err(format!(
            "cannot infer schema from empty or invalid JSONL file `{}`",
            path.display()
        ));
    }
    let inferred = InferredSchema {
        name: schema_name.to_string(),
        rows_sampled: parsed_objs.len(),
        cols,
    };
    let table_ty = inferred.to_public_table_ty();
    let mut rows = Vec::with_capacity(parsed_objs.len());
    for obj in parsed_objs {
        let mut cells = Vec::with_capacity(table_ty.cols.len());
        for col in &table_ty.cols {
            let found = obj.iter().find(|(k, _)| k == &col.name).map(|(_, v)| v);
            let val = json_value_to_dana(found, &col.ty).unwrap_or_else(|_| {
                if col.ty.is_option() {
                    Val::OptNone
                } else {
                    Val::Text(String::new())
                }
            });
            cells.push(val);
        }
        rows.push(TableRow {
            cells,
            group_meta: None,
        });
    }
    Ok((
        inferred,
        TableVal {
            cols: table_ty.cols,
            rows,
        },
    ))
}
