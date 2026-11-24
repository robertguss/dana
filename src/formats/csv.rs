//! RFC 4180 CSV/TSV parser and schema-validated quarantine loader (`(valid_rows, bad_rows)`).
//!
//! Preserves exact 1-based line numbers and enforces `quarantine_bad_row_table_ty` sensitivity
//! tag propagation on `bad_rows`.

use crate::core::bigint::BigInt;
use crate::core::check::quarantine_bad_row_table_ty;
use crate::core::syntax::{Float64, ScalarTy, TableTy};
use crate::formats::time::{parse_decimal_bigint, parse_iso_date, parse_iso_timestamp};
use crate::oracle::value::{TableRow, TableVal, Val};

/// A single parsed RFC 4180 CSV/TSV record with its 1-based starting line number and raw line text.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CsvRecord {
    pub line: usize,
    pub raw_line: String,
    pub fields: Vec<String>,
}

/// Parse UTF-8 CSV/TSV text into RFC 4180 records with 1-based line numbers.
#[must_use]
pub fn parse_csv_records(input: &str, delimiter: u8) -> Vec<CsvRecord> {
    let text = input.strip_prefix('\u{FEFF}').unwrap_or(input);
    let bytes = text.as_bytes();
    let mut records = Vec::new();
    let mut pos = 0usize;
    let mut line_no = 1usize;

    while pos < bytes.len() {
        // Skip completely empty trailing newline at EOF.
        let rec_start = pos;
        let rec_line = line_no;
        let mut fields = Vec::new();

        loop {
            let mut field = String::new();
            if pos < bytes.len() && bytes[pos] == b'"' {
                pos += 1; // opening quote
                while pos < bytes.len() {
                    if bytes[pos] == b'"' {
                        if pos + 1 < bytes.len() && bytes[pos + 1] == b'"' {
                            field.push('"');
                            pos += 2;
                        } else {
                            pos += 1; // closing quote
                            break;
                        }
                    } else {
                        let ch_start = pos;
                        if bytes[pos] == b'\n' {
                            line_no += 1;
                        }
                        pos += 1;
                        while pos < bytes.len() && !text.is_char_boundary(pos) {
                            pos += 1;
                        }
                        field.push_str(&text[ch_start..pos]);
                    }
                }
                // Consume up to delimiter or newline.
                while pos < bytes.len()
                    && bytes[pos] != delimiter
                    && bytes[pos] != b'\n'
                    && bytes[pos] != b'\r'
                {
                    let ch_start = pos;
                    pos += 1;
                    while pos < bytes.len() && !text.is_char_boundary(pos) {
                        pos += 1;
                    }
                    field.push_str(&text[ch_start..pos]);
                }
            } else {
                let start = pos;
                while pos < bytes.len()
                    && bytes[pos] != delimiter
                    && bytes[pos] != b'\n'
                    && bytes[pos] != b'\r'
                {
                    pos += 1;
                }
                field.push_str(&text[start..pos]);
            }
            fields.push(field);

            if pos < bytes.len() && bytes[pos] == delimiter {
                pos += 1;
                continue;
            }
            let rec_end = pos;
            if pos < bytes.len() && bytes[pos] == b'\r' {
                pos += 1;
            }
            if pos < bytes.len() && bytes[pos] == b'\n' {
                pos += 1;
                line_no += 1;
            }
            let raw_line = text[rec_start..rec_end].to_string();
            // Skip pure blank lines.
            if !(fields.len() == 1 && fields[0].is_empty() && raw_line.is_empty()) {
                records.push(CsvRecord {
                    line: rec_line,
                    raw_line,
                    fields,
                });
            }
            break;
        }
    }

    records
}

/// Parse a single cell string according to a [`ScalarTy`], returning `(error_kind, val)`.
pub fn parse_csv_cell(raw: &str, ty: &ScalarTy) -> Result<Val, &'static str> {
    let trimmed = raw.trim();
    match ty {
        ScalarTy::Option(inner) => {
            if trimmed.is_empty() {
                Ok(Val::OptNone)
            } else {
                let v = parse_csv_cell(raw, inner)?;
                Ok(Val::OptSome(Box::new(v)))
            }
        }
        ScalarTy::Text => Ok(Val::Text(raw.to_string())),
        ScalarTy::Bool => match trimmed.to_ascii_lowercase().as_str() {
            "true" | "1" | "yes" => Ok(Val::Bool(true)),
            "false" | "0" | "no" => Ok(Val::Bool(false)),
            "" => Err("MissingRequired"),
            _ => Err("BadBool"),
        },
        ScalarTy::Int => {
            if trimmed.is_empty() {
                return Err("MissingRequired");
            }
            let n: i64 = trimmed.parse().map_err(|_| "BadInt")?;
            Ok(Val::Int(BigInt::from(n)))
        }
        ScalarTy::Decimal => {
            if trimmed.is_empty() {
                return Err("MissingRequired");
            }
            let d = parse_decimal_bigint(trimmed).map_err(|_| "BadDecimal")?;
            Ok(Val::Decimal(d))
        }
        ScalarTy::Float => {
            if trimmed.is_empty() {
                return Err("MissingRequired");
            }
            let f: f64 = trimmed.parse().map_err(|_| "BadFloat")?;
            if f.is_nan() || f.is_infinite() {
                return Err("BadFloat");
            }
            Ok(Val::Float(Float64::from_f64(f)))
        }
        ScalarTy::Date => {
            if trimmed.is_empty() {
                return Err("MissingRequired");
            }
            let days = parse_iso_date(trimmed).map_err(|_| "BadDate")?;
            Ok(Val::Date(BigInt::from(days)))
        }
        ScalarTy::Timestamp => {
            if trimmed.is_empty() {
                return Err("MissingRequired");
            }
            let us = parse_iso_timestamp(trimmed).map_err(|_| "BadTimestamp")?;
            Ok(Val::Timestamp(BigInt::from(us)))
        }
        ScalarTy::Duration => {
            if trimmed.is_empty() {
                return Err("MissingRequired");
            }
            let us: i64 = trimmed.parse().map_err(|_| "BadDuration")?;
            Ok(Val::Duration(BigInt::from(us)))
        }
        ScalarTy::Bytes => Ok(Val::Bytes(raw.as_bytes().to_vec())),
        ScalarTy::Unit => Ok(Val::Unit),
        ScalarTy::Data(_) => Err("UnsupportedCellType"),
    }
}

/// Parse CSV text into `(valid_rows, bad_rows)` against a [`TableTy`] schema and optional
/// per-column constraint evaluator callback `check_col(col_idx, &Val) -> bool`.
///
/// # Errors
/// Returns an error string if the header row is missing required schema columns.
pub fn parse_csv_with_schema<F>(
    input: &str,
    schema: &TableTy,
    delimiter: u8,
    mut check_constraint: F,
) -> Result<(TableVal, TableVal), String>
where
    F: FnMut(usize, &Val) -> bool,
{
    let records = parse_csv_records(input, delimiter);
    let bad_tt = quarantine_bad_row_table_ty(schema);

    let Some(header) = records.first() else {
        return Ok((
            TableVal {
                cols: schema.cols.clone(),
                rows: Vec::new(),
            },
            TableVal {
                cols: bad_tt.cols,
                rows: Vec::new(),
            },
        ));
    };

    let mut col_indices = Vec::with_capacity(schema.cols.len());
    for col in &schema.cols {
        let Some(idx) = header
            .fields
            .iter()
            .position(|h| h.trim() == col.name.as_str())
        else {
            return Err(format!("missing required CSV column `{}`", col.name));
        };
        col_indices.push(idx);
    }

    let mut good_rows = Vec::new();
    let mut bad_rows = Vec::new();

    for rec in &records[1..] {
        let mut cells = Vec::with_capacity(schema.cols.len());
        let mut bad_hit: Option<(&str, &str, String)> = None;

        for (ci, col) in schema.cols.iter().enumerate() {
            let field_idx = col_indices[ci];
            let Some(raw_val) = rec.fields.get(field_idx) else {
                bad_hit = Some((col.name.as_str(), "MissingColumn", String::new()));
                break;
            };
            match parse_csv_cell(raw_val, &col.ty) {
                Ok(val) => {
                    let inner_ok = match &val {
                        Val::OptNone => true,
                        Val::OptSome(inner) => check_constraint(ci, inner),
                        other => check_constraint(ci, other),
                    };
                    if !inner_ok {
                        bad_hit = Some((col.name.as_str(), "ConstraintFailed", raw_val.clone()));
                        break;
                    }
                    cells.push(val);
                }
                Err(kind) => {
                    bad_hit = Some((col.name.as_str(), kind, raw_val.clone()));
                    break;
                }
            }
        }

        if let Some((col_name, err_kind, raw_val)) = bad_hit {
            bad_rows.push(TableRow {
                cells: vec![
                    Val::Int(BigInt::from(rec.line)),
                    Val::Text(col_name.to_string()),
                    Val::Text(err_kind.to_string()),
                    Val::Text(raw_val),
                    Val::Text(rec.raw_line.clone()),
                ],
                group_meta: None,
            });
        } else {
            good_rows.push(TableRow {
                cells,
                group_meta: None,
            });
        }
    }

    Ok((
        TableVal {
            cols: schema.cols.clone(),
            rows: good_rows,
        },
        TableVal {
            cols: bad_tt.cols,
            rows: bad_rows,
        },
    ))
}

/// Format a [`TableVal`] as RFC 4180 CSV text.
#[must_use]
pub fn format_csv_table(tv: &TableVal, delimiter: u8) -> String {
    let delim = delimiter as char;
    let mut out = String::new();
    for (i, c) in tv.cols.iter().enumerate() {
        if i > 0 {
            out.push(delim);
        }
        push_csv_escaped(&mut out, &c.name, delimiter);
    }
    out.push('\n');
    for row in &tv.rows {
        for (i, cell) in row.cells.iter().enumerate() {
            if i > 0 {
                out.push(delim);
            }
            let rendered = render_csv_cell(cell);
            push_csv_escaped(&mut out, &rendered, delimiter);
        }
        out.push('\n');
    }
    out
}

fn render_csv_cell(v: &Val) -> String {
    match v {
        Val::OptNone => String::new(),
        Val::OptSome(inner) => render_csv_cell(inner),
        Val::Text(s) => s.clone(),
        Val::Date(d) => d
            .to_i64()
            .map_or_else(|| d.to_string(), crate::formats::time::format_iso_date),
        Val::Timestamp(ts) => ts.to_i64().map_or_else(
            || ts.to_string(),
            crate::formats::time::format_iso_timestamp,
        ),
        other => crate::oracle::value::render_public_val(other),
    }
}

fn push_csv_escaped(out: &mut String, field: &str, delimiter: u8) {
    let needs_quote = field
        .bytes()
        .any(|b| b == delimiter || b == b'"' || b == b'\n' || b == b'\r');
    if needs_quote {
        out.push('"');
        for ch in field.chars() {
            if ch == '"' {
                out.push('"');
            }
            out.push(ch);
        }
        out.push('"');
    } else {
        out.push_str(field);
    }
}
