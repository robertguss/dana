//! Native zero-crate OOXML Excel (`.xlsx`) reader and writer with quarantine-first parsing,
//! iterative O(1)-stack XML tokenization (strict XXE/DTD rejection), Excel 1900/1904 serial
//! date/timestamp math, and exact `Decimal` preservation.
//!
//! Compiles under `#[forbid(unsafe_code)]` via `src/lib.rs`.

use std::collections::HashMap;
use std::fmt::Write as _;
use std::fs;
use std::path::Path;

use crate::core::bigint::{BigInt, DEC_MAX, DEC_MIN};
use crate::core::check::quarantine_bad_row_table_ty;
use crate::core::syntax::{Float64, ScalarTy, TableTy};
use crate::formats::crypto::to_hex_lower;
use crate::formats::time::{
    MICROS_PER_DAY, format_iso_date, format_iso_timestamp, parse_decimal_bigint_strict,
    parse_iso_date, parse_iso_timestamp,
};
use crate::formats::zip::{ZipArchive, ZipCompression, validate_zip_entry_name, write_zip_bytes};
use crate::oracle::value::{TableRow, TableVal, Val, render_decimal};

/// Excel 1900 epoch offset for dates on or after 1900-03-01 (`serial >= 61`):
/// `days_since_1970 = serial - 25569`.
const EXCEL_1900_OFFSET_POST_LEAP: i64 = 25_569;
/// Excel 1900 epoch offset for dates in 1900-01-01..=1900-02-28 (`1 <= serial <= 59`).
const EXCEL_1900_OFFSET_PRE_LEAP: i64 = 25_568;
/// Excel 1904 epoch offset: `days_from_civil(1904, 1, 1) == -24107`.
const EXCEL_1904_OFFSET: i64 = 24_107;

// ---------------------------------------------------------------------------
// Iterative O(1)-Stack XML Tokenizer (Strict XXE/DTD Rejection)
// ---------------------------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Eq)]
enum XmlEvent {
    Start {
        name: String,
        attrs: Vec<(String, String)>,
        empty: bool,
    },
    End(String),
    Text(String),
}

struct XmlTokenizer<'a> {
    src: &'a str,
    bytes: &'a [u8],
    pos: usize,
}

impl<'a> XmlTokenizer<'a> {
    fn new(input: &'a str) -> Self {
        let stripped = input.strip_prefix('\u{FEFF}').unwrap_or(input);
        Self {
            src: stripped,
            bytes: stripped.as_bytes(),
            pos: 0,
        }
    }

    fn next_event(&mut self) -> Result<Option<XmlEvent>, String> {
        loop {
            if self.pos >= self.bytes.len() {
                return Ok(None);
            }
            if self.bytes[self.pos] == b'<' {
                if self.src[self.pos..].starts_with("<?") {
                    let Some(end_rel) = self.src[self.pos + 2..].find("?>") else {
                        return Err("unterminated XML processing instruction".to_string());
                    };
                    self.pos += 2 + end_rel + 2;
                    continue;
                }
                if self.src[self.pos..].starts_with("<!--") {
                    let Some(end_rel) = self.src[self.pos + 4..].find("-->") else {
                        return Err("unterminated XML comment".to_string());
                    };
                    self.pos += 4 + end_rel + 3;
                    continue;
                }
                if self.src[self.pos..].starts_with("<![CDATA[") {
                    let start = self.pos + 9;
                    let Some(end_rel) = self.src[start..].find("]]>") else {
                        return Err("unterminated XML CDATA section".to_string());
                    };
                    let text = self.src[start..start + end_rel].to_string();
                    self.pos = start + end_rel + 3;
                    return Ok(Some(XmlEvent::Text(text)));
                }
                if self.src[self.pos..].starts_with("<!") {
                    return Err(
                        "XML DTD/ENTITY declarations (`<!DOCTYPE`/`<!ENTITY`) are forbidden"
                            .to_string(),
                    );
                }
                if self.src[self.pos..].starts_with("</") {
                    self.pos += 2;
                    self.skip_ws();
                    let name = self.read_name()?;
                    self.skip_ws();
                    if self.bytes.get(self.pos) != Some(&b'>') {
                        return Err(format!("expected `>` closing XML tag `</{name}>`"));
                    }
                    self.pos += 1;
                    return Ok(Some(XmlEvent::End(name)));
                }
                // Opening or self-closing tag
                self.pos += 1;
                let name = self.read_name()?;
                let mut attrs = Vec::new();
                let mut empty = false;
                loop {
                    self.skip_ws();
                    match self.bytes.get(self.pos) {
                        None => return Err(format!("unterminated XML start tag `<{name}>`")),
                        Some(&b'>') => {
                            self.pos += 1;
                            break;
                        }
                        Some(&b'/') => {
                            if self.bytes.get(self.pos + 1) != Some(&b'>') {
                                return Err(format!("expected `/>` in XML tag `<{name}>`"));
                            }
                            self.pos += 2;
                            empty = true;
                            break;
                        }
                        Some(_) => {
                            let attr_name = self.read_name()?;
                            self.skip_ws();
                            if self.bytes.get(self.pos) != Some(&b'=') {
                                return Err(format!(
                                    "expected `=` after XML attribute `{attr_name}`"
                                ));
                            }
                            self.pos += 1;
                            self.skip_ws();
                            let quote = match self.bytes.get(self.pos) {
                                Some(&q @ (b'"' | b'\'')) => q,
                                _ => {
                                    return Err(format!(
                                        "expected quote for XML attribute `{attr_name}`"
                                    ));
                                }
                            };
                            self.pos += 1;
                            let val_start = self.pos;
                            while let Some(&b) = self.bytes.get(self.pos) {
                                if b == quote {
                                    break;
                                }
                                self.pos += 1;
                            }
                            if self.bytes.get(self.pos) != Some(&quote) {
                                return Err(format!(
                                    "unterminated XML attribute `{attr_name}` value"
                                ));
                            }
                            let raw_val = &self.src[val_start..self.pos];
                            self.pos += 1;
                            let decoded = decode_xml_entities(raw_val)?;
                            attrs.push((attr_name, decoded));
                        }
                    }
                }
                return Ok(Some(XmlEvent::Start { name, attrs, empty }));
            }

            // Text node up to next `<`
            let start = self.pos;
            while let Some(&b) = self.bytes.get(self.pos) {
                if b == b'<' {
                    break;
                }
                self.pos += 1;
            }
            let raw_text = &self.src[start..self.pos];
            let decoded = decode_xml_entities(raw_text)?;
            return Ok(Some(XmlEvent::Text(decoded)));
        }
    }

    fn skip_ws(&mut self) {
        while let Some(&b) = self.bytes.get(self.pos) {
            if matches!(b, b' ' | b'\t' | b'\r' | b'\n') {
                self.pos += 1;
            } else {
                break;
            }
        }
    }

    fn read_name(&mut self) -> Result<String, String> {
        let start = self.pos;
        while let Some(&b) = self.bytes.get(self.pos) {
            if matches!(b, b' ' | b'\t' | b'\r' | b'\n' | b'=' | b'>' | b'/' | b'<') {
                break;
            }
            self.pos += 1;
        }
        if self.pos == start {
            return Err("expected XML tag or attribute name".to_string());
        }
        Ok(self.src[start..self.pos].to_string())
    }
}

fn local_name(name: &str) -> &str {
    name.rsplit_once(':').map_or(name, |(_, local)| local)
}

fn get_attr<'a>(attrs: &'a [(String, String)], key: &str) -> Option<&'a str> {
    attrs
        .iter()
        .find(|(k, _)| k == key || local_name(k) == key)
        .map(|(_, v)| v.as_str())
}

fn decode_xml_entities(raw: &str) -> Result<String, String> {
    if !raw.contains('&') {
        return Ok(raw.to_string());
    }
    let mut out = String::with_capacity(raw.len());
    let mut rest = raw;
    while let Some(amp_idx) = rest.find('&') {
        out.push_str(&rest[..amp_idx]);
        let after_amp = &rest[amp_idx + 1..];
        let Some(semi_idx) = after_amp.find(';') else {
            return Err("unterminated XML entity reference".to_string());
        };
        let entity = &after_amp[..semi_idx];
        match entity {
            "amp" => out.push('&'),
            "lt" => out.push('<'),
            "gt" => out.push('>'),
            "quot" => out.push('"'),
            "apos" => out.push('\''),
            num if num.starts_with('#') => {
                let code_opt =
                    if let Some(hex) = num.strip_prefix("#x").or_else(|| num.strip_prefix("#X")) {
                        u32::from_str_radix(hex, 16).ok()
                    } else {
                        num[1..].parse::<u32>().ok()
                    };
                let Some(code) = code_opt else {
                    return Err(format!("invalid XML numeric entity `&{entity};`"));
                };
                if code == 0 {
                    return Err("NUL character reference forbidden in XML".to_string());
                }
                let Some(ch) = char::from_u32(code) else {
                    return Err(format!("invalid Unicode scalar in XML entity `&{entity};`"));
                };
                out.push(ch);
            }
            other => {
                return Err(format!("unsupported XML entity `&{other};`"));
            }
        }
        rest = &after_amp[semi_idx + 1..];
    }
    out.push_str(rest);
    Ok(out)
}

fn push_xml_escaped(out: &mut String, s: &str) {
    for ch in s.chars() {
        match ch {
            '&' => out.push_str("&amp;"),
            '<' => out.push_str("&lt;"),
            '>' => out.push_str("&gt;"),
            '"' => out.push_str("&quot;"),
            '\'' => out.push_str("&apos;"),
            c => out.push(c),
        }
    }
}

// ---------------------------------------------------------------------------
// OOXML Workbook, Relationships, Shared Strings, and Styles Parsing
// ---------------------------------------------------------------------------

struct SheetEntry {
    name: String,
    rel_id: String,
}

struct WorkbookMeta {
    sheets: Vec<SheetEntry>,
    date1904: bool,
}

fn parse_workbook_xml(xml: &str) -> Result<WorkbookMeta, String> {
    let mut tok = XmlTokenizer::new(xml);
    let mut sheets = Vec::new();
    let mut date1904 = false;

    while let Some(ev) = tok.next_event()? {
        if let XmlEvent::Start { name, attrs, .. } = ev {
            match local_name(&name) {
                "workbookPr" => {
                    if let Some(v) = get_attr(&attrs, "date1904")
                        && (v == "1" || v.eq_ignore_ascii_case("true"))
                    {
                        date1904 = true;
                    }
                }
                "sheet" => {
                    let sname = get_attr(&attrs, "name")
                        .ok_or_else(|| "workbook <sheet> missing `name` attribute".to_string())?
                        .to_string();
                    let rid = attrs
                        .iter()
                        .find(|(k, _)| k == "r:id" || local_name(k) == "id")
                        .map(|(_, v)| v.clone())
                        .ok_or_else(|| {
                            format!("workbook <sheet name=\"{sname}\"> missing `r:id` attribute")
                        })?;
                    sheets.push(SheetEntry {
                        name: sname,
                        rel_id: rid,
                    });
                }
                _ => {}
            }
        }
    }

    Ok(WorkbookMeta { sheets, date1904 })
}

fn parse_workbook_rels(xml: &str) -> Result<HashMap<String, String>, String> {
    let mut tok = XmlTokenizer::new(xml);
    let mut map = HashMap::new();
    while let Some(ev) = tok.next_event()? {
        if let XmlEvent::Start { name, attrs, .. } = ev
            && local_name(&name) == "Relationship"
            && let (Some(id), Some(target)) = (get_attr(&attrs, "Id"), get_attr(&attrs, "Target"))
        {
            map.insert(id.to_string(), target.to_string());
        }
    }
    Ok(map)
}

fn resolve_xl_target(target: &str) -> Result<String, String> {
    let cleaned = target.strip_prefix('/').unwrap_or(target);
    validate_zip_entry_name(cleaned).map_err(|e| e.to_string())?;
    if cleaned.starts_with("xl/") {
        Ok(cleaned.to_string())
    } else {
        let joined = format!("xl/{cleaned}");
        validate_zip_entry_name(&joined).map_err(|e| e.to_string())?;
        Ok(joined)
    }
}

fn parse_shared_strings(xml: &str) -> Result<Vec<String>, String> {
    let mut tok = XmlTokenizer::new(xml);
    let mut strings = Vec::new();
    let mut in_si = false;
    let mut in_t = false;
    let mut in_rph = false;
    let mut cur = String::new();

    while let Some(ev) = tok.next_event()? {
        match ev {
            XmlEvent::Start { name, empty, .. } => match local_name(&name) {
                "si" => {
                    cur.clear();
                    if empty {
                        strings.push(String::new());
                    } else {
                        in_si = true;
                    }
                }
                "rPh" if in_si && !empty => in_rph = true,
                "t" if in_si && !in_rph && !empty => in_t = true,
                _ => {}
            },
            XmlEvent::End(name) => match local_name(&name) {
                "si" => {
                    if in_si {
                        strings.push(std::mem::take(&mut cur));
                        in_si = false;
                        in_t = false;
                        in_rph = false;
                    }
                }
                "rPh" => in_rph = false,
                "t" => in_t = false,
                _ => {}
            },
            XmlEvent::Text(text) => {
                if in_si && in_t && !in_rph {
                    cur.push_str(&text);
                }
            }
        }
    }

    Ok(strings)
}

fn is_builtin_date_num_fmt(id: u32) -> bool {
    matches!(id, 14..=22 | 45..=47)
}

fn is_custom_date_format_code(code: &str) -> bool {
    let mut in_quotes = false;
    let mut in_brackets = false;
    let mut escaped = false;
    for ch in code.chars() {
        if escaped {
            escaped = false;
            continue;
        }
        if ch == '\\' {
            escaped = true;
            continue;
        }
        if ch == '"' {
            in_quotes = !in_quotes;
            continue;
        }
        if in_quotes {
            continue;
        }
        if ch == '[' {
            in_brackets = true;
            continue;
        }
        if ch == ']' {
            in_brackets = false;
            continue;
        }
        if in_brackets {
            continue;
        }
        if matches!(ch, 'y' | 'Y' | 'd' | 'D' | 'h' | 'H' | 's' | 'S') {
            return true;
        }
    }
    false
}

/// Parse `xl/styles.xml` and return a vector indexed by `<c s="idx">` indicating whether
/// style `idx` formats numeric values as an Excel date/time serial.
fn parse_date_style_flags(xml: &str) -> Result<Vec<bool>, String> {
    let mut tok = XmlTokenizer::new(xml);
    let mut custom_fmts: HashMap<u32, String> = HashMap::new();
    let mut cell_xfs_num_fmt_ids: Vec<u32> = Vec::new();
    let mut in_cell_xfs = false;

    while let Some(ev) = tok.next_event()? {
        match ev {
            XmlEvent::Start { name, attrs, empty } => match local_name(&name) {
                "numFmt" => {
                    if let (Some(id_s), Some(code)) =
                        (get_attr(&attrs, "numFmtId"), get_attr(&attrs, "formatCode"))
                        && let Ok(id) = id_s.parse::<u32>()
                    {
                        custom_fmts.insert(id, code.to_string());
                    }
                }
                "cellXfs" => {
                    if !empty {
                        in_cell_xfs = true;
                    }
                }
                "xf" if in_cell_xfs => {
                    let num_fmt_id = get_attr(&attrs, "numFmtId")
                        .and_then(|s| s.parse::<u32>().ok())
                        .unwrap_or(0);
                    cell_xfs_num_fmt_ids.push(num_fmt_id);
                }
                _ => {}
            },
            XmlEvent::End(name) => {
                if local_name(&name) == "cellXfs" {
                    in_cell_xfs = false;
                }
            }
            XmlEvent::Text(_) => {}
        }
    }

    let flags = cell_xfs_num_fmt_ids
        .into_iter()
        .map(|id| {
            is_builtin_date_num_fmt(id)
                || custom_fmts
                    .get(&id)
                    .is_some_and(|code| is_custom_date_format_code(code))
        })
        .collect();
    Ok(flags)
}

// ---------------------------------------------------------------------------
// Worksheet Coordinate Parsing & Cell Representation
// ---------------------------------------------------------------------------

/// Parse an Excel cell coordinate like `"A1"` or `"AB42"` into 0-based column index.
fn parse_col_index(cell_ref: &str) -> Result<usize, String> {
    let mut col: usize = 0;
    let mut letters = 0usize;
    for b in cell_ref.bytes() {
        if b.is_ascii_alphabetic() {
            let v = usize::from(b.to_ascii_uppercase() - b'A') + 1;
            col = col
                .checked_mul(26)
                .and_then(|c| c.checked_add(v))
                .ok_or_else(|| format!("Excel column coordinate `{cell_ref}` overflow"))?;
            letters += 1;
        } else {
            break;
        }
    }
    if letters == 0 {
        return Err(format!("invalid Excel cell coordinate `{cell_ref}`"));
    }
    Ok(col - 1)
}

/// Convert a 0-based column index (`0` -> `"A"`, `26` -> `"AA"`, `27` -> `"AB"`) to Excel letters.
fn col_index_to_letters(mut idx: usize) -> String {
    let mut chars = Vec::new();
    loop {
        let rem = idx % 26;
        chars.push((b'A' + rem as u8) as char);
        if idx < 26 {
            break;
        }
        idx = idx / 26 - 1;
    }
    chars.into_iter().rev().collect()
}

#[derive(Clone, Debug)]
enum XlsxCell {
    Empty,
    Str(String),
    Bool(bool),
    Num(String),
    DateSerial { raw: String, serial: f64 },
    Error(String),
}

impl XlsxCell {
    fn raw_text(&self) -> String {
        match self {
            Self::Empty => String::new(),
            Self::Str(s) | Self::Num(s) | Self::Error(s) => s.clone(),
            Self::Bool(b) => if *b { "true" } else { "false" }.to_string(),
            Self::DateSerial { raw, .. } => raw.clone(),
        }
    }

    fn is_empty(&self) -> bool {
        matches!(self, Self::Empty)
    }
}

struct ParsedRow {
    row_num: usize,
    cells: HashMap<usize, XlsxCell>,
}

fn parse_worksheet_rows(
    xml: &str,
    shared_strings: &[String],
    date_styles: &[bool],
) -> Result<Vec<ParsedRow>, String> {
    let mut tok = XmlTokenizer::new(xml);
    let mut rows = Vec::new();

    let mut in_row = false;
    let mut cur_row_num = 0usize;
    let mut cur_cells: HashMap<usize, XlsxCell> = HashMap::new();
    let mut next_col_idx = 0usize;

    let mut in_cell = false;
    let mut cur_col_idx = 0usize;
    let mut cur_cell_type = String::new();
    let mut cur_style_idx: Option<usize> = None;
    let mut in_v = false;
    let mut in_is = false;
    let mut in_t = false;
    let mut in_rph = false;
    let mut val_buf = String::new();
    let mut has_val = false;

    while let Some(ev) = tok.next_event()? {
        match ev {
            XmlEvent::Start { name, attrs, empty } => match local_name(&name) {
                "row" => {
                    let explicit_r = get_attr(&attrs, "r").and_then(|s| s.parse::<usize>().ok());
                    cur_row_num = explicit_r.unwrap_or(cur_row_num + 1);
                    cur_cells.clear();
                    next_col_idx = 0;
                    if !empty {
                        in_row = true;
                    }
                }
                "c" if in_row => {
                    cur_col_idx = match get_attr(&attrs, "r") {
                        Some(r) => parse_col_index(r)?,
                        None => next_col_idx,
                    };
                    next_col_idx = cur_col_idx + 1;
                    cur_cell_type = get_attr(&attrs, "t").unwrap_or("n").to_string();
                    cur_style_idx = get_attr(&attrs, "s").and_then(|s| s.parse::<usize>().ok());
                    val_buf.clear();
                    has_val = false;
                    in_v = false;
                    in_is = false;
                    in_t = false;
                    in_rph = false;
                    if !empty {
                        in_cell = true;
                    }
                }
                "v" if in_cell && !empty => {
                    in_v = true;
                    has_val = true;
                }
                "is" if in_cell && !empty => {
                    in_is = true;
                }
                "rPh" if in_is && !empty => {
                    in_rph = true;
                }
                "t" if in_is && !in_rph && !empty => {
                    in_t = true;
                    has_val = true;
                }
                _ => {}
            },
            XmlEvent::End(name) => match local_name(&name) {
                "v" => in_v = false,
                "rPh" => in_rph = false,
                "t" => in_t = false,
                "is" => in_is = false,
                "c" if in_cell => {
                    in_cell = false;
                    let cell = build_xlsx_cell(
                        &cur_cell_type,
                        cur_style_idx,
                        has_val,
                        &val_buf,
                        shared_strings,
                        date_styles,
                    )?;
                    if !cell.is_empty() {
                        cur_cells.insert(cur_col_idx, cell);
                    }
                }
                "row" if in_row => {
                    in_row = false;
                    if !cur_cells.is_empty() {
                        rows.push(ParsedRow {
                            row_num: cur_row_num,
                            cells: std::mem::take(&mut cur_cells),
                        });
                    }
                }
                _ => {}
            },
            XmlEvent::Text(text) => {
                if (in_v) || (in_is && in_t && !in_rph) {
                    val_buf.push_str(&text);
                }
            }
        }
    }

    Ok(rows)
}

fn build_xlsx_cell(
    cell_type: &str,
    style_idx: Option<usize>,
    has_val: bool,
    val_buf: &str,
    shared_strings: &[String],
    date_styles: &[bool],
) -> Result<XlsxCell, String> {
    if !has_val && val_buf.is_empty() {
        return Ok(XlsxCell::Empty);
    }
    match cell_type {
        "s" => {
            let idx: usize = val_buf
                .trim()
                .parse()
                .map_err(|_| format!("invalid shared string index `{val_buf}`"))?;
            let s = shared_strings
                .get(idx)
                .ok_or_else(|| format!("shared string index {idx} out of bounds"))?;
            Ok(XlsxCell::Str(s.clone()))
        }
        "inlineStr" | "str" => Ok(XlsxCell::Str(val_buf.to_string())),
        "b" => match val_buf.trim() {
            "1" | "true" | "TRUE" => Ok(XlsxCell::Bool(true)),
            "0" | "false" | "FALSE" => Ok(XlsxCell::Bool(false)),
            other => Ok(XlsxCell::Error(other.to_string())),
        },
        "e" => Ok(XlsxCell::Error(val_buf.to_string())),
        _ => {
            let trimmed = val_buf.trim();
            if trimmed.is_empty() {
                return Ok(XlsxCell::Empty);
            }
            let is_date_style = style_idx
                .and_then(|s| date_styles.get(s).copied())
                .unwrap_or(false);
            if is_date_style && let Ok(serial) = trimmed.parse::<f64>() {
                return Ok(XlsxCell::DateSerial {
                    raw: trimmed.to_string(),
                    serial,
                });
            }
            Ok(XlsxCell::Num(trimmed.to_string()))
        }
    }
}

// ---------------------------------------------------------------------------
// Excel Serial Date/Timestamp & Exact Decimal Conversions
// ---------------------------------------------------------------------------

/// Convert an Excel serial day count to days since `1970-01-01`.
///
/// In the 1900 date system:
/// - `serial >= 61` (1900-03-01 onwards): `serial - 25569`
/// - `1 <= serial <= 59` (1900-01-01..=1900-02-28): `serial - 25568`
/// - `serial == 60` (fictitious Lotus 1900-02-29) or `< 1`: rejected.
#[must_use]
pub fn excel_serial_to_days(serial_whole: i64, date1904: bool) -> Option<i64> {
    if date1904 {
        if serial_whole < 0 {
            return None;
        }
        serial_whole.checked_sub(EXCEL_1904_OFFSET)
    } else if serial_whole >= 61 {
        serial_whole.checked_sub(EXCEL_1900_OFFSET_POST_LEAP)
    } else if (1..=59).contains(&serial_whole) {
        serial_whole.checked_sub(EXCEL_1900_OFFSET_PRE_LEAP)
    } else {
        None
    }
}

/// Convert days since `1970-01-01` to an Excel 1900 serial number (returns `None` for dates before 1900-01-01).
#[must_use]
pub fn days_to_excel_1900_serial(days: i64) -> Option<i64> {
    // 1900-03-01 is -25508; 1900-01-01 is -25567.
    if days >= -25_508 {
        days.checked_add(EXCEL_1900_OFFSET_POST_LEAP)
    } else if days >= -25_567 {
        days.checked_add(EXCEL_1900_OFFSET_PRE_LEAP)
    } else {
        None
    }
}

/// Convert an Excel floating-point serial (whole day + fractional day) to UTC microseconds since Unix epoch.
#[must_use]
pub fn excel_serial_to_micros(serial: f64, date1904: bool) -> Option<i64> {
    if !serial.is_finite() {
        return None;
    }
    let whole_f = serial.floor();
    if whole_f < (i64::MIN as f64) || whole_f > (i64::MAX as f64) {
        return None;
    }
    let whole_serial = whole_f as i64;
    let frac = serial - whole_f;
    let mut day_micros = (frac * (MICROS_PER_DAY as f64)).round() as i64;
    let mut days = excel_serial_to_days(whole_serial, date1904)?;
    if day_micros >= MICROS_PER_DAY {
        days = days.checked_add(1)?;
        day_micros -= MICROS_PER_DAY;
    } else if day_micros < 0 {
        day_micros = 0;
    }
    days.checked_mul(MICROS_PER_DAY)?.checked_add(day_micros)
}

/// Convert UTC microseconds since Unix epoch to an Excel 1900 serial float if lossless round-trip holds.
#[must_use]
pub fn micros_to_excel_1900_serial(micros: i64) -> Option<f64> {
    let days = micros.div_euclid(MICROS_PER_DAY);
    let rem = micros.rem_euclid(MICROS_PER_DAY);
    let serial_whole = days_to_excel_1900_serial(days)?;
    let serial = (serial_whole as f64) + (rem as f64) / (MICROS_PER_DAY as f64);
    if excel_serial_to_micros(serial, false) == Some(micros) {
        Some(serial)
    } else {
        None
    }
}

/// Parse an exact fixed-point decimal string (including scientific notation from Excel `<v>`)
/// into a `10^-18`-scaled [`BigInt`] without passing through IEEE-754 float rounding.
fn parse_decimal_xlsx(raw: &str) -> Result<BigInt, &'static str> {
    let trimmed = raw.trim();
    if trimmed.is_empty() {
        return Err("MissingRequired");
    }
    if !trimmed.contains(['e', 'E']) {
        return parse_decimal_bigint_strict(trimmed).map_err(|_| "BadDecimal");
    }
    // Parse scientific notation: [+-]?int(.frac)?[eE][+-]?exp
    let (neg, rest) = if let Some(r) = trimmed.strip_prefix('-') {
        (true, r)
    } else if let Some(r) = trimmed.strip_prefix('+') {
        (false, r)
    } else {
        (false, trimmed)
    };
    let Some(e_pos) = rest.find(['e', 'E']) else {
        return Err("BadDecimal");
    };
    let mantissa = &rest[..e_pos];
    let exp_str = &rest[e_pos + 1..];
    let exp: i32 = exp_str.parse().map_err(|_| "BadDecimal")?;
    let (int_part, frac_part) = match mantissa.split_once('.') {
        Some((i, f)) => (i, f),
        None => (mantissa, ""),
    };
    if int_part.is_empty()
        || !int_part.bytes().all(|b| b.is_ascii_digit())
        || !frac_part.bytes().all(|b| b.is_ascii_digit())
    {
        return Err("BadDecimal");
    }
    let digits = format!("{int_part}{frac_part}");
    let digits_trimmed = digits.trim_start_matches('0');
    if digits_trimmed.is_empty() {
        return Ok(BigInt::ZERO);
    }
    // Value is digits_val * 10^(exp - frac_part.len()). We need digits_val * 10^(18 + exp - frac_part.len()).
    let frac_len = i32::try_from(frac_part.len()).map_err(|_| "BadDecimal")?;
    let shift = 18i32
        .checked_add(exp)
        .and_then(|v| v.checked_sub(frac_len))
        .ok_or("BadDecimal")?;
    let mut scaled: BigInt = digits_trimmed.parse().map_err(|_| "BadDecimal")?;
    if shift >= 0 {
        if shift > 60 {
            return Err("BadDecimal");
        }
        let mult = pow10_bigint(shift as u32);
        scaled = &scaled * &mult;
    } else {
        let down = (-shift) as u32;
        if down > 60 {
            return Err("BadDecimal");
        }
        let div = pow10_bigint(down);
        let Some((q, r)) = scaled.div_rem_euclid(&div) else {
            return Err("BadDecimal");
        };
        if !r.is_zero() {
            return Err("BadDecimal");
        }
        scaled = q;
    }
    if neg {
        scaled = -scaled;
    }
    if scaled < BigInt::from(DEC_MIN) || scaled > BigInt::from(DEC_MAX) {
        return Err("BadDecimal");
    }
    Ok(scaled)
}

fn pow10_bigint(exp: u32) -> BigInt {
    let mut acc = BigInt::one();
    let ten = BigInt::from(10i64);
    for _ in 0..exp {
        acc = &acc * &ten;
    }
    acc
}

fn parse_int_xlsx(raw: &str) -> Result<i64, &'static str> {
    let trimmed = raw.trim();
    if trimmed.is_empty() {
        return Err("MissingRequired");
    }
    if let Ok(n) = trimmed.parse::<i64>() {
        return Ok(n);
    }
    // Excel often stores integers as `42.0` or `1E+3`; verify exact integer via decimal parser.
    let dec = parse_decimal_xlsx(trimmed).map_err(|_| "BadInt")?;
    let scale = BigInt::from(crate::core::bigint::DEC_SCALE);
    let Some((q, r)) = dec.div_rem_euclid(&scale) else {
        return Err("BadInt");
    };
    if !r.is_zero() {
        return Err("BadInt");
    }
    q.to_i64().ok_or("BadInt")
}

fn parse_xlsx_cell(cell: &XlsxCell, ty: &ScalarTy, date1904: bool) -> Result<Val, &'static str> {
    if let ScalarTy::Option(inner) = ty {
        return match cell {
            XlsxCell::Empty => Ok(Val::OptNone),
            XlsxCell::Str(s) if s.trim().is_empty() => Ok(Val::OptNone),
            other => Ok(Val::OptSome(Box::new(parse_xlsx_cell(
                other, inner, date1904,
            )?))),
        };
    }

    match ty {
        ScalarTy::Option(_) => Err("UnsupportedCellType"),
        ScalarTy::Text => match cell {
            XlsxCell::Empty => Ok(Val::Text(String::new())),
            XlsxCell::Str(s) | XlsxCell::Num(s) => Ok(Val::Text(s.clone())),
            XlsxCell::Bool(b) => Ok(Val::Text(if *b { "true" } else { "false" }.to_string())),
            XlsxCell::DateSerial { raw, .. } => Ok(Val::Text(raw.clone())),
            XlsxCell::Error(_) => Err("ExcelError"),
        },
        ScalarTy::Bool => match cell {
            XlsxCell::Empty => Err("MissingRequired"),
            XlsxCell::Bool(b) => Ok(Val::Bool(*b)),
            XlsxCell::Num(s) | XlsxCell::Str(s) => match s.trim().to_ascii_lowercase().as_str() {
                "true" | "1" | "1.0" | "yes" => Ok(Val::Bool(true)),
                "false" | "0" | "0.0" | "no" => Ok(Val::Bool(false)),
                "" => Err("MissingRequired"),
                _ => Err("BadBool"),
            },
            XlsxCell::DateSerial { .. } | XlsxCell::Error(_) => Err("BadBool"),
        },
        ScalarTy::Int => match cell {
            XlsxCell::Empty => Err("MissingRequired"),
            XlsxCell::Num(s) | XlsxCell::Str(s) => Ok(Val::Int(BigInt::from(parse_int_xlsx(s)?))),
            XlsxCell::DateSerial { raw, .. } => Ok(Val::Int(BigInt::from(parse_int_xlsx(raw)?))),
            XlsxCell::Bool(_) | XlsxCell::Error(_) => Err("BadInt"),
        },
        ScalarTy::Decimal => match cell {
            XlsxCell::Empty => Err("MissingRequired"),
            XlsxCell::Num(s) | XlsxCell::Str(s) => Ok(Val::Decimal(parse_decimal_xlsx(s)?)),
            XlsxCell::DateSerial { raw, .. } => Ok(Val::Decimal(parse_decimal_xlsx(raw)?)),
            XlsxCell::Bool(_) | XlsxCell::Error(_) => Err("BadDecimal"),
        },
        ScalarTy::Float => match cell {
            XlsxCell::Empty => Err("MissingRequired"),
            XlsxCell::Num(s) | XlsxCell::Str(s) => {
                let trimmed = s.trim();
                if trimmed.is_empty() {
                    return Err("MissingRequired");
                }
                let f: f64 = trimmed.parse().map_err(|_| "BadFloat")?;
                if !f.is_finite() {
                    return Err("BadFloat");
                }
                Ok(Val::Float(Float64::from_f64(f)))
            }
            XlsxCell::DateSerial { serial, .. } => {
                if !serial.is_finite() {
                    return Err("BadFloat");
                }
                Ok(Val::Float(Float64::from_f64(*serial)))
            }
            XlsxCell::Bool(_) | XlsxCell::Error(_) => Err("BadFloat"),
        },
        ScalarTy::Date => match cell {
            XlsxCell::Empty => Err("MissingRequired"),
            XlsxCell::DateSerial { serial, .. } => {
                if !serial.is_finite() {
                    return Err("BadDate");
                }
                let whole = serial.floor() as i64;
                let days = excel_serial_to_days(whole, date1904).ok_or("BadDate")?;
                Ok(Val::Date(BigInt::from(days)))
            }
            XlsxCell::Num(s) => {
                let serial: f64 = s.trim().parse().map_err(|_| "BadDate")?;
                if !serial.is_finite() {
                    return Err("BadDate");
                }
                let whole = serial.floor() as i64;
                let days = excel_serial_to_days(whole, date1904).ok_or("BadDate")?;
                Ok(Val::Date(BigInt::from(days)))
            }
            XlsxCell::Str(s) => {
                let trimmed = s.trim();
                if trimmed.is_empty() {
                    return Err("MissingRequired");
                }
                let days = parse_iso_date(trimmed).map_err(|_| "BadDate")?;
                Ok(Val::Date(BigInt::from(days)))
            }
            XlsxCell::Bool(_) | XlsxCell::Error(_) => Err("BadDate"),
        },
        ScalarTy::Timestamp => match cell {
            XlsxCell::Empty => Err("MissingRequired"),
            XlsxCell::DateSerial { serial, .. } => {
                let us = excel_serial_to_micros(*serial, date1904).ok_or("BadTimestamp")?;
                Ok(Val::Timestamp(BigInt::from(us)))
            }
            XlsxCell::Num(s) => {
                let serial: f64 = s.trim().parse().map_err(|_| "BadTimestamp")?;
                let us = excel_serial_to_micros(serial, date1904).ok_or("BadTimestamp")?;
                Ok(Val::Timestamp(BigInt::from(us)))
            }
            XlsxCell::Str(s) => {
                let trimmed = s.trim();
                if trimmed.is_empty() {
                    return Err("MissingRequired");
                }
                let us = parse_iso_timestamp(trimmed).map_err(|_| "BadTimestamp")?;
                Ok(Val::Timestamp(BigInt::from(us)))
            }
            XlsxCell::Bool(_) | XlsxCell::Error(_) => Err("BadTimestamp"),
        },
        ScalarTy::Duration => match cell {
            XlsxCell::Empty => Err("MissingRequired"),
            XlsxCell::Num(s) | XlsxCell::Str(s) => {
                let us = parse_int_xlsx(s).map_err(|_| "BadDuration")?;
                Ok(Val::Duration(BigInt::from(us)))
            }
            XlsxCell::DateSerial { .. } | XlsxCell::Bool(_) | XlsxCell::Error(_) => {
                Err("BadDuration")
            }
        },
        ScalarTy::Bytes => match cell {
            XlsxCell::Empty => Ok(Val::Bytes(Vec::new())),
            XlsxCell::Str(s) => Ok(Val::Bytes(s.as_bytes().to_vec())),
            _ => Err("TypeMismatch"),
        },
        ScalarTy::Unit => Ok(Val::Unit),
        ScalarTy::Data(_) => Err("UnsupportedCellType"),
    }
}

// ---------------------------------------------------------------------------
// Public XLSX Reader API
// ---------------------------------------------------------------------------

/// Read an OOXML `.xlsx` workbook from raw bytes with quarantine-first schema validation.
///
/// Matches `sheet` by exact worksheet name (defaulting to the first sheet when `None`),
/// enforces per-column `where` constraints via `check_constraint`, and returns
/// `(valid_rows, bad_rows)` where `bad_rows` carries privacy tags per `quarantine_bad_row_table_ty`.
///
/// # Errors
/// Returns an error string on ZIP corruption/traversal/zip-bomb, XXE/DTD XML rejection,
/// missing worksheet, or missing required header columns.
pub fn read_xlsx_bytes_with_schema<F>(
    bytes: &[u8],
    sheet: Option<&str>,
    schema: &TableTy,
    mut check_constraint: F,
) -> Result<(TableVal, TableVal), String>
where
    F: FnMut(usize, &Val) -> bool,
{
    let archive = ZipArchive::from_bytes(bytes).map_err(|e| e.to_string())?;
    let wb_bytes = archive
        .get_case_insensitive("xl/workbook.xml")
        .ok_or_else(|| "missing `xl/workbook.xml` in XLSX archive".to_string())?;
    let wb_xml = std::str::from_utf8(wb_bytes)
        .map_err(|_| "`xl/workbook.xml` is not valid UTF-8".to_string())?;
    let wb = parse_workbook_xml(wb_xml)?;

    let target_sheet = match sheet {
        Some(req) => wb
            .sheets
            .iter()
            .find(|s| s.name == req)
            .ok_or_else(|| format!("worksheet `{req}` not found in workbook"))?,
        None => wb
            .sheets
            .first()
            .ok_or_else(|| "XLSX workbook contains no worksheets".to_string())?,
    };

    let rels_bytes = archive
        .get_case_insensitive("xl/_rels/workbook.xml.rels")
        .ok_or_else(|| "missing `xl/_rels/workbook.xml.rels` in XLSX archive".to_string())?;
    let rels_xml = std::str::from_utf8(rels_bytes)
        .map_err(|_| "`xl/_rels/workbook.xml.rels` is not valid UTF-8".to_string())?;
    let rels = parse_workbook_rels(rels_xml)?;

    let rel_target = rels.get(&target_sheet.rel_id).ok_or_else(|| {
        format!(
            "missing relationship `{}` for worksheet `{}`",
            target_sheet.rel_id, target_sheet.name
        )
    })?;
    let sheet_path = resolve_xl_target(rel_target)?;
    let sheet_bytes = archive.get_case_insensitive(&sheet_path).ok_or_else(|| {
        format!(
            "worksheet XML `{sheet_path}` for `{}` not found in archive",
            target_sheet.name
        )
    })?;
    let sheet_xml = std::str::from_utf8(sheet_bytes)
        .map_err(|_| format!("`{sheet_path}` is not valid UTF-8"))?;

    let shared_strings =
        if let Some(ss_bytes) = archive.get_case_insensitive("xl/sharedStrings.xml") {
            let ss_xml = std::str::from_utf8(ss_bytes)
                .map_err(|_| "`xl/sharedStrings.xml` is not valid UTF-8".to_string())?;
            parse_shared_strings(ss_xml)?
        } else {
            Vec::new()
        };

    let date_styles = if let Some(st_bytes) = archive.get_case_insensitive("xl/styles.xml") {
        let st_xml = std::str::from_utf8(st_bytes)
            .map_err(|_| "`xl/styles.xml` is not valid UTF-8".to_string())?;
        parse_date_style_flags(st_xml)?
    } else {
        Vec::new()
    };

    let parsed_rows = parse_worksheet_rows(sheet_xml, &shared_strings, &date_styles)?;
    let bad_tt = quarantine_bad_row_table_ty(schema);

    let Some((header_row, data_rows)) = parsed_rows.split_first() else {
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

    let mut header_map: HashMap<String, usize> = HashMap::new();
    for (&col_idx, cell) in &header_row.cells {
        let name = cell.raw_text().trim().to_string();
        if !name.is_empty() {
            header_map.entry(name).or_insert(col_idx);
        }
    }

    let mut col_indices = Vec::with_capacity(schema.cols.len());
    for col in &schema.cols {
        let Some(&idx) = header_map.get(col.name.as_str()) else {
            return Err(format!(
                "missing required XLSX column `{}` in worksheet `{}`",
                col.name, target_sheet.name
            ));
        };
        col_indices.push(idx);
    }

    let mut good_rows = Vec::new();
    let mut bad_rows = Vec::new();

    for row in data_rows {
        let mut cells = Vec::with_capacity(schema.cols.len());
        let mut bad_hit: Option<(&str, &str, String)> = None;

        for (ci, col) in schema.cols.iter().enumerate() {
            let xlsx_col = col_indices[ci];
            let raw_cell = row.cells.get(&xlsx_col).unwrap_or(&XlsxCell::Empty);
            match parse_xlsx_cell(raw_cell, &col.ty, wb.date1904) {
                Ok(val) => {
                    let inner_ok = match &val {
                        Val::OptNone => true,
                        Val::OptSome(inner) => check_constraint(ci, inner),
                        other => check_constraint(ci, other),
                    };
                    if !inner_ok {
                        bad_hit =
                            Some((col.name.as_str(), "ConstraintFailed", raw_cell.raw_text()));
                        break;
                    }
                    cells.push(val);
                }
                Err(kind) => {
                    bad_hit = Some((col.name.as_str(), kind, raw_cell.raw_text()));
                    break;
                }
            }
        }

        if let Some((col_name, err_kind, raw_val)) = bad_hit {
            let mut raw_row = String::new();
            for (ci, _) in schema.cols.iter().enumerate() {
                if ci > 0 {
                    raw_row.push(',');
                }
                if let Some(c) = row.cells.get(&col_indices[ci]) {
                    raw_row.push_str(&c.raw_text());
                }
            }
            bad_rows.push(TableRow {
                cells: vec![
                    Val::Int(BigInt::from(row.row_num)),
                    Val::Text(col_name.to_string()),
                    Val::Text(err_kind.to_string()),
                    Val::Text(raw_val),
                    Val::Text(raw_row),
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

/// Read an OOXML `.xlsx` file from disk with quarantine-first schema validation.
///
/// # Errors
/// Returns an error string on filesystem I/O, ZIP/XML validation, missing sheet, or missing column.
pub fn read_xlsx_file_with_schema<F>(
    path: &Path,
    sheet: Option<&str>,
    schema: &TableTy,
    check_constraint: F,
) -> Result<(TableVal, TableVal), String>
where
    F: FnMut(usize, &Val) -> bool,
{
    let bytes = fs::read(path).map_err(|e| format!("{}: {e}", path.display()))?;
    read_xlsx_bytes_with_schema(&bytes, sheet, schema, check_constraint)
}

// ---------------------------------------------------------------------------
// Public XLSX Writer API
// ---------------------------------------------------------------------------

/// Encode one or more named [`TableVal`] sheets into a valid OOXML `.xlsx` workbook.
///
/// Produces `[Content_Types].xml`, `_rels/.rels`, `xl/workbook.xml`,
/// `xl/_rels/workbook.xml.rels`, `xl/styles.xml`, and `xl/worksheets/sheetN.xml`
/// with bold header rows, typed numeric/boolean/string cells, and styled Excel 1900 serial
/// dates & timestamps that round-trip losslessly through [`read_xlsx_bytes_with_schema`].
///
/// # Errors
/// Returns an error string if `sheets` is empty, sheet names are invalid/duplicated, or ZIP encoding fails.
pub fn write_xlsx_sheets(sheets: &[(String, TableVal)]) -> Result<Vec<u8>, String> {
    if sheets.is_empty() {
        return Err("cannot write XLSX workbook with zero sheets".to_string());
    }
    let mut seen_names = Vec::with_capacity(sheets.len());
    for (name, _) in sheets {
        if name.is_empty() || name.len() > 31 {
            return Err(format!(
                "invalid XLSX sheet name `{name}` (must be 1..=31 characters)"
            ));
        }
        if name
            .chars()
            .any(|c| matches!(c, '\\' | '/' | '?' | '*' | '[' | ']' | ':'))
        {
            return Err(format!(
                "invalid XLSX sheet name `{name}` (contains forbidden character)"
            ));
        }
        if seen_names
            .iter()
            .any(|n: &String| n.eq_ignore_ascii_case(name))
        {
            return Err(format!("duplicate XLSX sheet name `{name}`"));
        }
        seen_names.push(name.clone());
    }

    let content_types = build_content_types_xml(sheets.len());
    let root_rels = build_root_rels_xml();
    let workbook_xml = build_workbook_xml(sheets);
    let wb_rels_xml = build_workbook_rels_xml(sheets.len());
    let styles_xml = build_styles_xml();

    let mut sheet_xmls: Vec<(String, Vec<u8>)> = Vec::with_capacity(sheets.len());
    for (idx, (_, tv)) in sheets.iter().enumerate() {
        let path = format!("xl/worksheets/sheet{}.xml", idx + 1);
        let xml = build_worksheet_xml(tv);
        sheet_xmls.push((path, xml.into_bytes()));
    }

    let mut entries: Vec<(&str, &[u8])> = Vec::with_capacity(5 + sheet_xmls.len());
    entries.push(("[Content_Types].xml", content_types.as_bytes()));
    entries.push(("_rels/.rels", root_rels.as_bytes()));
    entries.push(("xl/workbook.xml", workbook_xml.as_bytes()));
    entries.push(("xl/_rels/workbook.xml.rels", wb_rels_xml.as_bytes()));
    entries.push(("xl/styles.xml", styles_xml.as_bytes()));
    for (path, bytes) in &sheet_xmls {
        entries.push((path.as_str(), bytes.as_slice()));
    }

    write_zip_bytes(&entries, ZipCompression::Deflated).map_err(|e| e.to_string())
}

/// Write one or more named [`TableVal`] sheets to an `.xlsx` file on disk.
///
/// # Errors
/// Returns an error string on validation, ZIP encoding, or filesystem write failure.
pub fn write_xlsx_file(path: &Path, sheets: &[(String, TableVal)]) -> Result<(), String> {
    let bytes = write_xlsx_sheets(sheets)?;
    fs::write(path, bytes).map_err(|e| format!("{}: {e}", path.display()))
}

fn build_content_types_xml(num_sheets: usize) -> String {
    let mut xml = String::from(
        "<?xml version=\"1.0\" encoding=\"UTF-8\" standalone=\"yes\"?>\n\
         <Types xmlns=\"http://schemas.openxmlformats.org/package/2006/content-types\">\
         <Default Extension=\"rels\" ContentType=\"application/vnd.openxmlformats-package.relationships+xml\"/>\
         <Default Extension=\"xml\" ContentType=\"application/xml\"/>\
         <Override PartName=\"/xl/workbook.xml\" ContentType=\"application/vnd.openxmlformats-officedocument.spreadsheetml.sheet.main+xml\"/>\
         <Override PartName=\"/xl/styles.xml\" ContentType=\"application/vnd.openxmlformats-officedocument.spreadsheetml.styles+xml\"/>",
    );
    for i in 1..=num_sheets {
        let _ = write!(
            xml,
            "<Override PartName=\"/xl/worksheets/sheet{i}.xml\" ContentType=\"application/vnd.openxmlformats-officedocument.spreadsheetml.worksheet+xml\"/>"
        );
    }
    xml.push_str("</Types>");
    xml
}

fn build_root_rels_xml() -> String {
    String::from(
        "<?xml version=\"1.0\" encoding=\"UTF-8\" standalone=\"yes\"?>\n\
         <Relationships xmlns=\"http://schemas.openxmlformats.org/package/2006/relationships\">\
         <Relationship Id=\"rId1\" Type=\"http://schemas.openxmlformats.org/officeDocument/2006/relationships/officeDocument\" Target=\"xl/workbook.xml\"/>\
         </Relationships>",
    )
}

fn build_workbook_xml(sheets: &[(String, TableVal)]) -> String {
    let mut xml = String::from(
        "<?xml version=\"1.0\" encoding=\"UTF-8\" standalone=\"yes\"?>\n\
         <workbook xmlns=\"http://schemas.openxmlformats.org/spreadsheetml/2006/main\" \
         xmlns:r=\"http://schemas.openxmlformats.org/officeDocument/2006/relationships\"><sheets>",
    );
    for (idx, (name, _)) in sheets.iter().enumerate() {
        let sheet_id = idx + 1;
        xml.push_str("<sheet name=\"");
        push_xml_escaped(&mut xml, name);
        let _ = write!(xml, "\" sheetId=\"{sheet_id}\" r:id=\"rId{sheet_id}\"/>");
    }
    xml.push_str("</sheets></workbook>");
    xml
}

fn build_workbook_rels_xml(num_sheets: usize) -> String {
    let mut xml = String::from(
        "<?xml version=\"1.0\" encoding=\"UTF-8\" standalone=\"yes\"?>\n\
         <Relationships xmlns=\"http://schemas.openxmlformats.org/package/2006/relationships\">",
    );
    for i in 1..=num_sheets {
        let _ = write!(
            xml,
            "<Relationship Id=\"rId{i}\" Type=\"http://schemas.openxmlformats.org/officeDocument/2006/relationships/worksheet\" Target=\"worksheets/sheet{i}.xml\"/>"
        );
    }
    let style_rid = num_sheets + 1;
    let _ = write!(
        xml,
        "<Relationship Id=\"rId{style_rid}\" Type=\"http://schemas.openxmlformats.org/officeDocument/2006/relationships/styles\" Target=\"styles.xml\"/>\
         </Relationships>"
    );
    xml
}

fn build_styles_xml() -> String {
    String::from(
        "<?xml version=\"1.0\" encoding=\"UTF-8\" standalone=\"yes\"?>\n\
         <styleSheet xmlns=\"http://schemas.openxmlformats.org/spreadsheetml/2006/main\">\
         <numFmts count=\"2\">\
         <numFmt numFmtId=\"164\" formatCode=\"yyyy-mm-dd\"/>\
         <numFmt numFmtId=\"165\" formatCode=\"yyyy-mm-dd hh:mm:ss\"/>\
         </numFmts>\
         <fonts count=\"2\">\
         <font><sz val=\"11\"/><name val=\"Calibri\"/></font>\
         <font><b/><sz val=\"11\"/><name val=\"Calibri\"/></font>\
         </fonts>\
         <fills count=\"2\">\
         <fill><patternFill patternType=\"none\"/></fill>\
         <fill><patternFill patternType=\"gray125\"/></fill>\
         </fills>\
         <borders count=\"1\"><border><left/><right/><top/><bottom/><diagonal/></border></borders>\
         <cellStyleXfs count=\"1\"><xf numFmtId=\"0\" fontId=\"0\" fillId=\"0\" borderId=\"0\"/></cellStyleXfs>\
         <cellXfs count=\"4\">\
         <xf numFmtId=\"0\" fontId=\"0\" fillId=\"0\" borderId=\"0\" xfId=\"0\"/>\
         <xf numFmtId=\"0\" fontId=\"1\" fillId=\"0\" borderId=\"0\" xfId=\"0\" applyFont=\"1\"/>\
         <xf numFmtId=\"164\" fontId=\"0\" fillId=\"0\" borderId=\"0\" xfId=\"0\" applyNumberFormat=\"1\"/>\
         <xf numFmtId=\"165\" fontId=\"0\" fillId=\"0\" borderId=\"0\" xfId=\"0\" applyNumberFormat=\"1\"/>\
         </cellXfs>\
         </styleSheet>",
    )
}

fn build_worksheet_xml(tv: &TableVal) -> String {
    let mut xml = String::from(
        "<?xml version=\"1.0\" encoding=\"UTF-8\" standalone=\"yes\"?>\n\
         <worksheet xmlns=\"http://schemas.openxmlformats.org/spreadsheetml/2006/main\"><sheetData>",
    );

    // Row 1: bold headers (style index 1)
    xml.push_str("<row r=\"1\">");
    for (ci, col) in tv.cols.iter().enumerate() {
        let coord = format!("{}1", col_index_to_letters(ci));
        let _ = write!(xml, "<c r=\"{coord}\" t=\"inlineStr\" s=\"1\"><is><t>");
        push_xml_escaped(&mut xml, &col.name);
        xml.push_str("</t></is></c>");
    }
    xml.push_str("</row>");

    // Data rows (2..)
    for (ri, row) in tv.rows.iter().enumerate() {
        let excel_row = ri + 2;
        let _ = write!(xml, "<row r=\"{excel_row}\">");
        for (ci, cell) in row.cells.iter().enumerate() {
            let coord = format!("{}{excel_row}", col_index_to_letters(ci));
            write_xlsx_cell(&mut xml, &coord, cell);
        }
        xml.push_str("</row>");
    }

    xml.push_str("</sheetData></worksheet>");
    xml
}

fn write_xlsx_cell(xml: &mut String, coord: &str, val: &Val) {
    let mut cur = val;
    while let Val::OptSome(inner) = cur {
        cur = inner;
    }
    match cur {
        Val::OptNone | Val::Unit => {}
        Val::Bool(b) => {
            let bit = if *b { '1' } else { '0' };
            let _ = write!(xml, "<c r=\"{coord}\" t=\"b\"><v>{bit}</v></c>");
        }
        Val::Int(n) => {
            let _ = write!(xml, "<c r=\"{coord}\"><v>{n}</v></c>");
        }
        Val::Decimal(d) => {
            let s = render_decimal(d);
            let _ = write!(xml, "<c r=\"{coord}\"><v>{s}</v></c>");
        }
        Val::Float(f) => {
            let fv = f.to_f64();
            if fv.is_finite() {
                let _ = write!(xml, "<c r=\"{coord}\"><v>{fv}</v></c>");
            }
        }
        Val::Date(d) => {
            if let Some(days) = d.to_i64() {
                if let Some(serial) = days_to_excel_1900_serial(days) {
                    let _ = write!(xml, "<c r=\"{coord}\" s=\"2\"><v>{serial}</v></c>");
                } else {
                    write_inline_str(xml, coord, &format_iso_date(days));
                }
            }
        }
        Val::Timestamp(ts) => {
            if let Some(us) = ts.to_i64() {
                if let Some(serial) = micros_to_excel_1900_serial(us) {
                    let _ = write!(xml, "<c r=\"{coord}\" s=\"3\"><v>{serial}</v></c>");
                } else {
                    write_inline_str(xml, coord, &format_iso_timestamp(us));
                }
            }
        }
        Val::Duration(us) => {
            let _ = write!(xml, "<c r=\"{coord}\"><v>{us}</v></c>");
        }
        Val::Text(s) => {
            write_inline_str(xml, coord, s);
        }
        Val::Bytes(bs) => match std::str::from_utf8(bs) {
            Ok(s) => write_inline_str(xml, coord, s),
            Err(_) => write_inline_str(xml, coord, &to_hex_lower(bs)),
        },
        other => {
            write_inline_str(xml, coord, &crate::oracle::value::render_public_val(other));
        }
    }
}

fn write_inline_str(xml: &mut String, coord: &str, text: &str) {
    let preserve = text.starts_with(char::is_whitespace) || text.ends_with(char::is_whitespace);
    if preserve {
        let _ = write!(
            xml,
            "<c r=\"{coord}\" t=\"inlineStr\"><is><t xml:space=\"preserve\">"
        );
    } else {
        let _ = write!(xml, "<c r=\"{coord}\" t=\"inlineStr\"><is><t>");
    }
    push_xml_escaped(xml, text);
    xml.push_str("</t></is></c>");
}
