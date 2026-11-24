//! Strict RFC 8259 iterative (O(1)-stack) JSON parser & serializer and streaming JSONL
//! schema-validated quarantine reader/writer.

use std::fmt::{self, Write as _};
use std::io::{self, BufRead, BufReader, Cursor, Read, Write};

use crate::core::bigint::BigInt;
use crate::core::check::quarantine_bad_row_table_ty;
use crate::core::syntax::{Float64, ScalarTy, TableTy};
use crate::formats::time::{
    format_iso_date, format_iso_timestamp, parse_decimal_bigint, parse_iso_date,
    parse_iso_timestamp,
};
use crate::oracle::value::{TableRow, TableVal, Val, render_public_val};

/// Maximum JSON container nesting depth (prevents pathological inputs without overflowing stack).
pub const MAX_JSON_DEPTH: usize = 256;
/// Default streaming batch size for JSONL record iteration.
pub const JSONL_BATCH_SIZE: usize = 2048;

/// Typed error for strict RFC 8259 JSON parsing.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct JsonError {
    pub message: String,
    pub offset: usize,
}

impl JsonError {
    #[must_use]
    pub fn new(message: impl Into<String>, offset: usize) -> Self {
        Self {
            message: message.into(),
            offset,
        }
    }
}

impl fmt::Display for JsonError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} at byte {}", self.message, self.offset)
    }
}

impl std::error::Error for JsonError {}

/// Strict RFC 8259 JSON value preserving exact numeric lexemes (`Number(String)`) so Dana's
/// 18-digit fixed-point `Decimal` values never suffer IEEE-754 rounding loss.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum JsonValue {
    Null,
    Bool(bool),
    /// Validated RFC 8259 number lexeme (exact representation for `Int`, `Decimal`, and `Float`).
    Number(String),
    Str(String),
    Array(Vec<JsonValue>),
    Object(Vec<(String, JsonValue)>),
}

impl Drop for JsonValue {
    fn drop(&mut self) {
        let mut stack = Vec::new();
        match self {
            Self::Array(xs) => stack.extend(std::mem::take(xs)),
            Self::Object(kvs) => {
                for (_, v) in std::mem::take(kvs) {
                    stack.push(v);
                }
            }
            _ => return,
        }
        while let Some(mut node) = stack.pop() {
            match &mut node {
                Self::Array(xs) => stack.extend(std::mem::take(xs)),
                Self::Object(kvs) => {
                    for (_, v) in std::mem::take(kvs) {
                        stack.push(v);
                    }
                }
                _ => {}
            }
        }
    }
}

impl JsonValue {
    #[must_use]
    pub fn as_str(&self) -> Option<&str> {
        match self {
            Self::Str(s) => Some(s.as_str()),
            _ => None,
        }
    }

    #[must_use]
    pub fn as_i64(&self) -> Option<i64> {
        match self {
            Self::Number(raw) => raw.parse::<i64>().ok(),
            _ => None,
        }
    }

    #[must_use]
    pub fn as_f64(&self) -> Option<f64> {
        match self {
            Self::Number(raw) => {
                let f = raw.parse::<f64>().ok()?;
                if f.is_finite() { Some(f) } else { None }
            }
            _ => None,
        }
    }

    #[must_use]
    pub fn as_decimal(&self) -> Option<BigInt> {
        match self {
            Self::Number(raw) | Self::Str(raw) => parse_decimal_bigint(raw).ok(),
            _ => None,
        }
    }

    #[must_use]
    pub fn as_object(&self) -> Option<&[(String, JsonValue)]> {
        match self {
            Self::Object(kvs) => Some(kvs.as_slice()),
            _ => None,
        }
    }

    #[must_use]
    pub fn get(&self, key: &str) -> Option<&JsonValue> {
        // Last key wins per common JSON convention if duplicate keys occur in input.
        self.as_object()?
            .iter()
            .rev()
            .find(|(k, _)| k == key)
            .map(|(_, v)| v)
    }
}

enum ContainerFrame {
    Array(Vec<JsonValue>),
    Object {
        entries: Vec<(String, JsonValue)>,
        pending_key: Option<String>,
    },
}

/// Strictly parse an RFC 8259 JSON document iteratively in O(1) call stack.
///
/// # Errors
/// Returns [`JsonError`] on malformed syntax, invalid escapes, excessive nesting (>256),
/// or trailing non-whitespace bytes.
pub fn parse_json(input: &str) -> Result<JsonValue, JsonError> {
    let bytes = input.as_bytes();
    let mut pos = 0usize;
    let mut stack: Vec<ContainerFrame> = Vec::new();

    #[derive(Clone, Copy, PartialEq, Eq)]
    enum Expect {
        Value,
        AfterValue,
    }
    let mut expect = Expect::Value;
    let mut root_val: Option<JsonValue> = None;

    loop {
        skip_ws(bytes, &mut pos);
        match expect {
            Expect::Value => {
                let Some(&b) = bytes.get(pos) else {
                    return Err(JsonError::new("unexpected end of JSON input", pos));
                };
                match b {
                    b'[' => {
                        if stack.len() >= MAX_JSON_DEPTH {
                            return Err(JsonError::new(
                                format!("maximum JSON nesting depth ({MAX_JSON_DEPTH}) exceeded"),
                                pos,
                            ));
                        }
                        pos += 1;
                        skip_ws(bytes, &mut pos);
                        if bytes.get(pos) == Some(&b']') {
                            pos += 1;
                            let val = JsonValue::Array(Vec::new());
                            attach_json_value(&mut stack, &mut root_val, val)?;
                            expect = Expect::AfterValue;
                        } else {
                            stack.push(ContainerFrame::Array(Vec::new()));
                            expect = Expect::Value;
                        }
                    }
                    b'{' => {
                        if stack.len() >= MAX_JSON_DEPTH {
                            return Err(JsonError::new(
                                format!("maximum JSON nesting depth ({MAX_JSON_DEPTH}) exceeded"),
                                pos,
                            ));
                        }
                        pos += 1;
                        skip_ws(bytes, &mut pos);
                        if bytes.get(pos) == Some(&b'}') {
                            pos += 1;
                            let val = JsonValue::Object(Vec::new());
                            attach_json_value(&mut stack, &mut root_val, val)?;
                            expect = Expect::AfterValue;
                        } else {
                            if bytes.get(pos) != Some(&b'"') {
                                return Err(JsonError::new(
                                    "expected string key in JSON object",
                                    pos,
                                ));
                            }
                            let key = parse_json_string(input, &mut pos)?;
                            skip_ws(bytes, &mut pos);
                            if bytes.get(pos) != Some(&b':') {
                                return Err(JsonError::new(
                                    "expected `:` after JSON object key",
                                    pos,
                                ));
                            }
                            pos += 1;
                            stack.push(ContainerFrame::Object {
                                entries: Vec::new(),
                                pending_key: Some(key),
                            });
                            expect = Expect::Value;
                        }
                    }
                    b'"' => {
                        let s = parse_json_string(input, &mut pos)?;
                        attach_json_value(&mut stack, &mut root_val, JsonValue::Str(s))?;
                        expect = Expect::AfterValue;
                    }
                    b't' => {
                        if bytes.get(pos..pos + 4) == Some(b"true") {
                            pos += 4;
                            attach_json_value(&mut stack, &mut root_val, JsonValue::Bool(true))?;
                            expect = Expect::AfterValue;
                        } else {
                            return Err(JsonError::new("invalid literal", pos));
                        }
                    }
                    b'f' => {
                        if bytes.get(pos..pos + 5) == Some(b"false") {
                            pos += 5;
                            attach_json_value(&mut stack, &mut root_val, JsonValue::Bool(false))?;
                            expect = Expect::AfterValue;
                        } else {
                            return Err(JsonError::new("invalid literal", pos));
                        }
                    }
                    b'n' => {
                        if bytes.get(pos..pos + 4) == Some(b"null") {
                            pos += 4;
                            attach_json_value(&mut stack, &mut root_val, JsonValue::Null)?;
                            expect = Expect::AfterValue;
                        } else {
                            return Err(JsonError::new("invalid literal", pos));
                        }
                    }
                    b'-' | b'0'..=b'9' => {
                        let num = parse_json_number(input, &mut pos)?;
                        attach_json_value(&mut stack, &mut root_val, JsonValue::Number(num))?;
                        expect = Expect::AfterValue;
                    }
                    _ => {
                        return Err(JsonError::new(
                            format!("unexpected byte `{}` in JSON", b as char),
                            pos,
                        ));
                    }
                }
            }
            Expect::AfterValue => {
                if stack.is_empty() {
                    if pos < bytes.len() {
                        return Err(JsonError::new("trailing characters after JSON value", pos));
                    }
                    return root_val.ok_or_else(|| JsonError::new("missing root JSON value", pos));
                }
                let Some(&b) = bytes.get(pos) else {
                    return Err(JsonError::new("unterminated JSON container", pos));
                };
                match stack.last_mut() {
                    Some(ContainerFrame::Array(_)) => match b {
                        b',' => {
                            pos += 1;
                            expect = Expect::Value;
                        }
                        b']' => {
                            pos += 1;
                            let Some(ContainerFrame::Array(elems)) = stack.pop() else {
                                return Err(JsonError::new("JSON parser stack mismatch", pos));
                            };
                            attach_json_value(&mut stack, &mut root_val, JsonValue::Array(elems))?;
                            expect = Expect::AfterValue;
                        }
                        _ => {
                            return Err(JsonError::new("expected `,` or `]` in JSON array", pos));
                        }
                    },
                    Some(ContainerFrame::Object { pending_key, .. }) => match b {
                        b',' => {
                            pos += 1;
                            skip_ws(bytes, &mut pos);
                            if bytes.get(pos) != Some(&b'"') {
                                return Err(JsonError::new(
                                    "expected string key after `,` in JSON object",
                                    pos,
                                ));
                            }
                            let key = parse_json_string(input, &mut pos)?;
                            skip_ws(bytes, &mut pos);
                            if bytes.get(pos) != Some(&b':') {
                                return Err(JsonError::new(
                                    "expected `:` after JSON object key",
                                    pos,
                                ));
                            }
                            pos += 1;
                            *pending_key = Some(key);
                            expect = Expect::Value;
                        }
                        b'}' => {
                            pos += 1;
                            let Some(ContainerFrame::Object { entries, .. }) = stack.pop() else {
                                return Err(JsonError::new("JSON parser stack mismatch", pos));
                            };
                            attach_json_value(
                                &mut stack,
                                &mut root_val,
                                JsonValue::Object(entries),
                            )?;
                            expect = Expect::AfterValue;
                        }
                        _ => {
                            return Err(JsonError::new("expected `,` or `}` in JSON object", pos));
                        }
                    },
                    None => {
                        return Err(JsonError::new("unexpected empty JSON container stack", pos));
                    }
                }
            }
        }
    }
}

fn attach_json_value(
    stack: &mut [ContainerFrame],
    root_val: &mut Option<JsonValue>,
    val: JsonValue,
) -> Result<(), JsonError> {
    match stack.last_mut() {
        None => {
            *root_val = Some(val);
            Ok(())
        }
        Some(ContainerFrame::Array(elems)) => {
            elems.push(val);
            Ok(())
        }
        Some(ContainerFrame::Object {
            entries,
            pending_key,
        }) => {
            let key = pending_key
                .take()
                .ok_or_else(|| JsonError::new("missing JSON object key", 0))?;
            entries.push((key, val));
            Ok(())
        }
    }
}

fn skip_ws(bytes: &[u8], pos: &mut usize) {
    while let Some(&b) = bytes.get(*pos) {
        if matches!(b, b' ' | b'\t' | b'\r' | b'\n') {
            *pos += 1;
        } else {
            break;
        }
    }
}

fn parse_json_string(input: &str, pos: &mut usize) -> Result<String, JsonError> {
    let bytes = input.as_bytes();
    if bytes.get(*pos) != Some(&b'"') {
        return Err(JsonError::new("expected opening `\"`", *pos));
    }
    *pos += 1;
    let mut out = String::new();
    let mut chunk_start = *pos;

    while let Some(&b) = bytes.get(*pos) {
        if b == b'"' {
            out.push_str(&input[chunk_start..*pos]);
            *pos += 1;
            return Ok(out);
        }
        if b < 0x20 {
            return Err(JsonError::new(
                "unescaped control character in JSON string",
                *pos,
            ));
        }
        if b == b'\\' {
            out.push_str(&input[chunk_start..*pos]);
            *pos += 1;
            let Some(&esc) = bytes.get(*pos) else {
                return Err(JsonError::new("unterminated escape in JSON string", *pos));
            };
            *pos += 1;
            match esc {
                b'"' => out.push('"'),
                b'\\' => out.push('\\'),
                b'/' => out.push('/'),
                b'b' => out.push('\u{0008}'),
                b'f' => out.push('\u{000C}'),
                b'n' => out.push('\n'),
                b'r' => out.push('\r'),
                b't' => out.push('\t'),
                b'u' => {
                    let u1 = parse_hex4(bytes, pos)?;
                    if (0xD800..=0xDBFF).contains(&u1) {
                        // High surrogate must be followed by `\u` low surrogate.
                        if bytes.get(*pos..*pos + 2) != Some(b"\\u") {
                            return Err(JsonError::new(
                                "unpaired UTF-16 high surrogate in JSON string",
                                *pos,
                            ));
                        }
                        *pos += 2;
                        let u2 = parse_hex4(bytes, pos)?;
                        if !(0xDC00..=0xDFFF).contains(&u2) {
                            return Err(JsonError::new(
                                "invalid UTF-16 low surrogate in JSON string",
                                *pos,
                            ));
                        }
                        let cp =
                            0x10000 + ((u32::from(u1) - 0xD800) << 10) + (u32::from(u2) - 0xDC00);
                        let ch = char::from_u32(cp)
                            .ok_or_else(|| JsonError::new("invalid Unicode scalar", *pos))?;
                        out.push(ch);
                    } else if (0xDC00..=0xDFFF).contains(&u1) {
                        return Err(JsonError::new(
                            "unpaired UTF-16 low surrogate in JSON string",
                            *pos,
                        ));
                    } else {
                        let ch = char::from_u32(u32::from(u1))
                            .ok_or_else(|| JsonError::new("invalid Unicode scalar", *pos))?;
                        out.push(ch);
                    }
                }
                _ => {
                    return Err(JsonError::new(
                        format!("invalid JSON string escape `\\{}`", esc as char),
                        *pos - 1,
                    ));
                }
            }
            chunk_start = *pos;
        } else {
            *pos += 1;
        }
    }
    Err(JsonError::new("unterminated JSON string", *pos))
}

fn parse_hex4(bytes: &[u8], pos: &mut usize) -> Result<u16, JsonError> {
    if *pos + 4 > bytes.len() {
        return Err(JsonError::new("truncated \\uXXXX escape", *pos));
    }
    let mut val = 0u16;
    for i in 0..4 {
        let d = match bytes[*pos + i] {
            b'0'..=b'9' => u16::from(bytes[*pos + i] - b'0'),
            b'a'..=b'f' => u16::from(bytes[*pos + i] - b'a') + 10,
            b'A'..=b'F' => u16::from(bytes[*pos + i] - b'A') + 10,
            _ => return Err(JsonError::new("invalid hex digit in \\uXXXX", *pos + i)),
        };
        val = (val << 4) | d;
    }
    *pos += 4;
    Ok(val)
}

fn parse_json_number(input: &str, pos: &mut usize) -> Result<String, JsonError> {
    let bytes = input.as_bytes();
    let start = *pos;
    if bytes.get(*pos) == Some(&b'-') {
        *pos += 1;
    }
    match bytes.get(*pos) {
        Some(&b'0') => {
            *pos += 1;
            if bytes.get(*pos).is_some_and(u8::is_ascii_digit) {
                return Err(JsonError::new(
                    "leading zero not allowed in JSON number",
                    *pos,
                ));
            }
        }
        Some(b'1'..=b'9') => {
            while bytes.get(*pos).is_some_and(u8::is_ascii_digit) {
                *pos += 1;
            }
        }
        _ => return Err(JsonError::new("expected digit in JSON number", *pos)),
    }
    if bytes.get(*pos) == Some(&b'.') {
        *pos += 1;
        let frac_start = *pos;
        while bytes.get(*pos).is_some_and(u8::is_ascii_digit) {
            *pos += 1;
        }
        if *pos == frac_start {
            return Err(JsonError::new(
                "expected digit after decimal point in JSON number",
                *pos,
            ));
        }
    }
    if matches!(bytes.get(*pos), Some(b'e' | b'E')) {
        *pos += 1;
        if matches!(bytes.get(*pos), Some(b'+' | b'-')) {
            *pos += 1;
        }
        let exp_start = *pos;
        while bytes.get(*pos).is_some_and(u8::is_ascii_digit) {
            *pos += 1;
        }
        if *pos == exp_start {
            return Err(JsonError::new("expected digit in JSON exponent", *pos));
        }
    }
    Ok(input[start..*pos].to_string())
}

/// Escape and append a JSON string (including surrounding quotes) to `out`.
pub fn push_json_string(out: &mut String, s: &str) {
    out.push('"');
    for ch in s.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\u{0008}' => out.push_str("\\b"),
            '\u{000C}' => out.push_str("\\f"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => {
                let _ = write!(out, "\\u{:04x}", c as u32);
            }
            c => out.push(c),
        }
    }
    out.push('"');
}

/// Serialize a [`JsonValue`] to compact RFC 8259 JSON iteratively (O(1) stack).
#[must_use]
pub fn to_json_compact(val: &JsonValue) -> String {
    enum Emit<'a> {
        Val(&'a JsonValue),
        Lit(&'static str),
        Key(&'a str),
    }
    let mut out = String::new();
    let mut stack = vec![Emit::Val(val)];
    while let Some(item) = stack.pop() {
        match item {
            Emit::Lit(s) => out.push_str(s),
            Emit::Key(k) => {
                push_json_string(&mut out, k);
                out.push(':');
            }
            Emit::Val(v) => match v {
                JsonValue::Null => out.push_str("null"),
                JsonValue::Bool(b) => out.push_str(if *b { "true" } else { "false" }),
                JsonValue::Number(raw) => out.push_str(raw),
                JsonValue::Str(s) => push_json_string(&mut out, s),
                JsonValue::Array(xs) => {
                    out.push('[');
                    stack.push(Emit::Lit("]"));
                    for (i, el) in xs.iter().enumerate().rev() {
                        stack.push(Emit::Val(el));
                        if i > 0 {
                            stack.push(Emit::Lit(","));
                        }
                    }
                }
                JsonValue::Object(kvs) => {
                    out.push('{');
                    stack.push(Emit::Lit("}"));
                    for (i, (k, ev)) in kvs.iter().enumerate().rev() {
                        stack.push(Emit::Val(ev));
                        stack.push(Emit::Key(k.as_str()));
                        if i > 0 {
                            stack.push(Emit::Lit(","));
                        }
                    }
                }
            },
        }
    }
    out
}

/// A single raw line from a JSONL stream with its 1-based line number.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct JsonlLine {
    pub line: usize,
    pub raw_line: String,
}

/// Streaming JSONL line reader over any [`BufRead`] in bounded batches.
pub struct JsonlBatchReader<R: BufRead> {
    reader: R,
    line_no: usize,
    started: bool,
}

impl<R: BufRead> fmt::Debug for JsonlBatchReader<R> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("JsonlBatchReader")
            .field("line_no", &self.line_no)
            .finish_non_exhaustive()
    }
}

impl<R: BufRead> JsonlBatchReader<R> {
    #[must_use]
    pub fn new(reader: R) -> Self {
        Self {
            reader,
            line_no: 0,
            started: false,
        }
    }

    /// Read up to `max_rows` non-empty JSONL lines.
    ///
    /// # Errors
    /// Returns any underlying I/O or UTF-8 error.
    pub fn next_batch(&mut self, max_rows: usize) -> io::Result<Vec<JsonlLine>> {
        let mut out = Vec::with_capacity(max_rows.min(JSONL_BATCH_SIZE));
        let mut buf = String::new();
        while out.len() < max_rows {
            buf.clear();
            let n = self.reader.read_line(&mut buf)?;
            if n == 0 {
                break;
            }
            self.line_no += 1;
            let trimmed_end = buf.trim_end_matches(['\r', '\n']);
            let line_str = if !self.started {
                self.started = true;
                trimmed_end.strip_prefix('\u{FEFF}').unwrap_or(trimmed_end)
            } else {
                trimmed_end
            };
            if line_str.trim().is_empty() {
                continue;
            }
            out.push(JsonlLine {
                line: self.line_no,
                raw_line: line_str.to_string(),
            });
        }
        Ok(out)
    }
}

/// Convert a [`JsonValue`] field into a typed Dana [`Val`] according to `ty`.
pub fn json_value_to_dana(val: Option<&JsonValue>, ty: &ScalarTy) -> Result<Val, &'static str> {
    match ty {
        ScalarTy::Option(inner) => match val {
            None | Some(JsonValue::Null) => Ok(Val::OptNone),
            Some(v) => Ok(Val::OptSome(Box::new(json_value_to_dana(Some(v), inner)?))),
        },
        other => {
            let Some(v) = val else {
                return Err("MissingRequired");
            };
            if matches!(v, JsonValue::Null) {
                return Err("MissingRequired");
            }
            match (other, v) {
                (ScalarTy::Bool, JsonValue::Bool(b)) => Ok(Val::Bool(*b)),
                (ScalarTy::Bool, _) => Err("BadBool"),
                (ScalarTy::Int, JsonValue::Number(raw)) => {
                    let n: i64 = raw.parse().map_err(|_| "BadInt")?;
                    Ok(Val::Int(BigInt::from(n)))
                }
                (ScalarTy::Int, _) => Err("BadInt"),
                (ScalarTy::Decimal, JsonValue::Number(raw) | JsonValue::Str(raw)) => {
                    let d = parse_decimal_bigint(raw).map_err(|_| "BadDecimal")?;
                    Ok(Val::Decimal(d))
                }
                (ScalarTy::Decimal, _) => Err("BadDecimal"),
                (ScalarTy::Float, JsonValue::Number(raw)) => {
                    let f: f64 = raw.parse().map_err(|_| "BadFloat")?;
                    if !f.is_finite() {
                        return Err("BadFloat");
                    }
                    Ok(Val::Float(Float64::from_f64(f)))
                }
                (ScalarTy::Float, _) => Err("BadFloat"),
                (ScalarTy::Text, JsonValue::Str(s)) => Ok(Val::Text(s.clone())),
                (ScalarTy::Text, _) => Err("TypeMismatch"),
                (ScalarTy::Date, JsonValue::Str(s)) => {
                    let days = parse_iso_date(s).map_err(|_| "BadDate")?;
                    Ok(Val::Date(BigInt::from(days)))
                }
                (ScalarTy::Date, _) => Err("BadDate"),
                (ScalarTy::Timestamp, JsonValue::Str(s)) => {
                    let us = parse_iso_timestamp(s).map_err(|_| "BadTimestamp")?;
                    Ok(Val::Timestamp(BigInt::from(us)))
                }
                (ScalarTy::Timestamp, _) => Err("BadTimestamp"),
                (ScalarTy::Duration, JsonValue::Number(raw)) => {
                    let us: i64 = raw.parse().map_err(|_| "BadDuration")?;
                    Ok(Val::Duration(BigInt::from(us)))
                }
                (ScalarTy::Duration, _) => Err("BadDuration"),
                (ScalarTy::Bytes, JsonValue::Str(s)) => Ok(Val::Bytes(s.as_bytes().to_vec())),
                (ScalarTy::Bytes, _) => Err("TypeMismatch"),
                (ScalarTy::Unit, _) => Ok(Val::Unit),
                (ScalarTy::Data(_) | ScalarTy::Option(_), _) => Err("UnsupportedCellType"),
            }
        }
    }
}

/// Stream JSONL bytes from any [`Read`] in 2,048-row batches into `(valid_rows, bad_rows)`
/// against a [`TableTy`] schema and optional per-column constraint evaluator callback.
///
/// # Errors
/// Returns an error string on underlying I/O or UTF-8 failure.
pub fn read_jsonl_stream_with_schema<R, F>(
    reader: R,
    schema: &TableTy,
    mut check_constraint: F,
) -> Result<(TableVal, TableVal), String>
where
    R: Read,
    F: FnMut(usize, &Val) -> bool,
{
    let mut batch_reader = JsonlBatchReader::new(BufReader::new(reader));
    let bad_tt = quarantine_bad_row_table_ty(schema);
    let mut good_rows = Vec::new();
    let mut bad_rows = Vec::new();

    loop {
        let batch = batch_reader
            .next_batch(JSONL_BATCH_SIZE)
            .map_err(|e| e.to_string())?;
        if batch.is_empty() {
            break;
        }
        for jl in batch {
            let parsed = match parse_json(&jl.raw_line) {
                Ok(v) => v,
                Err(_) => {
                    bad_rows.push(TableRow {
                        cells: vec![
                            Val::Int(BigInt::from(jl.line)),
                            Val::Text(String::new()),
                            Val::Text("BadJson".to_string()),
                            Val::Text(jl.raw_line.clone()),
                            Val::Text(jl.raw_line),
                        ],
                        group_meta: None,
                    });
                    continue;
                }
            };
            if parsed.as_object().is_none() {
                bad_rows.push(TableRow {
                    cells: vec![
                        Val::Int(BigInt::from(jl.line)),
                        Val::Text(String::new()),
                        Val::Text("BadJson".to_string()),
                        Val::Text(jl.raw_line.clone()),
                        Val::Text(jl.raw_line),
                    ],
                    group_meta: None,
                });
                continue;
            }

            let mut cells = Vec::with_capacity(schema.cols.len());
            let mut bad_hit: Option<(&str, &str, String)> = None;
            for (ci, col) in schema.cols.iter().enumerate() {
                let raw_jval = parsed.get(&col.name);
                match json_value_to_dana(raw_jval, &col.ty) {
                    Ok(val) => {
                        let ok = match &val {
                            Val::OptNone => true,
                            Val::OptSome(inner) => check_constraint(ci, inner),
                            other => check_constraint(ci, other),
                        };
                        if !ok {
                            let raw_str = raw_jval.map(to_json_compact).unwrap_or_default();
                            bad_hit = Some((col.name.as_str(), "ConstraintFailed", raw_str));
                            break;
                        }
                        cells.push(val);
                    }
                    Err(kind) => {
                        let raw_str = raw_jval.map(to_json_compact).unwrap_or_default();
                        bad_hit = Some((col.name.as_str(), kind, raw_str));
                        break;
                    }
                }
            }

            if let Some((col_name, err_kind, raw_val)) = bad_hit {
                bad_rows.push(TableRow {
                    cells: vec![
                        Val::Int(BigInt::from(jl.line)),
                        Val::Text(col_name.to_string()),
                        Val::Text(err_kind.to_string()),
                        Val::Text(raw_val),
                        Val::Text(jl.raw_line),
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

/// Parse UTF-8 JSONL text into `(valid_rows, bad_rows)`.
///
/// # Errors
/// Returns an error string on I/O failure.
pub fn parse_jsonl_with_schema<F>(
    input: &str,
    schema: &TableTy,
    check_constraint: F,
) -> Result<(TableVal, TableVal), String>
where
    F: FnMut(usize, &Val) -> bool,
{
    read_jsonl_stream_with_schema(Cursor::new(input.as_bytes()), schema, check_constraint)
}

/// Append a single Dana [`Val`] encoded as an RFC 8259 JSON value to `out`.
pub fn push_dana_val_as_json(out: &mut String, v: &Val) {
    match v {
        Val::Unit | Val::OptNone => out.push_str("null"),
        Val::OptSome(inner) => push_dana_val_as_json(out, inner),
        Val::Bool(b) => out.push_str(if *b { "true" } else { "false" }),
        Val::Int(n) => {
            let _ = write!(out, "{n}");
        }
        Val::Decimal(_) => {
            // Preserve exact fixed-point decimal precision as a JSON string.
            push_json_string(out, &render_public_val(v));
        }
        Val::Float(f) => {
            let fv = f.to_f64();
            if fv.is_finite() {
                let _ = write!(out, "{fv}");
            } else {
                out.push_str("null");
            }
        }
        Val::Text(s) => push_json_string(out, s),
        Val::Date(d) => {
            let s = d.to_i64().map_or_else(|| d.to_string(), format_iso_date);
            push_json_string(out, &s);
        }
        Val::Timestamp(ts) => {
            let s = ts
                .to_i64()
                .map_or_else(|| ts.to_string(), format_iso_timestamp);
            push_json_string(out, &s);
        }
        Val::Duration(us) => {
            let _ = write!(out, "{us}");
        }
        other => push_json_string(out, &render_public_val(other)),
    }
}

/// Stream a [`TableVal`] as JSONL (one canonical JSON object per line) to any [`Write`] sink.
///
/// # Errors
/// Returns any underlying I/O error.
pub fn write_jsonl_table<W: Write>(writer: &mut W, tv: &TableVal) -> io::Result<()> {
    let mut line = String::new();
    for row in &tv.rows {
        line.clear();
        line.push('{');
        for (i, (col, cell)) in tv.cols.iter().zip(&row.cells).enumerate() {
            if i > 0 {
                line.push(',');
            }
            push_json_string(&mut line, &col.name);
            line.push(':');
            push_dana_val_as_json(&mut line, cell);
        }
        line.push_str("}\n");
        writer.write_all(line.as_bytes())?;
    }
    Ok(())
}

/// Format a [`TableVal`] as JSONL text.
#[must_use]
pub fn format_jsonl_table(tv: &TableVal) -> String {
    let mut buf = Vec::new();
    let _ = write_jsonl_table(&mut buf, tv);
    String::from_utf8(buf).unwrap_or_default()
}
