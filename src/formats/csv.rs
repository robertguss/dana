//! Streaming RFC 4180 CSV/TSV parser, writer, and schema-validated quarantine loader (`(valid_rows, bad_rows)`).
//!
//! Reads arbitrarily large plain, `.gz`, or `.zst` CSV/TSV files in bounded 2,048-row batches
//! over any [`BufRead`], preserving exact 1-based line numbers across multiline quoted fields
//! and enforcing `quarantine_bad_row_table_ty` sensitivity tag propagation on `bad_rows`.

use std::fmt::{self, Write as _};
use std::io::{self, BufRead, BufReader, Cursor, Read, Write};

use crate::core::bigint::BigInt;
use crate::core::check::quarantine_bad_row_table_ty;
use crate::core::syntax::{ColSpec, Float64, ScalarTy, TableTy};
use crate::formats::constraint::{FastColConstraint, UnboxedCell};
use crate::formats::crypto::to_hex_lower;
use crate::formats::time::{
    format_iso_date, format_iso_timestamp, parse_decimal_bigint_strict, parse_decimal_i128,
    parse_iso_date, parse_iso_timestamp,
};
use crate::oracle::value::{TableRow, TableVal, Val, render_decimal_i128_into};
use crate::vm::batch::{Batch, Column, ColumnData, NullBitmap};
use crate::vm::ops::VmTable;

/// Default streaming batch size for CSV/TSV record iteration (matches the Phase 2C VM batch size).
pub const CSV_BATCH_SIZE: usize = 2048;

/// A single parsed RFC 4180 CSV/TSV record with its 1-based starting line number and raw line text.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CsvRecord {
    pub line: usize,
    pub raw_line: String,
    pub fields: Vec<String>,
}

/// Streaming RFC 4180 CSV/TSV record reader over any [`BufRead`].
///
/// Handles UTF-8 BOM, `\r\n` and `\n` line endings, multiline quoted fields, and doubled `""` quotes
/// without slurping the entire file into memory.
pub struct CsvBatchReader<R: BufRead> {
    reader: R,
    delimiter: u8,
    line_no: usize,
    started: bool,
    eof: bool,
    preserve_empty_lines: bool,
    pending: [u8; 3],
    pending_pos: usize,
    pending_len: usize,
}

impl<R: BufRead> fmt::Debug for CsvBatchReader<R> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("CsvBatchReader")
            .field("delimiter", &(self.delimiter as char))
            .field("line_no", &self.line_no)
            .field("eof", &self.eof)
            .finish_non_exhaustive()
    }
}

impl<R: BufRead> CsvBatchReader<R> {
    #[must_use]
    pub fn new(reader: R, delimiter: u8) -> Self {
        Self {
            reader,
            delimiter,
            line_no: 1,
            started: false,
            eof: false,
            preserve_empty_lines: false,
            pending: [0; 3],
            pending_pos: 0,
            pending_len: 0,
        }
    }

    /// When enabled (used for single-column schemas), empty lines represent a valid 1-field empty row
    /// rather than being skipped, preserving `Option(T)` `none` rows across write/read round-trips.
    pub fn set_preserve_empty_lines(&mut self, preserve: bool) {
        self.preserve_empty_lines = preserve;
    }

    fn push_pending(&mut self, byte: u8) {
        self.pending[0] = byte;
        self.pending_pos = 0;
        self.pending_len = 1;
    }

    fn next_byte(&mut self) -> io::Result<Option<u8>> {
        if self.pending_pos < self.pending_len {
            let b = self.pending[self.pending_pos];
            self.pending_pos += 1;
            return Ok(Some(b));
        }
        let buf = self.reader.fill_buf()?;
        if buf.is_empty() {
            self.eof = true;
            return Ok(None);
        }
        let b = buf[0];
        self.reader.consume(1);
        Ok(Some(b))
    }

    fn skip_utf8_bom(&mut self) -> io::Result<()> {
        if self.started {
            return Ok(());
        }
        self.started = true;
        let buf = self.reader.fill_buf()?;
        if buf.len() >= 3 && buf[0] == 0xEF && buf[1] == 0xBB && buf[2] == 0xBF {
            self.reader.consume(3);
            return Ok(());
        }
        if buf.first() == Some(&0xEF) && buf.len() < 3 {
            // Tiny underlying buffer splitting a potential 3-byte BOM: read up to 3 bytes and
            // replay them losslessly via `self.pending` if they are not `[EF, BB, BF]`.
            let mut probe = [0u8; 3];
            let mut got = 0usize;
            while got < 3 {
                let Some(b) = self.next_byte()? else {
                    break;
                };
                probe[got] = b;
                got += 1;
            }
            if !(got == 3 && probe == [0xEF, 0xBB, 0xBF]) {
                self.pending = probe;
                self.pending_pos = 0;
                self.pending_len = got;
            }
        }
        Ok(())
    }

    /// Read the next non-blank RFC 4180 CSV record, or `Ok(None)` at EOF.
    ///
    /// # Errors
    /// Returns an `io::Error` on underlying I/O or invalid UTF-8 errors.
    pub fn next_record(&mut self) -> io::Result<Option<CsvRecord>> {
        self.skip_utf8_bom()?;
        loop {
            if self.eof && self.pending_pos >= self.pending_len {
                return Ok(None);
            }
            let Some(first) = self.next_byte()? else {
                return Ok(None);
            };
            // Skip pure blank lines (`\n` or `\r\n`), unless preserving empty rows for 1-column schemas.
            if first == b'\n' {
                let rec_line = self.line_no;
                self.line_no += 1;
                if self.preserve_empty_lines {
                    return Ok(Some(CsvRecord {
                        line: rec_line,
                        raw_line: String::new(),
                        fields: vec![String::new()],
                    }));
                }
                continue;
            }
            if first == b'\r' {
                let rec_line = self.line_no;
                if let Some(next) = self.next_byte()?
                    && next != b'\n'
                {
                    self.push_pending(next);
                }
                self.line_no += 1;
                if self.preserve_empty_lines {
                    return Ok(Some(CsvRecord {
                        line: rec_line,
                        raw_line: String::new(),
                        fields: vec![String::new()],
                    }));
                }
                continue;
            }

            let rec_line = self.line_no;
            let mut raw_bytes = Vec::new();
            let mut fields = Vec::new();
            let mut cur_byte = Some(first);

            loop {
                let mut field_bytes = Vec::new();
                if cur_byte == Some(b'"') {
                    raw_bytes.push(b'"');
                    let mut closed = false;
                    loop {
                        match self.next_byte()? {
                            None => {
                                break;
                            }
                            Some(b'"') => {
                                raw_bytes.push(b'"');
                                match self.next_byte()? {
                                    Some(b'"') => {
                                        raw_bytes.push(b'"');
                                        field_bytes.push(b'"');
                                    }
                                    other => {
                                        closed = true;
                                        cur_byte = other;
                                        break;
                                    }
                                }
                            }
                            Some(b) => {
                                if b == b'\n' {
                                    self.line_no += 1;
                                }
                                raw_bytes.push(b);
                                field_bytes.push(b);
                            }
                        }
                    }
                    if !closed {
                        return Err(io::Error::new(
                            io::ErrorKind::InvalidData,
                            format!("unterminated quoted field starting at CSV line {rec_line}"),
                        ));
                    }
                    // Consume any stray characters after closing quote up to delimiter or newline.
                    while let Some(b) = cur_byte {
                        if b == self.delimiter || b == b'\n' || b == b'\r' {
                            break;
                        }
                        raw_bytes.push(b);
                        field_bytes.push(b);
                        cur_byte = self.next_byte()?;
                    }
                } else {
                    while let Some(b) = cur_byte {
                        if b == self.delimiter || b == b'\n' || b == b'\r' {
                            break;
                        }
                        raw_bytes.push(b);
                        field_bytes.push(b);
                        cur_byte = self.next_byte()?;
                    }
                }

                let field = String::from_utf8(field_bytes).map_err(|e| {
                    io::Error::new(
                        io::ErrorKind::InvalidData,
                        format!("invalid UTF-8 in CSV line {rec_line}: {e}"),
                    )
                })?;
                fields.push(field);

                match cur_byte {
                    Some(b) if b == self.delimiter => {
                        raw_bytes.push(b);
                        cur_byte = self.next_byte()?;
                        // Trailing delimiter before EOL/EOF produces a final empty field.
                        if cur_byte.is_none() || cur_byte == Some(b'\n') || cur_byte == Some(b'\r')
                        {
                            fields.push(String::new());
                            if cur_byte == Some(b'\r') {
                                if let Some(next) = self.next_byte()?
                                    && next != b'\n'
                                {
                                    self.push_pending(next);
                                }
                                self.line_no += 1;
                            } else if cur_byte == Some(b'\n') {
                                self.line_no += 1;
                            }
                            break;
                        }
                    }
                    Some(b'\r') => {
                        if let Some(next) = self.next_byte()?
                            && next != b'\n'
                        {
                            self.push_pending(next);
                        }
                        self.line_no += 1;
                        break;
                    }
                    Some(b'\n') => {
                        self.line_no += 1;
                        break;
                    }
                    None => break,
                    Some(_) => break,
                }
            }

            let raw_line = String::from_utf8(raw_bytes).map_err(|e| {
                io::Error::new(
                    io::ErrorKind::InvalidData,
                    format!("invalid UTF-8 in CSV line {rec_line}: {e}"),
                )
            })?;
            return Ok(Some(CsvRecord {
                line: rec_line,
                raw_line,
                fields,
            }));
        }
    }

    /// Read up to `max_rows` records into a batch. Returns an empty `Vec` at EOF.
    ///
    /// # Errors
    /// Returns any I/O or UTF-8 error encountered while reading the batch.
    pub fn next_batch(&mut self, max_rows: usize) -> io::Result<Vec<CsvRecord>> {
        let mut batch = Vec::with_capacity(max_rows.min(CSV_BATCH_SIZE));
        for _ in 0..max_rows {
            match self.next_record()? {
                Some(rec) => batch.push(rec),
                None => break,
            }
        }
        Ok(batch)
    }

    /// Zero-allocation fast path for unquoted single-line CSV records residing inside the
    /// underlying `BufRead` buffer; falls back to full RFC 4180 `next_record` on quotes,
    /// cross-buffer lines, bare `\r`, or EOF lines without trailing newline.
    fn next_record_fast(
        &mut self,
        scratch_line: &mut String,
        scratch_ranges: &mut Vec<(usize, usize)>,
        scratch_fallback: &mut Option<CsvRecord>,
    ) -> io::Result<Option<usize>> {
        self.skip_utf8_bom()?;
        loop {
            if self.eof && self.pending_pos >= self.pending_len {
                return Ok(None);
            }
            if self.pending_pos == self.pending_len {
                let buf = self.reader.fill_buf()?;
                if buf.is_empty() {
                    self.eof = true;
                    return Ok(None);
                }
                if let Some(nl) = buf.iter().position(|&b| b == b'\n') {
                    let raw = &buf[..nl];
                    let clean = raw.strip_suffix(b"\r").unwrap_or(raw);
                    // Single pass: split on `delimiter` while checking for `"` or bare `\r`.
                    scratch_ranges.clear();
                    let delim = self.delimiter;
                    let mut start = 0usize;
                    let mut special = false;
                    for (idx, &b) in clean.iter().enumerate() {
                        if b == delim {
                            scratch_ranges.push((start, idx));
                            start = idx + 1;
                        } else if b == b'"' || b == b'\r' {
                            special = true;
                            break;
                        }
                    }
                    if !special {
                        let rec_line = self.line_no;
                        self.line_no += 1;
                        if clean.is_empty() {
                            self.reader.consume(nl + 1);
                            if self.preserve_empty_lines {
                                scratch_line.clear();
                                scratch_ranges.clear();
                                scratch_ranges.push((0, 0));
                                *scratch_fallback = None;
                                return Ok(Some(rec_line));
                            }
                            continue;
                        }
                        let line_str = std::str::from_utf8(clean).map_err(|e| {
                            io::Error::new(
                                io::ErrorKind::InvalidData,
                                format!("invalid UTF-8 in CSV line {rec_line}: {e}"),
                            )
                        })?;
                        scratch_line.clear();
                        scratch_line.push_str(line_str);
                        scratch_ranges.push((start, clean.len()));
                        self.reader.consume(nl + 1);
                        *scratch_fallback = None;
                        return Ok(Some(rec_line));
                    }
                }
            }
            match self.next_record()? {
                Some(rec) => {
                    let line = rec.line;
                    *scratch_fallback = Some(rec);
                    return Ok(Some(line));
                }
                None => return Ok(None),
            }
        }
    }
}

/// Parse UTF-8 CSV/TSV text into RFC 4180 records with 1-based line numbers.
#[must_use]
pub fn parse_csv_records(input: &str, delimiter: u8) -> Vec<CsvRecord> {
    let mut reader = CsvBatchReader::new(Cursor::new(input.as_bytes()), delimiter);
    let mut records = Vec::new();
    while let Ok(Some(rec)) = reader.next_record() {
        records.push(rec);
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
            let d = parse_decimal_bigint_strict(trimmed).map_err(|_| "BadDecimal")?;
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

/// Stream CSV/TSV bytes from any [`Read`] in 2,048-row batches into `(valid_rows, bad_rows)`
/// against a [`TableTy`] schema and optional per-column constraint evaluator callback.
///
/// # Errors
/// Returns an error string on I/O, UTF-8, or missing required header column errors.
pub fn read_csv_stream_with_schema<R, F>(
    reader: R,
    schema: &TableTy,
    delimiter: u8,
    mut check_constraint: F,
) -> Result<(TableVal, TableVal), String>
where
    R: Read,
    F: FnMut(usize, &Val) -> bool,
{
    let mut batch_reader =
        CsvBatchReader::new(BufReader::with_capacity(64 * 1024, reader), delimiter);
    let bad_tt = quarantine_bad_row_table_ty(schema);

    let Some(header) = batch_reader.next_record().map_err(|e| e.to_string())? else {
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
    if header.fields.len() == 1 {
        batch_reader.set_preserve_empty_lines(true);
    }

    let mut good_rows = Vec::new();
    let mut bad_rows = Vec::new();
    let mut scratch_line = String::with_capacity(256);
    let mut scratch_ranges: Vec<(usize, usize)> = Vec::with_capacity(header.fields.len().max(8));
    let mut scratch_fallback: Option<CsvRecord> = None;

    while let Some(rec_line) = batch_reader
        .next_record_fast(
            &mut scratch_line,
            &mut scratch_ranges,
            &mut scratch_fallback,
        )
        .map_err(|e| e.to_string())?
    {
        let mut cells = Vec::with_capacity(schema.cols.len());
        let mut bad_hit: Option<(&str, &str, String)> = None;

        for (ci, col) in schema.cols.iter().enumerate() {
            let field_idx = col_indices[ci];
            let raw_opt: Option<&str> = match &scratch_fallback {
                Some(rec) => rec.fields.get(field_idx).map(String::as_str),
                None => scratch_ranges
                    .get(field_idx)
                    .map(|&(s, e)| &scratch_line[s..e]),
            };
            let Some(raw_val) = raw_opt else {
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
                        bad_hit =
                            Some((col.name.as_str(), "ConstraintFailed", raw_val.to_string()));
                        break;
                    }
                    cells.push(val);
                }
                Err(kind) => {
                    bad_hit = Some((col.name.as_str(), kind, raw_val.to_string()));
                    break;
                }
            }
        }

        if let Some((col_name, err_kind, raw_val)) = bad_hit {
            let raw_line = match scratch_fallback.take() {
                Some(rec) => rec.raw_line,
                None => scratch_line.clone(),
            };
            bad_rows.push(TableRow {
                cells: vec![
                    Val::Int(BigInt::from(rec_line)),
                    Val::Text(col_name.to_string()),
                    Val::Text(err_kind.to_string()),
                    Val::Text(raw_val),
                    Val::Text(raw_line),
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

/// Parse CSV text into `(valid_rows, bad_rows)` against a [`TableTy`] schema and optional
/// per-column constraint evaluator callback `check_col(col_idx, &Val) -> bool`.
///
/// # Errors
/// Returns an error string if the header row is missing required schema columns.
pub fn parse_csv_with_schema<F>(
    input: &str,
    schema: &TableTy,
    delimiter: u8,
    check_constraint: F,
) -> Result<(TableVal, TableVal), String>
where
    F: FnMut(usize, &Val) -> bool,
{
    read_csv_stream_with_schema(
        Cursor::new(input.as_bytes()),
        schema,
        delimiter,
        check_constraint,
    )
}

// ---------------------------------------------------------------------------
// Direct Streaming-Columnar CSV/TSV Decoder into 2,048-Row `VmTable` Batches
// ---------------------------------------------------------------------------

enum CsvColBuf {
    Unit(usize),
    Bool(Vec<u8>),
    Int(Vec<i64>),
    Decimal(Vec<i128>),
    Float(Vec<u64>),
    Text { offsets: Vec<usize>, data: Vec<u8> },
    Bytes { offsets: Vec<usize>, data: Vec<u8> },
    Date(Vec<i64>),
    Timestamp(Vec<i64>),
    Duration(Vec<i64>),
    Generic(Vec<Val>),
}

impl CsvColBuf {
    fn new_for_scalar(ty: &ScalarTy, cap: usize) -> (Self, Option<NullBitmap>) {
        match ty {
            ScalarTy::Option(inner) if !inner.is_option() => {
                let buf = Self::new_leaf(inner, cap);
                if matches!(buf, Self::Generic(_)) {
                    (buf, None)
                } else {
                    (buf, Some(NullBitmap::with_capacity(cap)))
                }
            }
            other => (Self::new_leaf(other, cap), None),
        }
    }

    fn new_leaf(ty: &ScalarTy, cap: usize) -> Self {
        match ty {
            ScalarTy::Unit => Self::Unit(0),
            ScalarTy::Bool => Self::Bool(Vec::with_capacity(cap)),
            ScalarTy::Int => Self::Int(Vec::with_capacity(cap)),
            ScalarTy::Decimal => Self::Decimal(Vec::with_capacity(cap)),
            ScalarTy::Float => Self::Float(Vec::with_capacity(cap)),
            ScalarTy::Text => {
                let mut offsets = Vec::with_capacity(cap + 1);
                offsets.push(0);
                Self::Text {
                    offsets,
                    data: Vec::with_capacity(cap * 8),
                }
            }
            ScalarTy::Bytes => {
                let mut offsets = Vec::with_capacity(cap + 1);
                offsets.push(0);
                Self::Bytes {
                    offsets,
                    data: Vec::with_capacity(cap * 8),
                }
            }
            ScalarTy::Date => Self::Date(Vec::with_capacity(cap)),
            ScalarTy::Timestamp => Self::Timestamp(Vec::with_capacity(cap)),
            ScalarTy::Duration => Self::Duration(Vec::with_capacity(cap)),
            ScalarTy::Data(_) | ScalarTy::Option(_) => Self::Generic(Vec::with_capacity(cap)),
        }
    }

    #[inline]
    fn push_null(&mut self) {
        match self {
            Self::Unit(n) => *n += 1,
            Self::Bool(v) => v.push(0),
            Self::Int(v) | Self::Date(v) | Self::Timestamp(v) | Self::Duration(v) => v.push(0),
            Self::Decimal(v) => v.push(0),
            Self::Float(v) => v.push(0),
            Self::Text { offsets, data } | Self::Bytes { offsets, data } => {
                offsets.push(data.len());
            }
            Self::Generic(v) => v.push(Val::OptNone),
        }
    }

    fn into_column_data(self) -> ColumnData {
        match self {
            Self::Unit(n) => ColumnData::Unit(n),
            Self::Bool(v) => ColumnData::Bool(v),
            Self::Int(v) => ColumnData::Int(v),
            Self::Decimal(v) => ColumnData::Decimal(v),
            Self::Float(v) => ColumnData::Float(v),
            Self::Text { offsets, data } => ColumnData::Text { offsets, data },
            Self::Bytes { offsets, data } => ColumnData::Bytes { offsets, data },
            Self::Date(v) => ColumnData::Date(v),
            Self::Timestamp(v) => ColumnData::Timestamp(v),
            Self::Duration(v) => ColumnData::Duration(v),
            Self::Generic(v) => ColumnData::Generic(v),
        }
    }
}

/// Reusable unboxed row cell slot (zero heap allocation per cell on all primitive/Text columns).
enum CsvRowSlot {
    Null,
    Unit,
    Bool(bool),
    Int(i64),
    Decimal(i128),
    Float(u64),
    TextField(usize),
    BytesField(usize),
    Date(i64),
    Timestamp(i64),
    Duration(i64),
    Generic(Val),
}

#[inline]
fn parse_csv_bool_fast(trimmed: &str) -> Result<bool, &'static str> {
    if trimmed.is_empty() {
        return Err("MissingRequired");
    }
    if trimmed == "1" || trimmed.eq_ignore_ascii_case("true") || trimmed.eq_ignore_ascii_case("yes")
    {
        Ok(true)
    } else if trimmed == "0"
        || trimmed.eq_ignore_ascii_case("false")
        || trimmed.eq_ignore_ascii_case("no")
    {
        Ok(false)
    } else {
        Err("BadBool")
    }
}

#[inline]
fn parse_csv_cell_slot(
    raw: &str,
    field_idx: usize,
    ty: &ScalarTy,
) -> Result<CsvRowSlot, &'static str> {
    match ty {
        ScalarTy::Option(inner) if !inner.is_option() => {
            if raw.trim().is_empty() {
                Ok(CsvRowSlot::Null)
            } else {
                parse_csv_cell_slot(raw, field_idx, inner)
            }
        }
        ScalarTy::Option(_) => parse_csv_cell(raw, ty).map(CsvRowSlot::Generic),
        ScalarTy::Text => Ok(CsvRowSlot::TextField(field_idx)),
        ScalarTy::Bytes => Ok(CsvRowSlot::BytesField(field_idx)),
        ScalarTy::Unit => Ok(CsvRowSlot::Unit),
        ScalarTy::Bool => parse_csv_bool_fast(raw.trim()).map(CsvRowSlot::Bool),
        ScalarTy::Int => {
            let trimmed = raw.trim();
            if trimmed.is_empty() {
                return Err("MissingRequired");
            }
            trimmed
                .parse::<i64>()
                .map(CsvRowSlot::Int)
                .map_err(|_| "BadInt")
        }
        ScalarTy::Decimal => {
            let trimmed = raw.trim();
            if trimmed.is_empty() {
                return Err("MissingRequired");
            }
            parse_decimal_i128(trimmed)
                .map(CsvRowSlot::Decimal)
                .ok_or("BadDecimal")
        }
        ScalarTy::Float => {
            let trimmed = raw.trim();
            if trimmed.is_empty() {
                return Err("MissingRequired");
            }
            let f: f64 = trimmed.parse().map_err(|_| "BadFloat")?;
            if f.is_nan() || f.is_infinite() {
                return Err("BadFloat");
            }
            Ok(CsvRowSlot::Float(Float64::from_f64(f).bits))
        }
        ScalarTy::Date => {
            let trimmed = raw.trim();
            if trimmed.is_empty() {
                return Err("MissingRequired");
            }
            parse_iso_date(trimmed)
                .map(CsvRowSlot::Date)
                .map_err(|_| "BadDate")
        }
        ScalarTy::Timestamp => {
            let trimmed = raw.trim();
            if trimmed.is_empty() {
                return Err("MissingRequired");
            }
            parse_iso_timestamp(trimmed)
                .map(CsvRowSlot::Timestamp)
                .map_err(|_| "BadTimestamp")
        }
        ScalarTy::Duration => {
            let trimmed = raw.trim();
            if trimmed.is_empty() {
                return Err("MissingRequired");
            }
            trimmed
                .parse::<i64>()
                .map(CsvRowSlot::Duration)
                .map_err(|_| "BadDuration")
        }
        ScalarTy::Data(_) => Err("UnsupportedCellType"),
    }
}

#[inline]
fn slot_as_unboxed<'a>(slot: &'a CsvRowSlot, raw_str: &'a str) -> Option<UnboxedCell<'a>> {
    match slot {
        CsvRowSlot::Null => Some(UnboxedCell::Null),
        CsvRowSlot::Unit => Some(UnboxedCell::Unit),
        CsvRowSlot::Bool(b) => Some(UnboxedCell::Bool(*b)),
        CsvRowSlot::Int(n) => Some(UnboxedCell::Int(*n)),
        CsvRowSlot::Decimal(d) => Some(UnboxedCell::Decimal(*d)),
        CsvRowSlot::Float(bits) => Some(UnboxedCell::Float(*bits)),
        CsvRowSlot::TextField(_) => Some(UnboxedCell::Text(raw_str)),
        CsvRowSlot::BytesField(_) => Some(UnboxedCell::Bytes(raw_str.as_bytes())),
        CsvRowSlot::Date(d) => Some(UnboxedCell::Date(*d)),
        CsvRowSlot::Timestamp(t) => Some(UnboxedCell::Timestamp(*t)),
        CsvRowSlot::Duration(d) => Some(UnboxedCell::Duration(*d)),
        CsvRowSlot::Generic(_) => None,
    }
}

fn flush_csv_batch(
    specs: &[ColSpec],
    bufs: &mut Vec<(CsvColBuf, Option<NullBitmap>)>,
    cur_len: &mut usize,
    batch_size: usize,
    batches: &mut Vec<Batch>,
) {
    if *cur_len == 0 {
        return;
    }
    let fresh = specs
        .iter()
        .map(|s| CsvColBuf::new_for_scalar(&s.ty, batch_size))
        .collect();
    let finished = std::mem::replace(bufs, fresh);
    let cols = specs
        .iter()
        .cloned()
        .zip(finished)
        .map(|(spec, (buf, validity))| Column {
            spec,
            data: buf.into_column_data(),
            validity,
        })
        .collect();
    batches.push(Batch {
        cols,
        len: *cur_len,
        selection: None,
        group_meta: None,
    });
    *cur_len = 0;
}

/// Stream CSV/TSV bytes from any [`Read`] directly into 2,048-row columnar [`VmTable`] batches
/// plus quarantined `bad_rows` [`TableVal`], eliminating row-wise `TableVal` / `Val` / `BigInt`
/// materialization on the VM path.
///
/// Matches [`read_csv_stream_with_schema`] cell-for-cell across valid rows, bad-row quarantine
/// line numbers, error kinds, multiline quoted fields, `.gz`/`.zst` streams, and `where` constraints.
///
/// # Errors
/// Returns an error string on I/O, UTF-8, or missing required header column errors.
pub fn read_csv_stream_to_vm_table<R, F>(
    reader: R,
    schema: &TableTy,
    delimiter: u8,
    batch_size: usize,
    fast_constraints: &[FastColConstraint],
    mut fallback_constraint: F,
) -> Result<(VmTable, TableVal), String>
where
    R: Read,
    F: FnMut(usize, &Val) -> bool,
{
    let mut batch_reader =
        CsvBatchReader::new(BufReader::with_capacity(64 * 1024, reader), delimiter);
    let bad_tt = quarantine_bad_row_table_ty(schema);

    let Some(header) = batch_reader.next_record().map_err(|e| e.to_string())? else {
        return Ok((
            VmTable {
                cols: schema.cols.clone(),
                batches: Vec::new(),
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
    if header.fields.len() == 1 {
        batch_reader.set_preserve_empty_lines(true);
    }

    let chunk = batch_size.clamp(1, usize::from(u16::MAX));
    let mut col_bufs: Vec<(CsvColBuf, Option<NullBitmap>)> = schema
        .cols
        .iter()
        .map(|s| CsvColBuf::new_for_scalar(&s.ty, chunk))
        .collect();
    let mut cur_len = 0usize;
    let mut batches: Vec<Batch> = Vec::new();
    let mut bad_rows: Vec<TableRow> = Vec::new();

    let mut scratch_line = String::with_capacity(256);
    let mut scratch_ranges: Vec<(usize, usize)> = Vec::with_capacity(header.fields.len().max(8));
    let mut scratch_fallback: Option<CsvRecord> = None;
    let mut row_slots: Vec<CsvRowSlot> = Vec::with_capacity(schema.cols.len());

    while let Some(rec_line) = batch_reader
        .next_record_fast(
            &mut scratch_line,
            &mut scratch_ranges,
            &mut scratch_fallback,
        )
        .map_err(|e| e.to_string())?
    {
        row_slots.clear();
        let mut bad_hit: Option<(&str, &str, String)> = None;

        for (ci, col) in schema.cols.iter().enumerate() {
            let field_idx = col_indices[ci];
            let raw_opt: Option<&str> = match &scratch_fallback {
                Some(rec) => rec.fields.get(field_idx).map(String::as_str),
                None => scratch_ranges
                    .get(field_idx)
                    .map(|&(s, e)| &scratch_line[s..e]),
            };
            let Some(raw_val) = raw_opt else {
                bad_hit = Some((col.name.as_str(), "MissingColumn", String::new()));
                break;
            };
            match parse_csv_cell_slot(raw_val, field_idx, &col.ty) {
                Ok(slot) => {
                    let constraint_ok = match &slot {
                        CsvRowSlot::Null => true,
                        CsvRowSlot::Generic(v) => match v {
                            Val::OptNone => true,
                            Val::OptSome(inner) => fallback_constraint(ci, inner),
                            other => fallback_constraint(ci, other),
                        },
                        _ => {
                            let fc = fast_constraints
                                .get(ci)
                                .unwrap_or(&FastColConstraint::AlwaysTrue);
                            if fc.is_always_true() {
                                true
                            } else if let Some(unboxed) = slot_as_unboxed(&slot, raw_val)
                                && let Some(res) = fc.eval_unboxed(unboxed)
                            {
                                res
                            } else {
                                let boxed = slot_as_unboxed(&slot, raw_val)
                                    .map_or(Val::Unit, UnboxedCell::to_val);
                                fallback_constraint(ci, &boxed)
                            }
                        }
                    };
                    if !constraint_ok {
                        bad_hit =
                            Some((col.name.as_str(), "ConstraintFailed", raw_val.to_string()));
                        break;
                    }
                    row_slots.push(slot);
                }
                Err(kind) => {
                    bad_hit = Some((col.name.as_str(), kind, raw_val.to_string()));
                    break;
                }
            }
        }

        if let Some((col_name, err_kind, raw_val)) = bad_hit {
            let raw_line = match scratch_fallback.take() {
                Some(rec) => rec.raw_line,
                None => scratch_line.clone(),
            };
            bad_rows.push(TableRow {
                cells: vec![
                    Val::Int(BigInt::from(rec_line)),
                    Val::Text(col_name.to_string()),
                    Val::Text(err_kind.to_string()),
                    Val::Text(raw_val),
                    Val::Text(raw_line),
                ],
                group_meta: None,
            });
            continue;
        }

        // Row passed every parse & `where` check: commit unboxed cells straight into column buffers!
        for ((buf, validity), slot) in col_bufs.iter_mut().zip(row_slots.drain(..)) {
            if matches!(slot, CsvRowSlot::Null) {
                if let Some(bm) = validity {
                    bm.push(false);
                }
                buf.push_null();
                continue;
            }
            if let Some(bm) = validity {
                bm.push(true);
            }
            match (buf, slot) {
                (CsvColBuf::Unit(n), CsvRowSlot::Unit) => *n += 1,
                (CsvColBuf::Bool(v), CsvRowSlot::Bool(b)) => v.push(u8::from(b)),
                (CsvColBuf::Int(v), CsvRowSlot::Int(n)) => v.push(n),
                (CsvColBuf::Decimal(v), CsvRowSlot::Decimal(d)) => v.push(d),
                (CsvColBuf::Float(v), CsvRowSlot::Float(bits)) => v.push(bits),
                (CsvColBuf::Date(v), CsvRowSlot::Date(d)) => v.push(d),
                (CsvColBuf::Timestamp(v), CsvRowSlot::Timestamp(t)) => v.push(t),
                (CsvColBuf::Duration(v), CsvRowSlot::Duration(d)) => v.push(d),
                (CsvColBuf::Text { offsets, data }, CsvRowSlot::TextField(fidx)) => {
                    let s: &str = match &scratch_fallback {
                        Some(rec) => rec.fields.get(fidx).map_or("", String::as_str),
                        None => scratch_ranges
                            .get(fidx)
                            .map_or("", |&(s, e)| &scratch_line[s..e]),
                    };
                    data.extend_from_slice(s.as_bytes());
                    offsets.push(data.len());
                }
                (CsvColBuf::Bytes { offsets, data }, CsvRowSlot::BytesField(fidx)) => {
                    let s: &str = match &scratch_fallback {
                        Some(rec) => rec.fields.get(fidx).map_or("", String::as_str),
                        None => scratch_ranges
                            .get(fidx)
                            .map_or("", |&(s, e)| &scratch_line[s..e]),
                    };
                    data.extend_from_slice(s.as_bytes());
                    offsets.push(data.len());
                }
                (CsvColBuf::Generic(v), CsvRowSlot::Generic(val)) => v.push(val),
                (CsvColBuf::Generic(v), other) => {
                    let raw_s: &str = match other {
                        CsvRowSlot::TextField(fidx) | CsvRowSlot::BytesField(fidx) => {
                            match &scratch_fallback {
                                Some(rec) => rec.fields.get(fidx).map_or("", String::as_str),
                                None => scratch_ranges
                                    .get(fidx)
                                    .map_or("", |&(s, e)| &scratch_line[s..e]),
                            }
                        }
                        _ => "",
                    };
                    v.push(slot_as_unboxed(&other, raw_s).map_or(Val::Unit, UnboxedCell::to_val));
                }
                _ => {}
            }
        }
        cur_len += 1;
        if cur_len >= chunk {
            flush_csv_batch(
                &schema.cols,
                &mut col_bufs,
                &mut cur_len,
                chunk,
                &mut batches,
            );
        }
    }

    flush_csv_batch(
        &schema.cols,
        &mut col_bufs,
        &mut cur_len,
        chunk,
        &mut batches,
    );

    Ok((
        VmTable {
            cols: schema.cols.clone(),
            batches,
        },
        TableVal {
            cols: bad_tt.cols,
            rows: bad_rows,
        },
    ))
}

/// Append a single columnar batch cell directly into `line` in RFC 4180 CSV/TSV format,
/// matching [`render_csv_cell`] + [`push_csv_escaped`] byte-for-byte with zero per-cell allocation.
fn push_column_csv_cell(out: &mut String, col: &Column, row: usize, delimiter: u8) {
    if let Some(bm) = &col.validity
        && !bm.is_valid(row)
    {
        return;
    }
    match &col.data {
        ColumnData::Unit(_) => out.push_str("Unit"),
        ColumnData::Bool(v) => out.push_str(if v[row] != 0 { "true" } else { "false" }),
        ColumnData::Int(v) => {
            let _ = write!(out, "{}", v[row]);
        }
        ColumnData::Decimal(v) => render_decimal_i128_into(out, v[row]),
        ColumnData::Float(v) => {
            let fv = Float64::from_bits(v[row]).to_f64();
            if fv.is_finite() {
                let _ = write!(out, "{fv}");
            }
        }
        ColumnData::Text { .. } => {
            if let Some(s) = col.data.text_at(row) {
                push_csv_escaped(out, s, delimiter);
            }
        }
        ColumnData::Bytes { .. } => {
            if let Some(bs) = col.data.bytes_at(row) {
                match std::str::from_utf8(bs) {
                    Ok(s) => push_csv_escaped(out, s, delimiter),
                    Err(_) => {
                        let hex = to_hex_lower(bs);
                        out.push_str(&hex);
                    }
                }
            }
        }
        ColumnData::Date(v) => out.push_str(&format_iso_date(v[row])),
        ColumnData::Timestamp(v) => out.push_str(&format_iso_timestamp(v[row])),
        ColumnData::Duration(v) => {
            let _ = write!(out, "duration({})", v[row]);
        }
        ColumnData::Generic(v) => {
            let rendered = render_csv_cell(&v[row]);
            push_csv_escaped(out, &rendered, delimiter);
        }
    }
}

/// Stream a columnar [`VmTable`] as RFC 4180 CSV/TSV directly to any [`Write`] sink
/// without materializing row-wise [`TableVal`] rows.
///
/// # Errors
/// Returns any underlying I/O error.
pub fn write_csv_vm_table<W: Write>(writer: &mut W, vm: &VmTable, delimiter: u8) -> io::Result<()> {
    let delim = delimiter as char;
    let mut line = String::with_capacity(256);
    for (i, c) in vm.cols.iter().enumerate() {
        if i > 0 {
            line.push(delim);
        }
        push_csv_escaped(&mut line, &c.name, delimiter);
    }
    line.push('\n');
    writer.write_all(line.as_bytes())?;

    for batch in &vm.batches {
        if batch.is_empty() {
            continue;
        }
        match &batch.selection {
            Some(sel) => {
                for &r_u16 in sel {
                    let r = usize::from(r_u16);
                    line.clear();
                    for (i, col) in batch.cols.iter().enumerate() {
                        if i > 0 {
                            line.push(delim);
                        }
                        push_column_csv_cell(&mut line, col, r, delimiter);
                    }
                    line.push('\n');
                    writer.write_all(line.as_bytes())?;
                }
            }
            None => {
                for r in 0..batch.len {
                    line.clear();
                    for (i, col) in batch.cols.iter().enumerate() {
                        if i > 0 {
                            line.push(delim);
                        }
                        push_column_csv_cell(&mut line, col, r, delimiter);
                    }
                    line.push('\n');
                    writer.write_all(line.as_bytes())?;
                }
            }
        }
    }
    Ok(())
}

/// Format a columnar [`VmTable`] as RFC 4180 CSV text directly from columnar batches.
#[must_use]
pub fn format_csv_vm_table(vm: &VmTable, delimiter: u8) -> String {
    let mut buf = Vec::new();
    let _ = write_csv_vm_table(&mut buf, vm, delimiter);
    String::from_utf8(buf).unwrap_or_default()
}

/// Stream a [`TableVal`] as RFC 4180 CSV/TSV directly to any [`Write`] sink.
///
/// # Errors
/// Returns any underlying I/O error.
pub fn write_csv_table<W: Write>(writer: &mut W, tv: &TableVal, delimiter: u8) -> io::Result<()> {
    let delim = delimiter as char;
    let mut line = String::new();
    for (i, c) in tv.cols.iter().enumerate() {
        if i > 0 {
            line.push(delim);
        }
        push_csv_escaped(&mut line, &c.name, delimiter);
    }
    line.push('\n');
    writer.write_all(line.as_bytes())?;

    for row in &tv.rows {
        line.clear();
        for (i, cell) in row.cells.iter().enumerate() {
            if i > 0 {
                line.push(delim);
            }
            let rendered = render_csv_cell(cell);
            push_csv_escaped(&mut line, &rendered, delimiter);
        }
        line.push('\n');
        writer.write_all(line.as_bytes())?;
    }
    Ok(())
}

/// Format a [`TableVal`] as RFC 4180 CSV text.
#[must_use]
pub fn format_csv_table(tv: &TableVal, delimiter: u8) -> String {
    let mut buf = Vec::new();
    let _ = write_csv_table(&mut buf, tv, delimiter);
    String::from_utf8(buf).unwrap_or_default()
}

/// Render a single [`Val`] cell for CSV/TSV output.
#[must_use]
pub fn render_csv_cell(v: &Val) -> String {
    match v {
        Val::OptNone => String::new(),
        Val::OptSome(inner) => render_csv_cell(inner),
        Val::Text(s) => s.clone(),
        Val::Float(f) => {
            let fv = f.to_f64();
            if fv.is_finite() {
                format!("{fv}")
            } else {
                String::new()
            }
        }
        Val::Bytes(bs) => match std::str::from_utf8(bs) {
            Ok(s) => s.to_string(),
            Err(_) => to_hex_lower(bs),
        },
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

/// Append a single RFC 4180-escaped field to `out`.
pub fn push_csv_escaped(out: &mut String, field: &str, delimiter: u8) {
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
