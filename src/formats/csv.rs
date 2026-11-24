//! Streaming RFC 4180 CSV/TSV parser, writer, and schema-validated quarantine loader (`(valid_rows, bad_rows)`).
//!
//! Reads arbitrarily large plain, `.gz`, or `.zst` CSV/TSV files in bounded 2,048-row batches
//! over any [`BufRead`], preserving exact 1-based line numbers across multiline quoted fields
//! and enforcing `quarantine_bad_row_table_ty` sensitivity tag propagation on `bad_rows`.

use std::fmt;
use std::io::{self, BufRead, BufReader, Cursor, Read, Write};

use crate::core::bigint::BigInt;
use crate::core::check::quarantine_bad_row_table_ty;
use crate::core::syntax::{Float64, ScalarTy, TableTy};
use crate::formats::crypto::to_hex_lower;
use crate::formats::time::{parse_decimal_bigint_strict, parse_iso_date, parse_iso_timestamp};
use crate::oracle::value::{TableRow, TableVal, Val};

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
    let mut batch_reader = CsvBatchReader::new(BufReader::new(reader), delimiter);
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

    loop {
        let batch = batch_reader
            .next_batch(CSV_BATCH_SIZE)
            .map_err(|e| e.to_string())?;
        if batch.is_empty() {
            break;
        }
        for rec in batch {
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
                            bad_hit =
                                Some((col.name.as_str(), "ConstraintFailed", raw_val.clone()));
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
                        Val::Text(rec.raw_line),
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
