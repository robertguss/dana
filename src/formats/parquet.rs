//! Native zero-crate Apache Parquet reader and writer (`#[forbid(unsafe_code)]`).
//!
//! Implements:
//! - Pure-Rust Thrift Compact Protocol (`TCompactProtocol`) encoder & decoder for Parquet metadata
//! - Pure-Rust Snappy block decompressor (`UNCOMPRESSED`, `SNAPPY`, `GZIP`, `ZSTD` reader codecs;
//!   `UNCOMPRESSED`, `GZIP`, `ZSTD` writer codecs via allowlisted `src/ffi/{zlib,zstd}.rs`)
//! - `PLAIN` and `RLE_DICTIONARY` / `PLAIN_DICTIONARY` decoding (`DataPage` v1 & v2)
//! - RLE/Bit-Packing Hybrid definition levels (`OPTIONAL` columns) and dictionary indices
//! - Lossless Dana `ScalarTy` <-> Parquet physical/logical type mapping including 18-digit exact
//!   `Decimal` (`FIXED_LEN_BYTE_ARRAY(16)` with arbitrary-scale rescaling on read) and schema
//!   `where` constraint enforcement.

use std::collections::{HashMap, HashSet};
use std::fs;
use std::io::{Cursor, Read, Write};
use std::path::Path;

use crate::core::bigint::{BigInt, DEC_MAX, DEC_MIN};
use crate::core::syntax::{AggKind, ColSpec, Float64, ScalarTy, TableTy, TagSet};
use crate::ffi::{GzipReader, GzipWriter, ZstdReader, zstd_compress_block, zstd_decompress_block};
use crate::formats::constraint::FastColConstraint;
use crate::formats::infer::{
    InferredColumn, InferredSchema, InferredTy, looks_like_pii_column, sanitize_col_name,
};
use crate::oracle::value::{TableRow, TableVal, Val};
use crate::vm::batch::{Batch, Column, ColumnData, NullBitmap};
use crate::vm::ops::VmTable;

const PARQUET_MAGIC: &[u8; 4] = b"PAR1";
const DEFAULT_ROW_GROUP_ROWS: usize = 65_536;
const MAX_PARQUET_PAGE_BYTES: usize = 64 * 1024 * 1024;
const MAX_PARQUET_PAGE_VALUES: usize = 16 * 1024 * 1024;
const MAX_PARQUET_FOOTER_BYTES: usize = 32 * 1024 * 1024;
const MAX_THRIFT_SKIP_DEPTH: usize = 64;

// Thrift Compact Protocol wire types
const CT_BOOL_TRUE: u8 = 1;
const CT_BOOL_FALSE: u8 = 2;
const CT_BYTE: u8 = 3;
const CT_I16: u8 = 4;
const CT_I32: u8 = 5;
const CT_I64: u8 = 6;
const CT_DOUBLE: u8 = 7;
const CT_BINARY: u8 = 8;
const CT_LIST: u8 = 9;
const CT_SET: u8 = 10;
const CT_MAP: u8 = 11;
const CT_STRUCT: u8 = 12;

// Parquet physical Type enum
const PT_BOOLEAN: i32 = 0;
const PT_INT32: i32 = 1;
const PT_INT64: i32 = 2;
const PT_FLOAT: i32 = 4;
const PT_DOUBLE: i32 = 5;
const PT_BYTE_ARRAY: i32 = 6;
const PT_FIXED_LEN_BYTE_ARRAY: i32 = 7;

// Parquet ConvertedType enum
const CONV_UTF8: i32 = 0;
const CONV_DECIMAL: i32 = 5;
const CONV_DATE: i32 = 6;
const CONV_TIMESTAMP_MILLIS: i32 = 9;
const CONV_TIMESTAMP_MICROS: i32 = 10;

// Parquet FieldRepetitionType enum
const REP_REQUIRED: i32 = 0;
const REP_OPTIONAL: i32 = 1;
const REP_REPEATED: i32 = 2;

// Parquet Encoding enum
const ENC_PLAIN: i32 = 0;
const ENC_PLAIN_DICTIONARY: i32 = 2;
const ENC_RLE: i32 = 3;
const ENC_RLE_DICTIONARY: i32 = 8;

// Parquet CompressionCodec enum
const CODEC_UNCOMPRESSED: i32 = 0;
const CODEC_SNAPPY: i32 = 1;
const CODEC_GZIP: i32 = 2;
const CODEC_ZSTD: i32 = 6;

// Parquet PageType enum
const PAGE_DATA_V1: i32 = 0;
const PAGE_DICTIONARY: i32 = 2;
const PAGE_DATA_V2: i32 = 3;

/// Supported compression codecs when writing Parquet files.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub enum ParquetCompression {
    Uncompressed,
    Gzip,
    #[default]
    Zstd,
}

impl ParquetCompression {
    const fn to_thrift_codec(self) -> i32 {
        match self {
            Self::Uncompressed => CODEC_UNCOMPRESSED,
            Self::Gzip => CODEC_GZIP,
            Self::Zstd => CODEC_ZSTD,
        }
    }
}

/// Configuration options for writing Parquet files.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ParquetWriteOptions {
    pub compression: ParquetCompression,
    pub row_group_rows: usize,
}

impl Default for ParquetWriteOptions {
    fn default() -> Self {
        Self {
            compression: ParquetCompression::Zstd,
            row_group_rows: DEFAULT_ROW_GROUP_ROWS,
        }
    }
}

// ---------------------------------------------------------------------------
// Pure-Rust Snappy Block Decompressor (Parquet SNAPPY codec)
// ---------------------------------------------------------------------------

/// Decompress a raw Snappy block (standard Parquet `SNAPPY` page format) with strict
/// bounds checking and an output byte cap.
///
/// # Errors
/// Returns an error string if the input is malformed, truncated, has an invalid back-reference
/// offset, or exceeds `max_output_bytes`.
pub fn snappy_decompress(input: &[u8], max_output_bytes: usize) -> Result<Vec<u8>, String> {
    let mut pos = 0usize;
    let mut uncomp_len: usize = 0;
    let mut shift = 0u32;
    loop {
        let &b = input
            .get(pos)
            .ok_or_else(|| "truncated Snappy length varint".to_string())?;
        pos += 1;
        if shift >= 35 {
            return Err("Snappy uncompressed length varint overflow".to_string());
        }
        uncomp_len |= usize::from(b & 0x7F) << shift;
        if (b & 0x80) == 0 {
            break;
        }
        shift += 7;
    }

    if uncomp_len > max_output_bytes {
        return Err(format!(
            "Snappy uncompressed size ({uncomp_len}) exceeds limit ({max_output_bytes})"
        ));
    }

    let mut out = Vec::with_capacity(uncomp_len.min(1024 * 1024));
    while pos < input.len() {
        let tag = input[pos];
        pos += 1;
        match tag & 0x03 {
            0 => {
                // Literal bytes
                let len_code = usize::from(tag >> 2);
                let lit_len = if len_code < 60 {
                    len_code + 1
                } else {
                    let extra = len_code - 59; // 1..=4
                    if pos + extra > input.len() {
                        return Err("truncated Snappy literal length".to_string());
                    }
                    let mut n = 0usize;
                    for i in 0..extra {
                        n |= usize::from(input[pos + i]) << (i * 8);
                    }
                    pos += extra;
                    n.checked_add(1)
                        .ok_or_else(|| "Snappy literal length overflow".to_string())?
                };
                if pos.checked_add(lit_len).is_none_or(|end| end > input.len()) {
                    return Err("truncated Snappy literal payload".to_string());
                }
                if out
                    .len()
                    .checked_add(lit_len)
                    .is_none_or(|end| end > uncomp_len)
                {
                    return Err("Snappy literal exceeds declared uncompressed length".to_string());
                }
                out.extend_from_slice(&input[pos..pos + lit_len]);
                pos += lit_len;
            }
            1 => {
                // Copy with 1-byte offset
                let copy_len = usize::from((tag >> 2) & 0x07) + 4;
                let &lo = input
                    .get(pos)
                    .ok_or_else(|| "truncated Snappy 1-byte copy offset".to_string())?;
                pos += 1;
                let offset = (usize::from(tag & 0xE0) << 3) | usize::from(lo);
                snappy_copy(&mut out, offset, copy_len, uncomp_len)?;
            }
            2 => {
                // Copy with 2-byte little-endian offset
                let copy_len = usize::from(tag >> 2) + 1;
                if pos + 2 > input.len() {
                    return Err("truncated Snappy 2-byte copy offset".to_string());
                }
                let offset = usize::from(u16::from_le_bytes([input[pos], input[pos + 1]]));
                pos += 2;
                snappy_copy(&mut out, offset, copy_len, uncomp_len)?;
            }
            _ => {
                // Copy with 4-byte little-endian offset
                let copy_len = usize::from(tag >> 2) + 1;
                if pos + 4 > input.len() {
                    return Err("truncated Snappy 4-byte copy offset".to_string());
                }
                let offset = u32::from_le_bytes([
                    input[pos],
                    input[pos + 1],
                    input[pos + 2],
                    input[pos + 3],
                ]) as usize;
                pos += 4;
                snappy_copy(&mut out, offset, copy_len, uncomp_len)?;
            }
        }
    }

    if out.len() != uncomp_len {
        return Err(format!(
            "Snappy decompressed length mismatch: expected {uncomp_len}, got {}",
            out.len()
        ));
    }
    Ok(out)
}

fn snappy_copy(
    out: &mut Vec<u8>,
    offset: usize,
    copy_len: usize,
    uncomp_len: usize,
) -> Result<(), String> {
    if offset == 0 || offset > out.len() {
        return Err(format!(
            "invalid Snappy copy offset {offset} (output len {})",
            out.len()
        ));
    }
    if out
        .len()
        .checked_add(copy_len)
        .is_none_or(|end| end > uncomp_len)
    {
        return Err("Snappy copy exceeds declared uncompressed length".to_string());
    }
    let start = out.len() - offset;
    if offset >= copy_len {
        out.extend_from_within(start..start + copy_len);
    } else {
        // Overlapping RLE copy must proceed byte-by-byte.
        for i in 0..copy_len {
            let b = out[start + i];
            out.push(b);
        }
    }
    Ok(())
}

fn compress_page_bytes(raw: &[u8], codec: ParquetCompression) -> Result<Vec<u8>, String> {
    match codec {
        ParquetCompression::Uncompressed => Ok(raw.to_vec()),
        ParquetCompression::Gzip => {
            let mut w = GzipWriter::new(Vec::new()).map_err(|e| e.to_string())?;
            w.write_all(raw).map_err(|e| e.to_string())?;
            w.finish().map_err(|e| e.to_string())
        }
        ParquetCompression::Zstd => zstd_compress_block(raw, 3).map_err(|e| e.to_string()),
    }
}

fn decompress_page_bytes(
    compressed: &[u8],
    codec: i32,
    expected_uncompressed: usize,
) -> Result<Vec<u8>, String> {
    if expected_uncompressed > MAX_PARQUET_PAGE_BYTES {
        return Err(format!(
            "Parquet page uncompressed size ({expected_uncompressed}) exceeds limit ({MAX_PARQUET_PAGE_BYTES})"
        ));
    }
    let out = match codec {
        CODEC_UNCOMPRESSED => compressed.to_vec(),
        CODEC_SNAPPY => snappy_decompress(compressed, expected_uncompressed)?,
        CODEC_GZIP => {
            let r = GzipReader::new(Cursor::new(compressed)).map_err(|e| e.to_string())?;
            let mut limited = r.take((expected_uncompressed + 1) as u64);
            let mut buf = Vec::with_capacity(expected_uncompressed.min(1024 * 1024));
            limited.read_to_end(&mut buf).map_err(|e| e.to_string())?;
            buf
        }
        CODEC_ZSTD => {
            if let Some(buf) = zstd_decompress_block(compressed, expected_uncompressed)
                .map_err(|e| e.to_string())?
            {
                buf
            } else {
                let r = ZstdReader::new(Cursor::new(compressed)).map_err(|e| e.to_string())?;
                let mut limited = r.take((expected_uncompressed + 1) as u64);
                let mut buf = Vec::with_capacity(expected_uncompressed.min(1024 * 1024));
                limited.read_to_end(&mut buf).map_err(|e| e.to_string())?;
                buf
            }
        }
        other => {
            return Err(format!("unsupported Parquet compression codec `{other}`"));
        }
    };
    if out.len() != expected_uncompressed {
        return Err(format!(
            "Parquet page uncompressed length mismatch: expected {expected_uncompressed}, got {}",
            out.len()
        ));
    }
    Ok(out)
}

// ---------------------------------------------------------------------------
// Thrift Compact Protocol Encoder & Decoder
// ---------------------------------------------------------------------------

struct ThriftWriter {
    buf: Vec<u8>,
}

impl ThriftWriter {
    fn new() -> Self {
        Self { buf: Vec::new() }
    }

    fn into_bytes(self) -> Vec<u8> {
        self.buf
    }

    fn write_varint_u64(&mut self, mut v: u64) {
        loop {
            let byte = (v & 0x7F) as u8;
            v >>= 7;
            if v == 0 {
                self.buf.push(byte);
                break;
            }
            self.buf.push(byte | 0x80);
        }
    }

    fn write_zigzag_i32(&mut self, v: i32) {
        let zz = ((v << 1) ^ (v >> 31)) as u32;
        self.write_varint_u64(u64::from(zz));
    }

    fn write_zigzag_i64(&mut self, v: i64) {
        let zz = ((v << 1) ^ (v >> 63)) as u64;
        self.write_varint_u64(zz);
    }

    fn write_field_header(&mut self, last_id: &mut i16, field_id: i16, ctype: u8) {
        let delta = field_id - *last_id;
        if (1..=15).contains(&delta) {
            self.buf.push(((delta as u8) << 4) | (ctype & 0x0F));
        } else {
            self.buf.push(ctype & 0x0F);
            self.write_zigzag_i32(i32::from(field_id));
        }
        *last_id = field_id;
    }

    fn write_bool_field(&mut self, last_id: &mut i16, field_id: i16, val: bool) {
        let ct = if val { CT_BOOL_TRUE } else { CT_BOOL_FALSE };
        self.write_field_header(last_id, field_id, ct);
    }

    fn write_i32_field(&mut self, last_id: &mut i16, field_id: i16, val: i32) {
        self.write_field_header(last_id, field_id, CT_I32);
        self.write_zigzag_i32(val);
    }

    fn write_i64_field(&mut self, last_id: &mut i16, field_id: i16, val: i64) {
        self.write_field_header(last_id, field_id, CT_I64);
        self.write_zigzag_i64(val);
    }

    fn write_str(&mut self, s: &str) {
        self.write_varint_u64(s.len() as u64);
        self.buf.extend_from_slice(s.as_bytes());
    }

    fn write_str_field(&mut self, last_id: &mut i16, field_id: i16, s: &str) {
        self.write_field_header(last_id, field_id, CT_BINARY);
        self.write_str(s);
    }

    fn write_list_header(&mut self, elem_type: u8, len: usize) {
        if len < 15 {
            self.buf.push(((len as u8) << 4) | (elem_type & 0x0F));
        } else {
            self.buf.push(0xF0 | (elem_type & 0x0F));
            self.write_varint_u64(len as u64);
        }
    }

    fn write_stop(&mut self) {
        self.buf.push(0x00);
    }
}

struct ThriftReader<'a> {
    data: &'a [u8],
    pos: usize,
}

impl<'a> ThriftReader<'a> {
    fn new(data: &'a [u8]) -> Self {
        Self { data, pos: 0 }
    }

    fn read_byte(&mut self) -> Result<u8, String> {
        let &b = self
            .data
            .get(self.pos)
            .ok_or_else(|| "unexpected EOF in Thrift compact stream".to_string())?;
        self.pos += 1;
        Ok(b)
    }

    fn read_varint_u64(&mut self) -> Result<u64, String> {
        let mut res = 0u64;
        let mut shift = 0u32;
        loop {
            let b = self.read_byte()?;
            if shift >= 64 {
                return Err("Thrift varint u64 overflow".to_string());
            }
            res |= u64::from(b & 0x7F) << shift;
            if (b & 0x80) == 0 {
                return Ok(res);
            }
            shift += 7;
        }
    }

    fn read_zigzag_i16(&mut self) -> Result<i16, String> {
        let v = self.read_zigzag_i32()?;
        i16::try_from(v).map_err(|_| "Thrift i16 overflow".to_string())
    }

    fn read_zigzag_i32(&mut self) -> Result<i32, String> {
        let u = self.read_varint_u64()?;
        let u32v = u32::try_from(u).map_err(|_| "Thrift i32 zigzag overflow".to_string())?;
        Ok(((u32v >> 1) as i32) ^ -((u32v & 1) as i32))
    }

    fn read_zigzag_i64(&mut self) -> Result<i64, String> {
        let u = self.read_varint_u64()?;
        Ok(((u >> 1) as i64) ^ -((u & 1) as i64))
    }

    fn read_binary(&mut self) -> Result<&'a [u8], String> {
        let len_u64 = self.read_varint_u64()?;
        let len =
            usize::try_from(len_u64).map_err(|_| "Thrift binary length overflow".to_string())?;
        let end = self
            .pos
            .checked_add(len)
            .ok_or_else(|| "Thrift binary bounds overflow".to_string())?;
        if end > self.data.len() {
            return Err("truncated Thrift binary payload".to_string());
        }
        let slice = &self.data[self.pos..end];
        self.pos = end;
        Ok(slice)
    }

    fn read_string(&mut self) -> Result<String, String> {
        let bs = self.read_binary()?;
        std::str::from_utf8(bs)
            .map(ToOwned::to_owned)
            .map_err(|_| "invalid UTF-8 in Thrift string".to_string())
    }

    fn read_field_header(&mut self, last_id: &mut i16) -> Result<Option<(i16, u8)>, String> {
        let b = self.read_byte()?;
        if b == 0 {
            return Ok(None);
        }
        let delta = i16::from(b >> 4);
        let ctype = b & 0x0F;
        let field_id = if delta == 0 {
            self.read_zigzag_i16()?
        } else {
            last_id
                .checked_add(delta)
                .ok_or_else(|| "Thrift field ID overflow".to_string())?
        };
        *last_id = field_id;
        Ok(Some((field_id, ctype)))
    }

    fn read_list_header(&mut self) -> Result<(u8, usize), String> {
        let b = self.read_byte()?;
        let elem_type = b & 0x0F;
        let hi = (b >> 4) as usize;
        let count = if hi == 0x0F {
            let n = self.read_varint_u64()?;
            usize::try_from(n).map_err(|_| "Thrift list length overflow".to_string())?
        } else {
            hi
        };
        Ok((elem_type, count))
    }

    /// Iteratively skip an unknown Thrift Compact value (O(1) call stack, bounded nesting).
    fn skip_field(&mut self, ctype: u8) -> Result<(), String> {
        enum SkipTask {
            Field(u8),
            Elem(u8),
            Struct {
                depth: usize,
                last_id: i16,
            },
            Repeat {
                ctype: u8,
                count: usize,
                depth: usize,
            },
            MapEntries {
                ktype: u8,
                vtype: u8,
                count: usize,
                depth: usize,
            },
        }

        let mut stack = vec![SkipTask::Field(ctype)];
        while let Some(task) = stack.pop() {
            match task {
                SkipTask::Field(ct) => match ct {
                    CT_BOOL_TRUE | CT_BOOL_FALSE => {}
                    CT_BYTE => {
                        let _ = self.read_byte()?;
                    }
                    CT_I16 | CT_I32 | CT_I64 => {
                        let _ = self.read_varint_u64()?;
                    }
                    CT_DOUBLE => {
                        if self.pos + 8 > self.data.len() {
                            return Err("truncated Thrift double".to_string());
                        }
                        self.pos += 8;
                    }
                    CT_BINARY => {
                        let _ = self.read_binary()?;
                    }
                    CT_LIST | CT_SET => {
                        let (et, count) = self.read_list_header()?;
                        if count > 0 {
                            stack.push(SkipTask::Repeat {
                                ctype: et,
                                count,
                                depth: 1,
                            });
                        }
                    }
                    CT_MAP => {
                        let count_u64 = self.read_varint_u64()?;
                        let count = usize::try_from(count_u64)
                            .map_err(|_| "Thrift map length overflow".to_string())?;
                        if count > 0 {
                            let kv = self.read_byte()?;
                            stack.push(SkipTask::MapEntries {
                                ktype: kv >> 4,
                                vtype: kv & 0x0F,
                                count,
                                depth: 1,
                            });
                        }
                    }
                    CT_STRUCT => {
                        stack.push(SkipTask::Struct {
                            depth: 1,
                            last_id: 0,
                        });
                    }
                    other => {
                        return Err(format!("unknown Thrift compact type {other}"));
                    }
                },
                SkipTask::Elem(ct) => match ct {
                    CT_BOOL_TRUE | CT_BOOL_FALSE | CT_BYTE => {
                        let _ = self.read_byte()?;
                    }
                    other => stack.push(SkipTask::Field(other)),
                },
                SkipTask::Repeat {
                    ctype: et,
                    count,
                    depth,
                } => {
                    if depth > MAX_THRIFT_SKIP_DEPTH {
                        return Err("Thrift nesting depth exceeded".to_string());
                    }
                    if count > 1 {
                        stack.push(SkipTask::Repeat {
                            ctype: et,
                            count: count - 1,
                            depth,
                        });
                    }
                    match et {
                        CT_STRUCT => stack.push(SkipTask::Struct {
                            depth: depth + 1,
                            last_id: 0,
                        }),
                        CT_LIST | CT_SET => {
                            let (inner_et, inner_c) = self.read_list_header()?;
                            if inner_c > 0 {
                                stack.push(SkipTask::Repeat {
                                    ctype: inner_et,
                                    count: inner_c,
                                    depth: depth + 1,
                                });
                            }
                        }
                        CT_MAP => {
                            let inner_c = usize::try_from(self.read_varint_u64()?)
                                .map_err(|_| "Thrift map length overflow".to_string())?;
                            if inner_c > 0 {
                                let kv = self.read_byte()?;
                                stack.push(SkipTask::MapEntries {
                                    ktype: kv >> 4,
                                    vtype: kv & 0x0F,
                                    count: inner_c,
                                    depth: depth + 1,
                                });
                            }
                        }
                        other => stack.push(SkipTask::Elem(other)),
                    }
                }
                SkipTask::MapEntries {
                    ktype,
                    vtype,
                    count,
                    depth,
                } => {
                    if depth > MAX_THRIFT_SKIP_DEPTH {
                        return Err("Thrift nesting depth exceeded".to_string());
                    }
                    if count > 1 {
                        stack.push(SkipTask::MapEntries {
                            ktype,
                            vtype,
                            count: count - 1,
                            depth,
                        });
                    }
                    stack.push(SkipTask::Elem(vtype));
                    stack.push(SkipTask::Elem(ktype));
                }
                SkipTask::Struct { depth, mut last_id } => {
                    if depth > MAX_THRIFT_SKIP_DEPTH {
                        return Err("Thrift struct nesting depth exceeded".to_string());
                    }
                    if let Some((_, ct)) = self.read_field_header(&mut last_id)? {
                        // Continue reading remaining fields of this struct after skipping this field.
                        stack.push(SkipTask::Struct { depth, last_id });
                        match ct {
                            CT_STRUCT => stack.push(SkipTask::Struct {
                                depth: depth + 1,
                                last_id: 0,
                            }),
                            other => stack.push(SkipTask::Field(other)),
                        }
                    }
                }
            }
        }
        Ok(())
    }
}

// ---------------------------------------------------------------------------
// Parquet Thrift Metadata Structures
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum TimeUnit {
    Millis,
    Micros,
    Nanos,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum LogicalType {
    String,
    Decimal {
        scale: i32,
        precision: i32,
    },
    Date,
    Timestamp {
        is_adjusted_to_utc: bool,
        unit: TimeUnit,
    },
    Other,
}

#[derive(Clone, Debug)]
struct SchemaElement {
    phys_type: Option<i32>,
    type_length: Option<i32>,
    repetition_type: Option<i32>,
    name: String,
    num_children: Option<i32>,
    converted_type: Option<i32>,
    scale: Option<i32>,
    precision: Option<i32>,
    logical_type: Option<LogicalType>,
}

#[derive(Clone, Debug)]
struct ColumnMetaData {
    phys_type: i32,
    encodings: Vec<i32>,
    path_in_schema: Vec<String>,
    codec: i32,
    num_values: i64,
    total_uncompressed_size: i64,
    total_compressed_size: i64,
    data_page_offset: i64,
    dictionary_page_offset: Option<i64>,
}

#[derive(Clone, Debug)]
struct ColumnChunk {
    file_offset: i64,
    meta_data: Option<ColumnMetaData>,
}

#[derive(Clone, Debug)]
struct RowGroup {
    columns: Vec<ColumnChunk>,
    total_byte_size: i64,
    num_rows: i64,
}

#[derive(Clone, Debug)]
struct FileMetaData {
    version: i32,
    schema: Vec<SchemaElement>,
    num_rows: i64,
    row_groups: Vec<RowGroup>,
    created_by: Option<String>,
}

#[derive(Clone, Debug)]
struct DataPageHeader {
    num_values: i32,
    encoding: i32,
    definition_level_encoding: i32,
    repetition_level_encoding: i32,
}

#[derive(Clone, Debug)]
struct DictionaryPageHeader {
    num_values: i32,
    encoding: i32,
}

#[derive(Clone, Debug)]
struct DataPageHeaderV2 {
    num_values: i32,
    encoding: i32,
    definition_levels_byte_length: i32,
    repetition_levels_byte_length: i32,
    is_compressed: bool,
}

#[derive(Clone, Debug)]
struct PageHeader {
    page_type: i32,
    uncompressed_page_size: i32,
    compressed_page_size: i32,
    data_page_header: Option<DataPageHeader>,
    dictionary_page_header: Option<DictionaryPageHeader>,
    data_page_header_v2: Option<DataPageHeaderV2>,
}

// --- Thrift Encoding of Parquet Structs ---

fn write_logical_type(w: &mut ThriftWriter, lt: LogicalType) {
    let mut last = 0i16;
    match lt {
        LogicalType::String => {
            w.write_field_header(&mut last, 1, CT_STRUCT);
            w.write_stop();
        }
        LogicalType::Decimal { scale, precision } => {
            w.write_field_header(&mut last, 5, CT_STRUCT);
            let mut dlast = 0i16;
            w.write_i32_field(&mut dlast, 1, scale);
            w.write_i32_field(&mut dlast, 2, precision);
            w.write_stop();
        }
        LogicalType::Date => {
            w.write_field_header(&mut last, 6, CT_STRUCT);
            w.write_stop();
        }
        LogicalType::Timestamp {
            is_adjusted_to_utc,
            unit,
        } => {
            w.write_field_header(&mut last, 8, CT_STRUCT);
            let mut tlast = 0i16;
            w.write_bool_field(&mut tlast, 1, is_adjusted_to_utc);
            w.write_field_header(&mut tlast, 2, CT_STRUCT);
            let mut ulast = 0i16;
            let unit_fid = match unit {
                TimeUnit::Millis => 1,
                TimeUnit::Micros => 2,
                TimeUnit::Nanos => 3,
            };
            w.write_field_header(&mut ulast, unit_fid, CT_STRUCT);
            w.write_stop();
            w.write_stop();
            w.write_stop();
        }
        LogicalType::Other => {}
    }
    w.write_stop();
}

fn write_schema_element(w: &mut ThriftWriter, se: &SchemaElement) {
    let mut last = 0i16;
    if let Some(pt) = se.phys_type {
        w.write_i32_field(&mut last, 1, pt);
    }
    if let Some(tl) = se.type_length {
        w.write_i32_field(&mut last, 2, tl);
    }
    if let Some(rep) = se.repetition_type {
        w.write_i32_field(&mut last, 3, rep);
    }
    w.write_str_field(&mut last, 4, &se.name);
    if let Some(nc) = se.num_children {
        w.write_i32_field(&mut last, 5, nc);
    }
    if let Some(ct) = se.converted_type {
        w.write_i32_field(&mut last, 6, ct);
    }
    if let Some(sc) = se.scale {
        w.write_i32_field(&mut last, 7, sc);
    }
    if let Some(pr) = se.precision {
        w.write_i32_field(&mut last, 8, pr);
    }
    if let Some(lt) = se.logical_type {
        w.write_field_header(&mut last, 10, CT_STRUCT);
        write_logical_type(w, lt);
    }
    w.write_stop();
}

fn write_column_metadata(w: &mut ThriftWriter, cm: &ColumnMetaData) {
    let mut last = 0i16;
    w.write_i32_field(&mut last, 1, cm.phys_type);
    w.write_field_header(&mut last, 2, CT_LIST);
    w.write_list_header(CT_I32, cm.encodings.len());
    for &enc in &cm.encodings {
        w.write_zigzag_i32(enc);
    }
    w.write_field_header(&mut last, 3, CT_LIST);
    w.write_list_header(CT_BINARY, cm.path_in_schema.len());
    for seg in &cm.path_in_schema {
        w.write_str(seg);
    }
    w.write_i32_field(&mut last, 4, cm.codec);
    w.write_i64_field(&mut last, 5, cm.num_values);
    w.write_i64_field(&mut last, 6, cm.total_uncompressed_size);
    w.write_i64_field(&mut last, 7, cm.total_compressed_size);
    w.write_i64_field(&mut last, 9, cm.data_page_offset);
    if let Some(doff) = cm.dictionary_page_offset {
        w.write_i64_field(&mut last, 11, doff);
    }
    w.write_stop();
}

fn write_column_chunk(w: &mut ThriftWriter, cc: &ColumnChunk) {
    let mut last = 0i16;
    w.write_i64_field(&mut last, 2, cc.file_offset);
    if let Some(cm) = &cc.meta_data {
        w.write_field_header(&mut last, 3, CT_STRUCT);
        write_column_metadata(w, cm);
    }
    w.write_stop();
}

fn write_row_group(w: &mut ThriftWriter, rg: &RowGroup) {
    let mut last = 0i16;
    w.write_field_header(&mut last, 1, CT_LIST);
    w.write_list_header(CT_STRUCT, rg.columns.len());
    for cc in &rg.columns {
        write_column_chunk(w, cc);
    }
    w.write_i64_field(&mut last, 2, rg.total_byte_size);
    w.write_i64_field(&mut last, 3, rg.num_rows);
    w.write_stop();
}

fn write_file_metadata(w: &mut ThriftWriter, fm: &FileMetaData) {
    let mut last = 0i16;
    w.write_i32_field(&mut last, 1, fm.version);
    w.write_field_header(&mut last, 2, CT_LIST);
    w.write_list_header(CT_STRUCT, fm.schema.len());
    for se in &fm.schema {
        write_schema_element(w, se);
    }
    w.write_i64_field(&mut last, 3, fm.num_rows);
    w.write_field_header(&mut last, 4, CT_LIST);
    w.write_list_header(CT_STRUCT, fm.row_groups.len());
    for rg in &fm.row_groups {
        write_row_group(w, rg);
    }
    if let Some(cb) = &fm.created_by {
        w.write_str_field(&mut last, 6, cb);
    }
    w.write_stop();
}

fn write_page_header(w: &mut ThriftWriter, ph: &PageHeader) {
    let mut last = 0i16;
    w.write_i32_field(&mut last, 1, ph.page_type);
    w.write_i32_field(&mut last, 2, ph.uncompressed_page_size);
    w.write_i32_field(&mut last, 3, ph.compressed_page_size);
    if let Some(dph) = &ph.data_page_header {
        w.write_field_header(&mut last, 5, CT_STRUCT);
        let mut dlast = 0i16;
        w.write_i32_field(&mut dlast, 1, dph.num_values);
        w.write_i32_field(&mut dlast, 2, dph.encoding);
        w.write_i32_field(&mut dlast, 3, dph.definition_level_encoding);
        w.write_i32_field(&mut dlast, 4, dph.repetition_level_encoding);
        w.write_stop();
    }
    w.write_stop();
}

// --- Thrift Decoding of Parquet Structs ---

fn read_logical_type(r: &mut ThriftReader<'_>) -> Result<LogicalType, String> {
    let mut last = 0i16;
    let mut result = LogicalType::Other;
    while let Some((fid, ct)) = r.read_field_header(&mut last)? {
        match (fid, ct) {
            (1, CT_STRUCT) => {
                r.skip_field(CT_STRUCT)?;
                result = LogicalType::String;
            }
            (5, CT_STRUCT) => {
                let mut dlast = 0i16;
                let mut scale = 0i32;
                let mut precision = 0i32;
                while let Some((dfid, dct)) = r.read_field_header(&mut dlast)? {
                    match (dfid, dct) {
                        (1, CT_I32) => scale = r.read_zigzag_i32()?,
                        (2, CT_I32) => precision = r.read_zigzag_i32()?,
                        _ => r.skip_field(dct)?,
                    }
                }
                result = LogicalType::Decimal { scale, precision };
            }
            (6, CT_STRUCT) => {
                r.skip_field(CT_STRUCT)?;
                result = LogicalType::Date;
            }
            (8, CT_STRUCT) => {
                let mut tlast = 0i16;
                let mut is_utc = true;
                let mut unit = TimeUnit::Micros;
                while let Some((tfid, tct)) = r.read_field_header(&mut tlast)? {
                    match (tfid, tct) {
                        (1, CT_BOOL_TRUE) => is_utc = true,
                        (1, CT_BOOL_FALSE) => is_utc = false,
                        (2, CT_STRUCT) => {
                            let mut ulast = 0i16;
                            while let Some((ufid, uct)) = r.read_field_header(&mut ulast)? {
                                match (ufid, uct) {
                                    (1, CT_STRUCT) => {
                                        r.skip_field(CT_STRUCT)?;
                                        unit = TimeUnit::Millis;
                                    }
                                    (2, CT_STRUCT) => {
                                        r.skip_field(CT_STRUCT)?;
                                        unit = TimeUnit::Micros;
                                    }
                                    (3, CT_STRUCT) => {
                                        r.skip_field(CT_STRUCT)?;
                                        unit = TimeUnit::Nanos;
                                    }
                                    _ => r.skip_field(uct)?,
                                }
                            }
                        }
                        _ => r.skip_field(tct)?,
                    }
                }
                result = LogicalType::Timestamp {
                    is_adjusted_to_utc: is_utc,
                    unit,
                };
            }
            _ => r.skip_field(ct)?,
        }
    }
    Ok(result)
}

fn read_schema_element(r: &mut ThriftReader<'_>) -> Result<SchemaElement, String> {
    let mut last = 0i16;
    let mut se = SchemaElement {
        phys_type: None,
        type_length: None,
        repetition_type: None,
        name: String::new(),
        num_children: None,
        converted_type: None,
        scale: None,
        precision: None,
        logical_type: None,
    };
    while let Some((fid, ct)) = r.read_field_header(&mut last)? {
        match (fid, ct) {
            (1, CT_I32) => se.phys_type = Some(r.read_zigzag_i32()?),
            (2, CT_I32) => se.type_length = Some(r.read_zigzag_i32()?),
            (3, CT_I32) => se.repetition_type = Some(r.read_zigzag_i32()?),
            (4, CT_BINARY) => se.name = r.read_string()?,
            (5, CT_I32) => se.num_children = Some(r.read_zigzag_i32()?),
            (6, CT_I32) => se.converted_type = Some(r.read_zigzag_i32()?),
            (7, CT_I32) => se.scale = Some(r.read_zigzag_i32()?),
            (8, CT_I32) => se.precision = Some(r.read_zigzag_i32()?),
            (10, CT_STRUCT) => se.logical_type = Some(read_logical_type(r)?),
            _ => r.skip_field(ct)?,
        }
    }
    Ok(se)
}

fn read_column_metadata(r: &mut ThriftReader<'_>) -> Result<ColumnMetaData, String> {
    let mut last = 0i16;
    let mut cm = ColumnMetaData {
        phys_type: 0,
        encodings: Vec::new(),
        path_in_schema: Vec::new(),
        codec: CODEC_UNCOMPRESSED,
        num_values: 0,
        total_uncompressed_size: 0,
        total_compressed_size: 0,
        data_page_offset: 0,
        dictionary_page_offset: None,
    };
    while let Some((fid, ct)) = r.read_field_header(&mut last)? {
        match (fid, ct) {
            (1, CT_I32) => cm.phys_type = r.read_zigzag_i32()?,
            (2, CT_LIST) => {
                let (_, count) = r.read_list_header()?;
                for _ in 0..count {
                    cm.encodings.push(r.read_zigzag_i32()?);
                }
            }
            (3, CT_LIST) => {
                let (_, count) = r.read_list_header()?;
                for _ in 0..count {
                    cm.path_in_schema.push(r.read_string()?);
                }
            }
            (4, CT_I32) => cm.codec = r.read_zigzag_i32()?,
            (5, CT_I64) => cm.num_values = r.read_zigzag_i64()?,
            (6, CT_I64) => cm.total_uncompressed_size = r.read_zigzag_i64()?,
            (7, CT_I64) => cm.total_compressed_size = r.read_zigzag_i64()?,
            (9, CT_I64) => cm.data_page_offset = r.read_zigzag_i64()?,
            (11, CT_I64) => cm.dictionary_page_offset = Some(r.read_zigzag_i64()?),
            _ => r.skip_field(ct)?,
        }
    }
    Ok(cm)
}

fn read_column_chunk(r: &mut ThriftReader<'_>) -> Result<ColumnChunk, String> {
    let mut last = 0i16;
    let mut cc = ColumnChunk {
        file_offset: 0,
        meta_data: None,
    };
    while let Some((fid, ct)) = r.read_field_header(&mut last)? {
        match (fid, ct) {
            (2, CT_I64) => cc.file_offset = r.read_zigzag_i64()?,
            (3, CT_STRUCT) => cc.meta_data = Some(read_column_metadata(r)?),
            _ => r.skip_field(ct)?,
        }
    }
    Ok(cc)
}

fn read_row_group(r: &mut ThriftReader<'_>) -> Result<RowGroup, String> {
    let mut last = 0i16;
    let mut rg = RowGroup {
        columns: Vec::new(),
        total_byte_size: 0,
        num_rows: 0,
    };
    while let Some((fid, ct)) = r.read_field_header(&mut last)? {
        match (fid, ct) {
            (1, CT_LIST) => {
                let (_, count) = r.read_list_header()?;
                for _ in 0..count {
                    rg.columns.push(read_column_chunk(r)?);
                }
            }
            (2, CT_I64) => rg.total_byte_size = r.read_zigzag_i64()?,
            (3, CT_I64) => rg.num_rows = r.read_zigzag_i64()?,
            _ => r.skip_field(ct)?,
        }
    }
    Ok(rg)
}

fn read_file_metadata(r: &mut ThriftReader<'_>) -> Result<FileMetaData, String> {
    let mut last = 0i16;
    let mut fm = FileMetaData {
        version: 1,
        schema: Vec::new(),
        num_rows: 0,
        row_groups: Vec::new(),
        created_by: None,
    };
    while let Some((fid, ct)) = r.read_field_header(&mut last)? {
        match (fid, ct) {
            (1, CT_I32) => fm.version = r.read_zigzag_i32()?,
            (2, CT_LIST) => {
                let (_, count) = r.read_list_header()?;
                for _ in 0..count {
                    fm.schema.push(read_schema_element(r)?);
                }
            }
            (3, CT_I64) => fm.num_rows = r.read_zigzag_i64()?,
            (4, CT_LIST) => {
                let (_, count) = r.read_list_header()?;
                for _ in 0..count {
                    fm.row_groups.push(read_row_group(r)?);
                }
            }
            (6, CT_BINARY) => fm.created_by = Some(r.read_string()?),
            _ => r.skip_field(ct)?,
        }
    }
    Ok(fm)
}

fn read_page_header(r: &mut ThriftReader<'_>) -> Result<PageHeader, String> {
    let mut last = 0i16;
    let mut ph = PageHeader {
        page_type: 0,
        uncompressed_page_size: 0,
        compressed_page_size: 0,
        data_page_header: None,
        dictionary_page_header: None,
        data_page_header_v2: None,
    };
    while let Some((fid, ct)) = r.read_field_header(&mut last)? {
        match (fid, ct) {
            (1, CT_I32) => ph.page_type = r.read_zigzag_i32()?,
            (2, CT_I32) => ph.uncompressed_page_size = r.read_zigzag_i32()?,
            (3, CT_I32) => ph.compressed_page_size = r.read_zigzag_i32()?,
            (5, CT_STRUCT) => {
                let mut dlast = 0i16;
                let mut dph = DataPageHeader {
                    num_values: 0,
                    encoding: ENC_PLAIN,
                    definition_level_encoding: ENC_RLE,
                    repetition_level_encoding: ENC_RLE,
                };
                while let Some((dfid, dct)) = r.read_field_header(&mut dlast)? {
                    match (dfid, dct) {
                        (1, CT_I32) => dph.num_values = r.read_zigzag_i32()?,
                        (2, CT_I32) => dph.encoding = r.read_zigzag_i32()?,
                        (3, CT_I32) => dph.definition_level_encoding = r.read_zigzag_i32()?,
                        (4, CT_I32) => dph.repetition_level_encoding = r.read_zigzag_i32()?,
                        _ => r.skip_field(dct)?,
                    }
                }
                ph.data_page_header = Some(dph);
            }
            (7, CT_STRUCT) => {
                let mut dlast = 0i16;
                let mut dict = DictionaryPageHeader {
                    num_values: 0,
                    encoding: ENC_PLAIN,
                };
                while let Some((dfid, dct)) = r.read_field_header(&mut dlast)? {
                    match (dfid, dct) {
                        (1, CT_I32) => dict.num_values = r.read_zigzag_i32()?,
                        (2, CT_I32) => dict.encoding = r.read_zigzag_i32()?,
                        _ => r.skip_field(dct)?,
                    }
                }
                ph.dictionary_page_header = Some(dict);
            }
            (8, CT_STRUCT) => {
                let mut dlast = 0i16;
                let mut v2 = DataPageHeaderV2 {
                    num_values: 0,
                    encoding: ENC_PLAIN,
                    definition_levels_byte_length: 0,
                    repetition_levels_byte_length: 0,
                    is_compressed: true,
                };
                while let Some((dfid, dct)) = r.read_field_header(&mut dlast)? {
                    match (dfid, dct) {
                        (1, CT_I32) => v2.num_values = r.read_zigzag_i32()?,
                        (4, CT_I32) => v2.encoding = r.read_zigzag_i32()?,
                        (5, CT_I32) => v2.definition_levels_byte_length = r.read_zigzag_i32()?,
                        (6, CT_I32) => v2.repetition_levels_byte_length = r.read_zigzag_i32()?,
                        (7, CT_BOOL_TRUE) => v2.is_compressed = true,
                        (7, CT_BOOL_FALSE) => v2.is_compressed = false,
                        _ => r.skip_field(dct)?,
                    }
                }
                ph.data_page_header_v2 = Some(v2);
            }
            _ => r.skip_field(ct)?,
        }
    }
    Ok(ph)
}

// ---------------------------------------------------------------------------
// RLE / Bit-Packing Hybrid Codec
// ---------------------------------------------------------------------------

fn write_uvarint(out: &mut Vec<u8>, mut v: u64) {
    loop {
        let byte = (v & 0x7F) as u8;
        v >>= 7;
        if v == 0 {
            out.push(byte);
            break;
        }
        out.push(byte | 0x80);
    }
}

fn read_uvarint(data: &[u8], pos: &mut usize) -> Result<u64, String> {
    let mut res = 0u64;
    let mut shift = 0u32;
    loop {
        let &b = data
            .get(*pos)
            .ok_or_else(|| "truncated RLE varint header".to_string())?;
        *pos += 1;
        if shift >= 64 {
            return Err("RLE varint header overflow".to_string());
        }
        res |= u64::from(b & 0x7F) << shift;
        if (b & 0x80) == 0 {
            return Ok(res);
        }
        shift += 7;
    }
}

/// Encode `values` using Parquet's RLE/Bit-Packing Hybrid encoding for `bit_width` (1..=32).
fn encode_rle_hybrid(values: &[u32], bit_width: u8) -> Vec<u8> {
    if bit_width == 0 || values.is_empty() {
        return Vec::new();
    }
    let byte_width = usize::from(bit_width).div_ceil(8);
    let mut out = Vec::new();
    let mut i = 0usize;
    while i < values.len() {
        let val = values[i];
        let mut run = 1usize;
        while i + run < values.len() && values[i + run] == val {
            run += 1;
        }
        // RLE run header: `(run_len << 1) | 0`
        write_uvarint(&mut out, (run as u64) << 1);
        let le = val.to_le_bytes();
        out.extend_from_slice(&le[..byte_width]);
        i += run;
    }
    out
}

/// Decode `count` values from Parquet's RLE/Bit-Packing Hybrid stream for `bit_width` (0..=32).
fn decode_rle_hybrid(data: &[u8], bit_width: u8, count: usize) -> Result<Vec<u32>, String> {
    if count == 0 {
        return Ok(Vec::new());
    }
    if count > MAX_PARQUET_PAGE_VALUES {
        return Err(format!(
            "Parquet RLE value count ({count}) exceeds limit ({MAX_PARQUET_PAGE_VALUES})"
        ));
    }
    if bit_width == 0 {
        return Ok(vec![0u32; count]);
    }
    if bit_width > 32 {
        return Err(format!("unsupported RLE bit_width {bit_width}"));
    }
    let bw = usize::from(bit_width);
    let byte_width = bw.div_ceil(8);
    let mask: u64 = if bit_width == 32 {
        u64::from(u32::MAX)
    } else {
        (1u64 << bit_width) - 1
    };

    let mut out = Vec::with_capacity(count.min(65_536));
    let mut pos = 0usize;
    while out.len() < count {
        let header = read_uvarint(data, &mut pos)?;
        if (header & 1) == 0 {
            // RLE run
            let run_len = usize::try_from(header >> 1)
                .map_err(|_| "Parquet RLE run length overflow".to_string())?;
            if pos
                .checked_add(byte_width)
                .is_none_or(|end| end > data.len())
            {
                return Err("truncated Parquet RLE run value".to_string());
            }
            let mut val = 0u32;
            for j in 0..byte_width {
                val |= u32::from(data[pos + j]) << (j * 8);
            }
            pos += byte_width;
            let take = run_len.min(count - out.len());
            out.resize(out.len() + take, val);
        } else {
            // Bit-packed run: `(num_groups << 1) | 1`, 8 values per group
            let num_groups = usize::try_from(header >> 1)
                .map_err(|_| "Parquet bit-packed group count overflow".to_string())?;
            let total_bytes = num_groups
                .checked_mul(bw)
                .ok_or_else(|| "Parquet bit-packed byte length overflow".to_string())?;
            let Some(end) = pos.checked_add(total_bytes) else {
                return Err("Parquet bit-packed bounds overflow".to_string());
            };
            if end > data.len() {
                return Err("truncated Parquet bit-packed run".to_string());
            }
            let slice = &data[pos..end];
            pos = end;

            let total_vals = num_groups
                .checked_mul(8)
                .ok_or_else(|| "Parquet bit-packed value count overflow".to_string())?;
            let mut bit_cursor = 0usize;
            for _ in 0..total_vals {
                if out.len() >= count {
                    break;
                }
                let byte_idx = bit_cursor / 8;
                let bit_off = bit_cursor % 8;
                let mut acc = 0u64;
                let need_bytes = (bit_off + bw).div_ceil(8);
                for k in 0..need_bytes {
                    if let Some(&b) = slice.get(byte_idx + k) {
                        acc |= u64::from(b) << (k * 8);
                    }
                }
                let val = ((acc >> bit_off) & mask) as u32;
                out.push(val);
                bit_cursor += bw;
            }
        }
    }
    Ok(out)
}

// ---------------------------------------------------------------------------
// Physical Value Encoding & Decoding (PLAIN & Dictionary)
// ---------------------------------------------------------------------------

#[derive(Clone, Debug)]
enum RawParquetVal {
    Bool(bool),
    Int32(i32),
    Int64(i64),
    Float(f32),
    Double(f64),
    Bytes(Vec<u8>),
}

fn decode_plain_values(
    data: &[u8],
    phys_type: i32,
    type_length: Option<i32>,
    count: usize,
) -> Result<(Vec<RawParquetVal>, usize), String> {
    if count > MAX_PARQUET_PAGE_VALUES {
        return Err(format!(
            "Parquet PLAIN value count ({count}) exceeds limit ({MAX_PARQUET_PAGE_VALUES})"
        ));
    }
    let mut vals = Vec::with_capacity(count.min(65_536));
    let mut pos = 0usize;
    match phys_type {
        PT_BOOLEAN => {
            let need_bytes = count.div_ceil(8);
            if need_bytes > data.len() {
                return Err("truncated Parquet BOOLEAN PLAIN payload".to_string());
            }
            for i in 0..count {
                let bit = (data[i / 8] >> (i % 8)) & 1;
                vals.push(RawParquetVal::Bool(bit != 0));
            }
            pos = need_bytes;
        }
        PT_INT32 => {
            let need = count
                .checked_mul(4)
                .ok_or_else(|| "Parquet INT32 byte size overflow".to_string())?;
            if need > data.len() {
                return Err("truncated Parquet INT32 PLAIN payload".to_string());
            }
            for chunk in data[..need].chunks_exact(4) {
                let arr: [u8; 4] = chunk
                    .try_into()
                    .map_err(|_| "INT32 chunk error".to_string())?;
                vals.push(RawParquetVal::Int32(i32::from_le_bytes(arr)));
            }
            pos = need;
        }
        PT_INT64 => {
            let need = count
                .checked_mul(8)
                .ok_or_else(|| "Parquet INT64 byte size overflow".to_string())?;
            if need > data.len() {
                return Err("truncated Parquet INT64 PLAIN payload".to_string());
            }
            for chunk in data[..need].chunks_exact(8) {
                let arr: [u8; 8] = chunk
                    .try_into()
                    .map_err(|_| "INT64 chunk error".to_string())?;
                vals.push(RawParquetVal::Int64(i64::from_le_bytes(arr)));
            }
            pos = need;
        }
        PT_FLOAT => {
            let need = count
                .checked_mul(4)
                .ok_or_else(|| "Parquet FLOAT byte size overflow".to_string())?;
            if need > data.len() {
                return Err("truncated Parquet FLOAT PLAIN payload".to_string());
            }
            for chunk in data[..need].chunks_exact(4) {
                let arr: [u8; 4] = chunk
                    .try_into()
                    .map_err(|_| "FLOAT chunk error".to_string())?;
                vals.push(RawParquetVal::Float(f32::from_le_bytes(arr)));
            }
            pos = need;
        }
        PT_DOUBLE => {
            let need = count
                .checked_mul(8)
                .ok_or_else(|| "Parquet DOUBLE byte size overflow".to_string())?;
            if need > data.len() {
                return Err("truncated Parquet DOUBLE PLAIN payload".to_string());
            }
            for chunk in data[..need].chunks_exact(8) {
                let arr: [u8; 8] = chunk
                    .try_into()
                    .map_err(|_| "DOUBLE chunk error".to_string())?;
                vals.push(RawParquetVal::Double(f64::from_le_bytes(arr)));
            }
            pos = need;
        }
        PT_BYTE_ARRAY => {
            for _ in 0..count {
                if pos + 4 > data.len() {
                    return Err("truncated Parquet BYTE_ARRAY length prefix".to_string());
                }
                let arr: [u8; 4] = data[pos..pos + 4]
                    .try_into()
                    .map_err(|_| "BYTE_ARRAY len slice error".to_string())?;
                pos += 4;
                let len = u32::from_le_bytes(arr) as usize;
                let end = pos
                    .checked_add(len)
                    .ok_or_else(|| "Parquet BYTE_ARRAY bounds overflow".to_string())?;
                if end > data.len() {
                    return Err("truncated Parquet BYTE_ARRAY payload".to_string());
                }
                vals.push(RawParquetVal::Bytes(data[pos..end].to_vec()));
                pos = end;
            }
        }
        PT_FIXED_LEN_BYTE_ARRAY => {
            let flen = usize::try_from(
                type_length
                    .ok_or_else(|| "FIXED_LEN_BYTE_ARRAY missing `type_length`".to_string())?,
            )
            .map_err(|_| "negative FIXED_LEN_BYTE_ARRAY `type_length`".to_string())?;
            let need = count
                .checked_mul(flen)
                .ok_or_else(|| "Parquet FIXED_LEN_BYTE_ARRAY size overflow".to_string())?;
            if need > data.len() {
                return Err("truncated Parquet FIXED_LEN_BYTE_ARRAY payload".to_string());
            }
            if flen == 0 {
                for _ in 0..count {
                    vals.push(RawParquetVal::Bytes(Vec::new()));
                }
            } else {
                for chunk in data[..need].chunks_exact(flen) {
                    vals.push(RawParquetVal::Bytes(chunk.to_vec()));
                }
            }
            pos = need;
        }
        other => {
            return Err(format!("unsupported Parquet physical type `{other}`"));
        }
    }
    Ok((vals, pos))
}

fn encode_plain_column(
    col: &ColSpec,
    rows: &[TableRow],
    col_idx: usize,
) -> Result<(Vec<u8>, Option<Vec<u32>>), String> {
    let (inner_ty, is_opt) = peel_option(&col.ty);
    let mut def_levels = if is_opt {
        Some(Vec::with_capacity(rows.len()))
    } else {
        None
    };

    let mut non_null: Vec<&Val> = Vec::with_capacity(rows.len());
    for row in rows {
        let cell = row
            .cells
            .get(col_idx)
            .ok_or_else(|| format!("row missing cell for column `{}`", col.name))?;
        if is_opt {
            match cell {
                Val::OptNone => {
                    if let Some(dl) = def_levels.as_mut() {
                        dl.push(0);
                    }
                }
                Val::OptSome(inner) => {
                    if let Some(dl) = def_levels.as_mut() {
                        dl.push(1);
                    }
                    non_null.push(inner.as_ref());
                }
                other => {
                    if let Some(dl) = def_levels.as_mut() {
                        dl.push(1);
                    }
                    non_null.push(other);
                }
            }
        } else {
            let v = match cell {
                Val::OptSome(inner) => inner.as_ref(),
                Val::OptNone => {
                    return Err(format!(
                        "unexpected null value in required Parquet column `{}`",
                        col.name
                    ));
                }
                other => other,
            };
            non_null.push(v);
        }
    }

    let mut out = Vec::new();
    match inner_ty {
        ScalarTy::Bool => {
            let mut cur_byte = 0u8;
            let mut bit = 0u8;
            for v in non_null {
                let Val::Bool(b) = v else {
                    return Err(format!("expected Bool in column `{}`", col.name));
                };
                if *b {
                    cur_byte |= 1u8 << bit;
                }
                bit += 1;
                if bit == 8 {
                    out.push(cur_byte);
                    cur_byte = 0;
                    bit = 0;
                }
            }
            if bit > 0 {
                out.push(cur_byte);
            }
        }
        ScalarTy::Int => {
            for v in non_null {
                let Val::Int(n) = v else {
                    return Err(format!("expected Int in column `{}`", col.name));
                };
                let i = n
                    .to_i64()
                    .ok_or_else(|| format!("Int out of i64 range in column `{}`", col.name))?;
                out.extend_from_slice(&i.to_le_bytes());
            }
        }
        ScalarTy::Float => {
            for v in non_null {
                let Val::Float(f) = v else {
                    return Err(format!("expected Float in column `{}`", col.name));
                };
                out.extend_from_slice(&f.to_f64().to_le_bytes());
            }
        }
        ScalarTy::Decimal => {
            for v in non_null {
                let Val::Decimal(d) = v else {
                    return Err(format!("expected Decimal in column `{}`", col.name));
                };
                let scaled = d
                    .to_i128()
                    .ok_or_else(|| format!("Decimal out of i128 range in column `{}`", col.name))?;
                out.extend_from_slice(&scaled.to_be_bytes());
            }
        }
        ScalarTy::Text => {
            for v in non_null {
                let Val::Text(s) = v else {
                    return Err(format!("expected Text in column `{}`", col.name));
                };
                let len = u32::try_from(s.len())
                    .map_err(|_| format!("Text value exceeds u32 in column `{}`", col.name))?;
                out.extend_from_slice(&len.to_le_bytes());
                out.extend_from_slice(s.as_bytes());
            }
        }
        ScalarTy::Bytes => {
            for v in non_null {
                let Val::Bytes(bs) = v else {
                    return Err(format!("expected Bytes in column `{}`", col.name));
                };
                let len = u32::try_from(bs.len())
                    .map_err(|_| format!("Bytes value exceeds u32 in column `{}`", col.name))?;
                out.extend_from_slice(&len.to_le_bytes());
                out.extend_from_slice(bs);
            }
        }
        ScalarTy::Date => {
            for v in non_null {
                let Val::Date(d) = v else {
                    return Err(format!("expected Date in column `{}`", col.name));
                };
                let days = d
                    .to_i64()
                    .and_then(|x| i32::try_from(x).ok())
                    .ok_or_else(|| format!("Date out of i32 range in column `{}`", col.name))?;
                out.extend_from_slice(&days.to_le_bytes());
            }
        }
        ScalarTy::Timestamp => {
            for v in non_null {
                let Val::Timestamp(ts) = v else {
                    return Err(format!("expected Timestamp in column `{}`", col.name));
                };
                let us = ts.to_i64().ok_or_else(|| {
                    format!("Timestamp out of i64 range in column `{}`", col.name)
                })?;
                out.extend_from_slice(&us.to_le_bytes());
            }
        }
        ScalarTy::Duration => {
            for v in non_null {
                let Val::Duration(dur) = v else {
                    return Err(format!("expected Duration in column `{}`", col.name));
                };
                let us = dur
                    .to_i64()
                    .ok_or_else(|| format!("Duration out of i64 range in column `{}`", col.name))?;
                out.extend_from_slice(&us.to_le_bytes());
            }
        }
        other => {
            return Err(format!(
                "unsupported Parquet column type `{other:?}` for column `{}`",
                col.name
            ));
        }
    }

    Ok((out, def_levels))
}

fn peel_option(ty: &ScalarTy) -> (&ScalarTy, bool) {
    match ty {
        ScalarTy::Option(inner) => (inner.as_ref(), true),
        other => (other, false),
    }
}

fn schema_element_for_col(col: &ColSpec) -> Result<SchemaElement, String> {
    let (inner, is_opt) = peel_option(&col.ty);
    let rep = Some(if is_opt { REP_OPTIONAL } else { REP_REQUIRED });
    let mut se = SchemaElement {
        phys_type: None,
        type_length: None,
        repetition_type: rep,
        name: col.name.clone(),
        num_children: None,
        converted_type: None,
        scale: None,
        precision: None,
        logical_type: None,
    };
    match inner {
        ScalarTy::Bool => se.phys_type = Some(PT_BOOLEAN),
        ScalarTy::Int => se.phys_type = Some(PT_INT64),
        ScalarTy::Float => se.phys_type = Some(PT_DOUBLE),
        ScalarTy::Decimal => {
            se.phys_type = Some(PT_FIXED_LEN_BYTE_ARRAY);
            se.type_length = Some(16);
            se.converted_type = Some(CONV_DECIMAL);
            se.scale = Some(18);
            se.precision = Some(38);
            se.logical_type = Some(LogicalType::Decimal {
                scale: 18,
                precision: 38,
            });
        }
        ScalarTy::Text => {
            se.phys_type = Some(PT_BYTE_ARRAY);
            se.converted_type = Some(CONV_UTF8);
            se.logical_type = Some(LogicalType::String);
        }
        ScalarTy::Bytes => {
            se.phys_type = Some(PT_BYTE_ARRAY);
        }
        ScalarTy::Date => {
            se.phys_type = Some(PT_INT32);
            se.converted_type = Some(CONV_DATE);
            se.logical_type = Some(LogicalType::Date);
        }
        ScalarTy::Timestamp => {
            se.phys_type = Some(PT_INT64);
            se.converted_type = Some(CONV_TIMESTAMP_MICROS);
            se.logical_type = Some(LogicalType::Timestamp {
                is_adjusted_to_utc: true,
                unit: TimeUnit::Micros,
            });
        }
        ScalarTy::Duration => {
            se.phys_type = Some(PT_INT64);
        }
        other => {
            return Err(format!(
                "unsupported Dana scalar type `{other:?}` for Parquet column `{}`",
                col.name
            ));
        }
    }
    Ok(se)
}

// ---------------------------------------------------------------------------
// Schema Verification & Parquet -> Dana Value Conversion
// ---------------------------------------------------------------------------

fn parquet_decimal_scale(se: &SchemaElement) -> Option<i32> {
    if let Some(LogicalType::Decimal { scale, .. }) = se.logical_type {
        return Some(scale);
    }
    if se.converted_type == Some(CONV_DECIMAL) {
        return Some(se.scale.unwrap_or(0));
    }
    None
}

fn parquet_timestamp_unit(se: &SchemaElement) -> Option<TimeUnit> {
    if let Some(LogicalType::Timestamp { unit, .. }) = se.logical_type {
        return Some(unit);
    }
    match se.converted_type {
        Some(CONV_TIMESTAMP_MILLIS) => Some(TimeUnit::Millis),
        Some(CONV_TIMESTAMP_MICROS) => Some(TimeUnit::Micros),
        _ => None,
    }
}

fn is_parquet_date(se: &SchemaElement) -> bool {
    matches!(se.logical_type, Some(LogicalType::Date)) || se.converted_type == Some(CONV_DATE)
}

fn verify_parquet_col_compat(col: &ColSpec, se: &SchemaElement) -> Result<(), String> {
    if se.repetition_type == Some(REP_REPEATED) {
        return Err(format!(
            "Parquet column `{}` has unsupported REPEATED repetition",
            col.name
        ));
    }
    let Some(pt) = se.phys_type else {
        return Err(format!(
            "Parquet column `{}` is a nested group, expected scalar column",
            col.name
        ));
    };
    let (inner, _) = peel_option(&col.ty);
    let ok = match inner {
        ScalarTy::Bool => pt == PT_BOOLEAN,
        ScalarTy::Int => {
            matches!(pt, PT_INT64 | PT_INT32)
                && parquet_decimal_scale(se).is_none()
                && !is_parquet_date(se)
                && parquet_timestamp_unit(se).is_none()
        }
        ScalarTy::Float => matches!(pt, PT_DOUBLE | PT_FLOAT),
        ScalarTy::Decimal => {
            matches!(
                pt,
                PT_INT32 | PT_INT64 | PT_BYTE_ARRAY | PT_FIXED_LEN_BYTE_ARRAY
            ) && parquet_decimal_scale(se).is_some()
        }
        ScalarTy::Text => pt == PT_BYTE_ARRAY && parquet_decimal_scale(se).is_none(),
        ScalarTy::Bytes => matches!(pt, PT_BYTE_ARRAY | PT_FIXED_LEN_BYTE_ARRAY),
        ScalarTy::Date => pt == PT_INT32 && is_parquet_date(se),
        ScalarTy::Timestamp => pt == PT_INT64 && parquet_timestamp_unit(se).is_some(),
        ScalarTy::Duration => {
            pt == PT_INT64
                && parquet_decimal_scale(se).is_none()
                && parquet_timestamp_unit(se).is_none()
        }
        _ => false,
    };
    if !ok {
        return Err(format!(
            "Parquet schema drift on column `{}`: expected `{:?}`, found physical type {pt} (converted={:?}, logical={:?})",
            col.name, col.ty, se.converted_type, se.logical_type
        ));
    }
    Ok(())
}

fn decode_be_twos_complement_bigint(bytes: &[u8]) -> Result<BigInt, String> {
    if bytes.is_empty() {
        return Err("empty big-endian two's-complement decimal bytes".to_string());
    }
    if bytes.len() <= 16 {
        let sign_fill = if (bytes[0] & 0x80) != 0 { 0xFF } else { 0x00 };
        let mut buf = [sign_fill; 16];
        buf[16 - bytes.len()..].copy_from_slice(bytes);
        return Ok(BigInt::from(i128::from_be_bytes(buf)));
    }
    // Arbitrary-width big-endian two's complement
    let neg = (bytes[0] & 0x80) != 0;
    let mag_bytes: Vec<u8> = if neg {
        // Two's complement negate: invert bits and add 1
        let mut inv: Vec<u8> = bytes.iter().map(|&b| !b).collect();
        let mut carry = 1u16;
        for b in inv.iter_mut().rev() {
            let sum = u16::from(*b) + carry;
            *b = (sum & 0xFF) as u8;
            carry = sum >> 8;
        }
        inv
    } else {
        bytes.to_vec()
    };
    let mut acc = BigInt::ZERO;
    let base = BigInt::from(256i64);
    for b in mag_bytes {
        acc = &(&acc * &base) + &BigInt::from(i64::from(b));
    }
    Ok(if neg { -acc } else { acc })
}

fn pow10_bigint(exp: u32) -> BigInt {
    let mut acc = BigInt::one();
    let ten = BigInt::from(10i64);
    for _ in 0..exp {
        acc = &acc * &ten;
    }
    acc
}

fn rescale_decimal_to_dana(raw: BigInt, src_scale: i32) -> Result<BigInt, String> {
    if !(0..=76).contains(&src_scale) {
        return Err(format!("unsupported Parquet decimal scale {src_scale}"));
    }
    let scaled = if src_scale == 18 {
        raw
    } else if src_scale < 18 {
        let mult = pow10_bigint((18 - src_scale) as u32);
        &raw * &mult
    } else {
        let div = pow10_bigint((src_scale - 18) as u32);
        let Some((q, r)) = raw.div_rem_euclid(&div) else {
            return Err("Parquet decimal rescaling division error".to_string());
        };
        if !r.is_zero() {
            return Err(format!(
                "Parquet decimal with scale {src_scale} has non-zero precision beyond 18 fractional digits"
            ));
        }
        q
    };
    if scaled < BigInt::from(DEC_MIN) || scaled > BigInt::from(DEC_MAX) {
        return Err("Parquet decimal value overflows Dana fixed-point Decimal range".to_string());
    }
    Ok(scaled)
}

fn raw_parquet_to_dana(
    raw: &RawParquetVal,
    col: &ColSpec,
    se: &SchemaElement,
) -> Result<Val, String> {
    let (inner, _) = peel_option(&col.ty);
    match (inner, raw) {
        (ScalarTy::Bool, RawParquetVal::Bool(b)) => Ok(Val::Bool(*b)),
        (ScalarTy::Int, RawParquetVal::Int64(n)) => Ok(Val::Int(BigInt::from(*n))),
        (ScalarTy::Int, RawParquetVal::Int32(n)) => Ok(Val::Int(BigInt::from(i64::from(*n)))),
        (ScalarTy::Float, RawParquetVal::Double(f)) => Ok(Val::Float(Float64::from_f64(*f))),
        (ScalarTy::Float, RawParquetVal::Float(f)) => {
            Ok(Val::Float(Float64::from_f64(f64::from(*f))))
        }
        (ScalarTy::Decimal, raw_v) => {
            let src_scale = parquet_decimal_scale(se).ok_or_else(|| {
                format!(
                    "Parquet column `{}` missing DECIMAL scale metadata",
                    col.name
                )
            })?;
            let unscaled = match raw_v {
                RawParquetVal::Int32(n) => BigInt::from(i64::from(*n)),
                RawParquetVal::Int64(n) => BigInt::from(*n),
                RawParquetVal::Bytes(bs) => decode_be_twos_complement_bigint(bs)?,
                _ => {
                    return Err(format!(
                        "unexpected Parquet physical representation for Decimal column `{}`",
                        col.name
                    ));
                }
            };
            let scaled = rescale_decimal_to_dana(unscaled, src_scale)?;
            Ok(Val::Decimal(scaled))
        }
        (ScalarTy::Text, RawParquetVal::Bytes(bs)) => {
            let s = std::str::from_utf8(bs)
                .map_err(|e| format!("invalid UTF-8 in Parquet Text column `{}`: {e}", col.name))?;
            Ok(Val::Text(s.to_string()))
        }
        (ScalarTy::Bytes, RawParquetVal::Bytes(bs)) => Ok(Val::Bytes(bs.clone())),
        (ScalarTy::Date, RawParquetVal::Int32(days)) => {
            Ok(Val::Date(BigInt::from(i64::from(*days))))
        }
        (ScalarTy::Timestamp, RawParquetVal::Int64(v)) => {
            let unit = parquet_timestamp_unit(se).ok_or_else(|| {
                format!(
                    "Parquet column `{}` missing TIMESTAMP unit metadata",
                    col.name
                )
            })?;
            let micros = match unit {
                TimeUnit::Millis => v
                    .checked_mul(1_000)
                    .ok_or_else(|| "Parquet TIMESTAMP_MILLIS overflow".to_string())?,
                TimeUnit::Micros => *v,
                TimeUnit::Nanos => v.div_euclid(1_000),
            };
            Ok(Val::Timestamp(BigInt::from(micros)))
        }
        (ScalarTy::Duration, RawParquetVal::Int64(us)) => Ok(Val::Duration(BigInt::from(*us))),
        _ => Err(format!(
            "Parquet value type mismatch for column `{}`",
            col.name
        )),
    }
}

// ---------------------------------------------------------------------------
// Public Parquet Writer API
// ---------------------------------------------------------------------------

/// Encode a [`TableVal`] into Apache Parquet binary bytes using default options (`Zstd`, 65,536-row groups).
///
/// # Errors
/// Returns an error string on unsupported column types, out-of-range values, or compression errors.
pub fn write_parquet_bytes(
    tv: &TableVal,
    compression: ParquetCompression,
) -> Result<Vec<u8>, String> {
    write_parquet_bytes_with_options(
        tv,
        ParquetWriteOptions {
            compression,
            row_group_rows: DEFAULT_ROW_GROUP_ROWS,
        },
    )
}

fn infer_col_scalar_ty(rows: &[TableRow], col_idx: usize) -> ScalarTy {
    let mut saw_none = false;
    let mut saw_some = false;
    let mut inner: Option<ScalarTy> = None;
    for row in rows {
        let Some(cell) = row.cells.get(col_idx) else {
            continue;
        };
        match cell {
            Val::OptNone => saw_none = true,
            Val::OptSome(v) => {
                saw_some = true;
                if inner.is_none() {
                    inner = scalar_ty_from_val(v);
                }
            }
            other => {
                if inner.is_none() {
                    inner = scalar_ty_from_val(other);
                }
            }
        }
    }
    let base = inner.unwrap_or(ScalarTy::Text);
    if saw_none || saw_some {
        ScalarTy::Option(Box::new(base))
    } else {
        base
    }
}

fn scalar_ty_from_val(v: &Val) -> Option<ScalarTy> {
    match v {
        Val::Bool(_) => Some(ScalarTy::Bool),
        Val::Int(_) => Some(ScalarTy::Int),
        Val::Decimal(_) => Some(ScalarTy::Decimal),
        Val::Float(_) => Some(ScalarTy::Float),
        Val::Text(_) => Some(ScalarTy::Text),
        Val::Bytes(_) => Some(ScalarTy::Bytes),
        Val::Date(_) => Some(ScalarTy::Date),
        Val::Timestamp(_) => Some(ScalarTy::Timestamp),
        Val::Duration(_) => Some(ScalarTy::Duration),
        Val::OptSome(inner) => scalar_ty_from_val(inner),
        _ => None,
    }
}

/// Encode a [`TableVal`] into Apache Parquet binary bytes with explicit [`ParquetWriteOptions`].
///
/// # Errors
/// Returns an error string on invalid options, unsupported column types, or compression errors.
pub fn write_parquet_bytes_with_options(
    tv: &TableVal,
    opts: ParquetWriteOptions,
) -> Result<Vec<u8>, String> {
    if opts.row_group_rows == 0 {
        return Err("Parquet row_group_rows must be positive".to_string());
    }

    let resolved_cols: Vec<ColSpec> = tv
        .cols
        .iter()
        .enumerate()
        .map(|(ci, c)| {
            if c.ty == ScalarTy::Unit {
                let mut cloned = c.clone();
                cloned.ty = infer_col_scalar_ty(&tv.rows, ci);
                cloned
            } else {
                c.clone()
            }
        })
        .collect();

    let mut schema_elems = Vec::with_capacity(1 + resolved_cols.len());
    schema_elems.push(SchemaElement {
        phys_type: None,
        type_length: None,
        repetition_type: None,
        name: "dana_schema".to_string(),
        num_children: Some(
            i32::try_from(resolved_cols.len())
                .map_err(|_| "Parquet column count overflow".to_string())?,
        ),
        converted_type: None,
        scale: None,
        precision: None,
        logical_type: None,
    });
    for col in &resolved_cols {
        schema_elems.push(schema_element_for_col(col)?);
    }

    let mut out = Vec::new();
    out.extend_from_slice(PARQUET_MAGIC);

    let mut row_groups = Vec::new();
    for chunk_rows in tv.rows.chunks(opts.row_group_rows) {
        let rg_num_rows = chunk_rows.len();
        let rg_num_rows_i32 = i32::try_from(rg_num_rows)
            .map_err(|_| "Parquet row group size exceeds i32".to_string())?;
        let mut columns = Vec::with_capacity(resolved_cols.len());
        let mut rg_uncompressed_total = 0i64;

        for (ci, col) in resolved_cols.iter().enumerate() {
            let se = &schema_elems[ci + 1];
            let phys_type = se
                .phys_type
                .ok_or_else(|| "missing physical type for Parquet leaf".to_string())?;
            let (plain_bytes, def_levels_opt) = encode_plain_column(col, chunk_rows, ci)?;

            let mut uncompressed_page = Vec::new();
            let mut encodings = Vec::new();
            if let Some(def_levels) = def_levels_opt {
                let rle = encode_rle_hybrid(&def_levels, 1);
                let rle_len = u32::try_from(rle.len())
                    .map_err(|_| "Parquet definition levels exceed u32".to_string())?;
                uncompressed_page.extend_from_slice(&rle_len.to_le_bytes());
                uncompressed_page.extend_from_slice(&rle);
                encodings.push(ENC_RLE);
            }
            uncompressed_page.extend_from_slice(&plain_bytes);
            encodings.push(ENC_PLAIN);

            let compressed_page = compress_page_bytes(&uncompressed_page, opts.compression)?;
            let uncomp_sz = i32::try_from(uncompressed_page.len())
                .map_err(|_| "Parquet uncompressed page exceeds i32".to_string())?;
            let comp_sz = i32::try_from(compressed_page.len())
                .map_err(|_| "Parquet compressed page exceeds i32".to_string())?;

            let page_hdr = PageHeader {
                page_type: PAGE_DATA_V1,
                uncompressed_page_size: uncomp_sz,
                compressed_page_size: comp_sz,
                data_page_header: Some(DataPageHeader {
                    num_values: rg_num_rows_i32,
                    encoding: ENC_PLAIN,
                    definition_level_encoding: ENC_RLE,
                    repetition_level_encoding: ENC_RLE,
                }),
                dictionary_page_header: None,
                data_page_header_v2: None,
            };
            let mut hdr_w = ThriftWriter::new();
            write_page_header(&mut hdr_w, &page_hdr);
            let hdr_bytes = hdr_w.into_bytes();

            let data_page_offset = i64::try_from(out.len())
                .map_err(|_| "Parquet file offset exceeds i64".to_string())?;
            out.extend_from_slice(&hdr_bytes);
            out.extend_from_slice(&compressed_page);

            let total_uncomp = i64::try_from(hdr_bytes.len() + uncompressed_page.len())
                .map_err(|_| "Parquet total_uncompressed_size overflow".to_string())?;
            let total_comp = i64::try_from(hdr_bytes.len() + compressed_page.len())
                .map_err(|_| "Parquet total_compressed_size overflow".to_string())?;
            rg_uncompressed_total = rg_uncompressed_total
                .checked_add(total_uncomp)
                .ok_or_else(|| "Parquet row group size overflow".to_string())?;

            columns.push(ColumnChunk {
                file_offset: data_page_offset,
                meta_data: Some(ColumnMetaData {
                    phys_type,
                    encodings,
                    path_in_schema: vec![col.name.clone()],
                    codec: opts.compression.to_thrift_codec(),
                    num_values: rg_num_rows as i64,
                    total_uncompressed_size: total_uncomp,
                    total_compressed_size: total_comp,
                    data_page_offset,
                    dictionary_page_offset: None,
                }),
            });
        }

        row_groups.push(RowGroup {
            columns,
            total_byte_size: rg_uncompressed_total,
            num_rows: rg_num_rows as i64,
        });
    }

    let file_meta = FileMetaData {
        version: 1,
        schema: schema_elems,
        num_rows: tv.rows.len() as i64,
        row_groups,
        created_by: Some("dana native parquet writer 0.2".to_string()),
    };
    let mut fm_w = ThriftWriter::new();
    write_file_metadata(&mut fm_w, &file_meta);
    let fm_bytes = fm_w.into_bytes();
    let fm_len = u32::try_from(fm_bytes.len())
        .map_err(|_| "Parquet footer metadata exceeds u32".to_string())?;

    out.extend_from_slice(&fm_bytes);
    out.extend_from_slice(&fm_len.to_le_bytes());
    out.extend_from_slice(PARQUET_MAGIC);

    Ok(out)
}

/// Write a [`TableVal`] to an Apache Parquet file on disk using the specified compression codec.
///
/// # Errors
/// Returns an error string on encoding or filesystem write errors.
pub fn write_parquet_table(
    path: &Path,
    tv: &TableVal,
    compression: ParquetCompression,
) -> Result<(), String> {
    let bytes = write_parquet_bytes(tv, compression)?;
    fs::write(path, bytes).map_err(|e| format!("{}: {e}", path.display()))
}

// ---------------------------------------------------------------------------
// Public Parquet Reader API
// ---------------------------------------------------------------------------

/// Read an Apache Parquet file from raw bytes, verifying schema column names, physical/logical
/// types, nullability, and per-column `where` constraints via `check_constraint`.
///
/// Supports `PLAIN` and `RLE_DICTIONARY`/`PLAIN_DICTIONARY` encodings, `DataPage` v1 & v2,
/// and `UNCOMPRESSED`, `SNAPPY`, `GZIP`, and `ZSTD` codecs.
///
/// # Errors
/// Returns an error string on invalid magic bytes, corrupted Thrift metadata, unsupported
/// encoding/codec, schema/nullability drift, or `where` constraint failure.
pub fn read_parquet_bytes_with_schema<F>(
    bytes: &[u8],
    schema: &TableTy,
    mut check_constraint: F,
) -> Result<TableVal, String>
where
    F: FnMut(usize, &Val) -> bool,
{
    if bytes.len() < 12 {
        return Err("Parquet file too short (minimum 12 bytes)".to_string());
    }
    if &bytes[..4] != PARQUET_MAGIC || &bytes[bytes.len() - 4..] != PARQUET_MAGIC {
        return Err("invalid Parquet header/footer magic (expected `PAR1`)".to_string());
    }
    let footer_len_slice: [u8; 4] = bytes[bytes.len() - 8..bytes.len() - 4]
        .try_into()
        .map_err(|_| "failed to read Parquet footer length".to_string())?;
    let footer_len = u32::from_le_bytes(footer_len_slice) as usize;
    if footer_len > MAX_PARQUET_FOOTER_BYTES || footer_len + 12 > bytes.len() {
        return Err(format!("invalid Parquet footer length ({footer_len})"));
    }
    let footer_start = bytes.len() - 8 - footer_len;
    let footer_bytes = &bytes[footer_start..bytes.len() - 8];

    let mut fm_reader = ThriftReader::new(footer_bytes);
    let fm = read_file_metadata(&mut fm_reader)?;
    if fm.schema.is_empty() {
        return Err("Parquet file has empty schema".to_string());
    }

    // Collect top-level leaf columns from `fm.schema[1..]`
    let mut leaf_by_name: HashMap<String, (usize, &SchemaElement)> = HashMap::new();
    let mut leaf_idx = 0usize;
    for se in fm.schema.iter().skip(1) {
        if se.phys_type.is_some() {
            leaf_by_name
                .entry(se.name.clone())
                .or_insert((leaf_idx, se));
            leaf_idx += 1;
        }
    }

    let mut mapped_cols: Vec<(usize, &SchemaElement)> = Vec::with_capacity(schema.cols.len());
    for col in &schema.cols {
        let Some(&(pq_col_idx, se)) = leaf_by_name.get(col.name.as_str()) else {
            return Err(format!(
                "Parquet schema drift: missing required column `{}`",
                col.name
            ));
        };
        verify_parquet_col_compat(col, se)?;
        mapped_cols.push((pq_col_idx, se));
    }

    let total_rows = usize::try_from(fm.num_rows)
        .map_err(|_| "Parquet file has negative num_rows".to_string())?;
    let mut rows: Vec<TableRow> = Vec::with_capacity(total_rows.min(65_536));

    for rg in &fm.row_groups {
        let rg_rows = usize::try_from(rg.num_rows)
            .map_err(|_| "Parquet row group has negative num_rows".to_string())?;
        if rg_rows == 0 {
            continue;
        }
        if rg_rows > MAX_PARQUET_PAGE_VALUES {
            return Err(format!(
                "Parquet row group num_rows ({rg_rows}) exceeds limit ({MAX_PARQUET_PAGE_VALUES})"
            ));
        }

        let mut col_data: Vec<Vec<Val>> = Vec::with_capacity(schema.cols.len());
        for (ci, col) in schema.cols.iter().enumerate() {
            let (pq_idx, se) = mapped_cols[ci];
            // Find matching column chunk by path_in_schema or positional index
            let chunk = rg
                .columns
                .iter()
                .find(|c| {
                    c.meta_data.as_ref().is_some_and(|m| {
                        m.path_in_schema.len() == 1 && m.path_in_schema[0] == col.name
                    })
                })
                .or_else(|| rg.columns.get(pq_idx))
                .ok_or_else(|| {
                    format!("Parquet row group missing column chunk for `{}`", col.name)
                })?;
            let meta = chunk.meta_data.as_ref().ok_or_else(|| {
                format!(
                    "Parquet column chunk for `{}` is missing inline metadata",
                    col.name
                )
            })?;
            let vals = decode_column_chunk(bytes, footer_start, meta, col, se, rg_rows)?;
            col_data.push(vals);
        }

        let mut col_iters: Vec<std::vec::IntoIter<Val>> =
            col_data.into_iter().map(Vec::into_iter).collect();
        for _ in 0..rg_rows {
            let global_row_idx = rows.len();
            let mut cells = Vec::with_capacity(schema.cols.len());
            for (ci, col) in schema.cols.iter().enumerate() {
                let val = col_iters[ci].next().unwrap_or(Val::Unit);
                let constraint_ok = match &val {
                    Val::OptNone => true,
                    Val::OptSome(inner) => check_constraint(ci, inner),
                    other => check_constraint(ci, other),
                };
                if !constraint_ok {
                    return Err(format!(
                        "Parquet row {} column `{}` failed schema `where` constraint",
                        global_row_idx + 1,
                        col.name
                    ));
                }
                cells.push(val);
            }
            rows.push(TableRow {
                cells,
                group_meta: None,
            });
        }
    }

    Ok(TableVal {
        cols: schema.cols.clone(),
        rows,
    })
}

/// Read an Apache Parquet file from disk with schema & constraint validation.
///
/// # Errors
/// Returns an error string on filesystem read, Parquet decode, schema drift, or constraint errors.
pub fn read_parquet_file_with_schema<F>(
    path: &Path,
    schema: &TableTy,
    check_constraint: F,
) -> Result<TableVal, String>
where
    F: FnMut(usize, &Val) -> bool,
{
    let bytes = fs::read(path).map_err(|e| format!("{}: {e}", path.display()))?;
    read_parquet_bytes_with_schema(&bytes, schema, check_constraint)
}

fn infer_parquet_inferred_ty(se: &SchemaElement) -> Result<InferredTy, String> {
    if se.repetition_type == Some(REP_REPEATED) {
        return Err(format!(
            "Parquet column `{}` has unsupported REPEATED repetition",
            se.name
        ));
    }
    let Some(pt) = se.phys_type else {
        return Err(format!(
            "Parquet column `{}` is a nested group, expected scalar column",
            se.name
        ));
    };
    if parquet_decimal_scale(se).is_some() {
        return Ok(InferredTy::Decimal);
    }
    match pt {
        PT_BOOLEAN => Ok(InferredTy::Bool),
        PT_INT32 => {
            if is_parquet_date(se) {
                Ok(InferredTy::Date)
            } else {
                Ok(InferredTy::Int)
            }
        }
        PT_INT64 => {
            if parquet_timestamp_unit(se).is_some() {
                Ok(InferredTy::Timestamp)
            } else {
                Ok(InferredTy::Int)
            }
        }
        PT_FLOAT | PT_DOUBLE => Ok(InferredTy::Float),
        PT_BYTE_ARRAY => {
            if se.converted_type == Some(CONV_UTF8)
                || matches!(se.logical_type, Some(LogicalType::String))
            {
                Ok(InferredTy::Text)
            } else {
                Ok(InferredTy::Bytes)
            }
        }
        PT_FIXED_LEN_BYTE_ARRAY => Ok(InferredTy::Bytes),
        other => Err(format!(
            "unsupported Parquet physical type {other} for column `{}`",
            se.name
        )),
    }
}

fn read_parquet_footer(bytes: &[u8]) -> Result<FileMetaData, String> {
    if bytes.len() < 12 {
        return Err("Parquet file too short (minimum 12 bytes)".to_string());
    }
    if &bytes[..4] != PARQUET_MAGIC || &bytes[bytes.len() - 4..] != PARQUET_MAGIC {
        return Err("invalid Parquet header/footer magic (expected `PAR1`)".to_string());
    }
    let footer_len_slice: [u8; 4] = bytes[bytes.len() - 8..bytes.len() - 4]
        .try_into()
        .map_err(|_| "failed to read Parquet footer length".to_string())?;
    let footer_len = u32::from_le_bytes(footer_len_slice) as usize;
    if footer_len > MAX_PARQUET_FOOTER_BYTES || footer_len + 12 > bytes.len() {
        return Err(format!("invalid Parquet footer length ({footer_len})"));
    }
    let footer_start = bytes.len() - 8 - footer_len;
    let footer_bytes = &bytes[footer_start..bytes.len() - 8];
    let mut fm_reader = ThriftReader::new(footer_bytes);
    read_file_metadata(&mut fm_reader)
}

/// Infer a Dana [`InferredSchema`] directly from Parquet `FileMetaData` footer bytes.
///
/// # Errors
/// Returns an error string on malformed Parquet headers/footers or unsupported column types.
pub fn infer_parquet_schema_from_bytes(
    bytes: &[u8],
    schema_name: &str,
) -> Result<InferredSchema, String> {
    let fm = read_parquet_footer(bytes)?;
    if fm.schema.is_empty() {
        return Err("Parquet file has empty schema".to_string());
    }
    let rows_sampled = usize::try_from(fm.num_rows).unwrap_or(0);
    let mut seen_names = HashSet::new();
    let mut cols = Vec::new();
    for se in fm.schema.iter().skip(1) {
        if se.phys_type.is_none() {
            continue;
        }
        let ty = infer_parquet_inferred_ty(se)?;
        let nullable = se.repetition_type == Some(REP_OPTIONAL);
        let mut name = sanitize_col_name(&se.name, cols.len());
        while !seen_names.insert(name.clone()) {
            name.push('_');
        }
        cols.push(InferredColumn {
            pii_hint: looks_like_pii_column(&name),
            name,
            ty,
            nullable,
            non_null_count: rows_sampled,
        });
    }
    if cols.is_empty() {
        return Err("Parquet file contains no scalar columns".to_string());
    }
    Ok(InferredSchema {
        name: schema_name.to_string(),
        rows_sampled,
        cols,
    })
}

/// Infer a Dana [`InferredSchema`] from a Parquet file on disk.
///
/// # Errors
/// Returns an error string on I/O or Parquet metadata decode errors.
pub fn infer_parquet_schema_from_file(
    path: &Path,
    schema_name: &str,
) -> Result<InferredSchema, String> {
    let bytes = fs::read(path).map_err(|e| format!("{}: {e}", path.display()))?;
    infer_parquet_schema_from_bytes(&bytes, schema_name)
}

/// Read an Apache Parquet file without a pre-declared schema (used by REPL `untyped.read_parquet`).
///
/// Uses the exact Parquet `FileMetaData` column names to decode every column, then exposes
/// Dana-sanitized column identifiers on the returned [`InferredSchema`] and [`TableVal`].
///
/// # Errors
/// Returns an error string on I/O, Parquet decode, or unsupported column type errors.
pub fn read_parquet_file_untyped(
    path: &Path,
    schema_name: &str,
) -> Result<(InferredSchema, TableVal), String> {
    let bytes = fs::read(path).map_err(|e| format!("{}: {e}", path.display()))?;
    let fm = read_parquet_footer(&bytes)?;
    if fm.schema.is_empty() {
        return Err("Parquet file has empty schema".to_string());
    }
    let rows_sampled = usize::try_from(fm.num_rows).unwrap_or(0);
    let mut seen_names = HashSet::new();
    let mut inferred_cols = Vec::new();
    let mut raw_cols = Vec::new();
    for se in fm.schema.iter().skip(1) {
        if se.phys_type.is_none() {
            continue;
        }
        let ty = infer_parquet_inferred_ty(se)?;
        let nullable = se.repetition_type == Some(REP_OPTIONAL);
        let mut dana_name = sanitize_col_name(&se.name, inferred_cols.len());
        while !seen_names.insert(dana_name.clone()) {
            dana_name.push('_');
        }
        raw_cols.push(ColSpec {
            name: se.name.clone(),
            ty: ty.to_scalar_ty(nullable),
            tags: TagSet::empty(),
            bucketed: false,
            agg_kind: AggKind::Raw,
        });
        inferred_cols.push(InferredColumn {
            pii_hint: looks_like_pii_column(&dana_name),
            name: dana_name,
            ty,
            nullable,
            non_null_count: rows_sampled,
        });
    }
    if raw_cols.is_empty() {
        return Err("Parquet file contains no scalar columns".to_string());
    }
    let raw_schema = TableTy {
        cols: raw_cols,
        ..TableTy::default()
    };
    let mut tv = read_parquet_bytes_with_schema(&bytes, &raw_schema, |_, _| true)?;
    let inferred = InferredSchema {
        name: schema_name.to_string(),
        rows_sampled: tv.rows.len(),
        cols: inferred_cols,
    };
    for (col_spec, inf_col) in tv.cols.iter_mut().zip(&inferred.cols) {
        col_spec.name.clone_from(&inf_col.name);
    }
    Ok((inferred, tv))
}

fn decode_column_chunk(
    file_bytes: &[u8],
    footer_start: usize,
    meta: &ColumnMetaData,
    col: &ColSpec,
    se: &SchemaElement,
    expected_rows: usize,
) -> Result<Vec<Val>, String> {
    let start_i64 = match meta.dictionary_page_offset {
        Some(doff) if doff > 0 && doff < meta.data_page_offset => doff,
        _ => meta.data_page_offset,
    };
    let start = usize::try_from(start_i64)
        .map_err(|_| format!("negative Parquet page offset for column `{}`", col.name))?;
    let comp_len = usize::try_from(meta.total_compressed_size)
        .map_err(|_| format!("negative Parquet compressed size for column `{}`", col.name))?;
    let end = start
        .checked_add(comp_len)
        .ok_or_else(|| "Parquet column chunk bounds overflow".to_string())?;
    if end > footer_start || end > file_bytes.len() {
        return Err(format!(
            "Parquet column chunk for `{}` extends past file data region",
            col.name
        ));
    }

    let is_pq_optional = se.repetition_type == Some(REP_OPTIONAL);
    let is_dana_optional = col.ty.is_option();
    let max_def_level: u32 = u32::from(is_pq_optional);

    let mut cursor = start;
    let mut dictionary: Option<Vec<RawParquetVal>> = None;
    let mut out_vals: Vec<Val> = Vec::with_capacity(expected_rows.min(65_536));

    while out_vals.len() < expected_rows && cursor < end {
        let mut hdr_reader = ThriftReader::new(&file_bytes[cursor..end]);
        let ph = read_page_header(&mut hdr_reader)?;
        let hdr_len = hdr_reader.pos;
        cursor += hdr_len;

        let comp_sz = usize::try_from(ph.compressed_page_size)
            .map_err(|_| "negative Parquet compressed_page_size".to_string())?;
        let uncomp_sz = usize::try_from(ph.uncompressed_page_size)
            .map_err(|_| "negative Parquet uncompressed_page_size".to_string())?;
        let Some(page_end) = cursor.checked_add(comp_sz) else {
            return Err(format!(
                "Parquet page size overflow in column `{}`",
                col.name
            ));
        };
        if page_end > end {
            return Err(format!(
                "truncated Parquet page payload in column `{}`",
                col.name
            ));
        }
        let page_raw = &file_bytes[cursor..page_end];
        cursor = page_end;

        match ph.page_type {
            PAGE_DICTIONARY => {
                let dph = ph
                    .dictionary_page_header
                    .ok_or_else(|| "DICTIONARY_PAGE missing dictionary_page_header".to_string())?;
                if dph.encoding != ENC_PLAIN && dph.encoding != ENC_PLAIN_DICTIONARY {
                    return Err(format!(
                        "unsupported Parquet dictionary encoding {}",
                        dph.encoding
                    ));
                }
                let dict_count = usize::try_from(dph.num_values)
                    .map_err(|_| "negative Parquet dictionary num_values".to_string())?;
                let payload = decompress_page_bytes(page_raw, meta.codec, uncomp_sz)?;
                let (dict_vals, _) =
                    decode_plain_values(&payload, meta.phys_type, se.type_length, dict_count)?;
                dictionary = Some(dict_vals);
            }
            PAGE_DATA_V1 => {
                let dph = ph
                    .data_page_header
                    .ok_or_else(|| "DATA_PAGE missing data_page_header".to_string())?;
                let num_values = usize::try_from(dph.num_values)
                    .map_err(|_| "negative Parquet DataPage num_values".to_string())?;
                let payload = decompress_page_bytes(page_raw, meta.codec, uncomp_sz)?;
                let mut pos = 0usize;

                let def_levels = if max_def_level > 0 {
                    if dph.definition_level_encoding != ENC_RLE {
                        return Err(format!(
                            "unsupported Parquet definition level encoding {}",
                            dph.definition_level_encoding
                        ));
                    }
                    if pos + 4 > payload.len() {
                        return Err("truncated Parquet definition level length".to_string());
                    }
                    let arr: [u8; 4] = payload[pos..pos + 4]
                        .try_into()
                        .map_err(|_| "def level len error".to_string())?;
                    pos += 4;
                    let def_len = u32::from_le_bytes(arr) as usize;
                    if pos + def_len > payload.len() {
                        return Err("truncated Parquet definition level data".to_string());
                    }
                    let levels = decode_rle_hybrid(&payload[pos..pos + def_len], 1, num_values)?;
                    pos += def_len;
                    Some(levels)
                } else {
                    None
                };

                let non_null_count = match &def_levels {
                    Some(dl) => dl.iter().filter(|&&d| d == max_def_level).count(),
                    None => num_values,
                };

                let raw_vals = decode_page_values(
                    &payload[pos..],
                    dph.encoding,
                    meta.phys_type,
                    se.type_length,
                    non_null_count,
                    dictionary.as_deref(),
                )?;
                append_decoded_page_vals(
                    &mut out_vals,
                    def_levels.as_deref(),
                    &raw_vals,
                    max_def_level,
                    is_dana_optional,
                    col,
                    se,
                )?;
            }
            PAGE_DATA_V2 => {
                let v2 = ph
                    .data_page_header_v2
                    .ok_or_else(|| "DATA_PAGE_V2 missing data_page_header_v2".to_string())?;
                let num_values = usize::try_from(v2.num_values)
                    .map_err(|_| "negative Parquet DataPageV2 num_values".to_string())?;
                let rep_len = usize::try_from(v2.repetition_levels_byte_length)
                    .map_err(|_| "negative DataPageV2 rep_len".to_string())?;
                let def_len = usize::try_from(v2.definition_levels_byte_length)
                    .map_err(|_| "negative DataPageV2 def_len".to_string())?;
                let levels_total = rep_len
                    .checked_add(def_len)
                    .ok_or_else(|| "DataPageV2 levels overflow".to_string())?;
                if levels_total > page_raw.len() || levels_total > uncomp_sz {
                    return Err("truncated Parquet DataPageV2 levels".to_string());
                }
                let def_levels = if max_def_level > 0 {
                    let def_slice = &page_raw[rep_len..rep_len + def_len];
                    Some(decode_rle_hybrid(def_slice, 1, num_values)?)
                } else {
                    None
                };
                let non_null_count = match &def_levels {
                    Some(dl) => dl.iter().filter(|&&d| d == max_def_level).count(),
                    None => num_values,
                };
                let data_part = &page_raw[levels_total..];
                let expected_data_uncomp = uncomp_sz - levels_total;
                let data_bytes = if v2.is_compressed {
                    decompress_page_bytes(data_part, meta.codec, expected_data_uncomp)?
                } else {
                    if data_part.len() != expected_data_uncomp {
                        return Err("DataPageV2 uncompressed payload length mismatch".to_string());
                    }
                    data_part.to_vec()
                };
                let raw_vals = decode_page_values(
                    &data_bytes,
                    v2.encoding,
                    meta.phys_type,
                    se.type_length,
                    non_null_count,
                    dictionary.as_deref(),
                )?;
                append_decoded_page_vals(
                    &mut out_vals,
                    def_levels.as_deref(),
                    &raw_vals,
                    max_def_level,
                    is_dana_optional,
                    col,
                    se,
                )?;
            }
            other => {
                // Skip non-data pages such as INDEX_PAGE (1) if present.
                if other != 1 {
                    return Err(format!("unsupported Parquet page type `{other}`"));
                }
            }
        }
    }

    if out_vals.len() != expected_rows {
        return Err(format!(
            "Parquet column `{}` decoded {} values, expected {expected_rows}",
            col.name,
            out_vals.len()
        ));
    }
    Ok(out_vals)
}

fn decode_page_values(
    data: &[u8],
    encoding: i32,
    phys_type: i32,
    type_length: Option<i32>,
    non_null_count: usize,
    dictionary: Option<&[RawParquetVal]>,
) -> Result<Vec<RawParquetVal>, String> {
    if non_null_count == 0 {
        return Ok(Vec::new());
    }
    match encoding {
        ENC_PLAIN => {
            let (vals, _) = decode_plain_values(data, phys_type, type_length, non_null_count)?;
            Ok(vals)
        }
        ENC_RLE_DICTIONARY | ENC_PLAIN_DICTIONARY => {
            let dict = dictionary.ok_or_else(|| {
                "Parquet dictionary-encoded data page encountered before DICTIONARY_PAGE"
                    .to_string()
            })?;
            let &bit_width = data
                .first()
                .ok_or_else(|| "truncated Parquet dictionary bit-width byte".to_string())?;
            let indices = decode_rle_hybrid(&data[1..], bit_width, non_null_count)?;
            let mut vals = Vec::with_capacity(non_null_count.min(65_536));
            for idx in indices {
                let v = dict.get(idx as usize).ok_or_else(|| {
                    format!(
                        "Parquet dictionary index {idx} out of bounds (dict len {})",
                        dict.len()
                    )
                })?;
                vals.push(v.clone());
            }
            Ok(vals)
        }
        other => Err(format!("unsupported Parquet page encoding `{other}`")),
    }
}

fn append_decoded_page_vals(
    out: &mut Vec<Val>,
    def_levels: Option<&[u32]>,
    raw_vals: &[RawParquetVal],
    max_def_level: u32,
    is_dana_optional: bool,
    col: &ColSpec,
    se: &SchemaElement,
) -> Result<(), String> {
    match def_levels {
        None => {
            for rv in raw_vals {
                let dana = raw_parquet_to_dana(rv, col, se)?;
                out.push(if is_dana_optional {
                    Val::OptSome(Box::new(dana))
                } else {
                    dana
                });
            }
        }
        Some(levels) => {
            let mut val_idx = 0usize;
            for &lvl in levels {
                if lvl == max_def_level {
                    let rv = raw_vals
                        .get(val_idx)
                        .ok_or_else(|| "Parquet non-null value underflow".to_string())?;
                    val_idx += 1;
                    let dana = raw_parquet_to_dana(rv, col, se)?;
                    out.push(if is_dana_optional {
                        Val::OptSome(Box::new(dana))
                    } else {
                        dana
                    });
                } else {
                    if !is_dana_optional {
                        return Err(format!(
                            "Parquet nullability drift: unexpected NULL in required column `{}`",
                            col.name
                        ));
                    }
                    out.push(Val::OptNone);
                }
            }
        }
    }
    Ok(())
}

// ===========================================================================
// Direct Columnar Apache Parquet Decoder & Writer (`VmTable` Fast Path)
// ===========================================================================

enum DefLevels {
    AllPresent,
    AllNull(usize),
    Mixed {
        levels: Vec<u8>,
        non_null_count: usize,
    },
}

/// Zero-allocation fast decoder for `bit_width == 1` Parquet definition levels.
/// Recognizes single-run all-present or all-null pages in O(1) without allocating a `Vec`.
fn decode_def_levels_1bit(data: &[u8], count: usize) -> Result<DefLevels, String> {
    if count == 0 {
        return Ok(DefLevels::AllPresent);
    }
    if count > MAX_PARQUET_PAGE_VALUES {
        return Err(format!(
            "Parquet RLE value count ({count}) exceeds limit ({MAX_PARQUET_PAGE_VALUES})"
        ));
    }
    let mut pos = 0usize;
    let first_hdr = read_uvarint(data, &mut pos)?;
    if (first_hdr & 1) == 0 {
        let run_len = usize::try_from(first_hdr >> 1)
            .map_err(|_| "Parquet RLE run length overflow".to_string())?;
        let &val_byte = data
            .get(pos)
            .ok_or_else(|| "truncated Parquet RLE run value".to_string())?;
        if run_len >= count {
            return Ok(if (val_byte & 1) != 0 {
                DefLevels::AllPresent
            } else {
                DefLevels::AllNull(count)
            });
        }
    }

    // General multi-run path into compact `Vec<u8>` (4x smaller than `Vec<u32>`).
    let mut levels = Vec::with_capacity(count.min(65_536));
    let mut non_null_count = 0usize;
    pos = 0;
    while levels.len() < count {
        let header = read_uvarint(data, &mut pos)?;
        if (header & 1) == 0 {
            let run_len = usize::try_from(header >> 1)
                .map_err(|_| "Parquet RLE run length overflow".to_string())?;
            let &val_byte = data
                .get(pos)
                .ok_or_else(|| "truncated Parquet RLE run value".to_string())?;
            pos += 1;
            let bit = val_byte & 1;
            let take = run_len.min(count - levels.len());
            levels.resize(levels.len() + take, bit);
            if bit != 0 {
                non_null_count += take;
            }
        } else {
            let num_groups = usize::try_from(header >> 1)
                .map_err(|_| "Parquet bit-packed group count overflow".to_string())?;
            let end = pos
                .checked_add(num_groups)
                .ok_or_else(|| "Parquet bit-packed bounds overflow".to_string())?;
            if end > data.len() {
                return Err("truncated Parquet bit-packed run".to_string());
            }
            for &byte in &data[pos..end] {
                for bit_i in 0..8u8 {
                    if levels.len() >= count {
                        break;
                    }
                    let bit = (byte >> bit_i) & 1;
                    levels.push(bit);
                    non_null_count += usize::from(bit);
                }
            }
            pos = end;
        }
    }
    if non_null_count == count {
        Ok(DefLevels::AllPresent)
    } else if non_null_count == 0 {
        Ok(DefLevels::AllNull(count))
    } else {
        Ok(DefLevels::Mixed {
            levels,
            non_null_count,
        })
    }
}

#[inline]
fn decode_decimal_be_to_i128(bytes: &[u8], src_scale: i32) -> Result<i128, String> {
    if bytes.is_empty() {
        return Err("empty big-endian two's-complement decimal bytes".to_string());
    }
    if bytes.len() <= 16 && (0..=38).contains(&src_scale) {
        let sign_fill = if (bytes[0] & 0x80) != 0 { 0xFF } else { 0x00 };
        let mut buf = [sign_fill; 16];
        buf[16 - bytes.len()..].copy_from_slice(bytes);
        let raw = i128::from_be_bytes(buf);
        return rescale_decimal_i128_fast(raw, src_scale);
    }
    let unscaled = decode_be_twos_complement_bigint(bytes)?;
    let scaled = rescale_decimal_to_dana(unscaled, src_scale)?;
    scaled
        .to_i128()
        .ok_or_else(|| "Parquet decimal value overflows Dana fixed-point Decimal range".to_string())
}

#[inline]
fn rescale_decimal_i128_fast(raw: i128, src_scale: i32) -> Result<i128, String> {
    if !(0..=76).contains(&src_scale) {
        return Err(format!("unsupported Parquet decimal scale {src_scale}"));
    }
    if src_scale == 18 {
        if !(DEC_MIN..=DEC_MAX).contains(&raw) {
            return Err(
                "Parquet decimal value overflows Dana fixed-point Decimal range".to_string(),
            );
        }
        return Ok(raw);
    }
    if src_scale < 18 {
        let mult = 10i128.pow((18 - src_scale) as u32);
        let scaled = raw.checked_mul(mult).ok_or_else(|| {
            "Parquet decimal value overflows Dana fixed-point Decimal range".to_string()
        })?;
        if !(DEC_MIN..=DEC_MAX).contains(&scaled) {
            return Err(
                "Parquet decimal value overflows Dana fixed-point Decimal range".to_string(),
            );
        }
        return Ok(scaled);
    }
    if src_scale <= 38 {
        let div = 10i128.pow((src_scale - 18) as u32);
        if raw % div != 0 {
            return Err(format!(
                "Parquet decimal with scale {src_scale} has non-zero precision beyond 18 fractional digits"
            ));
        }
        let q = raw / div;
        if !(DEC_MIN..=DEC_MAX).contains(&q) {
            return Err(
                "Parquet decimal value overflows Dana fixed-point Decimal range".to_string(),
            );
        }
        return Ok(q);
    }
    let scaled = rescale_decimal_to_dana(BigInt::from(raw), src_scale)?;
    scaled
        .to_i128()
        .ok_or_else(|| "Parquet decimal value overflows Dana fixed-point Decimal range".to_string())
}

#[inline]
fn convert_timestamp_unit(v: i64, unit: TimeUnit) -> Result<i64, String> {
    match unit {
        TimeUnit::Millis => v
            .checked_mul(1_000)
            .ok_or_else(|| "Parquet TIMESTAMP_MILLIS overflow".to_string()),
        TimeUnit::Micros => Ok(v),
        TimeUnit::Nanos => Ok(v.div_euclid(1_000)),
    }
}

/// Pre-converted typed dictionary decoded once per column chunk (UTF-8, Decimal rescaling,
/// and timestamp unit conversion happen ONCE per dictionary entry instead of once per row!).
enum TypedDict {
    Bool(Vec<u8>),
    Int(Vec<i64>),
    Float(Vec<u64>),
    Decimal(Vec<i128>),
    Text { offsets: Vec<usize>, data: Vec<u8> },
    Bytes { offsets: Vec<usize>, data: Vec<u8> },
    Date(Vec<i64>),
    Timestamp(Vec<i64>),
    Duration(Vec<i64>),
}

impl TypedDict {
    fn len(&self) -> usize {
        match self {
            Self::Bool(v) => v.len(),
            Self::Int(v) | Self::Date(v) | Self::Timestamp(v) | Self::Duration(v) => v.len(),
            Self::Float(v) => v.len(),
            Self::Decimal(v) => v.len(),
            Self::Text { offsets, .. } | Self::Bytes { offsets, .. } => {
                offsets.len().saturating_sub(1)
            }
        }
    }
}

fn decode_typed_dict(
    payload: &[u8],
    phys_type: i32,
    col: &ColSpec,
    se: &SchemaElement,
    dict_count: usize,
) -> Result<TypedDict, String> {
    if dict_count > MAX_PARQUET_PAGE_VALUES {
        return Err(format!(
            "Parquet PLAIN value count ({dict_count}) exceeds limit ({MAX_PARQUET_PAGE_VALUES})"
        ));
    }
    let (inner_ty, _) = peel_option(&col.ty);
    let mut builder = TypedColChunk::new(inner_ty, false, dict_count);
    builder.append_plain_non_null(payload, phys_type, se, col, dict_count)?;
    match builder.data {
        ColumnData::Bool(v) => Ok(TypedDict::Bool(v)),
        ColumnData::Int(v) => Ok(TypedDict::Int(v)),
        ColumnData::Float(v) => Ok(TypedDict::Float(v)),
        ColumnData::Decimal(v) => Ok(TypedDict::Decimal(v)),
        ColumnData::Text { offsets, data } => Ok(TypedDict::Text { offsets, data }),
        ColumnData::Bytes { offsets, data } => Ok(TypedDict::Bytes { offsets, data }),
        ColumnData::Date(v) => Ok(TypedDict::Date(v)),
        ColumnData::Timestamp(v) => Ok(TypedDict::Timestamp(v)),
        ColumnData::Duration(v) => Ok(TypedDict::Duration(v)),
        _ => Err(format!(
            "unsupported dictionary type `{:?}` for column `{}`",
            col.ty, col.name
        )),
    }
}

struct TypedColChunk {
    data: ColumnData,
    validity: Option<NullBitmap>,
}

impl TypedColChunk {
    fn new(inner_ty: &ScalarTy, is_optional: bool, cap: usize) -> Self {
        let cap_clamped = cap.min(1_048_576);
        let data = match inner_ty {
            ScalarTy::Bool => ColumnData::Bool(Vec::with_capacity(cap_clamped)),
            ScalarTy::Int => ColumnData::Int(Vec::with_capacity(cap_clamped)),
            ScalarTy::Float => ColumnData::Float(Vec::with_capacity(cap_clamped)),
            ScalarTy::Decimal => ColumnData::Decimal(Vec::with_capacity(cap_clamped)),
            ScalarTy::Text => {
                let mut offsets = Vec::with_capacity(cap_clamped + 1);
                offsets.push(0);
                ColumnData::Text {
                    offsets,
                    data: Vec::with_capacity(cap_clamped.saturating_mul(8)),
                }
            }
            ScalarTy::Bytes => {
                let mut offsets = Vec::with_capacity(cap_clamped + 1);
                offsets.push(0);
                ColumnData::Bytes {
                    offsets,
                    data: Vec::with_capacity(cap_clamped.saturating_mul(8)),
                }
            }
            ScalarTy::Date => ColumnData::Date(Vec::with_capacity(cap_clamped)),
            ScalarTy::Timestamp => ColumnData::Timestamp(Vec::with_capacity(cap_clamped)),
            ScalarTy::Duration => ColumnData::Duration(Vec::with_capacity(cap_clamped)),
            _ => ColumnData::Generic(Vec::with_capacity(cap_clamped)),
        };
        let validity = if is_optional && !matches!(data, ColumnData::Generic(_)) {
            Some(NullBitmap::with_capacity(cap_clamped))
        } else {
            None
        };
        Self { data, validity }
    }

    fn len(&self) -> usize {
        self.data.len()
    }

    fn push_nulls(&mut self, count: usize) {
        if let Some(bm) = &mut self.validity {
            for _ in 0..count {
                bm.push(false);
            }
        }
        match &mut self.data {
            ColumnData::Unit(n) => *n += count,
            ColumnData::Bool(v) => v.resize(v.len() + count, 0),
            ColumnData::Int(v)
            | ColumnData::Date(v)
            | ColumnData::Timestamp(v)
            | ColumnData::Duration(v) => v.resize(v.len() + count, 0),
            ColumnData::Decimal(v) => v.resize(v.len() + count, 0),
            ColumnData::Float(v) => v.resize(v.len() + count, 0),
            ColumnData::Text { offsets, data } | ColumnData::Bytes { offsets, data } => {
                let end = data.len();
                offsets.resize(offsets.len() + count, end);
            }
            ColumnData::Generic(v) => v.resize(v.len() + count, Val::OptNone),
        }
    }

    fn push_valid_bits(&mut self, count: usize) {
        if let Some(bm) = &mut self.validity {
            for _ in 0..count {
                bm.push(true);
            }
        }
    }

    fn append_plain_non_null(
        &mut self,
        payload: &[u8],
        phys_type: i32,
        se: &SchemaElement,
        col: &ColSpec,
        count: usize,
    ) -> Result<(), String> {
        if count == 0 {
            return Ok(());
        }
        if count > MAX_PARQUET_PAGE_VALUES {
            return Err(format!(
                "Parquet PLAIN value count ({count}) exceeds limit ({MAX_PARQUET_PAGE_VALUES})"
            ));
        }
        match (&mut self.data, phys_type) {
            (ColumnData::Bool(out), PT_BOOLEAN) => {
                let need = count.div_ceil(8);
                if need > payload.len() {
                    return Err("truncated Parquet BOOLEAN PLAIN payload".to_string());
                }
                out.reserve(count);
                for i in 0..count {
                    out.push((payload[i >> 3] >> (i & 7)) & 1);
                }
            }
            (ColumnData::Int(out), PT_INT64) | (ColumnData::Duration(out), PT_INT64) => {
                let need = count
                    .checked_mul(8)
                    .ok_or_else(|| "Parquet INT64 byte size overflow".to_string())?;
                if need > payload.len() {
                    return Err("truncated Parquet INT64 PLAIN payload".to_string());
                }
                out.reserve(count);
                for ch in payload[..need].chunks_exact(8) {
                    out.push(i64::from_le_bytes([
                        ch[0], ch[1], ch[2], ch[3], ch[4], ch[5], ch[6], ch[7],
                    ]));
                }
            }
            (ColumnData::Int(out), PT_INT32) | (ColumnData::Date(out), PT_INT32) => {
                let need = count
                    .checked_mul(4)
                    .ok_or_else(|| "Parquet INT32 byte size overflow".to_string())?;
                if need > payload.len() {
                    return Err("truncated Parquet INT32 PLAIN payload".to_string());
                }
                out.reserve(count);
                for ch in payload[..need].chunks_exact(4) {
                    out.push(i64::from(i32::from_le_bytes([ch[0], ch[1], ch[2], ch[3]])));
                }
            }
            (ColumnData::Timestamp(out), PT_INT64) => {
                let unit = parquet_timestamp_unit(se).ok_or_else(|| {
                    format!(
                        "Parquet column `{}` missing TIMESTAMP unit metadata",
                        col.name
                    )
                })?;
                let need = count
                    .checked_mul(8)
                    .ok_or_else(|| "Parquet INT64 byte size overflow".to_string())?;
                if need > payload.len() {
                    return Err("truncated Parquet INT64 PLAIN payload".to_string());
                }
                out.reserve(count);
                for ch in payload[..need].chunks_exact(8) {
                    let raw = i64::from_le_bytes([
                        ch[0], ch[1], ch[2], ch[3], ch[4], ch[5], ch[6], ch[7],
                    ]);
                    out.push(convert_timestamp_unit(raw, unit)?);
                }
            }
            (ColumnData::Float(out), PT_DOUBLE) => {
                let need = count
                    .checked_mul(8)
                    .ok_or_else(|| "Parquet DOUBLE byte size overflow".to_string())?;
                if need > payload.len() {
                    return Err("truncated Parquet DOUBLE PLAIN payload".to_string());
                }
                out.reserve(count);
                for ch in payload[..need].chunks_exact(8) {
                    let f = f64::from_le_bytes([
                        ch[0], ch[1], ch[2], ch[3], ch[4], ch[5], ch[6], ch[7],
                    ]);
                    out.push(Float64::from_f64(f).bits);
                }
            }
            (ColumnData::Float(out), PT_FLOAT) => {
                let need = count
                    .checked_mul(4)
                    .ok_or_else(|| "Parquet FLOAT byte size overflow".to_string())?;
                if need > payload.len() {
                    return Err("truncated Parquet FLOAT PLAIN payload".to_string());
                }
                out.reserve(count);
                for ch in payload[..need].chunks_exact(4) {
                    let f = f32::from_le_bytes([ch[0], ch[1], ch[2], ch[3]]);
                    out.push(Float64::from_f64(f64::from(f)).bits);
                }
            }
            (ColumnData::Decimal(out), pt) => {
                let src_scale = parquet_decimal_scale(se).ok_or_else(|| {
                    format!(
                        "Parquet column `{}` missing DECIMAL scale metadata",
                        col.name
                    )
                })?;
                out.reserve(count);
                match pt {
                    PT_INT32 => {
                        let need = count
                            .checked_mul(4)
                            .ok_or_else(|| "Parquet INT32 byte size overflow".to_string())?;
                        if need > payload.len() {
                            return Err("truncated Parquet INT32 PLAIN payload".to_string());
                        }
                        for ch in payload[..need].chunks_exact(4) {
                            let n = i32::from_le_bytes([ch[0], ch[1], ch[2], ch[3]]);
                            out.push(rescale_decimal_i128_fast(i128::from(n), src_scale)?);
                        }
                    }
                    PT_INT64 => {
                        let need = count
                            .checked_mul(8)
                            .ok_or_else(|| "Parquet INT64 byte size overflow".to_string())?;
                        if need > payload.len() {
                            return Err("truncated Parquet INT64 PLAIN payload".to_string());
                        }
                        for ch in payload[..need].chunks_exact(8) {
                            let n = i64::from_le_bytes([
                                ch[0], ch[1], ch[2], ch[3], ch[4], ch[5], ch[6], ch[7],
                            ]);
                            out.push(rescale_decimal_i128_fast(i128::from(n), src_scale)?);
                        }
                    }
                    PT_FIXED_LEN_BYTE_ARRAY => {
                        let flen = usize::try_from(se.type_length.ok_or_else(|| {
                            "FIXED_LEN_BYTE_ARRAY missing `type_length`".to_string()
                        })?)
                        .map_err(|_| "negative FIXED_LEN_BYTE_ARRAY `type_length`".to_string())?;
                        let need = count.checked_mul(flen).ok_or_else(|| {
                            "Parquet FIXED_LEN_BYTE_ARRAY size overflow".to_string()
                        })?;
                        if need > payload.len() {
                            return Err(
                                "truncated Parquet FIXED_LEN_BYTE_ARRAY payload".to_string()
                            );
                        }
                        if flen == 0 {
                            return Err(
                                "empty big-endian two's-complement decimal bytes".to_string()
                            );
                        }
                        for ch in payload[..need].chunks_exact(flen) {
                            out.push(decode_decimal_be_to_i128(ch, src_scale)?);
                        }
                    }
                    PT_BYTE_ARRAY => {
                        let mut pos = 0usize;
                        for _ in 0..count {
                            if pos + 4 > payload.len() {
                                return Err(
                                    "truncated Parquet BYTE_ARRAY length prefix".to_string()
                                );
                            }
                            let len = u32::from_le_bytes([
                                payload[pos],
                                payload[pos + 1],
                                payload[pos + 2],
                                payload[pos + 3],
                            ]) as usize;
                            pos += 4;
                            let end = pos
                                .checked_add(len)
                                .ok_or_else(|| "Parquet BYTE_ARRAY bounds overflow".to_string())?;
                            if end > payload.len() {
                                return Err("truncated Parquet BYTE_ARRAY payload".to_string());
                            }
                            out.push(decode_decimal_be_to_i128(&payload[pos..end], src_scale)?);
                            pos = end;
                        }
                    }
                    _ => {
                        return Err(format!(
                            "unexpected Parquet physical representation for Decimal column `{}`",
                            col.name
                        ));
                    }
                }
            }
            (ColumnData::Text { offsets, data }, PT_BYTE_ARRAY) => {
                offsets.reserve(count);
                let mut pos = 0usize;
                for _ in 0..count {
                    if pos + 4 > payload.len() {
                        return Err("truncated Parquet BYTE_ARRAY length prefix".to_string());
                    }
                    let len = u32::from_le_bytes([
                        payload[pos],
                        payload[pos + 1],
                        payload[pos + 2],
                        payload[pos + 3],
                    ]) as usize;
                    pos += 4;
                    let end = pos
                        .checked_add(len)
                        .ok_or_else(|| "Parquet BYTE_ARRAY bounds overflow".to_string())?;
                    if end > payload.len() {
                        return Err("truncated Parquet BYTE_ARRAY payload".to_string());
                    }
                    let slice = &payload[pos..end];
                    let _ = std::str::from_utf8(slice).map_err(|e| {
                        format!("invalid UTF-8 in Parquet Text column `{}`: {e}", col.name)
                    })?;
                    data.extend_from_slice(slice);
                    offsets.push(data.len());
                    pos = end;
                }
            }
            (ColumnData::Bytes { offsets, data }, PT_BYTE_ARRAY) => {
                offsets.reserve(count);
                let mut pos = 0usize;
                for _ in 0..count {
                    if pos + 4 > payload.len() {
                        return Err("truncated Parquet BYTE_ARRAY length prefix".to_string());
                    }
                    let len = u32::from_le_bytes([
                        payload[pos],
                        payload[pos + 1],
                        payload[pos + 2],
                        payload[pos + 3],
                    ]) as usize;
                    pos += 4;
                    let end = pos
                        .checked_add(len)
                        .ok_or_else(|| "Parquet BYTE_ARRAY bounds overflow".to_string())?;
                    if end > payload.len() {
                        return Err("truncated Parquet BYTE_ARRAY payload".to_string());
                    }
                    data.extend_from_slice(&payload[pos..end]);
                    offsets.push(data.len());
                    pos = end;
                }
            }
            (ColumnData::Bytes { offsets, data }, PT_FIXED_LEN_BYTE_ARRAY) => {
                let flen = usize::try_from(
                    se.type_length
                        .ok_or_else(|| "FIXED_LEN_BYTE_ARRAY missing `type_length`".to_string())?,
                )
                .map_err(|_| "negative FIXED_LEN_BYTE_ARRAY `type_length`".to_string())?;
                let need = count
                    .checked_mul(flen)
                    .ok_or_else(|| "Parquet FIXED_LEN_BYTE_ARRAY size overflow".to_string())?;
                if need > payload.len() {
                    return Err("truncated Parquet FIXED_LEN_BYTE_ARRAY payload".to_string());
                }
                offsets.reserve(count);
                if flen == 0 {
                    let end = data.len();
                    offsets.resize(offsets.len() + count, end);
                } else {
                    data.reserve(need);
                    for ch in payload[..need].chunks_exact(flen) {
                        data.extend_from_slice(ch);
                        offsets.push(data.len());
                    }
                }
            }
            _ => {
                return Err(format!(
                    "Parquet value type mismatch for column `{}`",
                    col.name
                ));
            }
        }
        Ok(())
    }

    fn append_dict_non_null(&mut self, dict: &TypedDict, indices: &[u32]) -> Result<(), String> {
        let dlen = dict.len();
        match (&mut self.data, dict) {
            (ColumnData::Bool(out), TypedDict::Bool(dv)) => {
                out.reserve(indices.len());
                for &idx in indices {
                    let &v = dv.get(idx as usize).ok_or_else(|| {
                        format!("Parquet dictionary index {idx} out of bounds (dict len {dlen})")
                    })?;
                    out.push(v);
                }
            }
            (ColumnData::Int(out), TypedDict::Int(dv))
            | (ColumnData::Date(out), TypedDict::Date(dv))
            | (ColumnData::Timestamp(out), TypedDict::Timestamp(dv))
            | (ColumnData::Duration(out), TypedDict::Duration(dv)) => {
                out.reserve(indices.len());
                for &idx in indices {
                    let &v = dv.get(idx as usize).ok_or_else(|| {
                        format!("Parquet dictionary index {idx} out of bounds (dict len {dlen})")
                    })?;
                    out.push(v);
                }
            }
            (ColumnData::Float(out), TypedDict::Float(dv)) => {
                out.reserve(indices.len());
                for &idx in indices {
                    let &v = dv.get(idx as usize).ok_or_else(|| {
                        format!("Parquet dictionary index {idx} out of bounds (dict len {dlen})")
                    })?;
                    out.push(v);
                }
            }
            (ColumnData::Decimal(out), TypedDict::Decimal(dv)) => {
                out.reserve(indices.len());
                for &idx in indices {
                    let &v = dv.get(idx as usize).ok_or_else(|| {
                        format!("Parquet dictionary index {idx} out of bounds (dict len {dlen})")
                    })?;
                    out.push(v);
                }
            }
            (
                ColumnData::Text { offsets, data },
                TypedDict::Text {
                    offsets: doff,
                    data: ddata,
                },
            )
            | (
                ColumnData::Bytes { offsets, data },
                TypedDict::Bytes {
                    offsets: doff,
                    data: ddata,
                },
            ) => {
                offsets.reserve(indices.len());
                for &idx in indices {
                    let i = idx as usize;
                    if i >= dlen {
                        return Err(format!(
                            "Parquet dictionary index {idx} out of bounds (dict len {dlen})"
                        ));
                    }
                    data.extend_from_slice(&ddata[doff[i]..doff[i + 1]]);
                    offsets.push(data.len());
                }
            }
            _ => {
                return Err("Parquet dictionary type mismatch".to_string());
            }
        }
        Ok(())
    }

    fn append_mixed_from_temp(&mut self, levels: &[u8], temp: &ColumnData) -> Result<(), String> {
        let mut val_idx = 0usize;
        if let Some(bm) = &mut self.validity {
            for &lvl in levels {
                bm.push(lvl != 0);
            }
        }
        match (&mut self.data, temp) {
            (ColumnData::Bool(out), ColumnData::Bool(src)) => {
                out.reserve(levels.len());
                for &lvl in levels {
                    if lvl != 0 {
                        let &v = src
                            .get(val_idx)
                            .ok_or_else(|| "Parquet non-null value underflow".to_string())?;
                        val_idx += 1;
                        out.push(v);
                    } else {
                        out.push(0);
                    }
                }
            }
            (ColumnData::Int(out), ColumnData::Int(src))
            | (ColumnData::Date(out), ColumnData::Date(src))
            | (ColumnData::Timestamp(out), ColumnData::Timestamp(src))
            | (ColumnData::Duration(out), ColumnData::Duration(src)) => {
                out.reserve(levels.len());
                for &lvl in levels {
                    if lvl != 0 {
                        let &v = src
                            .get(val_idx)
                            .ok_or_else(|| "Parquet non-null value underflow".to_string())?;
                        val_idx += 1;
                        out.push(v);
                    } else {
                        out.push(0);
                    }
                }
            }
            (ColumnData::Float(out), ColumnData::Float(src)) => {
                out.reserve(levels.len());
                for &lvl in levels {
                    if lvl != 0 {
                        let &v = src
                            .get(val_idx)
                            .ok_or_else(|| "Parquet non-null value underflow".to_string())?;
                        val_idx += 1;
                        out.push(v);
                    } else {
                        out.push(0);
                    }
                }
            }
            (ColumnData::Decimal(out), ColumnData::Decimal(src)) => {
                out.reserve(levels.len());
                for &lvl in levels {
                    if lvl != 0 {
                        let &v = src
                            .get(val_idx)
                            .ok_or_else(|| "Parquet non-null value underflow".to_string())?;
                        val_idx += 1;
                        out.push(v);
                    } else {
                        out.push(0);
                    }
                }
            }
            (
                ColumnData::Text { offsets, data },
                ColumnData::Text {
                    offsets: soff,
                    data: sdata,
                },
            )
            | (
                ColumnData::Bytes { offsets, data },
                ColumnData::Bytes {
                    offsets: soff,
                    data: sdata,
                },
            ) => {
                let src_len = soff.len().saturating_sub(1);
                offsets.reserve(levels.len());
                for &lvl in levels {
                    if lvl != 0 {
                        if val_idx >= src_len {
                            return Err("Parquet non-null value underflow".to_string());
                        }
                        data.extend_from_slice(&sdata[soff[val_idx]..soff[val_idx + 1]]);
                        offsets.push(data.len());
                        val_idx += 1;
                    } else {
                        offsets.push(data.len());
                    }
                }
            }
            _ => return Err("Parquet mixed-null scatter type mismatch".to_string()),
        }
        Ok(())
    }

    #[expect(
        clippy::too_many_arguments,
        reason = "Direct columnar Parquet page decoder threads physical/logical metadata and optional dictionary without heap boxing"
    )]
    fn append_page(
        &mut self,
        def_levels: Option<DefLevels>,
        value_bytes: &[u8],
        encoding: i32,
        phys_type: i32,
        col: &ColSpec,
        se: &SchemaElement,
        num_values: usize,
        is_dana_optional: bool,
        dict: Option<&TypedDict>,
    ) -> Result<(), String> {
        let (inner_ty, _) = peel_option(&col.ty);
        match def_levels {
            None | Some(DefLevels::AllPresent) => {
                self.push_valid_bits(num_values);
                match encoding {
                    ENC_PLAIN => {
                        self.append_plain_non_null(value_bytes, phys_type, se, col, num_values)?;
                    }
                    ENC_RLE_DICTIONARY | ENC_PLAIN_DICTIONARY => {
                        if num_values > 0 {
                            let d = dict.ok_or_else(|| {
                                "Parquet dictionary-encoded data page encountered before DICTIONARY_PAGE"
                                    .to_string()
                            })?;
                            let &bit_width = value_bytes.first().ok_or_else(|| {
                                "truncated Parquet dictionary bit-width byte".to_string()
                            })?;
                            let indices =
                                decode_rle_hybrid(&value_bytes[1..], bit_width, num_values)?;
                            self.append_dict_non_null(d, &indices)?;
                        }
                    }
                    other => {
                        return Err(format!("unsupported Parquet page encoding `{other}`"));
                    }
                }
            }
            Some(DefLevels::AllNull(n)) => {
                if !is_dana_optional {
                    return Err(format!(
                        "Parquet nullability drift: unexpected NULL in required column `{}`",
                        col.name
                    ));
                }
                self.push_nulls(n);
            }
            Some(DefLevels::Mixed {
                levels,
                non_null_count,
            }) => {
                if !is_dana_optional {
                    return Err(format!(
                        "Parquet nullability drift: unexpected NULL in required column `{}`",
                        col.name
                    ));
                }
                let mut temp = TypedColChunk::new(inner_ty, false, non_null_count);
                match encoding {
                    ENC_PLAIN => {
                        temp.append_plain_non_null(
                            value_bytes,
                            phys_type,
                            se,
                            col,
                            non_null_count,
                        )?;
                    }
                    ENC_RLE_DICTIONARY | ENC_PLAIN_DICTIONARY => {
                        if non_null_count > 0 {
                            let d = dict.ok_or_else(|| {
                                "Parquet dictionary-encoded data page encountered before DICTIONARY_PAGE"
                                    .to_string()
                            })?;
                            let &bit_width = value_bytes.first().ok_or_else(|| {
                                "truncated Parquet dictionary bit-width byte".to_string()
                            })?;
                            let indices =
                                decode_rle_hybrid(&value_bytes[1..], bit_width, non_null_count)?;
                            temp.append_dict_non_null(d, &indices)?;
                        }
                    }
                    other => {
                        return Err(format!("unsupported Parquet page encoding `{other}`"));
                    }
                }
                self.append_mixed_from_temp(&levels, &temp.data)?;
            }
        }
        Ok(())
    }
}

fn decode_column_chunk_typed(
    file_bytes: &[u8],
    footer_start: usize,
    meta: &ColumnMetaData,
    col: &ColSpec,
    se: &SchemaElement,
    expected_rows: usize,
) -> Result<Column, String> {
    let (inner_ty, is_dana_optional) = peel_option(&col.ty);
    if inner_ty.is_option() {
        // Rare nested `Option(Option(T))`: fall back cleanly to boxed `Val` decode.
        let vals = decode_column_chunk(file_bytes, footer_start, meta, col, se, expected_rows)?;
        return Ok(Column::from_vals(col.clone(), &vals));
    }

    let start_i64 = match meta.dictionary_page_offset {
        Some(doff) if doff > 0 && doff < meta.data_page_offset => doff,
        _ => meta.data_page_offset,
    };
    let start = usize::try_from(start_i64)
        .map_err(|_| format!("negative Parquet page offset for column `{}`", col.name))?;
    let comp_len = usize::try_from(meta.total_compressed_size)
        .map_err(|_| format!("negative Parquet compressed size for column `{}`", col.name))?;
    let end = start
        .checked_add(comp_len)
        .ok_or_else(|| "Parquet column chunk bounds overflow".to_string())?;
    if end > footer_start || end > file_bytes.len() {
        return Err(format!(
            "Parquet column chunk for `{}` extends past file data region",
            col.name
        ));
    }

    let is_pq_optional = se.repetition_type == Some(REP_OPTIONAL);
    let max_def_level: u32 = u32::from(is_pq_optional);

    let mut cursor = start;
    let mut dictionary: Option<TypedDict> = None;
    let mut chunk = TypedColChunk::new(inner_ty, is_dana_optional, expected_rows);

    while chunk.len() < expected_rows && cursor < end {
        let mut hdr_reader = ThriftReader::new(&file_bytes[cursor..end]);
        let ph = read_page_header(&mut hdr_reader)?;
        let hdr_len = hdr_reader.pos;
        cursor += hdr_len;

        let comp_sz = usize::try_from(ph.compressed_page_size)
            .map_err(|_| "negative Parquet compressed_page_size".to_string())?;
        let uncomp_sz = usize::try_from(ph.uncompressed_page_size)
            .map_err(|_| "negative Parquet uncompressed_page_size".to_string())?;
        let Some(page_end) = cursor.checked_add(comp_sz) else {
            return Err(format!(
                "Parquet page size overflow in column `{}`",
                col.name
            ));
        };
        if page_end > end {
            return Err(format!(
                "truncated Parquet page payload in column `{}`",
                col.name
            ));
        }
        let page_raw = &file_bytes[cursor..page_end];
        cursor = page_end;

        match ph.page_type {
            PAGE_DICTIONARY => {
                let dph = ph
                    .dictionary_page_header
                    .ok_or_else(|| "DICTIONARY_PAGE missing dictionary_page_header".to_string())?;
                if dph.encoding != ENC_PLAIN && dph.encoding != ENC_PLAIN_DICTIONARY {
                    return Err(format!(
                        "unsupported Parquet dictionary encoding {}",
                        dph.encoding
                    ));
                }
                let dict_count = usize::try_from(dph.num_values)
                    .map_err(|_| "negative Parquet dictionary num_values".to_string())?;
                let payload = decompress_page_bytes(page_raw, meta.codec, uncomp_sz)?;
                dictionary = Some(decode_typed_dict(
                    &payload,
                    meta.phys_type,
                    col,
                    se,
                    dict_count,
                )?);
            }
            PAGE_DATA_V1 => {
                let dph = ph
                    .data_page_header
                    .ok_or_else(|| "DATA_PAGE missing data_page_header".to_string())?;
                let num_values = usize::try_from(dph.num_values)
                    .map_err(|_| "negative Parquet DataPage num_values".to_string())?;
                let payload = decompress_page_bytes(page_raw, meta.codec, uncomp_sz)?;
                let mut pos = 0usize;

                let def_levels = if max_def_level > 0 {
                    if dph.definition_level_encoding != ENC_RLE {
                        return Err(format!(
                            "unsupported Parquet definition level encoding {}",
                            dph.definition_level_encoding
                        ));
                    }
                    if pos + 4 > payload.len() {
                        return Err("truncated Parquet definition level length".to_string());
                    }
                    let def_len = u32::from_le_bytes([
                        payload[pos],
                        payload[pos + 1],
                        payload[pos + 2],
                        payload[pos + 3],
                    ]) as usize;
                    pos += 4;
                    if pos + def_len > payload.len() {
                        return Err("truncated Parquet definition level data".to_string());
                    }
                    let dl = decode_def_levels_1bit(&payload[pos..pos + def_len], num_values)?;
                    pos += def_len;
                    Some(dl)
                } else {
                    None
                };

                chunk.append_page(
                    def_levels,
                    &payload[pos..],
                    dph.encoding,
                    meta.phys_type,
                    col,
                    se,
                    num_values,
                    is_dana_optional,
                    dictionary.as_ref(),
                )?;
            }
            PAGE_DATA_V2 => {
                let v2 = ph
                    .data_page_header_v2
                    .ok_or_else(|| "DATA_PAGE_V2 missing data_page_header_v2".to_string())?;
                let num_values = usize::try_from(v2.num_values)
                    .map_err(|_| "negative Parquet DataPageV2 num_values".to_string())?;
                let rep_len = usize::try_from(v2.repetition_levels_byte_length)
                    .map_err(|_| "negative DataPageV2 rep_len".to_string())?;
                let def_len = usize::try_from(v2.definition_levels_byte_length)
                    .map_err(|_| "negative DataPageV2 def_len".to_string())?;
                let levels_total = rep_len
                    .checked_add(def_len)
                    .ok_or_else(|| "DataPageV2 levels overflow".to_string())?;
                if levels_total > page_raw.len() || levels_total > uncomp_sz {
                    return Err("truncated Parquet DataPageV2 levels".to_string());
                }
                let def_levels = if max_def_level > 0 {
                    let def_slice = &page_raw[rep_len..rep_len + def_len];
                    Some(decode_def_levels_1bit(def_slice, num_values)?)
                } else {
                    None
                };
                let data_part = &page_raw[levels_total..];
                let expected_data_uncomp = uncomp_sz - levels_total;
                let owned_data;
                let data_bytes: &[u8] = if v2.is_compressed {
                    owned_data =
                        decompress_page_bytes(data_part, meta.codec, expected_data_uncomp)?;
                    &owned_data
                } else {
                    if data_part.len() != expected_data_uncomp {
                        return Err("DataPageV2 uncompressed payload length mismatch".to_string());
                    }
                    data_part
                };
                chunk.append_page(
                    def_levels,
                    data_bytes,
                    v2.encoding,
                    meta.phys_type,
                    col,
                    se,
                    num_values,
                    is_dana_optional,
                    dictionary.as_ref(),
                )?;
            }
            other => {
                if other != 1 {
                    return Err(format!("unsupported Parquet page type `{other}`"));
                }
            }
        }
    }

    if chunk.len() != expected_rows {
        return Err(format!(
            "Parquet column `{}` decoded {} values, expected {expected_rows}",
            col.name,
            chunk.len()
        ));
    }
    Ok(Column {
        spec: col.clone(),
        data: chunk.data,
        validity: chunk.validity,
    })
}

/// Read an Apache Parquet file directly into 2,048-row columnar [`VmTable`] batches without
/// materializing intermediate `Vec<Vec<Val>>` or `Vec<TableRow>` structures.
///
/// Decodes `PLAIN` and `RLE_DICTIONARY`/`PLAIN_DICTIONARY` pages (`DataPage` v1 & v2,
/// `UNCOMPRESSED`/`SNAPPY`/`GZIP`/`ZSTD`) directly into typed columnar vectors (parallelized
/// across columns within large row groups) and validates schema `where` constraints via
/// [`FastColConstraint`] (with fallback to `fallback_constraint`), preserving exact 1-based
/// `(row, column)` error messages and all `MAX_PARQUET_*` safety limits.
///
/// # Errors
/// Returns an error string on invalid magic bytes, corrupted Thrift metadata, unsupported
/// encoding/codec, schema/nullability drift, or `where` constraint failure.
pub fn read_parquet_bytes_to_vm_table<F>(
    bytes: &[u8],
    schema: &TableTy,
    batch_size: usize,
    fast_constraints: &[FastColConstraint],
    mut fallback_constraint: F,
) -> Result<VmTable, String>
where
    F: FnMut(usize, &Val) -> bool,
{
    if bytes.len() < 12 {
        return Err("Parquet file too short (minimum 12 bytes)".to_string());
    }
    if &bytes[..4] != PARQUET_MAGIC || &bytes[bytes.len() - 4..] != PARQUET_MAGIC {
        return Err("invalid Parquet header/footer magic (expected `PAR1`)".to_string());
    }
    let footer_len_slice: [u8; 4] = bytes[bytes.len() - 8..bytes.len() - 4]
        .try_into()
        .map_err(|_| "failed to read Parquet footer length".to_string())?;
    let footer_len = u32::from_le_bytes(footer_len_slice) as usize;
    if footer_len > MAX_PARQUET_FOOTER_BYTES || footer_len + 12 > bytes.len() {
        return Err(format!("invalid Parquet footer length ({footer_len})"));
    }
    let footer_start = bytes.len() - 8 - footer_len;
    let footer_bytes = &bytes[footer_start..bytes.len() - 8];

    let mut fm_reader = ThriftReader::new(footer_bytes);
    let fm = read_file_metadata(&mut fm_reader)?;
    if fm.schema.is_empty() {
        return Err("Parquet file has empty schema".to_string());
    }

    let mut leaf_by_name: HashMap<String, (usize, &SchemaElement)> = HashMap::new();
    let mut leaf_idx = 0usize;
    for se in fm.schema.iter().skip(1) {
        if se.phys_type.is_some() {
            leaf_by_name
                .entry(se.name.clone())
                .or_insert((leaf_idx, se));
            leaf_idx += 1;
        }
    }

    let mut mapped_cols: Vec<(usize, &SchemaElement)> = Vec::with_capacity(schema.cols.len());
    for col in &schema.cols {
        let Some(&(pq_col_idx, se)) = leaf_by_name.get(col.name.as_str()) else {
            return Err(format!(
                "Parquet schema drift: missing required column `{}`",
                col.name
            ));
        };
        verify_parquet_col_compat(col, se)?;
        mapped_cols.push((pq_col_idx, se));
    }

    let total_rows = usize::try_from(fm.num_rows)
        .map_err(|_| "Parquet file has negative num_rows".to_string())?;
    let chunk_size = batch_size.clamp(1, usize::from(u16::MAX));
    let mut all_batches: Vec<Batch> = Vec::with_capacity(total_rows.div_ceil(chunk_size));
    let mut global_row_offset = 0usize;

    for rg in &fm.row_groups {
        let rg_rows = usize::try_from(rg.num_rows)
            .map_err(|_| "Parquet row group has negative num_rows".to_string())?;
        if rg_rows == 0 {
            continue;
        }
        if rg_rows > MAX_PARQUET_PAGE_VALUES {
            return Err(format!(
                "Parquet row group num_rows ({rg_rows}) exceeds limit ({MAX_PARQUET_PAGE_VALUES})"
            ));
        }

        // Resolve column metadata references upfront so parallel column decoding has clean borrows.
        let mut col_tasks: Vec<(&ColSpec, &SchemaElement, &ColumnMetaData)> =
            Vec::with_capacity(schema.cols.len());
        for (ci, col) in schema.cols.iter().enumerate() {
            let (pq_idx, se) = mapped_cols[ci];
            let chunk = rg
                .columns
                .iter()
                .find(|c| {
                    c.meta_data.as_ref().is_some_and(|m| {
                        m.path_in_schema.len() == 1 && m.path_in_schema[0] == col.name
                    })
                })
                .or_else(|| rg.columns.get(pq_idx))
                .ok_or_else(|| {
                    format!("Parquet row group missing column chunk for `{}`", col.name)
                })?;
            let meta = chunk.meta_data.as_ref().ok_or_else(|| {
                format!(
                    "Parquet column chunk for `{}` is missing inline metadata",
                    col.name
                )
            })?;
            col_tasks.push((col, se, meta));
        }

        let rg_cols: Vec<Column> = if rg_rows >= 8_192 && col_tasks.len() >= 2 {
            std::thread::scope(|scope| -> Result<Vec<Column>, String> {
                let mut handles = Vec::with_capacity(col_tasks.len());
                for &(col, se, meta) in &col_tasks {
                    handles.push(scope.spawn(move || {
                        decode_column_chunk_typed(bytes, footer_start, meta, col, se, rg_rows)
                    }));
                }
                let mut decoded = Vec::with_capacity(col_tasks.len());
                for h in handles {
                    let res = h
                        .join()
                        .map_err(|_| "Parquet column decode worker panicked".to_string())?;
                    decoded.push(res?);
                }
                Ok(decoded)
            })?
        } else {
            let mut decoded = Vec::with_capacity(col_tasks.len());
            for &(col, se, meta) in &col_tasks {
                decoded.push(decode_column_chunk_typed(
                    bytes,
                    footer_start,
                    meta,
                    col,
                    se,
                    rg_rows,
                )?);
            }
            decoded
        };

        // Vectorized schema `where` validation preserving exact earliest 1-based `(row, col)` error!
        let mut earliest_fail: Option<(usize, usize)> = None;
        for (ci, col_data) in rg_cols.iter().enumerate() {
            let fc = fast_constraints
                .get(ci)
                .unwrap_or(&FastColConstraint::AlwaysTrue);
            if fc.is_always_true() {
                continue;
            }
            let limit = earliest_fail.map_or(rg_rows, |(r, _)| r);
            if let Some(bad_r) =
                fc.find_first_violation(col_data, limit, |v| fallback_constraint(ci, v))
            {
                earliest_fail = Some((bad_r, ci));
            }
        }
        if let Some((bad_r, bad_ci)) = earliest_fail {
            return Err(format!(
                "Parquet row {} column `{}` failed schema `where` constraint",
                global_row_offset + bad_r + 1,
                schema.cols[bad_ci].name
            ));
        }

        // Slice row group columns into `chunk_size` (2,048-row) VM batches.
        if rg_rows <= chunk_size {
            all_batches.push(Batch {
                cols: rg_cols,
                len: rg_rows,
                selection: None,
                group_meta: None,
            });
        } else {
            let mut offset = 0usize;
            while offset < rg_rows {
                let take = (rg_rows - offset).min(chunk_size);
                let batch_cols = rg_cols.iter().map(|c| c.slice(offset, take)).collect();
                all_batches.push(Batch {
                    cols: batch_cols,
                    len: take,
                    selection: None,
                    group_meta: None,
                });
                offset += take;
            }
        }
        global_row_offset += rg_rows;
    }

    Ok(VmTable {
        cols: schema.cols.clone(),
        batches: all_batches,
    })
}

fn infer_vm_col_scalar_ty(tbl: &VmTable, col_idx: usize) -> ScalarTy {
    let mut saw_nullable = false;
    let mut base: Option<ScalarTy> = None;
    for b in &tbl.batches {
        if b.is_empty() {
            continue;
        }
        let Some(col) = b.cols.get(col_idx) else {
            continue;
        };
        if col.validity.is_some() {
            saw_nullable = true;
        }
        if base.is_none() {
            base = match &col.data {
                ColumnData::Bool(_) => Some(ScalarTy::Bool),
                ColumnData::Int(_) => Some(ScalarTy::Int),
                ColumnData::Decimal(_) => Some(ScalarTy::Decimal),
                ColumnData::Float(_) => Some(ScalarTy::Float),
                ColumnData::Text { .. } => Some(ScalarTy::Text),
                ColumnData::Bytes { .. } => Some(ScalarTy::Bytes),
                ColumnData::Date(_) => Some(ScalarTy::Date),
                ColumnData::Timestamp(_) => Some(ScalarTy::Timestamp),
                ColumnData::Duration(_) => Some(ScalarTy::Duration),
                ColumnData::Generic(vs) => {
                    let mut inner = None;
                    for r_u16 in b.active_indices() {
                        match &vs[usize::from(r_u16)] {
                            Val::OptNone => saw_nullable = true,
                            Val::OptSome(v) => {
                                saw_nullable = true;
                                if inner.is_none() {
                                    inner = scalar_ty_from_val(v);
                                }
                            }
                            other => {
                                if inner.is_none() {
                                    inner = scalar_ty_from_val(other);
                                }
                            }
                        }
                    }
                    inner
                }
                ColumnData::Unit(_) => None,
            };
        }
    }
    let ty = base.unwrap_or(ScalarTy::Text);
    if saw_nullable {
        ScalarTy::Option(Box::new(ty))
    } else {
        ty
    }
}

/// Slice reference into a `VmTable` batch covering `active_start..active_start + count` active rows.
#[derive(Clone, Copy)]
struct BatchRowSlice<'a> {
    batch: &'a Batch,
    active_start: usize,
    count: usize,
}

fn encode_plain_column_vm(
    col: &ColSpec,
    slices: &[BatchRowSlice<'_>],
    col_idx: usize,
    total_rows: usize,
) -> Result<(Vec<u8>, Option<Vec<u32>>), String> {
    let (inner_ty, is_opt) = peel_option(&col.ty);
    let mut def_levels = if is_opt {
        Some(Vec::with_capacity(total_rows))
    } else {
        None
    };

    let init_cap = match inner_ty {
        ScalarTy::Bool => total_rows.div_ceil(8),
        ScalarTy::Date => total_rows.saturating_mul(4),
        ScalarTy::Int | ScalarTy::Float | ScalarTy::Timestamp | ScalarTy::Duration => {
            total_rows.saturating_mul(8)
        }
        ScalarTy::Decimal => total_rows.saturating_mul(16),
        _ => total_rows.saturating_mul(8),
    };
    let mut out = Vec::with_capacity(init_cap);

    // State for LSB-first packed BOOLEAN encoding across batch slices.
    let mut bool_byte = 0u8;
    let mut bool_bit = 0u8;

    for sl in slices {
        let c = sl
            .batch
            .cols
            .get(col_idx)
            .ok_or_else(|| format!("batch missing column `{}`", col.name))?;
        let sel_opt = sl.batch.selection.as_deref();
        let validity = c.validity.as_ref();

        // Fast contiguous bulk path when `selection` is `None` and `validity` is `None`!
        if sel_opt.is_none() && validity.is_none() {
            let start = sl.active_start;
            let end = start + sl.count;
            if let Some(dl) = def_levels.as_mut()
                && !matches!(c.data, ColumnData::Generic(_))
            {
                dl.resize(dl.len() + sl.count, 1);
            }
            match (inner_ty, &c.data) {
                (ScalarTy::Bool, ColumnData::Bool(vs)) => {
                    for &b in &vs[start..end] {
                        if b != 0 {
                            bool_byte |= 1u8 << bool_bit;
                        }
                        bool_bit += 1;
                        if bool_bit == 8 {
                            out.push(bool_byte);
                            bool_byte = 0;
                            bool_bit = 0;
                        }
                    }
                    continue;
                }
                (ScalarTy::Int, ColumnData::Int(vs))
                | (ScalarTy::Timestamp, ColumnData::Timestamp(vs))
                | (ScalarTy::Duration, ColumnData::Duration(vs)) => {
                    for &n in &vs[start..end] {
                        out.extend_from_slice(&n.to_le_bytes());
                    }
                    continue;
                }
                (ScalarTy::Float, ColumnData::Float(vs)) => {
                    for &bits in &vs[start..end] {
                        out.extend_from_slice(&bits.to_le_bytes());
                    }
                    continue;
                }
                (ScalarTy::Decimal, ColumnData::Decimal(vs)) => {
                    for &d in &vs[start..end] {
                        out.extend_from_slice(&d.to_be_bytes());
                    }
                    continue;
                }
                (ScalarTy::Date, ColumnData::Date(vs)) => {
                    for &d in &vs[start..end] {
                        let days = i32::try_from(d).map_err(|_| {
                            format!("Date out of i32 range in column `{}`", col.name)
                        })?;
                        out.extend_from_slice(&days.to_le_bytes());
                    }
                    continue;
                }
                (ScalarTy::Text, ColumnData::Text { offsets, data })
                | (ScalarTy::Bytes, ColumnData::Bytes { offsets, data }) => {
                    for r in start..end {
                        let slice = &data[offsets[r]..offsets[r + 1]];
                        let len = u32::try_from(slice.len()).map_err(|_| {
                            format!("variable-length value exceeds u32 in column `{}`", col.name)
                        })?;
                        out.extend_from_slice(&len.to_le_bytes());
                        out.extend_from_slice(slice);
                    }
                    continue;
                }
                _ => {}
            }
        }

        // General per-active-row path (handles selection vectors, nulls, and `Generic` columns).
        for pos in sl.active_start..sl.active_start + sl.count {
            let r = match sel_opt {
                Some(sel) => usize::from(sel[pos]),
                None => pos,
            };
            if let Some(bm) = validity {
                if !bm.is_valid(r) {
                    if let Some(dl) = def_levels.as_mut() {
                        dl.push(0);
                        continue;
                    }
                    return Err(format!(
                        "unexpected null value in required Parquet column `{}`",
                        col.name
                    ));
                }
                if let Some(dl) = def_levels.as_mut() {
                    dl.push(1);
                }
            } else if !matches!(c.data, ColumnData::Generic(_))
                && let Some(dl) = def_levels.as_mut()
            {
                dl.push(1);
            }

            match (inner_ty, &c.data) {
                (ScalarTy::Bool, ColumnData::Bool(vs)) => {
                    if vs[r] != 0 {
                        bool_byte |= 1u8 << bool_bit;
                    }
                    bool_bit += 1;
                    if bool_bit == 8 {
                        out.push(bool_byte);
                        bool_byte = 0;
                        bool_bit = 0;
                    }
                }
                (ScalarTy::Int, ColumnData::Int(vs))
                | (ScalarTy::Timestamp, ColumnData::Timestamp(vs))
                | (ScalarTy::Duration, ColumnData::Duration(vs)) => {
                    out.extend_from_slice(&vs[r].to_le_bytes());
                }
                (ScalarTy::Float, ColumnData::Float(vs)) => {
                    out.extend_from_slice(&vs[r].to_le_bytes());
                }
                (ScalarTy::Decimal, ColumnData::Decimal(vs)) => {
                    out.extend_from_slice(&vs[r].to_be_bytes());
                }
                (ScalarTy::Date, ColumnData::Date(vs)) => {
                    let days = i32::try_from(vs[r])
                        .map_err(|_| format!("Date out of i32 range in column `{}`", col.name))?;
                    out.extend_from_slice(&days.to_le_bytes());
                }
                (ScalarTy::Text, ColumnData::Text { offsets, data })
                | (ScalarTy::Bytes, ColumnData::Bytes { offsets, data }) => {
                    let slice = &data[offsets[r]..offsets[r + 1]];
                    let len = u32::try_from(slice.len()).map_err(|_| {
                        format!("variable-length value exceeds u32 in column `{}`", col.name)
                    })?;
                    out.extend_from_slice(&len.to_le_bytes());
                    out.extend_from_slice(slice);
                }
                (_, ColumnData::Generic(vs)) => {
                    let cell = &vs[r];
                    let inner_v = if is_opt {
                        match cell {
                            Val::OptNone => {
                                if let Some(dl) = def_levels.as_mut() {
                                    dl.push(0);
                                }
                                continue;
                            }
                            Val::OptSome(inner) => {
                                if let Some(dl) = def_levels.as_mut() {
                                    dl.push(1);
                                }
                                inner.as_ref()
                            }
                            other => {
                                if let Some(dl) = def_levels.as_mut() {
                                    dl.push(1);
                                }
                                other
                            }
                        }
                    } else {
                        match cell {
                            Val::OptSome(inner) => inner.as_ref(),
                            Val::OptNone => {
                                return Err(format!(
                                    "unexpected null value in required Parquet column `{}`",
                                    col.name
                                ));
                            }
                            other => other,
                        }
                    };
                    encode_single_val_plain(
                        inner_ty,
                        inner_v,
                        &col.name,
                        &mut out,
                        &mut bool_byte,
                        &mut bool_bit,
                    )?;
                }
                _ => {
                    return Err(format!(
                        "mismatched columnar buffer for Parquet column `{}` (expected `{inner_ty:?}`)",
                        col.name
                    ));
                }
            }
        }
    }

    if *inner_ty == ScalarTy::Bool && bool_bit > 0 {
        out.push(bool_byte);
    }

    Ok((out, def_levels))
}

fn encode_single_val_plain(
    inner_ty: &ScalarTy,
    v: &Val,
    col_name: &str,
    out: &mut Vec<u8>,
    bool_byte: &mut u8,
    bool_bit: &mut u8,
) -> Result<(), String> {
    match (inner_ty, v) {
        (ScalarTy::Bool, Val::Bool(b)) => {
            if *b {
                *bool_byte |= 1u8 << *bool_bit;
            }
            *bool_bit += 1;
            if *bool_bit == 8 {
                out.push(*bool_byte);
                *bool_byte = 0;
                *bool_bit = 0;
            }
        }
        (ScalarTy::Int, Val::Int(n)) => {
            let i = n
                .to_i64()
                .ok_or_else(|| format!("Int out of i64 range in column `{col_name}`"))?;
            out.extend_from_slice(&i.to_le_bytes());
        }
        (ScalarTy::Float, Val::Float(f)) => {
            out.extend_from_slice(&f.to_f64().to_le_bytes());
        }
        (ScalarTy::Decimal, Val::Decimal(d)) => {
            let scaled = d
                .to_i128()
                .ok_or_else(|| format!("Decimal out of i128 range in column `{col_name}`"))?;
            out.extend_from_slice(&scaled.to_be_bytes());
        }
        (ScalarTy::Text, Val::Text(s)) => {
            let len = u32::try_from(s.len())
                .map_err(|_| format!("Text value exceeds u32 in column `{col_name}`"))?;
            out.extend_from_slice(&len.to_le_bytes());
            out.extend_from_slice(s.as_bytes());
        }
        (ScalarTy::Bytes, Val::Bytes(bs)) => {
            let len = u32::try_from(bs.len())
                .map_err(|_| format!("Bytes value exceeds u32 in column `{col_name}`"))?;
            out.extend_from_slice(&len.to_le_bytes());
            out.extend_from_slice(bs);
        }
        (ScalarTy::Date, Val::Date(d)) => {
            let days = d
                .to_i64()
                .and_then(|x| i32::try_from(x).ok())
                .ok_or_else(|| format!("Date out of i32 range in column `{col_name}`"))?;
            out.extend_from_slice(&days.to_le_bytes());
        }
        (ScalarTy::Timestamp, Val::Timestamp(ts)) => {
            let us = ts
                .to_i64()
                .ok_or_else(|| format!("Timestamp out of i64 range in column `{col_name}`"))?;
            out.extend_from_slice(&us.to_le_bytes());
        }
        (ScalarTy::Duration, Val::Duration(dur)) => {
            let us = dur
                .to_i64()
                .ok_or_else(|| format!("Duration out of i64 range in column `{col_name}`"))?;
            out.extend_from_slice(&us.to_le_bytes());
        }
        _ => {
            return Err(format!(
                "expected `{inner_ty:?}` in Parquet column `{col_name}`"
            ));
        }
    }
    Ok(())
}

struct EncodedParquetColPage {
    phys_type: i32,
    col_name: String,
    encodings: Vec<i32>,
    hdr_bytes: Vec<u8>,
    compressed_page: Vec<u8>,
    uncompressed_page_len: usize,
}

fn encode_vm_col_page(
    col: &ColSpec,
    phys_type: i32,
    slices: &[BatchRowSlice<'_>],
    ci: usize,
    rg_num_rows: usize,
    rg_num_rows_i32: i32,
    compression: ParquetCompression,
) -> Result<EncodedParquetColPage, String> {
    let (plain_bytes, def_levels_opt) = encode_plain_column_vm(col, slices, ci, rg_num_rows)?;
    let mut encodings = Vec::with_capacity(2);
    let uncompressed_page = if let Some(def_levels) = def_levels_opt {
        let rle = encode_rle_hybrid(&def_levels, 1);
        let rle_len = u32::try_from(rle.len())
            .map_err(|_| "Parquet definition levels exceed u32".to_string())?;
        let mut page = Vec::with_capacity(4 + rle.len() + plain_bytes.len());
        page.extend_from_slice(&rle_len.to_le_bytes());
        page.extend_from_slice(&rle);
        page.extend_from_slice(&plain_bytes);
        encodings.push(ENC_RLE);
        encodings.push(ENC_PLAIN);
        page
    } else {
        encodings.push(ENC_PLAIN);
        plain_bytes
    };

    let compressed_page = compress_page_bytes(&uncompressed_page, compression)?;
    let uncomp_sz = i32::try_from(uncompressed_page.len())
        .map_err(|_| "Parquet uncompressed page exceeds i32".to_string())?;
    let comp_sz = i32::try_from(compressed_page.len())
        .map_err(|_| "Parquet compressed page exceeds i32".to_string())?;

    let page_hdr = PageHeader {
        page_type: PAGE_DATA_V1,
        uncompressed_page_size: uncomp_sz,
        compressed_page_size: comp_sz,
        data_page_header: Some(DataPageHeader {
            num_values: rg_num_rows_i32,
            encoding: ENC_PLAIN,
            definition_level_encoding: ENC_RLE,
            repetition_level_encoding: ENC_RLE,
        }),
        dictionary_page_header: None,
        data_page_header_v2: None,
    };
    let mut hdr_w = ThriftWriter::new();
    write_page_header(&mut hdr_w, &page_hdr);
    let hdr_bytes = hdr_w.into_bytes();

    Ok(EncodedParquetColPage {
        phys_type,
        col_name: col.name.clone(),
        encodings,
        hdr_bytes,
        compressed_page,
        uncompressed_page_len: uncompressed_page.len(),
    })
}

/// Encode a columnar [`VmTable`] directly into Apache Parquet binary bytes using default options
/// (`Zstd`, 65,536-row groups) without ever converting to row-wise [`TableVal`].
///
/// # Errors
/// Returns an error string on unsupported column types, out-of-range values, or compression errors.
pub fn write_parquet_vm_table_bytes(
    tbl: &VmTable,
    compression: ParquetCompression,
) -> Result<Vec<u8>, String> {
    write_parquet_vm_table_bytes_with_options(
        tbl,
        ParquetWriteOptions {
            compression,
            row_group_rows: DEFAULT_ROW_GROUP_ROWS,
        },
    )
}

/// Encode a columnar [`VmTable`] directly into Apache Parquet binary bytes with explicit
/// [`ParquetWriteOptions`].
///
/// # Errors
/// Returns an error string on invalid options, unsupported column types, or compression errors.
pub fn write_parquet_vm_table_bytes_with_options(
    tbl: &VmTable,
    opts: ParquetWriteOptions,
) -> Result<Vec<u8>, String> {
    if opts.row_group_rows == 0 {
        return Err("Parquet row_group_rows must be positive".to_string());
    }

    let resolved_cols: Vec<ColSpec> = tbl
        .cols
        .iter()
        .enumerate()
        .map(|(ci, c)| {
            if c.ty == ScalarTy::Unit {
                let mut cloned = c.clone();
                cloned.ty = infer_vm_col_scalar_ty(tbl, ci);
                cloned
            } else {
                c.clone()
            }
        })
        .collect();

    let mut schema_elems = Vec::with_capacity(1 + resolved_cols.len());
    schema_elems.push(SchemaElement {
        phys_type: None,
        type_length: None,
        repetition_type: None,
        name: "dana_schema".to_string(),
        num_children: Some(
            i32::try_from(resolved_cols.len())
                .map_err(|_| "Parquet column count overflow".to_string())?,
        ),
        converted_type: None,
        scale: None,
        precision: None,
        logical_type: None,
    });
    let mut phys_types = Vec::with_capacity(resolved_cols.len());
    for col in &resolved_cols {
        let se = schema_element_for_col(col)?;
        let pt = se
            .phys_type
            .ok_or_else(|| "missing physical type for Parquet leaf".to_string())?;
        phys_types.push(pt);
        schema_elems.push(se);
    }

    let total_rows = tbl.total_rows();
    let mut out = Vec::new();
    out.extend_from_slice(PARQUET_MAGIC);

    // Partition active batch rows into row groups of `opts.row_group_rows` without copying rows.
    let mut rg_plans: Vec<(usize, Vec<BatchRowSlice<'_>>)> = Vec::new();
    let mut cur_slices: Vec<BatchRowSlice<'_>> = Vec::new();
    let mut cur_rows = 0usize;
    for b in &tbl.batches {
        let active = b.active_len();
        if active == 0 {
            continue;
        }
        let mut pos = 0usize;
        while pos < active {
            let room = opts.row_group_rows - cur_rows;
            let take = (active - pos).min(room);
            cur_slices.push(BatchRowSlice {
                batch: b,
                active_start: pos,
                count: take,
            });
            cur_rows += take;
            pos += take;
            if cur_rows >= opts.row_group_rows {
                rg_plans.push((cur_rows, std::mem::take(&mut cur_slices)));
                cur_rows = 0;
            }
        }
    }
    if cur_rows > 0 {
        rg_plans.push((cur_rows, cur_slices));
    }

    let mut row_groups = Vec::with_capacity(rg_plans.len());
    for (rg_num_rows, slices) in &rg_plans {
        let rg_num_rows = *rg_num_rows;
        let rg_num_rows_i32 = i32::try_from(rg_num_rows)
            .map_err(|_| "Parquet row group size exceeds i32".to_string())?;

        let encoded_cols: Vec<EncodedParquetColPage> =
            if rg_num_rows >= 8_192 && resolved_cols.len() >= 2 {
                std::thread::scope(|scope| -> Result<Vec<EncodedParquetColPage>, String> {
                    let mut handles = Vec::with_capacity(resolved_cols.len());
                    for (ci, col) in resolved_cols.iter().enumerate() {
                        let pt = phys_types[ci];
                        let sl_ref: &[BatchRowSlice<'_>] = slices;
                        handles.push(scope.spawn(move || {
                            encode_vm_col_page(
                                col,
                                pt,
                                sl_ref,
                                ci,
                                rg_num_rows,
                                rg_num_rows_i32,
                                opts.compression,
                            )
                        }));
                    }
                    let mut pages = Vec::with_capacity(resolved_cols.len());
                    for h in handles {
                        let res = h
                            .join()
                            .map_err(|_| "Parquet column encode worker panicked".to_string())?;
                        pages.push(res?);
                    }
                    Ok(pages)
                })?
            } else {
                let mut pages = Vec::with_capacity(resolved_cols.len());
                for (ci, col) in resolved_cols.iter().enumerate() {
                    pages.push(encode_vm_col_page(
                        col,
                        phys_types[ci],
                        slices,
                        ci,
                        rg_num_rows,
                        rg_num_rows_i32,
                        opts.compression,
                    )?);
                }
                pages
            };

        let mut columns = Vec::with_capacity(encoded_cols.len());
        let mut rg_uncompressed_total = 0i64;
        for ep in encoded_cols {
            let data_page_offset = i64::try_from(out.len())
                .map_err(|_| "Parquet file offset exceeds i64".to_string())?;
            out.extend_from_slice(&ep.hdr_bytes);
            out.extend_from_slice(&ep.compressed_page);

            let total_uncomp = i64::try_from(ep.hdr_bytes.len() + ep.uncompressed_page_len)
                .map_err(|_| "Parquet total_uncompressed_size overflow".to_string())?;
            let total_comp = i64::try_from(ep.hdr_bytes.len() + ep.compressed_page.len())
                .map_err(|_| "Parquet total_compressed_size overflow".to_string())?;
            rg_uncompressed_total = rg_uncompressed_total
                .checked_add(total_uncomp)
                .ok_or_else(|| "Parquet row group size overflow".to_string())?;

            columns.push(ColumnChunk {
                file_offset: data_page_offset,
                meta_data: Some(ColumnMetaData {
                    phys_type: ep.phys_type,
                    encodings: ep.encodings,
                    path_in_schema: vec![ep.col_name],
                    codec: opts.compression.to_thrift_codec(),
                    num_values: rg_num_rows as i64,
                    total_uncompressed_size: total_uncomp,
                    total_compressed_size: total_comp,
                    data_page_offset,
                    dictionary_page_offset: None,
                }),
            });
        }

        row_groups.push(RowGroup {
            columns,
            total_byte_size: rg_uncompressed_total,
            num_rows: rg_num_rows as i64,
        });
    }

    let file_meta = FileMetaData {
        version: 1,
        schema: schema_elems,
        num_rows: total_rows as i64,
        row_groups,
        created_by: Some("dana native parquet writer 0.4".to_string()),
    };
    let mut fm_w = ThriftWriter::new();
    write_file_metadata(&mut fm_w, &file_meta);
    let fm_bytes = fm_w.into_bytes();
    let fm_len = u32::try_from(fm_bytes.len())
        .map_err(|_| "Parquet footer metadata exceeds u32".to_string())?;

    out.extend_from_slice(&fm_bytes);
    out.extend_from_slice(&fm_len.to_le_bytes());
    out.extend_from_slice(PARQUET_MAGIC);

    Ok(out)
}
