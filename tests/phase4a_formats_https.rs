#![forbid(unsafe_code)]

//! Phase 4A comprehensive test suite:
//! - Raw RFC 1951 DEFLATE/INFLATE & PKZIP codec (CRC-32, STORED/DEFLATED, path traversal, zip-bomb)
//! - Native Apache Parquet reader & writer (all Dana scalar types, Option nulls, exact 18-digit Decimal,
//!   Uncompressed/Gzip/Zstd, multi-row-group, synthetic RLE_DICTIONARY + SNAPPY + DataPageV2 + rescaled
//!   Decimal/Timestamp/Int32/Float, schema drift & `where` constraints, live `ecommerce-ledger-audit.dana`)
//! - Native Excel `.xlsx` reader & writer (single & multi-sheet, 1900 serial dates & timestamps,
//!   sharedStrings/inlineStr/formula-str/booleans/sparse coordinates, quarantine `bad_rows` with PII tags,
//!   XXE/DTD/zip-bomb/path-traversal rejection, live `donor-reconciliation.dana` + SQLite + 4-sheet report)
//! - Capability-gated HTTPS client (`HttpsAllow` over real loopback OpenSSL TLS with chunked + gzipped
//!   paginated JSON, `parse_table`/`bool_at`/`text_at`/`int_at`, cross-host/plain-HTTP/redirect/untrusted-CA/
//!   `--allow-export` denials, and offline `Https.fake` running `registrar-sync.dana` pagination).

use std::collections::HashMap;
use std::fs;
use std::io::{BufRead, BufReader, Write};
use std::net::TcpListener;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex};
use std::thread;

use dana::base::{DiagCode, SourceMap, render_diagnostic};
use dana::check::{check_module, check_resolved, parse_policy, resolve_path};
use dana::core::bigint::BigInt;
use dana::core::syntax::{AggKind, BugKind, ColSpec, Float64, ScalarTy, TableTy, TagSet};
use dana::db::{SqlParam, open_connection};
use dana::ffi::{GzipWriter, TlsServerAcceptor, raw_deflate, raw_inflate};
use dana::formats::parquet::{
    ParquetCompression, ParquetWriteOptions, read_parquet_bytes_with_schema,
    read_parquet_file_with_schema, snappy_decompress, write_parquet_bytes,
    write_parquet_bytes_with_options, write_parquet_table,
};
use dana::formats::time::{
    days_from_civil, parse_decimal_bigint_strict, parse_iso_date, parse_iso_timestamp,
};
use dana::formats::xlsx::{
    days_to_excel_1900_serial, excel_serial_to_days, excel_serial_to_micros,
    micros_to_excel_1900_serial, read_xlsx_bytes_with_schema, read_xlsx_file_with_schema,
    write_xlsx_file, write_xlsx_sheets,
};
use dana::formats::zip::{ZipArchive, ZipCompression, ZipLimits, crc32, write_zip_bytes};
use dana::lower::lower_program;
use dana::net::{HttpsClientConfig, ParsedHttpsUrl, https_get_json};
use dana::oracle::value::{TableRow, TableVal, Val, val_eq};
use dana::runtime::{RunConfig, RunResult, run_exec_program, run_program_tests};
use dana::syntax::parse_module;
use dana::vm::{VmConfig, run_exec_program_vm, run_program_tests_vm};

type TestResult<T = ()> = Result<T, Box<dyn std::error::Error>>;

static TMP_SEQ: AtomicU64 = AtomicU64::new(1);

struct TempDir {
    path: PathBuf,
}

impl TempDir {
    fn new(prefix: &str) -> TestResult<Self> {
        let n = TMP_SEQ.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "dana_phase4a_{prefix}_{}_{}",
            std::process::id(),
            n
        ));
        if path.exists() {
            fs::remove_dir_all(&path)?;
        }
        fs::create_dir_all(&path)?;
        Ok(Self { path })
    }

    fn path(&self) -> &Path {
        &self.path
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}

fn repo_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

fn col(name: &str, ty: ScalarTy, tags: &[&str]) -> ColSpec {
    ColSpec {
        name: name.to_string(),
        ty,
        tags: TagSet::of_list(tags.iter().map(|s| (*s).to_string()).collect()),
        bucketed: false,
        agg_kind: AggKind::Raw,
    }
}

fn opt(ty: ScalarTy) -> ScalarTy {
    ScalarTy::Option(Box::new(ty))
}

fn table_ty(cols: Vec<ColSpec>) -> TableTy {
    TableTy {
        cols,
        ..TableTy::default()
    }
}

fn assert_tables_eq(actual: &TableVal, expected: &TableVal) {
    assert_eq!(actual.cols.len(), expected.cols.len(), "col count mismatch");
    for (a, b) in actual.cols.iter().zip(&expected.cols) {
        assert_eq!(a.name, b.name);
        assert_eq!(a.ty, b.ty);
    }
    assert_eq!(actual.rows.len(), expected.rows.len(), "row count mismatch");
    for (ri, (ra, rb)) in actual.rows.iter().zip(&expected.rows).enumerate() {
        assert_eq!(ra.cells.len(), rb.cells.len(), "row {ri} cell count");
        for (ci, (ca, cb)) in ra.cells.iter().zip(&rb.cells).enumerate() {
            assert!(
                val_eq(ca, cb),
                "row {ri} col {ci} (`{}`) mismatch: actual={ca:?}, expected={cb:?}",
                expected.cols[ci].name
            );
        }
    }
}

fn compile_source(
    src: &str,
    policy: Option<dana::core::syntax::Policy>,
) -> Result<dana::runtime::ExecProgram, String> {
    let mut sm = SourceMap::new();
    let fid = sm.add_file("test.dana".to_string(), src.to_string());
    let ast = parse_module(fid, src).map_err(|d| render_diagnostic(&d, &sm))?;
    let checked = check_module(fid, ast, policy, &sm).map_err(|ds| {
        ds.iter()
            .map(|d| render_diagnostic(d, &sm))
            .collect::<String>()
    })?;
    let lowered = lower_program(checked).map_err(|d| render_diagnostic(&d, &sm))?;
    Ok(lowered.exec)
}

fn compile_example(
    rel_path: &str,
    with_policy: bool,
) -> Result<dana::runtime::ExecProgram, String> {
    let root = repo_root();
    let mut sm = SourceMap::new();
    let policy = if with_policy {
        let ppath = root.join("examples/dana.policy");
        let psrc = fs::read_to_string(&ppath).map_err(|e| format!("read policy: {e}"))?;
        let pfid = sm.add_file(ppath.display().to_string(), psrc.clone());
        Some(parse_policy(pfid, &psrc).map_err(|d| render_diagnostic(&d, &sm))?)
    } else {
        None
    };
    let path = root.join(rel_path);
    let resolved = resolve_path(&path, policy, &mut sm).map_err(|ds| {
        ds.iter()
            .map(|d| render_diagnostic(d, &sm))
            .collect::<String>()
    })?;
    let checked = check_resolved(&resolved, &sm).map_err(|ds| {
        ds.iter()
            .map(|d| render_diagnostic(d, &sm))
            .collect::<String>()
    })?;
    let lowered = lower_program(checked).map_err(|d| render_diagnostic(&d, &sm))?;
    Ok(lowered.exec)
}

fn generate_self_signed_cert(dir: &Path) -> TestResult<(String, String)> {
    let cert_path = dir.join("server.crt");
    let key_path = dir.join("server.key");
    let cert_str = cert_path.to_string_lossy().into_owned();
    let key_str = key_path.to_string_lossy().into_owned();

    let status = Command::new("openssl")
        .args([
            "req",
            "-x509",
            "-newkey",
            "rsa:2048",
            "-nodes",
            "-keyout",
            &key_str,
            "-out",
            &cert_str,
            "-days",
            "1",
            "-subj",
            "/CN=localhost",
            "-addext",
            "subjectAltName=DNS:localhost,IP:127.0.0.1",
        ])
        .output()?;
    if !status.status.success() {
        return Err(format!(
            "openssl req failed: {}",
            String::from_utf8_lossy(&status.stderr)
        )
        .into());
    }
    Ok((cert_str, key_str))
}

// ===========================================================================
// 1. Raw DEFLATE/INFLATE & PKZIP Codec Tests
// ===========================================================================

#[test]
fn raw_deflate_inflate_roundtrip_and_zip_bomb_cap() -> TestResult {
    // Empty payload
    let empty_def = raw_deflate(&[])?;
    assert_eq!(raw_inflate(&empty_def, 0)?, Vec::<u8>::new());

    // Normal payload
    let payload = b"Dana Phase 4A raw RFC 1951 DEFLATE test payload! ".repeat(500);
    let compressed = raw_deflate(&payload)?;
    assert!(compressed.len() < payload.len() / 10);
    let roundtrip = raw_inflate(&compressed, payload.len())?;
    assert_eq!(roundtrip, payload);

    // Strictly enforce max_output_bytes (even 1 byte under limit must fail!)
    let err = raw_inflate(&compressed, payload.len() - 1);
    assert!(err.is_err(), "raw_inflate must reject output exceeding cap");

    // Truncated stream must fail
    let trunc = raw_inflate(&compressed[..compressed.len() / 2], payload.len());
    assert!(trunc.is_err(), "raw_inflate must reject truncated streams");
    Ok(())
}

#[test]
fn pkzip_crc32_roundtrip_and_security_rejections() -> TestResult {
    // Standard IEEE CRC-32 check value
    assert_eq!(crc32(b"123456789"), 0xCBF4_3926);

    let entries = [
        ("hello.txt", b"Hello PKZIP!".as_slice()),
        ("nested/data.bin", &[0u8, 1, 2, 255, 42, 0, 13, 10]),
        ("empty.txt", b"".as_slice()),
    ];

    for comp in [ZipCompression::Stored, ZipCompression::Deflated] {
        let zip_bytes = write_zip_bytes(&entries, comp)?;
        let archive = ZipArchive::from_bytes(&zip_bytes)?;
        assert_eq!(archive.entries().len(), 3);
        assert_eq!(archive.get("hello.txt"), Some(b"Hello PKZIP!".as_slice()));
        assert_eq!(
            archive.get("nested/data.bin"),
            Some(&[0u8, 1, 2, 255, 42, 0, 13, 10][..])
        );
        assert_eq!(archive.get("empty.txt"), Some(b"".as_slice()));
    }

    // Path traversal rejection on writer
    for bad_name in [
        "../escape.txt",
        "a/../b.txt",
        "/abs/path.txt",
        "win\\path.txt",
    ] {
        let res = write_zip_bytes(&[(bad_name, b"x")], ZipCompression::Stored);
        assert!(res.is_err(), "writer must reject unsafe path `{bad_name}`");
    }

    // Path traversal rejection on reader (craft raw zip bypassing writer check)
    let mut bad_zip = write_zip_bytes(&[("aa/bb.txt", b"hello")], ZipCompression::Stored)?;
    // Replace every occurrence of "aa/bb.txt" with "../bb.txt"
    let needle = b"aa/bb.txt";
    let repl = b"../bb.txt";
    for i in 0..=bad_zip.len() - needle.len() {
        if &bad_zip[i..i + needle.len()] == needle {
            bad_zip[i..i + repl.len()].copy_from_slice(repl);
        }
    }
    let traversal_err = ZipArchive::from_bytes(&bad_zip);
    assert!(
        traversal_err.is_err(),
        "reader must reject `..` path traversal entry"
    );

    // CRC-32 corruption detection
    let mut corrupt_zip = write_zip_bytes(&[("f.txt", b"integrity")], ZipCompression::Stored)?;
    // Flip a byte inside the payload ("integrity")
    let pos = corrupt_zip
        .windows(9)
        .position(|w| w == b"integrity")
        .ok_or("payload not found")?;
    corrupt_zip[pos] ^= 0xFF;
    let crc_err = ZipArchive::from_bytes(&corrupt_zip);
    assert!(crc_err.is_err(), "reader must detect CRC-32 corruption");

    // Zip-bomb cap rejection
    let big = vec![b'A'; 200_000];
    let bomb_zip = write_zip_bytes(&[("bomb.txt", &big)], ZipCompression::Deflated)?;
    let bomb_err = ZipArchive::from_bytes_with_limits(
        &bomb_zip,
        ZipLimits {
            max_entry_bytes: 10_000,
            max_total_bytes: 10_000,
            max_entries: 100,
        },
    );
    assert!(
        bomb_err.is_err(),
        "reader must reject zip bomb exceeding cap"
    );
    Ok(())
}

// ===========================================================================
// 2. Native Apache Parquet Tests
// ===========================================================================

#[test]
fn parquet_roundtrip_all_scalar_types_nulls_decimal_and_codecs() -> TestResult {
    let schema = table_ty(vec![
        col("b", ScalarTy::Bool, &[]),
        col("b_opt", opt(ScalarTy::Bool), &[]),
        col("i", ScalarTy::Int, &[]),
        col("i_opt", opt(ScalarTy::Int), &[]),
        col("f", ScalarTy::Float, &[]),
        col("f_opt", opt(ScalarTy::Float), &[]),
        col("dec", ScalarTy::Decimal, &["financial"]),
        col("dec_opt", opt(ScalarTy::Decimal), &[]),
        col("txt", ScalarTy::Text, &[]),
        col("txt_opt", opt(ScalarTy::Text), &[]),
        col("raw", ScalarTy::Bytes, &[]),
        col("dt", ScalarTy::Date, &[]),
        col("ts", ScalarTy::Timestamp, &[]),
        col("dur", ScalarTy::Duration, &[]),
    ]);

    let d1 = parse_decimal_bigint_strict("123456789012345.123456789012345678")?;
    let d2 = parse_decimal_bigint_strict("-0.000000000000000001")?;
    let d3 = parse_decimal_bigint_strict("0.00")?;
    let d4 = parse_decimal_bigint_strict("999999999999999999.500000000000000005")?;

    let expected = TableVal {
        cols: schema.cols.clone(),
        rows: vec![
            TableRow {
                cells: vec![
                    Val::Bool(true),
                    Val::OptSome(Box::new(Val::Bool(false))),
                    Val::Int(BigInt::from(i64::MAX)),
                    Val::OptSome(Box::new(Val::Int(BigInt::from(-42i64)))),
                    Val::Float(Float64::from_f64(std::f64::consts::PI)),
                    Val::OptNone,
                    Val::Decimal(d1.clone()),
                    Val::OptSome(Box::new(Val::Decimal(d2.clone()))),
                    Val::Text("hello, 世界! \n\t\"quotes\"".to_string()),
                    Val::OptNone,
                    Val::Bytes(vec![0x00, 0xDE, 0xAD, 0xBE, 0xEF]),
                    Val::Date(BigInt::from(parse_iso_date("2026-10-01")?)),
                    Val::Timestamp(BigInt::from(parse_iso_timestamp(
                        "2026-10-01T12:34:56.123456Z",
                    )?)),
                    Val::Duration(BigInt::from(3_600_000_000i64)),
                ],
                group_meta: None,
            },
            TableRow {
                cells: vec![
                    Val::Bool(false),
                    Val::OptNone,
                    Val::Int(BigInt::from(i64::MIN)),
                    Val::OptNone,
                    Val::Float(Float64::from_f64(-0.125)),
                    Val::OptSome(Box::new(Val::Float(Float64::from_f64(2.5)))),
                    Val::Decimal(d2.clone()),
                    Val::OptNone,
                    Val::Text(String::new()),
                    Val::OptSome(Box::new(Val::Text("present".to_string()))),
                    Val::Bytes(Vec::new()),
                    Val::Date(BigInt::from(parse_iso_date("1969-12-31")?)),
                    Val::Timestamp(BigInt::from(parse_iso_timestamp("1970-01-01T00:00:00Z")?)),
                    Val::Duration(BigInt::from(-1_500_000i64)),
                ],
                group_meta: None,
            },
            TableRow {
                cells: vec![
                    Val::Bool(true),
                    Val::OptSome(Box::new(Val::Bool(true))),
                    Val::Int(BigInt::from(0i64)),
                    Val::OptSome(Box::new(Val::Int(BigInt::from(7i64)))),
                    Val::Float(Float64::from_f64(0.0)),
                    Val::OptSome(Box::new(Val::Float(Float64::from_f64(-99.75)))),
                    Val::Decimal(d3),
                    Val::OptSome(Box::new(Val::Decimal(d4))),
                    Val::Text("row-3".to_string()),
                    Val::OptSome(Box::new(Val::Text("ok".to_string()))),
                    Val::Bytes(vec![42]),
                    Val::Date(BigInt::from(parse_iso_date("2000-02-29")?)),
                    Val::Timestamp(BigInt::from(parse_iso_timestamp(
                        "2035-06-15T23:59:59.999999Z",
                    )?)),
                    Val::Duration(BigInt::from(0i64)),
                ],
                group_meta: None,
            },
        ],
    };

    // Test Uncompressed, Gzip, Zstd + multi-row-group (2 rows per row group)
    for codec in [
        ParquetCompression::Uncompressed,
        ParquetCompression::Gzip,
        ParquetCompression::Zstd,
    ] {
        let bytes = write_parquet_bytes(&expected, codec)?;
        assert_eq!(&bytes[..4], b"PAR1");
        assert_eq!(&bytes[bytes.len() - 4..], b"PAR1");
        let decoded = read_parquet_bytes_with_schema(&bytes, &schema, |_, _| true)?;
        assert_tables_eq(&decoded, &expected);

        let multi_rg = write_parquet_bytes_with_options(
            &expected,
            ParquetWriteOptions {
                compression: codec,
                row_group_rows: 2,
            },
        )?;
        let decoded_rg = read_parquet_bytes_with_schema(&multi_rg, &schema, |_, _| true)?;
        assert_tables_eq(&decoded_rg, &expected);
    }

    // Empty table round-trip
    let empty_tv = TableVal {
        cols: schema.cols.clone(),
        rows: Vec::new(),
    };
    let empty_bytes = write_parquet_bytes(&empty_tv, ParquetCompression::Zstd)?;
    let empty_dec = read_parquet_bytes_with_schema(&empty_bytes, &schema, |_, _| true)?;
    assert_tables_eq(&empty_dec, &empty_tv);

    // Schema drift checks
    let missing_col_schema = table_ty(vec![col("nonexistent", ScalarTy::Int, &[])]);
    let valid_bytes = write_parquet_bytes(&expected, ParquetCompression::Zstd)?;
    assert!(
        read_parquet_bytes_with_schema(&valid_bytes, &missing_col_schema, |_, _| true).is_err()
    );

    let wrong_ty_schema = table_ty(vec![col("i", ScalarTy::Text, &[])]);
    assert!(read_parquet_bytes_with_schema(&valid_bytes, &wrong_ty_schema, |_, _| true).is_err());

    // Nullability drift: `i_opt` has a NULL in row 1, reading it as required `Int` MUST fail
    let non_null_schema = table_ty(vec![col("i_opt", ScalarTy::Int, &[])]);
    assert!(read_parquet_bytes_with_schema(&valid_bytes, &non_null_schema, |_, _| true).is_err());

    // `where` constraint enforcement: fail when dec < 0
    let constraint_res = read_parquet_bytes_with_schema(&valid_bytes, &schema, |ci, val| {
        if ci == 6
            && let Val::Decimal(d) = val
        {
            return !d.is_negative();
        }
        true
    });
    assert!(
        constraint_res.is_err(),
        "negative decimal must fail schema `where` constraint"
    );
    Ok(())
}

/// Minimal Snappy block encoder emitting both literals and overlapping RLE back-reference copies,
/// used to construct a genuine synthetic `SNAPPY` + `RLE_DICTIONARY` Parquet file for decoder tests.
fn test_snappy_encode(raw: &[u8]) -> Vec<u8> {
    fn push_varint(out: &mut Vec<u8>, mut v: usize) {
        loop {
            let b = (v & 0x7F) as u8;
            v >>= 7;
            if v == 0 {
                out.push(b);
                break;
            }
            out.push(b | 0x80);
        }
    }
    fn push_literal(out: &mut Vec<u8>, lit: &[u8]) {
        if lit.is_empty() {
            return;
        }
        let n = lit.len() - 1;
        if n < 60 {
            out.push((n as u8) << 2);
        } else if n < 256 {
            out.push(60u8 << 2);
            out.push(n as u8);
        } else {
            out.push(61u8 << 2);
            out.extend_from_slice(&(n as u16).to_le_bytes());
        }
        out.extend_from_slice(lit);
    }

    let mut out = Vec::new();
    push_varint(&mut out, raw.len());
    // Emit a literal + 2-byte copy back-reference when repeating pattern exists
    if raw.len() >= 12 && raw[..4] == raw[4..8] {
        push_literal(&mut out, &raw[..4]);
        // Copy 4 bytes from offset 4 using 2-byte offset tag (`((len-1) << 2) | 2`)
        out.push(((4u8 - 1) << 2) | 2);
        out.extend_from_slice(&4u16.to_le_bytes());
        push_literal(&mut out, &raw[8..]);
    } else {
        push_literal(&mut out, raw);
    }
    out
}

#[test]
fn parquet_synthetic_rle_dictionary_snappy_and_type_conversions() -> TestResult {
    // 1. Direct Snappy overlapping RLE copy verification (e.g. "AB" + copy offset=2 len=6 -> "ABABABAB")
    let mut snappy_rle = Vec::new();
    snappy_rle.push(8u8); // uncompressed length = 8
    snappy_rle.push((1u8) << 2); // literal len = 2
    snappy_rle.extend_from_slice(b"AB");
    // 1-byte offset copy: len=6 -> (len-4)=2 -> bits 4..2 = 2, offset=2 -> tag = (2<<2)|1 = 9, next=2
    snappy_rle.push(((6u8 - 4) << 2) | 1);
    snappy_rle.push(2u8);
    assert_eq!(snappy_decompress(&snappy_rle, 16)?, b"ABABABAB");

    // 2. Build a genuine Parquet binary with:
    //    - Col 0 (`dept`: Text, OPTIONAL, RLE_DICTIONARY + SNAPPY, DataPageV1)
    //    - Col 1 (`amount`: Decimal(10, 2) stored as INT64, REQUIRED, PLAIN + SNAPPY, DataPageV2!)
    //    - Col 2 (`ts`: Timestamp MILLIS stored as INT64, REQUIRED, PLAIN + UNCOMPRESSED)
    //    - Col 3 (`count`: INT32, REQUIRED, PLAIN + UNCOMPRESSED)
    //    - Col 4 (`score`: FLOAT, REQUIRED, PLAIN + UNCOMPRESSED)
    let mut w = Vec::<u8>::new();
    w.extend_from_slice(b"PAR1");

    // Helper Thrift Compact writer closures for synthetic Parquet construction
    fn t_uvarint(buf: &mut Vec<u8>, mut v: u64) {
        loop {
            let b = (v & 0x7F) as u8;
            v >>= 7;
            if v == 0 {
                buf.push(b);
                break;
            }
            buf.push(b | 0x80);
        }
    }
    fn t_zz32(buf: &mut Vec<u8>, v: i32) {
        t_uvarint(buf, u64::from(((v << 1) ^ (v >> 31)) as u32));
    }
    fn t_zz64(buf: &mut Vec<u8>, v: i64) {
        t_uvarint(buf, ((v << 1) ^ (v >> 63)) as u64);
    }
    fn t_fhdr(buf: &mut Vec<u8>, last: &mut i16, fid: i16, ct: u8) {
        let d = fid - *last;
        if (1..=15).contains(&d) {
            buf.push(((d as u8) << 4) | ct);
        } else {
            buf.push(ct);
            t_zz32(buf, i32::from(fid));
        }
        *last = fid;
    }
    fn t_str(buf: &mut Vec<u8>, s: &str) {
        t_uvarint(buf, s.len() as u64);
        buf.extend_from_slice(s.as_bytes());
    }
    fn t_list(buf: &mut Vec<u8>, et: u8, n: usize) {
        if n < 15 {
            buf.push(((n as u8) << 4) | et);
        } else {
            buf.push(0xF0 | et);
            t_uvarint(buf, n as u64);
        }
    }

    // --- Col 0 (`dept`, OPTIONAL, DICTIONARY_PAGE + RLE_DICTIONARY DATA_PAGE, SNAPPY) ---
    // 5 rows: ["ENG", None, "OPS", "ENG", "ENG"]
    let mut dict_plain = Vec::new();
    for s in ["ENG", "OPS"] {
        dict_plain.extend_from_slice(&(s.len() as u32).to_le_bytes());
        dict_plain.extend_from_slice(s.as_bytes());
    }
    let dict_snappy = test_snappy_encode(&dict_plain);
    let col0_dict_off = w.len() as i64;
    let mut ph0_dict = Vec::new();
    {
        let mut last = 0i16;
        t_fhdr(&mut ph0_dict, &mut last, 1, 5);
        t_zz32(&mut ph0_dict, 2); // DICTIONARY_PAGE
        t_fhdr(&mut ph0_dict, &mut last, 2, 5);
        t_zz32(&mut ph0_dict, dict_plain.len() as i32);
        t_fhdr(&mut ph0_dict, &mut last, 3, 5);
        t_zz32(&mut ph0_dict, dict_snappy.len() as i32);
        t_fhdr(&mut ph0_dict, &mut last, 7, 12); // DictionaryPageHeader
        let mut dl = 0i16;
        t_fhdr(&mut ph0_dict, &mut dl, 1, 5);
        t_zz32(&mut ph0_dict, 2); // num_values
        t_fhdr(&mut ph0_dict, &mut dl, 2, 5);
        t_zz32(&mut ph0_dict, 0); // PLAIN
        ph0_dict.push(0);
        ph0_dict.push(0);
    }
    w.extend_from_slice(&ph0_dict);
    w.extend_from_slice(&dict_snappy);

    // DataPageV1 for Col 0: def_levels = [1, 0, 1, 1, 1], indices = [0, 1, 0, 0]
    let col0_data_off = w.len() as i64;
    // Def levels bit-packed group of 8 (bit_width = 1): 0b0001_1101 = 0x1D
    let def_rle = vec![(1u8 << 1) | 1, 0b0001_1101];
    // Dictionary indices: bit_width = 1, bit-packed group of 8: [0, 1, 0, 0, ...] = 0b0000_0010 = 0x02
    let dict_indices = vec![1u8, (1u8 << 1) | 1, 0b0000_0010];
    let mut page0_uncomp = Vec::new();
    page0_uncomp.extend_from_slice(&(def_rle.len() as u32).to_le_bytes());
    page0_uncomp.extend_from_slice(&def_rle);
    page0_uncomp.extend_from_slice(&dict_indices);
    let page0_snappy = test_snappy_encode(&page0_uncomp);
    let mut ph0_data = Vec::new();
    {
        let mut last = 0i16;
        t_fhdr(&mut ph0_data, &mut last, 1, 5);
        t_zz32(&mut ph0_data, 0); // DATA_PAGE
        t_fhdr(&mut ph0_data, &mut last, 2, 5);
        t_zz32(&mut ph0_data, page0_uncomp.len() as i32);
        t_fhdr(&mut ph0_data, &mut last, 3, 5);
        t_zz32(&mut ph0_data, page0_snappy.len() as i32);
        t_fhdr(&mut ph0_data, &mut last, 5, 12); // DataPageHeader
        let mut dl = 0i16;
        t_fhdr(&mut ph0_data, &mut dl, 1, 5);
        t_zz32(&mut ph0_data, 5); // num_values
        t_fhdr(&mut ph0_data, &mut dl, 2, 5);
        t_zz32(&mut ph0_data, 8); // RLE_DICTIONARY
        t_fhdr(&mut ph0_data, &mut dl, 3, 5);
        t_zz32(&mut ph0_data, 3); // RLE
        t_fhdr(&mut ph0_data, &mut dl, 4, 5);
        t_zz32(&mut ph0_data, 3); // RLE
        ph0_data.push(0);
        ph0_data.push(0);
    }
    w.extend_from_slice(&ph0_data);
    w.extend_from_slice(&page0_snappy);
    let col0_comp_total = (w.len() as i64) - col0_dict_off;
    let col0_uncomp_total =
        (ph0_dict.len() + dict_plain.len() + ph0_data.len() + page0_uncomp.len()) as i64;

    // --- Col 1 (`amount`: Decimal(10, 2) as INT64, DataPageV2 + SNAPPY) ---
    // Values: 12.34, -5.00, 0.01, 100.50, 12.34 -> unscaled i64: [1234, -500, 1, 10050, 1234]
    let col1_off = w.len() as i64;
    let mut col1_plain = Vec::new();
    for v in [1234i64, -500, 1, 10050, 1234] {
        col1_plain.extend_from_slice(&v.to_le_bytes());
    }
    let col1_snappy = test_snappy_encode(&col1_plain);
    let mut ph1 = Vec::new();
    {
        let mut last = 0i16;
        t_fhdr(&mut ph1, &mut last, 1, 5);
        t_zz32(&mut ph1, 3); // DATA_PAGE_V2
        t_fhdr(&mut ph1, &mut last, 2, 5);
        t_zz32(&mut ph1, col1_plain.len() as i32);
        t_fhdr(&mut ph1, &mut last, 3, 5);
        t_zz32(&mut ph1, col1_snappy.len() as i32);
        t_fhdr(&mut ph1, &mut last, 8, 12); // DataPageHeaderV2
        let mut dl = 0i16;
        t_fhdr(&mut ph1, &mut dl, 1, 5);
        t_zz32(&mut ph1, 5); // num_values
        t_fhdr(&mut ph1, &mut dl, 2, 5);
        t_zz32(&mut ph1, 0); // num_nulls
        t_fhdr(&mut ph1, &mut dl, 3, 5);
        t_zz32(&mut ph1, 5); // num_rows
        t_fhdr(&mut ph1, &mut dl, 4, 5);
        t_zz32(&mut ph1, 0); // PLAIN
        t_fhdr(&mut ph1, &mut dl, 5, 5);
        t_zz32(&mut ph1, 0); // def_len
        t_fhdr(&mut ph1, &mut dl, 6, 5);
        t_zz32(&mut ph1, 0); // rep_len
        t_fhdr(&mut ph1, &mut dl, 7, 1); // is_compressed = true
        ph1.push(0);
        ph1.push(0);
    }
    w.extend_from_slice(&ph1);
    w.extend_from_slice(&col1_snappy);
    let col1_comp_total = (ph1.len() + col1_snappy.len()) as i64;
    let col1_uncomp_total = (ph1.len() + col1_plain.len()) as i64;

    // --- Col 2 (`ts`: TIMESTAMP_MILLIS INT64, UNCOMPRESSED) ---
    let col2_off = w.len() as i64;
    let mut col2_plain = Vec::new();
    for ms in [1_000i64, 2_500, 0, 1_700_000_000_123, -1_000] {
        col2_plain.extend_from_slice(&ms.to_le_bytes());
    }
    let mut ph2 = Vec::new();
    {
        let mut last = 0i16;
        t_fhdr(&mut ph2, &mut last, 1, 5);
        t_zz32(&mut ph2, 0);
        t_fhdr(&mut ph2, &mut last, 2, 5);
        t_zz32(&mut ph2, col2_plain.len() as i32);
        t_fhdr(&mut ph2, &mut last, 3, 5);
        t_zz32(&mut ph2, col2_plain.len() as i32);
        t_fhdr(&mut ph2, &mut last, 5, 12);
        let mut dl = 0i16;
        t_fhdr(&mut ph2, &mut dl, 1, 5);
        t_zz32(&mut ph2, 5);
        t_fhdr(&mut ph2, &mut dl, 2, 5);
        t_zz32(&mut ph2, 0);
        t_fhdr(&mut ph2, &mut dl, 3, 5);
        t_zz32(&mut ph2, 3);
        t_fhdr(&mut ph2, &mut dl, 4, 5);
        t_zz32(&mut ph2, 3);
        ph2.push(0);
        ph2.push(0);
    }
    w.extend_from_slice(&ph2);
    w.extend_from_slice(&col2_plain);
    let col2_total = (ph2.len() + col2_plain.len()) as i64;

    // --- Col 3 (`count`: INT32, UNCOMPRESSED) ---
    let col3_off = w.len() as i64;
    let mut col3_plain = Vec::new();
    for n in [10i32, -20, 30, 40, 50] {
        col3_plain.extend_from_slice(&n.to_le_bytes());
    }
    let mut ph3 = Vec::new();
    {
        let mut last = 0i16;
        t_fhdr(&mut ph3, &mut last, 1, 5);
        t_zz32(&mut ph3, 0);
        t_fhdr(&mut ph3, &mut last, 2, 5);
        t_zz32(&mut ph3, col3_plain.len() as i32);
        t_fhdr(&mut ph3, &mut last, 3, 5);
        t_zz32(&mut ph3, col3_plain.len() as i32);
        t_fhdr(&mut ph3, &mut last, 5, 12);
        let mut dl = 0i16;
        t_fhdr(&mut ph3, &mut dl, 1, 5);
        t_zz32(&mut ph3, 5);
        t_fhdr(&mut ph3, &mut dl, 2, 5);
        t_zz32(&mut ph3, 0);
        t_fhdr(&mut ph3, &mut dl, 3, 5);
        t_zz32(&mut ph3, 3);
        t_fhdr(&mut ph3, &mut dl, 4, 5);
        t_zz32(&mut ph3, 3);
        ph3.push(0);
        ph3.push(0);
    }
    w.extend_from_slice(&ph3);
    w.extend_from_slice(&col3_plain);
    let col3_total = (ph3.len() + col3_plain.len()) as i64;

    // --- Col 4 (`score`: FLOAT, UNCOMPRESSED) ---
    let col4_off = w.len() as i64;
    let mut col4_plain = Vec::new();
    for f in [1.5f32, 2.25, -0.5, 0.0, 4.0] {
        col4_plain.extend_from_slice(&f.to_le_bytes());
    }
    let mut ph4 = Vec::new();
    {
        let mut last = 0i16;
        t_fhdr(&mut ph4, &mut last, 1, 5);
        t_zz32(&mut ph4, 0);
        t_fhdr(&mut ph4, &mut last, 2, 5);
        t_zz32(&mut ph4, col4_plain.len() as i32);
        t_fhdr(&mut ph4, &mut last, 3, 5);
        t_zz32(&mut ph4, col4_plain.len() as i32);
        t_fhdr(&mut ph4, &mut last, 5, 12);
        let mut dl = 0i16;
        t_fhdr(&mut ph4, &mut dl, 1, 5);
        t_zz32(&mut ph4, 5);
        t_fhdr(&mut ph4, &mut dl, 2, 5);
        t_zz32(&mut ph4, 0);
        t_fhdr(&mut ph4, &mut dl, 3, 5);
        t_zz32(&mut ph4, 3);
        t_fhdr(&mut ph4, &mut dl, 4, 5);
        t_zz32(&mut ph4, 3);
        ph4.push(0);
        ph4.push(0);
    }
    w.extend_from_slice(&ph4);
    w.extend_from_slice(&col4_plain);
    let col4_total = (ph4.len() + col4_plain.len()) as i64;

    // --- FileMetaData ---
    let mut fm = Vec::new();
    {
        let mut last = 0i16;
        t_fhdr(&mut fm, &mut last, 1, 5);
        t_zz32(&mut fm, 2); // version 2
        t_fhdr(&mut fm, &mut last, 2, 9); // schema list (6 elements: root + 5 cols)
        t_list(&mut fm, 12, 6);
        // Root
        {
            let mut sl = 0i16;
            t_fhdr(&mut fm, &mut sl, 4, 8);
            t_str(&mut fm, "root");
            t_fhdr(&mut fm, &mut sl, 5, 5);
            t_zz32(&mut fm, 5);
            fm.push(0);
        }
        // Col 0: dept BYTE_ARRAY OPTIONAL UTF8
        {
            let mut sl = 0i16;
            t_fhdr(&mut fm, &mut sl, 1, 5);
            t_zz32(&mut fm, 6);
            t_fhdr(&mut fm, &mut sl, 3, 5);
            t_zz32(&mut fm, 1);
            t_fhdr(&mut fm, &mut sl, 4, 8);
            t_str(&mut fm, "dept");
            t_fhdr(&mut fm, &mut sl, 6, 5);
            t_zz32(&mut fm, 0); // UTF8
            fm.push(0);
        }
        // Col 1: amount INT64 REQUIRED DECIMAL(10, 2)
        {
            let mut sl = 0i16;
            t_fhdr(&mut fm, &mut sl, 1, 5);
            t_zz32(&mut fm, 2);
            t_fhdr(&mut fm, &mut sl, 3, 5);
            t_zz32(&mut fm, 0);
            t_fhdr(&mut fm, &mut sl, 4, 8);
            t_str(&mut fm, "amount");
            t_fhdr(&mut fm, &mut sl, 6, 5);
            t_zz32(&mut fm, 5); // DECIMAL
            t_fhdr(&mut fm, &mut sl, 7, 5);
            t_zz32(&mut fm, 2); // scale = 2
            t_fhdr(&mut fm, &mut sl, 8, 5);
            t_zz32(&mut fm, 10); // precision = 10
            fm.push(0);
        }
        // Col 2: ts INT64 REQUIRED TIMESTAMP_MILLIS
        {
            let mut sl = 0i16;
            t_fhdr(&mut fm, &mut sl, 1, 5);
            t_zz32(&mut fm, 2);
            t_fhdr(&mut fm, &mut sl, 3, 5);
            t_zz32(&mut fm, 0);
            t_fhdr(&mut fm, &mut sl, 4, 8);
            t_str(&mut fm, "ts");
            t_fhdr(&mut fm, &mut sl, 6, 5);
            t_zz32(&mut fm, 9); // TIMESTAMP_MILLIS
            fm.push(0);
        }
        // Col 3: count INT32 REQUIRED
        {
            let mut sl = 0i16;
            t_fhdr(&mut fm, &mut sl, 1, 5);
            t_zz32(&mut fm, 1);
            t_fhdr(&mut fm, &mut sl, 3, 5);
            t_zz32(&mut fm, 0);
            t_fhdr(&mut fm, &mut sl, 4, 8);
            t_str(&mut fm, "count");
            fm.push(0);
        }
        // Col 4: score FLOAT REQUIRED
        {
            let mut sl = 0i16;
            t_fhdr(&mut fm, &mut sl, 1, 5);
            t_zz32(&mut fm, 4);
            t_fhdr(&mut fm, &mut sl, 3, 5);
            t_zz32(&mut fm, 0);
            t_fhdr(&mut fm, &mut sl, 4, 8);
            t_str(&mut fm, "score");
            fm.push(0);
        }

        // num_rows = 5
        t_fhdr(&mut fm, &mut last, 3, 6);
        t_zz64(&mut fm, 5);

        // row_groups (1)
        t_fhdr(&mut fm, &mut last, 4, 9);
        t_list(&mut fm, 12, 1);
        {
            let mut rl = 0i16;
            t_fhdr(&mut fm, &mut rl, 1, 9); // columns (5)
            t_list(&mut fm, 12, 5);

            let write_cc = |buf: &mut Vec<u8>,
                            pt: i32,
                            name: &str,
                            codec: i32,
                            sizes: (i64, i64),
                            offsets: (i64, Option<i64>)| {
                let (uncomp, comp) = sizes;
                let (data_off, dict_off) = offsets;
                let mut cl = 0i16;
                t_fhdr(buf, &mut cl, 2, 6);
                t_zz64(buf, dict_off.unwrap_or(data_off));
                t_fhdr(buf, &mut cl, 3, 12);
                let mut ml = 0i16;
                t_fhdr(buf, &mut ml, 1, 5);
                t_zz32(buf, pt);
                t_fhdr(buf, &mut ml, 2, 9);
                t_list(buf, 5, 1);
                t_zz32(buf, if dict_off.is_some() { 8 } else { 0 });
                t_fhdr(buf, &mut ml, 3, 9);
                t_list(buf, 8, 1);
                t_str(buf, name);
                t_fhdr(buf, &mut ml, 4, 5);
                t_zz32(buf, codec);
                t_fhdr(buf, &mut ml, 5, 6);
                t_zz64(buf, 5);
                t_fhdr(buf, &mut ml, 6, 6);
                t_zz64(buf, uncomp);
                t_fhdr(buf, &mut ml, 7, 6);
                t_zz64(buf, comp);
                t_fhdr(buf, &mut ml, 9, 6);
                t_zz64(buf, data_off);
                if let Some(doff) = dict_off {
                    t_fhdr(buf, &mut ml, 11, 6);
                    t_zz64(buf, doff);
                }
                buf.push(0);
                buf.push(0);
            };
            write_cc(
                &mut fm,
                6,
                "dept",
                1, // SNAPPY
                (col0_uncomp_total, col0_comp_total),
                (col0_data_off, Some(col0_dict_off)),
            );
            write_cc(
                &mut fm,
                2,
                "amount",
                1, // SNAPPY
                (col1_uncomp_total, col1_comp_total),
                (col1_off, None),
            );
            write_cc(
                &mut fm,
                2,
                "ts",
                0,
                (col2_total, col2_total),
                (col2_off, None),
            );
            write_cc(
                &mut fm,
                1,
                "count",
                0,
                (col3_total, col3_total),
                (col3_off, None),
            );
            write_cc(
                &mut fm,
                4,
                "score",
                0,
                (col4_total, col4_total),
                (col4_off, None),
            );

            t_fhdr(&mut fm, &mut rl, 2, 6);
            t_zz64(
                &mut fm,
                col0_uncomp_total + col1_uncomp_total + col2_total + col3_total + col4_total,
            );
            t_fhdr(&mut fm, &mut rl, 3, 6);
            t_zz64(&mut fm, 5);
            fm.push(0);
        }
        fm.push(0);
    }

    w.extend_from_slice(&fm);
    w.extend_from_slice(&(fm.len() as u32).to_le_bytes());
    w.extend_from_slice(b"PAR1");

    let schema = table_ty(vec![
        col("dept", opt(ScalarTy::Text), &[]),
        col("amount", ScalarTy::Decimal, &[]),
        col("ts", ScalarTy::Timestamp, &[]),
        col("count", ScalarTy::Int, &[]),
        col("score", ScalarTy::Float, &[]),
    ]);
    let decoded = read_parquet_bytes_with_schema(&w, &schema, |_, _| true)?;
    assert_eq!(decoded.rows.len(), 5);

    let expected_depts = [
        Val::OptSome(Box::new(Val::Text("ENG".to_string()))),
        Val::OptNone,
        Val::OptSome(Box::new(Val::Text("OPS".to_string()))),
        Val::OptSome(Box::new(Val::Text("ENG".to_string()))),
        Val::OptSome(Box::new(Val::Text("ENG".to_string()))),
    ];
    let expected_amounts = ["12.34", "-5.00", "0.01", "100.50", "12.34"];
    let expected_ts_us = [
        1_000_000i64,
        2_500_000,
        0,
        1_700_000_000_123_000,
        -1_000_000,
    ];
    let expected_counts = [10i64, -20, 30, 40, 50];
    let expected_scores = [1.5f64, 2.25, -0.5, 0.0, 4.0];

    for i in 0..5 {
        assert!(val_eq(&decoded.rows[i].cells[0], &expected_depts[i]));
        assert!(val_eq(
            &decoded.rows[i].cells[1],
            &Val::Decimal(parse_decimal_bigint_strict(expected_amounts[i])?)
        ));
        assert!(val_eq(
            &decoded.rows[i].cells[2],
            &Val::Timestamp(BigInt::from(expected_ts_us[i]))
        ));
        assert!(val_eq(
            &decoded.rows[i].cells[3],
            &Val::Int(BigInt::from(expected_counts[i]))
        ));
        assert!(val_eq(
            &decoded.rows[i].cells[4],
            &Val::Float(Float64::from_f64(expected_scores[i]))
        ));
    }
    Ok(())
}

#[test]
fn live_ecommerce_ledger_audit_parquet_csv_sqlite_e2e() -> TestResult {
    let tmp = TempDir::new("ecommerce")?;
    let data_dir = tmp.path().join("data");
    fs::create_dir_all(&data_dir)?;

    // Write `data/orders.parquet`
    let orders_tv = TableVal {
        cols: vec![
            col("order_id", ScalarTy::Text, &[]),
            col("created_at", ScalarTy::Timestamp, &[]),
            col("currency", ScalarTy::Text, &[]),
            col("order_total", ScalarTy::Decimal, &[]),
        ],
        rows: vec![
            TableRow {
                cells: vec![
                    Val::Text("O-1".to_string()),
                    Val::Timestamp(BigInt::from(parse_iso_timestamp("2026-10-01T10:00:00Z")?)),
                    Val::Text("USD".to_string()),
                    Val::Decimal(parse_decimal_bigint_strict("100.00")?),
                ],
                group_meta: None,
            },
            TableRow {
                cells: vec![
                    Val::Text("O-2".to_string()),
                    Val::Timestamp(BigInt::from(parse_iso_timestamp("2026-10-01T11:00:00Z")?)),
                    Val::Text("USD".to_string()),
                    Val::Decimal(parse_decimal_bigint_strict("50.00")?),
                ],
                group_meta: None,
            },
            TableRow {
                cells: vec![
                    Val::Text("O-3".to_string()),
                    Val::Timestamp(BigInt::from(parse_iso_timestamp("2026-10-01T12:00:00Z")?)),
                    Val::Text("USD".to_string()),
                    Val::Decimal(parse_decimal_bigint_strict("75.00")?),
                ],
                group_meta: None,
            },
        ],
    };
    write_parquet_table(
        &data_dir.join("orders.parquet"),
        &orders_tv,
        ParquetCompression::Zstd,
    )?;

    // Write `data/payments.parquet`
    let payments_tv = TableVal {
        cols: vec![
            col("payment_id", ScalarTy::Text, &[]),
            col("order_id", ScalarTy::Text, &[]),
            col("settled_amount", ScalarTy::Decimal, &[]),
        ],
        rows: vec![
            TableRow {
                cells: vec![
                    Val::Text("P-1".to_string()),
                    Val::Text("O-1".to_string()),
                    Val::Decimal(parse_decimal_bigint_strict("100.00")?),
                ],
                group_meta: None,
            },
            TableRow {
                cells: vec![
                    Val::Text("P-2".to_string()),
                    Val::Text("O-2".to_string()),
                    Val::Decimal(parse_decimal_bigint_strict("60.00")?),
                ],
                group_meta: None,
            },
            TableRow {
                cells: vec![
                    Val::Text("P-3".to_string()),
                    Val::Text("O-3".to_string()),
                    Val::Decimal(parse_decimal_bigint_strict("75.00")?),
                ],
                group_meta: None,
            },
            TableRow {
                cells: vec![
                    Val::Text("P-4".to_string()),
                    Val::Text("O-999".to_string()),
                    Val::Decimal(parse_decimal_bigint_strict("25.00")?),
                ],
                group_meta: None,
            },
        ],
    };
    write_parquet_table(
        &data_dir.join("payments.parquet"),
        &payments_tv,
        ParquetCompression::Gzip,
    )?;

    // Write `data/refunds.csv`
    fs::write(
        data_dir.join("refunds.csv"),
        "refund_id,order_id,refund_amount\nRF-1,O-1,10.00\n",
    )?;

    // Prepare SQLite DB for `AuditDB`
    let db_path = tmp.path().join("audit.db");
    let db_uri = format!("sqlite://{}", db_path.display());
    {
        let mut conn = open_connection(&db_uri)?;
        conn.execute(
            r#"CREATE TABLE "ledger_runs" (
                "order_id" TEXT PRIMARY KEY NOT NULL,
                "order_total" TEXT NOT NULL,
                "net_collected" TEXT NOT NULL,
                "variance" TEXT NOT NULL,
                "status" TEXT NOT NULL
            )"#,
            &[],
        )?;
    }

    let prog = compile_example("examples/ecommerce-ledger-audit.dana", true)?;
    let mut db_bindings = HashMap::new();
    db_bindings.insert("AuditDB".to_string(), db_uri.clone());

    // First verify `dry_run` suppresses both SQLite and Parquet writes
    let dry_cfg = RunConfig {
        work_dir: Some(tmp.path().to_path_buf()),
        db_bindings: db_bindings.clone(),
        dry_run: true,
        ..RunConfig::default()
    };
    let dry_res = run_exec_program_vm(&prog, &dry_cfg, &VmConfig::default());
    match dry_res {
        RunResult::Ok {
            exit_code, stdout, ..
        } => {
            assert_eq!(exit_code, 1); // exceptions & orphans exist
            assert!(
                stdout
                    .iter()
                    .any(|l| l.contains("[DRY-RUN] would write parquet")),
                "expected dry-run parquet notice in stdout: {stdout:?}"
            );
            assert!(
                !tmp.path()
                    .join("reports/ledger-exceptions.parquet")
                    .exists(),
                "dry-run must NOT write Parquet file to disk"
            );
        }
        other => return Err(format!("dry-run failed: {other:?}").into()),
    }

    // Live execution on both VM and Oracle
    let live_cfg = RunConfig {
        work_dir: Some(tmp.path().to_path_buf()),
        db_bindings,
        ..RunConfig::default()
    };
    let vm_res = run_exec_program_vm(&prog, &live_cfg, &VmConfig::default());
    let oracle_res = run_exec_program(&prog, &live_cfg);

    for (label, res) in [("vm", vm_res), ("oracle", oracle_res)] {
        match res {
            RunResult::Ok {
                exit_code, stdout, ..
            } => {
                assert_eq!(exit_code, 1, "{label} exit_code");
                assert!(
                    stdout
                        .iter()
                        .any(|l| l.contains("Audited 3 orders: 2 exceptions, 1 orphan payments.")),
                    "{label} unexpected stdout: {stdout:?}"
                );
            }
            other => return Err(format!("{label} execution failed: {other:?}").into()),
        }
    }

    // Verify output Parquet file contains the 2 unbalanced exceptions (`O-1` underpaid, `O-2` overpaid)
    let summary_schema = table_ty(vec![
        col("order_id", ScalarTy::Text, &[]),
        col("order_total", ScalarTy::Decimal, &[]),
        col("net_collected", ScalarTy::Decimal, &[]),
        col("variance", ScalarTy::Decimal, &[]),
        col("status", ScalarTy::Text, &[]),
    ]);
    let exc_tbl = read_parquet_file_with_schema(
        &tmp.path().join("reports/ledger-exceptions.parquet"),
        &summary_schema,
        |_, _| true,
    )?;
    assert_eq!(exc_tbl.rows.len(), 2);

    // Verify SQLite `ledger_runs` table has all 3 audited orders
    let mut conn = open_connection(&db_uri)?;
    let db_rows = conn.query_rows(
        "SELECT order_id, order_total, net_collected, variance, status FROM ledger_runs ORDER BY order_id",
        &[],
        &summary_schema,
    )?;
    assert_eq!(db_rows.rows.len(), 3);
    assert!(val_eq(
        &db_rows.rows[0].cells[4],
        &Val::Text("underpaid".to_string())
    ));
    assert!(val_eq(
        &db_rows.rows[1].cells[4],
        &Val::Text("overpaid".to_string())
    ));
    assert!(val_eq(
        &db_rows.rows[2].cells[4],
        &Val::Text("balanced".to_string())
    ));
    Ok(())
}

// ===========================================================================
// 3. Native Excel `.xlsx` Tests
// ===========================================================================

#[test]
fn xlsx_roundtrip_serial_dates_shared_strings_quarantine_and_security() -> TestResult {
    // 1. Excel 1900 serial date/timestamp edge cases
    assert_eq!(
        excel_serial_to_days(59, false),
        Some(days_from_civil(1900, 2, 28))
    );
    assert_eq!(excel_serial_to_days(60, false), None); // fictitious 1900-02-29 rejected
    assert_eq!(
        excel_serial_to_days(61, false),
        Some(days_from_civil(1900, 3, 1))
    );
    assert_eq!(excel_serial_to_days(25_569, false), Some(0)); // 1970-01-01
    let d_2026 = parse_iso_date("2026-10-01")?;
    let s_2026 = days_to_excel_1900_serial(d_2026).ok_or("serial failed")?;
    assert_eq!(excel_serial_to_days(s_2026, false), Some(d_2026));

    let ts_us = parse_iso_timestamp("2026-10-01T14:30:45.250000Z")?;
    let ts_serial = micros_to_excel_1900_serial(ts_us).ok_or("ts serial failed")?;
    assert_eq!(excel_serial_to_micros(ts_serial, false), Some(ts_us));

    // 2. Multi-sheet typed round-trip across scalar types + Option nulls + XML escaping
    let schema1 = table_ty(vec![
        col("id", ScalarTy::Int, &[]),
        col("label", ScalarTy::Text, &["pii"]),
        col("flag", ScalarTy::Bool, &[]),
        col("amt", ScalarTy::Decimal, &["financial"]),
        col("score", opt(ScalarTy::Float), &[]),
        col("dt", ScalarTy::Date, &[]),
        col("ts", ScalarTy::Timestamp, &[]),
    ]);
    let t1 = TableVal {
        cols: schema1.cols.clone(),
        rows: vec![
            TableRow {
                cells: vec![
                    Val::Int(BigInt::from(1)),
                    Val::Text("  Alice & Bob <\"quoted\"> 'ok'  ".to_string()),
                    Val::Bool(true),
                    Val::Decimal(parse_decimal_bigint_strict("12345.678901234567890123")?),
                    Val::OptSome(Box::new(Val::Float(Float64::from_f64(98.5)))),
                    Val::Date(BigInt::from(d_2026)),
                    Val::Timestamp(BigInt::from(ts_us)),
                ],
                group_meta: None,
            },
            TableRow {
                cells: vec![
                    Val::Int(BigInt::from(2)),
                    Val::Text("Carol".to_string()),
                    Val::Bool(false),
                    Val::Decimal(parse_decimal_bigint_strict("-0.05")?),
                    Val::OptNone,
                    Val::Date(BigInt::from(days_from_civil(1900, 2, 28))),
                    Val::Timestamp(BigInt::from(parse_iso_timestamp("1985-07-04T00:00:00Z")?)),
                ],
                group_meta: None,
            },
        ],
    };
    let schema2 = table_ty(vec![
        col("k", ScalarTy::Text, &[]),
        col("v", ScalarTy::Int, &[]),
    ]);
    let t2 = TableVal {
        cols: schema2.cols.clone(),
        rows: vec![TableRow {
            cells: vec![Val::Text("total".to_string()), Val::Int(BigInt::from(2))],
            group_meta: None,
        }],
    };

    let wb_bytes = write_xlsx_sheets(&[
        ("Primary".to_string(), t1.clone()),
        ("Meta".to_string(), t2.clone()),
    ])?;

    // Default sheet (first) & explicit named sheets
    let (r1_def, bad1_def) = read_xlsx_bytes_with_schema(&wb_bytes, None, &schema1, |_, _| true)?;
    assert!(bad1_def.rows.is_empty());
    assert_tables_eq(&r1_def, &t1);

    let (r2, bad2) = read_xlsx_bytes_with_schema(&wb_bytes, Some("Meta"), &schema2, |_, _| true)?;
    assert!(bad2.rows.is_empty());
    assert_tables_eq(&r2, &t2);

    // Missing sheet returns clean error
    assert!(
        read_xlsx_bytes_with_schema(&wb_bytes, Some("DoesNotExist"), &schema1, |_, _| true)
            .is_err()
    );

    // 3. Hand-crafted OOXML workbook testing sharedStrings (rich text + entities), formula cached str,
    //    sparse coordinates (AB1), built-in style numFmtId=14 & custom date format, and quarantine PII tagging!
    let workbook_xml = br#"<?xml version="1.0" encoding="UTF-8"?>
<workbook xmlns="http://schemas.openxmlformats.org/spreadsheetml/2006/main" xmlns:r="http://schemas.openxmlformats.org/officeDocument/2006/relationships">
  <sheets><sheet name="Gifts" sheetId="1" r:id="rId1"/></sheets>
</workbook>"#;
    let rels_xml = br#"<?xml version="1.0" encoding="UTF-8"?>
<Relationships xmlns="http://schemas.openxmlformats.org/package/2006/relationships">
  <Relationship Id="rId1" Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/worksheet" Target="worksheets/sheet1.xml"/>
</Relationships>"#;
    let shared_xml = br#"<?xml version="1.0" encoding="UTF-8"?>
<sst xmlns="http://schemas.openxmlformats.org/spreadsheetml/2006/main" count="4" uniqueCount="4">
  <si><t>donor_name</t></si>
  <si><r><t>Alice </t></r><r><t>&amp; Co &#x27;26</t></r></si>
  <si><t>gift_date</t></si>
  <si><t>amount</t></si>
</sst>"#;
    let styles_xml = br#"<?xml version="1.0" encoding="UTF-8"?>
<styleSheet xmlns="http://schemas.openxmlformats.org/spreadsheetml/2006/main">
  <cellXfs count="2">
    <xf numFmtId="0"/>
    <xf numFmtId="14"/>
  </cellXfs>
</styleSheet>"#;
    // Sparse columns: A=donor_name, C=gift_date, AB=amount
    // Row 2: valid (shared string + serial date 46296 -> 2026-10-01 + positive amount)
    // Row 3: invalid fictitious date serial 60 -> quarantined!
    // Row 4: negative amount (-10.00) -> fails `where` constraint -> quarantined!
    let sheet_xml = format!(
        r#"<?xml version="1.0" encoding="UTF-8"?>
<worksheet xmlns="http://schemas.openxmlformats.org/spreadsheetml/2006/main">
  <sheetData>
    <row r="1">
      <c r="A1" t="s"><v>0</v></c>
      <c r="C1" t="s"><v>2</v></c>
      <c r="AB1" t="s"><v>3</v></c>
    </row>
    <row r="2">
      <c r="A2" t="s"><v>1</v></c>
      <c r="C2" s="1"><v>{s_2026}</v></c>
      <c r="AB2"><v>250.50</v></c>
    </row>
    <row r="3">
      <c r="A3" t="str"><v>Bob Secret</v></c>
      <c r="C3" s="1"><v>60</v></c>
      <c r="AB3"><v>100.00</v></c>
    </row>
    <row r="4">
      <c r="A4" t="inlineStr"><is><t>Carol Secret</t></is></c>
      <c r="C4" s="1"><v>{s_2026}</v></c>
      <c r="AB4"><v>-10.00</v></c>
    </row>
  </sheetData>
</worksheet>"#
    );

    let custom_xlsx = write_zip_bytes(
        &[
            ("xl/workbook.xml", workbook_xml),
            ("xl/_rels/workbook.xml.rels", rels_xml),
            ("xl/sharedStrings.xml", shared_xml),
            ("xl/styles.xml", styles_xml),
            ("xl/worksheets/sheet1.xml", sheet_xml.as_bytes()),
        ],
        ZipCompression::Deflated,
    )?;

    let gift_schema = table_ty(vec![
        col("donor_name", ScalarTy::Text, &["pii", "donor"]),
        col("gift_date", ScalarTy::Date, &[]),
        col("amount", ScalarTy::Decimal, &["financial", "donor"]),
    ]);
    let (good, bad) =
        read_xlsx_bytes_with_schema(&custom_xlsx, Some("Gifts"), &gift_schema, |ci, val| {
            if ci == 2
                && let Val::Decimal(d) = val
            {
                return d.is_positive();
            }
            true
        })?;
    assert_eq!(good.rows.len(), 1);
    assert!(val_eq(
        &good.rows[0].cells[0],
        &Val::Text("Alice & Co '26".to_string())
    ));
    assert!(val_eq(
        &good.rows[0].cells[1],
        &Val::Date(BigInt::from(d_2026))
    ));
    assert!(val_eq(
        &good.rows[0].cells[2],
        &Val::Decimal(parse_decimal_bigint_strict("250.50")?)
    ));

    // Verify quarantine rows & privacy tagging on `bad_rows`!
    assert_eq!(bad.rows.len(), 2);
    assert!(val_eq(&bad.rows[0].cells[0], &Val::Int(BigInt::from(3))));
    assert!(val_eq(
        &bad.rows[0].cells[1],
        &Val::Text("gift_date".to_string())
    ));
    assert!(val_eq(
        &bad.rows[0].cells[2],
        &Val::Text("BadDate".to_string())
    ));
    assert!(val_eq(&bad.rows[1].cells[0], &Val::Int(BigInt::from(4))));
    assert!(val_eq(
        &bad.rows[1].cells[1],
        &Val::Text("amount".to_string())
    ));
    assert!(val_eq(
        &bad.rows[1].cells[2],
        &Val::Text("ConstraintFailed".to_string())
    ));
    // `line`, `column`, `error_kind` are public; `raw_value` and `raw_row` carry [donor, financial, pii]!
    assert!(bad.cols[0].tags.is_empty());
    assert!(bad.cols[1].tags.is_empty());
    assert!(bad.cols[2].tags.is_empty());
    assert!(bad.cols[3].tags.contains("pii"));
    assert!(bad.cols[3].tags.contains("donor"));
    assert!(bad.cols[3].tags.contains("financial"));
    assert!(bad.cols[4].tags.contains("pii"));

    // 4. XXE / DTD rejection
    let xxe_wb = br#"<?xml version="1.0"?>
<!DOCTYPE foo [ <!ENTITY xxe SYSTEM "file:///etc/passwd"> ]>
<workbook><sheets><sheet name="S" sheetId="1" r:id="rId1"/></sheets></workbook>"#;
    let xxe_xlsx = write_zip_bytes(
        &[
            ("xl/workbook.xml", xxe_wb),
            ("xl/_rels/workbook.xml.rels", rels_xml),
            ("xl/worksheets/sheet1.xml", sheet_xml.as_bytes()),
        ],
        ZipCompression::Deflated,
    )?;
    let xxe_err = read_xlsx_bytes_with_schema(&xxe_xlsx, None, &gift_schema, |_, _| true);
    assert!(xxe_err.is_err(), "XXE/DTD XML payload MUST be rejected");
    Ok(())
}

#[test]
fn live_donor_reconciliation_xlsx_sqlite_and_multisheet_report_e2e() -> TestResult {
    let tmp = TempDir::new("donor_recon")?;

    // 1. Write input `gifts.xlsx` with worksheet "Gifts" (3 valid rows + 1 bad negative amount row!)
    let input_tv = TableVal {
        cols: vec![
            col("receipt_no", ScalarTy::Text, &[]),
            col("donor_name", ScalarTy::Text, &["pii", "donor"]),
            col("fund_code", ScalarTy::Text, &[]),
            col("gift_date", ScalarTy::Date, &[]),
            col("amount", ScalarTy::Decimal, &["financial", "donor"]),
        ],
        rows: vec![
            TableRow {
                cells: vec![
                    Val::Text("R-100".to_string()),
                    Val::Text("Alice Smith".to_string()),
                    Val::Text("GEN".to_string()),
                    Val::Date(BigInt::from(parse_iso_date("2026-10-01")?)),
                    Val::Decimal(parse_decimal_bigint_strict("250.00")?),
                ],
                group_meta: None,
            },
            TableRow {
                cells: vec![
                    Val::Text("R-101".to_string()),
                    Val::Text("Bob Jones".to_string()),
                    Val::Text("SCHOL".to_string()),
                    Val::Date(BigInt::from(parse_iso_date("2026-10-02")?)),
                    Val::Decimal(parse_decimal_bigint_strict("100.50")?),
                ],
                group_meta: None,
            },
            TableRow {
                cells: vec![
                    Val::Text("R-102".to_string()),
                    Val::Text("Carol Lee".to_string()),
                    Val::Text("GEN".to_string()),
                    Val::Date(BigInt::from(parse_iso_date("2026-10-03")?)),
                    Val::Decimal(parse_decimal_bigint_strict("75.25")?),
                ],
                group_meta: None,
            },
            // Malformed row: amount = -5.00 violates `where . > 0`
            TableRow {
                cells: vec![
                    Val::Text("R-BAD".to_string()),
                    Val::Text("Sensitive Donor Name".to_string()),
                    Val::Text("GEN".to_string()),
                    Val::Date(BigInt::from(parse_iso_date("2026-10-04")?)),
                    Val::Decimal(parse_decimal_bigint_strict("-5.00")?),
                ],
                group_meta: None,
            },
        ],
    };
    let input_xlsx = tmp.path().join("gifts.xlsx");
    write_xlsx_file(&input_xlsx, &[("Gifts".to_string(), input_tv)])?;

    // 2. Seed SQLite `Seminary` DB with `DbGift` table
    let db_path = tmp.path().join("seminary.db");
    let db_uri = format!("sqlite://{}", db_path.display());
    {
        let mut conn = open_connection(&db_uri)?;
        conn.execute(
            r#"CREATE TABLE "DbGift" (
                "receipt_no" TEXT PRIMARY KEY NOT NULL,
                "donor_id" INTEGER NOT NULL,
                "fund_code" TEXT NOT NULL,
                "gift_date" TEXT NOT NULL,
                "amount" TEXT NOT NULL
            )"#,
            &[],
        )?;
        for (rcpt, did, fund, dt, amt) in [
            ("R-100", 1i64, "GEN", "2026-10-01", "250.00"),
            ("R-101", 2, "SCHOL", "2026-10-02", "100.00"),
            ("R-103", 3, "BLDG", "2026-10-04", "500.00"),
        ] {
            conn.execute(
                r#"INSERT INTO "DbGift" (receipt_no, donor_id, fund_code, gift_date, amount) VALUES (?, ?, ?, ?, ?)"#,
                &[
                    SqlParam::Text(rcpt.to_string()),
                    SqlParam::Int(did),
                    SqlParam::Text(fund.to_string()),
                    SqlParam::Text(dt.to_string()),
                    SqlParam::Decimal(parse_decimal_bigint_strict(amt)?),
                ],
            )?;
        }
    }

    let prog = compile_example("examples/donor-reconciliation.dana", true)?;
    let mut db_bindings = HashMap::new();
    db_bindings.insert("Seminary".to_string(), db_uri);

    // 3. Running WITHOUT `--allow-export donor,financial` MUST be denied!
    let denied_cfg = RunConfig {
        args: vec!["gifts.xlsx".to_string()],
        work_dir: Some(tmp.path().to_path_buf()),
        db_bindings: db_bindings.clone(),
        allow_export: TagSet::empty(),
        ..RunConfig::default()
    };
    match run_exec_program_vm(&prog, &denied_cfg, &VmConfig::default()) {
        RunResult::Stopped { bug, .. } => assert_eq!(bug.kind, BugKind::ExportGateDenied),
        other => return Err(format!("expected ExportGateDenied, got {other:?}").into()),
    }

    // 4. Dry-run MUST NOT write the `.xlsx` report to disk
    let dry_cfg = RunConfig {
        args: vec!["gifts.xlsx".to_string()],
        work_dir: Some(tmp.path().to_path_buf()),
        db_bindings: db_bindings.clone(),
        dry_run: true,
        ..RunConfig::default()
    };
    match run_exec_program_vm(&prog, &dry_cfg, &VmConfig::default()) {
        RunResult::Ok {
            exit_code, stdout, ..
        } => {
            assert_eq!(exit_code, 1); // 1 malformed row
            assert!(
                stdout
                    .iter()
                    .any(|l| l.contains("[DRY-RUN] would write xlsx"))
            );
            assert!(
                !tmp.path()
                    .join("finance-audit/reconciliation-report.xlsx")
                    .exists()
            );
        }
        other => return Err(format!("dry-run failed: {other:?}").into()),
    }

    // 5. Authorized live execution on BOTH VM and Oracle
    let live_cfg = RunConfig {
        args: vec!["gifts.xlsx".to_string()],
        work_dir: Some(tmp.path().to_path_buf()),
        db_bindings,
        allow_export: TagSet::of_list(vec!["donor".to_string(), "financial".to_string()]),
        ..RunConfig::default()
    };
    for (label, res) in [
        (
            "vm",
            run_exec_program_vm(&prog, &live_cfg, &VmConfig::default()),
        ),
        ("oracle", run_exec_program(&prog, &live_cfg)),
    ] {
        match res {
            RunResult::Ok {
                exit_code,
                stdout,
                stderr,
            } => {
                assert_eq!(exit_code, 1, "{label} exit_code");
                assert!(
                    stdout
                        .iter()
                        .any(|l| l.contains("Reconciled 3 spreadsheet rows (1 malformed).")),
                    "{label} stdout: {stdout:?}"
                );
                // Verify PII never leaked into stderr!
                let joined_err = stderr.join("\n");
                assert!(
                    joined_err.contains("row 5, col amount: ConstraintFailed"),
                    "{label} stderr: {stderr:?}"
                );
                assert!(
                    !joined_err.contains("Sensitive Donor Name"),
                    "PII leaked into stderr!"
                );
            }
            other => return Err(format!("{label} live run failed: {other:?}").into()),
        }
    }

    // 6. Read back all 4 sheets from `finance-audit/reconciliation-report.xlsx`!
    let report_path = tmp.path().join("finance-audit/reconciliation-report.xlsx");
    let summary_schema = table_ty(vec![
        col("metric", ScalarTy::Text, &[]),
        col("count", ScalarTy::Int, &[]),
    ]);
    let (summary, sb) =
        read_xlsx_file_with_schema(&report_path, Some("Summary"), &summary_schema, |_, _| true)?;
    assert!(sb.rows.is_empty());
    assert_eq!(summary.rows.len(), 4);
    for (idx, expected_metric) in ["matched", "amount_mismatch", "only_in_sheet", "only_in_db"]
        .iter()
        .enumerate()
    {
        assert!(val_eq(
            &summary.rows[idx].cells[0],
            &Val::Text((*expected_metric).to_string())
        ));
        assert!(val_eq(
            &summary.rows[idx].cells[1],
            &Val::Int(BigInt::from(1))
        ));
    }

    let mm_schema = table_ty(vec![
        col("receipt_no", ScalarTy::Text, &[]),
        col("fund_code", ScalarTy::Text, &[]),
        col("sheet_amount", ScalarTy::Decimal, &[]),
        col("db_amount", ScalarTy::Decimal, &[]),
        col("delta", ScalarTy::Decimal, &[]),
    ]);
    let (mm, mmb) = read_xlsx_file_with_schema(
        &report_path,
        Some("AmountMismatches"),
        &mm_schema,
        |_, _| true,
    )?;
    assert!(mmb.rows.is_empty());
    assert_eq!(mm.rows.len(), 1);
    assert!(val_eq(
        &mm.rows[0].cells[0],
        &Val::Text("R-101".to_string())
    ));
    assert!(val_eq(
        &mm.rows[0].cells[4],
        &Val::Decimal(parse_decimal_bigint_strict("0.50")?)
    ));

    let only_schema = table_ty(vec![
        col("receipt_no", ScalarTy::Text, &[]),
        col("fund_code", ScalarTy::Text, &[]),
        col("amount", ScalarTy::Decimal, &[]),
    ]);
    let (only_sheet, _) = read_xlsx_file_with_schema(
        &report_path,
        Some("OnlyInSpreadsheet"),
        &only_schema,
        |_, _| true,
    )?;
    assert_eq!(only_sheet.rows.len(), 1);
    assert!(val_eq(
        &only_sheet.rows[0].cells[0],
        &Val::Text("R-102".to_string())
    ));

    let (only_db, _) = read_xlsx_file_with_schema(
        &report_path,
        Some("OnlyInDatabase"),
        &only_schema,
        |_, _| true,
    )?;
    assert_eq!(only_db.rows.len(), 1);
    assert!(val_eq(
        &only_db.rows[0].cells[0],
        &Val::Text("R-103".to_string())
    ));
    Ok(())
}

// ===========================================================================
// 4. Capability-Gated HTTPS Client & `Https.fake` Tests
// ===========================================================================

#[test]
fn https_url_parser_strict_validation() -> TestResult {
    let u = ParsedHttpsUrl::parse_and_check_host(
        "https://API.Example.COM:8443/v2/items?page=1#frag",
        "api.example.com",
    )?;
    assert_eq!(u.host, "API.Example.COM");
    assert_eq!(u.port, 8443);
    assert_eq!(u.path_and_query, "/v2/items?page=1");
    assert_eq!(u.host_header(), "API.Example.COM:8443");

    // Plain HTTP rejected
    assert!(ParsedHttpsUrl::parse("http://127.0.0.1/v2").is_err());
    // Cross-host rejected
    assert!(ParsedHttpsUrl::parse_and_check_host("https://evil.test/v2", "127.0.0.1").is_err());
    // Userinfo rejected
    assert!(ParsedHttpsUrl::parse("https://user:pass@127.0.0.1/v2").is_err());
    // CR/LF rejected
    assert!(ParsedHttpsUrl::parse("https://127.0.0.1/v2\r\nEvil: 1").is_err());
    Ok(())
}

fn gzip_bytes(raw: &[u8]) -> TestResult<Vec<u8>> {
    let mut w = GzipWriter::new(Vec::new())?;
    w.write_all(raw)?;
    Ok(w.finish()?)
}

fn encode_chunked(data: &[u8], chunk_sz: usize) -> Vec<u8> {
    let mut out = Vec::new();
    for ch in data.chunks(chunk_sz.max(1)) {
        out.extend_from_slice(format!("{:X}\r\n", ch.len()).as_bytes());
        out.extend_from_slice(ch);
        out.extend_from_slice(b"\r\n");
    }
    out.extend_from_slice(b"0\r\n\r\n");
    out
}

#[test]
fn https_loopback_tls_chunked_gzip_pagination_and_security_gates() -> TestResult {
    let dir = TempDir::new("https_tls")?;
    let (cert_path, key_path) = generate_self_signed_cert(dir.path())?;
    let acceptor = TlsServerAcceptor::from_pem_files(&cert_path, &key_path)
        .map_err(|e| format!("acceptor: {e}"))?;

    let listener = TcpListener::bind("127.0.0.1:0")?;
    let port = listener.local_addr()?.port();
    let seen_auth = Arc::new(Mutex::new(Vec::<String>::new()));
    let seen_auth_srv = Arc::clone(&seen_auth);

    // Expect 6 connections:
    // 1. Page 1 (chunked + gzip) - VM run
    // 2. Page 2 (chunked + gzip) - VM run
    // 3. Page 1 (chunked + gzip) - Oracle run
    // 4. Page 2 (chunked + gzip) - Oracle run
    // 5. Redirect 302 test
    // 6. Untrusted CA test (handshake fails on client)
    let page1_json = br#"{"items":[{"id":1,"email":"alice@sem.edu","gpa":"3.90"},{"id":2,"email":"invalid-email","gpa":"3.50"}],"has_more":true,"meta":{"cursor":"c2","total":3}}"#;
    let page2_json = br#"{"items":[{"id":3,"email":"bob@sem.edu","gpa":"3.75"}],"has_more":false,"meta":{"cursor":"done","total":3}}"#;
    let page1_gz = gzip_bytes(page1_json)?;
    let page2_gz = gzip_bytes(page2_json)?;

    let srv = thread::spawn(move || {
        for _ in 0..6 {
            let Ok((tcp, _)) = listener.accept() else {
                break;
            };
            let Ok(tls) = acceptor.accept(tcp) else {
                continue;
            };
            let mut reader = BufReader::new(tls);
            let mut req_line = String::new();
            if reader.read_line(&mut req_line).is_err() {
                continue;
            }
            let path = req_line
                .split_ascii_whitespace()
                .nth(1)
                .unwrap_or("/")
                .to_string();
            loop {
                let mut hline = String::new();
                if reader.read_line(&mut hline).is_err() {
                    break;
                }
                let trimmed = hline.trim();
                if trimmed.is_empty() {
                    break;
                }
                if let Some((k, v)) = trimmed.split_once(':')
                    && k.trim().eq_ignore_ascii_case("authorization")
                    && let Ok(mut guard) = seen_auth_srv.lock()
                {
                    guard.push(v.trim().to_string());
                }
            }
            let mut tls = reader.into_inner();
            if path.starts_with("/redirect") {
                let resp = "HTTP/1.1 302 Found\r\nLocation: https://evil.example.com/steal\r\nContent-Length: 0\r\nConnection: close\r\n\r\n";
                let _ = tls.write_all(resp.as_bytes());
            } else if path.contains("page=1") {
                let chunked = encode_chunked(&page1_gz, 19);
                let hdr = "HTTP/1.1 200 OK\r\nContent-Type: application/json\r\nContent-Encoding: gzip\r\nTransfer-Encoding: chunked\r\nConnection: close\r\n\r\n";
                let _ = tls.write_all(hdr.as_bytes());
                let _ = tls.write_all(&chunked);
            } else {
                let chunked = encode_chunked(&page2_gz, 23);
                let hdr = "HTTP/1.1 200 OK\r\nContent-Type: application/json\r\nContent-Encoding: gzip\r\nTransfer-Encoding: chunked\r\nConnection: close\r\n\r\n";
                let _ = tls.write_all(hdr.as_bytes());
                let _ = tls.write_all(&chunked);
            }
            let _ = tls.flush();
        }
    });

    // 1. Live Dana program exercising `HttpsAllow("127.0.0.1", allows: [pii])` + `Secret` + pagination
    let dana_src = format!(
        r#"
module LoopbackSync

schema ApiItem
  id: Int [pii]
  email: Text [pii] where .contains?("@")
  gpa: Decimal
end

fn main(
  api: HttpsAllow("127.0.0.1", allows: [pii]),
  token: Secret("api_token"),
  console: Console
) : Int
  var pages = []
  var all_bad = []
  var page = 1
  var last_cursor = ""
  var reported_total = 0

  while true
    resp = try api.get_json(
      "https://127.0.0.1:{port}/v2/items?page=#{{page}}",
      headers: {{"Authorization": "Bearer #{{token}}"}}
    )
    (rows, bad) = resp.parse_table("items", as: ApiItem)
    pages = pages.append(rows)
    all_bad = all_bad.append(bad)
    last_cursor = resp.text_at("meta.cursor")
    reported_total = resp.int_at("meta.total")
    break if not resp.bool_at("has_more")
    page = page + 1
  end

  combined = Table.concat(pages)
  combined_bad = Table.concat(all_bad)
  console.print("rows=#{{combined.count()}} bad=#{{combined_bad.count()}} cursor=#{{last_cursor}} total=#{{reported_total}}")
  0
end
"#
    );
    let prog = compile_source(&dana_src, None)?;

    // 1a. WITHOUT `--allow-export pii`, PII egress MUST stop with ExportGateDenied BEFORE connecting!
    let denied_cfg = RunConfig {
        https_ca_cert: Some(PathBuf::from(&cert_path)),
        allow_export: TagSet::empty(),
        ..RunConfig::default()
    };
    match run_exec_program_vm(&prog, &denied_cfg, &VmConfig::default()) {
        RunResult::Stopped { bug, .. } => assert_eq!(bug.kind, BugKind::ExportGateDenied),
        other => return Err(format!("expected ExportGateDenied, got {other:?}").into()),
    }

    // 1b. WITH `--allow-export pii`, both VM and Oracle paginate cleanly over TLS + chunked + gzip!
    let ok_cfg = RunConfig {
        https_ca_cert: Some(PathBuf::from(&cert_path)),
        allow_export: TagSet::singleton("pii"),
        ..RunConfig::default()
    };
    for (label, res) in [
        (
            "vm",
            run_exec_program_vm(&prog, &ok_cfg, &VmConfig::default()),
        ),
        ("oracle", run_exec_program(&prog, &ok_cfg)),
    ] {
        match res {
            RunResult::Ok {
                exit_code, stdout, ..
            } => {
                assert_eq!(exit_code, 0, "{label} exit_code");
                assert_eq!(
                    stdout,
                    vec!["rows=2 bad=1 cursor=done total=3".to_string()],
                    "{label} stdout"
                );
            }
            other => return Err(format!("{label} HTTPS run failed: {other:?}").into()),
        }
    }

    // Verify `Authorization: Bearer ...` header arrived on every request
    {
        let guard = seen_auth
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        assert_eq!(guard.len(), 4);
        assert!(guard.iter().all(|h| h.starts_with("Bearer ")));
    }

    // 2. Direct security checks on `https_get_json`
    let client_cfg = HttpsClientConfig {
        ca_cert_path: Some(cert_path),
        ..HttpsClientConfig::default()
    };

    // Cross-host rejection (fails before TCP!)
    let cross_err = https_get_json(
        &format!("https://other.example.com:{port}/v2/items"),
        "127.0.0.1",
        &[],
        &client_cfg,
    );
    assert!(cross_err.is_err());

    // Plain http:// rejection (fails before TCP!)
    let http_err = https_get_json(
        &format!("http://127.0.0.1:{port}/v2/items"),
        "127.0.0.1",
        &[],
        &client_cfg,
    );
    assert!(http_err.is_err());

    // Redirect 302 NEVER followed! (Connection 5)
    let redir_err = https_get_json(
        &format!("https://127.0.0.1:{port}/redirect"),
        "127.0.0.1",
        &[],
        &client_cfg,
    );
    assert!(redir_err.is_err(), "302 redirect MUST NOT be followed");

    // Untrusted self-signed cert without CA cert MUST fail TLS verification! (Connection 6)
    let untrusted_err = https_get_json(
        &format!("https://127.0.0.1:{port}/v2/items?page=1"),
        "127.0.0.1",
        &[],
        &HttpsClientConfig::default(),
    );
    assert!(
        untrusted_err.is_err(),
        "untrusted self-signed cert MUST be rejected"
    );

    let _ = srv.join();
    Ok(())
}

#[test]
fn offline_https_fake_runs_registrar_sync_pagination_and_enforces_spec_only() -> TestResult {
    // 1. Append an offline `test` block to `examples/registrar-sync.dana` that drives
    //    `fetch_all_students` and `prepare_sync` using `Https.fake` + `Secret.fake`!
    let base_src = fs::read_to_string(repo_root().join("examples/registrar-sync.dana"))?;
    let extended_src = format!(
        r#"{base_src}

test "offline Https.fake paginates fetch_all_students and quarantines invalid records"
  api = Https.fake(
    "api.populiweb.com",
    responses: {{
      "https://api.populiweb.com/v2/students?page=1&per_page=200": "{{\"items\":[{{\"external_id\":101,\"email\":\"  Alice@Sem.EDU \",\"program\":\" MDiv \",\"gpa\":\"3.85\",\"active?\":true}},{{\"external_id\":102,\"email\":\"not-an-email\",\"program\":\"MAR\",\"gpa\":\"3.50\",\"active?\":true}}],\"has_more\":true}}",
      "https://api.populiweb.com/v2/students?page=2&per_page=200": "{{\"items\":[{{\"external_id\":103,\"email\":\"Carol@Sem.EDU\",\"program\":\"ThM\",\"gpa\":null,\"active?\":true}}],\"has_more\":false}}"
    }}
  )
  token = Secret.fake("test-populi-token")
  (incoming, bad_rows) = try fetch_all_students(api, token)
  assert incoming.count() == 2
  assert bad_rows.count() == 1
  assert bad_rows.first!.column == "email"
  assert bad_rows.first!.error_kind == "ConstraintFailed"

  existing = table
    | student_id | email           | program | gpa  | active? |
    | 101        | "alice@sem.edu" | "MDiv"  | 3.80 | true    |
    | 200        | "old@sem.edu"   | "MAR"   | 3.20 | true    |
  end
  synced = prepare_sync(incoming, existing) |> sort_by(.student_id)
  assert synced.count() == 3
  assert synced.first!.email == "alice@sem.edu"
end
"#
    );

    let prog = compile_source(&extended_src, None)?;
    let cfg = RunConfig::default();
    let oracle_out = run_program_tests(&prog, Some("Https.fake"), &cfg);
    let vm_out = run_program_tests_vm(&prog, Some("Https.fake"), &cfg, &VmConfig::default());
    assert_eq!(oracle_out.len(), 1);
    assert_eq!(vm_out.len(), 1);
    assert!(
        oracle_out[0].passed,
        "oracle failed: {:?}",
        oracle_out[0].message
    );
    assert!(vm_out[0].passed, "vm failed: {:?}", vm_out[0].message);

    // 2. `Https.fake` MUST be statically rejected outside spec (`test`/`examples`/`promise`) blocks!
    let illegal_src = r#"
module IllegalFakeHttps

fn main() : Int
  api = Https.fake("api.example.com", responses: {})
  0
end
"#;
    let mut sm = SourceMap::new();
    let fid = sm.add_file("illegal.dana".to_string(), illegal_src.to_string());
    let ast = parse_module(fid, illegal_src).map_err(|d| render_diagnostic(&d, &sm))?;
    let diags = check_module(fid, ast, None, &sm)
        .err()
        .ok_or("expected Https.fake outside spec block to fail typecheck")?;
    assert!(
        diags.iter().any(|d| d.code() == DiagCode::CapabilityError),
        "expected CapabilityError, got: {diags:?}"
    );
    Ok(())
}

#[test]
fn single_table_write_xlsx_and_default_sheet_read_roundtrip_e2e() -> TestResult {
    let tmp = TempDir::new("single_xlsx")?;
    let dana_src = r#"
module SingleXlsxRoundtrip

schema Item
  sku: Text
  qty: Int where . > 0
  price: Decimal
end

fn main(files: ReadFiles, out: WriteFiles("exports/"), console: Console) : Int
  items = table
    | sku    | qty | price  |
    | "A-10" | 3   | 19.95  |
    | "B-20" | 7   | 105.00 |
  end
  try out.write_xlsx("catalog.xlsx", items)
  (loaded, bad) = try files.read_xlsx("exports/catalog.xlsx", as: Item)
  console.print("loaded=#{loaded.count()} bad=#{bad.count()}")
  0
end
"#;
    let prog = compile_source(dana_src, None)?;
    let cfg = RunConfig {
        work_dir: Some(tmp.path().to_path_buf()),
        ..RunConfig::default()
    };
    for (label, res) in [
        ("vm", run_exec_program_vm(&prog, &cfg, &VmConfig::default())),
        ("oracle", run_exec_program(&prog, &cfg)),
    ] {
        match res {
            RunResult::Ok {
                exit_code, stdout, ..
            } => {
                assert_eq!(exit_code, 0, "{label}");
                assert_eq!(stdout, vec!["loaded=2 bad=0".to_string()], "{label}");
            }
            other => return Err(format!("{label} failed: {other:?}").into()),
        }
    }
    Ok(())
}
