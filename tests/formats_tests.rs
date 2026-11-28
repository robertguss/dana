//! Phase 2B integration & property tests:
//! - Audited `src/ffi/` streaming gzip (`zlib`) & Zstandard (`libzstd`) codecs + error handling
//! - Pure-Rust FIPS 180-4 SHA-256 & RFC 2104 HMAC-SHA256 (RFC 4231 test vectors)
//! - RFC 8536 TZif v2/v3 parser, POSIX TZ post-2038 DST transitions, and `in_tz` / `date_in_tz`
//! - Streaming RFC 4180 CSV/TSV & iterative RFC 8259 JSON/JSONL quarantine codecs (plain, `.gz`, `.zst`)
//! - `dana infer-schema` and `dana fake` CLI end-to-end determinism & round-trip checks
//! - Review #3 follow-up checks (`Err` vs `Error` in `case`, bare `None` to `Option` parameter).

use std::fs::{self, File};
use std::io::{BufWriter, Cursor, Read, Write};
use std::path::PathBuf;

use dana::base::{DiagCode, SourceMap, render_diagnostic};
use dana::check::check_module;
use dana::core::bigint::BigInt;
use dana::core::syntax::{AggKind, ColSpec, Float64, ScalarTy, TableTy, TagSet};
use dana::ffi::{GzipReader, GzipWriter, ZstdReader, ZstdWriter};
use dana::formats::compress::{
    AutoDecodeReader, AutoEncodeWriter, CompressionKind, compress_bytes, decompress_bytes,
    detect_compression_magic, strip_compression_ext,
};
use dana::formats::crypto::{hmac_sha256, hmac_sha256_pseudonym, sha256, to_hex_lower};
use dana::formats::csv::{
    CSV_BATCH_SIZE, CsvBatchReader, parse_csv_records, read_csv_stream_with_schema,
};
use dana::formats::infer::{
    InferFormat, InferredTy, infer_schema_from_file, infer_schema_from_reader,
};
use dana::formats::json::{
    JsonValue, MAX_JSON_DEPTH, format_json_array_table, format_json_array_vm_table,
    format_jsonl_table, format_jsonl_vm_table, parse_json, parse_jsonl_with_schema,
    to_json_compact, write_jsonl_table,
};
use dana::formats::time::{
    format_iso_date, format_timestamp_in_tz, load_timezone, local_date_in_tz, parse_iso_timestamp,
};
use dana::lower::lower_program;
use dana::oracle::value::{TableRow, TableVal, Val, val_eq, val_list_eq};
use dana::runtime::{RunConfig, RunResult, run_exec_program, run_program_tests};
use dana::syntax::{format_module, parse_module};
use dana::vm::batch::table_to_batches;
use dana::vm::ops::VmTable;

fn repo_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

fn temp_test_dir(tag: &str) -> Result<PathBuf, String> {
    let dir = std::env::temp_dir().join(format!("dana_2b_{tag}_{}", std::process::id()));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).map_err(|e| e.to_string())?;
    Ok(dir)
}

#[test]
fn ffi_gzip_and_zstd_streaming_roundtrip_multiframe_and_corrupt_rejection() -> Result<(), String> {
    let payload_empty = b"".as_slice();
    let payload_small = b"hello dana streaming codecs 2026!\n".as_slice();
    let mut payload_large = Vec::with_capacity(260_000);
    for i in 0..10_000u32 {
        payload_large.extend_from_slice(format!("row,{i},value_{i:06},2026-10-01\n").as_bytes());
    }

    for (label, data) in [
        ("empty", payload_empty),
        ("small", payload_small),
        ("large_260k", payload_large.as_slice()),
    ] {
        let gz = compress_bytes(data, CompressionKind::Gzip).map_err(|e| e.to_string())?;
        assert_eq!(detect_compression_magic(&gz), CompressionKind::Gzip);
        let back_gz = decompress_bytes(&gz).map_err(|e| e.to_string())?;
        assert_eq!(back_gz.as_slice(), data, "gzip mismatch on {label}");

        let zst = compress_bytes(data, CompressionKind::Zstd).map_err(|e| e.to_string())?;
        assert_eq!(detect_compression_magic(&zst), CompressionKind::Zstd);
        let back_zst = decompress_bytes(&zst).map_err(|e| e.to_string())?;
        assert_eq!(back_zst.as_slice(), data, "zstd mismatch on {label}");
    }

    // Multi-member concatenated gzip stream
    let m1 = compress_bytes(b"first member\n", CompressionKind::Gzip).map_err(|e| e.to_string())?;
    let m2 =
        compress_bytes(b"second member\n", CompressionKind::Gzip).map_err(|e| e.to_string())?;
    let mut multi_gz = Vec::new();
    multi_gz.extend_from_slice(&m1);
    multi_gz.extend_from_slice(&m2);
    let multi_gz_out = decompress_bytes(&multi_gz).map_err(|e| e.to_string())?;
    assert_eq!(multi_gz_out, b"first member\nsecond member\n");

    // Multi-frame concatenated zstd stream
    let f1 = compress_bytes(b"frame one\n", CompressionKind::Zstd).map_err(|e| e.to_string())?;
    let f2 = compress_bytes(b"frame two\n", CompressionKind::Zstd).map_err(|e| e.to_string())?;
    let mut multi_zst = Vec::new();
    multi_zst.extend_from_slice(&f1);
    multi_zst.extend_from_slice(&f2);
    let multi_zst_out = decompress_bytes(&multi_zst).map_err(|e| e.to_string())?;
    assert_eq!(multi_zst_out, b"frame one\nframe two\n");

    // Truncated gzip must error
    let trunc_gz = &m1[..m1.len() - 4];
    let mut gz_r = GzipReader::new(Cursor::new(trunc_gz)).map_err(|e| e.to_string())?;
    let mut sink = Vec::new();
    assert!(
        gz_r.read_to_end(&mut sink).is_err(),
        "truncated gzip stream must return InvalidData"
    );

    // Corrupted CRC in gzip trailer must error
    let mut bad_crc_gz = m1.clone();
    let last_idx = bad_crc_gz.len() - 5;
    bad_crc_gz[last_idx] ^= 0xFF;
    let mut gz_r2 = GzipReader::new(Cursor::new(&bad_crc_gz)).map_err(|e| e.to_string())?;
    sink.clear();
    assert!(
        gz_r2.read_to_end(&mut sink).is_err(),
        "corrupt gzip CRC must return InvalidData"
    );

    // Truncated zstd frame must error
    let trunc_zst = &f1[..f1.len() - 3];
    let mut zst_r = ZstdReader::new(Cursor::new(trunc_zst)).map_err(|e| e.to_string())?;
    sink.clear();
    assert!(
        zst_r.read_to_end(&mut sink).is_err(),
        "truncated zstd frame must return InvalidData"
    );

    // Corrupt zstd payload must error
    let bad_zst = [0x28u8, 0xB5, 0x2F, 0xFD, 0xFF, 0xFF, 0xFF, 0xFF];
    let mut zst_r2 = ZstdReader::new(Cursor::new(&bad_zst)).map_err(|e| e.to_string())?;
    sink.clear();
    assert!(
        zst_r2.read_to_end(&mut sink).is_err(),
        "corrupt zstd payload must return InvalidData"
    );

    // Explicit flush + finish on GzipWriter / ZstdWriter
    let mut gw = GzipWriter::with_level(Vec::new(), 1).map_err(|e| e.to_string())?;
    gw.write_all(b"chunk-a").map_err(|e| e.to_string())?;
    gw.flush().map_err(|e| e.to_string())?;
    gw.write_all(b"-chunk-b").map_err(|e| e.to_string())?;
    let gbytes = gw.finish().map_err(|e| e.to_string())?;
    assert_eq!(
        decompress_bytes(&gbytes).map_err(|e| e.to_string())?,
        b"chunk-a-chunk-b"
    );

    let mut zw = ZstdWriter::with_level(Vec::new(), 1).map_err(|e| e.to_string())?;
    zw.write_all(b"chunk-x").map_err(|e| e.to_string())?;
    zw.flush().map_err(|e| e.to_string())?;
    zw.write_all(b"-chunk-y").map_err(|e| e.to_string())?;
    let zbytes = zw.finish().map_err(|e| e.to_string())?;
    assert_eq!(
        decompress_bytes(&zbytes).map_err(|e| e.to_string())?,
        b"chunk-x-chunk-y"
    );

    // Plain passthrough via AutoDecodeReader
    let mut plain_r =
        AutoDecodeReader::new(Cursor::new(b"plain text")).map_err(|e| e.to_string())?;
    assert_eq!(plain_r.kind(), CompressionKind::Plain);
    let mut plain_out = String::new();
    plain_r
        .read_to_string(&mut plain_out)
        .map_err(|e| e.to_string())?;
    assert_eq!(plain_out, "plain text");
    assert_eq!(strip_compression_ext("events.tsv.zst"), "events.tsv");
    assert_eq!(strip_compression_ext("logs.jsonl.gz"), "logs.jsonl");

    // 1-byte output buffer streaming drain test (catches premature EOF when decoder still holds buffered bytes!)
    let sample_4k = b"0123456789abcdef".repeat(256);
    let gz_4k = compress_bytes(&sample_4k, CompressionKind::Gzip).map_err(|e| e.to_string())?;
    let mut gz_1b = GzipReader::new(Cursor::new(&gz_4k)).map_err(|e| e.to_string())?;
    let mut out_1b = Vec::new();
    let mut byte = [0u8; 1];
    loop {
        let n = gz_1b.read(&mut byte).map_err(|e| e.to_string())?;
        if n == 0 {
            break;
        }
        out_1b.push(byte[0]);
    }
    assert_eq!(out_1b, sample_4k, "1-byte gzip drain mismatch");

    let zst_4k = compress_bytes(&sample_4k, CompressionKind::Zstd).map_err(|e| e.to_string())?;
    let mut zst_1b = ZstdReader::new(Cursor::new(&zst_4k)).map_err(|e| e.to_string())?;
    out_1b.clear();
    loop {
        let n = zst_1b.read(&mut byte).map_err(|e| e.to_string())?;
        if n == 0 {
            break;
        }
        out_1b.push(byte[0]);
    }
    assert_eq!(out_1b, sample_4k, "1-byte zstd drain mismatch");
    Ok(())
}

#[test]
fn sha256_and_rfc4231_hmac_sha256_vectors() {
    assert_eq!(
        to_hex_lower(&sha256(b"")),
        "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
    );
    assert_eq!(
        to_hex_lower(&sha256(b"abc")),
        "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
    );
    assert_eq!(
        to_hex_lower(&sha256(
            b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"
        )),
        "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"
    );

    // RFC 4231 Test Cases 1, 2, 3, 4, 6, 7
    assert_eq!(
        to_hex_lower(&hmac_sha256(&[0x0b; 20], b"Hi There")),
        "b0344c61d8db38535ca8afceaf0bf12b881dc200c9833da726e9376c2e32cff7"
    );
    assert_eq!(
        to_hex_lower(&hmac_sha256(b"Jefe", b"what do ya want for nothing?")),
        "5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843"
    );
    assert_eq!(
        to_hex_lower(&hmac_sha256(&[0xaa; 20], &[0xdd; 50])),
        "773ea91e36800e46854db8ebd09181a72959098b3ef8c122d9635514ced565fe"
    );
    let key4: Vec<u8> = (0x01u8..=0x19u8).collect();
    assert_eq!(
        to_hex_lower(&hmac_sha256(&key4, &[0xcd; 50])),
        "82558a389a443c0ea4cc819899f2083a85f0faa3e578f8077a2e3ff46729665b"
    );
    assert_eq!(
        to_hex_lower(&hmac_sha256(
            &[0xaa; 131],
            b"Test Using Larger Than Block-Size Key - Hash Key First"
        )),
        "60e431591ee0b67f0d8a26aacbf5b77f8e0bc6213728c5140546040f0ee37f54"
    );
    assert_eq!(
        to_hex_lower(&hmac_sha256(
            &[0xaa; 131],
            b"This is a test using a larger than block-size key and a larger than block-size data. The key needs to be hashed before being used by the HMAC algorithm."
        )),
        "9b09ffa71b942fcb27635fbcd5b0e944bfdc63644f0713938a7f51535c3a35e2"
    );

    let t1 = hmac_sha256_pseudonym(b"secret_k1", &Val::Text("alice@u.edu".into()));
    let t2 = hmac_sha256_pseudonym(b"secret_k1", &Val::Text("alice@u.edu".into()));
    let t3 = hmac_sha256_pseudonym(b"secret_k2", &Val::Text("alice@u.edu".into()));
    let t4 = hmac_sha256_pseudonym(b"secret_k1", &Val::Int(BigInt::from(42)));
    assert_eq!(t1, t2);
    assert_eq!(t1.len(), 3 + 32);
    assert!(t1.starts_with("ps_"));
    assert_ne!(t1, t3);
    assert_ne!(t1, t4);
}

#[test]
fn tzif_iana_timezones_dst_post2038_and_dana_in_tz() -> Result<(), String> {
    let jan_us = parse_iso_timestamp("2026-01-15T12:30:00Z").map_err(|e| e.message)?;
    assert_eq!(
        format_timestamp_in_tz(jan_us, "America/New_York").map_err(|e| e.message)?,
        "2026-01-15T07:30:00-05:00"
    );
    let jul_us = parse_iso_timestamp("2026-07-04T12:30:00Z").map_err(|e| e.message)?;
    assert_eq!(
        format_timestamp_in_tz(jul_us, "America/New_York").map_err(|e| e.message)?,
        "2026-07-04T08:30:00-04:00"
    );

    let before_dst = parse_iso_timestamp("2026-03-08T06:59:59Z").map_err(|e| e.message)?;
    let at_dst = parse_iso_timestamp("2026-03-08T07:00:00Z").map_err(|e| e.message)?;
    assert_eq!(
        format_timestamp_in_tz(before_dst, "America/New_York").map_err(|e| e.message)?,
        "2026-03-08T01:59:59-05:00"
    );
    assert_eq!(
        format_timestamp_in_tz(at_dst, "America/New_York").map_err(|e| e.message)?,
        "2026-03-08T03:00:00-04:00"
    );

    let late_utc = parse_iso_timestamp("2026-07-04T02:30:00Z").map_err(|e| e.message)?;
    assert_eq!(
        format_iso_date(local_date_in_tz(late_utc, "America/New_York").map_err(|e| e.message)?),
        "2026-07-03"
    );

    assert_eq!(
        format_timestamp_in_tz(jul_us, "Europe/Berlin").map_err(|e| e.message)?,
        "2026-07-04T14:30:00+02:00"
    );
    assert_eq!(
        format_timestamp_in_tz(jan_us, "Asia/Tokyo").map_err(|e| e.message)?,
        "2026-01-15T21:30:00+09:00"
    );
    assert_eq!(
        format_timestamp_in_tz(jan_us, "Australia/Sydney").map_err(|e| e.message)?,
        "2026-01-15T23:30:00+11:00"
    );
    assert_eq!(
        format_timestamp_in_tz(jul_us, "Australia/Sydney").map_err(|e| e.message)?,
        "2026-07-04T22:30:00+10:00"
    );

    // Post-2038 POSIX TZ footer rules
    let y2050_jan = parse_iso_timestamp("2050-01-15T12:00:00Z").map_err(|e| e.message)?;
    let y2050_jul = parse_iso_timestamp("2050-07-04T12:00:00Z").map_err(|e| e.message)?;
    assert_eq!(
        format_timestamp_in_tz(y2050_jan, "America/New_York").map_err(|e| e.message)?,
        "2050-01-15T07:00:00-05:00"
    );
    assert_eq!(
        format_timestamp_in_tz(y2050_jul, "America/New_York").map_err(|e| e.message)?,
        "2050-07-04T08:00:00-04:00"
    );
    assert_eq!(
        format_timestamp_in_tz(y2050_jan, "Australia/Sydney").map_err(|e| e.message)?,
        "2050-01-15T23:00:00+11:00"
    );
    assert_eq!(
        format_timestamp_in_tz(y2050_jul, "Australia/Sydney").map_err(|e| e.message)?,
        "2050-07-04T22:00:00+10:00"
    );

    // Path traversal / unknown timezone rejected
    assert!(load_timezone("../../etc/passwd").is_err());
    assert!(load_timezone("/etc/passwd").is_err());
    assert!(load_timezone("Mars/Olympus_Mons").is_err());

    let src = r#"
module TzTest

fn convert_table()
  events = table
    | id | at                     |
    | 1  | 2026-07-04T02:30:00Z   |
    | 2  | 2026-01-15T12:30:00Z   |
  end
  events
    |> derive(
      ny_text: .at.in_tz("America/New_York"),
      ny_day: .at.date_in_tz("America/New_York")
    )
end

test "in_tz and date_in_tz work in outer expressions and pipelines"
  ts = 2026-07-04T12:30:00Z
  assert ts.in_tz("America/New_York") == "2026-07-04T08:30:00-04:00"
  assert in_tz(ts, "UTC") == "2026-07-04T12:30:00Z"
  out = convert_table()
  assert out.first!.ny_text == "2026-07-03T22:30:00-04:00"
  assert out.first!.ny_day == 2026-07-03
end
"#;
    let mut sm = SourceMap::new();
    let fid = sm.add_file("tz_test.dana", src);
    let m = parse_module(fid, src).map_err(|d| render_diagnostic(&d, &sm))?;
    let checked = check_module(fid, m, None, &sm).map_err(|ds| format!("{ds:?}"))?;
    let lowered = lower_program(checked).map_err(|d| render_diagnostic(&d, &sm))?;
    let outcomes = run_program_tests(&lowered.exec, None, &RunConfig::default());
    assert_eq!(outcomes.len(), 1);
    assert!(outcomes[0].passed, "{:?}", outcomes[0].message);
    Ok(())
}

#[test]
fn streaming_csv_multibatch_multiline_and_compressed_io() -> Result<(), String> {
    let csv = "\u{FEFF}id,note,extra\r\n1,\"line1\nline2 with \"\"quotes\"\"\",\r\n2,plain,ok\r\n";
    let recs = parse_csv_records(csv, b',');
    assert_eq!(recs.len(), 3);
    assert_eq!(recs[0].line, 1);
    assert_eq!(recs[1].line, 2);
    assert_eq!(
        recs[1].fields,
        vec!["1", "line1\nline2 with \"quotes\"", ""]
    );
    assert_eq!(recs[2].line, 4);
    assert_eq!(recs[2].fields, vec!["2", "plain", "ok"]);

    let total_rows = CSV_BATCH_SIZE * 2 + 137;
    let mut buf = String::from("id,amount\n");
    for i in 1..=total_rows {
        if i == 100 || i == 3000 {
            buf.push_str(&format!("{i},not_a_decimal\n"));
        } else {
            buf.push_str(&format!("{i},{i}.25\n"));
        }
    }
    let zst_bytes =
        compress_bytes(buf.as_bytes(), CompressionKind::Zstd).map_err(|e| e.to_string())?;
    let schema = TableTy {
        cols: vec![
            ColSpec {
                name: "id".to_string(),
                ty: ScalarTy::Int,
                tags: TagSet::singleton("pii"),
                bucketed: false,
                agg_kind: AggKind::Raw,
            },
            ColSpec {
                name: "amount".to_string(),
                ty: ScalarTy::Decimal,
                tags: TagSet::empty(),
                bucketed: false,
                agg_kind: AggKind::Raw,
            },
        ],
        row_tags: TagSet::empty(),
        order_tags: TagSet::empty(),
        grouped_by: None,
        summarized: false,
        distinct_by: None,
    };
    let dec = AutoDecodeReader::new(Cursor::new(&zst_bytes)).map_err(|e| e.to_string())?;
    assert_eq!(dec.kind(), CompressionKind::Zstd);
    let (good, bad) = read_csv_stream_with_schema(dec, &schema, b',', |_, _| true)?;
    assert_eq!(good.rows.len(), total_rows - 2);
    assert_eq!(bad.rows.len(), 2);
    assert!(val_eq(&bad.rows[0].cells[0], &Val::Int(BigInt::from(101))));
    assert!(val_eq(
        &bad.rows[0].cells[2],
        &Val::Text("BadDecimal".to_string())
    ));
    assert!(val_eq(&bad.rows[1].cells[0], &Val::Int(BigInt::from(3001))));
    assert!(bad.cols[3].tags.contains("pii"));
    assert!(bad.cols[4].tags.contains("pii"));

    let mut br = CsvBatchReader::new(Cursor::new(buf.as_bytes()), b',');
    let hdr = br.next_record().map_err(|e| e.to_string())?;
    assert!(hdr.is_some());
    let b1 = br.next_batch(CSV_BATCH_SIZE).map_err(|e| e.to_string())?;
    let b2 = br.next_batch(CSV_BATCH_SIZE).map_err(|e| e.to_string())?;
    let b3 = br.next_batch(CSV_BATCH_SIZE).map_err(|e| e.to_string())?;
    assert_eq!(b1.len(), CSV_BATCH_SIZE);
    assert_eq!(b2.len(), CSV_BATCH_SIZE);
    assert_eq!(b3.len(), 137);
    Ok(())
}

#[test]
fn iterative_json_rfc8259_and_streaming_jsonl_quarantine() -> Result<(), String> {
    let j =
        parse_json(r#"{"emoji":"\uD83D\uDE00","price":12.50,"ok":true,"nil":null,"arr":[1,2]}"#)
            .map_err(|e| e.to_string())?;
    assert_eq!(j.get("emoji").and_then(JsonValue::as_str), Some("😀"));
    assert_eq!(
        j.get("price"),
        Some(&JsonValue::Number("12.50".to_string()))
    );
    let compact = to_json_compact(&j);
    let reparsed = parse_json(&compact).map_err(|e| e.to_string())?;
    assert_eq!(j, reparsed);

    for bad in [
        "01",
        "[1, 2,]",
        r#"{"a":1,}"#,
        "\"raw\nnewline\"",
        r#""\uD83D""#,
        r#""\uDC00""#,
        "123 trailing",
        "1.",
        "1e+",
    ] {
        assert!(parse_json(bad).is_err(), "expected JSON error on `{bad}`");
    }

    let deep = format!(
        "{}0{}",
        "[".repeat(MAX_JSON_DEPTH + 20),
        "]".repeat(MAX_JSON_DEPTH + 20)
    );
    assert!(parse_json(&deep).is_err());

    let schema = TableTy {
        cols: vec![
            ColSpec {
                name: "id".to_string(),
                ty: ScalarTy::Int,
                tags: TagSet::singleton("pii"),
                bucketed: false,
                agg_kind: AggKind::Raw,
            },
            ColSpec {
                name: "amount".to_string(),
                ty: ScalarTy::Decimal,
                tags: TagSet::empty(),
                bucketed: false,
                agg_kind: AggKind::Raw,
            },
            ColSpec {
                name: "note".to_string(),
                ty: ScalarTy::Option(Box::new(ScalarTy::Text)),
                tags: TagSet::empty(),
                bucketed: false,
                agg_kind: AggKind::Raw,
            },
        ],
        row_tags: TagSet::empty(),
        order_tags: TagSet::empty(),
        grouped_by: None,
        summarized: false,
        distinct_by: None,
    };
    let jsonl = "\
{\"id\":1,\"amount\":12.50,\"note\":\"ok\"}\n\
{broken json\n\
{\"id\":2,\"amount\":\"99.99\"}\n\
{\"id\":\"not_int\",\"amount\":5.00}\n\
{\"id\":3,\"amount\":-1.00}\n";
    let (good, bad) = parse_jsonl_with_schema(jsonl, &schema, |ci, val| {
        if ci == 1
            && let Val::Decimal(d) = val
        {
            return *d > BigInt::ZERO;
        }
        true
    })?;
    assert_eq!(good.rows.len(), 2);
    assert_eq!(bad.rows.len(), 3);
    assert!(val_eq(&bad.rows[0].cells[0], &Val::Int(BigInt::from(2))));
    assert!(val_eq(
        &bad.rows[0].cells[2],
        &Val::Text("BadJson".to_string())
    ));
    assert!(val_eq(&bad.rows[1].cells[0], &Val::Int(BigInt::from(4))));
    assert!(val_eq(
        &bad.rows[1].cells[2],
        &Val::Text("BadInt".to_string())
    ));
    assert!(val_eq(&bad.rows[2].cells[0], &Val::Int(BigInt::from(5))));
    assert!(val_eq(
        &bad.rows[2].cells[2],
        &Val::Text("ConstraintFailed".to_string())
    ));
    assert!(bad.cols[3].tags.contains("pii"));
    assert!(bad.cols[4].tags.contains("pii"));

    let mut written = Vec::new();
    write_jsonl_table(&mut written, &good).map_err(|e| e.to_string())?;
    let written_str = String::from_utf8(written).map_err(|e| e.to_string())?;
    let (good2, bad2) = parse_jsonl_with_schema(&written_str, &schema, |_, _| true)?;
    assert_eq!(bad2.rows.len(), 0);
    assert_eq!(good2.rows.len(), good.rows.len());
    for (r1, r2) in good2.rows.iter().zip(&good.rows) {
        assert!(val_list_eq(&r1.cells, &r2.cells));
    }
    Ok(())
}

#[test]
fn live_dana_program_reads_and_writes_compressed_jsonl_and_csv() -> Result<(), String> {
    let dir = temp_test_dir("live_jsonl")?;
    let in_jsonl_gz = dir.join("events.jsonl.gz");
    {
        let raw = "\
{\"day\":\"2026-10-01\",\"category\":\"food\",\"amount\":12.50}\n\
{\"day\":\"2026-10-02\",\"category\":\"food\",\"amount\":-5.00}\n\
{\"day\":\"2026-10-03\",\"category\":\"rent\",\"amount\":\"900.00\"}\n";
        let f = File::create(&in_jsonl_gz).map_err(|e| e.to_string())?;
        let mut enc = AutoEncodeWriter::new(BufWriter::new(f), CompressionKind::Gzip)
            .map_err(|e| e.to_string())?;
        enc.write_all(raw.as_bytes()).map_err(|e| e.to_string())?;
        enc.finish().map_err(|e| e.to_string())?;
    }

    let src = r#"
module JsonlLive

schema Event
  day: Date
  category: Text where not .empty?
  amount: Decimal where . > 0
end

fn main(args: Args, files: ReadFiles, out: WriteFiles("out/"), console: Console) : Int
  path = args.first.or_return(2)
  (rows, bad) = try files.read_jsonl(path, as: Event)
  summary = rows
    |> group_by(.category)
    |> summarize(total: sum(.amount), n: count())
    |> sort_desc(.total)
  try out.write_jsonl("summary.jsonl.zst", summary)
  try out.write_csv("summary.csv.gz", summary)
  console.print("bad=#{bad.count()}")
  0
end
"#;
    let mut sm = SourceMap::new();
    let fid = sm.add_file("jsonl_live.dana", src);
    let m = parse_module(fid, src).map_err(|d| render_diagnostic(&d, &sm))?;
    let checked = check_module(fid, m, None, &sm).map_err(|ds| format!("{ds:?}"))?;
    let lowered = lower_program(checked).map_err(|d| render_diagnostic(&d, &sm))?;

    let cfg = RunConfig {
        args: vec![in_jsonl_gz.display().to_string()],
        work_dir: Some(dir.clone()),
        live_io: true,
        ..RunConfig::default()
    };
    let res = run_exec_program(&lowered.exec, &cfg);
    match res {
        RunResult::Ok {
            exit_code, stdout, ..
        } => {
            assert_eq!(exit_code, 0);
            assert_eq!(stdout, vec!["bad=1".to_string()]);
        }
        other => return Err(format!("expected RunResult::Ok, got {other:?}")),
    }

    let out_zst_bytes = fs::read(dir.join("out/summary.jsonl.zst")).map_err(|e| e.to_string())?;
    assert_eq!(
        detect_compression_magic(&out_zst_bytes),
        CompressionKind::Zstd
    );
    let out_zst_text =
        String::from_utf8(decompress_bytes(&out_zst_bytes).map_err(|e| e.to_string())?)
            .map_err(|e| e.to_string())?;
    assert!(out_zst_text.contains("\"rent\"") && out_zst_text.contains("900.0"));

    let out_gz_bytes = fs::read(dir.join("out/summary.csv.gz")).map_err(|e| e.to_string())?;
    assert_eq!(
        detect_compression_magic(&out_gz_bytes),
        CompressionKind::Gzip
    );
    let out_gz_text =
        String::from_utf8(decompress_bytes(&out_gz_bytes).map_err(|e| e.to_string())?)
            .map_err(|e| e.to_string())?;
    assert!(out_gz_text.contains("category,total,n\nrent,900.0,1\nfood,12.5,1\n"));

    let _ = fs::remove_dir_all(&dir);
    Ok(())
}

#[test]
fn cli_fake_and_infer_schema_determinism_and_expenses_roundtrip() -> Result<(), String> {
    let dir = temp_test_dir("fake_infer")?;
    let exp_dana = repo_root().join("examples/expenses.dana");
    let fake_csv1 = dir.join("fake1.csv.gz");
    let fake_csv2 = dir.join("fake2.csv.gz");
    let fake_jsonl = dir.join("fake.jsonl.zst");

    let run_fake = |out: &PathBuf, seed: &str, fmt: &str| {
        dana::cli::run_cli(&[
            "fake".to_string(),
            exp_dana.display().to_string(),
            "--schema".to_string(),
            "Expense".to_string(),
            "--rows".to_string(),
            "250".to_string(),
            "--seed".to_string(),
            seed.to_string(),
            "--format".to_string(),
            fmt.to_string(),
            "--out".to_string(),
            out.display().to_string(),
        ])
    };
    assert_eq!(run_fake(&fake_csv1, "42", "csv"), 0);
    assert_eq!(run_fake(&fake_csv2, "42", "csv"), 0);
    assert_eq!(run_fake(&fake_jsonl, "42", "jsonl"), 0);

    let b1 = decompress_bytes(&fs::read(&fake_csv1).map_err(|e| e.to_string())?)
        .map_err(|e| e.to_string())?;
    let b2 = decompress_bytes(&fs::read(&fake_csv2).map_err(|e| e.to_string())?)
        .map_err(|e| e.to_string())?;
    assert_eq!(b1, b2, "same seed must produce identical fake rows");

    let rc_run = dana::cli::run_cli(&[
        "run".to_string(),
        exp_dana.display().to_string(),
        "--".to_string(),
        fake_csv1.display().to_string(),
    ]);
    assert_eq!(
        rc_run, 0,
        "fake expenses data must satisfy all schema where constraints (0 bad rows)"
    );

    let inf_csv = infer_schema_from_file(&fake_csv1, "InferredExpense", None, 1_000)?;
    assert_eq!(inf_csv.rows_sampled, 250);
    let dana_src = format!("module Inferred\n\n{}", inf_csv.render_dana());
    let mut sm = SourceMap::new();
    let fid = sm.add_file("inferred.dana", dana_src.clone());
    let parsed = parse_module(fid, &dana_src).map_err(|d| render_diagnostic(&d, &sm))?;
    assert_eq!(
        format_module(&parsed),
        dana_src,
        "infer-schema output must be canonically formatted Dana"
    );

    let inf_jsonl = infer_schema_from_file(&fake_jsonl, "InferredJsonl", None, 1_000)?;
    assert_eq!(inf_jsonl.rows_sampled, 250);
    assert_eq!(inf_jsonl.cols.len(), 3);

    let sample = "student_id,score,note\n101,10,\n102,12.5,hello\n";
    let inf_pii = infer_schema_from_reader(
        Cursor::new(sample.as_bytes()),
        "StudentRow",
        InferFormat::Csv,
        100,
    )?;
    let rendered = inf_pii.render_dana();
    assert!(
        rendered.contains("student_id: Int [pii]"),
        "expected PII hint:\n{rendered}"
    );
    assert!(
        rendered.contains("score: Decimal\n"),
        "expected Int+Decimal -> Decimal:\n{rendered}"
    );
    assert!(
        rendered.contains("note: Text?\n"),
        "expected nullable Text?:\n{rendered}"
    );

    assert_eq!(
        dana::cli::run_cli(&[
            "infer-schema".to_string(),
            fake_jsonl.display().to_string(),
            "--name".to_string(),
            "CliExpense".to_string(),
        ]),
        0
    );

    let _ = fs::remove_dir_all(&dir);
    Ok(())
}

#[test]
fn review3_followups_result_err_diagnostic_and_bare_none_arg() -> Result<(), String> {
    let bad_err = r#"
module BadErr
fn f(r: Result(Int, Text)) : Int
  case r
    Ok(v): v
    Err(_): 0
  end
end
"#;
    let mut sm = SourceMap::new();
    let fid = sm.add_file("bad_err.dana", bad_err);
    let m = parse_module(fid, bad_err).map_err(|d| render_diagnostic(&d, &sm))?;
    let Err(diags) = check_module(fid, m, None, &sm) else {
        return Err("expected TypeError on Err(...)".to_string());
    };
    assert!(
        diags.iter().any(|d| d.code() == DiagCode::TypeError),
        "expected E0201 TypeError, got {diags:?}"
    );

    let none_arg = r#"
module BareNoneArg
fn f(x: Int?) : Int
  x ?? 0
end
fn g() : Int
  f(None) + f(Some(4))
end
"#;
    let fid2 = sm.add_file("none_arg.dana", none_arg);
    let m2 = parse_module(fid2, none_arg).map_err(|d| render_diagnostic(&d, &sm))?;
    let checked2 = check_module(fid2, m2, None, &sm).map_err(|ds| format!("{ds:?}"))?;
    let lowered2 = lower_program(checked2).map_err(|d| render_diagnostic(&d, &sm))?;
    assert!(
        lowered2.verified_core.is_some(),
        "expected Core IR verification to succeed on f(None)"
    );
    Ok(())
}

#[test]
fn review2b_b1_b4_and_minor_regressions() -> Result<(), String> {
    // B1: Non-ASCII timestamp must NEVER panic; must quarantine cleanly in JSONL & CSV and infer as Text.
    assert!(parse_iso_timestamp("2026-01-01T00:00:0\u{00e9}Z").is_err());
    let bad_ts_csv = "ts\n2026-01-01T00:00:0\u{00e9}Z\n";
    let inf_bad_ts = infer_schema_from_reader(
        Cursor::new(bad_ts_csv.as_bytes()),
        "BadTs",
        InferFormat::Csv,
        100,
    )?;
    assert!(inf_bad_ts.render_dana().contains("ts: Text"));

    let ts_schema = TableTy {
        cols: vec![ColSpec {
            name: "at".to_string(),
            ty: ScalarTy::Timestamp,
            tags: TagSet::empty(),
            bucketed: false,
            agg_kind: AggKind::Raw,
        }],
        row_tags: TagSet::empty(),
        order_tags: TagSet::empty(),
        grouped_by: None,
        summarized: false,
        distinct_by: None,
    };
    let (g_ts, b_ts) = parse_jsonl_with_schema(
        "{\"at\":\"2026-01-01T00:00:0\u{00e9}Z\"}\n",
        &ts_schema,
        |_, _| true,
    )?;
    assert_eq!(g_ts.rows.len(), 0);
    assert_eq!(b_ts.rows.len(), 1);
    assert!(val_eq(
        &b_ts.rows[0].cells[2],
        &Val::Text("BadTimestamp".to_string())
    ));

    // B2: `dana fake` satisfies Float CSV, upper-bound-only Int, sub-cent Decimal, and `!=` in both CSV and JSONL!
    let dir = temp_test_dir("b2_fake")?;
    let schema_file = dir.join("constraints.dana");
    let schema_src = r#"
module FakeConstraints

schema Tight
  f: Float
  neg: Int where . < 0
  small: Int where . <= 0
  tiny: Decimal where . < 0.005
  nz: Int where . >= 0 and . <= 2 and . != 1
  raw: Bytes
end

fn main(args: Args, files: ReadFiles, console: Console) : Int
  path = args.first.or_return(2)
  (good, bad) = try files.read_csv(path, as: Tight)
  console.print("good=#{good.count()} bad=#{bad.count()}")
  if bad.count() > 0
    1
  else
    0
  end
end
"#;
    fs::write(&schema_file, schema_src).map_err(|e| e.to_string())?;
    let fake_csv = dir.join("tight.csv");
    let fake_jsonl = dir.join("tight.jsonl");
    assert_eq!(
        dana::cli::run_cli(&[
            "fake".to_string(),
            schema_file.display().to_string(),
            "--schema".to_string(),
            "Tight".to_string(),
            "--rows".to_string(),
            "25".to_string(),
            "--seed".to_string(),
            "3".to_string(),
            "--format".to_string(),
            "csv".to_string(),
            "--out".to_string(),
            fake_csv.display().to_string(),
        ]),
        0
    );
    assert_eq!(
        dana::cli::run_cli(&[
            "fake".to_string(),
            schema_file.display().to_string(),
            "--schema".to_string(),
            "Tight".to_string(),
            "--rows".to_string(),
            "25".to_string(),
            "--seed".to_string(),
            "3".to_string(),
            "--format".to_string(),
            "jsonl".to_string(),
            "--out".to_string(),
            fake_jsonl.display().to_string(),
        ]),
        0
    );
    assert_eq!(
        dana::cli::run_cli(&[
            "run".to_string(),
            schema_file.display().to_string(),
            "--".to_string(),
            fake_csv.display().to_string(),
        ]),
        0,
        "CSV fake rows must satisfy all Tight schema constraints"
    );

    // Also verify JSONL reading of the fake JSONL output passes 100% with 0 bad rows!
    let jsonl_check_src = r#"
module FakeConstraintsJsonl

schema Tight
  f: Float
  neg: Int where . < 0
  small: Int where . <= 0
  tiny: Decimal where . < 0.005
  nz: Int where . >= 0 and . <= 2 and . != 1
  raw: Bytes
end

fn main(args: Args, files: ReadFiles, console: Console) : Int
  path = args.first.or_return(2)
  (good, bad) = try files.read_jsonl(path, as: Tight)
  console.print("good=#{good.count()} bad=#{bad.count()}")
  if bad.count() > 0
    1
  else
    0
  end
end
"#;
    let jsonl_file = dir.join("constraints_jsonl.dana");
    fs::write(&jsonl_file, jsonl_check_src).map_err(|e| e.to_string())?;
    assert_eq!(
        dana::cli::run_cli(&[
            "run".to_string(),
            jsonl_file.display().to_string(),
            "--".to_string(),
            fake_jsonl.display().to_string(),
        ]),
        0,
        "JSONL fake rows must satisfy all Tight schema constraints"
    );

    // B3: `in_tz` / `date_in_tz` statically reject non-Timestamp / non-Text arguments across all call forms.
    for (name, bad_tz_src) in [
        (
            "row_method_non_ts",
            "module T\nschema S\n  name: Text\nend\nfn f(t: Table(S))\n  t |> derive(a: .name.in_tz(\"UTC\"))\nend\n",
        ),
        (
            "row_free_non_ts",
            "module T\nschema S\n  id: Int\nend\nfn f(t: Table(S))\n  t |> derive(b: in_tz(.id, \"UTC\"))\nend\n",
        ),
        (
            "outer_free_non_ts",
            "module T\nfn f() : Text\n  in_tz(5, \"UTC\")\nend\n",
        ),
        (
            "outer_pipe_non_ts",
            "module T\nfn f() : Text\n  5 |> in_tz(\"UTC\")\nend\n",
        ),
        (
            "outer_bad_zone_ty",
            "module T\nfn f(ts: Timestamp) : Text\n  ts.in_tz(123)\nend\n",
        ),
    ] {
        let mut sm = SourceMap::new();
        let fid = sm.add_file(format!("{name}.dana"), bad_tz_src);
        let m = parse_module(fid, bad_tz_src).map_err(|d| render_diagnostic(&d, &sm))?;
        let Err(diags) = check_module(fid, m, None, &sm) else {
            return Err(format!("B3 case `{name}` unexpectedly passed check_module"));
        };
        assert!(
            diags.iter().any(|d| d.code() == DiagCode::TypeError),
            "B3 case `{name}` expected E0201 TypeError, got {diags:?}"
        );
    }

    // B4 + Minor 9: Keyword column names sanitized & leading-zero codes stay Text; invalid `--name` exits 2.
    let kw_csv =
        "end,fn,schema,module,table,case,try,not,true,none,if,zip\n1,2,3,4,5,6,7,8,9,10,11,00123\n";
    let inf_kw = infer_schema_from_reader(
        Cursor::new(kw_csv.as_bytes()),
        "KwSafe",
        InferFormat::Csv,
        100,
    )?;
    let kw_dana = format!("module KwMod\n\n{}", inf_kw.render_dana());
    assert!(kw_dana.contains("end_col: Int"));
    assert!(kw_dana.contains("zip: Text"));
    let mut sm = SourceMap::new();
    let fid = sm.add_file("kw_safe.dana", kw_dana.clone());
    let parsed_kw = parse_module(fid, &kw_dana).map_err(|d| render_diagnostic(&d, &sm))?;
    assert_eq!(format_module(&parsed_kw), kw_dana);
    let _ = check_module(fid, parsed_kw, None, &sm).map_err(|ds| format!("{ds:?}"))?;

    let kw_csv_path = dir.join("kw.csv");
    fs::write(&kw_csv_path, kw_csv).map_err(|e| e.to_string())?;
    assert_eq!(
        dana::cli::run_cli(&[
            "infer-schema".to_string(),
            kw_csv_path.display().to_string(),
            "--name".to_string(),
            "bad name; drop".to_string(),
        ]),
        2,
        "invalid --name must be rejected with exit code 2"
    );

    // Minor 1: Pseudonym unwraps Option::Some cleanly and hashes actual Bytes contents (no length collision).
    let b_abc = hmac_sha256_pseudonym(b"k", &Val::OptSome(Box::new(Val::Bytes(b"abc".to_vec()))));
    let b_xyz = hmac_sha256_pseudonym(b"k", &Val::OptSome(Box::new(Val::Bytes(b"xyz".to_vec()))));
    assert_ne!(b_abc, b_xyz, "Some(Bytes) of equal length must not collide");
    let t_plain = hmac_sha256_pseudonym(b"k", &Val::Text("alice".to_string()));
    let t_opt = hmac_sha256_pseudonym(
        b"k",
        &Val::OptSome(Box::new(Val::Text("alice".to_string()))),
    );
    assert_eq!(t_plain, t_opt, "Text and Some(Text) must join identically");

    // Minor 2: Zstd frame checksum detects single-bit flips in Dana-written `.zst` payloads!
    let orig = b"deterministic zstd checksum verification payload 0123456789".repeat(32);
    let zst = compress_bytes(&orig, CompressionKind::Zstd).map_err(|e| e.to_string())?;
    for flip_pos in [zst.len() / 2, zst.len() - 2] {
        let mut flipped = zst.clone();
        flipped[flip_pos] ^= 0x01;
        assert!(
            decompress_bytes(&flipped).is_err(),
            "zstd checksum must detect single-bit flip at byte {flip_pos}"
        );
    }

    // Minor 4: Unterminated CSV quote returns error instead of swallowing rest of file.
    let unterm = "a,b\n\"x,2\n3,4\n";
    let two_col = TableTy {
        cols: vec![
            ColSpec {
                name: "a".to_string(),
                ty: ScalarTy::Text,
                tags: TagSet::empty(),
                bucketed: false,
                agg_kind: AggKind::Raw,
            },
            ColSpec {
                name: "b".to_string(),
                ty: ScalarTy::Text,
                tags: TagSet::empty(),
                bucketed: false,
                agg_kind: AggKind::Raw,
            },
        ],
        row_tags: TagSet::empty(),
        order_tags: TagSet::empty(),
        grouped_by: None,
        summarized: false,
        distinct_by: None,
    };
    assert!(
        read_csv_stream_with_schema(Cursor::new(unterm.as_bytes()), &two_col, b',', |_, _| true)
            .is_err(),
        "unterminated CSV quote must error"
    );

    // Minor 5: Single-column nullable CSV preserves empty `None` rows across write & read!
    let one_col = TableTy {
        cols: vec![ColSpec {
            name: "note".to_string(),
            ty: ScalarTy::Option(Box::new(ScalarTy::Text)),
            tags: TagSet::empty(),
            bucketed: false,
            agg_kind: AggKind::Raw,
        }],
        row_tags: TagSet::empty(),
        order_tags: TagSet::empty(),
        grouped_by: None,
        summarized: false,
        distinct_by: None,
    };
    let one_csv = "note\nhello\n\nworld\n";
    let (g1, b1) =
        read_csv_stream_with_schema(Cursor::new(one_csv.as_bytes()), &one_col, b',', |_, _| true)?;
    assert_eq!(b1.rows.len(), 0);
    assert_eq!(
        g1.rows.len(),
        3,
        "1-column nullable CSV must preserve None row"
    );
    assert!(val_eq(&g1.rows[1].cells[0], &Val::OptNone));

    // Minor 6: Sub-minute LMT timezone offset (1874 America/New_York = -04:56:02).
    let y1874 = parse_iso_timestamp("1874-06-01T12:00:00Z").map_err(|e| e.message)?;
    assert_eq!(
        format_timestamp_in_tz(y1874, "America/New_York").map_err(|e| e.message)?,
        "1874-06-01T07:03:58-04:56:02"
    );

    // Minor 8: Strict JSONL decimal rejects underscored strings like `"1_0"`.
    let dec_schema = TableTy {
        cols: vec![ColSpec {
            name: "v".to_string(),
            ty: ScalarTy::Decimal,
            tags: TagSet::empty(),
            bucketed: false,
            agg_kind: AggKind::Raw,
        }],
        row_tags: TagSet::empty(),
        order_tags: TagSet::empty(),
        grouped_by: None,
        summarized: false,
        distinct_by: None,
    };
    let (gd, bd) = parse_jsonl_with_schema("{\"v\":\"1_0\"}\n", &dec_schema, |_, _| true)?;
    assert_eq!(gd.rows.len(), 0);
    assert_eq!(bd.rows.len(), 1);
    assert!(val_eq(
        &bd.rows[0].cells[2],
        &Val::Text("BadDecimal".to_string())
    ));

    let _ = fs::remove_dir_all(&dir);
    Ok(())
}

#[test]
fn jsonl_and_json_array_preserve_dot_zero_on_integral_floats() -> Result<(), String> {
    let cols = vec![
        ColSpec {
            name: "id".to_string(),
            ty: ScalarTy::Int,
            tags: TagSet::empty(),
            bucketed: false,
            agg_kind: AggKind::Raw,
        },
        ColSpec {
            name: "elevation_m".to_string(),
            ty: ScalarTy::Option(Box::new(ScalarTy::Float)),
            tags: TagSet::empty(),
            bucketed: false,
            agg_kind: AggKind::Raw,
        },
    ];
    let tv = TableVal {
        cols: cols.clone(),
        rows: vec![
            TableRow {
                cells: vec![
                    Val::Int(BigInt::from(1)),
                    Val::OptSome(Box::new(Val::Float(Float64::from_f64(170.0)))),
                ],
                group_meta: None,
            },
            TableRow {
                cells: vec![
                    Val::Int(BigInt::from(2)),
                    Val::OptSome(Box::new(Val::Float(Float64::from_f64(-9999.0)))),
                ],
                group_meta: None,
            },
            TableRow {
                cells: vec![
                    Val::Int(BigInt::from(3)),
                    Val::OptSome(Box::new(Val::Float(Float64::from_f64(-0.0)))),
                ],
                group_meta: None,
            },
            TableRow {
                cells: vec![
                    Val::Int(BigInt::from(4)),
                    Val::OptSome(Box::new(Val::Float(Float64::from_f64(1.5)))),
                ],
                group_meta: None,
            },
        ],
    };
    let schema_tt = TableTy {
        cols: cols.clone(),
        row_tags: TagSet::empty(),
        order_tags: TagSet::empty(),
        grouped_by: None,
        summarized: false,
        distinct_by: None,
    };
    let vm = VmTable {
        cols,
        batches: table_to_batches(&tv, 64),
    };

    let jsonl_tv = format_jsonl_table(&tv);
    let jsonl_vm = format_jsonl_vm_table(&vm);
    assert_eq!(jsonl_tv, jsonl_vm);
    let expected_jsonl = "\
{\"id\":1,\"elevation_m\":170.0}
{\"id\":2,\"elevation_m\":-9999.0}
{\"id\":3,\"elevation_m\":0.0}
{\"id\":4,\"elevation_m\":1.5}
";
    assert_eq!(jsonl_tv, expected_jsonl);

    let arr_tv = format_json_array_table(&tv);
    let arr_vm = format_json_array_vm_table(&vm);
    assert_eq!(arr_tv, arr_vm);
    assert_eq!(
        arr_tv,
        "[{\"id\":1,\"elevation_m\":170.0},{\"id\":2,\"elevation_m\":-9999.0},{\"id\":3,\"elevation_m\":0.0},{\"id\":4,\"elevation_m\":1.5}]"
    );

    let inferred = infer_schema_from_reader(
        Cursor::new(jsonl_tv.as_bytes()),
        "GeoPoint",
        InferFormat::Jsonl,
        100,
    )?;
    assert_eq!(inferred.cols[0].ty, InferredTy::Int);
    assert_eq!(inferred.cols[1].ty, InferredTy::Decimal);
    let (roundtrip_good, roundtrip_bad) =
        parse_jsonl_with_schema(&jsonl_tv, &schema_tt, |_, _| true)?;
    assert_eq!(roundtrip_good.rows.len(), 4);
    assert!(roundtrip_bad.rows.is_empty());
    Ok(())
}
