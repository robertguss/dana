#![forbid(unsafe_code)]

//! Phase 5A — Zero-Crate 12-Parser Structure-Aware Mutation Fuzzer.
//!
//! Exercises all 12 untrusted parser boundaries in Dana inside bounded 2 MiB stack threads
//! using a deterministic seeded Xoshiro256++ PRNG mutator seeded from real in-memory corpus
//! artifacts:
//! 1. Dana Source Lexer, Parser & Canonical Formatter (with formatter idempotence check)
//! 2. Dana Core IR S-Expression Wire Parser, Verifier & Canonical Printer
//! 3. Policy (`dana.policy`), Lockfiles (`schema.lock`, `vendor.lock`) & DB URI Parsers
//! 4. CSV / TSV Quarantine Parser & Type-Lattice Schema Inference
//! 5. RFC 8259 JSON / JSONL Parser, Serializer & Dana Decoder
//! 6. ISO Date, ISO Timestamp, Fixed-Point Decimal & IANA TZif Parser
//! 7. Compression FFI (`GzipReader`, `ZstdReader`, `raw_inflate` bomb cap) & PKZIP
//! 8. Apache Parquet (Uncompressed, Gzip, Zstd, synthetic RLE_DICTIONARY + Snappy + DataPageV2)
//! 9. OOXML Excel `.xlsx` (multi-sheet, XXE/DTD rejection, zip-bomb & traversal rejection)
//! 10. HTTP/1.1 & HTTPS (`ParsedHttpsUrl`, `parse_http_response_from_reader` chunked/gzip/cap)
//! 11. PostgreSQL Wire Protocol v3.0 (`parse_pg_wire_frame`, `fuzz_decode_pg_payload`)
//! 12. Safe Interactive REPL Input Splitter & Evaluator (`ReplSession`)
//!
//! Iteration count is configurable via `DANA_FUZZ_ITERS` (default `2_500` per parser family ->
//! `30_000+` fuzzed inputs in fast CI; supports `DANA_FUZZ_ITERS=100000` for overnight soak).

use std::fs;
use std::io::{Cursor, Read, Write};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};
use std::thread;

use dana::base::FileId;
use dana::check::{
    VendorEntry, VendorLock, format_vendor_lock, parse_policy, parse_vendor_lock, sha256_hex,
};
use dana::core::{
    AggItem, AggKind, AggOp, BigInt, ColSpec, DeriveItem, Expr, Float64, FunDecl, FunKind, HostOp,
    JoinKind, JoinOn, LTy, Literal, Plan, PrimOp, Program, RowExpr, RowLit, ScalarTy, SortDir,
    SuppressMode, TableTy, TagSet, Ty, WindowFn, WindowItem, check_program, parse_canonical_sexp,
    parse_program, print_program,
};
use dana::db::postgres::{fuzz_decode_pg_payload, oid, parse_pg_wire_frame};
use dana::db::schema_lock::{
    LockedCol, LockedDb, LockedTable, SchemaLock, format_schema_lock, parse_schema_lock,
};
use dana::db::{DbUri, SqlDialect};
use dana::ffi::{GzipReader, GzipWriter, ZstdReader, ZstdWriter, raw_deflate, raw_inflate};
use dana::formats::csv::{format_csv_table, parse_csv_records, parse_csv_with_schema};
use dana::formats::infer::{InferFormat, infer_schema_from_reader};
use dana::formats::json::{
    format_jsonl_table, parse_json, parse_jsonl_with_schema, to_json_compact,
};
use dana::formats::parquet::{
    ParquetCompression, ParquetWriteOptions, infer_parquet_schema_from_bytes,
    read_parquet_bytes_with_schema, snappy_decompress, write_parquet_bytes_with_options,
};
use dana::formats::time::{
    TzData, days_from_civil, parse_decimal_bigint, parse_decimal_bigint_strict, parse_iso_date,
    parse_iso_timestamp,
};
use dana::formats::xlsx::{
    infer_xlsx_schema_from_bytes, read_xlsx_bytes_with_schema, write_xlsx_sheets,
};
use dana::formats::zip::{ZipArchive, ZipCompression, ZipLimits, write_zip_bytes};
use dana::net::{HttpsConfig, JsonResponse, ParsedHttpsUrl, parse_http_response_from_reader};
use dana::oracle::value::{TableRow, TableVal, Val};
use dana::repl::{ReplConfig, ReplSession};
use dana::syntax::{format_module, parse_fragment_bytes, parse_module, parse_module_bytes};

type TestResult<T = ()> = Result<T, Box<dyn std::error::Error>>;

const DEFAULT_FUZZ_ITERS: usize = 2_500;
const BOUNDED_STACK_BYTES: usize = 2 * 1024 * 1024;
const BASE_SEED: u64 = 0xDA4A_5A01_2026_0505;
const MAX_MUTATED_LEN: usize = 16 * 1024;

static TMP_SEQ: AtomicU64 = AtomicU64::new(1);

struct TempDir {
    path: PathBuf,
}

impl TempDir {
    fn new(prefix: &str) -> Result<Self, String> {
        let n = TMP_SEQ.fetch_add(1, Ordering::Relaxed);
        let path =
            std::env::temp_dir().join(format!("dana_fuzz_{prefix}_{}_{}", std::process::id(), n));
        if path.exists() {
            fs::remove_dir_all(&path).map_err(|e| format!("rm temp dir: {e}"))?;
        }
        fs::create_dir_all(&path).map_err(|e| format!("mkdir temp dir: {e}"))?;
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

fn fuzz_iters() -> usize {
    std::env::var("DANA_FUZZ_ITERS")
        .ok()
        .and_then(|s| s.trim().replace('_', "").parse::<usize>().ok())
        .filter(|&n| n > 0)
        .unwrap_or(DEFAULT_FUZZ_ITERS)
}

fn fuzz_base_seed() -> u64 {
    std::env::var("DANA_FUZZ_SEED")
        .ok()
        .and_then(|s| s.trim().parse::<u64>().ok())
        .unwrap_or(BASE_SEED)
}

fn repo_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

/// Run a fuzz harness on a dedicated thread with an explicit 2 MiB stack cap to prove zero
/// stack overflows, zero panics, and bounded recursion depth.
fn run_bounded_2mib<F>(name: &str, f: F) -> TestResult
where
    F: FnOnce() -> Result<String, String> + Send + 'static,
{
    let handle = thread::Builder::new()
        .name(format!("fuzz-{name}"))
        .stack_size(BOUNDED_STACK_BYTES)
        .spawn(f)?;
    match handle.join() {
        Ok(Ok(summary)) => {
            eprintln!("[fuzz/{name}] {summary}");
            Ok(())
        }
        Ok(Err(msg)) => Err(format!("fuzz/{name} failed: {msg}").into()),
        Err(payload) => {
            let detail = if let Some(s) = payload.downcast_ref::<&str>() {
                (*s).to_string()
            } else if let Some(s) = payload.downcast_ref::<String>() {
                s.clone()
            } else {
                "non-string panic payload".to_string()
            };
            Err(format!("fuzz/{name} PANICKED on 2 MiB stack: {detail}").into())
        }
    }
}

// ===========================================================================
// Deterministic Seeded Xoshiro256++ PRNG & Structure-Aware Mutator
// ===========================================================================

#[derive(Clone, Debug)]
struct Xoshiro256Pp {
    s: [u64; 4],
}

impl Xoshiro256Pp {
    fn from_seed(mut seed: u64) -> Self {
        let mut next_sm64 = || -> u64 {
            seed = seed.wrapping_add(0x9E37_79B9_7F4A_7C15);
            let mut z = seed;
            z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
            z ^ (z >> 31)
        };
        Self {
            s: [next_sm64(), next_sm64(), next_sm64(), next_sm64()],
        }
    }

    fn next_u64(&mut self) -> u64 {
        let result = self.s[0]
            .wrapping_add(self.s[3])
            .rotate_left(23)
            .wrapping_add(self.s[0]);
        let t = self.s[1] << 17;
        self.s[2] ^= self.s[0];
        self.s[3] ^= self.s[1];
        self.s[1] ^= self.s[2];
        self.s[0] ^= self.s[3];
        self.s[2] ^= t;
        self.s[3] = self.s[3].rotate_left(45);
        result
    }

    fn gen_usize(&mut self, bound: usize) -> usize {
        if bound <= 1 {
            0
        } else {
            (self.next_u64() as usize) % bound
        }
    }

    fn gen_u8(&mut self) -> u8 {
        (self.next_u64() & 0xFF) as u8
    }

    fn gen_bool(&mut self, num: usize, den: usize) -> bool {
        self.gen_usize(den) < num
    }
}

const MAGIC_I16: &[i16] = &[0, 1, -1, 127, 128, -128, i16::MIN, i16::MAX];
const MAGIC_I32: &[i32] = &[
    0,
    1,
    -1,
    2,
    4,
    255,
    256,
    65_535,
    65_536,
    i32::MIN,
    i32::MIN + 1,
    i32::MAX - 1,
    i32::MAX,
];
const MAGIC_U32: &[u32] = &[0, 1, 255, 65_535, 0x7FFF_FFFF, 0x8000_0000, u32::MAX];
const MAGIC_I64: &[i64] = &[
    0,
    1,
    -1,
    i64::MIN,
    i64::MIN + 1,
    i64::MAX - 1,
    i64::MAX,
    i32::MIN as i64,
    i32::MAX as i64,
];
const MAGIC_U64: &[u64] = &[0, 1, u32::MAX as u64, i64::MAX as u64, u64::MAX];

const MAGIC_ASCII_NUMS: &[&[u8]] = &[
    b"0",
    b"-0",
    b"-1",
    b"1",
    b"-32768",
    b"32767",
    b"65535",
    b"-2147483648",
    b"2147483647",
    b"4294967295",
    b"-9223372036854775808",
    b"9223372036854775807",
    b"18446744073709551615",
    b"99999999999999999999999999999999999999999",
    b"1e309",
    b"1e-99999",
    b"NaN",
    b"Infinity",
    b"-Infinity",
];

const INVALID_UTF8_SEQS: &[&[u8]] = &[
    &[0xFF],
    &[0xFE, 0xFF],
    &[0xC0, 0xAF],
    &[0xE0, 0x80, 0xAF],
    &[0xED, 0xA0, 0x80],
    &[0xF4, 0x90, 0x80, 0x80],
    &[0xC3],
    &[0xE2, 0x82],
    &[0xF0, 0x9F, 0x98],
    b"\xEF\xBB\xBF\x80\x81",
];

const ADVERSARIAL_PAYLOADS: &[&[u8]] = &[
    b"<!DOCTYPE foo [<!ENTITY xxe SYSTEM \"file:///etc/passwd\">]><root>&xxe;</root>",
    b"<!DOCTYPE lolz [<!ENTITY lol \"lol\"><!ENTITY lol2 \"&lol;&lol;&lol;&lol;\">]><a/>",
    b"../../../etc/passwd",
    b"/etc/passwd",
    b"C:\\Windows\\System32\\cmd.exe",
    b"\r\nTransfer-Encoding: chunked\r\nContent-Length: 999999999\r\n\r\n",
    b"\0\0\0\0\r\n\r\n",
    b"\\xdeadbeef0",
    b"2024-02-30T25:61:61.999999999+99:99",
];

/// Apply `1..=5` stacked structure-aware mutations to a corpus entry, drawing optional splices
/// from `corpus` and domain-specific dictionary tokens from `dict`.
fn mutate_bytes(
    rng: &mut Xoshiro256Pp,
    corpus: &[Vec<u8>],
    dict: &[&[u8]],
    iter: usize,
) -> Vec<u8> {
    if corpus.is_empty() {
        return Vec::new();
    }
    // First pass over raw unmutated corpus seeds guarantees valid corpus coverage.
    if iter < corpus.len() {
        return corpus[iter].clone();
    }
    let mut buf = corpus[rng.gen_usize(corpus.len())].clone();
    let rounds = 1 + rng.gen_usize(5);

    for _ in 0..rounds {
        let op = rng.gen_usize(15);
        match op {
            // 0: Single or multi-bit flip
            0 => {
                if !buf.is_empty() {
                    let pos = rng.gen_usize(buf.len());
                    let bits = 1 + rng.gen_usize(4);
                    for _ in 0..bits {
                        let bit = 1u8 << rng.gen_usize(8);
                        buf[pos] ^= bit;
                    }
                }
            }
            // 1: Random byte overwrite / arithmetic delta
            1 => {
                if !buf.is_empty() {
                    let pos = rng.gen_usize(buf.len());
                    if rng.gen_bool(1, 2) {
                        buf[pos] = rng.gen_u8();
                    } else {
                        let delta = (rng.gen_usize(33) as i16) - 16;
                        buf[pos] = buf[pos].wrapping_add(delta as u8);
                    }
                }
            }
            // 2: Insert random bytes
            2 => {
                let pos = rng.gen_usize(buf.len() + 1);
                let count = 1 + rng.gen_usize(16);
                let mut ins = Vec::with_capacity(count);
                for _ in 0..count {
                    ins.push(rng.gen_u8());
                }
                buf.splice(pos..pos, ins);
            }
            // 3: Delete random byte slice
            3 => {
                if !buf.is_empty() {
                    let start = rng.gen_usize(buf.len());
                    let max_del = (buf.len() - start).min(64);
                    let len = 1 + rng.gen_usize(max_del.max(1));
                    buf.drain(start..(start + len).min(buf.len()));
                }
            }
            // 4: Crossover / splice from another corpus seed
            4 => {
                let other = &corpus[rng.gen_usize(corpus.len())];
                if !other.is_empty() {
                    let o_start = rng.gen_usize(other.len());
                    let o_len = 1 + rng.gen_usize((other.len() - o_start).clamp(1, 128));
                    let slice = other[o_start..(o_start + o_len).min(other.len())].to_vec();
                    let pos = rng.gen_usize(buf.len() + 1);
                    if rng.gen_bool(1, 2) && pos < buf.len() {
                        let end = (pos + slice.len()).min(buf.len());
                        buf.splice(pos..end, slice);
                    } else {
                        buf.splice(pos..pos, slice);
                    }
                }
            }
            // 5: Inject binary magic boundary integer (BE or LE)
            5 => {
                let big_endian = rng.gen_bool(1, 2);
                let mut tmp = Vec::with_capacity(8);
                match rng.gen_usize(5) {
                    0 => {
                        let v = MAGIC_I16[rng.gen_usize(MAGIC_I16.len())];
                        tmp.extend_from_slice(&if big_endian {
                            v.to_be_bytes()
                        } else {
                            v.to_le_bytes()
                        });
                    }
                    1 => {
                        let v = MAGIC_I32[rng.gen_usize(MAGIC_I32.len())];
                        tmp.extend_from_slice(&if big_endian {
                            v.to_be_bytes()
                        } else {
                            v.to_le_bytes()
                        });
                    }
                    2 => {
                        let v = MAGIC_U32[rng.gen_usize(MAGIC_U32.len())];
                        tmp.extend_from_slice(&if big_endian {
                            v.to_be_bytes()
                        } else {
                            v.to_le_bytes()
                        });
                    }
                    3 => {
                        let v = MAGIC_I64[rng.gen_usize(MAGIC_I64.len())];
                        tmp.extend_from_slice(&if big_endian {
                            v.to_be_bytes()
                        } else {
                            v.to_le_bytes()
                        });
                    }
                    _ => {
                        let v = MAGIC_U64[rng.gen_usize(MAGIC_U64.len())];
                        tmp.extend_from_slice(&if big_endian {
                            v.to_be_bytes()
                        } else {
                            v.to_le_bytes()
                        });
                    }
                }
                if !buf.is_empty() && rng.gen_bool(2, 3) {
                    let pos = rng.gen_usize(buf.len());
                    let end = (pos + tmp.len()).min(buf.len());
                    buf.splice(pos..end, tmp);
                } else {
                    let pos = rng.gen_usize(buf.len() + 1);
                    buf.splice(pos..pos, tmp);
                }
            }
            // 6: Inject ASCII magic boundary integer
            6 => {
                let tok = MAGIC_ASCII_NUMS[rng.gen_usize(MAGIC_ASCII_NUMS.len())];
                let pos = rng.gen_usize(buf.len() + 1);
                buf.splice(pos..pos, tok.iter().copied());
            }
            // 7: Truncate (prefix or suffix, including mid-UTF-8-char boundaries)
            7 => {
                if !buf.is_empty() {
                    let cut = rng.gen_usize(buf.len());
                    if rng.gen_bool(2, 3) {
                        buf.truncate(cut);
                    } else {
                        buf.drain(..cut);
                    }
                }
            }
            // 8: Repetition / expansion burst (triggers buffer/header/bomb limits)
            8 => {
                if !buf.is_empty() {
                    let start = rng.gen_usize(buf.len());
                    let span = 1 + rng.gen_usize((buf.len() - start).clamp(1, 24));
                    let chunk = buf[start..(start + span).min(buf.len())].to_vec();
                    let reps = 2 + rng.gen_usize(40);
                    let pos = rng.gen_usize(buf.len() + 1);
                    let mut rep = Vec::with_capacity(chunk.len().saturating_mul(reps).min(2048));
                    for _ in 0..reps {
                        if rep.len() + chunk.len() > 2048 {
                            break;
                        }
                        rep.extend_from_slice(&chunk);
                    }
                    buf.splice(pos..pos, rep);
                }
            }
            // 9: Deep nesting generator (`[[[[...`, `((((...`, `{{{{...`, `<a<a>...`)
            9 => {
                let depth = 64 + rng.gen_usize(512);
                let mut nested = Vec::with_capacity(depth * 4);
                match rng.gen_usize(5) {
                    0 => {
                        nested.extend(std::iter::repeat_n(b'[', depth));
                        nested.extend(std::iter::repeat_n(b']', depth));
                    }
                    1 => {
                        nested.extend(std::iter::repeat_n(b'(', depth));
                        nested.push(b'1');
                        nested.extend(std::iter::repeat_n(b')', depth));
                    }
                    2 => {
                        for _ in 0..depth {
                            nested.extend_from_slice(b"{\"a\":");
                        }
                        nested.push(b'1');
                        nested.extend(std::iter::repeat_n(b'}', depth));
                    }
                    3 => {
                        for _ in 0..depth {
                            nested.extend_from_slice(b"<a>");
                        }
                        for _ in 0..depth {
                            nested.extend_from_slice(b"</a>");
                        }
                    }
                    _ => {
                        for _ in 0..depth.min(220) {
                            nested.extend_from_slice(b"if true\n");
                        }
                        nested.extend_from_slice(b"1\n");
                        for _ in 0..depth.min(220) {
                            nested.extend_from_slice(b"end\n");
                        }
                    }
                }
                if rng.gen_bool(1, 2) {
                    buf = nested;
                } else {
                    let pos = rng.gen_usize(buf.len() + 1);
                    buf.splice(pos..pos, nested);
                }
            }
            // 10: Invalid UTF-8 & mid-character boundary injection
            10 => {
                let bad = INVALID_UTF8_SEQS[rng.gen_usize(INVALID_UTF8_SEQS.len())];
                let pos = rng.gen_usize(buf.len() + 1);
                buf.splice(pos..pos, bad.iter().copied());
            }
            // 11: NUL & CRLF injection
            11 => {
                const INJECTS: &[&[u8]] = &[b"\0", b"\r\n", b"\r\n\r\n", b"\r", b"\n\0\r\n"];
                let tok = INJECTS[rng.gen_usize(INJECTS.len())];
                let pos = rng.gen_usize(buf.len() + 1);
                buf.splice(pos..pos, tok.iter().copied());
            }
            // 12: XXE / ZIP traversal / protocol smuggling payload splice
            12 => {
                let payload = ADVERSARIAL_PAYLOADS[rng.gen_usize(ADVERSARIAL_PAYLOADS.len())];
                let pos = rng.gen_usize(buf.len() + 1);
                buf.splice(pos..pos, payload.iter().copied());
            }
            // 13: Domain dictionary token splice
            13 => {
                if !dict.is_empty() {
                    let tok = dict[rng.gen_usize(dict.len())];
                    let pos = rng.gen_usize(buf.len() + 1);
                    buf.splice(pos..pos, tok.iter().copied());
                }
            }
            // 14: Swap two slices or duplicate a line
            _ => {
                if buf.len() >= 4 {
                    let a = rng.gen_usize(buf.len() - 1);
                    let b = rng.gen_usize(buf.len() - 1);
                    buf.swap(a, b);
                }
            }
        }
        if buf.len() > MAX_MUTATED_LEN {
            buf.truncate(MAX_MUTATED_LEN);
        }
    }
    buf
}

// ===========================================================================
// Shared Rich Schema & Corpus Builders
// ===========================================================================

fn col(name: &str, ty: ScalarTy, tags: &[&str]) -> ColSpec {
    ColSpec {
        name: name.to_string(),
        ty,
        tags: TagSet::of_list(tags.iter().map(|s| (*s).to_string()).collect()),
        bucketed: false,
        agg_kind: AggKind::Raw,
    }
}

fn rich_table_schema() -> TableTy {
    TableTy {
        cols: vec![
            col("id", ScalarTy::Int, &[]),
            col("email", ScalarTy::Text, &["pii"]),
            col("amount", ScalarTy::Decimal, &[]),
            col("score", ScalarTy::Float, &[]),
            col("active", ScalarTy::Bool, &[]),
            col("day", ScalarTy::Date, &[]),
            col("ts", ScalarTy::Timestamp, &[]),
            col("note", ScalarTy::Option(Box::new(ScalarTy::Text)), &[]),
        ],
        ..TableTy::default()
    }
}

fn rich_sample_table() -> TableVal {
    let schema = rich_table_schema();
    let d1 = days_from_civil(2025, 3, 15);
    let d2 = days_from_civil(2024, 2, 29);
    let dec1 = parse_decimal_bigint_strict("123.45").unwrap_or_else(|_| BigInt::from(0i64));
    let dec2 = parse_decimal_bigint_strict("-0.005").unwrap_or_else(|_| BigInt::from(0i64));
    TableVal {
        cols: schema.cols,
        rows: vec![
            TableRow {
                cells: vec![
                    Val::Int(BigInt::from(1i64)),
                    Val::Text("alice@uni.edu".to_string()),
                    Val::Decimal(dec1),
                    Val::Float(Float64::from_f64(98.5)),
                    Val::Bool(true),
                    Val::Date(BigInt::from(d1)),
                    Val::Timestamp(BigInt::from(1_742_000_000_123_456i64)),
                    Val::OptSome(Box::new(Val::Text("hello, \"world\"\nline2".to_string()))),
                ],
                group_meta: None,
            },
            TableRow {
                cells: vec![
                    Val::Int(BigInt::from(-42i64)),
                    Val::Text("bob@uni.edu".to_string()),
                    Val::Decimal(dec2),
                    Val::Float(Float64::from_f64(-1.25)),
                    Val::Bool(false),
                    Val::Date(BigInt::from(d2)),
                    Val::Timestamp(BigInt::from(0i64)),
                    Val::OptNone,
                ],
                group_meta: None,
            },
        ],
    }
}

fn build_valid_core_programs() -> Vec<Vec<u8>> {
    let base_cols = vec![
        col("dept", ScalarTy::Text, &[]),
        col("id", ScalarTy::Int, &[]),
        col("ssn", ScalarTy::Text, &["pii"]),
        col("val", ScalarTy::Int, &[]),
    ];
    let base_tt = TableTy {
        cols: base_cols.clone(),
        ..TableTy::default()
    };

    let lit_rows = vec![
        RowLit {
            cells: vec![
                Literal::Text("A".to_string()),
                Literal::Int(BigInt::from(1i64)),
                Literal::Text("111-11-1111".to_string()),
                Literal::Int(BigInt::from(10i64)),
            ],
        },
        RowLit {
            cells: vec![
                Literal::Text("A".to_string()),
                Literal::Int(BigInt::from(2i64)),
                Literal::Text("222-22-2222".to_string()),
                Literal::Int(BigInt::from(20i64)),
            ],
        },
    ];

    let base_plan = Plan::SourceExpr(Box::new(Expr::TableLit {
        schema: base_tt,
        rows: lit_rows,
    }));

    // Program 1: Filter -> Derive -> GroupBy -> Summarize -> SuppressSmallGroups -> ConsolePrintTable
    let p1_plan = Plan::SuppressSmallGroups {
        input: Box::new(Plan::Summarize {
            input: Box::new(Plan::GroupBy {
                input: Box::new(Plan::Derive {
                    input: Box::new(Plan::Filter {
                        input: Box::new(base_plan.clone()),
                        pred: RowExpr::Prim {
                            op: PrimOp::Gt,
                            args: vec![
                                RowExpr::Col("val".to_string()),
                                RowExpr::Lit(Literal::Int(BigInt::from(0i64))),
                            ],
                        },
                    }),
                    items: vec![DeriveItem::ColExpr {
                        name: "doubled".to_string(),
                        expr: Box::new(RowExpr::Prim {
                            op: PrimOp::MulInt,
                            args: vec![
                                RowExpr::Col("val".to_string()),
                                RowExpr::Lit(Literal::Int(BigInt::from(2i64))),
                            ],
                        }),
                    }],
                }),
                keys: vec!["dept".to_string()],
            }),
            aggs: vec![
                AggItem {
                    name: "n".to_string(),
                    op: AggOp::Count,
                    arg: None,
                },
                AggItem {
                    name: "total".to_string(),
                    op: AggOp::Sum,
                    arg: Some(RowExpr::Col("doubled".to_string())),
                },
            ],
            distinct_key: None,
        }),
        min_k: BigInt::from(5u64),
        distinct_by: None,
        mode: SuppressMode::Drop,
    };

    let prog1 = Program {
        funs: vec![FunDecl {
            name: "main".to_string(),
            kind: FunKind::Function,
            is_pure: false,
            params: vec![("c".to_string(), LTy::public(Ty::Console(TagSet::empty())))],
            pc: TagSet::empty(),
            ret: LTy::public(Ty::Unit),
            body: Expr::Host {
                op: HostOp::ConsolePrintTable,
                args: vec![Expr::Var("c".to_string()), Expr::Rel(Box::new(p1_plan))],
            },
        }],
        entry: Some("main".to_string()),
        ..Program::default()
    };

    // Program 2: Redact + Window + Sort + Limit + Join
    let right_tt = TableTy {
        cols: vec![
            col("id", ScalarTy::Int, &[]),
            col("label", ScalarTy::Text, &[]),
        ],
        ..TableTy::default()
    };
    let right_plan = Plan::SourceExpr(Box::new(Expr::TableLit {
        schema: right_tt,
        rows: vec![RowLit {
            cells: vec![
                Literal::Int(BigInt::from(1i64)),
                Literal::Text("ok".to_string()),
            ],
        }],
    }));
    let p2_plan = Plan::Limit {
        input: Box::new(Plan::Sort {
            input: Box::new(Plan::Window {
                input: Box::new(Plan::Join {
                    kind: JoinKind::LeftOne,
                    left: Box::new(Plan::Redact {
                        input: Box::new(base_plan),
                        col: "ssn".to_string(),
                        replacement: "[REDACTED]".to_string(),
                    }),
                    right: Box::new(right_plan),
                    on: JoinOn::SameKeys(vec!["id".to_string()]),
                    suffixes: Some(("_l".to_string(), "_r".to_string())),
                }),
                items: vec![WindowItem {
                    name: "rn".to_string(),
                    win_fn: WindowFn::RowNumber,
                    over: vec!["dept".to_string()],
                    order: vec![("id".to_string(), SortDir::Asc)],
                }],
            }),
            keys: vec![("id".to_string(), SortDir::Desc)],
        }),
        n: BigInt::from(10u64),
    };

    let prog2 = Program {
        funs: vec![FunDecl {
            name: "main".to_string(),
            kind: FunKind::Function,
            is_pure: false,
            params: vec![("c".to_string(), LTy::public(Ty::Console(TagSet::empty())))],
            pc: TagSet::empty(),
            ret: LTy::public(Ty::Unit),
            body: Expr::Host {
                op: HostOp::ConsolePrintTable,
                args: vec![Expr::Var("c".to_string()), Expr::Rel(Box::new(p2_plan))],
            },
        }],
        entry: Some("main".to_string()),
        ..Program::default()
    };

    vec![
        print_program(&prog1).into_bytes(),
        print_program(&prog2).into_bytes(),
    ]
}

fn build_valid_tzif_seeds() -> Vec<Vec<u8>> {
    let mut seeds = Vec::new();

    // Synthetic valid TZif v1 (version = 0) with 2 transitions & 2 local time types
    {
        let mut b = Vec::new();
        b.extend_from_slice(b"TZif");
        b.push(0); // v1
        b.extend_from_slice(&[0u8; 15]);
        b.extend_from_slice(&0u32.to_be_bytes()); // isutcnt
        b.extend_from_slice(&0u32.to_be_bytes()); // isstdcnt
        b.extend_from_slice(&0u32.to_be_bytes()); // leapcnt
        b.extend_from_slice(&2u32.to_be_bytes()); // timecnt
        b.extend_from_slice(&2u32.to_be_bytes()); // typecnt
        b.extend_from_slice(&8u32.to_be_bytes()); // charcnt
        // 2x i32 transitions
        b.extend_from_slice(&1_000_000i32.to_be_bytes());
        b.extend_from_slice(&2_000_000i32.to_be_bytes());
        // 2x type_indices
        b.extend_from_slice(&[0u8, 1u8]);
        // 2x ttinfo (6 bytes each: utoff i32, isdst u8, idx u8)
        b.extend_from_slice(&(-18_000i32).to_be_bytes());
        b.extend_from_slice(&[0u8, 0u8]);
        b.extend_from_slice(&(-14_400i32).to_be_bytes());
        b.extend_from_slice(&[1u8, 4u8]);
        // 8 bytes of abbreviations
        b.extend_from_slice(b"EST\0EDT\0");
        seeds.push(b);
    }

    // Synthetic valid TZif v2 (version = b'2') with v1 header + v2 64-bit block + POSIX footer
    {
        let mut b = Vec::new();
        // v1 header (1 type, 0 transitions)
        b.extend_from_slice(b"TZif2");
        b.extend_from_slice(&[0u8; 15]);
        b.extend_from_slice(&0u32.to_be_bytes()); // isutcnt
        b.extend_from_slice(&0u32.to_be_bytes()); // isstdcnt
        b.extend_from_slice(&0u32.to_be_bytes()); // leapcnt
        b.extend_from_slice(&0u32.to_be_bytes()); // timecnt
        b.extend_from_slice(&1u32.to_be_bytes()); // typecnt
        b.extend_from_slice(&4u32.to_be_bytes()); // charcnt
        b.extend_from_slice(&0i32.to_be_bytes());
        b.extend_from_slice(&[0u8, 0u8]);
        b.extend_from_slice(b"UTC\0");

        // v2 header (2 transitions, 2 types)
        b.extend_from_slice(b"TZif2");
        b.extend_from_slice(&[0u8; 15]);
        b.extend_from_slice(&0u32.to_be_bytes());
        b.extend_from_slice(&0u32.to_be_bytes());
        b.extend_from_slice(&0u32.to_be_bytes());
        b.extend_from_slice(&2u32.to_be_bytes()); // timecnt
        b.extend_from_slice(&2u32.to_be_bytes()); // typecnt
        b.extend_from_slice(&8u32.to_be_bytes()); // charcnt
        b.extend_from_slice(&1_700_000_000i64.to_be_bytes());
        b.extend_from_slice(&1_710_000_000i64.to_be_bytes());
        b.extend_from_slice(&[0u8, 1u8]);
        b.extend_from_slice(&(-18_000i32).to_be_bytes());
        b.extend_from_slice(&[0u8, 0u8]);
        b.extend_from_slice(&(-14_400i32).to_be_bytes());
        b.extend_from_slice(&[1u8, 4u8]);
        b.extend_from_slice(b"EST\0EDT\0");
        b.extend_from_slice(b"\nEST5EDT,M3.2.0,M11.1.0\n");
        seeds.push(b);
    }

    if let Ok(ny) = fs::read("/usr/share/zoneinfo/America/New_York") {
        seeds.push(ny);
    }
    if let Ok(utc) = fs::read("/usr/share/zoneinfo/UTC") {
        seeds.push(utc);
    }
    seeds
}

fn snappy_encode_seed(raw: &[u8]) -> Vec<u8> {
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
    let mut out = Vec::new();
    push_varint(&mut out, raw.len());
    if !raw.is_empty() {
        let n = raw.len() - 1;
        if n < 60 {
            out.push((n as u8) << 2);
        } else {
            out.push(60u8 << 2);
            out.push(n as u8);
        }
        out.extend_from_slice(raw);
    }
    out
}

fn build_synthetic_rle_dict_snappy_parquet() -> Vec<u8> {
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

    let mut w = Vec::new();
    w.extend_from_slice(b"PAR1");

    // Dictionary page: ["ENG", "OPS"]
    let mut dict_plain = Vec::new();
    for s in ["ENG", "OPS"] {
        dict_plain.extend_from_slice(&(s.len() as u32).to_le_bytes());
        dict_plain.extend_from_slice(s.as_bytes());
    }
    let dict_snappy = snappy_encode_seed(&dict_plain);
    let dict_off = w.len() as i64;
    let mut ph_dict = Vec::new();
    {
        let mut last = 0i16;
        t_fhdr(&mut ph_dict, &mut last, 1, 5);
        t_zz32(&mut ph_dict, 2); // DICTIONARY_PAGE
        t_fhdr(&mut ph_dict, &mut last, 2, 5);
        t_zz32(&mut ph_dict, dict_plain.len() as i32);
        t_fhdr(&mut ph_dict, &mut last, 3, 5);
        t_zz32(&mut ph_dict, dict_snappy.len() as i32);
        t_fhdr(&mut ph_dict, &mut last, 7, 12);
        let mut dl = 0i16;
        t_fhdr(&mut ph_dict, &mut dl, 1, 5);
        t_zz32(&mut ph_dict, 2);
        t_fhdr(&mut ph_dict, &mut dl, 2, 5);
        t_zz32(&mut ph_dict, 0);
        ph_dict.push(0);
        ph_dict.push(0);
    }
    w.extend_from_slice(&ph_dict);
    w.extend_from_slice(&dict_snappy);

    // DataPageV1: 3 rows ["ENG", None, "OPS"], RLE_DICTIONARY + SNAPPY
    let data_off = w.len() as i64;
    let def_rle = vec![(1u8 << 1) | 1, 0b0000_0101]; // [1, 0, 1]
    let dict_idx = vec![1u8, (1u8 << 1) | 1, 0b0000_0010]; // [0, 1]
    let mut page_uncomp = Vec::new();
    page_uncomp.extend_from_slice(&(def_rle.len() as u32).to_le_bytes());
    page_uncomp.extend_from_slice(&def_rle);
    page_uncomp.extend_from_slice(&dict_idx);
    let page_snappy = snappy_encode_seed(&page_uncomp);
    let mut ph_data = Vec::new();
    {
        let mut last = 0i16;
        t_fhdr(&mut ph_data, &mut last, 1, 5);
        t_zz32(&mut ph_data, 0); // DATA_PAGE
        t_fhdr(&mut ph_data, &mut last, 2, 5);
        t_zz32(&mut ph_data, page_uncomp.len() as i32);
        t_fhdr(&mut ph_data, &mut last, 3, 5);
        t_zz32(&mut ph_data, page_snappy.len() as i32);
        t_fhdr(&mut ph_data, &mut last, 5, 12);
        let mut dl = 0i16;
        t_fhdr(&mut ph_data, &mut dl, 1, 5);
        t_zz32(&mut ph_data, 3);
        t_fhdr(&mut ph_data, &mut dl, 2, 5);
        t_zz32(&mut ph_data, 8); // RLE_DICTIONARY
        t_fhdr(&mut ph_data, &mut dl, 3, 5);
        t_zz32(&mut ph_data, 3);
        t_fhdr(&mut ph_data, &mut dl, 4, 5);
        t_zz32(&mut ph_data, 3);
        ph_data.push(0);
        ph_data.push(0);
    }
    w.extend_from_slice(&ph_data);
    w.extend_from_slice(&page_snappy);
    let comp_total = (w.len() as i64) - dict_off;
    let uncomp_total =
        (ph_dict.len() + dict_plain.len() + ph_data.len() + page_uncomp.len()) as i64;

    // Minimal FileMetaData footer
    let mut fm = Vec::new();
    let mut fl = 0i16;
    t_fhdr(&mut fm, &mut fl, 1, 5);
    t_zz32(&mut fm, 2); // version
    t_fhdr(&mut fm, &mut fl, 2, 9); // schema list<SchemaElement>
    t_list(&mut fm, 12, 2);
    // Root element
    {
        let mut l = 0i16;
        t_fhdr(&mut fm, &mut l, 4, 8);
        t_str(&mut fm, "schema");
        t_fhdr(&mut fm, &mut l, 5, 5);
        t_zz32(&mut fm, 1);
        fm.push(0);
    }
    // Leaf column `dept` (BYTE_ARRAY, OPTIONAL, UTF8)
    {
        let mut l = 0i16;
        t_fhdr(&mut fm, &mut l, 1, 5);
        t_zz32(&mut fm, 6); // BYTE_ARRAY
        t_fhdr(&mut fm, &mut l, 3, 5);
        t_zz32(&mut fm, 1); // OPTIONAL
        t_fhdr(&mut fm, &mut l, 4, 8);
        t_str(&mut fm, "dept");
        t_fhdr(&mut fm, &mut l, 6, 5);
        t_zz32(&mut fm, 0); // UTF8
        fm.push(0);
    }
    t_fhdr(&mut fm, &mut fl, 3, 6);
    t_zz64(&mut fm, 3); // num_rows
    t_fhdr(&mut fm, &mut fl, 4, 9); // row_groups
    t_list(&mut fm, 12, 1);
    {
        let mut rgl = 0i16;
        t_fhdr(&mut fm, &mut rgl, 1, 9); // columns
        t_list(&mut fm, 12, 1);
        {
            let mut cl = 0i16;
            t_fhdr(&mut fm, &mut cl, 2, 6);
            t_zz64(&mut fm, dict_off);
            t_fhdr(&mut fm, &mut cl, 3, 12); // meta_data
            {
                let mut ml = 0i16;
                t_fhdr(&mut fm, &mut ml, 1, 5);
                t_zz32(&mut fm, 6); // BYTE_ARRAY
                t_fhdr(&mut fm, &mut ml, 2, 9);
                t_list(&mut fm, 5, 2);
                t_zz32(&mut fm, 2);
                t_zz32(&mut fm, 8);
                t_fhdr(&mut fm, &mut ml, 3, 9);
                t_list(&mut fm, 8, 1);
                t_str(&mut fm, "dept");
                t_fhdr(&mut fm, &mut ml, 4, 5);
                t_zz32(&mut fm, 1); // SNAPPY
                t_fhdr(&mut fm, &mut ml, 5, 6);
                t_zz64(&mut fm, 3);
                t_fhdr(&mut fm, &mut ml, 6, 6);
                t_zz64(&mut fm, uncomp_total);
                t_fhdr(&mut fm, &mut ml, 7, 6);
                t_zz64(&mut fm, comp_total);
                t_fhdr(&mut fm, &mut ml, 9, 6);
                t_zz64(&mut fm, data_off);
                t_fhdr(&mut fm, &mut ml, 11, 6);
                t_zz64(&mut fm, dict_off);
                fm.push(0);
            }
            fm.push(0);
        }
        t_fhdr(&mut fm, &mut rgl, 2, 6);
        t_zz64(&mut fm, uncomp_total);
        t_fhdr(&mut fm, &mut rgl, 3, 6);
        t_zz64(&mut fm, 3);
        fm.push(0);
    }
    fm.push(0);

    w.extend_from_slice(&fm);
    w.extend_from_slice(&(fm.len() as u32).to_le_bytes());
    w.extend_from_slice(b"PAR1");
    w
}

fn pg_frame(tag: u8, payload: &[u8]) -> Vec<u8> {
    let mut out = Vec::with_capacity(5 + payload.len());
    out.push(tag);
    out.extend_from_slice(&((payload.len() + 4) as i32).to_be_bytes());
    out.extend_from_slice(payload);
    out
}

fn gzip_bytes(raw: &[u8]) -> Result<Vec<u8>, String> {
    let mut w = GzipWriter::new(Vec::new()).map_err(|e| format!("gzip init: {e}"))?;
    w.write_all(raw).map_err(|e| format!("gzip write: {e}"))?;
    w.finish().map_err(|e| format!("gzip finish: {e}"))
}

fn zstd_bytes(raw: &[u8]) -> Result<Vec<u8>, String> {
    let mut w = ZstdWriter::new(Vec::new()).map_err(|e| format!("zstd init: {e}"))?;
    w.write_all(raw).map_err(|e| format!("zstd write: {e}"))?;
    w.finish().map_err(|e| format!("zstd finish: {e}"))
}

// ===========================================================================
// 1. Dana Source Lexer, Parser & Formatter Fuzzer
// ===========================================================================

#[test]
fn fuzz_01_dana_source_lexer_parser_formatter() -> TestResult {
    let iters = fuzz_iters();
    let seed = fuzz_base_seed().wrapping_add(1);
    run_bounded_2mib("01_dana_source", move || {
        let mut corpus: Vec<Vec<u8>> = Vec::new();
        let ex_dir = repo_root().join("examples");
        if let Ok(entries) = fs::read_dir(&ex_dir) {
            let mut paths: Vec<PathBuf> = entries
                .filter_map(Result::ok)
                .map(|e| e.path())
                .filter(|p| p.extension().and_then(|e| e.to_str()) == Some("dana"))
                .collect();
            paths.sort();
            for p in paths {
                if let Ok(bytes) = fs::read(&p) {
                    corpus.push(bytes);
                }
            }
        }
        corpus.push(
            br##"module Mini
tag secret
schema Row
  id: Int
  name: Text [pii]
  val: Decimal?
end
fn add(a: Int, b: Int) : Int
  if a > 0
    a + b
  else
    0
  end
end
fn main(console: Console) : Int
  x = add(1, 2)
  console.print("#{x}")
  0
end
"##
            .to_vec(),
        );
        corpus.push(
            br#"module Pipes
fn main(console: Console) : Int
  t = table
    | k   | v   |
    | "a" | 10  |
    | "b" | 20  |
  end
  r = t |> where(.v > 5) |> derive(w: .v * 2) |> sort_by(.w, :desc) |> limit(1)
  console.print_table(r)
  0
end
"#
            .to_vec(),
        );

        let dict: &[&[u8]] = &[
            b"module ",
            b"schema ",
            b"struct ",
            b"enum ",
            b"fn ",
            b"end\n",
            b"if ",
            b"else\n",
            b"case ",
            b"while ",
            b"for ",
            b" |> ",
            b"where(",
            b"derive(",
            b"summarize(",
            b"suppress_small_groups(",
            b"\"",
            b"\"\"\"",
            b"#{",
            b"}",
            b"??",
            b"->",
            b"[pii]",
        ];

        let mut rng = Xoshiro256Pp::from_seed(seed);
        let mut valid_parses = 0usize;
        let mut frag_parses = 0usize;
        for i in 0..iters {
            let input = mutate_bytes(&mut rng, &corpus, dict, i);
            if let Ok(m) = parse_module_bytes(FileId(0), &input) {
                valid_parses += 1;
                let fmt1 = format_module(&m);
                let m2 = parse_module(FileId(0), &fmt1).map_err(|d| {
                    format!(
                        "formatter broke parse on iter {i}: {}\n--- input ---\n{}\n--- fmt1 ---\n{fmt1}",
                        d.message(),
                        String::from_utf8_lossy(&input)
                    )
                })?;
                let fmt2 = format_module(&m2);
                if fmt1 != fmt2 {
                    return Err(format!(
                        "formatter not idempotent on iter {i}!\n--- fmt1 ---\n{fmt1}\n--- fmt2 ---\n{fmt2}"
                    ));
                }
            }
            if parse_fragment_bytes(FileId(0), &input).is_ok() {
                frag_parses += 1;
            }
        }
        Ok(format!(
            "iters={iters}, valid_module_parses={valid_parses} (100% formatter-idempotent), valid_fragment_parses={frag_parses}"
        ))
    })
}

// ===========================================================================
// 2. Dana Core IR S-Expression Wire Parser & Verifier Fuzzer
// ===========================================================================

#[test]
fn fuzz_02_core_ir_sexp_wire_and_verifier() -> TestResult {
    let iters = fuzz_iters();
    let seed = fuzz_base_seed().wrapping_add(2);
    run_bounded_2mib("02_core_ir", move || {
        let corpus = build_valid_core_programs();
        let dict: &[&[u8]] = &[
            b"(dana-core 0.1 ",
            b"(policy ",
            b"(funs ",
            b"(fun ",
            b"(rel ",
            b"(filter ",
            b"(join ",
            b"(group-by ",
            b"(summarize ",
            b"(suppress-small-groups ",
            b"(window ",
            b"(lit ",
            b"(prim ",
            b"(host ",
            b"(tags ",
            b"()",
            b"(",
            b")",
            b"\"\\u{0}\"",
        ];
        let mut rng = Xoshiro256Pp::from_seed(seed);
        let mut sexp_ok = 0usize;
        let mut prog_ok = 0usize;
        let mut checked_ok = 0usize;

        // Explicit deep S-exp nesting check on 2 MiB stack
        let deep = format!("{}{}", "(".repeat(1024), ")".repeat(1024));
        let _ = parse_canonical_sexp(&deep);
        let _ = parse_program(&deep);

        for i in 0..iters {
            let input = mutate_bytes(&mut rng, &corpus, dict, i);
            let s = String::from_utf8_lossy(&input);
            if parse_canonical_sexp(&s).is_ok() {
                sexp_ok += 1;
            }
            if let Ok(prog) = parse_program(&s) {
                prog_ok += 1;
                if check_program(&prog).is_ok() {
                    checked_ok += 1;
                }
                let printed = print_program(&prog);
                let reparsed = parse_program(&printed).map_err(|e| {
                    format!("Core IR print_program did not re-parse on iter {i}: {e}")
                })?;
                let printed2 = print_program(&reparsed);
                if printed != printed2 {
                    return Err(format!("Core IR print_program not canonical on iter {i}"));
                }
            }
        }
        Ok(format!(
            "iters={iters}, sexp_ok={sexp_ok}, prog_ok={prog_ok}, checked_ok={checked_ok}"
        ))
    })
}

// ===========================================================================
// 3. Policy, Lockfile & DB URI Parsers Fuzzer
// ===========================================================================

#[test]
fn fuzz_03_policy_lockfiles_and_db_uri() -> TestResult {
    let iters = fuzz_iters();
    let seed = fuzz_base_seed().wrapping_add(3);
    run_bounded_2mib("03_policy_locks_uri", move || {
        let mut corpus: Vec<Vec<u8>> = Vec::new();
        if let Ok(pol) = fs::read(repo_root().join("examples/dana.policy")) {
            corpus.push(pol);
        }
        let sample_lock = SchemaLock {
            version: 1,
            dbs: vec![LockedDb {
                name: "Analytics".to_string(),
                dialect: SqlDialect::Postgres,
                tables: vec![LockedTable {
                    name: "orders".to_string(),
                    cols: vec![
                        LockedCol {
                            name: "id".to_string(),
                            ty: ScalarTy::Int,
                            nullable: false,
                            pk: true,
                            tags: TagSet::empty(),
                        },
                        LockedCol {
                            name: "email".to_string(),
                            ty: ScalarTy::Text,
                            nullable: true,
                            pk: false,
                            tags: TagSet::of_list(vec!["pii".to_string()]),
                        },
                    ],
                }],
            }],
        };
        corpus.push(format_schema_lock(&sample_lock).into_bytes());

        let sample_vlock = VendorLock {
            version: 1,
            entries: vec![VendorEntry {
                module: "Vendor.Math".to_string(),
                path: "math.dana".to_string(),
                sha256: sha256_hex(b"module Vendor.Math\n"),
            }],
        };
        corpus.push(format_vendor_lock(&sample_vlock).into_bytes());

        for uri in [
            "sqlite::memory:",
            "sqlite:///tmp/test%20db.sqlite?mode=ro",
            "sqlite:relative.db?read_only=true",
            "postgres://alice:s3cr3t@localhost:5432/prod?sslmode=verify-full&connect_timeout=10",
            "postgresql://[::1]:5433/app?sslmode=disable",
        ] {
            corpus.push(uri.as_bytes().to_vec());
        }

        let dict: &[&[u8]] = &[
            b"version 1\n",
            b"min_group_size ",
            b"forbid manual_declassify\n",
            b"forbid repl_show_sensitive\n",
            b"allow console tags [pii]\n",
            b"allow export \"out/\" tags []\n",
            b"allow https \"api.example.com\" tags []\n",
            b"allow write Db.tbl tags [pii]\n",
            b"db Analytics dialect postgres\n",
            b"table \"orders\"\n",
            b"col id: Int? pk tags [pii]\n",
            b"end\n",
            b"module Vendor.Foo path \"../evil.dana\" sha256 \"",
            b"postgres://",
            b"sqlite://",
            b"?sslmode=verify-full",
            b"%2F%00%GG",
        ];

        let mut rng = Xoshiro256Pp::from_seed(seed);
        let (mut pol_ok, mut sl_ok, mut vl_ok, mut uri_ok) = (0usize, 0usize, 0usize, 0usize);

        // Verify credential redaction on rejected unknown schemes
        let bad_uri = DbUri::parse("mysql://admin:super_secret_pw@db.internal:3306/prod");
        match bad_uri {
            Err(e) => {
                if e.to_string().contains("super_secret_pw") {
                    return Err(format!("DbUri::parse leaked password in error: {e}"));
                }
            }
            Ok(_) => return Err("DbUri::parse unexpectedly accepted mysql://".to_string()),
        }

        for i in 0..iters {
            let input = mutate_bytes(&mut rng, &corpus, dict, i);
            let s = String::from_utf8_lossy(&input);
            if parse_policy(FileId(0), &s).is_ok() {
                pol_ok += 1;
            }
            if let Ok(lock) = parse_schema_lock(&s) {
                sl_ok += 1;
                let formatted = format_schema_lock(&lock);
                let _ = parse_schema_lock(&formatted).map_err(|e| {
                    format!("schema.lock roundtrip failed on iter {i}: {e}\n{formatted}")
                })?;
            }
            if let Ok(vlock) = parse_vendor_lock(&s) {
                vl_ok += 1;
                let formatted = format_vendor_lock(&vlock);
                let _ = parse_vendor_lock(&formatted).map_err(|e| {
                    format!("vendor.lock roundtrip failed on iter {i}: {e}\n{formatted}")
                })?;
            }
            if DbUri::parse(&s).is_ok() {
                uri_ok += 1;
            }
        }
        Ok(format!(
            "iters={iters}, policy_ok={pol_ok}, schema_lock_ok={sl_ok}, vendor_lock_ok={vl_ok}, db_uri_ok={uri_ok}"
        ))
    })
}

// ===========================================================================
// 4. CSV / TSV Quarantine Parser & Schema Inference Fuzzer
// ===========================================================================

#[test]
fn fuzz_04_csv_tsv_quarantine_and_inference() -> TestResult {
    let iters = fuzz_iters();
    let seed = fuzz_base_seed().wrapping_add(4);
    run_bounded_2mib("04_csv_tsv", move || {
        let tv = rich_sample_table();
        let schema = rich_table_schema();
        let csv_seed = format_csv_table(&tv, b',');
        let tsv_seed = format_csv_table(&tv, b'\t');
        let mut bom_seed = vec![0xEF, 0xBB, 0xBF];
        bom_seed.extend_from_slice(csv_seed.as_bytes());

        let corpus = vec![
            csv_seed.into_bytes(),
            tsv_seed.into_bytes(),
            bom_seed,
            b"id,email,amount,score,active,day,ts,note\n1,a@b,bad_dec,NaN,maybe,2024-02-30,bad_ts,\"unterminated".to_vec(),
            b"a,b,c\r\n\"x\"\"y\",\"line1\nline2\",3\r\n\r\n".to_vec(),
        ];
        let dict: &[&[u8]] = &[b",", b"\t", b"\"", b"\"\"", b"\r\n", b"\n", b"\xEF\xBB\xBF"];

        let mut rng = Xoshiro256Pp::from_seed(seed);
        let mut schema_ok = 0usize;
        for i in 0..iters {
            let input = mutate_bytes(&mut rng, &corpus, dict, i);
            let delim = if (i & 1) == 0 { b',' } else { b'\t' };
            let fmt = if delim == b',' {
                InferFormat::Csv
            } else {
                InferFormat::Tsv
            };
            let _ = infer_schema_from_reader(Cursor::new(&input), "FuzzCsv", fmt, 200);
            let s = String::from_utf8_lossy(&input);
            let _ = parse_csv_records(&s, delim);
            if let Ok((_good, bad)) = parse_csv_with_schema(&s, &schema, delim, |_, _| true) {
                schema_ok += 1;
                // Privacy invariant: bad_rows raw columns must retain schema's `pii` tag.
                let has_pii = bad
                    .cols
                    .iter()
                    .any(|c| c.name == "raw_line" && c.tags.elems().iter().any(|t| t == "pii"));
                if !has_pii {
                    return Err("CSV bad_rows lost `pii` sensitivity tag!".to_string());
                }
            }
        }
        Ok(format!("iters={iters}, schema_parsed={schema_ok}"))
    })
}

// ===========================================================================
// 5. JSON / JSONL Parser & Dana Decoder Fuzzer
// ===========================================================================

#[test]
fn fuzz_05_json_jsonl_parser_and_decoder() -> TestResult {
    let iters = fuzz_iters();
    let seed = fuzz_base_seed().wrapping_add(5);
    run_bounded_2mib("05_json_jsonl", move || {
        let tv = rich_sample_table();
        let schema = rich_table_schema();
        let jsonl_seed = format_jsonl_table(&tv);
        let corpus = vec![
            jsonl_seed.into_bytes(),
            br#"{"id":1,"email":"a@b.c","amount":12.34,"score":-1.5e2,"active":true,"day":"2025-01-01","ts":"2025-01-01T00:00:00Z","note":null}"#.to_vec(),
            br#"{"items":[{"id":1,"email":"x@y","amount":"1.00","score":0,"active":false,"day":"2024-02-29","ts":"2024-02-29T12:00:00Z","note":"\uD83D\uDE00"}],"meta":{"has_more":true,"cursor":"abc"}}"#.to_vec(),
            br#"[null,true,false,0,-0,1e-18,1e+18,"hello\n\t\"\\\/\b\f\u0041",{"a":[1,2,3]}]"#.to_vec(),
        ];
        let dict: &[&[u8]] = &[
            b"{",
            b"}",
            b"[",
            b"]",
            b":",
            b",",
            b"null",
            b"true",
            b"false",
            b"\"\\uD800\\uDC00\"",
            b"\"\\uD800\"",
            b"1e99999",
            b"-0.000000000000000001",
        ];

        // Explicit deep nesting checks on 2 MiB stack
        let deep_arr = format!("{}{}", "[".repeat(1024), "]".repeat(1024));
        if parse_json(&deep_arr).is_ok() {
            return Err(
                "parse_json accepted depth-1024 array exceeding MAX_JSON_DEPTH".to_string(),
            );
        }
        let deep_obj = format!("{}1{}", "{\"a\":".repeat(1024), "}".repeat(1024));
        if parse_json(&deep_obj).is_ok() {
            return Err(
                "parse_json accepted depth-1024 object exceeding MAX_JSON_DEPTH".to_string(),
            );
        }

        let mut rng = Xoshiro256Pp::from_seed(seed);
        let mut json_ok = 0usize;
        let mut jsonl_ok = 0usize;
        for i in 0..iters {
            let input = mutate_bytes(&mut rng, &corpus, dict, i);
            let _ =
                infer_schema_from_reader(Cursor::new(&input), "FuzzJsonl", InferFormat::Jsonl, 200);
            let s = String::from_utf8_lossy(&input);
            if let Ok(val) = parse_json(&s) {
                json_ok += 1;
                let compact = to_json_compact(&val);
                let _ = parse_json(&compact).map_err(|e| {
                    format!("to_json_compact produced unparseable JSON on iter {i}: {e}")
                })?;
                let resp = JsonResponse::from_value(val);
                let _ = resp.bool_at("meta.has_more");
                let _ = resp.text_at("meta.cursor");
                let _ = resp.int_at("id");
                let _ = resp.parse_table("items", &schema, |_, _| true);
            }
            if let Ok((_good, bad)) = parse_jsonl_with_schema(&s, &schema, |_, _| true) {
                jsonl_ok += 1;
                let has_pii = bad
                    .cols
                    .iter()
                    .any(|c| c.name == "raw_line" && c.tags.elems().iter().any(|t| t == "pii"));
                if !has_pii {
                    return Err("JSONL bad_rows lost `pii` sensitivity tag!".to_string());
                }
            }
        }
        Ok(format!(
            "iters={iters}, json_ok={json_ok}, jsonl_ok={jsonl_ok}"
        ))
    })
}

// ===========================================================================
// 6. Date, Timestamp, Decimal & IANA TZif Parser Fuzzer
// ===========================================================================

#[test]
fn fuzz_06_temporal_decimal_and_tzif() -> TestResult {
    let iters = fuzz_iters();
    let seed = fuzz_base_seed().wrapping_add(6);
    run_bounded_2mib("06_time_decimal_tzif", move || {
        let mut corpus = build_valid_tzif_seeds();
        for s in [
            "1970-01-01",
            "2024-02-29",
            "0001-01-01",
            "9999-12-31",
            "2024-02-29T23:59:59.999999Z",
            "2025-07-04T12:30:00.123456+05:30",
            "2025-07-04 12:30:00-08:00",
            "0",
            "-0.000000000000000001",
            "99999999999999999999.999999999999999999",
            "-99999999999999999999.999999999999999999",
            "123_456.789",
        ] {
            corpus.push(s.as_bytes().to_vec());
        }
        let dict: &[&[u8]] = &[
            b"TZif",
            b"TZif2",
            b"TZif3",
            b"\nEST5EDT,M3.2.0,M11.1.0\n",
            b"\n<+0530>-5:30\n",
            b"\nFOO-2147483648\n",
            b"T",
            b"Z",
            b"+00:00",
            b"-23:59",
            b".999999999",
        ];

        let mut rng = Xoshiro256Pp::from_seed(seed);
        let (mut d_ok, mut ts_ok, mut dec_ok, mut tz_ok) = (0usize, 0usize, 0usize, 0usize);
        for i in 0..iters {
            let input = mutate_bytes(&mut rng, &corpus, dict, i);
            if let Ok(tz) = TzData::parse(&input) {
                tz_ok += 1;
                let _ = tz.offset_secs_at_unix_secs(0);
                let _ = tz.offset_secs_at_unix_secs(1_700_000_000);
                let _ = tz.offset_secs_at_unix_secs(2_500_000_000);
                let _ = tz.offset_secs_at(1_700_000_000_000_000);
            }
            let s = String::from_utf8_lossy(&input);
            if parse_iso_date(&s).is_ok() {
                d_ok += 1;
            }
            if parse_iso_timestamp(&s).is_ok() {
                ts_ok += 1;
            }
            if parse_decimal_bigint_strict(&s).is_ok() {
                dec_ok += 1;
            }
            let _ = parse_decimal_bigint(&s);
        }
        Ok(format!(
            "iters={iters}, date_ok={d_ok}, ts_ok={ts_ok}, dec_ok={dec_ok}, tzif_ok={tz_ok}"
        ))
    })
}

// ===========================================================================
// 7. Compression FFI (`GzipReader`, `ZstdReader`, `raw_inflate`) & PKZIP Fuzzer
// ===========================================================================

#[test]
fn fuzz_07_compression_ffi_and_pkzip() -> TestResult {
    let iters = fuzz_iters();
    let seed = fuzz_base_seed().wrapping_add(7);
    run_bounded_2mib("07_compression_pkzip", move || {
        let sample = b"Dana compression and PKZIP fuzzing seed payload repeated repeated repeated!";
        let gz_seed = gzip_bytes(sample)?;
        let zst_seed = zstd_bytes(sample)?;
        let raw_def_seed = raw_deflate(sample).map_err(|e| format!("raw_deflate seed: {e}"))?;
        let zip_seed = write_zip_bytes(
            &[
                ("hello.txt", sample.as_slice()),
                ("nested/data.txt", sample.as_slice()),
            ],
            ZipCompression::Deflated,
        )
        .map_err(|e| format!("zip seed: {e}"))?;

        // Explicit decompression bomb (512 KiB of zeroes -> tiny compressed blob)
        let zeros = vec![0u8; 512 * 1024];
        let raw_bomb = raw_deflate(&zeros).map_err(|e| format!("raw_deflate bomb: {e}"))?;
        if raw_inflate(&raw_bomb, 16 * 1024).is_ok() {
            return Err(
                "raw_inflate failed to reject 512 KiB bomb against 16 KiB limit".to_string(),
            );
        }
        let zip_bomb = write_zip_bytes(&[("bomb.bin", zeros.as_slice())], ZipCompression::Deflated)
            .map_err(|e| format!("zip bomb: {e}"))?;
        let tight_limits = ZipLimits {
            max_entry_bytes: 32 * 1024,
            max_total_bytes: 64 * 1024,
            max_entries: 32,
        };
        if ZipArchive::from_bytes_with_limits(&zip_bomb, tight_limits).is_ok() {
            return Err("ZipArchive failed to reject zip bomb exceeding limits".to_string());
        }

        // Explicit path traversal ZIP check: mutate valid ZIP entry name to `../evil`
        let mut trav_zip =
            write_zip_bytes(&[("aaaaaaa.txt", b"x".as_slice())], ZipCompression::Stored)
                .map_err(|e| format!("trav zip: {e}"))?;
        for w in 0..trav_zip.len().saturating_sub(11) {
            if &trav_zip[w..w + 11] == b"aaaaaaa.txt" {
                trav_zip[w..w + 11].copy_from_slice(b"../evil.txt");
            }
        }
        if ZipArchive::from_bytes_with_limits(&trav_zip, tight_limits).is_ok() {
            return Err("ZipArchive accepted `../evil.txt` path traversal entry!".to_string());
        }

        let corpus = vec![
            gz_seed,
            zst_seed,
            raw_def_seed,
            zip_seed,
            raw_bomb,
            zip_bomb,
            trav_zip,
        ];
        let dict: &[&[u8]] = &[
            &[0x1F, 0x8B, 0x08, 0x00],
            &[0x28, 0xB5, 0x2F, 0xFD],
            b"PK\x03\x04",
            b"PK\x01\x02",
            b"PK\x05\x06",
            b"../evil",
        ];

        let mut rng = Xoshiro256Pp::from_seed(seed);
        let (mut gz_ok, mut zst_ok, mut inf_ok, mut zip_ok) = (0usize, 0usize, 0usize, 0usize);
        for i in 0..iters {
            let input = mutate_bytes(&mut rng, &corpus, dict, i);

            if let Ok(gz) = GzipReader::new(Cursor::new(&input)) {
                let mut out = Vec::new();
                if gz.take(32 * 1024).read_to_end(&mut out).is_ok() {
                    gz_ok += 1;
                }
            }
            if let Ok(zst) = ZstdReader::new(Cursor::new(&input)) {
                let mut out = Vec::new();
                if zst.take(32 * 1024).read_to_end(&mut out).is_ok() {
                    zst_ok += 1;
                }
            }
            if raw_inflate(&input, 32 * 1024).is_ok() {
                inf_ok += 1;
            }
            if ZipArchive::from_bytes_with_limits(&input, tight_limits).is_ok() {
                zip_ok += 1;
            }
        }
        Ok(format!(
            "iters={iters}, gz_ok={gz_ok}, zst_ok={zst_ok}, raw_inflate_ok={inf_ok}, zip_ok={zip_ok}"
        ))
    })
}

// ===========================================================================
// 8. Apache Parquet Fuzzer
// ===========================================================================

#[test]
fn fuzz_08_apache_parquet_and_snappy() -> TestResult {
    let iters = fuzz_iters();
    let seed = fuzz_base_seed().wrapping_add(8);
    run_bounded_2mib("08_parquet", move || {
        let tv = rich_sample_table();
        let schema = rich_table_schema();
        let dept_schema = TableTy {
            cols: vec![col("dept", ScalarTy::Option(Box::new(ScalarTy::Text)), &[])],
            ..TableTy::default()
        };

        let pq_uncomp = write_parquet_bytes_with_options(
            &tv,
            ParquetWriteOptions {
                compression: ParquetCompression::Uncompressed,
                row_group_rows: 1,
            },
        )?;
        let pq_gzip = write_parquet_bytes_with_options(
            &tv,
            ParquetWriteOptions {
                compression: ParquetCompression::Gzip,
                row_group_rows: 2,
            },
        )?;
        let pq_zstd = write_parquet_bytes_with_options(
            &tv,
            ParquetWriteOptions {
                compression: ParquetCompression::Zstd,
                row_group_rows: 2,
            },
        )?;
        let pq_dict_snappy = build_synthetic_rle_dict_snappy_parquet();
        // Verify synthetic RLE_DICTIONARY + Snappy seed parses validly before fuzzing!
        let parsed_syn = read_parquet_bytes_with_schema(&pq_dict_snappy, &dept_schema, |_, _| true)
            .map_err(|e| format!("synthetic RLE_DICTIONARY+Snappy seed failed: {e}"))?;
        if parsed_syn.rows.len() != 3 {
            return Err(format!(
                "synthetic Parquet seed expected 3 rows, got {}",
                parsed_syn.rows.len()
            ));
        }

        // Valid Snappy RLE overlapping copy seed ("ABABABAB")
        let snappy_rle = vec![8u8, 1u8 << 2, b'A', b'B', ((6u8 - 4) << 2) | 1, 2u8];
        let corpus = vec![pq_uncomp, pq_gzip, pq_zstd, pq_dict_snappy, snappy_rle];
        let dict: &[&[u8]] = &[
            b"PAR1",
            &[0xFF, 0xFF, 0xFF, 0x7F],
            &[0x80, 0x80, 0x80, 0x80, 0x08],
        ];

        let mut rng = Xoshiro256Pp::from_seed(seed);
        let (mut read_ok, mut infer_ok, mut snappy_ok) = (0usize, 0usize, 0usize);
        for i in 0..iters {
            let input = mutate_bytes(&mut rng, &corpus, dict, i);
            if read_parquet_bytes_with_schema(&input, &schema, |_, _| true).is_ok() {
                read_ok += 1;
            }
            if read_parquet_bytes_with_schema(&input, &dept_schema, |_, _| true).is_ok() {
                read_ok += 1;
            }
            if infer_parquet_schema_from_bytes(&input, "FuzzPq").is_ok() {
                infer_ok += 1;
            }
            if snappy_decompress(&input, 64 * 1024).is_ok() {
                snappy_ok += 1;
            }
        }
        Ok(format!(
            "iters={iters}, read_ok={read_ok}, infer_ok={infer_ok}, snappy_ok={snappy_ok}"
        ))
    })
}

// ===========================================================================
// 9. OOXML Excel `.xlsx` Fuzzer (including XXE/DTD & zip-bomb rejection)
// ===========================================================================

#[test]
fn fuzz_09_ooxml_xlsx_and_xxe() -> TestResult {
    let iters = fuzz_iters();
    let seed = fuzz_base_seed().wrapping_add(9);
    run_bounded_2mib("09_xlsx", move || {
        let tv = rich_sample_table();
        let schema = rich_table_schema();
        let valid_xlsx = write_xlsx_sheets(&[("Sheet1".to_string(), tv.clone())])?;

        // Build explicit XXE workbook seed and assert hard rejection
        let xxe_xlsx = write_zip_bytes(
            &[
                (
                    "xl/workbook.xml",
                    br#"<?xml version="1.0"?><!DOCTYPE foo [<!ENTITY xxe SYSTEM "file:///etc/passwd">]><workbook><sheets><sheet name="Sheet1" sheetId="1" r:id="rId1"/></sheets></workbook>"#.as_slice(),
                ),
                (
                    "xl/_rels/workbook.xml.rels",
                    br#"<?xml version="1.0"?><Relationships><Relationship Id="rId1" Target="worksheets/sheet1.xml"/></Relationships>"#.as_slice(),
                ),
                (
                    "xl/worksheets/sheet1.xml",
                    br#"<?xml version="1.0"?><worksheet><sheetData/></worksheet>"#.as_slice(),
                ),
            ],
            ZipCompression::Deflated,
        )
        .map_err(|e| format!("xxe xlsx seed: {e}"))?;
        if read_xlsx_bytes_with_schema(&xxe_xlsx, None, &schema, |_, _| true).is_ok() {
            return Err("XLSX reader accepted XML containing <!DOCTYPE/<!ENTITY XXE!".to_string());
        }

        // Build explicit entity-expansion / sheet XXE seed and assert hard rejection
        let sheet_xxe_xlsx = write_zip_bytes(
            &[
                (
                    "xl/workbook.xml",
                    br#"<?xml version="1.0"?><workbook><sheets><sheet name="Sheet1" sheetId="1" r:id="rId1"/></sheets></workbook>"#.as_slice(),
                ),
                (
                    "xl/_rels/workbook.xml.rels",
                    br#"<?xml version="1.0"?><Relationships><Relationship Id="rId1" Target="worksheets/sheet1.xml"/></Relationships>"#.as_slice(),
                ),
                (
                    "xl/worksheets/sheet1.xml",
                    br#"<?xml version="1.0"?><!DOCTYPE lolz [<!ENTITY lol "lol">]><worksheet><sheetData/></worksheet>"#.as_slice(),
                ),
            ],
            ZipCompression::Stored,
        )
        .map_err(|e| format!("sheet xxe seed: {e}"))?;
        if read_xlsx_bytes_with_schema(&sheet_xxe_xlsx, None, &schema, |_, _| true).is_ok() {
            return Err("XLSX reader accepted worksheet XML with <!DOCTYPE!".to_string());
        }

        let corpus = vec![valid_xlsx, xxe_xlsx, sheet_xxe_xlsx];
        let dict: &[&[u8]] = &[
            b"PK\x03\x04",
            b"<!DOCTYPE ",
            b"<!ENTITY ",
            b"xl/workbook.xml",
            b"xl/worksheets/sheet1.xml",
            b"../../../etc/passwd",
            b"&#x00;",
            b"&unknown;",
        ];

        let mut rng = Xoshiro256Pp::from_seed(seed);
        let (mut read_ok, mut infer_ok) = (0usize, 0usize);
        for i in 0..iters {
            let input = mutate_bytes(&mut rng, &corpus, dict, i);
            if let Ok((_good, bad)) =
                read_xlsx_bytes_with_schema(&input, None, &schema, |_, _| true)
            {
                read_ok += 1;
                let has_pii = bad
                    .cols
                    .iter()
                    .any(|c| c.name == "raw_line" && c.tags.elems().iter().any(|t| t == "pii"));
                if !has_pii {
                    return Err("XLSX bad_rows lost `pii` sensitivity tag!".to_string());
                }
            }
            if infer_xlsx_schema_from_bytes(&input, None, "FuzzXlsx").is_ok() {
                infer_ok += 1;
            }
        }
        Ok(format!(
            "iters={iters}, read_ok={read_ok}, infer_ok={infer_ok}"
        ))
    })
}

// ===========================================================================
// 10. HTTP/1.1 & HTTPS Fuzzer
// ===========================================================================

#[test]
fn fuzz_10_http11_and_https_url() -> TestResult {
    let iters = fuzz_iters();
    let seed = fuzz_base_seed().wrapping_add(10);
    run_bounded_2mib("10_http_https", move || {
        let json_body = br#"{"ok":true,"items":[1,2,3]}"#;
        let gz_body = gzip_bytes(json_body)?;

        let mut resp_cl = format!(
            "HTTP/1.1 200 OK\r\nContent-Type: application/json\r\nContent-Length: {}\r\n\r\n",
            json_body.len()
        )
        .into_bytes();
        resp_cl.extend_from_slice(json_body);

        let resp_chunked = format!(
            "HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n{:x}\r\n{}\r\n0\r\nX-Trailer: 1\r\n\r\n",
            json_body.len(),
            String::from_utf8_lossy(json_body)
        )
        .into_bytes();

        let mut resp_gz_chunked =
            b"HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\nContent-Encoding: gzip\r\n\r\n"
                .to_vec();
        resp_gz_chunked.extend_from_slice(format!("{:x}\r\n", gz_body.len()).as_bytes());
        resp_gz_chunked.extend_from_slice(&gz_body);
        resp_gz_chunked.extend_from_slice(b"\r\n0\r\n\r\n");

        // Explicit gzip-bomb response rejection test
        let bomb_gz = gzip_bytes(&vec![b'A'; 128 * 1024])?;
        let mut resp_bomb = format!(
            "HTTP/1.1 200 OK\r\nContent-Encoding: gzip\r\nContent-Length: {}\r\n\r\n",
            bomb_gz.len()
        )
        .into_bytes();
        resp_bomb.extend_from_slice(&bomb_gz);
        let cfg = HttpsConfig {
            max_response_bytes: 64 * 1024,
            ..HttpsConfig::default()
        };
        if parse_http_response_from_reader(Cursor::new(&resp_bomb), &cfg).is_ok() {
            return Err("parse_http_response_from_reader accepted 128 KiB gzip bomb!".to_string());
        }
        // Explicit redirect & conflicting Content-Length rejection tests
        if parse_http_response_from_reader(
            Cursor::new(b"HTTP/1.1 302 Found\r\nLocation: https://evil.test/\r\n\r\n"),
            &cfg,
        )
        .is_ok()
        {
            return Err("parse_http_response_from_reader allowed 302 redirect!".to_string());
        }
        if parse_http_response_from_reader(
            Cursor::new(b"HTTP/1.1 200 OK\r\nContent-Length: 2\r\nContent-Length: 4\r\n\r\nhi"),
            &cfg,
        )
        .is_ok()
        {
            return Err(
                "parse_http_response_from_reader allowed conflicting Content-Length!".to_string(),
            );
        }

        let corpus = vec![
            resp_cl,
            resp_chunked,
            resp_gz_chunked,
            resp_bomb,
            b"https://api.example.com/v2/items?page=1#frag".to_vec(),
            b"https://api.example.com:8443/v2".to_vec(),
            b"https://[::1]:8443/ok".to_vec(),
        ];
        let dict: &[&[u8]] = &[
            b"HTTP/1.1 200 OK\r\n",
            b"HTTP/1.1 301 Moved\r\n",
            b"Transfer-Encoding: chunked\r\n",
            b"Content-Encoding: gzip\r\n",
            b"Content-Length: ",
            b"\r\n\r\n",
            b"0\r\n\r\n",
            b"https://",
            b"http://",
            b"user:pass@",
        ];

        let mut rng = Xoshiro256Pp::from_seed(seed);
        let (mut url_ok, mut resp_ok) = (0usize, 0usize);
        for i in 0..iters {
            let input = mutate_bytes(&mut rng, &corpus, dict, i);
            let s = String::from_utf8_lossy(&input);
            let _ = ParsedHttpsUrl::parse(&s);
            if ParsedHttpsUrl::parse_and_check_host(&s, "api.example.com").is_ok() {
                url_ok += 1;
            }
            if let Ok(resp) = parse_http_response_from_reader(Cursor::new(&input), &cfg) {
                resp_ok += 1;
                if resp.body.len() > cfg.max_response_bytes {
                    return Err(format!(
                        "HTTP body len {} exceeded cap {}",
                        resp.body.len(),
                        cfg.max_response_bytes
                    ));
                }
            }
        }
        Ok(format!(
            "iters={iters}, url_allowed_ok={url_ok}, http_resp_ok={resp_ok}"
        ))
    })
}

// ===========================================================================
// 11. PostgreSQL Wire Protocol v3.0 Fuzzer
// ===========================================================================

#[test]
fn fuzz_11_postgres_wire_protocol_v3() -> TestResult {
    let iters = fuzz_iters();
    let seed = fuzz_base_seed().wrapping_add(11);
    run_bounded_2mib("11_postgres_v3", move || {
        // RowDescription ('T') with 2 columns
        let mut row_desc = Vec::new();
        row_desc.extend_from_slice(&2i16.to_be_bytes());
        row_desc.extend_from_slice(b"id\0");
        row_desc.extend_from_slice(&0u32.to_be_bytes());
        row_desc.extend_from_slice(&1i16.to_be_bytes());
        row_desc.extend_from_slice(&oid::INT8.to_be_bytes());
        row_desc.extend_from_slice(&8i16.to_be_bytes());
        row_desc.extend_from_slice(&(-1i32).to_be_bytes());
        row_desc.extend_from_slice(&0i16.to_be_bytes());
        row_desc.extend_from_slice(b"note\0");
        row_desc.extend_from_slice(&0u32.to_be_bytes());
        row_desc.extend_from_slice(&2i16.to_be_bytes());
        row_desc.extend_from_slice(&oid::TEXT.to_be_bytes());
        row_desc.extend_from_slice(&(-1i16).to_be_bytes());
        row_desc.extend_from_slice(&(-1i32).to_be_bytes());
        row_desc.extend_from_slice(&0i16.to_be_bytes());

        // DataRow ('D') with 2 cells (1 non-null, 1 null)
        let mut data_row = Vec::new();
        data_row.extend_from_slice(&2i16.to_be_bytes());
        data_row.extend_from_slice(&2i32.to_be_bytes());
        data_row.extend_from_slice(b"42");
        data_row.extend_from_slice(&(-1i32).to_be_bytes());

        // ErrorResponse ('E')
        let err_payload = b"SERROR\0C22012\0Mdivision by zero\0Ddetail\0\0";
        // ParameterStatus ('S')
        let param_payload = b"server_version\x0016.2\0";
        // CommandComplete ('C')
        let cmd_payload = b"UPDATE 17\0";
        // AuthSASLContinue ('R', code=11)
        let mut scram_payload = Vec::new();
        scram_payload.extend_from_slice(&11i32.to_be_bytes());
        scram_payload.extend_from_slice(b"r=clientnonceSERVER,s=c2FsdA==,i=4096");
        // Binary INTERVAL (16 bytes)
        let mut interval_bin = Vec::new();
        interval_bin.extend_from_slice(&1_000_000i64.to_be_bytes());
        interval_bin.extend_from_slice(&2i32.to_be_bytes());
        interval_bin.extend_from_slice(&1i32.to_be_bytes());

        let corpus = vec![
            pg_frame(b'T', &row_desc),
            pg_frame(b'D', &data_row),
            pg_frame(b'E', err_payload),
            pg_frame(b'S', param_payload),
            pg_frame(b'C', cmd_payload),
            pg_frame(b'R', &scram_payload),
            pg_frame(b'Z', b"I"),
            interval_bin,
            b"1 day 02:03:04.500000".to_vec(),
            b"-999999999999999999 seconds".to_vec(),
            b"\\xdeadbeef0102".to_vec(),
            b"r=clientnonceXYZ,s=YWJjZA==,i=4096".to_vec(),
        ];
        let dict: &[&[u8]] = &[
            b"T",
            b"D",
            b"E",
            b"S",
            b"R",
            b"C",
            b"Z",
            b"\\x",
            b" seconds",
            b" days ",
            b"r=clientnonce",
            b",s=",
            b",i=",
            b"\0",
        ];

        let mut rng = Xoshiro256Pp::from_seed(seed);
        let mut frames_ok = 0usize;
        for i in 0..iters {
            let input = mutate_bytes(&mut rng, &corpus, dict, i);
            if let Ok((tag, payload)) = parse_pg_wire_frame(&input) {
                frames_ok += 1;
                fuzz_decode_pg_payload(tag, &payload);
            }
            let raw_tag = input.first().copied().unwrap_or(b'D');
            fuzz_decode_pg_payload(raw_tag, &input);
        }
        Ok(format!("iters={iters}, valid_frames={frames_ok}"))
    })
}

// ===========================================================================
// 12. Safe REPL Input Splitter & Evaluator Fuzzer
// ===========================================================================

#[test]
fn fuzz_12_safe_repl_splitter_and_evaluator() -> TestResult {
    let iters = fuzz_iters();
    let seed = fuzz_base_seed().wrapping_add(12);
    run_bounded_2mib("12_repl", move || {
        let tmp = TempDir::new("repl")?;
        let mut session = ReplSession::new(ReplConfig {
            work_dir: tmp.path().to_path_buf(),
            ..ReplConfig::default()
        })
        .map_err(|d| format!("ReplSession::new failed: {}", d.message()))?;

        let corpus: Vec<Vec<u8>> = [
            "1 + 2 * 3",
            "x = 42",
            "fn double(n: Int) : Int\n  n * 2\nend",
            "schema S\n  a: Int\n  b: Text [pii]\nend",
            "t = table\n  | a | b |\n  | 1 | \"x\" |\nend",
            "t |> where(.a > 0) |> derive(c: .a + 1)",
            "if true\n  1\nelse\n  2\nend",
            "if true\n  1",
            "t |>",
            ":help",
            ":vars",
            ":type 1 + 2",
            ":profile t",
            ":explain t |> where(.a > 0)",
            ":infer-schema t",
            ":reset",
            ":unknown_cmd arg",
            "\"\"\"unterminated triple string",
            "# comment only",
        ]
        .iter()
        .map(|s| s.as_bytes().to_vec())
        .collect();

        let dict: &[&[u8]] = &[
            b":help",
            b":type ",
            b":profile ",
            b":explain ",
            b":infer-schema ",
            b":vars",
            b":reset",
            b":quit",
            b"untyped.read_csv(\"",
            b"if ",
            b"else ",
            b"end",
            b" |> ",
            b"fn ",
            b"schema ",
            b"table\n",
            b"\"\"\"",
        ];

        let mut rng = Xoshiro256Pp::from_seed(seed);
        let mut incomplete_cnt = 0usize;
        let mut eval_cnt = 0usize;
        for i in 0..iters {
            if i % 25 == 0 {
                session.reset();
            }
            let input = mutate_bytes(&mut rng, &corpus, dict, i);
            let s = String::from_utf8_lossy(&input);
            if ReplSession::is_incomplete_input(&s) {
                incomplete_cnt += 1;
            }
            // Exercise REPL evaluator on every mutated input (never panics or hangs).
            let _ = session.eval_input(&s);
            eval_cnt += 1;
        }
        Ok(format!(
            "iters={iters}, incomplete={incomplete_cnt}, evaluated={eval_cnt}"
        ))
    })
}

// ===========================================================================
// 13. Dedicated Minimal Regressions for Every Bug Uncovered by Phase 5A Fuzzing
// ===========================================================================

#[test]
fn fuzz_regressions_for_uncovered_bugs() -> TestResult {
    // Regression 1 (src/db/postgres.rs): interval & binary timestamp/interval integer overflows
    // must return clean Err rather than panicking on arithmetic overflow.
    for payload in [
        b"-999999999999999999 seconds".as_slice(),
        b"9223372036854775807 seconds".as_slice(),
        b"-9223372036854775808 seconds".as_slice(),
        b"9223372036854775807 days".as_slice(),
        b"9223372036854775807:00:00".as_slice(),
        b"0:9223372036854775807:00".as_slice(),
    ] {
        fuzz_decode_pg_payload(b'D', payload);
    }
    // Binary TIMESTAMP i64::MAX + PG_EPOCH_MICROS overflow
    fuzz_decode_pg_payload(b'D', &i64::MAX.to_be_bytes());
    // Binary 16-byte INTERVAL (i64::MAX, i32::MAX, i32::MAX) overflow
    let mut big_interval = Vec::with_capacity(16);
    big_interval.extend_from_slice(&i64::MAX.to_be_bytes());
    big_interval.extend_from_slice(&i32::MAX.to_be_bytes());
    big_interval.extend_from_slice(&i32::MAX.to_be_bytes());
    fuzz_decode_pg_payload(b'D', &big_interval);
    // Truncated RowDescription & DataRow claiming i16::MAX columns must not over-allocate
    fuzz_decode_pg_payload(b'T', &i16::MAX.to_be_bytes());
    fuzz_decode_pg_payload(b'D', &i16::MAX.to_be_bytes());

    // Regression 2 (src/syntax/fmt.rs): speculative render_expr in 2-stage pipeline, Call,
    // and IfInline previously advanced `self.c_idx` before falling back to multiline, silently
    // deleting comments and breaking formatter idempotence (`fmt(parse(fmt(m))) != fmt(m)`).
    let pipe_with_comment = r#"module FmtPipeComment

fn f(rows: Table(x: Int))
  rows
    |> derive(
      # keep this comment intact
      y: .x + 1
    )
end
"#;
    let m1 = parse_module(FileId(0), pipe_with_comment)
        .map_err(|d| format!("parse pipe_with_comment: {}", d.message()))?;
    let fmt1 = format_module(&m1);
    assert!(
        fmt1.contains("# keep this comment intact"),
        "formatter dropped comment inside 2-stage pipeline!\n{fmt1}"
    );
    let m2 =
        parse_module(FileId(0), &fmt1).map_err(|d| format!("reparse fmt1: {}", d.message()))?;
    let fmt2 = format_module(&m2);
    assert_eq!(fmt1, fmt2, "formatter must be strictly idempotent");

    // Regression 3 (src/formats/time.rs): POSIX TZ footer `-i32::MIN` negation overflow and
    // DST `+3600` overflow must return Err rather than panicking.
    let mut tz_neg_overflow = Vec::new();
    tz_neg_overflow.extend_from_slice(b"TZif2");
    tz_neg_overflow.extend_from_slice(&[0u8; 15]);
    for v in [0u32, 0, 0, 0, 1, 4] {
        tz_neg_overflow.extend_from_slice(&v.to_be_bytes());
    }
    tz_neg_overflow.extend_from_slice(&[0u8; 6]);
    tz_neg_overflow.extend_from_slice(b"UTC\0");
    tz_neg_overflow.extend_from_slice(b"TZif2");
    tz_neg_overflow.extend_from_slice(&[0u8; 15]);
    for v in [0u32, 0, 0, 0, 1, 4] {
        tz_neg_overflow.extend_from_slice(&v.to_be_bytes());
    }
    tz_neg_overflow.extend_from_slice(&[0u8; 6]);
    tz_neg_overflow.extend_from_slice(b"UTC\0");
    // POSIX offset `-596523:14:08` == `-2147483648` == `i32::MIN`
    tz_neg_overflow.extend_from_slice(b"\nFOO-596523:14:08\n");
    assert!(
        TzData::parse(&tz_neg_overflow).is_err(),
        "TZif with i32::MIN POSIX offset must return Err cleanly"
    );

    // Regression 4 (src/net/https.rs): truncated Content-Length and chunked headers claiming
    // 32 MiB on an empty body must return Err immediately without eager 32 MiB allocation.
    let huge_cl = b"HTTP/1.1 200 OK\r\nContent-Length: 33554432\r\n\r\n";
    assert!(
        parse_http_response_from_reader(Cursor::new(huge_cl), &HttpsConfig::default()).is_err()
    );
    let huge_chunk = b"HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n2000000\r\n";
    assert!(
        parse_http_response_from_reader(Cursor::new(huge_chunk), &HttpsConfig::default()).is_err()
    );
    // Max-usize body cap must not overflow `max_response_bytes + 1`
    let max_cfg = HttpsConfig {
        max_response_bytes: usize::MAX,
        ..HttpsConfig::default()
    };
    let ok_small = b"HTTP/1.1 200 OK\r\nContent-Length: 2\r\n\r\nok";
    let resp = parse_http_response_from_reader(Cursor::new(ok_small), &max_cfg)?;
    assert_eq!(resp.body, b"ok");

    // Regression 5 (src/formats/parquet.rs): crafted Parquet file claiming huge num_values
    // or bit_width=0 RLE count must return Err cleanly without OOM/huge preallocation.
    let valid_pq = write_parquet_bytes_with_options(
        &rich_sample_table(),
        ParquetWriteOptions {
            compression: ParquetCompression::Uncompressed,
            row_group_rows: 2,
        },
    )
    .map_err(|e| format!("write_parquet_bytes_with_options: {e}"))?;
    let mut bad_pq = valid_pq.clone();
    // Corrupt page header bytes near offset 4 to claim huge counts while staying tiny on disk.
    for b in bad_pq.iter_mut().skip(4).take(16) {
        *b = 0x7F;
    }
    let _ = infer_parquet_schema_from_bytes(&bad_pq, "BadPq");
    let _ = read_parquet_bytes_with_schema(&bad_pq, &rich_table_schema(), |_, _| true);

    Ok(())
}
