//! Dana v0.4 Slice 4.2 dedicated parity & regression test suite:
//! - Zero-copy `Val::Columnar(Arc<VmTable>)` equality, ordering, rendering & REPL privacy
//! - Exact `parse_decimal_i128` vs. `parse_decimal_bigint_strict` parity
//! - Direct streaming-columnar CSV/TSV reader (`read_csv_stream_to_vm_table`) & writer
//!   (`write_csv_vm_table`) parity across all types, quarantine `bad_rows`, compressed streams,
//!   fast-path & fallback `where` constraints
//! - Direct columnar Apache Parquet reader (`read_parquet_bytes_to_vm_table`) & writer
//!   (`write_parquet_vm_table_bytes`) parity across `PLAIN`, `RLE_DICTIONARY`, `DataPage` v1/v2,
//!   codecs (`UNCOMPRESSED`, `GZIP`, `ZSTD`), nullable & exact `Decimal` columns, parallel
//!   column decoding, earliest 1-based `(row, col)` constraint diagnostics, derived
//!   `ScalarTy::Unit` columns, and selection vectors
//! - Direct columnar `Stats.*` & `profile_vm_table` (including `[pii]`/`[ferpa]`/`row_tags`
//!   redaction) bit-for-bit parity with row-wise oracle
//! - End-to-end VM vs. Oracle parity across Table helpers, loops, promises, charts, reports,
//!   writers, and REPL preview/redaction.

use std::cmp::Ordering;
use std::io::Cursor;
use std::sync::Arc;

use dana::base::{FileId, SourceMap, render_diagnostic};
use dana::check::{check_resolved, resolve_module};
use dana::core::bigint::{BigInt, DEC_MAX, DEC_MIN};
use dana::core::syntax::{
    AggKind, ColSpec, Float64, LTy, Literal, PrimOp, ScalarTy, TableTy, TagSet, Ty,
};
use dana::formats::compress::{AutoDecodeReader, AutoEncodeWriter, CompressionKind};
use dana::formats::constraint::FastColConstraint;
use dana::formats::csv::{
    format_csv_table, format_csv_vm_table, read_csv_stream_to_vm_table, read_csv_stream_with_schema,
};
use dana::formats::json::{format_jsonl_table, format_jsonl_vm_table};
use dana::formats::parquet::{
    ParquetCompression, ParquetWriteOptions, read_parquet_bytes_to_vm_table,
    read_parquet_bytes_with_schema, write_parquet_bytes_with_options, write_parquet_vm_table_bytes,
    write_parquet_vm_table_bytes_with_options,
};
use dana::formats::time::{parse_decimal_bigint_strict, parse_decimal_i128};
use dana::lower::lower_program;
use dana::oracle::value::{
    TableRow, TableVal, Val, render_decimal, render_decimal_i128_into, render_public_val, val_cmp,
    val_eq, val_lt,
};
use dana::repl::{ReplConfig, ReplOutput, ReplSession};
use dana::runtime::{
    ExecPrimOp, ExecProgram, ExecRowExpr, RunConfig, RunResult, eval_exec_entry, run_exec_program,
};
use dana::stats::profile::{profile_table, profile_vm_table};
use dana::stats::{
    OutlierMethod, chi_square_gof_table, chi_square_gof_vm_table, chi_square_independence_table,
    chi_square_independence_vm_table, detect_outliers_table, detect_outliers_vm_table,
    linear_regression_table, linear_regression_vm_table, pearson_corr_table, pearson_corr_vm_table,
    spearman_corr_table, spearman_corr_vm_table, welch_t_test_tables, welch_t_test_vm_tables,
};
use dana::syntax::parse_module;
use dana::vm::batch::{BATCH_SIZE, Batch};
use dana::vm::ops::VmTable;
use dana::vm::{VmConfig, eval_exec_entry_vm, run_exec_program_vm};

type TestResult<T = ()> = Result<T, Box<dyn std::error::Error>>;

fn col(name: &str, ty: ScalarTy) -> ColSpec {
    ColSpec {
        name: name.to_string(),
        ty,
        tags: TagSet::empty(),
        bucketed: false,
        agg_kind: AggKind::Raw,
    }
}

fn tagged_col(name: &str, ty: ScalarTy, tags: &[&str]) -> ColSpec {
    ColSpec {
        name: name.to_string(),
        ty,
        tags: TagSet::of_list(tags.iter().map(|s| (*s).to_string()).collect()),
        bucketed: false,
        agg_kind: AggKind::Raw,
    }
}

fn compile_dana(src: &str) -> TestResult<ExecProgram> {
    let mut sm = SourceMap::new();
    let fid: FileId = sm.add_file("v04_test.dana".to_string(), src.to_string());
    let parsed = parse_module(fid, src).map_err(|d| render_diagnostic(&d, &sm))?;
    let resolved = resolve_module(fid, parsed, None).map_err(|ds| {
        ds.iter()
            .map(|d| render_diagnostic(d, &sm))
            .collect::<Vec<_>>()
            .join("\n")
    })?;
    let checked = check_resolved(&resolved, &sm).map_err(|ds| {
        ds.iter()
            .map(|d| render_diagnostic(d, &sm))
            .collect::<Vec<_>>()
            .join("\n")
    })?;
    let lowered = lower_program(checked).map_err(|d| render_diagnostic(&d, &sm))?;
    Ok(lowered.exec)
}

fn assert_tables_identical(a: &TableVal, b: &TableVal, label: &str) {
    assert_eq!(a.cols.len(), b.cols.len(), "{label}: col count mismatch");
    for (ca, cb) in a.cols.iter().zip(&b.cols) {
        assert_eq!(ca.name, cb.name, "{label}: col name mismatch");
    }
    assert_eq!(a.rows.len(), b.rows.len(), "{label}: row count mismatch");
    for (ri, (ra, rb)) in a.rows.iter().zip(&b.rows).enumerate() {
        assert_eq!(
            ra.cells.len(),
            rb.cells.len(),
            "{label}: row {ri} cell count mismatch"
        );
        for (ci, (va, vb)) in ra.cells.iter().zip(&rb.cells).enumerate() {
            assert!(
                val_eq(va, vb),
                "{label}: row {ri} col {ci} mismatch: {va:?} vs {vb:?}"
            );
        }
    }
}

#[test]
fn parse_decimal_i128_matches_bigint_strict_on_edges_and_prng() {
    let cases = [
        "0",
        "-0",
        "0.0",
        "-0.000000000000000000",
        "1",
        "-1",
        "42.5",
        "  -123456.789012345678901234  ",
        "0.000000000000000001",
        "-0.000000000000000001",
        "99999999999999999999.999999999999999999",
        "-99999999999999999999.999999999999999999",
        // Exact i128 boundary checks
        "170141183460469231731.687303715884105727",
        "-170141183460469231731.687303715884105727",
        // Overflow just past DEC_MAX / DEC_MIN
        "170141183460469231731.687303715884105728",
        "-170141183460469231731.687303715884105728",
        "999999999999999999999999999.0",
        // Syntax rejections
        "",
        "   ",
        ".5",
        "-.5",
        "1.",
        "1..2",
        "+1.5",
        "1_000.00",
        "1e5",
        "1E-3",
        "0.1234567890123456789", // 19 frac digits
        "abc",
        "12.3a",
    ];
    for s in cases {
        let strict = parse_decimal_bigint_strict(s)
            .ok()
            .and_then(|b| b.to_i128());
        let fast = parse_decimal_i128(s);
        assert_eq!(fast, strict, "decimal parse mismatch on {s:?}");
        if let Some(v) = fast {
            let mut rendered = String::new();
            render_decimal_i128_into(&mut rendered, v);
            assert_eq!(
                rendered,
                render_decimal(&BigInt::from(v)),
                "decimal render mismatch on {s:?}"
            );
        }
    }

    // Deterministic PRNG sweep of 2,000 decimal strings
    let mut seed: u64 = 0x5EED_0402_CAFE_BABE;
    let mut next_u64 = || {
        seed = seed
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        seed
    };
    for _ in 0..2_000 {
        let neg = (next_u64() & 1) == 1;
        let int_digits = (next_u64() % 20) + 1;
        let has_frac = (next_u64() % 3) != 0;
        let frac_digits = if has_frac { (next_u64() % 19) + 1 } else { 0 };
        let mut s = String::new();
        if neg {
            s.push('-');
        }
        for _ in 0..int_digits {
            s.push((b'0' + (next_u64() % 10) as u8) as char);
        }
        if has_frac {
            s.push('.');
            for _ in 0..frac_digits {
                s.push((b'0' + (next_u64() % 10) as u8) as char);
            }
        }
        let strict = parse_decimal_bigint_strict(&s)
            .ok()
            .and_then(|b| b.to_i128());
        let fast = parse_decimal_i128(&s);
        assert_eq!(fast, strict, "PRNG decimal mismatch on {s:?}");
    }

    for boundary in [DEC_MIN, DEC_MAX, 0, -1, 1] {
        let mut out = String::new();
        render_decimal_i128_into(&mut out, boundary);
        assert_eq!(parse_decimal_i128(&out), Some(boundary));
    }
}

#[test]
fn streaming_columnar_csv_and_tsv_compressed_parity_and_quarantine() -> TestResult {
    let schema = TableTy {
        cols: vec![
            col("id", ScalarTy::Int),
            col("name", ScalarTy::Text),
            col("amount", ScalarTy::Decimal),
            col("ratio", ScalarTy::Float),
            col("active?", ScalarTy::Bool),
            col("day", ScalarTy::Date),
            col("ts", ScalarTy::Timestamp),
            col("note", ScalarTy::Option(Box::new(ScalarTy::Text))),
        ],
        ..TableTy::default()
    };

    // 4,500 rows (spans 3 batches of 2,048!) including quotes, commas, escaped quotes,
    // multiline fields, CRLF, UTF-8 BOM, nulls, and bad/constraint-failing rows.
    let mut csv_text = String::from("\u{FEFF}id,name,amount,ratio,active?,day,ts,note\r\n");
    for i in 1..=4_500_i64 {
        if i % 500 == 0 {
            csv_text.push_str(&format!(
                "{i},\"Bob, Jr.\",NOT_A_DEC,1.25,true,2026-01-15,2026-01-15T08:30:00Z,ok\r\n"
            ));
        } else if i % 700 == 0 {
            csv_text.push_str(&format!(
                "{i},\"Carol\",-5.00,1.25,true,2026-01-15,2026-01-15T08:30:00Z,\r\n"
            ));
        } else if i % 900 == 0 {
            csv_text.push_str(&format!(
                "{i},\"\",12.50,0.5,false,2026-01-15,2026-01-15T08:30:00Z,hi\r\n"
            ));
        } else if i % 1100 == 0 {
            csv_text.push_str(&format!("{i},only_two\r\n"));
        } else {
            let name = if i % 13 == 0 {
                format!("\"Line1\nLine2, \"\"q{i}\"\"\"")
            } else {
                format!("user_{i}")
            };
            let note = if i % 4 == 0 {
                String::new()
            } else {
                format!("note-{i}")
            };
            let active = if i % 2 == 0 { "true" } else { "false" };
            csv_text.push_str(&format!(
                "{i},{name},{}.{:02},{:.3},{active},2026-03-{:02},2026-03-{:02}T10:15:30Z,{note}\r\n",
                i,
                i % 100,
                (i as f64) * 0.125,
                (i % 28) + 1,
                (i % 28) + 1,
            ));
        }
    }

    let c_name_not_empty = ExecRowExpr::Prim {
        op: ExecPrimOp::Core(PrimOp::NotBool),
        args: vec![ExecRowExpr::Prim {
            op: ExecPrimOp::Core(PrimOp::EmptyText),
            args: vec![ExecRowExpr::Col("__self".to_string())],
        }],
    };
    let c_amount_pos = ExecRowExpr::Prim {
        op: ExecPrimOp::Core(PrimOp::Gt),
        args: vec![
            ExecRowExpr::Col("__self".to_string()),
            ExecRowExpr::Lit(Literal::Decimal(BigInt::ZERO)),
        ],
    };
    let fast_constraints = vec![
        FastColConstraint::Fallback, // tests fallback path for col 0 (id != 77)
        FastColConstraint::compile(Some(&c_name_not_empty), &ScalarTy::Text, &|_| None),
        FastColConstraint::compile(Some(&c_amount_pos), &ScalarTy::Decimal, &|_| None),
        FastColConstraint::AlwaysTrue,
        FastColConstraint::AlwaysTrue,
        FastColConstraint::AlwaysTrue,
        FastColConstraint::AlwaysTrue,
        FastColConstraint::AlwaysTrue,
    ];
    assert!(!matches!(fast_constraints[1], FastColConstraint::Fallback));
    assert!(!matches!(fast_constraints[2], FastColConstraint::Fallback));

    let check_oracle = |ci: usize, val: &Val| -> bool {
        match (ci, val) {
            (0, Val::Int(n)) => n.to_i64() != Some(77),
            (1, Val::Text(s)) => !s.is_empty(),
            (2, Val::Decimal(d)) => !d.is_zero() && !d.is_negative(),
            _ => true,
        }
    };

    for comp in [
        CompressionKind::Plain,
        CompressionKind::Gzip,
        CompressionKind::Zstd,
    ] {
        let mut encoded = Vec::new();
        {
            let mut w = AutoEncodeWriter::new(&mut encoded, comp)?;
            std::io::Write::write_all(&mut w, csv_text.as_bytes())?;
            w.finish()?;
        }
        let r_oracle = AutoDecodeReader::new(Cursor::new(encoded.as_slice()))?;
        let (good_tv, bad_tv) = read_csv_stream_with_schema(r_oracle, &schema, b',', check_oracle)?;

        let r_vm = AutoDecodeReader::new(Cursor::new(encoded.as_slice()))?;
        let (good_vm, bad_vm) = read_csv_stream_to_vm_table(
            r_vm,
            &schema,
            b',',
            BATCH_SIZE,
            &fast_constraints,
            check_oracle,
        )?;

        assert!(good_vm.batches.len() >= 2, "must span multiple batches");
        assert_tables_identical(
            &good_vm.to_table_val(),
            &good_tv,
            &format!("csv good {comp:?}"),
        );
        assert_tables_identical(&bad_vm, &bad_tv, &format!("csv bad {comp:?}"));
        assert!(bad_vm.rows.len() >= 15, "must quarantine bad rows");

        assert_eq!(
            format_csv_vm_table(&good_vm, b','),
            format_csv_table(&good_tv, b','),
            "CSV writer mismatch"
        );
        assert_eq!(
            format_csv_vm_table(&good_vm, b'\t'),
            format_csv_table(&good_tv, b'\t'),
            "TSV writer mismatch"
        );
        assert_eq!(
            format_jsonl_vm_table(&good_vm),
            format_jsonl_table(&good_tv),
            "JSONL writer mismatch"
        );
    }
    Ok(())
}

#[test]
fn columnar_parquet_all_types_codecs_parallel_and_constraints() -> TestResult {
    let schema = TableTy {
        cols: vec![
            col("id", ScalarTy::Int),
            col("tag", ScalarTy::Text),
            col("price", ScalarTy::Decimal),
            col("score", ScalarTy::Float),
            col("ok?", ScalarTy::Bool),
            col("d", ScalarTy::Date),
            col("ts", ScalarTy::Timestamp),
            col("opt_int", ScalarTy::Option(Box::new(ScalarTy::Int))),
            col("opt_txt", ScalarTy::Option(Box::new(ScalarTy::Text))),
            col("opt_dec", ScalarTy::Option(Box::new(ScalarTy::Decimal))),
        ],
        ..TableTy::default()
    };

    // 9,000 rows triggers parallel column decoding (>= 8,192 rows) and multiple 2,048-row batches!
    let tags = ["alpha", "beta", "gamma", "delta"];
    let mut rows = Vec::with_capacity(9_000);
    for i in 0..9_000_i64 {
        let opt_i = if i % 5 == 0 {
            Val::OptNone
        } else {
            Val::OptSome(Box::new(Val::Int(BigInt::from(i * 3))))
        };
        let opt_t = if i % 7 == 0 {
            Val::OptNone
        } else {
            Val::OptSome(Box::new(Val::Text(
                tags[(i as usize) % tags.len()].to_string(),
            )))
        };
        let opt_d = if i % 11 == 0 {
            Val::OptNone
        } else {
            Val::OptSome(Box::new(Val::Decimal(BigInt::from(
                (i as i128) * 10_000_000_000_000_000_i128 + 123_456_789_i128,
            ))))
        };
        rows.push(TableRow {
            cells: vec![
                Val::Int(BigInt::from(i + 1)),
                Val::Text(tags[(i as usize) % tags.len()].to_string()),
                Val::Decimal(BigInt::from(
                    ((i + 1) as i128) * 1_000_000_000_000_000_000_i128 + 500_000_000_000_000_000,
                )),
                Val::Float(Float64::from_f64((i as f64) * 0.25 - 10.5)),
                Val::Bool(i % 3 != 0),
                Val::Date(BigInt::from(20_000 + (i % 365))),
                Val::Timestamp(BigInt::from(1_700_000_000_000_000_i64 + i * 1_000_000)),
                opt_i,
                opt_t,
                opt_d,
            ],
            group_meta: None,
        });
    }
    let tv = TableVal {
        cols: schema.cols.clone(),
        rows,
    };

    let vm_src = VmTable::from_table_val(&tv, BATCH_SIZE);
    let no_constraints = vec![FastColConstraint::AlwaysTrue; schema.cols.len()];

    for comp in [
        ParquetCompression::Uncompressed,
        ParquetCompression::Gzip,
        ParquetCompression::Zstd,
    ] {
        let opts = ParquetWriteOptions {
            compression: comp,
            row_group_rows: 4_500,
        };
        let bytes_from_tv = write_parquet_bytes_with_options(&tv, opts)?;
        let bytes_from_vm = write_parquet_vm_table_bytes_with_options(&vm_src, opts)?;

        for (tag_lbl, bytes) in [
            ("tv_written", &bytes_from_tv),
            ("vm_written", &bytes_from_vm),
        ] {
            let dec_tv = read_parquet_bytes_with_schema(bytes, &schema, |_, _| true)?;
            let dec_vm = read_parquet_bytes_to_vm_table(
                bytes,
                &schema,
                BATCH_SIZE,
                &no_constraints,
                |_, _| true,
            )?;
            assert_tables_identical(
                &dec_vm.to_table_val(),
                &dec_tv,
                &format!("parquet {comp:?} {tag_lbl}"),
            );
            assert_tables_identical(&dec_vm.to_table_val(), &tv, &format!("parquet rt {comp:?}"));
        }
    }

    // Verify exact earliest 1-based `(row, col)` constraint failure parity!
    let small_bytes = write_parquet_vm_table_bytes(&vm_src, ParquetCompression::Zstd)?;
    let c_id_lt_100 = ExecRowExpr::Prim {
        op: ExecPrimOp::Core(PrimOp::Lt),
        args: vec![
            ExecRowExpr::Col("__self".to_string()),
            ExecRowExpr::Lit(Literal::Int(BigInt::from(100))),
        ],
    };
    let c_price_lt_50 = ExecRowExpr::Prim {
        op: ExecPrimOp::Core(PrimOp::Lt),
        args: vec![
            ExecRowExpr::Col("__self".to_string()),
            ExecRowExpr::Lit(Literal::Decimal(BigInt::from(
                50_000_000_000_000_000_000_i128,
            ))),
        ],
    };
    let mut fast_cs = vec![FastColConstraint::AlwaysTrue; schema.cols.len()];
    fast_cs[0] = FastColConstraint::compile(Some(&c_id_lt_100), &ScalarTy::Int, &|_| None);
    fast_cs[2] = FastColConstraint::compile(Some(&c_price_lt_50), &ScalarTy::Decimal, &|_| None);

    let oracle_res =
        read_parquet_bytes_with_schema(&small_bytes, &schema, |ci, val| match (ci, val) {
            (0, Val::Int(n)) => n.to_i64().is_some_and(|x| x < 100),
            (2, Val::Decimal(d)) => d
                .to_i128()
                .is_some_and(|x| x < 50_000_000_000_000_000_000_i128),
            _ => true,
        });
    let vm_res =
        read_parquet_bytes_to_vm_table(&small_bytes, &schema, BATCH_SIZE, &fast_cs, |_, _| true);
    let (Err(oracle_err), Err(vm_err)) = (oracle_res, vm_res) else {
        return Err("expected both oracle and vm parquet constraint checks to fail".into());
    };
    assert_eq!(
        vm_err, oracle_err,
        "exact 1-based (row, col) constraint error must match"
    );

    // Filtered batches (selection vectors) + derived `ScalarTy::Unit` column round-trip!
    let mut filtered_vm = vm_src.slice_first(200);
    filtered_vm.cols[3].ty = ScalarTy::Unit;
    for b in &mut filtered_vm.batches {
        b.cols[3].spec.ty = ScalarTy::Unit;
        b.selection = Some((0..b.len as u16).step_by(2).collect());
    }
    let filt_bytes = write_parquet_vm_table_bytes(&filtered_vm, ParquetCompression::Zstd)?;
    let read_back = read_parquet_bytes_to_vm_table(
        &filt_bytes,
        &schema,
        BATCH_SIZE,
        &no_constraints,
        |_, _| true,
    )?;
    assert_tables_identical(
        &read_back.to_table_val(),
        &filtered_vm.to_table_val(),
        "filtered pq",
    );
    Ok(())
}

#[test]
fn columnar_stats_and_profile_match_row_wise_oracle_with_privacy_redaction() -> TestResult {
    let cols = vec![
        col("id", ScalarTy::Int),
        col("x", ScalarTy::Float),
        col("y", ScalarTy::Float),
        col("dec_v", ScalarTy::Decimal),
        col("cat_a", ScalarTy::Text),
        col("cat_b", ScalarTy::Text),
        col("flag?", ScalarTy::Bool),
        col("derived_f", ScalarTy::Unit),
        tagged_col("secret_email", ScalarTy::Text, &["pii"]),
        tagged_col("gpa", ScalarTy::Float, &["ferpa"]),
    ];

    // 9,000 rows triggers parallel column profiling (>= 8,192 rows).
    let cats_a = ["north", "south", "east"];
    let cats_b = ["web", "retail"];
    let mut rows = Vec::with_capacity(9_000);
    for i in 0..9_000_i64 {
        let x = (i as f64) * 0.1 + 1.0;
        let y = if i == 500 {
            50_000.0
        } else {
            2.5 * x + 3.0 + ((i % 7) as f64) * 0.2
        };
        rows.push(TableRow {
            cells: vec![
                Val::Int(BigInt::from(i)),
                Val::Float(Float64::from_f64(x)),
                Val::Float(Float64::from_f64(y)),
                Val::Decimal(BigInt::from((i as i128) * 1_000_000_000_000_000_000_i128)),
                Val::Text(cats_a[(i as usize) % cats_a.len()].to_string()),
                Val::Text(cats_b[((i / 2) as usize) % cats_b.len()].to_string()),
                Val::Bool(i % 3 == 0),
                Val::Float(Float64::from_f64((i % 100) as f64 * 0.125)),
                Val::Text(format!("private_user_{i}@secret.edu")),
                Val::Float(Float64::from_f64(2.0 + ((i % 20) as f64) * 0.1)),
            ],
            group_meta: None,
        });
    }
    let tv = TableVal {
        cols: cols.clone(),
        rows,
    };
    let vm = VmTable::from_table_val(&tv, BATCH_SIZE);

    assert_eq!(
        pearson_corr_vm_table(&vm, "x", "y"),
        pearson_corr_table(&tv, "x", "y")
    );
    assert_eq!(
        spearman_corr_vm_table(&vm, "x", "y"),
        spearman_corr_table(&tv, "x", "y")
    );
    assert_eq!(
        linear_regression_vm_table(&vm, "x", "y"),
        linear_regression_table(&tv, "x", "y")
    );
    assert_eq!(
        chi_square_independence_vm_table(&vm, "cat_a", "cat_b"),
        chi_square_independence_table(&tv, "cat_a", "cat_b")
    );

    let tv_a = TableVal {
        cols: cols.clone(),
        rows: tv.rows[..500].to_vec(),
    };
    let tv_b = TableVal {
        cols: cols.clone(),
        rows: tv.rows[500..1000].to_vec(),
    };
    let vm_a = VmTable::from_table_val(&tv_a, BATCH_SIZE);
    let vm_b = VmTable::from_table_val(&tv_b, BATCH_SIZE);
    assert_eq!(
        welch_t_test_vm_tables(&vm_a, &vm_b, "x"),
        welch_t_test_tables(&tv_a, &tv_b, "x")
    );
    assert_eq!(
        chi_square_gof_vm_table(&vm_a, "x", "y"),
        chi_square_gof_table(&tv_a, "x", "y")
    );

    for method in [OutlierMethod::ZScore, OutlierMethod::Iqr] {
        let out_tv = detect_outliers_table(&tv, "y", method, 3.0, "is_out?", &TagSet::empty())?;
        let out_vm = detect_outliers_vm_table(&vm, "y", method, 3.0, "is_out?", &TagSet::empty())?;
        assert_tables_identical(
            &out_vm.to_table_val(),
            &out_tv,
            &format!("outliers {method:?}"),
        );
    }

    let p_tv = profile_table(&tv, &TagSet::empty(), &[]);
    let p_vm = profile_vm_table(&vm, &TagSet::empty(), &[]);
    assert_eq!(
        p_vm, p_tv,
        "profile_vm_table must match profile_table bit-for-bit"
    );
    let rendered = dana::stats::profile::render_profile_terminal(&p_vm);
    assert!(rendered.contains("[REDACTED:pii]"));
    assert!(rendered.contains("[REDACTED:ferpa]"));
    assert!(!rendered.contains("private_user_"));

    let row_tags = TagSet::of_list(vec!["ferpa".to_string()]);
    let p_tv_red = profile_table(&tv, &row_tags, &[]);
    let p_vm_red = profile_vm_table(&vm, &row_tags, &[]);
    assert_eq!(p_vm_red, p_tv_red, "row_tags redacted profile must match");
    for col_sum in &p_vm_red.cols {
        assert!(!col_sum.redacted_tags.is_empty());
        assert!(col_sum.mean.is_none());
        assert!(col_sum.top_values.is_empty());
    }
    Ok(())
}

#[test]
fn val_columnar_structural_equality_ordering_and_end_to_end_vm_oracle_parity() -> TestResult {
    let schema_cols = vec![col("k", ScalarTy::Int), col("v", ScalarTy::Text)];
    let tv = TableVal {
        cols: schema_cols,
        rows: vec![
            TableRow {
                cells: vec![Val::Int(BigInt::from(1)), Val::Text("a".to_string())],
                group_meta: None,
            },
            TableRow {
                cells: vec![Val::Int(BigInt::from(2)), Val::Text("b".to_string())],
                group_meta: None,
            },
        ],
    };
    let v_tbl = Val::Table(tv.clone());
    let v_col = Val::Columnar(Arc::new(VmTable::from_table_val(&tv, BATCH_SIZE)));
    assert!(val_eq(&v_col, &v_tbl));
    assert!(val_eq(&v_tbl, &v_col));
    assert!(val_eq(&v_col, &v_col));
    assert_eq!(val_cmp(&v_col, &v_tbl), Ordering::Equal);
    assert_eq!(val_cmp(&v_tbl, &v_col), Ordering::Equal);
    assert!(!val_lt(&v_col, &v_tbl));
    assert!(!val_lt(&v_tbl, &v_col));
    assert_eq!(render_public_val(&v_col), render_public_val(&v_tbl));

    // Different batch split + interleaved empty batch must still compare equal!
    let mut b1 = VmTable::from_table_val(&tv, 1);
    assert_eq!(b1.batches.len(), 2);
    let v_col_split = Val::Columnar(Arc::new(b1.clone()));
    assert!(val_eq(&v_col, &v_col_split));
    assert_eq!(val_cmp(&v_col, &v_col_split), Ordering::Equal);
    b1.batches.insert(
        0,
        Batch {
            cols: Vec::new(),
            len: 0,
            selection: None,
            group_meta: None,
        },
    );
    assert!(val_eq(&v_col, &Val::Columnar(Arc::new(b1))));

    // Full Dana program exercising CSV columnar ingestion, promises, loops, Table helpers,
    // Stats.*, profile(), and CSV/Parquet/JSONL/XLSX writers on VM vs Oracle!
    let src = r#"
module ColumnarParity
use Stats

schema Reading
  id: Int where . > 0
  grp: Text where not .empty?
  val: Float
  amt: Decimal where . >= 0.0
end

fn run_analytics(t: Table(Reading)) : Table(grp: Text, total_amt: Decimal, avg_val: Float?, cnt: Int)
  promise unique(.grp)
  promise all(.cnt > 0)

  t
    |> where(.val >= 0.0)
    |> group_by(.grp)
    |> summarize(
      total_amt: sum(.amt),
      avg_val: mean(.val),
      cnt: count()
    )
    |> sort_by(.grp)
end

fn main(files: ReadFiles, out: WriteFiles("out"), console: Console) : Int
  (readings, bad) = try files.read_csv("data.csv", as: Reading)
  summary = run_analytics(readings)
  r = Stats.corr(readings, x: .id, y: .val, method: :pearson)
  rs = Stats.corr(readings, x: .id, y: .val, method: :spearman)
  model = Stats.linear_regression(readings, x: .id, y: .val)
  flagged = Stats.outliers(readings, column: .val, method: :zscore, threshold: 2.0, flag: "is_outlier")
  prof = readings.profile()
  first_row = summary.first!
  var loop_sum = 0
  for row in summary
    loop_sum = loop_sum + row.cnt
  end
  try out.write_csv("summary.csv", summary)
  try out.write_jsonl("summary.jsonl", summary)
  try out.write_parquet("flagged.parquet", flagged)
  try out.write_xlsx("summary.xlsx", summary)
  console.print("cnt=#{readings.count()} bad=#{bad.count()} empty=#{summary.empty?}")
  console.print("sum_amt=#{readings.sum(.amt)} loop=#{loop_sum} first=#{first_row.grp}")
  console.print("r=#{r.round(4)} rs=#{rs.round(4)} slope=#{model.slope.round(4)}")
  console.print_profile(prof)
  0
end
"#;

    let prog = compile_dana(src)?;
    let tmp = std::env::temp_dir().join(format!("dana_v04_parity_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&tmp);
    let vm_dir = tmp.join("vm");
    let or_dir = tmp.join("oracle");
    std::fs::create_dir_all(&vm_dir)?;
    std::fs::create_dir_all(&or_dir)?;

    let csv_data = "id,grp,val,amt\n1,a,10.0,1.50\n2,a,20.0,2.50\n3,b,30.0,3.00\n4,b,40.0,4.00\n-1,a,5.0,1.00\n5,a,50.0,-2.00\n";
    std::fs::write(vm_dir.join("data.csv"), csv_data)?;
    std::fs::write(or_dir.join("data.csv"), csv_data)?;

    let vm_cfg = RunConfig {
        work_dir: Some(vm_dir.clone()),
        live_io: true,
        ..RunConfig::default()
    };
    let or_cfg = RunConfig {
        work_dir: Some(or_dir.clone()),
        live_io: true,
        ..RunConfig::default()
    };

    let vm_res = run_exec_program_vm(&prog, &vm_cfg, &VmConfig::default());
    let or_res = run_exec_program(&prog, &or_cfg);
    match (vm_res, or_res) {
        (
            RunResult::Ok {
                exit_code: vc,
                stdout: vo,
                stderr: ve,
            },
            RunResult::Ok {
                exit_code: oc,
                stdout: oo,
                stderr: oe,
            },
        ) => {
            assert_eq!(vc, 0);
            assert_eq!(vc, oc);
            assert_eq!(vo, oo, "VM vs Oracle stdout must match identically");
            assert_eq!(ve, oe);
        }
        (v, o) => return Err(format!("unexpected result: vm={v:?} oracle={o:?}").into()),
    }

    assert_eq!(
        std::fs::read_to_string(vm_dir.join("out/summary.csv"))?,
        std::fs::read_to_string(or_dir.join("out/summary.csv"))?,
    );
    assert_eq!(
        std::fs::read_to_string(vm_dir.join("out/summary.jsonl"))?,
        std::fs::read_to_string(or_dir.join("out/summary.jsonl"))?,
    );
    assert!(vm_dir.join("out/flagged.parquet").metadata()?.len() > 64);
    assert!(vm_dir.join("out/summary.xlsx").metadata()?.len() > 64);

    // Confirm VM entry returns `Val::Columnar` and matches Oracle `Val::Table` via `val_eq`!
    let tv_in = TableVal {
        cols: vec![
            col("id", ScalarTy::Int),
            col("grp", ScalarTy::Text),
            col("val", ScalarTy::Float),
            col("amt", ScalarTy::Decimal),
        ],
        rows: vec![TableRow {
            cells: vec![
                Val::Int(BigInt::from(1)),
                Val::Text("a".to_string()),
                Val::Float(Float64::from_f64(10.0)),
                Val::Decimal(BigInt::from(1_500_000_000_000_000_000_i128)),
            ],
            group_meta: None,
        }],
    };
    let vm_entry = eval_exec_entry_vm(
        &prog,
        "run_analytics",
        &[(
            "t".to_string(),
            Val::Columnar(Arc::new(VmTable::from_table_val(&tv_in, BATCH_SIZE))),
        )],
        &RunConfig::default(),
        &VmConfig::default(),
    );
    let or_entry = eval_exec_entry(
        &prog,
        "run_analytics",
        &[("t".to_string(), Val::Table(tv_in))],
        &RunConfig::default(),
    );
    match (vm_entry, or_entry) {
        (
            dana::runtime::EvalProgramResult::Ok { val: vv, .. },
            dana::runtime::EvalProgramResult::Ok { val: ov, .. },
        ) => {
            assert!(
                matches!(vv.as_ref(), Val::Columnar(_)),
                "VM plan result must stay columnar without TableVal materialization"
            );
            assert!(
                val_eq(&vv, &ov),
                "Val::Columnar must equal oracle Val::Table"
            );
        }
        other => return Err(format!("unexpected entry eval: {other:?}").into()),
    }

    // REPL preview & privacy redaction on columnar tables!
    let mut sess = ReplSession::new(ReplConfig {
        work_dir: vm_dir.clone(),
        ..ReplConfig::default()
    })
    .map_err(|d| d.message().to_string())?;
    let _ = sess
        .eval_input("schema SecretRec\n  id: Int\n  email: Text [pii]\n  gpa: Float [ferpa]\nend");
    std::fs::write(
        vm_dir.join("secret.csv"),
        "id,email,gpa\n1,alice@uni.edu,3.9\n2,bob@uni.edu,3.5\n",
    )?;
    let _ = sess.eval_input("(sec, _bad) = try files.read_csv(\"secret.csv\", as: SecretRec)");
    match sess.eval_input("sec") {
        ReplOutput::Value { rendered, .. } => {
            assert!(rendered.contains("[REDACTED:pii]"), "got: {rendered}");
            assert!(rendered.contains("[REDACTED:ferpa]"), "got: {rendered}");
            assert!(
                !rendered.contains("alice@uni.edu"),
                "leaked pii: {rendered}"
            );
            assert!(!rendered.contains("3.9"), "leaked ferpa: {rendered}");
            assert!(rendered.contains("(2 rows, 3 cols)"));
        }
        other => return Err(format!("unexpected repl output: {other:?}").into()),
    }

    let _ = std::fs::remove_dir_all(&tmp);
    let _ = LTy::new(Ty::Unit, TagSet::empty());
    Ok(())
}
