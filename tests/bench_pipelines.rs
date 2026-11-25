#![forbid(unsafe_code)]

//! Phase 5B smoke & documentation-lockstep test suite:
//! 1. Extracts every `<!-- dana-example: file -->` fenced ` ```dana ` block from
//!    `docs/reference/README.md` and `README.md` and verifies it passes the full
//!    `dana check` pipeline (`parse -> resolve -> check -> lower`) with 0 errors
//!    (plus runs embedded `test` blocks on both the vectorized VM and reference oracle).
//! 2. Compiles and executes all 4 `benchmarks/w*.dana` pipelines end-to-end on compact
//!    CSV, Parquet, and SQLite fixtures across BOTH the 2,048-row vectorized columnar VM
//!    (with SQL pushdown) and the naive reference oracle, verifying exact output parity
//!    and zero privacy/runtime errors.

use std::collections::HashMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

use dana::base::{SourceMap, render_diagnostic};
use dana::check::{check_resolved, resolve_module, resolve_path};
use dana::core::bigint::BigInt;
use dana::core::syntax::{AggKind, ColSpec, Float64, ScalarTy, TagSet};
use dana::db::sqlite::SqliteDriver;
use dana::db::{SqlDialect, SqliteUri};
use dana::formats::parquet::{
    ParquetCompression, read_parquet_file_with_schema, write_parquet_table,
};
use dana::lower::lower_program;
use dana::oracle::value::{TableRow, TableVal, Val};
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
            "dana_bench_smoke_{prefix}_{}_{}",
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

fn col(name: &str, ty: ScalarTy) -> ColSpec {
    ColSpec {
        name: name.to_string(),
        ty,
        tags: TagSet::empty(),
        bucketed: false,
        agg_kind: AggKind::Raw,
    }
}

fn compile_file(rel_path: &str) -> Result<dana::runtime::ExecProgram, String> {
    let path = repo_root().join(rel_path);
    let mut sm = SourceMap::new();
    let resolved = resolve_path(&path, None, &mut sm).map_err(|ds| {
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

fn compile_source(label: &str, src: &str) -> Result<dana::runtime::ExecProgram, String> {
    let mut sm = SourceMap::new();
    let fid = sm.add_file(label.to_string(), src.to_string());
    let ast = parse_module(fid, src).map_err(|d| render_diagnostic(&d, &sm))?;
    let resolved = resolve_module(fid, ast, None).map_err(|ds| {
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

fn extract_file_examples(md_text: &str) -> Vec<(usize, String)> {
    let mut blocks = Vec::new();
    let mut next_is_file = false;
    let mut in_block = false;
    let mut block_is_file = false;
    let mut start_line = 0usize;
    let mut buf = Vec::new();

    for (idx, line) in md_text.lines().enumerate() {
        let line_no = idx + 1;
        let trimmed = line.trim();
        if let Some(rest) = trimmed.strip_prefix("<!--")
            && let Some(inner) = rest.strip_suffix("-->")
        {
            let tag = inner.trim();
            if let Some(after) = tag.strip_prefix("dana-example:") {
                next_is_file = after.trim() == "file";
                continue;
            }
        }
        if !in_block && trimmed == "```dana" {
            in_block = true;
            block_is_file = next_is_file;
            next_is_file = false;
            start_line = line_no + 1;
            buf.clear();
            continue;
        }
        if in_block && trimmed == "```" {
            if block_is_file {
                let mut code = buf.join("\n");
                code.push('\n');
                blocks.push((start_line, code));
            }
            in_block = false;
            block_is_file = false;
            continue;
        }
        if in_block {
            buf.push(line);
        }
    }
    blocks
}

fn assert_inline_tests_pass(prog: &dana::runtime::ExecProgram, label: &str) -> TestResult {
    let cfg = RunConfig::default();
    let vm_cfg = VmConfig {
        batch_size: 4,
        parallel_threshold_rows: 4,
        max_threads: Some(2),
        optimize: true,
        ..VmConfig::default()
    };
    let oracle_res = run_program_tests(prog, None, &cfg);
    let vm_res = run_program_tests_vm(prog, None, &cfg, &vm_cfg);
    if oracle_res.is_empty() {
        return Err(format!("{label}: expected at least one inline test block").into());
    }
    assert_eq!(oracle_res.len(), vm_res.len());
    for (o, v) in oracle_res.iter().zip(&vm_res) {
        if !o.passed {
            return Err(format!("{label} oracle test `{}` failed: {:?}", o.name, o.message).into());
        }
        if !v.passed {
            return Err(format!("{label} vm test `{}` failed: {:?}", v.name, v.message).into());
        }
    }
    Ok(())
}

fn assert_run_ok(res: RunResult, label: &str) -> Result<(i64, Vec<String>, Vec<String>), String> {
    match res {
        RunResult::Ok {
            exit_code,
            stdout,
            stderr,
        } => Ok((exit_code, stdout, stderr)),
        RunResult::Stopped {
            bug,
            stdout,
            stderr,
        } => Err(format!(
            "{label}: stopped ({:?}): {} | stdout={stdout:?} stderr={stderr:?}",
            bug.kind, bug.message
        )),
        RunResult::Failed {
            message,
            stdout,
            stderr,
        } => Err(format!(
            "{label}: failed: {message} | stdout={stdout:?} stderr={stderr:?}"
        )),
    }
}

// ===========================================================================
// 1. Documentation Lockstep: All `<!-- dana-example: file -->` blocks check!
// ===========================================================================

#[test]
fn reference_and_readme_file_examples_pass_dana_check() -> TestResult {
    let root = repo_root();
    let docs = ["docs/reference/README.md", "README.md"];
    let mut total_blocks = 0usize;
    let mut total_inline_tests = 0usize;

    for rel in docs {
        let path = root.join(rel);
        let text = fs::read_to_string(&path)?;
        let blocks = extract_file_examples(&text);
        assert!(
            !blocks.is_empty(),
            "{rel}: expected at least one `<!-- dana-example: file -->` block"
        );

        for (line_no, code) in blocks {
            total_blocks += 1;
            let label = format!("{rel}:{line_no}");
            let prog = compile_source(&label, &code)
                .map_err(|e| format!("{label} failed `dana check`:\n{e}"))?;

            // If this doc example includes `test` or `examples` blocks, execute them on both VM & oracle!
            let cfg = RunConfig::default();
            let vm_cfg = VmConfig::default();
            let oracle_out = run_program_tests(&prog, None, &cfg);
            if !oracle_out.is_empty() {
                let vm_out = run_program_tests_vm(&prog, None, &cfg, &vm_cfg);
                assert_eq!(oracle_out.len(), vm_out.len());
                for (o, v) in oracle_out.iter().zip(&vm_out) {
                    assert!(
                        o.passed,
                        "{label} oracle test `{}` failed: {:?}",
                        o.name, o.message
                    );
                    assert!(
                        v.passed,
                        "{label} vm test `{}` failed: {:?}",
                        v.name, v.message
                    );
                    total_inline_tests += 1;
                }
            }
        }
    }

    assert!(
        total_blocks >= 8,
        "expected at least 8 file examples across docs/reference/README.md and README.md, found {total_blocks}"
    );
    assert!(
        total_inline_tests >= 4,
        "expected embedded doc example tests to run, ran {total_inline_tests}"
    );
    Ok(())
}

// ===========================================================================
// 2. Benchmark W1: CSV Quarantine + Pure UDF + GroupBy/Summarize/Sort
// ===========================================================================

#[test]
fn bench_w1_csv_udf_etl_vm_and_oracle() -> TestResult {
    let prog = compile_file("benchmarks/w1_csv_udf_etl.dana")
        .map_err(|e| format!("compile w1 failed:\n{e}"))?;
    assert_inline_tests_pass(&prog, "w1")?;

    let tmp = TempDir::new("w1")?;
    let csv_path = tmp.path().join("orders.csv");
    let csv_data = "\
order_id,region,category,tier,qty,unit_price,tax_rate
1,north,books,3,5,20.00,0.10
2,north,books,1,0,15.00,0.05
3,north,books,1,10,10.00,0.05
4,south,software,2,4,50.00,0.08
5,south,software,1,2,BAD_PRICE,0.08
6,east,hardware,1,1,30.00,0.05
7,west,services,1,-3,25.00,0.05
8,east,hardware,2,3,40.00,0.10
";
    fs::write(&csv_path, csv_data)?;

    let vm_dir = tmp.path().join("vm_work");
    let oracle_dir = tmp.path().join("oracle_work");
    fs::create_dir_all(&vm_dir)?;
    fs::create_dir_all(&oracle_dir)?;

    let vm_cfg_run = RunConfig {
        args: vec![csv_path.to_string_lossy().into_owned()],
        work_dir: Some(vm_dir.clone()),
        live_io: true,
        ..RunConfig::default()
    };
    let oracle_cfg_run = RunConfig {
        args: vec![csv_path.to_string_lossy().into_owned()],
        work_dir: Some(oracle_dir.clone()),
        live_io: true,
        ..RunConfig::default()
    };
    let vm_engine = VmConfig {
        batch_size: 2,
        parallel_threshold_rows: 2,
        max_threads: Some(2),
        optimize: true,
        ..VmConfig::default()
    };

    let (vm_code, vm_stdout, vm_stderr) =
        assert_run_ok(run_exec_program_vm(&prog, &vm_cfg_run, &vm_engine), "w1 vm")?;
    let (or_code, or_stdout, or_stderr) =
        assert_run_ok(run_exec_program(&prog, &oracle_cfg_run), "w1 oracle")?;

    assert_eq!(vm_code, 0);
    assert_eq!(or_code, 0);
    assert!(vm_stderr.is_empty());
    assert!(or_stderr.is_empty());
    assert_eq!(vm_stdout, or_stdout);
    assert_eq!(vm_stdout, vec!["W1 ok: valid=6 bad=2 groups=3".to_string()]);

    let vm_out = fs::read_to_string(vm_dir.join("bench-out/w1_summary.csv"))?;
    let or_out = fs::read_to_string(oracle_dir.join("bench-out/w1_summary.csv"))?;
    assert_eq!(vm_out, or_out, "W1 VM vs oracle CSV mismatch");
    // Expected exact totals (sorted desc):
    // south/software: row4 = 50*4*0.92*1.08 = 198.72 (1 order, qty 4)
    // north/books: row1 = 20*5*0.85*1.10 = 93.50; row3 = 10*10*0.95*1.05 = 99.75 -> 193.25 (2 orders, qty 15)
    // east/hardware: row6 = 30*1*1.00*1.05 = 31.50; row8 = 40*3*0.92*1.10 = 121.44 -> 152.94 (2 orders, qty 4)
    assert!(
        vm_out.contains("south,software,198.72,4,1"),
        "got:\n{vm_out}"
    );
    assert!(vm_out.contains("north,books,193.25,15,2"), "got:\n{vm_out}");
    assert!(
        vm_out.contains("east,hardware,152.94,4,2"),
        "got:\n{vm_out}"
    );
    Ok(())
}

// ===========================================================================
// 3. Benchmark W2: Parquet Join (Many-to-One) + Inlined UDF + Aggregation
// ===========================================================================

#[test]
fn bench_w2_columnar_join_analytics_vm_and_oracle() -> TestResult {
    let prog = compile_file("benchmarks/w2_columnar_join_analytics.dana")
        .map_err(|e| format!("compile w2 failed:\n{e}"))?;
    assert_inline_tests_pass(&prog, "w2")?;

    let tmp = TempDir::new("w2")?;
    let fact_path = tmp.path().join("sales.parquet");
    let dim_path = tmp.path().join("products.parquet");

    let sales_tv = TableVal {
        cols: vec![
            col("sale_id", ScalarTy::Int),
            col("product_id", ScalarTy::Int),
            col("channel", ScalarTy::Text),
            col("units", ScalarTy::Int),
            col("discount_bps", ScalarTy::Int),
        ],
        rows: vec![
            TableRow {
                cells: vec![
                    Val::Int(BigInt::from(1i64)),
                    Val::Int(BigInt::from(101i64)),
                    Val::Text("web".to_string()),
                    Val::Int(BigInt::from(2i64)),
                    Val::Int(BigInt::from(1000i64)),
                ],
                group_meta: None,
            },
            TableRow {
                cells: vec![
                    Val::Int(BigInt::from(2i64)),
                    Val::Int(BigInt::from(102i64)),
                    Val::Text("web".to_string()),
                    Val::Int(BigInt::from(3i64)),
                    Val::Int(BigInt::from(0i64)),
                ],
                group_meta: None,
            },
            TableRow {
                cells: vec![
                    Val::Int(BigInt::from(3i64)),
                    Val::Int(BigInt::from(101i64)),
                    Val::Text("retail".to_string()),
                    Val::Int(BigInt::from(1i64)),
                    Val::Int(BigInt::from(500i64)),
                ],
                group_meta: None,
            },
            TableRow {
                cells: vec![
                    Val::Int(BigInt::from(4i64)),
                    Val::Int(BigInt::from(103i64)),
                    Val::Text("web".to_string()),
                    Val::Int(BigInt::from(4i64)),
                    Val::Int(BigInt::from(2000i64)),
                ],
                group_meta: None,
            },
        ],
    };
    let prod_tv = TableVal {
        cols: vec![
            col("product_id", ScalarTy::Int),
            col("department", ScalarTy::Text),
            col("list_price", ScalarTy::Float),
            col("unit_cost", ScalarTy::Float),
            col("hazardous?", ScalarTy::Bool),
        ],
        rows: vec![
            TableRow {
                cells: vec![
                    Val::Int(BigInt::from(101i64)),
                    Val::Text("tools".to_string()),
                    Val::Float(Float64::from_f64(100.0)),
                    Val::Float(Float64::from_f64(40.0)),
                    Val::Bool(false),
                ],
                group_meta: None,
            },
            TableRow {
                cells: vec![
                    Val::Int(BigInt::from(102i64)),
                    Val::Text("tools".to_string()),
                    Val::Float(Float64::from_f64(50.0)),
                    Val::Float(Float64::from_f64(20.0)),
                    Val::Bool(true),
                ],
                group_meta: None,
            },
            TableRow {
                cells: vec![
                    Val::Int(BigInt::from(103i64)),
                    Val::Text("garden".to_string()),
                    Val::Float(Float64::from_f64(25.0)),
                    Val::Float(Float64::from_f64(10.0)),
                    Val::Bool(false),
                ],
                group_meta: None,
            },
        ],
    };

    write_parquet_table(&fact_path, &sales_tv, ParquetCompression::Zstd)?;
    write_parquet_table(&dim_path, &prod_tv, ParquetCompression::Zstd)?;

    let vm_dir = tmp.path().join("vm_work");
    let oracle_dir = tmp.path().join("oracle_work");
    fs::create_dir_all(&vm_dir)?;
    fs::create_dir_all(&oracle_dir)?;

    let args = vec![
        fact_path.to_string_lossy().into_owned(),
        dim_path.to_string_lossy().into_owned(),
    ];
    let vm_cfg_run = RunConfig {
        args: args.clone(),
        work_dir: Some(vm_dir.clone()),
        live_io: true,
        ..RunConfig::default()
    };
    let oracle_cfg_run = RunConfig {
        args,
        work_dir: Some(oracle_dir.clone()),
        live_io: true,
        ..RunConfig::default()
    };
    let vm_engine = VmConfig {
        batch_size: 2,
        parallel_threshold_rows: 2,
        max_threads: Some(2),
        optimize: true,
        ..VmConfig::default()
    };

    let (vm_code, vm_stdout, _) =
        assert_run_ok(run_exec_program_vm(&prog, &vm_cfg_run, &vm_engine), "w2 vm")?;
    let (or_code, or_stdout, _) =
        assert_run_ok(run_exec_program(&prog, &oracle_cfg_run), "w2 oracle")?;

    assert_eq!(vm_code, 0);
    assert_eq!(or_code, 0);
    assert_eq!(vm_stdout, or_stdout);
    assert_eq!(
        vm_stdout,
        vec!["W2 ok: sales=4 products=3 groups=3".to_string()]
    );

    let vm_out = fs::read_to_string(vm_dir.join("bench-out/w2_summary.csv"))?;
    let or_out = fs::read_to_string(oracle_dir.join("bench-out/w2_summary.csv"))?;
    assert_eq!(vm_out, or_out, "W2 VM vs oracle CSV mismatch");
    // garden/web: 25*0.8*4 = 80 rev, (20-10-0.5)*4 = 38 margin, 4 units, 1 txn
    assert!(vm_out.contains("garden,web,80,38,4,1"), "got:\n{vm_out}");
    assert!(
        vm_out.contains("tools,retail,95,54.5,1,1"),
        "got:\n{vm_out}"
    );
    assert!(vm_out.contains("tools,web,330,181.5,5,2"), "got:\n{vm_out}");
    Ok(())
}

// ===========================================================================
// 4. Benchmark W3: SQLite Pushdown + [pii]/[ferpa] Privacy + Window
// ===========================================================================

#[test]
fn bench_w3_sqlite_pushdown_privacy_vm_and_oracle() -> TestResult {
    let prog = compile_file("benchmarks/w3_sqlite_pushdown_privacy.dana")
        .map_err(|e| format!("compile w3 failed:\n{e}"))?;
    assert_inline_tests_pass(&prog, "w3")?;

    // Verify SQL pushdown + full FERPA/PII declassification in `dana explain`!
    let report = dana::cli::render_explain_report(
        &prog,
        Some(SqlDialect::Sqlite),
        None,
        Path::new("benchmarks/w3_sqlite_pushdown_privacy.dana"),
    );
    assert!(
        report.contains("FROM \"StudentEnrollment\" WHERE")
            && report.contains("[SQL PUSHDOWN -> sqlite]")
            && report.contains("CASE WHEN (\"age_years\" < ?)")
            && report.contains("OUTPUT: PUBLIC"),
        "expected parameterized SQLite pushdown and PUBLIC output in explain:\n{report}"
    );

    let tmp = TempDir::new("w3")?;
    let db_path = tmp.path().join("registrar.sqlite");
    let db_uri = format!("sqlite://{}", db_path.display());

    let mut conn = SqliteDriver::open(&SqliteUri {
        path: db_path.to_string_lossy().into_owned(),
        read_only: false,
    })?;
    let ddl = r#"
        CREATE TABLE "StudentEnrollment" (
            "enrollment_id" INTEGER PRIMARY KEY,
            "student_id" INTEGER NOT NULL,
            "student_email" TEXT NOT NULL,
            "department" TEXT NOT NULL,
            "term_year" INTEGER NOT NULL,
            "term_seq" INTEGER NOT NULL,
            "active?" INTEGER NOT NULL,
            "age_years" INTEGER NOT NULL,
            "grade_points" REAL NOT NULL
        );
    "#;
    let mut sql_lines = vec![ddl.to_string(), "BEGIN;".to_string()];
    let mut eid = 1i64;
    // 6 distinct CS students across 3 terms (2024..2026) in 22_to_29 age band -> MUST publish!
    for (term_idx, year) in [(1, 2024), (2, 2025), (3, 2026)] {
        for sid in 1..=6 {
            let gpa = 3.0 + (term_idx as f64) * 0.2;
            sql_lines.push(format!(
                "INSERT INTO \"StudentEnrollment\" VALUES ({eid}, {sid}, 's{sid}@edu', 'CS', {year}, {term_idx}, 1, 25, {gpa});"
            ));
            eid += 1;
        }
    }
    // Filtered-out rows (term_year = 2022, active? = 0) -> excluded by SQLite pushdown WHERE
    sql_lines.push(format!(
        "INSERT INTO \"StudentEnrollment\" VALUES ({eid}, 99, 'old@edu', 'CS', 2022, 1, 1, 25, 1.0);"
    ));
    eid += 1;
    sql_lines.push(format!(
        "INSERT INTO \"StudentEnrollment\" VALUES ({eid}, 98, 'inact@edu', 'CS', 2025, 2, 0, 25, 1.0);"
    ));
    eid += 1;
    // RareStudies: 1 distinct student taking 8 courses -> MUST be suppressed by distinct_by!
    for _ in 0..8 {
        sql_lines.push(format!(
            "INSERT INTO \"StudentEnrollment\" VALUES ({eid}, 500, 'rare@edu', 'RareStudies', 2025, 1, 1, 25, 4.0);"
        ));
        eid += 1;
    }
    sql_lines.push("COMMIT;".to_string());
    conn.execute_batch(&sql_lines.join("\n"))?;
    drop(conn);

    let vm_dir = tmp.path().join("vm_work");
    let oracle_dir = tmp.path().join("oracle_work");
    fs::create_dir_all(&vm_dir)?;
    fs::create_dir_all(&oracle_dir)?;

    let mut db_bindings = HashMap::new();
    db_bindings.insert("Registrar".to_string(), db_uri);

    let vm_cfg_run = RunConfig {
        work_dir: Some(vm_dir.clone()),
        live_io: true,
        db_bindings: db_bindings.clone(),
        ..RunConfig::default()
    };
    let oracle_cfg_run = RunConfig {
        work_dir: Some(oracle_dir.clone()),
        live_io: true,
        db_bindings,
        ..RunConfig::default()
    };
    let vm_engine = VmConfig {
        batch_size: 4,
        parallel_threshold_rows: 4,
        max_threads: Some(2),
        optimize: true,
        ..VmConfig::default()
    };

    let (vm_code, vm_stdout, _) =
        assert_run_ok(run_exec_program_vm(&prog, &vm_cfg_run, &vm_engine), "w3 vm")?;
    let (or_code, or_stdout, _) =
        assert_run_ok(run_exec_program(&prog, &oracle_cfg_run), "w3 oracle")?;

    assert_eq!(vm_code, 0);
    assert_eq!(or_code, 0);
    assert_eq!(vm_stdout, or_stdout);
    assert_eq!(vm_stdout, vec!["W3 ok: published_cells=3".to_string()]);

    let vm_out = fs::read_to_string(vm_dir.join("bench-out/w3_summary.csv"))?;
    let or_out = fs::read_to_string(oracle_dir.join("bench-out/w3_summary.csv"))?;
    assert_eq!(vm_out, or_out, "W3 VM vs oracle CSV mismatch");
    assert!(
        !vm_out.contains("RareStudies"),
        "FERPA small-group suppression leaked RareStudies:\n{vm_out}"
    );
    assert!(
        !vm_out.contains("@edu"),
        "PII email leaked into W3 output:\n{vm_out}"
    );
    // Term 1 avg=3.2 roll=3.2; Term 2 avg=3.4 roll=3.3; Term 3 avg=3.6 roll=3.4
    let data_lines: Vec<&str> = vm_out.lines().skip(1).collect();
    assert_eq!(data_lines.len(), 3, "got:\n{vm_out}");
    let expected = [(1, 3.2_f64, 3.2_f64), (2, 3.4, 3.3), (3, 3.6, 3.4)];
    for (line, (term, exp_avg, exp_roll)) in data_lines.iter().zip(expected) {
        let cols: Vec<&str> = line.split(',').collect();
        assert_eq!(cols.len(), 7, "bad csv line: {line}");
        assert_eq!(cols[0], "CS");
        assert_eq!(cols[1], "22_to_29");
        assert_eq!(cols[2].parse::<i64>()?, term);
        assert_eq!(cols[3].parse::<i64>()?, 6);
        assert_eq!(cols[4].parse::<i64>()?, 6);
        assert!(
            (cols[5].parse::<f64>()? - exp_avg).abs() < 1e-12,
            "line: {line}"
        );
        assert!(
            (cols[6].parse::<f64>()? - exp_roll).abs() < 1e-12,
            "line: {line}"
        );
    }
    Ok(())
}

// ===========================================================================
// 5. Benchmark W4: Zstd Parquet Round-Trip + Stats + Profile + HTML Report
// ===========================================================================

#[test]
fn bench_w4_parquet_stats_report_vm_and_oracle() -> TestResult {
    let prog = compile_file("benchmarks/w4_parquet_stats_report.dana")
        .map_err(|e| format!("compile w4 failed:\n{e}"))?;
    assert_inline_tests_pass(&prog, "w4")?;

    let tmp = TempDir::new("w4")?;
    let pq_path = tmp.path().join("telemetry.parquet");

    let mut rows = Vec::new();
    for i in 1..=20i64 {
        let zone = if i % 2 == 0 { "us-east" } else { "eu-west" };
        let load = (i as f64) * 4.0;
        let latency = 10.0 + 1.5 * load;
        let healthy = i != 10 && i != 20;
        rows.push(TableRow {
            cells: vec![
                Val::Int(BigInt::from(i)),
                Val::Text(zone.to_string()),
                Val::Float(Float64::from_f64(load)),
                Val::Float(Float64::from_f64(latency)),
                Val::Bool(healthy),
            ],
            group_meta: None,
        });
    }
    let tv = TableVal {
        cols: vec![
            col("reading_id", ScalarTy::Int),
            col("zone", ScalarTy::Text),
            col("load_pct", ScalarTy::Float),
            col("latency_ms", ScalarTy::Float),
            col("healthy?", ScalarTy::Bool),
        ],
        rows,
    };
    write_parquet_table(&pq_path, &tv, ParquetCompression::Zstd)?;

    let vm_dir = tmp.path().join("vm_work");
    let oracle_dir = tmp.path().join("oracle_work");
    fs::create_dir_all(&vm_dir)?;
    fs::create_dir_all(&oracle_dir)?;

    let vm_cfg_run = RunConfig {
        args: vec![pq_path.to_string_lossy().into_owned()],
        work_dir: Some(vm_dir.clone()),
        live_io: true,
        ..RunConfig::default()
    };
    let oracle_cfg_run = RunConfig {
        args: vec![pq_path.to_string_lossy().into_owned()],
        work_dir: Some(oracle_dir.clone()),
        live_io: true,
        ..RunConfig::default()
    };
    let vm_engine = VmConfig {
        batch_size: 4,
        parallel_threshold_rows: 4,
        max_threads: Some(2),
        optimize: true,
        ..VmConfig::default()
    };

    let (vm_code, vm_stdout, _) =
        assert_run_ok(run_exec_program_vm(&prog, &vm_cfg_run, &vm_engine), "w4 vm")?;
    let (or_code, or_stdout, _) =
        assert_run_ok(run_exec_program(&prog, &oracle_cfg_run), "w4 oracle")?;

    assert_eq!(vm_code, 0);
    assert_eq!(or_code, 0);
    assert_eq!(vm_stdout, or_stdout);
    assert!(
        vm_stdout
            .last()
            .is_some_and(|l| l.contains("W4 ok: clean=18 r=1 slope=1.5")),
        "unexpected W4 stdout: {vm_stdout:?}"
    );

    let vm_stats = fs::read_to_string(vm_dir.join("bench-out/w4_stats.csv"))?;
    let or_stats = fs::read_to_string(oracle_dir.join("bench-out/w4_stats.csv"))?;
    assert_eq!(vm_stats, or_stats, "W4 VM vs oracle stats CSV mismatch");
    assert!(vm_stats.contains("18,1,1.5,10,1"), "got:\n{vm_stats}");

    let vm_zones = fs::read_to_string(vm_dir.join("bench-out/w4_zones.csv"))?;
    let or_zones = fs::read_to_string(oracle_dir.join("bench-out/w4_zones.csv"))?;
    assert_eq!(vm_zones, or_zones, "W4 VM vs oracle zones CSV mismatch");

    let html = fs::read_to_string(vm_dir.join("bench-out/w4_report.html"))?;
    assert!(html.contains("<svg xmlns=\"http://www.w3.org/2000/svg\""));
    assert!(html.contains("Telemetry Performance &amp; Regression Report"));
    assert!(!html.contains("NaN"));

    // Verify written Zstd Parquet round-trips cleanly back with all 18 rows!
    let clean_schema = dana::core::syntax::TableTy {
        cols: vec![
            col("reading_id", ScalarTy::Int),
            col("zone", ScalarTy::Text),
            col("load_pct", ScalarTy::Float),
            col("latency_ms", ScalarTy::Float),
            col("healthy?", ScalarTy::Bool),
            col("load_ratio", ScalarTy::Float),
        ],
        ..dana::core::syntax::TableTy::default()
    };
    let roundtripped = read_parquet_file_with_schema(
        &vm_dir.join("bench-out/w4_clean.parquet"),
        &clean_schema,
        |_, _| true,
    )?;
    assert_eq!(roundtripped.rows.len(), 18);
    Ok(())
}
