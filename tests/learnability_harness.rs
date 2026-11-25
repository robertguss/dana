#![forbid(unsafe_code)]

//! Phase 5C Deterministic AI Learnability Grading Harness (Dana v0.3).
//!
//! Grades candidate submissions for the 6 unseen tasks specified in
//! `docs/evals/learnability-v0.3.md` across five deterministic gates:
//! 1. Canonical formatting (`dana format --check` / `format_module` equality)
//! 2. Static parse, module/policy resolution (`t2_dana.policy` for T2), type/privacy
//!    verification, and lowering (`parse_module`, `resolve_path`, `check_resolved`, `lower_program`)
//! 3. Author inline `test`/`examples` blocks (`run_program_tests_vm` + reference oracle parity)
//! 4. Hidden functional E2E grading (direct pure-function execution via `eval_exec_entry_vm`
//!    PLUS live `main(...)` execution against hidden CSV, SQLite, Parquet, and Secret fixtures)
//! 5. Hidden privacy-leak & policy audit (T2 FERPA suppression/PII non-leakage and T5 keyed
//!    HMAC pseudonymization, redaction, and runtime `--allow-export health` gate enforcement)

use std::collections::HashMap;
use std::fmt::Write as _;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};

use dana::base::{DiagCode, SourceMap, render_diagnostic};
use dana::check::{check_resolved, parse_policy, resolve_path};
use dana::core::bigint::{BigInt, DEC_SCALE};
use dana::core::syntax::{AggKind, BugKind, ColSpec, Float64, ScalarTy, TableTy, TagSet, Ty};
use dana::db::{SqlParam, open_connection};
use dana::formats::crypto::hmac_sha256_pseudonym;
use dana::formats::csv::read_csv_stream_with_schema;
use dana::formats::parquet::{ParquetCompression, write_parquet_table};
use dana::formats::time::{parse_decimal_bigint_strict, parse_iso_date};
use dana::lower::lower_program;
use dana::oracle::value::{TableRow, TableVal, Val};
use dana::runtime::{
    EvalProgramResult, ExecProgram, RunConfig, RunResult, run_exec_program, run_program_tests,
};
use dana::stats::{linear_regression, pearson_corr, spearman_corr, welch_t_test};
use dana::syntax::{format_module, parse_module};
use dana::vm::{VmConfig, eval_exec_entry_vm, run_exec_program_vm, run_program_tests_vm};

type TestResult<T = ()> = Result<T, Box<dyn std::error::Error>>;

static TMP_SEQ: AtomicU64 = AtomicU64::new(1);

const T2_POLICY_SRC: &str = "\
version 1

min_group_size 5
forbid manual_declassify
forbid repl_show_sensitive

allow console tags []";

const EXPECTED_MODULES: [(u8, &str); 6] = [
    (1, "LedgerEtl"),
    (2, "FerpaSummary"),
    (3, "OrdersAnalytics"),
    (4, "MetricStats"),
    (5, "ClinicExport"),
    (6, "SensorReport"),
];

struct TempDir {
    path: PathBuf,
}

impl TempDir {
    fn new(prefix: &str) -> Result<Self, String> {
        let n = TMP_SEQ.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "dana_learnability_{prefix}_{}_{}",
            std::process::id(),
            n
        ));
        if path.exists() {
            fs::remove_dir_all(&path).map_err(|e| format!("remove stale temp dir: {e}"))?;
        }
        fs::create_dir_all(&path).map_err(|e| format!("create temp dir: {e}"))?;
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

fn dana_bin() -> &'static str {
    env!("CARGO_BIN_EXE_dana")
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

fn dec(s: &str) -> Result<Val, String> {
    parse_decimal_bigint_strict(s)
        .map(Val::Decimal)
        .map_err(|e| format!("invalid decimal `{s}`: {e}"))
}

fn date_val(s: &str) -> Result<Val, String> {
    parse_iso_date(s)
        .map(|d| Val::Date(BigInt::from(d)))
        .map_err(|e| format!("invalid date `{s}`: {e}"))
}

fn float_val(x: f64) -> Val {
    Val::Float(Float64::from_f64(x))
}

fn row(cells: Vec<Val>) -> TableRow {
    TableRow {
        cells,
        group_meta: None,
    }
}

fn col_idx(tv: &TableVal, name: &str) -> Result<usize, String> {
    tv.cols.iter().position(|c| c.name == name).ok_or_else(|| {
        let names: Vec<&str> = tv.cols.iter().map(|c| c.name.as_str()).collect();
        format!("missing expected column `{name}` (found columns {names:?})")
    })
}

fn expect_text<'a>(tv: &'a TableVal, r: usize, col_name: &str) -> Result<&'a str, String> {
    let ci = col_idx(tv, col_name)?;
    match tv.rows.get(r).and_then(|row| row.cells.get(ci)) {
        Some(Val::Text(s)) => Ok(s.as_str()),
        other => Err(format!(
            "row {r} col `{col_name}`: expected Text, got {other:?}"
        )),
    }
}

fn expect_int(tv: &TableVal, r: usize, col_name: &str) -> Result<i64, String> {
    let ci = col_idx(tv, col_name)?;
    match tv.rows.get(r).and_then(|row| row.cells.get(ci)) {
        Some(Val::Int(n)) => n
            .to_i64()
            .ok_or_else(|| format!("row {r} col `{col_name}`: Int out of i64 range")),
        other => Err(format!(
            "row {r} col `{col_name}`: expected Int, got {other:?}"
        )),
    }
}

fn expect_bool(tv: &TableVal, r: usize, col_name: &str) -> Result<bool, String> {
    let ci = col_idx(tv, col_name)?;
    match tv.rows.get(r).and_then(|row| row.cells.get(ci)) {
        Some(Val::Bool(b)) => Ok(*b),
        other => Err(format!(
            "row {r} col `{col_name}`: expected Bool, got {other:?}"
        )),
    }
}

fn expect_date_days(tv: &TableVal, r: usize, col_name: &str) -> Result<i64, String> {
    let ci = col_idx(tv, col_name)?;
    match tv.rows.get(r).and_then(|row| row.cells.get(ci)) {
        Some(Val::Date(d)) => d
            .to_i64()
            .ok_or_else(|| format!("row {r} col `{col_name}`: Date out of i64 range")),
        other => Err(format!(
            "row {r} col `{col_name}`: expected Date, got {other:?}"
        )),
    }
}

fn expect_decimal_approx(
    tv: &TableVal,
    r: usize,
    col_name: &str,
    expected: f64,
    tol: f64,
) -> Result<(), String> {
    let ci = col_idx(tv, col_name)?;
    let raw = match tv.rows.get(r).and_then(|row| row.cells.get(ci)) {
        Some(Val::Decimal(d)) => d,
        Some(Val::OptSome(inner)) => match inner.as_ref() {
            Val::Decimal(d) => d,
            other => {
                return Err(format!(
                    "row {r} col `{col_name}`: expected Some(Decimal), got Some({other:?})"
                ));
            }
        },
        other => {
            return Err(format!(
                "row {r} col `{col_name}`: expected Decimal or Decimal?, got {other:?}"
            ));
        }
    };
    let actual = raw.to_f64() / (DEC_SCALE as f64);
    if (actual - expected).abs() > tol {
        return Err(format!(
            "row {r} col `{col_name}`: expected {expected} (±{tol}), got {actual}"
        ));
    }
    Ok(())
}

fn expect_float_approx(
    tv: &TableVal,
    r: usize,
    col_name: &str,
    expected: f64,
    tol: f64,
) -> Result<(), String> {
    let ci = col_idx(tv, col_name)?;
    let actual = match tv.rows.get(r).and_then(|row| row.cells.get(ci)) {
        Some(Val::Float(f)) => f.to_f64(),
        Some(Val::OptSome(inner)) => match inner.as_ref() {
            Val::Float(f) => f.to_f64(),
            other => {
                return Err(format!(
                    "row {r} col `{col_name}`: expected Some(Float), got Some({other:?})"
                ));
            }
        },
        other => {
            return Err(format!(
                "row {r} col `{col_name}`: expected Float or Float?, got {other:?}"
            ));
        }
    };
    if !actual.is_finite() || (actual - expected).abs() > tol {
        return Err(format!(
            "row {r} col `{col_name}`: expected {expected} (±{tol}), got {actual}"
        ));
    }
    Ok(())
}

fn call_pure_table_fn(
    prog: &ExecProgram,
    fn_name: &str,
    positional_args: Vec<Val>,
) -> Result<(TableVal, TableTy), String> {
    let func = prog
        .find_fun(fn_name)
        .ok_or_else(|| format!("missing required function `{fn_name}`"))?;
    if func.params.len() != positional_args.len() {
        return Err(format!(
            "function `{fn_name}` expects {} parameters, harness supplied {}",
            func.params.len(),
            positional_args.len()
        ));
    }
    let prebound: Vec<(String, Val)> = func
        .params
        .iter()
        .zip(positional_args)
        .map(|((pname, _), val)| (pname.clone(), val))
        .collect();
    let res = eval_exec_entry_vm(
        prog,
        fn_name,
        &prebound,
        &RunConfig::default(),
        &VmConfig::default(),
    );
    match res {
        EvalProgramResult::Ok { val, ret_lty, .. } => match (val.to_table_val(), &ret_lty.ty) {
            (Some(tv), Ty::Table(tt)) => Ok((tv, tt.clone())),
            (_, other_ty) => Err(format!(
                "`{fn_name}` did not return a Table (val={val:?}, ty={other_ty:?})"
            )),
        },
        EvalProgramResult::Stopped { bug, .. } => {
            Err(format!("`{fn_name}` stopped unexpectedly: {bug:?}"))
        }
        EvalProgramResult::Failed { message, .. } => {
            Err(format!("`{fn_name}` failed unexpectedly: {message}"))
        }
    }
}

fn run_main_both(prog: &ExecProgram, cfg: &RunConfig) -> Result<(i64, String, String), String> {
    let vm_res = run_exec_program_vm(prog, cfg, &VmConfig::default());
    let oracle_res = run_exec_program(prog, cfg);
    let (vm_code, vm_out, vm_err) = match vm_res {
        RunResult::Ok {
            exit_code,
            stdout,
            stderr,
        } => (exit_code, stdout.join("\n"), stderr.join("\n")),
        other => return Err(format!("VM main execution failed: {other:?}")),
    };
    let (or_code, _, _) = match oracle_res {
        RunResult::Ok {
            exit_code,
            stdout,
            stderr,
        } => (exit_code, stdout.join("\n"), stderr.join("\n")),
        other => return Err(format!("Oracle main execution failed: {other:?}")),
    };
    if vm_code != or_code {
        return Err(format!(
            "VM vs Oracle exit code mismatch: vm={vm_code}, oracle={or_code}"
        ));
    }
    Ok((vm_code, vm_out, vm_err))
}

fn expected_module_name(task_id: u8) -> Option<&'static str> {
    EXPECTED_MODULES
        .iter()
        .find(|(id, _)| *id == task_id)
        .map(|(_, name)| *name)
}

/// Complete deterministic grade breakdown for a single candidate task submission.
#[derive(Clone, Debug)]
struct TaskGrade {
    task_id: u8,
    file_path: String,
    formatted_cleanly: bool,
    check_passed: bool,
    author_tests_passed: bool,
    author_test_count: usize,
    hidden_e2e_passed: bool,
    privacy_audit_passed: bool,
    diag_codes: Vec<String>,
    errors: Vec<String>,
}

impl TaskGrade {
    fn new(task_id: u8, path: &Path) -> Self {
        Self {
            task_id,
            file_path: path.display().to_string(),
            formatted_cleanly: false,
            check_passed: false,
            author_tests_passed: false,
            author_test_count: 0,
            hidden_e2e_passed: false,
            privacy_audit_passed: false,
            diag_codes: Vec::new(),
            errors: Vec::new(),
        }
    }

    const fn functional_pass(&self) -> bool {
        self.check_passed
            && self.author_tests_passed
            && self.hidden_e2e_passed
            && self.privacy_audit_passed
    }

    const fn final_pass(&self) -> bool {
        self.formatted_cleanly && self.functional_pass()
    }

    fn push_diag_code(&mut self, code: &str) {
        if !self.diag_codes.iter().any(|c| c == code) {
            self.diag_codes.push(code.to_string());
        }
    }
}

/// Deterministically grade a single candidate `.dana` file against all 5 gates for `task_id` (`1..=6`).
fn grade_task_submission(task_id: u8, path: &Path) -> TaskGrade {
    let mut grade = TaskGrade::new(task_id, path);

    let Some(expected_mod) = expected_module_name(task_id) else {
        grade
            .errors
            .push(format!("invalid task_id `{task_id}` (expected 1..=6)"));
        return grade;
    };

    let src = match fs::read_to_string(path) {
        Ok(s) => s,
        Err(e) => {
            grade
                .errors
                .push(format!("cannot read `{}`: {e}", path.display()));
            return grade;
        }
    };

    // Gate 1: Parse + Canonical Format Check (`dana format --check`).
    let mut sm = SourceMap::new();
    let fid = sm.add_file(path.display().to_string(), src.clone());
    let parsed_mod = match parse_module(fid, &src) {
        Ok(m) => m,
        Err(d) => {
            grade.push_diag_code(d.code().as_str());
            grade
                .errors
                .push(format!("parse failed:\n{}", render_diagnostic(&d, &sm)));
            return grade;
        }
    };
    let canonical = format_module(&parsed_mod);
    grade.formatted_cleanly = canonical == src;
    if !grade.formatted_cleanly {
        grade.errors.push(
            "source is not canonically formatted (`dana format --check` differs)".to_string(),
        );
    }

    let actual_mod: String = parsed_mod
        .header
        .path
        .iter()
        .map(|s| s.name.as_str())
        .collect::<Vec<_>>()
        .join(".");
    if actual_mod != expected_mod {
        grade.errors.push(format!(
            "module header mismatch: expected `module {expected_mod}`, found `module {actual_mod}`"
        ));
        return grade;
    }

    // Gate 2: Static Resolve, Type/Privacy/Policy Check, and Lowering.
    let mut check_sm = SourceMap::new();
    let policy = if task_id == 2 {
        let pfid = check_sm.add_file("t2_dana.policy".to_string(), T2_POLICY_SRC.to_string());
        match parse_policy(pfid, T2_POLICY_SRC) {
            Ok(p) => Some(p),
            Err(d) => {
                grade.push_diag_code(d.code().as_str());
                grade.errors.push(format!(
                    "internal error parsing t2_dana.policy:\n{}",
                    render_diagnostic(&d, &check_sm)
                ));
                return grade;
            }
        }
    } else {
        None
    };

    let resolved = match resolve_path(path, policy, &mut check_sm) {
        Ok(r) => r,
        Err(ds) => {
            for d in &ds {
                grade.push_diag_code(d.code().as_str());
                grade
                    .errors
                    .push(format!("resolve: {}", render_diagnostic(d, &check_sm)));
            }
            return grade;
        }
    };
    let checked = match check_resolved(&resolved, &check_sm) {
        Ok(c) => c,
        Err(ds) => {
            for d in &ds {
                grade.push_diag_code(d.code().as_str());
                grade
                    .errors
                    .push(format!("check: {}", render_diagnostic(d, &check_sm)));
            }
            return grade;
        }
    };
    let lowered = match lower_program(checked) {
        Ok(l) => l,
        Err(d) => {
            grade.push_diag_code(d.code().as_str());
            grade
                .errors
                .push(format!("lower: {}", render_diagnostic(&d, &check_sm)));
            return grade;
        }
    };
    grade.check_passed = true;

    // Gate 3: Author Inline Unit Tests (VM + Oracle parity).
    let run_cfg = RunConfig::default();
    let vm_outcomes = run_program_tests_vm(&lowered.exec, None, &run_cfg, &VmConfig::default());
    let oracle_outcomes = run_program_tests(&lowered.exec, None, &run_cfg);
    grade.author_test_count = vm_outcomes.len();
    if vm_outcomes.is_empty() {
        grade
            .errors
            .push("missing required inline `test` block (0 tests found)".to_string());
    } else {
        let mut all_ok = true;
        for (vm_o, or_o) in vm_outcomes.iter().zip(&oracle_outcomes) {
            if !vm_o.passed {
                all_ok = false;
                grade.errors.push(format!(
                    "author test `{}` failed on VM: {:?}",
                    vm_o.name, vm_o.message
                ));
            }
            if !or_o.passed {
                all_ok = false;
                grade.errors.push(format!(
                    "author test `{}` failed on Oracle: {:?}",
                    or_o.name, or_o.message
                ));
            }
        }
        grade.author_tests_passed = all_ok;
    }

    // Gates 4 & 5: Hidden Functional E2E Grading + Hidden Privacy-Leak Audit.
    let (e2e_res, priv_res) = match task_id {
        1 => (grade_t1_hidden(&lowered.exec), Ok(())),
        2 => grade_t2_hidden(&lowered.exec),
        3 => (grade_t3_hidden(&lowered.exec), Ok(())),
        4 => (grade_t4_hidden(&lowered.exec), Ok(())),
        5 => grade_t5_hidden(&lowered.exec, path),
        6 => (grade_t6_hidden(&lowered.exec), Ok(())),
        _ => (Err("unsupported task id".to_string()), Ok(())),
    };

    match e2e_res {
        Ok(()) => grade.hidden_e2e_passed = true,
        Err(e) => grade.errors.push(format!("hidden E2E: {e}")),
    }
    match priv_res {
        Ok(()) => grade.privacy_audit_passed = true,
        Err(e) => grade.errors.push(format!("privacy audit: {e}")),
    }

    grade
}

// ===========================================================================
// Hidden Functional & Privacy Graders (Tasks 1..=6)
// ===========================================================================

fn grade_t1_hidden(prog: &ExecProgram) -> Result<(), String> {
    // 1. Direct pure-function test of `summarize_ledger`.
    let ledger_in = TableVal {
        cols: vec![
            col("txn_id", ScalarTy::Int, &[]),
            col("date", ScalarTy::Date, &[]),
            col("category", ScalarTy::Text, &[]),
            col("amount", ScalarTy::Decimal, &[]),
        ],
        rows: vec![
            row(vec![
                Val::Int(BigInt::from(1i64)),
                date_val("2026-03-01")?,
                Val::Text("Cloud".to_string()),
                dec("120.50")?,
            ]),
            row(vec![
                Val::Int(BigInt::from(2i64)),
                date_val("2026-03-02")?,
                Val::Text("Travel".to_string()),
                dec("85.25")?,
            ]),
            row(vec![
                Val::Int(BigInt::from(3i64)),
                date_val("2026-03-03")?,
                Val::Text("Cloud".to_string()),
                dec("229.50")?,
            ]),
            row(vec![
                Val::Int(BigInt::from(4i64)),
                date_val("2026-03-04")?,
                Val::Text("Meals".to_string()),
                dec("45.00")?,
            ]),
            row(vec![
                Val::Int(BigInt::from(5i64)),
                date_val("2026-03-05")?,
                Val::Text("Travel".to_string()),
                dec("115.25")?,
            ]),
        ],
    };

    let (summary, _) = call_pure_table_fn(prog, "summarize_ledger", vec![Val::Table(ledger_in)])?;
    if summary.rows.len() != 3 {
        return Err(format!(
            "summarize_ledger expected 3 rows, got {}",
            summary.rows.len()
        ));
    }
    let expected = [
        ("Cloud", 2i64, 350.00),
        ("Travel", 2, 200.50),
        ("Meals", 1, 45.00),
    ];
    for (idx, (cat, cnt, tot)) in expected.iter().enumerate() {
        let got_cat = expect_text(&summary, idx, "category")?;
        let got_cnt = expect_int(&summary, idx, "txn_count")?;
        if got_cat != *cat {
            return Err(format!(
                "summarize_ledger row {idx}: expected category `{cat}`, got `{got_cat}`"
            ));
        }
        if got_cnt != *cnt {
            return Err(format!(
                "summarize_ledger row {idx}: expected txn_count {cnt}, got {got_cnt}"
            ));
        }
        expect_decimal_approx(&summary, idx, "total_amount", *tot, 1e-9)?;
    }

    // 2. Live `main` E2E with dirty CSV (2 quarantined rows -> exit code 1).
    let tmp = TempDir::new("t1")?;
    let dirty_path = tmp.path().join("dirty.csv");
    fs::write(
        &dirty_path,
        "\
txn_id,date,category,amount
10,2026-03-01,Cloud,120.00
11,2026-03-02,Travel,150.50
12,2026-03-03,,40.00
13,2026-03-04,Cloud,80.00
14,2026-03-05,Meals,-15.00
15,2026-03-06,Meals,25.00
",
    )
    .map_err(|e| format!("write dirty.csv: {e}"))?;

    let dirty_cfg = RunConfig {
        args: vec![dirty_path.display().to_string()],
        work_dir: Some(tmp.path().to_path_buf()),
        live_io: true,
        ..RunConfig::default()
    };
    let (code, stdout, _) = run_main_both(prog, &dirty_cfg)?;
    if code != 1 {
        return Err(format!("dirty CSV expected exit code 1, got {code}"));
    }
    let p_cloud = stdout
        .find("Cloud")
        .ok_or_else(|| format!("dirty CSV stdout missing `Cloud`: {stdout}"))?;
    let p_travel = stdout
        .find("Travel")
        .ok_or_else(|| format!("dirty CSV stdout missing `Travel`: {stdout}"))?;
    let p_meals = stdout
        .find("Meals")
        .ok_or_else(|| format!("dirty CSV stdout missing `Meals`: {stdout}"))?;
    if !(p_cloud < p_travel && p_travel < p_meals) {
        return Err(format!(
            "dirty CSV stdout categories out of descending order: {stdout}"
        ));
    }
    if !stdout.contains("200") || !stdout.contains("150.5") || !stdout.contains("25") {
        return Err(format!(
            "dirty CSV stdout missing expected totals: {stdout}"
        ));
    }

    // 3. Live `main` E2E with clean CSV (0 bad rows -> exit code 0).
    let clean_path = tmp.path().join("clean.csv");
    fs::write(
        &clean_path,
        "\
txn_id,date,category,amount
20,2026-03-10,Ops,50.00
21,2026-03-11,Ops,75.00
",
    )
    .map_err(|e| format!("write clean.csv: {e}"))?;
    let clean_cfg = RunConfig {
        args: vec![clean_path.display().to_string()],
        work_dir: Some(tmp.path().to_path_buf()),
        live_io: true,
        ..RunConfig::default()
    };
    let (clean_code, clean_out, _) = run_main_both(prog, &clean_cfg)?;
    if clean_code != 0 {
        return Err(format!("clean CSV expected exit code 0, got {clean_code}"));
    }
    if !clean_out.contains("Ops") || !clean_out.contains("125") {
        return Err(format!("clean CSV stdout missing Ops/125: {clean_out}"));
    }

    // 4. Live `main` E2E with missing arg -> exit code 2.
    let no_arg_cfg = RunConfig {
        args: Vec::new(),
        work_dir: Some(tmp.path().to_path_buf()),
        live_io: true,
        ..RunConfig::default()
    };
    let (no_arg_code, _, _) = run_main_both(prog, &no_arg_cfg)?;
    if no_arg_code != 2 {
        return Err(format!(
            "missing CLI arg expected exit code 2, got {no_arg_code}"
        ));
    }

    Ok(())
}

fn grade_t2_hidden(prog: &ExecProgram) -> (Result<(), String>, Result<(), String>) {
    let e2e = grade_t2_hidden_inner(prog);
    match e2e {
        Ok((stdout, stderr, out_tt)) => {
            let priv_check = audit_t2_privacy(prog, &stdout, &stderr, &out_tt);
            (Ok(()), priv_check)
        }
        Err(e) => (
            Err(e),
            Err("skipped privacy audit because T2 hidden E2E failed".to_string()),
        ),
    }
}

fn grade_t2_hidden_inner(prog: &ExecProgram) -> Result<(String, String, TableTy), String> {
    let mut rows = Vec::new();
    let mut csv = String::from("student_id,email,gpa,age,program\n");

    let mut add_student =
        |id: i64, email: &str, gpa: &str, age: i64, program: &str| -> Result<(), String> {
            rows.push(row(vec![
                Val::Int(BigInt::from(id)),
                Val::Text(email.to_string()),
                dec(gpa)?,
                Val::Int(BigInt::from(age)),
                Val::Text(program.to_string()),
            ]));
            let _ = writeln!(csv, "{id},{email},{gpa},{age},{program}");
            Ok(())
        };

    // Cohort 1: CS / under_22 (5 distinct students -> survives, avg_gpa = 3.40)
    for (idx, (age, gpa)) in [
        (18i64, "3.00"),
        (19, "3.20"),
        (20, "3.40"),
        (21, "3.60"),
        (21, "3.80"),
    ]
    .iter()
    .enumerate()
    {
        let id = 990_101 + idx as i64;
        add_student(id, &format!("secret_cs_u22_{id}@priv.edu"), gpa, *age, "CS")?;
    }

    // Cohort 2: CS / 22_to_29 (6 distinct students including boundary age 22 -> survives, avg_gpa = 3.50)
    for (idx, (age, gpa)) in [
        (22i64, "3.00"),
        (23, "3.50"),
        (25, "3.50"),
        (26, "3.50"),
        (28, "3.50"),
        (29, "4.00"),
    ]
    .iter()
    .enumerate()
    {
        let id = 990_201 + idx as i64;
        add_student(id, &format!("secret_cs_mid_{id}@priv.edu"), gpa, *age, "CS")?;
    }

    // Cohort 3: History / 30_plus (5 distinct students including boundary age 30 -> survives, avg_gpa = 3.60)
    for (idx, (age, gpa)) in [
        (30i64, "3.20"),
        (31, "3.40"),
        (35, "3.60"),
        (42, "3.80"),
        (50, "4.00"),
    ]
    .iter()
    .enumerate()
    {
        let id = 990_301 + idx as i64;
        add_student(
            id,
            &format!("secret_hist_{id}@priv.edu"),
            gpa,
            *age,
            "History",
        )?;
    }

    // Suppressed Cohort A: RareCohort / 22_to_29 — 2 distinct students repeated 4x (8 rows, ONLY 2 distinct IDs!)
    for _ in 0..4 {
        add_student(
            990_801,
            "secret_rare_801@priv.edu",
            "3.90",
            25,
            "RareCohort",
        )?;
        add_student(
            990_802,
            "secret_rare_802@priv.edu",
            "3.70",
            26,
            "RareCohort",
        )?;
    }

    // Suppressed Cohort B: TinyMajor / under_22 — 4 distinct students (< 5 -> suppressed)
    for idx in 0..4i64 {
        let id = 990_901 + idx;
        add_student(
            id,
            &format!("secret_tiny_{id}@priv.edu"),
            "3.95",
            20,
            "TinyMajor",
        )?;
    }

    let students_tbl = TableVal {
        cols: vec![
            col("student_id", ScalarTy::Int, &["pii"]),
            col("email", ScalarTy::Text, &["pii"]),
            col("gpa", ScalarTy::Decimal, &["ferpa"]),
            col("age", ScalarTy::Int, &["ferpa"]),
            col("program", ScalarTy::Text, &[]),
        ],
        rows,
    };

    // 1. Direct pure-function check of `program_outcomes`.
    let (out, out_tt) =
        call_pure_table_fn(prog, "program_outcomes", vec![Val::Table(students_tbl)])?;
    if out.rows.len() != 3 {
        return Err(format!(
            "program_outcomes expected 3 surviving cohorts, got {} rows: {:?}",
            out.rows.len(),
            out.rows
        ));
    }
    let expected = [
        ("CS", "22_to_29", 6i64, 3.50),
        ("CS", "under_22", 5, 3.40),
        ("History", "30_plus", 5, 3.60),
    ];
    for (idx, (prog_name, band, cnt, gpa)) in expected.iter().enumerate() {
        let got_prog = expect_text(&out, idx, "program")?;
        let got_band = expect_text(&out, idx, "age_band")?;
        let got_cnt = expect_int(&out, idx, "student_count")?;
        if got_prog != *prog_name || got_band != *band || got_cnt != *cnt {
            return Err(format!(
                "program_outcomes row {idx}: expected ({prog_name}, {band}, {cnt}), got ({got_prog}, {got_band}, {got_cnt})"
            ));
        }
        expect_decimal_approx(&out, idx, "avg_gpa", *gpa, 1e-6)?;
    }

    // 2. Live `main` E2E reading `students.csv`.
    let tmp = TempDir::new("t2")?;
    fs::write(tmp.path().join("students.csv"), &csv)
        .map_err(|e| format!("write students.csv: {e}"))?;
    let cfg = RunConfig {
        work_dir: Some(tmp.path().to_path_buf()),
        live_io: true,
        ..RunConfig::default()
    };
    let (code, stdout, stderr) = run_main_both(prog, &cfg)?;
    if code != 0 {
        return Err(format!("T2 main expected exit code 0, got {code}"));
    }
    for required in ["CS", "22_to_29", "under_22", "History", "30_plus"] {
        if !stdout.contains(required) {
            return Err(format!("T2 stdout missing `{required}`:\n{stdout}"));
        }
    }
    Ok((stdout, stderr, out_tt))
}

fn audit_t2_privacy(
    prog: &ExecProgram,
    stdout: &str,
    stderr: &str,
    out_tt: &TableTy,
) -> Result<(), String> {
    if !out_tt.total_tags().is_empty() {
        return Err(format!(
            "program_outcomes return table still carries sensitive tags: {:?}",
            out_tt.total_tags().elems()
        ));
    }
    let main_fn = prog
        .find_fun("main")
        .ok_or_else(|| "missing `main` function".to_string())?;
    for (pname, plty) in &main_fn.params {
        if let Ty::Console(allows) = &plty.ty
            && !allows.is_empty()
        {
            return Err(format!(
                "T2 main parameter `{pname}` declares non-empty Console allows {:?}",
                allows.elems()
            ));
        }
    }
    let combined = format!("{stdout}\n{stderr}");
    for forbidden in [
        "RareCohort",
        "TinyMajor",
        "@priv.edu",
        "secret_",
        "990101",
        "990201",
        "990301",
        "990801",
        "990901",
    ] {
        if combined.contains(forbidden) {
            return Err(format!(
                "T2 privacy leak: forbidden sensitive/suppressed token `{forbidden}` appeared in output"
            ));
        }
    }
    Ok(())
}

fn grade_t3_hidden(prog: &ExecProgram) -> Result<(), String> {
    let customers = TableVal {
        cols: vec![
            col("customer_id", ScalarTy::Int, &[]),
            col("tier", ScalarTy::Text, &[]),
            col("active?", ScalarTy::Bool, &[]),
        ],
        rows: vec![
            row(vec![
                Val::Int(BigInt::from(1i64)),
                Val::Text("Gold".to_string()),
                Val::Bool(true),
            ]),
            row(vec![
                Val::Int(BigInt::from(2i64)),
                Val::Text("Gold".to_string()),
                Val::Bool(true),
            ]),
            row(vec![
                Val::Int(BigInt::from(3i64)),
                Val::Text("Silver".to_string()),
                Val::Bool(true),
            ]),
            row(vec![
                Val::Int(BigInt::from(4i64)),
                Val::Text("Bronze".to_string()),
                Val::Bool(false),
            ]),
            row(vec![
                Val::Int(BigInt::from(5i64)),
                Val::Text("Silver".to_string()),
                Val::Bool(true),
            ]),
            row(vec![
                Val::Int(BigInt::from(6i64)),
                Val::Text("Bronze".to_string()),
                Val::Bool(false),
            ]),
        ],
    };

    let orders = TableVal {
        cols: vec![
            col("order_id", ScalarTy::Int, &[]),
            col("customer_id", ScalarTy::Int, &[]),
            col("order_date", ScalarTy::Date, &[]),
            col("total", ScalarTy::Decimal, &[]),
        ],
        rows: vec![
            row(vec![
                Val::Int(BigInt::from(101i64)),
                Val::Int(BigInt::from(1i64)),
                date_val("2026-04-01")?,
                dec("100.00")?,
            ]),
            row(vec![
                Val::Int(BigInt::from(102i64)),
                Val::Int(BigInt::from(2i64)),
                date_val("2026-04-01")?,
                dec("200.00")?,
            ]),
            row(vec![
                Val::Int(BigInt::from(103i64)),
                Val::Int(BigInt::from(1i64)),
                date_val("2026-04-02")?,
                dec("500.00")?,
            ]),
            row(vec![
                Val::Int(BigInt::from(104i64)),
                Val::Int(BigInt::from(2i64)),
                date_val("2026-04-03")?,
                dec("700.00")?,
            ]),
            row(vec![
                Val::Int(BigInt::from(105i64)),
                Val::Int(BigInt::from(3i64)),
                date_val("2026-04-01")?,
                dec("80.00")?,
            ]),
            row(vec![
                Val::Int(BigInt::from(106i64)),
                Val::Int(BigInt::from(3i64)),
                date_val("2026-04-02")?,
                dec("120.00")?,
            ]),
            row(vec![
                Val::Int(BigInt::from(107i64)),
                Val::Int(BigInt::from(4i64)),
                date_val("2026-04-01")?,
                dec("999.00")?,
            ]),
        ],
    };

    // 1. Direct pure-function check of `active_tier_daily_revenue`.
    let (rev, _) = call_pure_table_fn(
        prog,
        "active_tier_daily_revenue",
        vec![Val::Table(customers.clone()), Val::Table(orders.clone())],
    )?;
    if rev.rows.len() != 5 {
        return Err(format!(
            "active_tier_daily_revenue expected 5 rows, got {}",
            rev.rows.len()
        ));
    }
    let expected_rev = [
        ("Gold", "2026-04-01", 300.00, 2i64, 300.0),
        ("Gold", "2026-04-02", 500.00, 1, 400.0),
        ("Gold", "2026-04-03", 700.00, 1, 600.0),
        ("Silver", "2026-04-01", 80.00, 1, 80.0),
        ("Silver", "2026-04-02", 120.00, 1, 100.0),
    ];
    for (idx, (tier, dt, daily_rev, cnt, roll)) in expected_rev.iter().enumerate() {
        let got_tier = expect_text(&rev, idx, "tier")?;
        let got_date = expect_date_days(&rev, idx, "order_date")?;
        let exp_date = parse_iso_date(dt).map_err(|e| format!("date parse: {e}"))?;
        let got_cnt = expect_int(&rev, idx, "order_count")?;
        if got_tier != *tier || got_date != exp_date || got_cnt != *cnt {
            return Err(format!(
                "active_tier_daily_revenue row {idx}: expected ({tier}, {dt}, {cnt}), got ({got_tier}, {got_date}, {got_cnt})"
            ));
        }
        expect_decimal_approx(&rev, idx, "daily_revenue", *daily_rev, 1e-9)?;
        expect_float_approx(&rev, idx, "rolling_2d_avg", *roll, 1e-6)?;
    }

    // 2. Direct pure-function check of `customers_without_orders`.
    let (no_orders, _) = call_pure_table_fn(
        prog,
        "customers_without_orders",
        vec![Val::Table(customers), Val::Table(orders)],
    )?;
    if no_orders.rows.len() != 2 {
        return Err(format!(
            "customers_without_orders expected 2 rows, got {}",
            no_orders.rows.len()
        ));
    }
    for (idx, (cid, tier)) in [(5i64, "Silver"), (6, "Bronze")].iter().enumerate() {
        let got_cid = expect_int(&no_orders, idx, "customer_id")?;
        let got_tier = expect_text(&no_orders, idx, "tier")?;
        if got_cid != *cid || got_tier != *tier {
            return Err(format!(
                "customers_without_orders row {idx}: expected ({cid}, {tier}), got ({got_cid}, {got_tier})"
            ));
        }
    }

    // 3. Live `main` E2E against a real SQLite `Store` database.
    let tmp = TempDir::new("t3")?;
    let db_path = tmp.path().join("store.sqlite");
    let db_uri = format!("sqlite://{}", db_path.display());
    {
        let mut conn = open_connection(&db_uri).map_err(|e| format!("open sqlite: {e}"))?;
        conn.execute(
            r#"CREATE TABLE "Customer" (
                "customer_id" INTEGER NOT NULL,
                "tier" TEXT NOT NULL,
                "active?" INTEGER NOT NULL
            )"#,
            &[],
        )
        .map_err(|e| format!("create Customer: {e}"))?;
        conn.execute(
            r#"CREATE TABLE "OrderRow" (
                "order_id" INTEGER NOT NULL,
                "customer_id" INTEGER NOT NULL,
                "order_date" TEXT NOT NULL,
                "total" TEXT NOT NULL
            )"#,
            &[],
        )
        .map_err(|e| format!("create OrderRow: {e}"))?;
        for (cid, tier, active) in [
            (1i64, "Gold", true),
            (2, "Gold", true),
            (3, "Silver", true),
            (4, "Bronze", false),
            (5, "Silver", true),
            (6, "Bronze", false),
        ] {
            conn.execute(
                r#"INSERT INTO "Customer" ("customer_id", "tier", "active?") VALUES (?1, ?2, ?3)"#,
                &[
                    SqlParam::Int(cid),
                    SqlParam::Text(tier.to_string()),
                    SqlParam::Bool(active),
                ],
            )
            .map_err(|e| format!("insert Customer: {e}"))?;
        }
        for (oid, cid, dt, tot) in [
            (101i64, 1i64, "2026-04-01", "100.00"),
            (102, 2, "2026-04-01", "200.00"),
            (103, 1, "2026-04-02", "500.00"),
            (104, 2, "2026-04-03", "700.00"),
            (105, 3, "2026-04-01", "80.00"),
            (106, 3, "2026-04-02", "120.00"),
            (107, 4, "2026-04-01", "999.00"),
        ] {
            conn.execute(
                r#"INSERT INTO "OrderRow" ("order_id", "customer_id", "order_date", "total") VALUES (?1, ?2, ?3, ?4)"#,
                &[
                    SqlParam::Int(oid),
                    SqlParam::Int(cid),
                    SqlParam::Text(dt.to_string()),
                    SqlParam::Decimal(
                        parse_decimal_bigint_strict(tot)
                            .map_err(|e| format!("decimal parse: {e}"))?,
                    ),
                ],
            )
            .map_err(|e| format!("insert OrderRow: {e}"))?;
        }
    }

    let mut db_bindings = HashMap::new();
    db_bindings.insert("Store".to_string(), db_uri);
    let cfg = RunConfig {
        work_dir: Some(tmp.path().to_path_buf()),
        db_bindings,
        live_io: true,
        ..RunConfig::default()
    };
    let (code, stdout, _) = run_main_both(prog, &cfg)?;
    if code != 0 {
        return Err(format!("T3 main expected exit code 0, got {code}"));
    }
    for required in ["Gold", "Silver", "300", "500", "700", "120"] {
        if !stdout.contains(required) {
            return Err(format!("T3 stdout missing `{required}`:\n{stdout}"));
        }
    }
    if stdout.contains("Bronze") || stdout.contains("999") {
        return Err(format!(
            "T3 stdout included inactive Bronze customer:\n{stdout}"
        ));
    }

    Ok(())
}

fn grade_t4_hidden(prog: &ExecProgram) -> Result<(), String> {
    let sample_data: [(&str, &str, f64, f64, f64); 6] = [
        ("E1", "A", 2.0, 4.0, 5.0),
        ("E2", "A", 4.0, 5.0, 9.0),
        ("E3", "A", 4.0, 6.0, 7.0),
        ("E4", "B", 6.0, 10.0, 15.0),
        ("E5", "B", 8.0, 11.0, 15.0),
        ("E6", "B", 10.0, 14.0, 23.0),
    ];

    let wide = TableVal {
        cols: vec![
            col("entity", ScalarTy::Text, &[]),
            col("group_name", ScalarTy::Text, &[]),
            col("q1", ScalarTy::Float, &[]),
            col("q2", ScalarTy::Float, &[]),
            col("q3", ScalarTy::Float, &[]),
        ],
        rows: sample_data
            .iter()
            .map(|(ent, grp, q1, q2, q3)| {
                row(vec![
                    Val::Text((*ent).to_string()),
                    Val::Text((*grp).to_string()),
                    float_val(*q1),
                    float_val(*q2),
                    float_val(*q3),
                ])
            })
            .collect(),
    };

    // 1. Direct pure-function check of `melt_quarters`.
    let (melted, _) = call_pure_table_fn(prog, "melt_quarters", vec![Val::Table(wide.clone())])?;
    if melted.rows.len() != 18 {
        return Err(format!(
            "melt_quarters expected 18 rows, got {}",
            melted.rows.len()
        ));
    }
    if expect_text(&melted, 0, "entity")? != "E1"
        || expect_text(&melted, 0, "group_name")? != "A"
        || expect_text(&melted, 0, "quarter")? != "q1"
    {
        return Err("melt_quarters row 0 mismatch".to_string());
    }
    expect_float_approx(&melted, 0, "score", 2.0, 1e-9)?;
    if expect_text(&melted, 17, "entity")? != "E6"
        || expect_text(&melted, 17, "group_name")? != "B"
        || expect_text(&melted, 17, "quarter")? != "q3"
    {
        return Err("melt_quarters row 17 mismatch".to_string());
    }
    expect_float_approx(&melted, 17, "score", 23.0, 1e-9)?;

    // 2. Direct pure-function check of `quarter_stats` against exact `dana::stats` references.
    let q1s: Vec<f64> = sample_data.iter().map(|r| r.2).collect();
    let q3s: Vec<f64> = sample_data.iter().map(|r| r.4).collect();
    let a_q3: Vec<f64> = sample_data
        .iter()
        .filter(|r| r.1 == "A")
        .map(|r| r.4)
        .collect();
    let b_q3: Vec<f64> = sample_data
        .iter()
        .filter(|r| r.1 == "B")
        .map(|r| r.4)
        .collect();

    let exp_rho = spearman_corr(&q1s, &q3s).ok_or_else(|| "spearman ref failed".to_string())?;
    let exp_ols =
        linear_regression(&q1s, &q3s).ok_or_else(|| "linear_regression ref failed".to_string())?;
    let exp_pred10 = exp_ols.slope * 10.0 + exp_ols.intercept;
    let exp_t = welch_t_test(&a_q3, &b_q3).ok_or_else(|| "welch_t_test ref failed".to_string())?;

    let (stats_tbl, _) = call_pure_table_fn(prog, "quarter_stats", vec![Val::Table(wide)])?;
    if stats_tbl.rows.len() != 1 {
        return Err(format!(
            "quarter_stats expected 1 row, got {}",
            stats_tbl.rows.len()
        ));
    }
    expect_float_approx(&stats_tbl, 0, "r_spearman", exp_rho, 1e-6)?;
    expect_float_approx(&stats_tbl, 0, "slope", exp_ols.slope, 1e-6)?;
    expect_float_approx(&stats_tbl, 0, "pred_10", exp_pred10, 1e-6)?;
    expect_float_approx(&stats_tbl, 0, "p_value", exp_t.p_value, 1e-6)?;

    // 3. Live `main` E2E reading `metrics.csv`.
    let tmp = TempDir::new("t4")?;
    let mut csv = String::from("entity,group_name,q1,q2,q3\n");
    for (ent, grp, q1, q2, q3) in &sample_data {
        let _ = writeln!(csv, "{ent},{grp},{q1},{q2},{q3}");
    }
    fs::write(tmp.path().join("metrics.csv"), csv)
        .map_err(|e| format!("write metrics.csv: {e}"))?;
    let cfg = RunConfig {
        work_dir: Some(tmp.path().to_path_buf()),
        live_io: true,
        ..RunConfig::default()
    };
    let (code, stdout, _) = run_main_both(prog, &cfg)?;
    if code != 0 {
        return Err(format!("T4 main expected exit code 0, got {code}"));
    }
    for required in ["r_spearman", "slope", "pred_10", "p_value"] {
        if !stdout.contains(required) {
            return Err(format!("T4 stdout missing `{required}`:\n{stdout}"));
        }
    }

    Ok(())
}

fn grade_t5_hidden(
    prog: &ExecProgram,
    file_path: &Path,
) -> (Result<(), String>, Result<(), String>) {
    let e2e_res = grade_t5_hidden_e2e(prog);
    let priv_res = grade_t5_hidden_privacy(prog, file_path);
    (e2e_res, priv_res)
}

fn build_t5_fixture() -> (TableVal, String) {
    let visits = TableVal {
        cols: vec![
            col("patient_id", ScalarTy::Text, &["pii"]),
            col("notes", ScalarTy::Text, &["pii"]),
            col("clinic_code", ScalarTy::Text, &[]),
            col("systolic_bp", ScalarTy::Int, &["health"]),
        ],
        rows: vec![
            row(vec![
                Val::Text("PAT-ALPHA-001".to_string()),
                Val::Text("Confidential note alpha-1".to_string()),
                Val::Text("C-WEST".to_string()),
                Val::Int(BigInt::from(142i64)),
            ]),
            row(vec![
                Val::Text("PAT-BETA-002".to_string()),
                Val::Text("Private diagnosis beta-2".to_string()),
                Val::Text("C-EAST".to_string()),
                Val::Int(BigInt::from(118i64)),
            ]),
            row(vec![
                Val::Text("PAT-ALPHA-001".to_string()),
                Val::Text("Follow-up secret alpha-2".to_string()),
                Val::Text("C-EAST".to_string()),
                Val::Int(BigInt::from(128i64)),
            ]),
            row(vec![
                Val::Text("PAT-GAMMA-003".to_string()),
                Val::Text("Sensitive chart gamma-3".to_string()),
                Val::Text("C-WEST".to_string()),
                Val::Int(BigInt::from(130i64)),
            ]),
        ],
    };
    let csv = "\
patient_id,notes,clinic_code,systolic_bp
PAT-ALPHA-001,Confidential note alpha-1,C-WEST,142
PAT-BETA-002,Private diagnosis beta-2,C-EAST,118
PAT-ALPHA-001,Follow-up secret alpha-2,C-EAST,128
PAT-GAMMA-003,Sensitive chart gamma-3,C-WEST,130
"
    .to_string();
    (visits, csv)
}

fn grade_t5_hidden_e2e(prog: &ExecProgram) -> Result<(), String> {
    let (visits, csv) = build_t5_fixture();

    // 1. Direct pure-function check of `prepare_research_export`.
    let secret_cap = Val::CapSecret {
        handle: dana::oracle::value::CapHandle::Real,
        name: "CLINIC_HMAC_KEY".to_string(),
    };
    let (prepared, prep_tt) = call_pure_table_fn(
        prog,
        "prepare_research_export",
        vec![Val::Table(visits), secret_cap],
    )?;
    if prepared.rows.len() != 4 {
        return Err(format!(
            "prepare_research_export expected 4 rows, got {}",
            prepared.rows.len()
        ));
    }

    // Verify sorted order by `(clinic_code, systolic_bp)`.
    let expected_order = [
        ("C-EAST", 118i64),
        ("C-EAST", 128),
        ("C-WEST", 130),
        ("C-WEST", 142),
    ];
    for (idx, (code, bp)) in expected_order.iter().enumerate() {
        let got_code = expect_text(&prepared, idx, "clinic_code")?;
        let got_bp = expect_int(&prepared, idx, "systolic_bp")?;
        let got_notes = expect_text(&prepared, idx, "notes")?;
        let got_pid = expect_text(&prepared, idx, "patient_id")?;
        if got_code != *code || got_bp != *bp {
            return Err(format!(
                "prepare_research_export row {idx}: expected ({code}, {bp}), got ({got_code}, {got_bp})"
            ));
        }
        if got_notes != "[REDACTED]" {
            return Err(format!(
                "prepare_research_export row {idx}: expected `[REDACTED]` notes, got `{got_notes}`"
            ));
        }
        if !got_pid.starts_with("ps_") || got_pid.len() != 35 {
            return Err(format!(
                "prepare_research_export row {idx}: invalid pseudonym token `{got_pid}`"
            ));
        }
    }
    // Rows 1 (C-EAST, 128) and 3 (C-WEST, 142) both belong to PAT-ALPHA-001.
    let alpha_a = expect_text(&prepared, 1, "patient_id")?;
    let alpha_b = expect_text(&prepared, 3, "patient_id")?;
    let beta = expect_text(&prepared, 0, "patient_id")?;
    let gamma = expect_text(&prepared, 2, "patient_id")?;
    if alpha_a != alpha_b {
        return Err(format!(
            "non-deterministic pseudonymization for PAT-ALPHA-001: `{alpha_a}` != `{alpha_b}`"
        ));
    }
    if alpha_a == beta || alpha_a == gamma || beta == gamma {
        return Err("distinct patients collided to the same pseudonym token".to_string());
    }

    // Check static tags: [pii] cleared everywhere, [health] preserved on systolic_bp.
    if prep_tt.total_tags().contains("pii") {
        return Err("prepare_research_export result still carries [pii]".to_string());
    }
    let bp_col = prep_tt
        .find_col("systolic_bp")
        .ok_or_else(|| "missing `systolic_bp` column in return type".to_string())?;
    if !bp_col.tags.contains("health") {
        return Err("prepare_research_export dropped [health] tag from `systolic_bp`".to_string());
    }

    // 2. Live `main` E2E with `--allow-export health` (VM + Oracle).
    let tmp = TempDir::new("t5_e2e")?;
    fs::write(tmp.path().join("visits.csv"), &csv).map_err(|e| format!("write visits.csv: {e}"))?;
    let ok_cfg = RunConfig {
        work_dir: Some(tmp.path().to_path_buf()),
        allow_export: TagSet::singleton("health"),
        live_io: true,
        ..RunConfig::default()
    };
    let (code, stdout, _) = run_main_both(prog, &ok_cfg)?;
    if code != 0 {
        return Err(format!("T5 main expected exit code 0, got {code}"));
    }
    if !stdout.contains("exported 4") {
        return Err(format!("T5 stdout missing `exported 4`:\n{stdout}"));
    }

    let out_csv_path = tmp.path().join("exports/clinic-export.csv");
    let out_csv_bytes = fs::read(&out_csv_path)
        .map_err(|e| format!("read exported CSV `{}`: {e}", out_csv_path.display()))?;
    let export_schema = TableTy {
        cols: vec![
            col("patient_id", ScalarTy::Text, &[]),
            col("notes", ScalarTy::Text, &[]),
            col("clinic_code", ScalarTy::Text, &[]),
            col("systolic_bp", ScalarTy::Int, &[]),
        ],
        ..TableTy::default()
    };
    let (parsed_out, bad_out) =
        read_csv_stream_with_schema(out_csv_bytes.as_slice(), &export_schema, b',', |_, _| true)
            .map_err(|e| format!("parse exported CSV: {e}"))?;
    if !bad_out.rows.is_empty() || parsed_out.rows.len() != 4 {
        return Err(format!(
            "exported CSV row mismatch: ok={}, bad={}",
            parsed_out.rows.len(),
            bad_out.rows.len()
        ));
    }
    if expect_text(&parsed_out, 1, "patient_id")? != expect_text(&parsed_out, 3, "patient_id")? {
        return Err("exported CSV failed deterministic HMAC consistency check".to_string());
    }
    for r in 0..4 {
        if expect_text(&parsed_out, r, "notes")? != "[REDACTED]" {
            return Err(format!("exported CSV row {r} notes not redacted"));
        }
    }

    Ok(())
}

fn grade_t5_hidden_privacy(prog: &ExecProgram, file_path: &Path) -> Result<(), String> {
    let (_, csv) = build_t5_fixture();

    // Probe A: In-process VM run WITHOUT `--allow-export health` MUST stop with ExportGateDenied
    // and MUST NOT write `exports/clinic-export.csv`.
    let tmp_deny = TempDir::new("t5_deny")?;
    fs::write(tmp_deny.path().join("visits.csv"), &csv)
        .map_err(|e| format!("write visits.csv: {e}"))?;
    let deny_cfg = RunConfig {
        work_dir: Some(tmp_deny.path().to_path_buf()),
        allow_export: TagSet::empty(),
        live_io: true,
        ..RunConfig::default()
    };
    match run_exec_program_vm(prog, &deny_cfg, &VmConfig::default()) {
        RunResult::Stopped { bug, .. } if bug.kind == BugKind::ExportGateDenied => {}
        other => {
            return Err(format!(
                "T5 without --allow-export health expected ExportGateDenied, got {other:?}"
            ));
        }
    }
    if tmp_deny.path().join("exports/clinic-export.csv").exists() {
        return Err(
            "T5 wrote exports/clinic-export.csv despite missing --allow-export".to_string(),
        );
    }

    // Probe B: Live `dana run` subprocess with explicit `CLINIC_HMAC_KEY` env var verifies:
    //   1. Non-zero exit without `--allow-export health`
    //   2. Exit 0 WITH `--allow-export health`
    //   3. Exported CSV uses the real `CLINIC_HMAC_KEY` HMAC-SHA256 key (not hardcoded)
    //   4. Zero raw patient IDs or clinical notes leak into exported CSV or stdout/stderr.
    let tmp_cli = TempDir::new("t5_cli")?;
    let script_copy = tmp_cli.path().join("t5.dana");
    fs::copy(file_path, &script_copy).map_err(|e| format!("copy t5.dana: {e}"))?;
    fs::write(tmp_cli.path().join("visits.csv"), &csv)
        .map_err(|e| format!("write visits.csv: {e}"))?;

    let secret_key = "eval-harness-hmac-secret-2026";
    let deny_out = Command::new(dana_bin())
        .current_dir(tmp_cli.path())
        .env("CLINIC_HMAC_KEY", secret_key)
        .args(["run", "t5.dana"])
        .output()
        .map_err(|e| format!("spawn dana run (deny): {e}"))?;
    if deny_out.status.success() {
        return Err("CLI `dana run t5.dana` succeeded without `--allow-export health`".to_string());
    }

    let ok_out = Command::new(dana_bin())
        .current_dir(tmp_cli.path())
        .env("CLINIC_HMAC_KEY", secret_key)
        .args(["run", "--allow-export", "health", "t5.dana"])
        .output()
        .map_err(|e| format!("spawn dana run (allow): {e}"))?;
    if !ok_out.status.success() {
        return Err(format!(
            "CLI `dana run --allow-export health t5.dana` failed: {}",
            String::from_utf8_lossy(&ok_out.stderr)
        ));
    }

    let exported_text = fs::read_to_string(tmp_cli.path().join("exports/clinic-export.csv"))
        .map_err(|e| format!("read CLI exported CSV: {e}"))?;
    let expected_alpha_tok = hmac_sha256_pseudonym(
        secret_key.as_bytes(),
        &Val::Text("PAT-ALPHA-001".to_string()),
    );
    if !exported_text.contains(&expected_alpha_tok) {
        return Err(format!(
            "exported CSV missing exact HMAC-SHA256 token `{expected_alpha_tok}` for CLINIC_HMAC_KEY"
        ));
    }

    let combined = format!(
        "{exported_text}\n{}\n{}",
        String::from_utf8_lossy(&ok_out.stdout),
        String::from_utf8_lossy(&ok_out.stderr)
    );
    for raw_pii in [
        "PAT-ALPHA-001",
        "PAT-BETA-002",
        "PAT-GAMMA-003",
        "Confidential note",
        "Private diagnosis",
        "Follow-up secret",
        "Sensitive chart",
    ] {
        if combined.contains(raw_pii) {
            return Err(format!(
                "T5 privacy leak: raw PII `{raw_pii}` appeared in export or output"
            ));
        }
    }

    Ok(())
}

fn grade_t6_hidden(prog: &ExecProgram) -> Result<(), String> {
    let raw_points: [(&str, &str, f64, f64); 9] = [
        ("S01", "North", 20.0, 100.0),
        ("S02", "North", 21.0, 105.0),
        ("S03", "North", 22.0, 110.0),
        ("S04", "North", 23.0, 115.0),
        ("S05", "South", 24.0, 120.0),
        ("S06", "South", 25.0, 125.0),
        ("S07", "South", 26.0, 130.0),
        ("S08", "South", 27.0, 135.0),
        ("S09", "South", 28.0, 500.0),
    ];

    // Feed unsorted order into `flag_power_outliers` to confirm ascending `.sensor_id` sort!
    let mut rows: Vec<TableRow> = raw_points
        .iter()
        .rev()
        .map(|(sid, zone, tc, pw)| {
            row(vec![
                Val::Text((*sid).to_string()),
                Val::Text((*zone).to_string()),
                float_val(*tc),
                float_val(*pw),
            ])
        })
        .collect();
    let points_tv = TableVal {
        cols: vec![
            col("sensor_id", ScalarTy::Text, &[]),
            col("zone", ScalarTy::Text, &[]),
            col("temp_c", ScalarTy::Float, &[]),
            col("power_w", ScalarTy::Float, &[]),
        ],
        rows: std::mem::take(&mut rows),
    };

    // 1. Direct pure-function check of `flag_power_outliers`.
    let (flagged, _) = call_pure_table_fn(
        prog,
        "flag_power_outliers",
        vec![Val::Table(points_tv.clone())],
    )?;
    if flagged.rows.len() != 9 {
        return Err(format!(
            "flag_power_outliers expected 9 rows, got {}",
            flagged.rows.len()
        ));
    }
    for (idx, (sid, _, _, _)) in raw_points.iter().enumerate() {
        let got_sid = expect_text(&flagged, idx, "sensor_id")?;
        let got_flag = expect_bool(&flagged, idx, "outlier?")?;
        let exp_flag = *sid == "S09";
        if got_sid != *sid || got_flag != exp_flag {
            return Err(format!(
                "flag_power_outliers row {idx}: expected ({sid}, outlier?={exp_flag}), got ({got_sid}, outlier?={got_flag})"
            ));
        }
    }

    // 2. Live `main` E2E reading Zstd-compressed `sensors.parquet`.
    let tmp = TempDir::new("t6")?;
    write_parquet_table(
        &tmp.path().join("sensors.parquet"),
        &points_tv,
        ParquetCompression::Zstd,
    )
    .map_err(|e| format!("write sensors.parquet: {e}"))?;

    let cfg = RunConfig {
        work_dir: Some(tmp.path().to_path_buf()),
        live_io: true,
        ..RunConfig::default()
    };
    let (code, stdout, _) = run_main_both(prog, &cfg)?;
    if code != 0 {
        return Err(format!("T6 main expected exit code 0, got {code}"));
    }
    if stdout.trim().is_empty() {
        return Err("T6 main printed empty stdout summary".to_string());
    }

    let temps: Vec<f64> = raw_points.iter().map(|p| p.2).collect();
    let powers: Vec<f64> = raw_points.iter().map(|p| p.3).collect();
    let exp_r = pearson_corr(&temps, &powers).ok_or_else(|| "pearson ref failed".to_string())?;
    let exp_ols = linear_regression(&temps, &powers)
        .ok_or_else(|| "linear_regression ref failed".to_string())?;
    let r_str = format!("{}", (exp_r * 1000.0).round() / 1000.0);
    let slope_str = format!("{}", (exp_ols.slope * 1000.0).round() / 1000.0);
    let r2_str = format!("{}", (exp_ols.r_squared * 1000.0).round() / 1000.0);
    let expected_title_fragment = format!("Temp vs Power (r = {r_str})");
    let expected_summary_fragment = format!("Slope={slope_str}, R2={r2_str}");

    let html = fs::read_to_string(tmp.path().join("reports/sensors.html"))
        .map_err(|e| format!("read reports/sensors.html: {e}"))?;
    for required in [
        "Sensor Diagnostics",
        "<svg xmlns=\"http://www.w3.org/2000/svg\"",
        "</svg>",
        "<line",
        "class=\"trendline\"",
        expected_title_fragment.as_str(),
        expected_summary_fragment.as_str(),
        "S09",
    ] {
        if !html.contains(required) {
            return Err(format!(
                "reports/sensors.html missing required content `{required}`"
            ));
        }
    }
    if html.contains("NaN") || html.contains("Infinity") {
        return Err("reports/sensors.html contains NaN or Infinity".to_string());
    }

    let md = fs::read_to_string(tmp.path().join("reports/sensors.md"))
        .map_err(|e| format!("read reports/sensors.md: {e}"))?;
    for required in [
        "Sensor Diagnostics",
        expected_summary_fragment.as_str(),
        "S09",
    ] {
        if !md.contains(required) {
            return Err(format!(
                "reports/sensors.md missing required content `{required}`"
            ));
        }
    }
    if md.contains("NaN") || md.contains("Infinity") {
        return Err("reports/sensors.md contains NaN or Infinity".to_string());
    }

    Ok(())
}

// ===========================================================================
// Internal Gold Reference Solutions (Harness Self-Verification Only — NOT in docs/)
// ===========================================================================

const GOLD_T1: &str = r#"module LedgerEtl

schema LedgerRow
  txn_id: Int
  date: Date
  category: Text where not .empty?
  amount: Decimal where . > 0
end

fn summarize_ledger(rows: Table(LedgerRow)) : Table(category: Text, txn_count: Int, total_amount: Decimal)
  promise unique(.category)

  rows
    |> group_by(.category)
    |> summarize(txn_count: count(), total_amount: sum(.amount))
    |> sort_by(.category)
    |> sort_desc(.total_amount)
end

fn main(args: Args, files: ReadFiles, console: Console) : Int
  path = args.first.or_return(2)
  (rows, bad_rows) = try files.read_csv(path, as: LedgerRow)
  summary = summarize_ledger(rows)
  console.print_table(summary)
  if bad_rows.empty?: 0 else: 1
end

test "quarantines invalid rows and summarizes ledger descending"
  csv = """
    txn_id,date,category,amount
    1,2026-01-01,Travel,50.00
    2,2026-01-02,Cloud,120.00
    3,2026-01-03,,10.00
    4,2026-01-04,Travel,25.00
  """
  files = Files.in_memory({"ledger.csv": csv}).read_only
  (rows, bad) = try files.read_csv("ledger.csv", as: LedgerRow)
  summary = summarize_ledger(rows)
  assert bad.count() == 1
  assert summary.count() == 2
  assert summary.first!.category == "Cloud"
  assert summary.first!.total_amount == 120.00
end
"#;

const GOLD_T2: &str = r#"module FerpaSummary

schema StudentRecord
  student_id: Int [pii]
  email: Text [pii]
  gpa: Decimal [ferpa] where . >= 0.0 and . <= 4.0
  age: Int [ferpa] where . >= 14 and . <= 120
  program: Text
end

fn program_outcomes(students: Table(StudentRecord))
  promise unique(.program, .age_band)
  promise all(.student_count >= 5)

  students
    |> derive(age_band: bucket(.age, cuts: [22, 30], labels: ["under_22", "22_to_29", "30_plus"]))
    |> group_by(.program, .age_band)
    |> summarize(student_count: count_distinct(.student_id), avg_gpa: mean(.gpa))
    |> suppress_small_groups(min: 5, distinct_by: .student_id)
    |> sort_by(.program, .age_band)
end

fn main(files: ReadFiles, console: Console) : Int
  (students, _bad) = try files.read_csv("students.csv", as: StudentRecord)
  console.print_table(program_outcomes(students))
  0
end

test "suppresses groups below 5 distinct students while keeping larger cohorts"
  students = table
    | student_id | email           | gpa  | age | program |
    | 1          | "s1@univ.edu"   | 3.50 | 20  | "CS"    |
    | 2          | "s2@univ.edu"   | 3.60 | 21  | "CS"    |
    | 3          | "s3@univ.edu"   | 3.70 | 19  | "CS"    |
    | 4          | "s4@univ.edu"   | 3.80 | 20  | "CS"    |
    | 5          | "s5@univ.edu"   | 3.90 | 18  | "CS"    |
    | 99         | "rare@univ.edu" | 4.00 | 35  | "Latin" |
  end
  out = program_outcomes(students)
  assert out.count() == 1
  assert out.first!.program == "CS"
  assert out.first!.age_band == "under_22"
  assert out.first!.student_count == 5
end
"#;

const GOLD_T3: &str = r#"module OrdersAnalytics

schema Customer
  customer_id: Int
  tier: Text
  active?: Bool
end

schema OrderRow
  order_id: Int
  customer_id: Int
  order_date: Date
  total: Decimal where . > 0
end

fn active_tier_daily_revenue(customers: Table(Customer), orders: Table(OrderRow))
  active_customers = customers |> where(.active?)
  orders
    |> join_many_to_one(active_customers, on: .customer_id)
    |> group_by(.tier, .order_date)
    |> summarize(daily_revenue: sum(.total), order_count: count())
    |> window(rolling_2d_avg: rolling_mean(.daily_revenue, rows: 2), over: [.tier], order: .order_date)
    |> sort_by(.tier, .order_date)
end

fn customers_without_orders(customers: Table(Customer), orders: Table(OrderRow))
  customers
    |> anti_join(orders, on: .customer_id)
    |> select(.customer_id, .tier)
    |> sort_by(.customer_id)
end

fn main(db: ReadDB(Store), console: Console) : Int
  revenue = active_tier_daily_revenue(db.table(Customer), db.table(OrderRow))
  console.print_table(revenue)
  0
end

test "computes active tier rolling revenue and anti-join idle customers"
  customers = table
    | customer_id | tier     | active? |
    | 1           | "Gold"   | true    |
    | 2           | "Silver" | true    |
    | 3           | "Bronze" | false   |
  end
  orders = table
    | order_id | customer_id | order_date | total  |
    | 10       | 1           | 2026-05-01 | 100.00 |
    | 11       | 1           | 2026-05-02 | 200.00 |
    | 12       | 3           | 2026-05-01 | 50.00  |
  end
  db = DB.in_memory(Store, {Customer: customers, OrderRow: orders})
  rev = active_tier_daily_revenue(db.table(Customer), db.table(OrderRow))
  idle = customers_without_orders(db.table(Customer), db.table(OrderRow))
  assert rev.count() == 2
  assert idle.count() == 1
  assert idle.first!.customer_id == 2
end
"#;

const GOLD_T4: &str = r#"module MetricStats
use Stats

schema WideMetric
  entity: Text
  group_name: Text
  q1: Float
  q2: Float
  q3: Float
end

fn melt_quarters(rows: Table(WideMetric))
  rows
    |> pivot_longer(cols: [.q1, .q2, .q3], names_to: "quarter", values_to: "score")
    |> sort_by(.entity, .quarter)
end

fn quarter_stats(rows: Table(WideMetric)) : Table(r_spearman: Float, slope: Float, pred_10: Float, p_value: Float)
  r_spearman = Stats.corr(rows, x: .q1, y: .q3, method: :spearman)
  model = Stats.linear_regression(rows, x: .q1, y: .q3)
  pred_10 = model.predict(10.0)
  ab = Stats.t_test(rows |> where(.group_name == "A"), rows |> where(.group_name == "B"), column: .q3)
  table
    | r_spearman | slope       | pred_10 | p_value    |
    | r_spearman | model.slope | pred_10 | ab.p_value |
  end
end

fn main(files: ReadFiles, console: Console) : Int
  (rows, _bad) = try files.read_csv("metrics.csv", as: WideMetric)
  console.print_table(quarter_stats(rows))
  0
end

test "melts quarters and computes spearman, regression, and welch t-test"
  rows = table
    | entity | group_name | q1  | q2  | q3   |
    | "A1"   | "A"        | 1.0 | 2.0 | 3.0  |
    | "A2"   | "A"        | 2.0 | 3.0 | 5.0  |
    | "B1"   | "B"        | 3.0 | 5.0 | 10.0 |
    | "B2"   | "B"        | 4.0 | 6.0 | 12.0 |
  end
  long = melt_quarters(rows)
  stats = quarter_stats(rows)
  assert long.count() == 12
  assert stats.count() == 1
  assert (stats.first!.r_spearman - 1.0).abs < 1e-9
  assert stats.first!.slope > 2.0
end
"#;

const GOLD_T5: &str = r#"module ClinicExport

schema ClinicVisit
  patient_id: Text [pii]
  notes: Text [pii]
  clinic_code: Text
  systolic_bp: Int [health] where . > 0
end

fn prepare_research_export(visits: Table(ClinicVisit), key: Secret("CLINIC_HMAC_KEY"))
  visits
    |> pseudonymize(.patient_id, key: key)
    |> redact(.notes)
    |> select(.patient_id, .notes, .clinic_code, .systolic_bp)
    |> sort_by(.clinic_code, .systolic_bp)
end

fn main(
  files: ReadFiles,
  key: Secret("CLINIC_HMAC_KEY"),
  out: WriteFiles("exports/", allows: [health]),
  console: Console
) : Int
  (visits, _bad) = try files.read_csv("visits.csv", as: ClinicVisit)
  prepared = prepare_research_export(visits, key)
  try out.write_csv("clinic-export.csv", prepared)
  console.print("exported #{prepared.count()}")
  0
end

test "pseudonymizes patient_id deterministically and redacts clinical notes"
  visits = table
    | patient_id | notes         | clinic_code | systolic_bp |
    | "P-1"      | "secret note" | "C1"        | 120         |
    | "P-1"      | "second note" | "C2"        | 130         |
  end
  out = prepare_research_export(visits, Secret.fake("test-key"))
  assert out.count() == 2
  assert out.first!.notes == "[REDACTED]"
  assert out.first!.patient_id != "P-1"
end
"#;

const GOLD_T6: &str = r#"module SensorReport
use Stats

schema SensorPoint
  sensor_id: Text
  zone: Text
  temp_c: Float
  power_w: Float where . >= 0.0
end

fn flag_power_outliers(points: Table(SensorPoint))
  Stats.outliers(points, column: .power_w, method: :zscore, threshold: 2.0) |> sort_by(.sensor_id)
end

fn main(files: ReadFiles, out: WriteFiles("reports/"), console: Console) : Int
  points = try files.read_parquet("sensors.parquet", as: SensorPoint)
  flagged = flag_power_outliers(points)
  r = Stats.corr(points, x: .temp_c, y: .power_w, method: :pearson)
  model = Stats.linear_regression(points, x: .temp_c, y: .power_w)
  chart = points
    |> chart_scatter(
      x: .temp_c,
      y: .power_w,
      color: .zone,
      trendline: model,
      title: "Temp vs Power (r = #{r.round(3)})"
    )
  report = Report.new("Sensor Diagnostics")
    |> add_summary("Slope=#{model.slope.round(3)}, R2=#{model.r_squared.round(3)}")
    |> add_chart(chart)
    |> add_table(flagged |> where(.outlier?))
  try out.write_html("sensors.html", report)
  try out.write_markdown("sensors.md", report)
  console.print(
    "Sensor report written: r=#{r.round(3)}, outliers=#{(flagged |> where(.outlier?)).count()}"
  )
  0
end

test "flags injected high-power outlier spike"
  points = table
    | sensor_id | zone | temp_c | power_w |
    | "S1"      | "A"  | 20.0   | 100.0   |
    | "S2"      | "A"  | 21.0   | 102.0   |
    | "S3"      | "A"  | 22.0   | 101.0   |
    | "S4"      | "B"  | 23.0   | 99.0    |
    | "S5"      | "B"  | 24.0   | 100.0   |
    | "S6"      | "B"  | 25.0   | 101.0   |
    | "S7"      | "B"  | 26.0   | 450.0   |
  end
  flagged = flag_power_outliers(points)
  spikes = flagged |> where(.outlier?)
  assert spikes.count() == 1
  assert spikes.first!.sensor_id == "S7"
end
"#;

fn canonicalize_dana(src: &str) -> Result<String, String> {
    let mut sm = SourceMap::new();
    let fid = sm.add_file("gold.dana".to_string(), src.to_string());
    let m = parse_module(fid, src).map_err(|d| render_diagnostic(&d, &sm))?;
    Ok(format_module(&m))
}

fn json_escape(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for ch in s.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
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
    out
}

fn render_grade_json(stage: &str, g: &TaskGrade) -> String {
    let codes: Vec<String> = g.diag_codes.iter().map(|c| json_escape(c)).collect();
    let errs: Vec<String> = g.errors.iter().map(|e| json_escape(e)).collect();
    format!(
        "{{\"task_id\":{},\"stage\":{},\"file\":{},\"formatted_cleanly\":{},\"check_passed\":{},\"author_tests_passed\":{},\"author_test_count\":{},\"hidden_e2e_passed\":{},\"privacy_audit_passed\":{},\"functional_pass\":{},\"final_pass\":{},\"diag_codes\":[{}],\"errors\":[{}]}}",
        g.task_id,
        json_escape(stage),
        json_escape(&g.file_path),
        g.formatted_cleanly,
        g.check_passed,
        g.author_tests_passed,
        g.author_test_count,
        g.hidden_e2e_passed,
        g.privacy_audit_passed,
        g.functional_pass(),
        g.final_pass(),
        codes.join(","),
        errs.join(",")
    )
}

// ===========================================================================
// Harness Self-Verification & External Evaluation Entrypoint Tests
// ===========================================================================

#[test]
fn harness_gold_solutions_pass_all_6_tasks() -> TestResult {
    let tmp = TempDir::new("gold_all_6")?;
    let golds: [(u8, &str, &str); 6] = [
        (1, "t1.dana", GOLD_T1),
        (2, "t2.dana", GOLD_T2),
        (3, "t3.dana", GOLD_T3),
        (4, "t4.dana", GOLD_T4),
        (5, "t5.dana", GOLD_T5),
        (6, "t6.dana", GOLD_T6),
    ];

    for (task_id, fname, raw_src) in golds {
        // Verify each gold constant is already canonically formatted via `dana format`.
        let formatted = canonicalize_dana(raw_src)?;
        assert_eq!(
            raw_src, formatted,
            "GOLD_T{task_id} should be canonically formatted:\n--- expected ---\n{formatted}"
        );

        let path = tmp.path().join(fname);
        fs::write(&path, raw_src)?;
        let grade = grade_task_submission(task_id, &path);
        assert!(
            grade.final_pass(),
            "GOLD_T{task_id} failed grading: {grade:#?}"
        );
        assert!(grade.formatted_cleanly, "T{task_id} format gate");
        assert!(grade.check_passed, "T{task_id} check gate");
        assert!(grade.author_tests_passed, "T{task_id} author tests gate");
        assert!(grade.author_test_count >= 1, "T{task_id} test count");
        assert!(grade.hidden_e2e_passed, "T{task_id} hidden E2E gate");
        assert!(grade.privacy_audit_passed, "T{task_id} privacy audit gate");
        assert!(grade.errors.is_empty(), "T{task_id} unexpected errors");
    }
    Ok(())
}

#[test]
fn harness_rejects_broken_and_leaky_submissions() -> TestResult {
    let tmp = TempDir::new("neg_checks")?;

    // 1. Unformatted valid T1 fails `formatted_cleanly` while passing functional gates.
    let unformatted_t1 = GOLD_T1.replace("  txn_id: Int", "    txn_id: Int");
    let p1 = tmp.path().join("t1_unfmt.dana");
    fs::write(&p1, unformatted_t1)?;
    let g1 = grade_task_submission(1, &p1);
    assert!(!g1.formatted_cleanly, "expected format failure");
    assert!(g1.functional_pass(), "expected functional pass: {g1:#?}");
    assert!(!g1.final_pass(), "unformatted file must fail final gate");

    // 2. T2 leaking raw StudentRecord to public Console fails static check with E0201.
    let leaky_t2 = r#"module FerpaSummary

schema StudentRecord
  student_id: Int [pii]
  email: Text [pii]
  gpa: Decimal [ferpa] where . >= 0.0 and . <= 4.0
  age: Int [ferpa] where . >= 14 and . <= 120
  program: Text
end

fn main(files: ReadFiles, console: Console) : Int
  (students, _bad) = try files.read_csv("students.csv", as: StudentRecord)
  console.print_table(students)
  0
end
"#;
    let p2 = tmp.path().join("t2_leak.dana");
    fs::write(&p2, leaky_t2)?;
    let g2 = grade_task_submission(2, &p2);
    assert!(!g2.check_passed, "raw PII print must fail static check");
    assert!(
        g2.diag_codes
            .iter()
            .any(|c| c == DiagCode::PrivacyError.as_str()),
        "expected PrivacyError ({}), got {:?}",
        DiagCode::PrivacyError.as_str(),
        g2.diag_codes
    );

    // 3. T2 using `min: 3` below `t2_dana.policy` floor fails static check with PrivacyError.
    let low_k_t2 = GOLD_T2.replace("min: 5", "min: 3");
    let p2k = tmp.path().join("t2_lowk.dana");
    fs::write(&p2k, low_k_t2)?;
    let g2k = grade_task_submission(2, &p2k);
    assert!(!g2k.check_passed, "min: 3 must fail policy check");
    assert!(
        g2k.diag_codes
            .iter()
            .any(|c| c == DiagCode::PrivacyError.as_str()),
        "expected PrivacyError ({}), got {:?}",
        DiagCode::PrivacyError.as_str(),
        g2k.diag_codes
    );

    // 4. T5 forgetting `redact(.notes)` fails static check with PrivacyError (PII to health-only WriteFiles).
    let unredacted_t5 = GOLD_T5.replace("    |> redact(.notes)\n", "");
    let p5 = tmp.path().join("t5_unredacted.dana");
    fs::write(&p5, unredacted_t5)?;
    let g5 = grade_task_submission(5, &p5);
    assert!(
        !g5.check_passed,
        "unredacted [pii] notes to health-only sink must fail static check"
    );
    assert!(
        g5.diag_codes
            .iter()
            .any(|c| c == DiagCode::PrivacyError.as_str()),
        "expected PrivacyError ({}), got {:?}",
        DiagCode::PrivacyError.as_str(),
        g5.diag_codes
    );

    // 5. T1 sorted ascending instead of descending fails hidden E2E gate.
    let wrong_sort_t1 = GOLD_T1.replace("sort_desc(.total_amount)", "sort_by(.total_amount)");
    let p1s = tmp.path().join("t1_wrong_sort.dana");
    fs::write(&p1s, wrong_sort_t1)?;
    let g1s = grade_task_submission(1, &p1s);
    assert!(g1s.check_passed, "wrong sort still type-checks");
    assert!(!g1s.hidden_e2e_passed, "wrong sort must fail hidden E2E");
    assert!(!g1s.final_pass());

    Ok(())
}

#[test]
fn protocol_doc_matches_harness_contract() -> TestResult {
    let doc_path = repo_root().join("docs/evals/learnability-v0.3.md");
    let doc = fs::read_to_string(&doc_path)?;

    // 1. Verify exact embedded `t2_dana.policy` matches `T2_POLICY_SRC` byte-for-byte.
    let pol_start = doc
        .find("<!-- BEGIN T2_DANA_POLICY -->")
        .ok_or("missing BEGIN T2_DANA_POLICY marker")?;
    let pol_end = doc
        .find("<!-- END T2_DANA_POLICY -->")
        .ok_or("missing END T2_DANA_POLICY marker")?;
    let pol_section = &doc[pol_start..pol_end];
    let fence_start = pol_section
        .find("```text\n")
        .ok_or("missing ```text fence in T2_DANA_POLICY")?
        + "```text\n".len();
    let fence_end = pol_section[fence_start..]
        .find("\n```")
        .ok_or("missing closing ``` fence in T2_DANA_POLICY")?;
    let doc_policy = &pol_section[fence_start..fence_start + fence_end];
    assert_eq!(
        doc_policy.trim(),
        T2_POLICY_SRC.trim(),
        "docs/evals/learnability-v0.3.md t2_dana.policy drifted from harness T2_POLICY_SRC"
    );

    // 2. Verify standalone `tasks.md` block exists and specifies every required contract token 1-for-1.
    let tasks_start = doc
        .find("<!-- BEGIN STANDALONE TASKS.MD -->")
        .ok_or("missing BEGIN STANDALONE TASKS.MD marker")?;
    let tasks_end = doc
        .find("<!-- END STANDALONE TASKS.MD -->")
        .ok_or("missing END STANDALONE TASKS.MD marker")?;
    let tasks_md = &doc[tasks_start..tasks_end];

    let required_tokens = [
        // Task 1
        "t1.dana",
        "module LedgerEtl",
        "schema LedgerRow",
        "txn_id: Int",
        "date: Date",
        "category: Text where not .empty?",
        "amount: Decimal where . > 0",
        "summarize_ledger",
        "promise unique(.category)",
        "fn main(args: Args, files: ReadFiles, console: Console) : Int",
        "args.first.or_return(2)",
        // Task 2
        "t2.dana",
        "module FerpaSummary",
        "t2_dana.policy",
        "schema StudentRecord",
        "student_id: Int [pii]",
        "email: Text [pii]",
        "gpa: Decimal [ferpa] where . >= 0.0 and . <= 4.0",
        "age: Int [ferpa] where . >= 14 and . <= 120",
        "program: Text",
        "program_outcomes",
        "bucket(.age, cuts: [22, 30], labels: [\"under_22\", \"22_to_29\", \"30_plus\"])",
        "suppress_small_groups(min: 5, distinct_by: .student_id)",
        "promise unique(.program, .age_band)",
        "promise all(.student_count >= 5)",
        "\"students.csv\"",
        // Task 3
        "t3.dana",
        "module OrdersAnalytics",
        "schema Customer",
        "customer_id: Int",
        "tier: Text",
        "active?: Bool",
        "schema OrderRow",
        "order_id: Int",
        "order_date: Date",
        "total: Decimal where . > 0",
        "active_tier_daily_revenue",
        "join_many_to_one",
        "rolling_mean(.daily_revenue, rows: 2)",
        "customers_without_orders",
        "anti_join(orders, on: .customer_id)",
        "fn main(db: ReadDB(Store), console: Console) : Int",
        // Task 4
        "t4.dana",
        "module MetricStats",
        "use Stats",
        "schema WideMetric",
        "melt_quarters",
        "pivot_longer(cols: [.q1, .q2, .q3], names_to: \"quarter\", values_to: \"score\")",
        "quarter_stats",
        "Stats.corr(rows, x: .q1, y: .q3, method: :spearman)",
        "Stats.linear_regression(rows, x: .q1, y: .q3)",
        "model.predict(10.0)",
        "Stats.t_test",
        "\"metrics.csv\"",
        // Task 5
        "t5.dana",
        "module ClinicExport",
        "schema ClinicVisit",
        "patient_id: Text [pii]",
        "notes: Text [pii]",
        "clinic_code: Text",
        "systolic_bp: Int [health] where . > 0",
        "prepare_research_export",
        "Secret(\"CLINIC_HMAC_KEY\")",
        "WriteFiles(\"exports/\", allows: [health])",
        "\"visits.csv\"",
        "\"clinic-export.csv\"",
        "exported #{prepared.count()}",
        // Task 6
        "t6.dana",
        "module SensorReport",
        "schema SensorPoint",
        "sensor_id: Text",
        "zone: Text",
        "temp_c: Float",
        "power_w: Float where . >= 0.0",
        "flag_power_outliers",
        "Stats.outliers(points, column: .power_w, method: :zscore, threshold: 2.0)",
        "\"sensors.parquet\"",
        "WriteFiles(\"reports/\")",
        "\"sensors.html\"",
        "\"sensors.md\"",
        "Report.new(\"Sensor Diagnostics\")",
    ];
    for tok in required_tokens {
        assert!(
            tasks_md.contains(tok),
            "docs/evals/learnability-v0.3.md standalone tasks.md missing required contract token `{tok}`"
        );
    }

    // 3. Verify pre-declared model matrix & v0.3 gate criteria are present (and NO fake results).
    for meta in [
        "claude-sonnet-5-5",
        "claude-haiku-5-5",
        "gemini-4-neon",
        "gemini-4-argon",
        ">= 85%",
        "v0.3",
        "Pre-Registration",
    ] {
        assert!(
            doc.contains(meta),
            "docs/evals/learnability-v0.3.md missing protocol requirement `{meta}`"
        );
    }

    Ok(())
}

fn grade_submission_dir(dir: &Path) -> Result<(String, String), String> {
    if !dir.is_dir() {
        return Err(format!(
            "DANA_EVAL_SUBMISSION_DIR is not a directory: `{}`",
            dir.display()
        ));
    }

    let dir_str = dir.display().to_string();
    let mut json_entries = Vec::new();
    let mut attempt1_func_pass = 0usize;
    let mut attempt1_strict_pass = 0usize;
    let mut attempt1_present = 0usize;
    let mut final_func_pass = 0usize;
    let mut final_strict_pass = 0usize;
    let mut final_present = 0usize;

    let mut md = String::new();
    let _ = writeln!(md, "### Learnability Grading Report: `{dir_str}`\n");
    let _ = writeln!(
        md,
        "| Task | Stage | Format | Check | Author Tests | Hidden E2E | Privacy | Functional | Final | Diag Codes |"
    );
    let _ = writeln!(
        md,
        "| --- | --- | :---: | :---: | :---: | :---: | :---: | :---: | :---: | --- |"
    );

    for task_id in 1..=6u8 {
        for (stage, filename) in [
            ("attempt1", format!("t{task_id}.attempt1.dana")),
            ("final", format!("t{task_id}.dana")),
        ] {
            let path = dir.join(&filename);
            if !path.exists() {
                continue;
            }
            let g = grade_task_submission(task_id, &path);
            if stage == "attempt1" {
                attempt1_present += 1;
                if g.functional_pass() {
                    attempt1_func_pass += 1;
                }
                if g.final_pass() {
                    attempt1_strict_pass += 1;
                }
            } else {
                final_present += 1;
                if g.functional_pass() {
                    final_func_pass += 1;
                }
                if g.final_pass() {
                    final_strict_pass += 1;
                }
            }
            let yn = |b: bool| if b { "PASS" } else { "FAIL" };
            let codes = if g.diag_codes.is_empty() {
                "-".to_string()
            } else {
                g.diag_codes.join(", ")
            };
            let _ = writeln!(
                md,
                "| T{task_id} | {stage} | {} | {} | {} ({}) | {} | {} | {} | {} | {codes} |",
                yn(g.formatted_cleanly),
                yn(g.check_passed),
                yn(g.author_tests_passed),
                g.author_test_count,
                yn(g.hidden_e2e_passed),
                yn(g.privacy_audit_passed),
                yn(g.functional_pass()),
                yn(g.final_pass()),
            );
            json_entries.push(render_grade_json(stage, &g));
        }
    }

    let _ = writeln!(
        md,
        "\n- **Attempt 1 (First-Shot):** {attempt1_func_pass}/{attempt1_present} functional, {attempt1_strict_pass}/{attempt1_present} strict (incl. format)"
    );
    let _ = writeln!(
        md,
        "- **Final (Compiler-Assisted):** {final_func_pass}/{final_present} functional, {final_strict_pass}/{final_present} strict (incl. format)"
    );

    let json = format!(
        "DANA_LEARNABILITY_JSON={{\"dir\":{},\"attempt1_present\":{},\"attempt1_functional_pass\":{},\"attempt1_strict_pass\":{},\"final_present\":{},\"final_functional_pass\":{},\"final_strict_pass\":{},\"results\":[{}]}}",
        json_escape(&dir_str),
        attempt1_present,
        attempt1_func_pass,
        attempt1_strict_pass,
        final_present,
        final_func_pass,
        final_strict_pass,
        json_entries.join(",")
    );
    Ok((md, json))
}

#[test]
fn submission_dir_scorer_reports_attempt1_and_final_json_and_markdown() -> TestResult {
    let tmp = TempDir::new("dir_scorer")?;
    let golds: [(u8, &str); 6] = [
        (1, GOLD_T1),
        (2, GOLD_T2),
        (3, GOLD_T3),
        (4, GOLD_T4),
        (5, GOLD_T5),
        (6, GOLD_T6),
    ];
    for (task_id, src) in golds {
        fs::write(tmp.path().join(format!("t{task_id}.attempt1.dana")), src)?;
        fs::write(tmp.path().join(format!("t{task_id}.dana")), src)?;
    }
    let (md, json) = grade_submission_dir(tmp.path())?;
    assert!(md.contains("6/6 functional, 6/6 strict"), "{md}");
    assert!(
        json.contains("\"attempt1_present\":6,\"attempt1_functional_pass\":6,\"attempt1_strict_pass\":6,\"final_present\":6,\"final_functional_pass\":6,\"final_strict_pass\":6"),
        "{json}"
    );
    Ok(())
}

#[test]
fn grade_external_submission_dir_if_set() -> TestResult {
    let Ok(dir_str) = std::env::var("DANA_EVAL_SUBMISSION_DIR") else {
        return Ok(());
    };
    let (md, json) = grade_submission_dir(Path::new(&dir_str))?;
    println!("{md}");
    println!("{json}");
    Ok(())
}
