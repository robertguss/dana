#![forbid(unsafe_code)]

//! Phase 4C comprehensive end-to-end test suite:
//! - SHA-256 hash-pinned pure-by-default `vendor/` modules (`vendor/vendor.lock`,
//!   `dana vendor pin|verify`, automatic resolver verification, tamper/unpinned/purity rejections)
//! - Safe interactive REPL (`dana repl`, `--eval`, piped stdin, multi-line `... end` blocks,
//!   all 8 meta-commands, automatic `[REDACTED:<tags>]` redaction for scalars/tables/`row_tags`,
//!   `--show-sensitive` vs `dana.policy` `forbid repl_show_sensitive` hard-fail, read-only default,
//!   SQLite `--db` pushdown, and `untyped.read_{csv,jsonl,parquet,xlsx}` + `:infer-schema`)
//! - All 10 real-world `examples/*.dana` executed live end-to-end (`main(...)`) across BOTH the
//!   vectorized columnar VM and the reference evaluator with real CSV, `.jsonl.gz`, `.parquet`,
//!   `.xlsx`, SQLite databases, and loopback OpenSSL TLS HTTPS fixtures.

use std::collections::HashMap;
use std::fs;
use std::io::{BufRead, BufReader, Cursor, Write};
use std::net::TcpListener;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};
use std::thread;

use dana::base::{DiagCode, SourceMap, render_diagnostic};
use dana::check::{
    check_resolved, parse_policy, parse_vendor_lock, pin_vendor_dir, resolve_path,
    verify_vendor_dir,
};
use dana::cli::run_cli;
use dana::core::bigint::BigInt;
use dana::core::syntax::{AggKind, BugKind, ColSpec, Float64, ScalarTy, TableTy, TagSet};
use dana::db::{SqlParam, open_connection};
use dana::ffi::{GzipWriter, TlsServerAcceptor};
use dana::formats::parquet::{
    ParquetCompression, read_parquet_file_with_schema, write_parquet_table,
};
use dana::formats::time::{parse_decimal_bigint_strict, parse_iso_date, parse_iso_timestamp};
use dana::formats::xlsx::{read_xlsx_file_with_schema, write_xlsx_file};
use dana::lower::lower_program;
use dana::oracle::value::{TableRow, TableVal, Val, val_eq};
use dana::repl::{ReplConfig, ReplOutput, ReplSession, run_repl_reader};
use dana::runtime::{RunConfig, RunResult, run_exec_program, run_program_tests};
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
            "dana_phase4c_{prefix}_{}_{}",
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

fn opt(ty: ScalarTy) -> ScalarTy {
    ScalarTy::Option(Box::new(ty))
}

fn table_ty(cols: Vec<ColSpec>) -> TableTy {
    TableTy {
        cols,
        ..TableTy::default()
    }
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

// ===========================================================================
// 1. SHA-256 Hash-Pinned Pure-by-Default `vendor/` Module Tests
// ===========================================================================

#[test]
fn vendor_pin_verify_import_and_run_e2e() -> TestResult {
    let tmp = TempDir::new("vendor_ok")?;
    let vendor_dir = tmp.path().join("vendor");
    fs::create_dir_all(vendor_dir.join("math"))?;

    let helpers_src = r#"module Helpers
expose double

fn hidden_offset() : Int
  1
end

fn double(x: Int) : Int
  x * 2
end
"#;
    let extra_src = r#"module Math.Extra

fn triple(x: Int) : Int
  x * 3
end
"#;
    fs::write(vendor_dir.join("helpers.dana"), helpers_src)?;
    fs::write(vendor_dir.join("math/extra.dana"), extra_src)?;

    // 1. `dana vendor pin --dir ...` writes canonical deterministic `vendor/vendor.lock`.
    let rc_pin = run_cli(&[
        "vendor".to_string(),
        "pin".to_string(),
        "--dir".to_string(),
        vendor_dir.display().to_string(),
    ]);
    assert_eq!(rc_pin, 0, "dana vendor pin should succeed");

    let lock_text = fs::read_to_string(vendor_dir.join("vendor.lock"))?;
    assert!(lock_text.starts_with("# Dana vendored module SHA-256 lockfile\nversion 1\n"));
    let parsed_lock = parse_vendor_lock(&lock_text)?;
    assert_eq!(parsed_lock.version, 1);
    assert_eq!(parsed_lock.entries.len(), 2);
    assert_eq!(parsed_lock.entries[0].module, "Helpers");
    assert_eq!(parsed_lock.entries[0].path, "helpers.dana");
    assert_eq!(parsed_lock.entries[0].sha256.len(), 64);
    assert_eq!(parsed_lock.entries[1].module, "Math.Extra");
    assert_eq!(parsed_lock.entries[1].path, "math/extra.dana");

    // Re-pinning must produce byte-for-byte identical vendor.lock.
    let (lock2, _) = pin_vendor_dir(&vendor_dir)?;
    assert_eq!(lock2, parsed_lock);
    assert_eq!(
        fs::read_to_string(vendor_dir.join("vendor.lock"))?,
        lock_text
    );

    // 2. `dana vendor verify --dir ...` passes cleanly.
    let rc_verify = run_cli(&[
        "vendor".to_string(),
        "verify".to_string(),
        "--dir".to_string(),
        vendor_dir.display().to_string(),
    ]);
    assert_eq!(rc_verify, 0, "dana vendor verify should pass");
    assert_eq!(verify_vendor_dir(&vendor_dir).map(|v| v.len()), Ok(2));

    // 3. Root script importing both vendored modules (qualified AND unqualified calls) checks & runs!
    let app_path = tmp.path().join("app.dana");
    fs::write(
        &app_path,
        r#"module App
use Helpers
use Math.Extra

fn main(console: Console) : Int
  a = Helpers.double(21)
  b = Math.Extra.triple(7)
  c = double(5)
  console.print("a=#{a} b=#{b} c=#{c}")
  0
end
"#,
    )?;

    assert_eq!(
        run_cli(&["check".to_string(), app_path.display().to_string()]),
        0,
        "dana check on pinned vendor imports must succeed"
    );

    let out = Command::new(dana_bin())
        .args(["run", &app_path.display().to_string()])
        .output()?;
    assert!(
        out.status.success(),
        "dana run failed: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert_eq!(
        String::from_utf8_lossy(&out.stdout).trim(),
        "a=42 b=21 c=10"
    );

    // 4. Calling an unexposed function in a vendored module (`Helpers.hidden_offset`) is rejected.
    let hidden_app = tmp.path().join("hidden.dana");
    fs::write(
        &hidden_app,
        r##"module HiddenApp
use Helpers

fn main(console: Console) : Int
  console.print("#{Helpers.hidden_offset()}")
  0
end
"##,
    )?;
    assert_eq!(
        run_cli(&["check".to_string(), hidden_app.display().to_string()]),
        1,
        "unexposed vendored function must be rejected"
    );
    Ok(())
}

#[test]
fn vendor_tamper_unpinned_and_missing_lock_rejected() -> TestResult {
    let tmp = TempDir::new("vendor_tamper")?;
    let vendor_dir = tmp.path().join("vendor");
    fs::create_dir_all(&vendor_dir)?;
    let helper_path = vendor_dir.join("helpers.dana");
    let app_path = tmp.path().join("app.dana");

    let original = "module Helpers\n\nfn double(x: Int) : Int\n  x * 2\nend\n";
    fs::write(&helper_path, original)?;
    fs::write(
        &app_path,
        "module App\nuse Helpers\n\nfn main(console: Console) : Int\n  console.print(\"#{Helpers.double(3)}\")\n  0\nend\n",
    )?;

    // 1. Missing vendor.lock fails both `verify` and `resolve_path` / `dana check`.
    assert!(verify_vendor_dir(&vendor_dir).is_err());
    let mut sm = SourceMap::new();
    let res_no_lock = resolve_path(&app_path, None, &mut sm);
    let diags = res_no_lock
        .err()
        .ok_or("expected missing vendor.lock to fail resolve_path")?;
    assert!(diags.iter().any(|d| d.code() == DiagCode::ResolveError));
    assert!(
        diags
            .iter()
            .any(|d| d.hints().iter().any(|h| h.contains("dana vendor pin"))),
        "expected hint to run `dana vendor pin`, got: {diags:?}"
    );

    // 2. Pin cleanly, then tamper 1 byte (`x * 2` -> `x * 3`).
    let _ = pin_vendor_dir(&vendor_dir)?;
    assert!(verify_vendor_dir(&vendor_dir).is_ok());

    let tampered = original.replace("x * 2", "x * 3");
    assert_eq!(tampered.len(), original.len());
    fs::write(&helper_path, &tampered)?;

    // Both `dana vendor verify` and `dana check` MUST reject with SHA-256 mismatch!
    let verify_errs = verify_vendor_dir(&vendor_dir)
        .err()
        .ok_or("expected verify_vendor_dir to catch 1-byte tamper")?;
    assert!(
        verify_errs.iter().any(|e| e.contains("SHA-256")),
        "verify_errs={verify_errs:?}"
    );
    assert_eq!(
        run_cli(&[
            "vendor".to_string(),
            "verify".to_string(),
            "--dir".to_string(),
            vendor_dir.display().to_string(),
        ]),
        1
    );

    let mut sm2 = SourceMap::new();
    let check_diags = resolve_path(&app_path, None, &mut sm2)
        .err()
        .ok_or("expected tampered vendor module to fail resolve_path")?;
    assert!(
        check_diags
            .iter()
            .any(|d| d.code() == DiagCode::ResolveError && d.message().contains("SHA-256")),
        "check_diags={check_diags:?}"
    );
    assert_eq!(
        run_cli(&["check".to_string(), app_path.display().to_string()]),
        1
    );

    // 3. Restore helper, re-pin, then drop an unpinned `vendor/rogue.dana`.
    fs::write(&helper_path, original)?;
    let _ = pin_vendor_dir(&vendor_dir)?;
    fs::write(
        vendor_dir.join("rogue.dana"),
        "module Rogue\n\nfn evil() : Int\n  1\nend\n",
    )?;

    let unpinned_errs = verify_vendor_dir(&vendor_dir)
        .err()
        .ok_or("expected unpinned vendor/rogue.dana to fail verify_vendor_dir")?;
    assert!(
        unpinned_errs.iter().any(|e| e.contains("unpinned")),
        "unpinned_errs={unpinned_errs:?}"
    );
    assert_eq!(
        run_cli(&[
            "vendor".to_string(),
            "verify".to_string(),
            "--dir".to_string(),
            vendor_dir.display().to_string(),
        ]),
        1
    );

    let rogue_app = tmp.path().join("rogue_app.dana");
    fs::write(
        &rogue_app,
        "module RogueApp\nuse Rogue\n\nfn main(console: Console) : Int\n  console.print(\"#{Rogue.evil()}\")\n  0\nend\n",
    )?;
    assert_eq!(
        run_cli(&["check".to_string(), rogue_app.display().to_string()]),
        1
    );
    Ok(())
}

#[test]
fn vendor_pure_by_default_rejects_main_fakes_and_policy_breach() -> TestResult {
    let cases: &[(&str, &str, DiagCode)] = &[
        (
            "vendor_defines_main",
            "module BadVendor\n\nfn main(console: Console) : Int\n  0\nend\n",
            DiagCode::CapabilityError,
        ),
        (
            "vendor_calls_files_in_memory",
            "module BadVendor\n\nfn leak() : Int\n  f = Files.in_memory({\"a.txt\": \"x\"})\n  0\nend\n",
            DiagCode::CapabilityError,
        ),
        (
            "vendor_calls_db_in_memory",
            "module BadVendor\n\nfn leak() : Int\n  d = DB.in_memory(Seminary, {})\n  0\nend\n",
            DiagCode::CapabilityError,
        ),
        (
            "vendor_calls_https_fake",
            "module BadVendor\n\nfn leak() : Int\n  h = Https.fake(\"api.example.com\", responses: {})\n  0\nend\n",
            DiagCode::CapabilityError,
        ),
        (
            "vendor_calls_args_of",
            "module BadVendor\n\nfn leak() : Int\n  a = Args.of([\"x\"])\n  0\nend\n",
            DiagCode::CapabilityError,
        ),
        (
            "vendor_calls_console_fake",
            "module BadVendor\n\nfn leak() : Int\n  c = Console.fake()\n  0\nend\n",
            DiagCode::CapabilityError,
        ),
        (
            "vendor_calls_secret_fake",
            "module BadVendor\n\nfn leak() : Int\n  s = Secret.fake(\"k\")\n  0\nend\n",
            DiagCode::CapabilityError,
        ),
        (
            "vendor_exceeds_root_policy",
            "module BadVendor\n\nfn exfil(out: WriteFiles(\"reports/\", allows: [pii])) : Int\n  0\nend\n",
            DiagCode::PrivacyError,
        ),
    ];

    for (label, vendor_src, expected_code) in cases {
        let tmp = TempDir::new(label)?;
        let vendor_dir = tmp.path().join("vendor");
        fs::create_dir_all(&vendor_dir)?;
        fs::write(vendor_dir.join("bad-vendor.dana"), vendor_src)?;
        let _ = pin_vendor_dir(&vendor_dir)?;

        let policy_src = "version 1\nmin_group_size 5\nallow export \"reports/\" tags []\n";
        fs::write(tmp.path().join("dana.policy"), policy_src)?;
        let app_path = tmp.path().join("app.dana");
        fs::write(
            &app_path,
            "module App\nuse BadVendor\n\nfn main(console: Console) : Int\n  0\nend\n",
        )?;

        let mut sm = SourceMap::new();
        let pfid = sm.add_file("dana.policy".to_string(), policy_src.to_string());
        let policy = parse_policy(pfid, policy_src).map_err(|d| render_diagnostic(&d, &sm))?;
        let resolved = resolve_path(&app_path, Some(policy), &mut sm)
            .map_err(|ds| format!("{label}: unexpected resolve fail: {ds:?}"))?;
        let diags = check_resolved(&resolved, &sm)
            .err()
            .ok_or_else(|| format!("{label}: expected check_resolved to fail"))?;
        assert!(
            diags.iter().any(|d| d.code() == *expected_code),
            "{label}: expected {expected_code:?}, got: {:?}",
            diags
                .iter()
                .map(|d| (d.code(), d.message()))
                .collect::<Vec<_>>()
        );
    }
    Ok(())
}

// ===========================================================================
// 2. Safe Interactive REPL & `untyped` Explorer Tests
// ===========================================================================

#[test]
fn repl_eval_one_liners_arithmetic_pipeline_stats_and_pivot_longer() -> TestResult {
    // 1. Arithmetic via real `dana repl --eval` subprocess
    let out1 = Command::new(dana_bin())
        .args(["repl", "--eval", "2 + 3 * 4"])
        .output()?;
    assert!(
        out1.status.success(),
        "stderr={}",
        String::from_utf8_lossy(&out1.stderr)
    );
    assert_eq!(String::from_utf8_lossy(&out1.stdout).trim(), "14");

    // 2. Table pipeline + Stats.corr + pivot_longer via `--eval`
    let script = r#"t = table
  | item | q1   | q2   |
  | "A"  | 10.0 | 20.0 |
  | "B"  | 20.0 | 40.0 |
  | "C"  | 30.0 | 60.0 |
end
r = Stats.corr(t, x: .q1, y: .q2)
long = t |> pivot_longer(cols: [.q1, .q2], names_to: "quarter", values_to: "sales")
(r.round(3), long.count())"#;
    let out2 = Command::new(dana_bin())
        .args(["repl", "--eval", script])
        .output()?;
    assert!(
        out2.status.success(),
        "stderr={}",
        String::from_utf8_lossy(&out2.stderr)
    );
    let stdout2 = String::from_utf8_lossy(&out2.stdout);
    assert!(
        stdout2.contains("(1, 6)") || stdout2.contains("(1.0, 6)"),
        "expected corr=1 and 6 pivoted rows in stdout:\n{stdout2}"
    );
    Ok(())
}

#[test]
fn repl_multi_turn_piped_session_and_meta_commands() -> TestResult {
    let tmp = TempDir::new("repl_session")?;
    let mut session = ReplSession::new(ReplConfig {
        work_dir: tmp.path().to_path_buf(),
        ..ReplConfig::default()
    })
    .map_err(|d| format!("ReplSession::new failed: {}", d.message()))?;

    let piped = r#"
schema Metric
  dept: Text
  score: Float
end
fn bump(x: Int) : Int
  x + 10
end
x = bump(32)
x
m = table
  | dept  | score |
  | "eng" | 90.0  |
  | "eng" | 95.0  |
  | "ops" | 80.0  |
end
:type x
:type m
:profile m
m |> group_by(.dept) |> summarize(avg_s: mean(.score)) |> chart_bar(x: .dept, y: .avg_s, title: "Dept Scores")
:explain m |> where(.score >= 85.0) |> group_by(.dept) |> summarize(n: count())
:vars
:help
:reset
:vars
:quit
"#;

    let mut out_buf = Vec::new();
    let mut err_buf = Vec::new();
    let rc = run_repl_reader(
        &mut session,
        Cursor::new(piped.as_bytes()),
        &mut out_buf,
        &mut err_buf,
        false,
        false,
    );
    let stdout = String::from_utf8(out_buf)?;
    let stderr = String::from_utf8(err_buf)?;
    assert_eq!(rc, 0, "stderr:\n{stderr}");
    assert!(stderr.is_empty(), "unexpected stderr:\n{stderr}");
    assert!(
        stdout.contains("defined schema Metric"),
        "stdout:\n{stdout}"
    );
    assert!(stdout.contains("defined fn bump"), "stdout:\n{stdout}");
    assert!(stdout.contains("42"), "stdout:\n{stdout}");
    assert!(stdout.contains("Int"), "stdout:\n{stdout}");
    assert!(
        stdout.contains("Dataset Profile (3 rows, 2 cols)"),
        "stdout:\n{stdout}"
    );
    assert!(
        stdout.contains("=== Dept Scores [Bar] ==="),
        "expected terminal chart in REPL output:\n{stdout}"
    );
    assert!(stdout.contains("[OPTIMIZED PLAN]"), "stdout:\n{stdout}");
    assert!(
        stdout.contains("[SENSITIVITY PROVENANCE]"),
        "stdout:\n{stdout}"
    );
    assert!(stdout.contains("files : ReadFiles"), "stdout:\n{stdout}");
    assert!(stdout.contains("session reset"), "stdout:\n{stdout}");

    // After `:reset`, `x` is no longer bound.
    match session.eval_input("x") {
        ReplOutput::Error(e) => assert!(e.contains("unknown identifier"), "e={e}"),
        other => {
            return Err(format!("expected unknown identifier after :reset, got {other:?}").into());
        }
    }

    // Verify piped stdin via actual `dana repl` binary process too!
    let mut child = Command::new(dana_bin())
        .arg("repl")
        .current_dir(tmp.path())
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()?;
    if let Some(mut stdin) = child.stdin.take() {
        stdin.write_all(b"a = 7\na * 6\n:quit\n")?;
    }
    let proc_out = child.wait_with_output()?;
    assert!(proc_out.status.success());
    let proc_stdout = String::from_utf8_lossy(&proc_out.stdout);
    assert!(proc_stdout.contains("42"), "proc_stdout={proc_stdout}");
    Ok(())
}

#[test]
fn repl_privacy_redaction_and_forbid_repl_show_sensitive_policy() -> TestResult {
    let tmp = TempDir::new("repl_privacy")?;

    // 1. Default safe mode (`allowed_show_tags = empty`): BOTH scalar [pii], table [pii] columns,
    //    AND `row_tags = [pii]` (implicit flow from filtering on a [pii] column) MUST redact!
    let mut safe_repl = ReplSession::new(ReplConfig {
        work_dir: tmp.path().to_path_buf(),
        ..ReplConfig::default()
    })
    .map_err(|d| format!("safe ReplSession failed: {}", d.message()))?;

    let setup = r#"
schema SecretRecord
  ssn: Text [pii]
  gpa: Decimal [ferpa]
  dept: Text
end
fn make_secret_scalar() : Text [pii]
  "999-88-7777"
end
fn make_records() : Table(SecretRecord)
  table
    | ssn           | gpa  | dept      |
    | "999-88-7777" | 3.95 | "History" |
    | "111-22-3333" | 3.50 | "Physics" |
  end
end
"#;
    let mut out_buf = Vec::new();
    let mut err_buf = Vec::new();
    let script = format!(
        "{setup}\nsec = make_secret_scalar()\nrecs = make_records()\nfiltered = recs |> where(.ssn == \"999-88-7777\")\n:profile recs\n:quit\n"
    );
    let rc = run_repl_reader(
        &mut safe_repl,
        Cursor::new(script.as_bytes()),
        &mut out_buf,
        &mut err_buf,
        false,
        false,
    );
    let stdout = String::from_utf8(out_buf)?;
    let stderr = String::from_utf8(err_buf)?;
    assert_eq!(rc, 0, "stderr:\n{stderr}");
    assert!(stderr.is_empty(), "unexpected stderr:\n{stderr}");
    assert!(
        stdout.contains("[REDACTED:pii]"),
        "expected [REDACTED:pii] in stdout:\n{stdout}"
    );
    assert!(
        stdout.contains("[REDACTED:ferpa]"),
        "expected [REDACTED:ferpa] in stdout:\n{stdout}"
    );
    // Raw secrets MUST NEVER appear anywhere in stdout or stderr!
    for secret in ["999-88-7777", "111-22-3333", "3.95", "3.50"] {
        assert!(
            !stdout.contains(secret),
            "raw secret `{secret}` leaked into REPL stdout!\n{stdout}"
        );
        assert!(
            !stderr.contains(secret),
            "raw secret `{secret}` leaked into REPL stderr!\n{stderr}"
        );
    }
    // Public column `History` appears in unfiltered `recs`, while `filtered` (which carries
    // `row_tags: [pii]`) redacts ALL cells including `dept`!
    assert!(
        stdout.contains("History"),
        "public dept should display in unfiltered table"
    );
    match safe_repl.eval_input("filtered") {
        ReplOutput::Value { rendered, .. } => {
            assert!(
                !rendered.contains("History"),
                "row_tags=[pii] MUST redact all cells including public columns:\n{rendered}"
            );
            assert!(
                rendered.contains("dept") && rendered.contains("(1 rows, 3 cols)"),
                "headers and row count must remain visible:\n{rendered}"
            );
            assert!(
                rendered.contains("[REDACTED:pii]") && rendered.contains("[REDACTED:ferpa,pii]"),
                "expected sorted redaction tags:\n{rendered}"
            );
        }
        other => return Err(format!("expected filtered table output, got {other:?}").into()),
    }
    // `order_tags` from `sort_by(.ssn)` must also redact even when projecting only `.dept`!
    match safe_repl.eval_input("recs |> sort_by(.ssn) |> select(.dept)") {
        ReplOutput::Value { rendered, .. } => {
            assert!(
                rendered.contains("[REDACTED:pii]") && !rendered.contains("History"),
                "order_tags=[pii] MUST redact cell values:\n{rendered}"
            );
        }
        other => return Err(format!("expected sorted table output, got {other:?}").into()),
    }

    // 2. With `--show-sensitive=pii` when policy allows (no `forbid repl_show_sensitive`):
    //    [pii] values display locally, while [ferpa] remains `[REDACTED:ferpa]`!
    let mut pii_repl = ReplSession::new(ReplConfig {
        work_dir: tmp.path().to_path_buf(),
        allowed_show_tags: TagSet::singleton("pii"),
        ..ReplConfig::default()
    })
    .map_err(|d| format!("pii ReplSession failed: {}", d.message()))?;
    let mut pii_out = Vec::new();
    let mut pii_err = Vec::new();
    let _ = run_repl_reader(
        &mut pii_repl,
        Cursor::new(format!("{setup}\nmake_secret_scalar()\nmake_records()\n").as_bytes()),
        &mut pii_out,
        &mut pii_err,
        false,
        false,
    );
    let pii_stdout = String::from_utf8(pii_out)?;
    assert!(
        pii_stdout.contains("999-88-7777"),
        "expected [pii] shown when --show-sensitive=pii is permitted:\n{pii_stdout}"
    );
    assert!(
        pii_stdout.contains("[REDACTED:ferpa]") && !pii_stdout.contains("3.95"),
        "unrequested [ferpa] MUST remain redacted:\n{pii_stdout}"
    );

    // 3. With `--policy examples/dana.policy` (`forbid repl_show_sensitive`) + `--show-sensitive=pii`:
    //    MUST HARD-FAIL immediately with `PrivacyError` (`E0202`, exit code 1)!
    let policy_path = repo_root().join("examples/dana.policy");
    let psrc = fs::read_to_string(&policy_path)?;
    let mut sm = SourceMap::new();
    let pfid = sm.add_file(policy_path.display().to_string(), psrc.clone());
    let policy = parse_policy(pfid, &psrc).map_err(|d| render_diagnostic(&d, &sm))?;

    let err_diag = ReplSession::new(ReplConfig {
        policy: Some(policy),
        allowed_show_tags: TagSet::singleton("pii"),
        work_dir: tmp.path().to_path_buf(),
        ..ReplConfig::default()
    })
    .err()
    .ok_or("expected ReplSession::new to hard-fail under forbid repl_show_sensitive")?;
    assert_eq!(err_diag.code(), DiagCode::PrivacyError);

    let cli_denied = Command::new(dana_bin())
        .args([
            "repl",
            "--policy",
            &policy_path.display().to_string(),
            "--show-sensitive=pii",
            "--eval",
            "1 + 1",
        ])
        .output()?;
    assert_eq!(cli_denied.status.code(), Some(1));
    let cli_stderr = String::from_utf8_lossy(&cli_denied.stderr);
    assert!(
        cli_stderr.contains("E0202") && cli_stderr.contains("forbids `--show-sensitive`"),
        "expected E0202 PrivacyError on stderr, got:\n{cli_stderr}"
    );
    assert!(
        String::from_utf8_lossy(&cli_denied.stdout)
            .trim()
            .is_empty(),
        "must fail BEFORE evaluating `1 + 1`"
    );

    // Without `--show-sensitive`, the exact same `--policy examples/dana.policy` runs cleanly!
    let cli_ok = Command::new(dana_bin())
        .args([
            "repl",
            "--policy",
            &policy_path.display().to_string(),
            "--eval",
            "2 + 2",
        ])
        .output()?;
    assert!(cli_ok.status.success());
    assert_eq!(String::from_utf8_lossy(&cli_ok.stdout).trim(), "4");
    Ok(())
}

#[test]
fn repl_read_only_enforcement_and_sqlite_db_pushdown() -> TestResult {
    let tmp = TempDir::new("repl_db")?;
    let db_path = tmp.path().join("seminary.sqlite");
    let db_uri = format!("sqlite://{}", db_path.display());

    {
        let mut conn = open_connection(&db_uri)?;
        conn.execute(
            r#"CREATE TABLE "Student" (
                "student_id" INTEGER NOT NULL,
                "email" TEXT NOT NULL,
                "program" TEXT NOT NULL,
                "active?" INTEGER NOT NULL
            )"#,
            &[],
        )?;
        for (id, email, prog, active) in [
            (1, "alice@secret.edu", "MDiv", true),
            (2, "bob@secret.edu", "MDiv", true),
            (3, "carol@secret.edu", "MAR", false),
        ] {
            conn.execute(
                r#"INSERT INTO "Student" ("student_id", "email", "program", "active?") VALUES (?1, ?2, ?3, ?4)"#,
                &[
                    SqlParam::Int(id),
                    SqlParam::Text(email.to_string()),
                    SqlParam::Text(prog.to_string()),
                    SqlParam::Bool(active),
                ],
            )?;
        }
    }

    let mut session = ReplSession::new(ReplConfig {
        db_bindings: vec![("Seminary".to_string(), db_uri)],
        work_dir: tmp.path().to_path_buf(),
        ..ReplConfig::default()
    })
    .map_err(|d| format!("ReplSession::new failed: {}", d.message()))?;

    // 1. No `out` / `WriteFiles` / `WriteTable` capability exists in REPL scope!
    let _ = session.eval_input("dummy = table\n  | a |\n  | 1 |\nend");
    match session.eval_input("out.write_csv(\"hack.csv\", dummy)") {
        ReplOutput::Error(e) => assert!(e.contains("unknown identifier"), "e={e}"),
        other => return Err(format!("expected WriteFiles unavailable, got {other:?}").into()),
    }

    // 2. Declare `Student` schema with [pii] and query via `Seminary.table(Student)`.
    let schema_res = session.eval_input(
        r#"schema Student
  student_id: Int [pii]
  email: Text [pii]
  program: Text
  active?: Bool
end"#,
    );
    assert!(matches!(schema_res, ReplOutput::Info(_)), "{schema_res:?}");

    match session.eval_input("active = Seminary.table(Student) |> where(.active?)") {
        ReplOutput::Value { rendered, .. } => {
            assert!(rendered.contains("[REDACTED:pii]"), "rendered:\n{rendered}");
            assert!(rendered.contains("MDiv"), "rendered:\n{rendered}");
            assert!(
                rendered.contains("(2 rows, 4 cols)"),
                "rendered:\n{rendered}"
            );
            assert!(!rendered.contains("alice@secret.edu"));
            assert!(!rendered.contains("bob@secret.edu"));
        }
        other => return Err(format!("expected active table, got {other:?}").into()),
    }

    // Lowercase alias `seminary` works too!
    match session.eval_input("seminary.table(Student).count()") {
        ReplOutput::Value { rendered, .. } => assert_eq!(rendered, "3"),
        other => return Err(format!("expected count 3, got {other:?}").into()),
    }

    // `:explain` shows SQLite pushdown + sensitivity provenance!
    match session.eval_input(":explain active |> select(.program)") {
        ReplOutput::Info(text) => {
            assert!(
                text.contains("[SQL PUSHDOWN -> sqlite]"),
                "explain:\n{text}"
            );
            assert!(
                text.contains("[SENSITIVITY PROVENANCE]"),
                "explain:\n{text}"
            );
        }
        other => return Err(format!("expected explain output, got {other:?}").into()),
    }
    Ok(())
}

#[test]
fn repl_untyped_csv_jsonl_parquet_xlsx_and_infer_schema() -> TestResult {
    let tmp = TempDir::new("repl_untyped")?;

    // 1. CSV fixture
    fs::write(
        tmp.path().join("sales.csv"),
        "date,category,qty,amount\n2026-10-01,books,2,25.50\n2026-10-02,coffee,5,17.25\n2026-10-03,books,1,12.00\n",
    )?;

    // 2. Compressed `.jsonl.gz` fixture
    let jsonl_raw = concat!(
        "{\"event\":\"click\",\"user_email\":\"a@example.com\",\"latency_ms\":12.5}\n",
        "{\"event\":\"purchase\",\"user_email\":\"b@example.com\",\"latency_ms\":48.0}\n",
        "{\"event\":\"click\",\"user_email\":null,\"latency_ms\":15.0}\n"
    );
    fs::write(
        tmp.path().join("events.jsonl.gz"),
        gzip_bytes(jsonl_raw.as_bytes())?,
    )?;

    // 3. Real Parquet fixture
    let pq_tv = TableVal {
        cols: vec![
            col("sku", ScalarTy::Text, &[]),
            col("qty", ScalarTy::Int, &[]),
            col("price", ScalarTy::Decimal, &[]),
        ],
        rows: vec![
            TableRow {
                cells: vec![
                    Val::Text("SKU-1".to_string()),
                    Val::Int(BigInt::from(4i64)),
                    Val::Decimal(parse_decimal_bigint_strict("19.95")?),
                ],
                group_meta: None,
            },
            TableRow {
                cells: vec![
                    Val::Text("SKU-2".to_string()),
                    Val::Int(BigInt::from(1i64)),
                    Val::Decimal(parse_decimal_bigint_strict("50.00")?),
                ],
                group_meta: None,
            },
        ],
    };
    write_parquet_table(
        &tmp.path().join("orders.parquet"),
        &pq_tv,
        ParquetCompression::Zstd,
    )?;

    // 4. Real multi-sheet XLSX fixture
    let xlsx_tv = TableVal {
        cols: vec![
            col("receipt_no", ScalarTy::Text, &[]),
            col("fund_code", ScalarTy::Text, &[]),
            col("amount", ScalarTy::Decimal, &[]),
        ],
        rows: vec![
            TableRow {
                cells: vec![
                    Val::Text("R-10".to_string()),
                    Val::Text("GEN".to_string()),
                    Val::Decimal(parse_decimal_bigint_strict("125.00")?),
                ],
                group_meta: None,
            },
            TableRow {
                cells: vec![
                    Val::Text("R-11".to_string()),
                    Val::Text("SCHOL".to_string()),
                    Val::Decimal(parse_decimal_bigint_strict("300.50")?),
                ],
                group_meta: None,
            },
        ],
    };
    let cover_tv = TableVal {
        cols: vec![col("note", ScalarTy::Text, &[])],
        rows: vec![TableRow {
            cells: vec![Val::Text("cover".to_string())],
            group_meta: None,
        }],
    };
    write_xlsx_file(
        &tmp.path().join("workbook.xlsx"),
        &[
            ("Cover".to_string(), cover_tv),
            ("Gifts".to_string(), xlsx_tv),
        ],
    )?;

    let mut session = ReplSession::new(ReplConfig {
        work_dir: tmp.path().to_path_buf(),
        ..ReplConfig::default()
    })
    .map_err(|d| format!("ReplSession::new failed: {}", d.message()))?;

    // CSV: load, preview, pipeline, profile, infer-schema
    match session.eval_input(r#"sales = untyped.read_csv("sales.csv")"#) {
        ReplOutput::Value { rendered, .. } => {
            assert!(
                rendered.contains("books") && rendered.contains("(3 rows, 4 cols)"),
                "{rendered}"
            );
        }
        other => return Err(format!("untyped.read_csv failed: {other:?}").into()),
    }
    match session
        .eval_input(r#"sales |> where(.category == "books") |> summarize(total: sum(.amount))"#)
    {
        ReplOutput::Value { rendered, .. } => {
            assert!(
                rendered.contains("37.5"),
                "expected 37.5 total:\n{rendered}"
            );
        }
        other => return Err(format!("pipeline on untyped CSV failed: {other:?}").into()),
    }
    match session.eval_input(":profile sales") {
        ReplOutput::Info(p) => {
            assert!(
                p.contains("Dataset Profile (3 rows, 4 cols)"),
                "profile:\n{p}"
            );
        }
        other => return Err(format!(":profile sales failed: {other:?}").into()),
    }
    match session.eval_input(":infer-schema sales") {
        ReplOutput::Info(s) => {
            assert!(s.contains("schema Sales"), "{s}");
            assert!(s.contains("date: Date"), "{s}");
            assert!(s.contains("qty: Int"), "{s}");
            assert!(s.contains("amount: Decimal"), "{s}");
        }
        other => return Err(format!(":infer-schema sales failed: {other:?}").into()),
    }

    // JSONL (.gz): load, count, infer-schema (with nullable + PII hint!)
    match session.eval_input(r#"ev = untyped.read_jsonl("events.jsonl.gz")"#) {
        ReplOutput::Value { rendered, .. } => {
            assert!(rendered.contains("(3 rows, 3 cols)"), "{rendered}");
        }
        other => return Err(format!("untyped.read_jsonl failed: {other:?}").into()),
    }
    match session.eval_input(":infer-schema ev") {
        ReplOutput::Info(s) => {
            assert!(s.contains("schema Ev"), "{s}");
            assert!(s.contains("user_email: Text? [pii]"), "{s}");
            assert!(
                s.contains("latency_ms: Decimal") || s.contains("latency_ms: Float"),
                "{s}"
            );
        }
        other => return Err(format!(":infer-schema ev failed: {other:?}").into()),
    }

    // Parquet: load, filter, infer-schema
    match session.eval_input(r#"orders = untyped.read_parquet("orders.parquet")"#) {
        ReplOutput::Value { rendered, .. } => {
            assert!(
                rendered.contains("SKU-1") && rendered.contains("(2 rows, 3 cols)"),
                "{rendered}"
            );
        }
        other => return Err(format!("untyped.read_parquet failed: {other:?}").into()),
    }
    match session.eval_input("orders |> where(.qty >= 2) |> select(.sku)") {
        ReplOutput::Value { rendered, .. } => {
            assert!(
                rendered.contains("SKU-1") && !rendered.contains("SKU-2"),
                "{rendered}"
            );
        }
        other => return Err(format!("pipeline on untyped parquet failed: {other:?}").into()),
    }
    match session.eval_input(":infer-schema orders") {
        ReplOutput::Info(s) => {
            assert!(s.contains("schema Orders"), "{s}");
            assert!(
                s.contains("sku: Text") && s.contains("qty: Int") && s.contains("price: Decimal"),
                "{s}"
            );
        }
        other => return Err(format!(":infer-schema orders failed: {other:?}").into()),
    }

    // XLSX (named sheet): load, count, infer-schema
    match session.eval_input(r#"gifts = untyped.read_xlsx("workbook.xlsx", sheet: "Gifts")"#) {
        ReplOutput::Value { rendered, .. } => {
            assert!(
                rendered.contains("R-10")
                    && rendered.contains("SCHOL")
                    && rendered.contains("(2 rows, 3 cols)"),
                "{rendered}"
            );
        }
        other => return Err(format!("untyped.read_xlsx failed: {other:?}").into()),
    }
    match session.eval_input("gifts.count()") {
        ReplOutput::Value { rendered, .. } => assert_eq!(rendered, "2"),
        other => return Err(format!("gifts.count() failed: {other:?}").into()),
    }
    match session.eval_input(":infer-schema gifts") {
        ReplOutput::Info(s) => {
            assert!(s.contains("schema Gifts"), "{s}");
            assert!(
                s.contains("receipt_no: Text") && s.contains("amount: Decimal"),
                "{s}"
            );
        }
        other => return Err(format!(":infer-schema gifts failed: {other:?}").into()),
    }

    // `:infer-schema` directly on disk file paths (CSV, Parquet, XLSX)
    for (cmd, expected_hdr) in [
        (":infer-schema \"sales.csv\"", "schema Sales"),
        (":infer-schema \"orders.parquet\"", "schema Orders"),
        (":infer-schema \"workbook.xlsx\"", "schema Workbook"),
    ] {
        match session.eval_input(cmd) {
            ReplOutput::Info(s) => assert!(s.contains(expected_hdr), "{cmd} -> {s}"),
            other => return Err(format!("{cmd} failed: {other:?}").into()),
        }
    }
    Ok(())
}

// ===========================================================================
// 3. All 10 Real-World Examples Live End-to-End Matrix (VM & Oracle)
// ===========================================================================

#[test]
fn e2e_01_expenses_live() -> TestResult {
    let tmp = TempDir::new("e2e_01_expenses")?;
    let csv_path = tmp.path().join("october.csv");
    fs::write(
        &csv_path,
        "date,category,amount\n2026-10-01,food,12.50\n2026-10-02,food,bad_num\n2026-10-03,rent,900.00\n",
    )?;
    let prog = compile_example("examples/expenses.dana", true)?;
    let cfg = RunConfig {
        args: vec![csv_path.display().to_string()],
        work_dir: Some(tmp.path().to_path_buf()),
        live_io: true,
        ..RunConfig::default()
    };
    for (engine, res) in [
        ("oracle", run_exec_program(&prog, &cfg)),
        ("vm", run_exec_program_vm(&prog, &cfg, &VmConfig::default())),
    ] {
        match res {
            RunResult::Ok {
                exit_code,
                stdout,
                stderr,
            } => {
                assert_eq!(exit_code, 1, "{engine} expected exit 1 with 1 bad row");
                assert_eq!(stderr.len(), 1, "{engine} stderr={stderr:?}");
                assert!(stderr[0].contains("line 3"), "{engine} stderr={stderr:?}");
                let out_s = stdout.join("\n");
                assert!(
                    out_s.contains("rent") && out_s.contains("900.0"),
                    "{engine} {out_s}"
                );
                assert!(
                    out_s.contains("food") && out_s.contains("12.5"),
                    "{engine} {out_s}"
                );
            }
            other => return Err(format!("{engine} failed: {other:?}").into()),
        }
    }
    Ok(())
}

#[test]
fn e2e_02_enrollment_report_live() -> TestResult {
    let tmp = TempDir::new("e2e_02_enrollment")?;
    let db_path = tmp.path().join("seminary.sqlite");
    let db_uri = format!("sqlite://{}", db_path.display());

    {
        let mut conn = open_connection(&db_uri)?;
        conn.execute(
            r#"CREATE TABLE "Student" (
                "student_id" INTEGER NOT NULL,
                "email" TEXT NOT NULL,
                "program" TEXT NOT NULL,
                "cohort_year" INTEGER NOT NULL,
                "active?" INTEGER NOT NULL
            )"#,
            &[],
        )?;
        conn.execute(
            r#"CREATE TABLE "CourseEnrollment" (
                "student_id" INTEGER NOT NULL,
                "term" TEXT NOT NULL,
                "term_start" TEXT NOT NULL,
                "credits" TEXT NOT NULL,
                "grade_points" TEXT
            )"#,
            &[],
        )?;
        // 6 active MDiv students (>= 5 survives!) + 2 ThM students (< 5 suppressed!)
        for id in 1..=6i64 {
            conn.execute(
                r#"INSERT INTO "Student" ("student_id", "email", "program", "cohort_year", "active?") VALUES (?1, ?2, ?3, ?4, ?5)"#,
                &[
                    SqlParam::Int(id),
                    SqlParam::Text(format!("mdiv_secret_{id}@sem.edu")),
                    SqlParam::Text("MDiv".to_string()),
                    SqlParam::Int(2025),
                    SqlParam::Bool(true),
                ],
            )?;
            for (term, tstart, gpa) in [
                ("2026-Spring", "2026-01-15", "3.50"),
                ("2026-Fall", "2026-09-01", "3.80"),
            ] {
                conn.execute(
                    r#"INSERT INTO "CourseEnrollment" ("student_id", "term", "term_start", "credits", "grade_points") VALUES (?1, ?2, ?3, ?4, ?5)"#,
                    &[
                        SqlParam::Int(id),
                        SqlParam::Text(term.to_string()),
                        SqlParam::Text(tstart.to_string()),
                        SqlParam::Decimal(parse_decimal_bigint_strict("3.0")?),
                        SqlParam::Decimal(parse_decimal_bigint_strict(gpa)?),
                    ],
                )?;
            }
        }
        // 2 ThM students taking 6 courses each -> only 2 distinct students -> MUST be suppressed!
        for id in 101..=102i64 {
            conn.execute(
                r#"INSERT INTO "Student" ("student_id", "email", "program", "cohort_year", "active?") VALUES (?1, ?2, ?3, ?4, ?5)"#,
                &[
                    SqlParam::Int(id),
                    SqlParam::Text(format!("thm_secret_{id}@sem.edu")),
                    SqlParam::Text("ThM".to_string()),
                    SqlParam::Int(2025),
                    SqlParam::Bool(true),
                ],
            )?;
            for _ in 0..6 {
                conn.execute(
                    r#"INSERT INTO "CourseEnrollment" ("student_id", "term", "term_start", "credits", "grade_points") VALUES (?1, ?2, ?3, ?4, ?5)"#,
                    &[
                        SqlParam::Int(id),
                        SqlParam::Text("2026-Fall".to_string()),
                        SqlParam::Text("2026-09-01".to_string()),
                        SqlParam::Decimal(parse_decimal_bigint_strict("3.0")?),
                        SqlParam::Decimal(parse_decimal_bigint_strict("3.95")?),
                    ],
                )?;
            }
        }
    }

    let prog = compile_example("examples/enrollment-report.dana", true)?;
    let mut db_bindings = HashMap::new();
    db_bindings.insert("Seminary".to_string(), db_uri);
    let cfg = RunConfig {
        work_dir: Some(tmp.path().to_path_buf()),
        db_bindings,
        live_io: true,
        ..RunConfig::default()
    };

    for (engine, res) in [
        ("oracle", run_exec_program(&prog, &cfg)),
        ("vm", run_exec_program_vm(&prog, &cfg, &VmConfig::default())),
    ] {
        match res {
            RunResult::Ok {
                exit_code, stdout, ..
            } => {
                assert_eq!(exit_code, 0, "{engine}");
                assert!(
                    stdout.join("\n").contains("2 published cells"),
                    "{engine} stdout={stdout:?}"
                );
            }
            other => return Err(format!("{engine} failed: {other:?}").into()),
        }
    }

    let html = fs::read_to_string(tmp.path().join("reports/enrollment-summary.html"))?;
    assert!(html.contains("Seminary Enrollment &amp; Academic Summary"));
    assert_eq!(
        html.matches("<svg xmlns=\"http://www.w3.org/2000/svg\"")
            .count(),
        2,
        "expected trend_chart + gpa_chart inline SVGs"
    );
    assert!(html.contains("MDiv"));
    assert!(
        !html.contains("ThM"),
        "suppressed < 5 distinct-student ThM leaked!"
    );
    assert!(!html.contains("mdiv_secret_"), "student email PII leaked!");
    assert!(!html.contains("NaN"));
    Ok(())
}

#[test]
fn e2e_03_research_export_live() -> TestResult {
    let tmp = TempDir::new("e2e_03_research")?;
    let db_path = tmp.path().join("seminary.sqlite");
    let db_uri = format!("sqlite://{}", db_path.display());

    {
        let mut conn = open_connection(&db_uri)?;
        conn.execute(
            r#"CREATE TABLE "Student" (
                "student_id" INTEGER NOT NULL,
                "full_name" TEXT NOT NULL,
                "email" TEXT NOT NULL,
                "program" TEXT NOT NULL,
                "cohort_year" INTEGER NOT NULL
            )"#,
            &[],
        )?;
        conn.execute(
            r#"CREATE TABLE "CounselingVisit" (
                "student_id" INTEGER NOT NULL,
                "visit_date" TEXT NOT NULL,
                "duration_min" INTEGER NOT NULL,
                "modality" TEXT NOT NULL
            )"#,
            &[],
        )?;
        for (id, name, email, prog, yr) in [
            (42, "Jane Secret Doe", "jane@secret.edu", "MDiv", 2025),
            (99, "John Hidden Roe", "john@secret.edu", "MAR", 2026),
        ] {
            conn.execute(
                r#"INSERT INTO "Student" ("student_id", "full_name", "email", "program", "cohort_year") VALUES (?1, ?2, ?3, ?4, ?5)"#,
                &[
                    SqlParam::Int(id),
                    SqlParam::Text(name.to_string()),
                    SqlParam::Text(email.to_string()),
                    SqlParam::Text(prog.to_string()),
                    SqlParam::Int(yr),
                ],
            )?;
        }
        for (id, dt, dur, modality) in [
            (42, "2026-02-14", 50, "in-person"),
            (42, "2026-03-01", 45, "telehealth"),
            (99, "2026-02-20", 60, "in-person"),
        ] {
            conn.execute(
                r#"INSERT INTO "CounselingVisit" ("student_id", "visit_date", "duration_min", "modality") VALUES (?1, ?2, ?3, ?4)"#,
                &[
                    SqlParam::Int(id),
                    SqlParam::Text(dt.to_string()),
                    SqlParam::Int(dur),
                    SqlParam::Text(modality.to_string()),
                ],
            )?;
        }
    }

    let prog = compile_example("examples/research-export.dana", true)?;
    let mut db_bindings = HashMap::new();
    db_bindings.insert("Seminary".to_string(), db_uri);

    // Without `--allow-export counseling`, MUST stop with ExportGateDenied!
    let denied_cfg = RunConfig {
        work_dir: Some(tmp.path().to_path_buf()),
        db_bindings: db_bindings.clone(),
        allow_export: TagSet::empty(),
        live_io: true,
        ..RunConfig::default()
    };
    match run_exec_program_vm(&prog, &denied_cfg, &VmConfig::default()) {
        RunResult::Stopped { bug, .. } => assert_eq!(bug.kind, BugKind::ExportGateDenied),
        other => return Err(format!("expected ExportGateDenied, got {other:?}").into()),
    }

    // With `--allow-export counseling`, both Oracle and VM produce pseudonymized Parquet + XLSX!
    let ok_cfg = RunConfig {
        work_dir: Some(tmp.path().to_path_buf()),
        db_bindings,
        allow_export: TagSet::singleton("counseling"),
        live_io: true,
        ..RunConfig::default()
    };
    for (engine, res) in [
        ("oracle", run_exec_program(&prog, &ok_cfg)),
        (
            "vm",
            run_exec_program_vm(&prog, &ok_cfg, &VmConfig::default()),
        ),
    ] {
        match res {
            RunResult::Ok {
                exit_code, stdout, ..
            } => {
                assert_eq!(exit_code, 0, "{engine}");
                assert!(
                    stdout
                        .join("\n")
                        .contains("Exported pseudonymized counseling records"),
                    "{engine} stdout={stdout:?}"
                );
            }
            other => return Err(format!("{engine} failed: {other:?}").into()),
        }
    }

    // Verify exported Parquet and XLSX carry HMAC-SHA256 `ps_...` tokens and ZERO PII!
    let out_schema = table_ty(vec![
        col("student_token", ScalarTy::Text, &[]),
        col("duration_min", ScalarTy::Int, &[]),
        col("modality", ScalarTy::Text, &[]),
        col("visit_month", ScalarTy::Date, &[]),
        col("program", ScalarTy::Text, &[]),
        col("cohort_year", ScalarTy::Int, &[]),
    ]);
    let pq_out = read_parquet_file_with_schema(
        &tmp.path().join("ir-exports/counseling-utilization.parquet"),
        &out_schema,
        |_, _| true,
    )?;
    assert_eq!(pq_out.rows.len(), 3);
    for row in &pq_out.rows {
        let Val::Text(tok) = &row.cells[0] else {
            return Err(format!("expected Text token, got {:?}", row.cells[0]).into());
        };
        assert!(
            tok.starts_with("ps_") && tok.len() == 35,
            "bad token: {tok}"
        );
        assert_ne!(tok, "42");
        assert_ne!(tok, "99");
    }

    let (xlsx_out, xlsx_bad) = read_xlsx_file_with_schema(
        &tmp.path().join("ir-exports/counseling-utilization.xlsx"),
        Some("Utilization"),
        &out_schema,
        |_, _| true,
    )?;
    assert_eq!(xlsx_out.rows.len(), 3);
    assert!(xlsx_bad.rows.is_empty());
    Ok(())
}

#[test]
fn e2e_04_donor_reconciliation_live() -> TestResult {
    let tmp = TempDir::new("e2e_04_donor")?;
    let xlsx_in = tmp.path().join("finance-gifts.xlsx");
    let db_path = tmp.path().join("seminary.sqlite");
    let db_uri = format!("sqlite://{}", db_path.display());

    // Build real Excel workbook with `"Gifts"` sheet
    let gifts_tv = TableVal {
        cols: vec![
            col("receipt_no", ScalarTy::Text, &[]),
            col("donor_name", ScalarTy::Text, &[]),
            col("fund_code", ScalarTy::Text, &[]),
            col("gift_date", ScalarTy::Date, &[]),
            col("amount", ScalarTy::Decimal, &[]),
        ],
        rows: vec![
            TableRow {
                cells: vec![
                    Val::Text("R-100".to_string()),
                    Val::Text("Alice Donor".to_string()),
                    Val::Text("GEN".to_string()),
                    Val::Date(BigInt::from(parse_iso_date("2026-10-01")?)),
                    Val::Decimal(parse_decimal_bigint_strict("250.00")?),
                ],
                group_meta: None,
            },
            TableRow {
                cells: vec![
                    Val::Text("R-101".to_string()),
                    Val::Text("Bob Donor".to_string()),
                    Val::Text("SCHOL".to_string()),
                    Val::Date(BigInt::from(parse_iso_date("2026-10-02")?)),
                    Val::Decimal(parse_decimal_bigint_strict("100.50")?),
                ],
                group_meta: None,
            },
            TableRow {
                cells: vec![
                    Val::Text("R-102".to_string()),
                    Val::Text("Carol Donor".to_string()),
                    Val::Text("GEN".to_string()),
                    Val::Date(BigInt::from(parse_iso_date("2026-10-03")?)),
                    Val::Decimal(parse_decimal_bigint_strict("75.25")?),
                ],
                group_meta: None,
            },
        ],
    };
    write_xlsx_file(&xlsx_in, &[("Gifts".to_string(), gifts_tv)])?;

    {
        let mut conn = open_connection(&db_uri)?;
        conn.execute(
            r#"CREATE TABLE "DbGift" (
                "receipt_no" TEXT NOT NULL,
                "donor_id" INTEGER NOT NULL,
                "fund_code" TEXT NOT NULL,
                "gift_date" TEXT NOT NULL,
                "amount" TEXT NOT NULL
            )"#,
            &[],
        )?;
        for (rcpt, did, fund, dt, amt) in [
            ("R-100", 1, "GEN", "2026-10-01", "250.00"),
            ("R-101", 2, "SCHOL", "2026-10-02", "100.00"),
            ("R-103", 3, "BLDG", "2026-10-04", "500.00"),
        ] {
            conn.execute(
                r#"INSERT INTO "DbGift" ("receipt_no", "donor_id", "fund_code", "gift_date", "amount") VALUES (?1, ?2, ?3, ?4, ?5)"#,
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
    let cfg = RunConfig {
        args: vec![xlsx_in.display().to_string()],
        work_dir: Some(tmp.path().to_path_buf()),
        db_bindings,
        allow_export: TagSet::of_list(vec!["donor".to_string(), "financial".to_string()]),
        live_io: true,
        ..RunConfig::default()
    };

    for (engine, res) in [
        ("oracle", run_exec_program(&prog, &cfg)),
        ("vm", run_exec_program_vm(&prog, &cfg, &VmConfig::default())),
    ] {
        match res {
            RunResult::Ok {
                exit_code, stdout, ..
            } => {
                assert_eq!(exit_code, 0, "{engine}");
                assert!(
                    stdout
                        .join("\n")
                        .contains("Reconciled 3 spreadsheet rows (0 malformed)"),
                    "{engine} stdout={stdout:?}"
                );
            }
            other => return Err(format!("{engine} failed: {other:?}").into()),
        }
    }

    // Read back all 4 sheets of the output reconciliation workbook!
    let report_path = tmp.path().join("finance-audit/reconciliation-report.xlsx");
    let summary_schema = table_ty(vec![
        col("metric", ScalarTy::Text, &[]),
        col("count", ScalarTy::Int, &[]),
    ]);
    let (summary, _) =
        read_xlsx_file_with_schema(&report_path, Some("Summary"), &summary_schema, |_, _| true)?;
    assert_eq!(summary.rows.len(), 4);

    let mismatch_schema = table_ty(vec![
        col("receipt_no", ScalarTy::Text, &[]),
        col("fund_code", ScalarTy::Text, &[]),
        col("sheet_amount", ScalarTy::Decimal, &[]),
        col("db_amount", ScalarTy::Decimal, &[]),
        col("delta", ScalarTy::Decimal, &[]),
    ]);
    let (mismatches, _) = read_xlsx_file_with_schema(
        &report_path,
        Some("AmountMismatches"),
        &mismatch_schema,
        |_, _| true,
    )?;
    assert_eq!(mismatches.rows.len(), 1);

    let side_schema = table_ty(vec![
        col("receipt_no", ScalarTy::Text, &[]),
        col("fund_code", ScalarTy::Text, &[]),
        col("amount", ScalarTy::Decimal, &[]),
    ]);
    let (only_sheet, _) = read_xlsx_file_with_schema(
        &report_path,
        Some("OnlyInSpreadsheet"),
        &side_schema,
        |_, _| true,
    )?;
    let (only_db, _) = read_xlsx_file_with_schema(
        &report_path,
        Some("OnlyInDatabase"),
        &side_schema,
        |_, _| true,
    )?;
    assert_eq!(only_sheet.rows.len(), 1);
    assert_eq!(only_db.rows.len(), 1);
    Ok(())
}

#[test]
fn e2e_05_registrar_sync_live_tls_and_sqlite_upsert() -> TestResult {
    let tmp = TempDir::new("e2e_05_registrar")?;

    // Part A: Live loopback OpenSSL TLS server + live SQLite `Seminary` DB upsert running
    //         `examples/registrar-sync.dana` redirected to `127.0.0.1:<port>`!
    let (cert_path, key_path) = generate_self_signed_cert(tmp.path())?;
    let acceptor = TlsServerAcceptor::from_pem_files(&cert_path, &key_path)
        .map_err(|e| format!("acceptor: {e}"))?;
    let listener = TcpListener::bind("127.0.0.1:0")?;
    let port = listener.local_addr()?.port();

    let page1_gz = gzip_bytes(
        br#"{"items":[{"external_id":101,"email":"  Alice@Sem.EDU ","program":" MDiv ","gpa":"3.85","active?":true},{"external_id":104,"email":"bad-email","program":"MAR","gpa":"3.50","active?":true}],"has_more":true}"#,
    )?;
    let page2_gz = gzip_bytes(
        br#"{"items":[{"external_id":103,"email":"Carol@Sem.EDU","program":"ThM","gpa":null,"active?":true}],"has_more":false}"#,
    )?;

    // 4 requests: 2 pages for VM + 2 pages for Oracle
    let srv = thread::spawn(move || {
        for _ in 0..4 {
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
                if reader.read_line(&mut hline).is_err() || hline.trim().is_empty() {
                    break;
                }
            }
            let mut tls = reader.into_inner();
            let body = if path.contains("page=1") {
                encode_chunked(&page1_gz, 21)
            } else {
                encode_chunked(&page2_gz, 21)
            };
            let hdr = "HTTP/1.1 200 OK\r\nContent-Type: application/json\r\nContent-Encoding: gzip\r\nTransfer-Encoding: chunked\r\nConnection: close\r\n\r\n";
            let _ = tls.write_all(hdr.as_bytes());
            let _ = tls.write_all(&body);
            let _ = tls.flush();
        }
    });

    let orig_src = fs::read_to_string(repo_root().join("examples/registrar-sync.dana"))?;
    let live_src = orig_src
        .replace("\"api.populiweb.com\"", "\"127.0.0.1\"")
        .replace(
            "https://api.populiweb.com/v2/students",
            &format!("https://127.0.0.1:{port}/v2/students"),
        );
    let live_policy_src = fs::read_to_string(repo_root().join("examples/dana.policy"))?
        .replace("\"api.populiweb.com\"", "\"127.0.0.1\"");
    let live_file = tmp.path().join("registrar-sync-live.dana");
    fs::write(&live_file, &live_src)?;

    let mut sm = SourceMap::new();
    let pfid = sm.add_file("dana.policy".to_string(), live_policy_src.clone());
    let live_policy =
        parse_policy(pfid, &live_policy_src).map_err(|d| render_diagnostic(&d, &sm))?;
    let resolved =
        resolve_path(&live_file, Some(live_policy), &mut sm).map_err(|ds| format!("{ds:?}"))?;
    let checked = check_resolved(&resolved, &sm).map_err(|ds| format!("{ds:?}"))?;
    let prog = lower_program(checked).map_err(|d| format!("{d:?}"))?.exec;

    for engine in ["vm", "oracle"] {
        let db_path = tmp.path().join(format!("seminary_{engine}.sqlite"));
        let db_uri = format!("sqlite://{}", db_path.display());
        {
            let mut conn = open_connection(&db_uri)?;
            // `db_read.table(DbStudent)` reads `"DbStudent"` and `db_write` writes `"students"`.
            for tbl in ["DbStudent", "students"] {
                conn.execute(
                    &format!(
                        r#"CREATE TABLE "{tbl}" (
                            "student_id" INTEGER PRIMARY KEY,
                            "email" TEXT NOT NULL,
                            "program" TEXT NOT NULL,
                            "gpa" TEXT,
                            "active?" INTEGER NOT NULL
                        )"#
                    ),
                    &[],
                )?;
                for (id, email, prg, gpa, act) in [
                    (101, "alice@sem.edu", "MDiv", "3.80", true),
                    (102, "bob@sem.edu", "MAR", "3.40", true),
                ] {
                    conn.execute(
                        &format!(
                            r#"INSERT INTO "{tbl}" ("student_id", "email", "program", "gpa", "active?") VALUES (?1, ?2, ?3, ?4, ?5)"#
                        ),
                        &[
                            SqlParam::Int(id),
                            SqlParam::Text(email.to_string()),
                            SqlParam::Text(prg.to_string()),
                            SqlParam::Decimal(parse_decimal_bigint_strict(gpa)?),
                            SqlParam::Bool(act),
                        ],
                    )?;
                }
            }
        }

        let mut db_bindings = HashMap::new();
        db_bindings.insert("Seminary".to_string(), db_uri.clone());
        let cfg = RunConfig {
            work_dir: Some(tmp.path().to_path_buf()),
            db_bindings,
            allow_export: TagSet::of_list(vec!["pii".to_string(), "ferpa".to_string()]),
            https_ca_cert: Some(PathBuf::from(&cert_path)),
            live_io: true,
            ..RunConfig::default()
        };
        let res = if engine == "vm" {
            run_exec_program_vm(&prog, &cfg, &VmConfig::default())
        } else {
            run_exec_program(&prog, &cfg)
        };
        match res {
            RunResult::Ok {
                exit_code,
                stdout,
                stderr,
            } => {
                assert_eq!(exit_code, 1, "{engine}: 1 quarantined bad email exits 1");
                assert_eq!(stderr.len(), 1, "{engine} stderr={stderr:?}");
                assert!(
                    stdout.join("\n").contains("1 inserted, 2 updated"),
                    "{engine} stdout={stdout:?}"
                );
            }
            other => return Err(format!("{engine} failed: {other:?}").into()),
        }

        // Verify SQLite `students` table now has 3 rows: 101 updated, 102 deactivated, 103 inserted!
        let mut conn = open_connection(&db_uri)?;
        let verify_schema = table_ty(vec![
            col("student_id", ScalarTy::Int, &[]),
            col("email", ScalarTy::Text, &[]),
            col("active?", ScalarTy::Bool, &[]),
        ]);
        let rows = conn.query_rows(
            r#"SELECT "student_id", "email", "active?" FROM "students" ORDER BY "student_id""#,
            &[],
            &verify_schema,
        )?;
        assert_eq!(rows.rows.len(), 3, "{engine} students row count");
        assert!(val_eq(
            &rows.rows[0].cells[1],
            &Val::Text("alice@sem.edu".to_string())
        ));
        assert!(val_eq(&rows.rows[1].cells[2], &Val::Bool(false)));
        assert!(val_eq(
            &rows.rows[2].cells[1],
            &Val::Text("carol@sem.edu".to_string())
        ));
    }
    let _ = srv.join();

    // Part B: Verbatim `examples/registrar-sync.dana` compiled with `examples/dana.policy`
    let verbatim_prog = compile_example("examples/registrar-sync.dana", true)?;
    let test_out = run_program_tests_vm(
        &verbatim_prog,
        None,
        &RunConfig::default(),
        &VmConfig::default(),
    );
    assert!(!test_out.is_empty() && test_out.iter().all(|o| o.passed));
    let test_oracle = run_program_tests(&verbatim_prog, None, &RunConfig::default());
    assert!(!test_oracle.is_empty() && test_oracle.iter().all(|o| o.passed));
    Ok(())
}

#[test]
fn e2e_06_course_outcomes_stats_live() -> TestResult {
    let tmp = TempDir::new("e2e_06_stats")?;
    fs::create_dir_all(tmp.path().join("data"))?;

    let tv = TableVal {
        cols: vec![
            col("section_id", ScalarTy::Text, &[]),
            col("modality", ScalarTy::Text, &[]),
            col("enrolled", ScalarTy::Int, &[]),
            col("avg_weekly_hours", opt(ScalarTy::Float), &[]),
            col("completion_rate", ScalarTy::Float, &[]),
        ],
        rows: vec![
            ("S1", "online", 20, Some(2.0), 0.62),
            ("S2", "online", 22, Some(3.0), 0.68),
            ("S3", "online", 19, Some(4.0), 0.72),
            ("S4", "in-person", 25, Some(6.0), 0.82),
            ("S5", "in-person", 28, Some(7.0), 0.87),
            ("S6", "in-person", 24, Some(8.0), 0.92),
            ("S7", "online", 15, None, 0.75),
            ("S8", "online", 18, Some(1.5), 0.10),
        ]
        .into_iter()
        .map(|(sid, m, enr, hrs, rate)| TableRow {
            cells: vec![
                Val::Text(sid.to_string()),
                Val::Text(m.to_string()),
                Val::Int(BigInt::from(enr)),
                hrs.map_or(Val::OptNone, |h| {
                    Val::OptSome(Box::new(Val::Float(Float64::from_f64(h))))
                }),
                Val::Float(Float64::from_f64(rate)),
            ],
            group_meta: None,
        })
        .collect(),
    };
    write_parquet_table(
        &tmp.path().join("data/section-outcomes.parquet"),
        &tv,
        ParquetCompression::Zstd,
    )?;

    let prog = compile_example("examples/course-outcomes-stats.dana", true)?;
    let cfg = RunConfig {
        work_dir: Some(tmp.path().to_path_buf()),
        live_io: true,
        ..RunConfig::default()
    };
    for (engine, res) in [
        ("oracle", run_exec_program(&prog, &cfg)),
        ("vm", run_exec_program_vm(&prog, &cfg, &VmConfig::default())),
    ] {
        match res {
            RunResult::Ok {
                exit_code, stdout, ..
            } => {
                assert_eq!(exit_code, 0, "{engine}");
                let out_s = stdout.join("\n");
                assert!(out_s.contains("Dataset Profile"), "{engine} {out_s}");
                assert!(out_s.contains("Pearson r="), "{engine} {out_s}");
            }
            other => return Err(format!("{engine} failed: {other:?}").into()),
        }
    }
    let html = fs::read_to_string(tmp.path().join("reports/course-outcomes.html"))?;
    assert!(html.contains("Course Section Outcomes Study"));
    assert!(html.contains("<svg xmlns=\"http://www.w3.org/2000/svg\""));
    assert!(html.contains("r = "), "expected dynamic r in chart title");
    assert!(!html.contains("NaN"));
    Ok(())
}

#[test]
fn e2e_07_saas_cohort_retention_live() -> TestResult {
    let tmp = TempDir::new("e2e_07_saas")?;
    let db_path = tmp.path().join("billing.sqlite");
    let db_uri = format!("sqlite://{}", db_path.display());

    {
        let mut conn = open_connection(&db_uri)?;
        conn.execute(
            r#"CREATE TABLE "Subscription" ("account_id" INTEGER NOT NULL, "plan" TEXT NOT NULL, "signup_date" TEXT NOT NULL)"#,
            &[],
        )?;
        conn.execute(
            r#"CREATE TABLE "MonthlyInvoice" ("account_id" INTEGER NOT NULL, "bill_month" TEXT NOT NULL, "mrr" TEXT NOT NULL, "paid?" INTEGER NOT NULL)"#,
            &[],
        )?;
        for (aid, plan, dt) in [
            (1, "pro", "2026-01-05"),
            (2, "pro", "2026-01-19"),
            (3, "team", "2026-02-04"),
            (4, "team", "2026-03-02"),
        ] {
            conn.execute(
                r#"INSERT INTO "Subscription" ("account_id", "plan", "signup_date") VALUES (?1, ?2, ?3)"#,
                &[
                    SqlParam::Int(aid),
                    SqlParam::Text(plan.to_string()),
                    SqlParam::Text(dt.to_string()),
                ],
            )?;
        }
        for (aid, bm, mrr, paid) in [
            (1, "2026-01-01", "100.00", true),
            (2, "2026-01-01", "100.00", true),
            (1, "2026-02-01", "100.00", true),
            (2, "2026-02-01", "100.00", false),
            (3, "2026-02-01", "200.00", true),
            (3, "2026-03-01", "200.00", true),
            (4, "2026-03-01", "150.00", true),
        ] {
            conn.execute(
                r#"INSERT INTO "MonthlyInvoice" ("account_id", "bill_month", "mrr", "paid?") VALUES (?1, ?2, ?3, ?4)"#,
                &[
                    SqlParam::Int(aid),
                    SqlParam::Text(bm.to_string()),
                    SqlParam::Decimal(parse_decimal_bigint_strict(mrr)?),
                    SqlParam::Bool(paid),
                ],
            )?;
        }
    }

    let prog = compile_example("examples/saas-cohort-retention.dana", true)?;
    let mut db_bindings = HashMap::new();
    db_bindings.insert("Billing".to_string(), db_uri);
    let cfg = RunConfig {
        work_dir: Some(tmp.path().to_path_buf()),
        db_bindings,
        live_io: true,
        ..RunConfig::default()
    };
    for (engine, res) in [
        ("oracle", run_exec_program(&prog, &cfg)),
        ("vm", run_exec_program_vm(&prog, &cfg, &VmConfig::default())),
    ] {
        match res {
            RunResult::Ok {
                exit_code, stdout, ..
            } => {
                assert_eq!(exit_code, 0, "{engine}");
                assert!(
                    stdout.join("\n").contains("M0"),
                    "{engine} stdout={stdout:?}"
                );
            }
            other => return Err(format!("{engine} failed: {other:?}").into()),
        }
    }
    let html = fs::read_to_string(tmp.path().join("reports/saas-retention.html"))?;
    assert_eq!(
        html.matches("<svg xmlns=\"http://www.w3.org/2000/svg\"")
            .count(),
        2
    );
    assert!(!html.contains("NaN"));
    Ok(())
}

#[test]
fn e2e_08_ecommerce_ledger_audit_live() -> TestResult {
    let tmp = TempDir::new("e2e_08_ecommerce")?;
    fs::create_dir_all(tmp.path().join("data"))?;

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
        ],
    };
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
                    Val::Text("O-999".to_string()),
                    Val::Decimal(parse_decimal_bigint_strict("25.00")?),
                ],
                group_meta: None,
            },
        ],
    };
    write_parquet_table(
        &tmp.path().join("data/orders.parquet"),
        &orders_tv,
        ParquetCompression::Zstd,
    )?;
    write_parquet_table(
        &tmp.path().join("data/payments.parquet"),
        &payments_tv,
        ParquetCompression::Zstd,
    )?;
    fs::write(
        tmp.path().join("data/refunds.csv"),
        "refund_id,order_id,refund_amount\nRF-1,O-1,10.00\n",
    )?;

    let db_path = tmp.path().join("audit.sqlite");
    let db_uri = format!("sqlite://{}", db_path.display());
    {
        let mut conn = open_connection(&db_uri)?;
        conn.execute(
            r#"CREATE TABLE "ledger_runs" (
                "order_id" TEXT PRIMARY KEY,
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
    let cfg = RunConfig {
        work_dir: Some(tmp.path().to_path_buf()),
        db_bindings,
        live_io: true,
        ..RunConfig::default()
    };
    for (engine, res) in [
        ("oracle", run_exec_program(&prog, &cfg)),
        ("vm", run_exec_program_vm(&prog, &cfg, &VmConfig::default())),
    ] {
        match res {
            RunResult::Ok {
                exit_code, stdout, ..
            } => {
                assert_eq!(exit_code, 1, "{engine}: exceptions/orphans exit 1");
                assert!(
                    stdout
                        .join("\n")
                        .contains("Audited 2 orders: 2 exceptions, 1 orphan payments"),
                    "{engine} stdout={stdout:?}"
                );
            }
            other => return Err(format!("{engine} failed: {other:?}").into()),
        }
    }

    let exc_schema = table_ty(vec![
        col("order_id", ScalarTy::Text, &[]),
        col("order_total", ScalarTy::Decimal, &[]),
        col("net_collected", ScalarTy::Decimal, &[]),
        col("variance", ScalarTy::Decimal, &[]),
        col("status", ScalarTy::Text, &[]),
    ]);
    let exc_tv = read_parquet_file_with_schema(
        &tmp.path().join("reports/ledger-exceptions.parquet"),
        &exc_schema,
        |_, _| true,
    )?;
    assert_eq!(exc_tv.rows.len(), 2);

    let mut conn = open_connection(&db_uri)?;
    let db_rows = conn.query_rows(
        r#"SELECT "order_id", "order_total", "net_collected", "variance", "status" FROM "ledger_runs" ORDER BY "order_id""#,
        &[],
        &exc_schema,
    )?;
    assert_eq!(db_rows.rows.len(), 2);
    Ok(())
}

#[test]
fn e2e_09_log_anomaly_triage_live() -> TestResult {
    let tmp = TempDir::new("e2e_09_logs")?;
    let gz_path = tmp.path().join("access.jsonl.gz");

    let mut raw_jsonl = String::new();
    for m in 0..11u32 {
        let mn = m * 5;
        raw_jsonl.push_str(&format!(
            "{{\"ts\":\"2026-10-01T12:{mn:02}:10Z\",\"client_ip\":\"198.51.100.{}\",\"endpoint\":\"/api/pay\",\"status\":200,\"latency_ms\":{:.1}}}\n",
            m + 1,
            24.0 + f64::from(m % 3)
        ));
    }
    raw_jsonl.push_str(
        "{\"ts\":\"2026-10-01T12:55:15Z\",\"client_ip\":\"203.0.113.77\",\"endpoint\":\"/api/pay\",\"status\":502,\"latency_ms\":950.0}\n",
    );
    for m in 0..4u32 {
        let mn = m * 5;
        raw_jsonl.push_str(&format!(
            "{{\"ts\":\"2026-10-01T12:{mn:02}:20Z\",\"client_ip\":\"192.0.2.{}\",\"endpoint\":\"/api/search\",\"status\":200,\"latency_ms\":18.5}}\n",
            m + 1
        ));
    }
    fs::write(&gz_path, gzip_bytes(raw_jsonl.as_bytes())?)?;

    let prog = compile_example("examples/log-anomaly-triage.dana", true)?;
    let cfg = RunConfig {
        args: vec![gz_path.display().to_string()],
        work_dir: Some(tmp.path().to_path_buf()),
        live_io: true,
        ..RunConfig::default()
    };
    for (engine, res) in [
        ("oracle", run_exec_program(&prog, &cfg)),
        ("vm", run_exec_program_vm(&prog, &cfg, &VmConfig::default())),
    ] {
        match res {
            RunResult::Ok {
                exit_code, stdout, ..
            } => {
                assert_eq!(exit_code, 1, "{engine}");
                let out_s = stdout.join("\n");
                assert!(
                    out_s.contains("p95 Latency (5m Buckets)"),
                    "{engine} {out_s}"
                );
                assert!(!out_s.contains("203.0.113.77"), "{engine} leaked IP PII");
            }
            other => return Err(format!("{engine} failed: {other:?}").into()),
        }
    }
    let html = fs::read_to_string(tmp.path().join("reports/incident-triage.html"))?;
    assert!(html.contains("<svg xmlns=\"http://www.w3.org/2000/svg\""));
    assert!(html.contains("[REDACTED]"));
    assert!(!html.contains("203.0.113.77"));
    assert!(!html.contains("NaN"));
    Ok(())
}

#[test]
fn e2e_10_hipaa_clinic_outcomes_live() -> TestResult {
    let tmp = TempDir::new("e2e_10_hipaa")?;
    let db_path = tmp.path().join("clinic.sqlite");
    let db_uri = format!("sqlite://{}", db_path.display());

    {
        let mut conn = open_connection(&db_uri)?;
        conn.execute(
            r#"CREATE TABLE "PatientEncounter" (
                "patient_id" INTEGER NOT NULL,
                "full_name" TEXT NOT NULL,
                "department" TEXT NOT NULL,
                "age_years" INTEGER NOT NULL,
                "length_of_stay_days" TEXT NOT NULL,
                "readmitted_30d?" INTEGER NOT NULL
            )"#,
            &[],
        )?;
        for i in 1..=11i64 {
            conn.execute(
                r#"INSERT INTO "PatientEncounter" ("patient_id", "full_name", "department", "age_years", "length_of_stay_days", "readmitted_30d?") VALUES (?1, ?2, ?3, ?4, ?5, ?6)"#,
                &[
                    SqlParam::Int(i),
                    SqlParam::Text(format!("SecretPatient_{i}")),
                    SqlParam::Text("Cardiology".to_string()),
                    SqlParam::Int(50 + (i % 10)),
                    SqlParam::Decimal(parse_decimal_bigint_strict("4.0")?),
                    SqlParam::Bool(i % 4 == 0),
                ],
            )?;
        }
        for i in 201..=203i64 {
            conn.execute(
                r#"INSERT INTO "PatientEncounter" ("patient_id", "full_name", "department", "age_years", "length_of_stay_days", "readmitted_30d?") VALUES (?1, ?2, ?3, ?4, ?5, ?6)"#,
                &[
                    SqlParam::Int(i),
                    SqlParam::Text(format!("SecretGenetics_{i}")),
                    SqlParam::Text("Genetics".to_string()),
                    SqlParam::Int(31),
                    SqlParam::Decimal(parse_decimal_bigint_strict("2.0")?),
                    SqlParam::Bool(false),
                ],
            )?;
        }
    }

    let prog = compile_example("examples/hipaa-clinic-outcomes.dana", true)?;
    let mut db_bindings = HashMap::new();
    db_bindings.insert("Clinic".to_string(), db_uri);
    let cfg = RunConfig {
        work_dir: Some(tmp.path().to_path_buf()),
        db_bindings,
        live_io: true,
        ..RunConfig::default()
    };
    for (engine, res) in [
        ("oracle", run_exec_program(&prog, &cfg)),
        ("vm", run_exec_program_vm(&prog, &cfg, &VmConfig::default())),
    ] {
        match res {
            RunResult::Ok {
                exit_code, stdout, ..
            } => {
                assert_eq!(exit_code, 0, "{engine}");
                let out_s = stdout.join("\n");
                assert!(out_s.contains("Cardiology"), "{engine} {out_s}");
                assert!(
                    !out_s.contains("Genetics"),
                    "{engine} leaked suppressed < 10 group"
                );
                assert!(
                    !out_s.contains("SecretPatient_"),
                    "{engine} leaked patient name"
                );
            }
            other => return Err(format!("{engine} failed: {other:?}").into()),
        }
    }

    let html = fs::read_to_string(tmp.path().join("reports/clinical-outcomes.html"))?;
    assert!(html.contains("<svg xmlns=\"http://www.w3.org/2000/svg\""));
    assert!(html.contains("Cardiology"));
    assert!(!html.contains("Genetics"));
    assert!(!html.contains("SecretPatient_"));
    assert!(!html.contains("NaN"));
    Ok(())
}
