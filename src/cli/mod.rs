//! Zero-crate CLI entry point for the `dana` toolchain binary.
//!
//! Subcommands:
//! - `dana check [--db Name=URI]... [--attach [DB:]schema=PATH]... [--schema-lock FILE] [--policy FILE] [--json] <FILE...>`
//! - `dana run [--oracle] [--oracle-steps N] [--db Name=URI]... [--attach [DB:]schema=PATH]... [--schema-lock FILE] [--policy FILE] [--allow-export TAGS] [--emit-core] <FILE> [-- ARGS...]`
//! - `dana dry-run [--oracle] [--oracle-steps N] [--db Name=URI]... [--attach [DB:]schema=PATH]... [--schema-lock FILE] [--policy FILE] [--allow-export TAGS] <FILE> [-- ARGS...]`
//! - `dana schema-sync --db Name=URI [--db Name2=URI2 ...] [--attach [DB:]schema=PATH]... [--schemas s1,s2,...] [--out schema.lock]`
//! - `dana explain [--dialect sqlite|postgres] [--schema-lock FILE] [--policy FILE] <FILE>`
//! - `dana repl [--policy FILE] [--db Name=URI]... [--attach [DB:]schema=PATH]... [--schema-lock FILE] [--show-sensitive TAGS] [--eval EXPR]`
//! - `dana vendor pin|verify [--dir PATH]`
//! - `dana test [--oracle] [--policy FILE] [--filter SUBSTR] [PATH...]`
//! - `dana format [--check] <PATH...>`
//! - `dana guide [SECTION]`
//! - `dana infer-schema` / `dana fake`

use std::collections::HashMap;
use std::fmt::Write as _;
use std::fs::{self, File};
use std::io::{self, BufWriter, Cursor, IsTerminal};
use std::path::{Path, PathBuf};

use crate::base::{
    DiagCode, Diagnostic, Severity, SourceMap, render_diagnostic, render_diagnostics_json,
};
use crate::check::{
    check_resolved, check_resolved_with_lock, expected_vendor_module_rel_path, parse_policy,
    pin_vendor_dir, resolve_path, verify_vendor_dir,
};
use crate::core::syntax::{Ident, Policy, TableTy, TagSet};
use crate::core::text::print_program;
use crate::db::schema_lock::{
    SchemaLock, SchemaLockFile, format_schema_lock, merge_schema_lock, parse_schema_lock,
};
use crate::db::{SqlDialect, open_connection, parse_attach_spec};
use crate::formats::compress::{AutoEncodeWriter, detect_compression_path, strip_compression_ext};
use crate::formats::fake::{FakeFormat, write_fake_rows};
use crate::formats::infer::{InferFormat, default_schema_name_from_path, infer_schema_from_file};
use crate::formats::parquet::infer_parquet_schema_from_file;
use crate::formats::xlsx::infer_xlsx_schema_from_file;
use crate::lower::lower_program;
use crate::oracle::cli::parse_comma_tags;
use crate::plan::{
    bind_exec_plan_sources, bind_lty_in_scope, exec_plan_db_names,
    explain_exec_plan_with_pushdown_scoped,
};
use crate::repl::{ReplConfig, ReplSession, run_repl_reader, run_repl_stdio};
use crate::runtime::{RunConfig, RunResult, run_exec_program, run_program_tests};
use crate::syntax::{format_module, parse_module};
use crate::vm::{VmConfig, run_exec_program_vm, run_program_tests_vm};

/// Authoritative Dana Language Reference v0.6 embedded for offline `dana guide`.
pub const EMBEDDED_GUIDE: &str = include_str!("../../docs/reference/README.md");

const USAGE: &str = "\
dana — fast, private, database-native data language toolchain (v0.6)

USAGE:
  dana <COMMAND> [OPTIONS]

COMMANDS:
  check [--db Name=URI]... [--attach [DB:]schema=PATH]... [--schema-lock FILE] [--policy FILE] [--json] <FILE...>
      Parse, type-check, privacy-check, and verify Dana source file(s) (with offline schema.lock).
  run [--oracle] [--oracle-steps N] [--db Name=URI]... [--attach [DB:]schema=PATH]... [--schema-lock FILE] [--policy FILE] [--allow-export TAGS] [--emit-core] <FILE> [-- ARGS...]
      Compile and execute a Dana program's `main` function (vectorized columnar VM + SQL pushdown
      by default; pass `--oracle` for the reference row-by-row engine).
  dry-run [--oracle] [--oracle-steps N] [--db Name=URI]... [--attach [DB:]schema=PATH]... [--schema-lock FILE] [--policy FILE] [--allow-export TAGS] <FILE> [-- ARGS...]
      Execute strictly read-only, printing redacted WriteTable diffs and suppressing disk/DB writes.
  schema-sync --db Name=URI [--db Name2=URI2 ...] [--attach [DB:]schema=PATH]... [--schemas s1,s2,...] [--out schema.lock]
      Introspect live SQLite/PostgreSQL databases and update schema.lock while preserving sensitivity tags.
  explain [--dialect sqlite|postgres] [--schema-lock FILE] [--policy FILE] <FILE>
      Show logical/optimized plans, parameterized SQL pushdown, boundary reasons, and sensitivity provenance.
  repl [--policy FILE] [--db Name=URI]... [--attach [DB:]schema=PATH]... [--schema-lock FILE] [--show-sensitive TAGS] [--eval EXPR]
      Start a safe read-only, privacy-redacted interactive REPL (or run a one-liner via `--eval`).
  vendor pin|verify [--dir PATH]
      Pin or verify SHA-256 hashes of pure-by-default vendored modules in `vendor/vendor.lock`.
  test [--oracle] [--oracle-steps N] [--policy FILE] [--filter SUBSTR] [PATH...]
      Run all inline `examples` and `test` blocks across file(s) or directory.
  format [--check] <PATH...>
      Format Dana source file(s) canonically with 2-space indentation.
  guide [SECTION]
      Print the embedded Dana Language Reference (optionally filtered by section).
  infer-schema <DATA_FILE> [--name Schema] [--sample-rows N] [--format csv|tsv|jsonl|parquet|xlsx]
      Infer a typed Dana schema from CSV/TSV/JSONL/Parquet/XLSX (supports .gz and .zst transparently).
  fake <FILE.dana> [--schema Name] [--rows N] [--seed S] [--format csv|tsv|jsonl] [--out PATH]
      Generate deterministic synthetic constraint-satisfying test data.
  --version, -V
      Show the `dana` toolchain version.
  help, --help, -h
      Show this help message.
";

/// Run the `dana` CLI with process arguments (excluding `argv[0]`), returning an exit code.
#[must_use]
pub fn run_cli(args: &[String]) -> i32 {
    let Some(cmd) = args.first() else {
        eprint!("{USAGE}");
        return 2;
    };
    let rest = &args[1..];
    match cmd.as_str() {
        "help" | "--help" | "-h" => {
            print!("{USAGE}");
            0
        }
        "--version" | "-V" => {
            println!("dana v{}", env!("CARGO_PKG_VERSION"));
            0
        }
        "guide" => cmd_guide(rest),
        "format" => cmd_format(rest),
        "check" => cmd_check(rest),
        "test" => cmd_test(rest),
        "run" => cmd_run_impl(rest, false),
        "dry-run" => cmd_run_impl(rest, true),
        "schema-sync" => cmd_schema_sync(rest),
        "explain" => cmd_explain(rest),
        "repl" => cmd_repl(rest),
        "vendor" => cmd_vendor(rest),
        "infer-schema" => cmd_infer_schema(rest),
        "fake" => cmd_fake(rest),
        other => {
            eprintln!("dana: unknown command `{other}`\n\n{USAGE}");
            2
        }
    }
}

fn cmd_guide(args: &[String]) -> i32 {
    if args.len() == 1 && matches!(args[0].as_str(), "--help" | "-h") {
        println!("usage: dana guide [SECTION]");
        return 0;
    }
    if args.is_empty() {
        print!("{EMBEDDED_GUIDE}");
        return 0;
    }
    let query = args.join(" ").to_ascii_lowercase();
    let mut printing = false;
    let mut found = false;
    for line in EMBEDDED_GUIDE.lines() {
        if line.starts_with("## ") {
            if printing {
                break;
            }
            if line.to_ascii_lowercase().contains(&query) {
                printing = true;
                found = true;
            }
        }
        if printing {
            println!("{line}");
        }
    }
    if !found {
        eprintln!("dana guide: no section matching `{query}`");
        return 1;
    }
    0
}

fn cmd_format(args: &[String]) -> i32 {
    let mut check_only = false;
    let mut paths = Vec::new();
    for a in args {
        if matches!(a.as_str(), "--help" | "-h") {
            println!("usage: dana format [--check] <PATH...>");
            return 0;
        } else if a == "--check" {
            check_only = true;
        } else if a.starts_with('-') {
            eprintln!("dana format: unknown flag `{a}`");
            return 2;
        } else {
            paths.push(PathBuf::from(a));
        }
    }
    if paths.is_empty() {
        eprintln!("dana format: provide at least one `.dana` file or directory");
        return 2;
    }
    let files = match expand_dana_paths(&paths) {
        Ok(f) => f,
        Err(e) => {
            eprintln!("dana format: {e}");
            return 2;
        }
    };

    let mut sm = SourceMap::new();
    let mut any_diff = false;
    for path in files {
        let src = match fs::read_to_string(&path) {
            Ok(s) => s,
            Err(e) => {
                eprintln!("dana format: cannot read `{}`: {e}", path.display());
                return 2;
            }
        };
        let fid = sm.add_file(path.display().to_string(), src.clone());
        let module = match parse_module(fid, &src) {
            Ok(m) => m,
            Err(d) => {
                eprint!("{}", render_diagnostic(&d, &sm));
                return 1;
            }
        };
        let formatted = format_module(&module);
        if formatted != src {
            any_diff = true;
            if check_only {
                eprintln!("would reformat {}", path.display());
                eprint!("{}", render_format_diff(&src, &formatted));
            } else if let Err(e) = fs::write(&path, formatted) {
                eprintln!("dana format: cannot write `{}`: {e}", path.display());
                return 2;
            }
        }
    }
    if check_only && any_diff { 1 } else { 0 }
}

const MAX_FORMAT_DIFF_LINES: usize = 40;
const MAX_LCS_CELLS: usize = 250_000;

#[derive(Clone, Copy)]
enum FormatDiffOp {
    Equal(usize, usize),
    Delete(usize),
    Insert(usize),
}

/// Render a compact, line-numbered diff between an unformatted file (`actual`) and its
/// canonical `dana format` output (`expected`), capped cleanly at 40 changed lines.
#[must_use]
pub fn render_format_diff(actual: &str, expected: &str) -> String {
    if actual == expected {
        return String::new();
    }

    let a_lines: Vec<&str> = actual.lines().collect();
    let b_lines: Vec<&str> = expected.lines().collect();
    if a_lines == b_lines {
        if !actual.ends_with('\n') && expected.ends_with('\n') {
            return "  (missing trailing newline)\n".to_string();
        }
        if actual.contains("\r\n") && !expected.contains("\r\n") {
            return "  (CRLF line endings; canonical format uses LF)\n".to_string();
        }
        return "  (trailing newline/whitespace differs)\n".to_string();
    }

    let mut prefix = 0usize;
    while prefix < a_lines.len() && prefix < b_lines.len() && a_lines[prefix] == b_lines[prefix] {
        prefix += 1;
    }
    let mut suffix = 0usize;
    while suffix < a_lines.len() - prefix
        && suffix < b_lines.len() - prefix
        && a_lines[a_lines.len() - 1 - suffix] == b_lines[b_lines.len() - 1 - suffix]
    {
        suffix += 1;
    }

    let a_mid = &a_lines[prefix..a_lines.len() - suffix];
    let b_mid = &b_lines[prefix..b_lines.len() - suffix];
    let ops = compute_format_diff_ops(a_mid, b_mid, prefix);

    let total_changed = ops
        .iter()
        .filter(|op| !matches!(op, FormatDiffOp::Equal(_, _)))
        .count();
    let num_w = a_lines.len().max(b_lines.len()).max(1).to_string().len();

    let mut out = String::new();
    let mut printed = 0usize;
    let mut idx = 0usize;
    let mut cur_a = prefix + 1;
    let mut cur_b = prefix + 1;

    while idx < ops.len() && printed < MAX_FORMAT_DIFF_LINES {
        match ops[idx] {
            FormatDiffOp::Equal(al, bl) => {
                cur_a = al + 1;
                cur_b = bl + 1;
                idx += 1;
            }
            FormatDiffOp::Delete(_) | FormatDiffOp::Insert(_) => {
                let hunk_a_start = cur_a;
                let hunk_b_start = cur_b;
                let mut dels = Vec::new();
                let mut ins = Vec::new();
                while idx < ops.len() {
                    match ops[idx] {
                        FormatDiffOp::Delete(al) => {
                            dels.push(al);
                            cur_a = al + 1;
                            idx += 1;
                        }
                        FormatDiffOp::Insert(bl) => {
                            ins.push(bl);
                            cur_b = bl + 1;
                            idx += 1;
                        }
                        FormatDiffOp::Equal(_, _) => break,
                    }
                }
                let _ = writeln!(
                    out,
                    "  @@ -{hunk_a_start},{} +{hunk_b_start},{} @@",
                    dels.len(),
                    ins.len()
                );
                for ln in dels {
                    if printed >= MAX_FORMAT_DIFF_LINES {
                        break;
                    }
                    let _ = writeln!(out, "  {ln:>num_w$} - {}", a_lines[ln - 1]);
                    printed += 1;
                }
                for ln in ins {
                    if printed >= MAX_FORMAT_DIFF_LINES {
                        break;
                    }
                    let _ = writeln!(out, "  {ln:>num_w$} + {}", b_lines[ln - 1]);
                    printed += 1;
                }
            }
        }
    }

    if total_changed > printed {
        let more = total_changed - printed;
        let noun = if more == 1 { "line" } else { "lines" };
        let _ = writeln!(out, "  ... ({more} more differing {noun})");
    } else if !actual.ends_with('\n') && expected.ends_with('\n') {
        out.push_str("  (missing trailing newline)\n");
    }

    out
}

fn compute_format_diff_ops(a_mid: &[&str], b_mid: &[&str], prefix: usize) -> Vec<FormatDiffOp> {
    let m = a_mid.len();
    let n = b_mid.len();
    if m.saturating_mul(n) <= MAX_LCS_CELLS {
        let stride = n + 1;
        let mut dp = vec![0u32; (m + 1) * stride];
        for i in (0..m).rev() {
            for j in (0..n).rev() {
                dp[i * stride + j] = if a_mid[i] == b_mid[j] {
                    dp[(i + 1) * stride + (j + 1)] + 1
                } else {
                    dp[(i + 1) * stride + j].max(dp[i * stride + (j + 1)])
                };
            }
        }
        let mut ops = Vec::with_capacity(m.max(n));
        let mut i = 0usize;
        let mut j = 0usize;
        while i < m && j < n {
            if a_mid[i] == b_mid[j] {
                ops.push(FormatDiffOp::Equal(prefix + i + 1, prefix + j + 1));
                i += 1;
                j += 1;
            } else if dp[(i + 1) * stride + j] >= dp[i * stride + (j + 1)] {
                ops.push(FormatDiffOp::Delete(prefix + i + 1));
                i += 1;
            } else {
                ops.push(FormatDiffOp::Insert(prefix + j + 1));
                j += 1;
            }
        }
        while i < m {
            ops.push(FormatDiffOp::Delete(prefix + i + 1));
            i += 1;
        }
        while j < n {
            ops.push(FormatDiffOp::Insert(prefix + j + 1));
            j += 1;
        }
        return ops;
    }

    // Linear-space fallback for very large differing spans.
    let mut ops = Vec::with_capacity(m + n);
    let shared = m.min(n);
    for k in 0..shared {
        if a_mid[k] == b_mid[k] {
            ops.push(FormatDiffOp::Equal(prefix + k + 1, prefix + k + 1));
        } else {
            ops.push(FormatDiffOp::Delete(prefix + k + 1));
            ops.push(FormatDiffOp::Insert(prefix + k + 1));
        }
    }
    for k in shared..m {
        ops.push(FormatDiffOp::Delete(prefix + k + 1));
    }
    for k in shared..n {
        ops.push(FormatDiffOp::Insert(prefix + k + 1));
    }
    ops
}

fn cmd_check(args: &[String]) -> i32 {
    let mut policy_path: Option<PathBuf> = None;
    let mut lock_path: Option<PathBuf> = None;
    let mut json_out = false;
    let mut files = Vec::new();
    let mut i = 0;
    while i < args.len() {
        let arg = args[i].as_str();
        if let Some(val) = arg.strip_prefix("--policy=") {
            policy_path = Some(PathBuf::from(val));
        } else if let Some(val) = arg.strip_prefix("--schema-lock=") {
            lock_path = Some(PathBuf::from(val));
        } else if let Some(val) = arg.strip_prefix("--db=") {
            if let Err(e) = parse_db_binding(val) {
                eprintln!("dana check: {e}");
                return 2;
            }
        } else if let Some(val) = arg.strip_prefix("--attach=") {
            if let Err(e) = crate::db::parse_attach_spec(val) {
                eprintln!("dana check: {e}");
                return 2;
            }
        } else {
            match arg {
                "--policy" => {
                    i += 1;
                    let Some(p) = args.get(i) else {
                        eprintln!("dana check: `--policy` requires a file path");
                        return 2;
                    };
                    policy_path = Some(PathBuf::from(p));
                }
                "--schema-lock" => {
                    i += 1;
                    let Some(p) = args.get(i) else {
                        eprintln!("dana check: `--schema-lock` requires a file path");
                        return 2;
                    };
                    lock_path = Some(PathBuf::from(p));
                }
                "--db" => {
                    i += 1;
                    let Some(raw) = args.get(i) else {
                        eprintln!("dana check: `--db` requires `Name=URI`");
                        return 2;
                    };
                    if let Err(e) = parse_db_binding(raw) {
                        eprintln!("dana check: {e}");
                        return 2;
                    }
                }
                "--attach" => {
                    i += 1;
                    let Some(raw) = args.get(i) else {
                        eprintln!("dana check: `--attach` requires `[DB:]schema=PATH`");
                        return 2;
                    };
                    if let Err(e) = crate::db::parse_attach_spec(raw) {
                        eprintln!("dana check: {e}");
                        return 2;
                    }
                }
                "--json" => json_out = true,
                "--help" | "-h" => {
                    println!(
                        "usage: dana check [--db Name=URI]... [--attach [DB:]schema=PATH]... [--schema-lock FILE] [--policy FILE] [--json] <FILE...>"
                    );
                    return 0;
                }
                flag if flag.starts_with('-') => {
                    eprintln!("dana check: unknown flag `{flag}`");
                    return 2;
                }
                path => files.push(PathBuf::from(path)),
            }
        }
        i += 1;
    }
    if files.is_empty() {
        eprintln!("dana check: provide at least one `.dana` file");
        return 2;
    }
    let expanded = match expand_dana_paths(&files) {
        Ok(f) => f,
        Err(e) => {
            eprintln!("dana check: {e}");
            return 2;
        }
    };

    let mut sm = SourceMap::new();
    let mut all_diags = Vec::new();
    for path in expanded {
        let policy = match load_policy_for(&path, policy_path.as_deref(), &mut sm) {
            Ok(p) => p,
            Err(d) => {
                all_diags.push(d);
                continue;
            }
        };
        let schema_lock = match load_schema_lock_for(&path, lock_path.as_deref()) {
            Ok(l) => l,
            Err(d) => {
                all_diags.push(d);
                continue;
            }
        };
        match resolve_path(&path, policy, &mut sm) {
            Ok(resolved) => match check_resolved_with_lock(&resolved, &sm, schema_lock.as_ref()) {
                Ok(checked) => {
                    all_diags.extend(checked.warnings.iter().cloned());
                    if let Err(d) = lower_program(checked) {
                        all_diags.push(d);
                    }
                }
                Err(ds) => all_diags.extend(ds),
            },
            Err(ds) => all_diags.extend(ds),
        }
    }

    if json_out {
        println!("{}", render_diagnostics_json(&all_diags, &sm));
    } else {
        for d in &all_diags {
            eprint!("{}", render_diagnostic(d, &sm));
        }
    }
    if all_diags.iter().any(|d| d.severity() == Severity::Error) {
        1
    } else {
        0
    }
}

fn parse_positive_usize_flag(cmd_name: &str, flag: &str, raw: &str) -> Result<usize, String> {
    if raw.is_empty() || !raw.bytes().all(|b| b.is_ascii_digit()) {
        return Err(format!(
            "{cmd_name}: `{flag}` requires a positive integer, got `{raw}`"
        ));
    }
    let parsed: usize = raw
        .parse()
        .map_err(|_| format!("{cmd_name}: `{flag}` value `{raw}` overflows step counter"))?;
    if parsed == 0 {
        return Err(format!("{cmd_name}: `{flag}` must be at least 1"));
    }
    Ok(parsed)
}

fn cmd_test(args: &[String]) -> i32 {
    let mut use_oracle = false;
    let mut oracle_steps: Option<usize> = None;
    let mut policy_path: Option<PathBuf> = None;
    let mut filter: Option<String> = None;
    let mut paths = Vec::new();
    let mut i = 0;
    while i < args.len() {
        let arg = args[i].as_str();
        if let Some(val) = arg.strip_prefix("--oracle-steps=") {
            if oracle_steps.is_some() {
                eprintln!("dana test: duplicate `--oracle-steps` flag");
                return 2;
            }
            match parse_positive_usize_flag("dana test", "--oracle-steps", val) {
                Ok(n) => oracle_steps = Some(n),
                Err(e) => {
                    eprintln!("{e}");
                    return 2;
                }
            }
        } else {
            match arg {
                "--oracle" => use_oracle = true,
                "--oracle-steps" => {
                    if oracle_steps.is_some() {
                        eprintln!("dana test: duplicate `--oracle-steps` flag");
                        return 2;
                    }
                    i += 1;
                    let Some(val) = args.get(i) else {
                        eprintln!("dana test: `--oracle-steps` requires a positive integer");
                        return 2;
                    };
                    match parse_positive_usize_flag("dana test", "--oracle-steps", val) {
                        Ok(n) => oracle_steps = Some(n),
                        Err(e) => {
                            eprintln!("{e}");
                            return 2;
                        }
                    }
                }
                "--policy" => {
                    i += 1;
                    let Some(p) = args.get(i) else {
                        eprintln!("dana test: `--policy` requires a file path");
                        return 2;
                    };
                    policy_path = Some(PathBuf::from(p));
                }
                "--filter" => {
                    i += 1;
                    let Some(f) = args.get(i) else {
                        eprintln!("dana test: `--filter` requires a pattern");
                        return 2;
                    };
                    filter = Some(f.clone());
                }
                "--help" | "-h" => {
                    println!(
                        "usage: dana test [--oracle] [--oracle-steps N] [--policy FILE] [--filter SUBSTR] [PATH...]"
                    );
                    return 0;
                }
                flag if flag.starts_with('-') => {
                    eprintln!("dana test: unknown flag `{flag}`");
                    return 2;
                }
                p => paths.push(PathBuf::from(p)),
            }
        }
        i += 1;
    }
    if paths.is_empty() {
        paths.push(PathBuf::from("."));
    }
    let files = match expand_dana_paths(&paths) {
        Ok(f) => f,
        Err(e) => {
            eprintln!("dana test: {e}");
            return 2;
        }
    };

    let mut sm = SourceMap::new();
    let mut total = 0usize;
    let mut failed = 0usize;
    let def_cfg = RunConfig::default();
    let cfg = RunConfig {
        fuel: oracle_steps.unwrap_or(def_cfg.fuel),
        ..def_cfg
    };
    let vm_cfg = VmConfig::default();

    for path in files {
        let policy = match load_policy_for(&path, policy_path.as_deref(), &mut sm) {
            Ok(p) => p,
            Err(d) => {
                eprint!("{}", render_diagnostic(&d, &sm));
                return 1;
            }
        };
        let resolved = match resolve_path(&path, policy, &mut sm) {
            Ok(r) => r,
            Err(ds) => {
                for d in &ds {
                    eprint!("{}", render_diagnostic(d, &sm));
                }
                return 1;
            }
        };
        let checked = match check_resolved(&resolved, &sm) {
            Ok(c) => c,
            Err(ds) => {
                for d in &ds {
                    eprint!("{}", render_diagnostic(d, &sm));
                }
                return 1;
            }
        };
        for w in &checked.warnings {
            eprint!("{}", render_diagnostic(w, &sm));
        }
        let lowered = match lower_program(checked) {
            Ok(l) => l,
            Err(d) => {
                eprint!("{}", render_diagnostic(&d, &sm));
                return 1;
            }
        };
        let outcomes = if use_oracle {
            run_program_tests(&lowered.exec, filter.as_deref(), &cfg)
        } else {
            run_program_tests_vm(&lowered.exec, filter.as_deref(), &cfg, &vm_cfg)
        };
        for o in outcomes {
            total += 1;
            if o.passed {
                println!("ok   {} :: {}", path.display(), o.name);
            } else {
                failed += 1;
                eprintln!(
                    "FAIL {} :: {}: {}",
                    path.display(),
                    o.name,
                    o.message.as_deref().unwrap_or("failed")
                );
            }
        }
    }

    println!(
        "\ntest result: {}. {} passed; {} failed",
        if failed == 0 { "ok" } else { "FAILED" },
        total - failed,
        failed
    );
    if failed == 0 { 0 } else { 1 }
}

fn cmd_run_impl(args: &[String], dry_run: bool) -> i32 {
    let cmd_name = if dry_run { "dana dry-run" } else { "dana run" };
    let mut use_oracle = false;
    let mut oracle_steps: Option<usize> = None;
    let mut policy_path: Option<PathBuf> = None;
    let mut lock_path: Option<PathBuf> = None;
    let mut db_bindings: HashMap<String, String> = HashMap::new();
    let mut sqlite_attachments: Vec<(Option<String>, String, String)> = Vec::new();
    let mut allow_export = TagSet::empty();
    let mut emit_core = false;
    let mut script_path: Option<PathBuf> = None;
    let mut prog_args = Vec::new();
    let mut i = 0;

    while i < args.len() {
        let arg = args[i].as_str();
        if let Some(val) = arg.strip_prefix("--oracle-steps=") {
            if oracle_steps.is_some() {
                eprintln!("{cmd_name}: duplicate `--oracle-steps` flag");
                return 2;
            }
            match parse_positive_usize_flag(cmd_name, "--oracle-steps", val) {
                Ok(n) => oracle_steps = Some(n),
                Err(e) => {
                    eprintln!("{e}");
                    return 2;
                }
            }
        } else if let Some(val) = arg.strip_prefix("--policy=") {
            policy_path = Some(PathBuf::from(val));
        } else if let Some(val) = arg.strip_prefix("--schema-lock=") {
            lock_path = Some(PathBuf::from(val));
        } else if let Some(val) = arg.strip_prefix("--db=") {
            match parse_db_binding(val) {
                Ok((name, uri)) => {
                    db_bindings.insert(name, uri);
                }
                Err(e) => {
                    eprintln!("{cmd_name}: {e}");
                    return 2;
                }
            }
        } else if let Some(val) = arg.strip_prefix("--attach=") {
            match crate::db::parse_attach_spec(val) {
                Ok(spec) => sqlite_attachments.push(spec),
                Err(e) => {
                    eprintln!("{cmd_name}: {e}");
                    return 2;
                }
            }
        } else if let Some(val) = arg.strip_prefix("--allow-export=") {
            match parse_comma_tags(val) {
                Ok(tags) => allow_export = allow_export.union(&tags),
                Err(e) => {
                    eprintln!("{cmd_name}: invalid `--allow-export`: {e}");
                    return 2;
                }
            }
        } else {
            match arg {
                "--" => {
                    prog_args.extend(args[i + 1..].iter().cloned());
                    break;
                }
                "--oracle" => use_oracle = true,
                "--oracle-steps" => {
                    if oracle_steps.is_some() {
                        eprintln!("{cmd_name}: duplicate `--oracle-steps` flag");
                        return 2;
                    }
                    i += 1;
                    let Some(val) = args.get(i) else {
                        eprintln!("{cmd_name}: `--oracle-steps` requires a positive integer");
                        return 2;
                    };
                    match parse_positive_usize_flag(cmd_name, "--oracle-steps", val) {
                        Ok(n) => oracle_steps = Some(n),
                        Err(e) => {
                            eprintln!("{e}");
                            return 2;
                        }
                    }
                }
                "--emit-core" if !dry_run => emit_core = true,
                "--attach" => {
                    i += 1;
                    let Some(raw) = args.get(i) else {
                        eprintln!("{cmd_name}: `--attach` requires `[DB:]schema=PATH`");
                        return 2;
                    };
                    match crate::db::parse_attach_spec(raw) {
                        Ok(spec) => sqlite_attachments.push(spec),
                        Err(e) => {
                            eprintln!("{cmd_name}: {e}");
                            return 2;
                        }
                    }
                }
                "--policy" => {
                    i += 1;
                    let Some(p) = args.get(i) else {
                        eprintln!("{cmd_name}: `--policy` requires a file path");
                        return 2;
                    };
                    policy_path = Some(PathBuf::from(p));
                }
                "--schema-lock" => {
                    i += 1;
                    let Some(p) = args.get(i) else {
                        eprintln!("{cmd_name}: `--schema-lock` requires a file path");
                        return 2;
                    };
                    lock_path = Some(PathBuf::from(p));
                }
                "--db" => {
                    i += 1;
                    let Some(raw) = args.get(i) else {
                        eprintln!("{cmd_name}: `--db` requires `Name=URI`");
                        return 2;
                    };
                    match parse_db_binding(raw) {
                        Ok((name, uri)) => {
                            db_bindings.insert(name, uri);
                        }
                        Err(e) => {
                            eprintln!("{cmd_name}: {e}");
                            return 2;
                        }
                    }
                }
                "--allow-export" => {
                    i += 1;
                    let Some(ts) = args.get(i) else {
                        eprintln!("{cmd_name}: `--allow-export` requires comma-separated tags");
                        return 2;
                    };
                    match parse_comma_tags(ts) {
                        Ok(tags) => allow_export = allow_export.union(&tags),
                        Err(e) => {
                            eprintln!("{cmd_name}: invalid `--allow-export`: {e}");
                            return 2;
                        }
                    }
                }
                "--help" | "-h" if script_path.is_none() => {
                    if dry_run {
                        println!(
                            "usage: dana dry-run [--oracle] [--oracle-steps N] [--db Name=URI]... [--attach [DB:]schema=PATH]... [--schema-lock FILE] [--policy FILE] [--allow-export TAGS] <FILE> [-- ARGS...]"
                        );
                    } else {
                        println!(
                            "usage: dana run [--oracle] [--oracle-steps N] [--db Name=URI]... [--attach [DB:]schema=PATH]... [--schema-lock FILE] [--policy FILE] [--allow-export TAGS] [--emit-core] <FILE> [-- ARGS...]"
                        );
                    }
                    return 0;
                }
                flag if flag.starts_with('-') => {
                    eprintln!("{cmd_name}: unknown flag `{flag}`");
                    return 2;
                }
                p if script_path.is_none() => script_path = Some(PathBuf::from(p)),
                other => prog_args.push(other.to_string()),
            }
        }
        i += 1;
    }

    let Some(path) = script_path else {
        eprintln!("{cmd_name}: missing `.dana` file path");
        return 2;
    };

    let mut sm = SourceMap::new();
    let policy = match load_policy_for(&path, policy_path.as_deref(), &mut sm) {
        Ok(p) => p,
        Err(d) => {
            eprint!("{}", render_diagnostic(&d, &sm));
            return 1;
        }
    };
    let schema_lock = match load_schema_lock_for(&path, lock_path.as_deref()) {
        Ok(l) => l,
        Err(d) => {
            eprint!("{}", render_diagnostic(&d, &sm));
            return 1;
        }
    };
    let resolved = match resolve_path(&path, policy, &mut sm) {
        Ok(r) => r,
        Err(ds) => {
            for d in &ds {
                eprint!("{}", render_diagnostic(d, &sm));
            }
            return 1;
        }
    };
    let checked = match check_resolved_with_lock(&resolved, &sm, schema_lock.as_ref()) {
        Ok(c) => c,
        Err(ds) => {
            for d in &ds {
                eprint!("{}", render_diagnostic(d, &sm));
            }
            return 1;
        }
    };
    for w in &checked.warnings {
        eprint!("{}", render_diagnostic(w, &sm));
    }
    let lowered = match lower_program(checked) {
        Ok(l) => l,
        Err(d) => {
            eprint!("{}", render_diagnostic(&d, &sm));
            return 1;
        }
    };

    if emit_core {
        match &lowered.verified_core {
            Some(cp) => {
                println!("{}", print_program(cp));
                return 0;
            }
            None => {
                eprintln!(
                    "dana run --emit-core: program uses Phase 2/3 runtime extensions outside Core IR v0.1"
                );
                return 1;
            }
        }
    }

    let def_cfg = RunConfig::default();
    let cfg = RunConfig {
        args: prog_args,
        allow_export,
        work_dir: None,
        live_io: true,
        fuel: oracle_steps.unwrap_or(def_cfg.fuel),
        db_bindings,
        sqlite_attachments,
        schema_lock,
        dry_run,
        ..def_cfg
    };
    let res = if use_oracle {
        run_exec_program(&lowered.exec, &cfg)
    } else {
        run_exec_program_vm(&lowered.exec, &cfg, &VmConfig::default())
    };
    match res {
        RunResult::Ok {
            exit_code,
            stdout,
            stderr,
        } => {
            for line in stdout {
                println!("{line}");
            }
            for line in stderr {
                eprintln!("{line}");
            }
            i32::try_from(exit_code).unwrap_or(1)
        }
        RunResult::Stopped {
            bug,
            stdout,
            stderr,
        } => {
            for line in stdout {
                println!("{line}");
            }
            for line in stderr {
                eprintln!("{line}");
            }
            eprintln!("dana runtime stop ({:?}): {}", bug.kind, bug.message);
            1
        }
        RunResult::Failed {
            message,
            stdout,
            stderr,
        } => {
            for line in stdout {
                println!("{line}");
            }
            for line in stderr {
                eprintln!("{line}");
            }
            eprintln!("dana runtime error: {message}");
            1
        }
    }
}

fn parse_schema_list(raw: &str) -> Result<Vec<String>, String> {
    if raw.is_empty() {
        return Err("`--schemas` requires at least one non-empty schema name".to_string());
    }
    let mut out = Vec::new();
    for part in raw.split(',') {
        let s = part.trim();
        if s.is_empty()
            || s.contains(char::is_whitespace)
            || s.as_bytes().contains(&0)
            || s.chars().any(char::is_control)
        {
            return Err(format!("invalid schema name `{part}` in `--schemas`"));
        }
        if !out.iter().any(|existing| existing == s) {
            out.push(s.to_string());
        }
    }
    if out.is_empty() {
        return Err("`--schemas` requires at least one non-empty schema name".to_string());
    }
    Ok(out)
}

fn cmd_schema_sync(args: &[String]) -> i32 {
    let mut db_specs: Vec<(String, String)> = Vec::new();
    let mut sqlite_attachments: Vec<(Option<String>, String, String)> = Vec::new();
    let mut schemas: Vec<String> = Vec::new();
    let mut out_path = PathBuf::from("schema.lock");
    let mut i = 0;

    while i < args.len() {
        let arg = args[i].as_str();
        if let Some(val) = arg.strip_prefix("--db=") {
            match parse_db_binding(val) {
                Ok(pair) => db_specs.push(pair),
                Err(e) => {
                    eprintln!("dana schema-sync: {e}");
                    return 2;
                }
            }
        } else if let Some(val) = arg.strip_prefix("--attach=") {
            match parse_attach_spec(val) {
                Ok(spec) => sqlite_attachments.push(spec),
                Err(e) => {
                    eprintln!("dana schema-sync: {e}");
                    return 2;
                }
            }
        } else if let Some(val) = arg.strip_prefix("--schemas=") {
            match parse_schema_list(val) {
                Ok(list) => {
                    for s in list {
                        if !schemas.contains(&s) {
                            schemas.push(s);
                        }
                    }
                }
                Err(e) => {
                    eprintln!("dana schema-sync: {e}");
                    return 2;
                }
            }
        } else if let Some(val) = arg.strip_prefix("--out=") {
            out_path = PathBuf::from(val);
        } else {
            match arg {
                "--db" => {
                    i += 1;
                    let Some(raw) = args.get(i) else {
                        eprintln!("dana schema-sync: `--db` requires `Name=URI`");
                        return 2;
                    };
                    match parse_db_binding(raw) {
                        Ok(pair) => db_specs.push(pair),
                        Err(e) => {
                            eprintln!("dana schema-sync: {e}");
                            return 2;
                        }
                    }
                }
                "--attach" => {
                    i += 1;
                    let Some(raw) = args.get(i) else {
                        eprintln!("dana schema-sync: `--attach` requires `[DB:]schema=PATH`");
                        return 2;
                    };
                    match parse_attach_spec(raw) {
                        Ok(spec) => sqlite_attachments.push(spec),
                        Err(e) => {
                            eprintln!("dana schema-sync: {e}");
                            return 2;
                        }
                    }
                }
                "--schemas" => {
                    i += 1;
                    let Some(raw) = args.get(i) else {
                        eprintln!(
                            "dana schema-sync: `--schemas` requires comma-separated schema names"
                        );
                        return 2;
                    };
                    match parse_schema_list(raw) {
                        Ok(list) => {
                            for s in list {
                                if !schemas.contains(&s) {
                                    schemas.push(s);
                                }
                            }
                        }
                        Err(e) => {
                            eprintln!("dana schema-sync: {e}");
                            return 2;
                        }
                    }
                }
                "--out" => {
                    i += 1;
                    let Some(p) = args.get(i) else {
                        eprintln!("dana schema-sync: `--out` requires a file path");
                        return 2;
                    };
                    out_path = PathBuf::from(p);
                }
                "--help" | "-h" => {
                    println!(
                        "usage: dana schema-sync --db Name=URI [--db Name2=URI2 ...] [--attach [DB:]schema=PATH]... [--schemas s1,s2,...] [--out schema.lock]"
                    );
                    return 0;
                }
                flag if flag.starts_with('-') => {
                    eprintln!("dana schema-sync: unknown flag `{flag}`");
                    return 2;
                }
                other => {
                    eprintln!("dana schema-sync: unexpected argument `{other}`");
                    return 2;
                }
            }
        }
        i += 1;
    }

    if db_specs.is_empty() {
        eprintln!("dana schema-sync: provide at least one `--db Name=URI`");
        return 2;
    }

    let mut lock = if out_path.is_file() {
        let src = match fs::read_to_string(&out_path) {
            Ok(s) => s,
            Err(e) => {
                eprintln!(
                    "dana schema-sync: cannot read existing `{}`: {e}",
                    out_path.display()
                );
                return 1;
            }
        };
        match parse_schema_lock(&src) {
            Ok(existing) => existing,
            Err(e) => {
                eprintln!(
                    "dana schema-sync: failed to parse `{}`: {e}",
                    out_path.display()
                );
                return 1;
            }
        }
    } else {
        SchemaLock::default()
    };

    for (db_name, uri) in &db_specs {
        let mut conn = match open_connection(uri) {
            Ok(c) => c,
            Err(e) => {
                eprintln!("dana schema-sync: failed connecting to `{db_name}`: {e}");
                return 1;
            }
        };
        if conn.dialect() == SqlDialect::Sqlite {
            for (filter, schema, path) in &sqlite_attachments {
                if (filter.is_none() || filter.as_deref() == Some(db_name.as_str()))
                    && let Err(e) = conn.attach_database(schema, path)
                {
                    eprintln!("dana schema-sync: failed attaching `{schema}` to `{db_name}`: {e}");
                    return 1;
                }
            }
        }
        let fresh = if schemas.is_empty() {
            conn.introspect_schema(db_name)
        } else {
            conn.introspect_schema_with_schemas(db_name, &schemas)
        };
        let fresh = match fresh {
            Ok(f) => f,
            Err(e) => {
                eprintln!("dana schema-sync: failed introspecting `{db_name}`: {e}");
                return 1;
            }
        };
        let (merged, report) = merge_schema_lock(&lock, &fresh);
        lock = merged;
        print!("{report}");
    }

    if let Some(parent) = out_path.parent()
        && !parent.as_os_str().is_empty()
        && let Err(e) = fs::create_dir_all(parent)
    {
        eprintln!(
            "dana schema-sync: cannot create directory `{}`: {e}",
            parent.display()
        );
        return 1;
    }
    let rendered = format_schema_lock(&lock);
    if let Err(e) = fs::write(&out_path, rendered) {
        eprintln!(
            "dana schema-sync: cannot write `{}`: {e}",
            out_path.display()
        );
        return 1;
    }
    println!("wrote {}", out_path.display());
    0
}

struct ScopedExecPlan<'a> {
    plan: &'a crate::runtime::ExecPlan,
    var_tags: HashMap<Ident, TagSet>,
    table_vars: HashMap<Ident, TableTy>,
}

fn collect_exec_plans_with_scope<'a>(
    expr: &'a crate::runtime::ExecExpr,
    var_tags: &HashMap<Ident, TagSet>,
    table_vars: &HashMap<Ident, TableTy>,
    out: &mut Vec<ScopedExecPlan<'a>>,
) {
    use crate::runtime::ExecExpr;
    match expr {
        ExecExpr::Rel(plan) => out.push(ScopedExecPlan {
            plan,
            var_tags: var_tags.clone(),
            table_vars: table_vars.clone(),
        }),
        ExecExpr::LetE {
            name,
            lty,
            bound,
            body,
        } => {
            collect_exec_plans_with_scope(bound, var_tags, table_vars, out);
            let mut next_var_tags = var_tags.clone();
            let mut next_table_vars = table_vars.clone();
            bind_lty_in_scope(name, lty, &mut next_var_tags, &mut next_table_vars);
            collect_exec_plans_with_scope(body, &next_var_tags, &next_table_vars, out);
        }
        ExecExpr::Join {
            params, rhs, body, ..
        } => {
            let mut rhs_var_tags = var_tags.clone();
            let mut rhs_table_vars = table_vars.clone();
            for (pname, plty) in params {
                bind_lty_in_scope(pname, plty, &mut rhs_var_tags, &mut rhs_table_vars);
            }
            collect_exec_plans_with_scope(rhs, &rhs_var_tags, &rhs_table_vars, out);
            collect_exec_plans_with_scope(body, var_tags, table_vars, out);
        }
        ExecExpr::IfE {
            cond,
            then_br,
            else_br,
        } => {
            collect_exec_plans_with_scope(cond, var_tags, table_vars, out);
            collect_exec_plans_with_scope(then_br, var_tags, table_vars, out);
            collect_exec_plans_with_scope(else_br, var_tags, table_vars, out);
        }
        ExecExpr::CaseE { scrut, arms } => {
            collect_exec_plans_with_scope(scrut, var_tags, table_vars, out);
            for a in arms {
                collect_exec_plans_with_scope(&a.body, var_tags, table_vars, out);
            }
        }
        ExecExpr::ForLoop {
            iter_expr,
            state_vars,
            body,
            after,
            ..
        } => {
            collect_exec_plans_with_scope(iter_expr, var_tags, table_vars, out);
            let mut loop_var_tags = var_tags.clone();
            let mut loop_table_vars = table_vars.clone();
            for (sname, slty) in state_vars {
                bind_lty_in_scope(sname, slty, &mut loop_var_tags, &mut loop_table_vars);
            }
            collect_exec_plans_with_scope(body, &loop_var_tags, &loop_table_vars, out);
            collect_exec_plans_with_scope(after, &loop_var_tags, &loop_table_vars, out);
        }
        ExecExpr::WhileLoop {
            cond,
            state_vars,
            body,
            after,
            ..
        } => {
            let mut loop_var_tags = var_tags.clone();
            let mut loop_table_vars = table_vars.clone();
            for (sname, slty) in state_vars {
                bind_lty_in_scope(sname, slty, &mut loop_var_tags, &mut loop_table_vars);
            }
            collect_exec_plans_with_scope(cond, &loop_var_tags, &loop_table_vars, out);
            collect_exec_plans_with_scope(body, &loop_var_tags, &loop_table_vars, out);
            collect_exec_plans_with_scope(after, &loop_var_tags, &loop_table_vars, out);
        }
        ExecExpr::App { fn_expr, args } => {
            collect_exec_plans_with_scope(fn_expr, var_tags, table_vars, out);
            for a in args {
                collect_exec_plans_with_scope(a, var_tags, table_vars, out);
            }
        }
        ExecExpr::Call { args, .. }
        | ExecExpr::Jump { args, .. }
        | ExecExpr::Tuple(args)
        | ExecExpr::Ctor { args, .. }
        | ExecExpr::Prim { args, .. }
        | ExecExpr::Host { args, .. } => {
            for a in args {
                collect_exec_plans_with_scope(a, var_tags, table_vars, out);
            }
        }
        ExecExpr::Proj { tup: e, .. } | ExecExpr::Assert { cond: e, .. } | ExecExpr::Fail(e) => {
            collect_exec_plans_with_scope(e, var_tags, table_vars, out);
        }
        ExecExpr::Lam { params, body, .. } => {
            let mut lam_var_tags = var_tags.clone();
            let mut lam_table_vars = table_vars.clone();
            for (pname, plty) in params {
                bind_lty_in_scope(pname, plty, &mut lam_var_tags, &mut lam_table_vars);
            }
            collect_exec_plans_with_scope(body, &lam_var_tags, &lam_table_vars, out);
        }
        ExecExpr::Stop { detail, .. } => {
            if let Some(d) = detail {
                collect_exec_plans_with_scope(d, var_tags, table_vars, out);
            }
        }
        ExecExpr::Lit(_)
        | ExecExpr::Var(_)
        | ExecExpr::ConstRef(_)
        | ExecExpr::TableLit { .. }
        | ExecExpr::CheckPromise { .. } => {}
    }
}

fn collect_call_db_bindings(
    prog: &crate::runtime::ExecProgram,
) -> HashMap<String, HashMap<String, crate::runtime::ExecPlan>> {
    use crate::runtime::ExecExpr;

    let mut fn_bindings: HashMap<String, HashMap<String, crate::runtime::ExecPlan>> =
        HashMap::new();

    for f in &prog.funs {
        if f.kind.is_spec() {
            continue;
        }
        let mut local_plans: HashMap<String, crate::runtime::ExecPlan> = HashMap::new();
        let mut stack = vec![&f.body];
        while let Some(cur) = stack.pop() {
            match cur {
                ExecExpr::LetE {
                    name, bound, body, ..
                } => {
                    if let ExecExpr::Rel(plan) = bound.as_ref() {
                        let resolved = bind_exec_plan_sources(plan, &local_plans);
                        if !exec_plan_db_names(&resolved, prog).is_empty() {
                            local_plans.insert(name.clone(), resolved);
                        }
                    }
                    stack.push(body);
                    stack.push(bound);
                }
                ExecExpr::Call { fn_name, args } => {
                    if let Some(callee) = prog.find_fun(fn_name)
                        && !callee.kind.is_spec()
                    {
                        for (arg, (pname, _)) in args.iter().zip(&callee.params) {
                            let resolved = match arg {
                                ExecExpr::Rel(plan) => {
                                    let b = bind_exec_plan_sources(plan, &local_plans);
                                    if exec_plan_db_names(&b, prog).is_empty() {
                                        None
                                    } else {
                                        Some(b)
                                    }
                                }
                                ExecExpr::Var(v) => local_plans.get(v).cloned(),
                                _ => None,
                            };
                            if let Some(plan) = resolved {
                                fn_bindings
                                    .entry(callee.name.clone())
                                    .or_default()
                                    .entry(pname.clone())
                                    .or_insert(plan);
                            }
                        }
                    }
                    for a in args {
                        stack.push(a);
                    }
                }
                ExecExpr::Join { rhs, body, .. } => {
                    stack.push(body);
                    stack.push(rhs);
                }
                ExecExpr::IfE {
                    cond,
                    then_br,
                    else_br,
                } => {
                    stack.push(else_br);
                    stack.push(then_br);
                    stack.push(cond);
                }
                ExecExpr::CaseE { scrut, arms } => {
                    for a in arms {
                        stack.push(&a.body);
                    }
                    stack.push(scrut);
                }
                ExecExpr::ForLoop {
                    iter_expr,
                    body,
                    after,
                    ..
                } => {
                    stack.push(after);
                    stack.push(body);
                    stack.push(iter_expr);
                }
                ExecExpr::WhileLoop {
                    cond, body, after, ..
                } => {
                    stack.push(after);
                    stack.push(body);
                    stack.push(cond);
                }
                ExecExpr::App { fn_expr, args } => {
                    for a in args {
                        stack.push(a);
                    }
                    stack.push(fn_expr);
                }
                ExecExpr::Jump { args, .. }
                | ExecExpr::Tuple(args)
                | ExecExpr::Ctor { args, .. }
                | ExecExpr::Prim { args, .. }
                | ExecExpr::Host { args, .. } => {
                    for a in args {
                        stack.push(a);
                    }
                }
                ExecExpr::Proj { tup: e, .. }
                | ExecExpr::Assert { cond: e, .. }
                | ExecExpr::Fail(e) => stack.push(e),
                ExecExpr::Lam { body, .. } => stack.push(body),
                ExecExpr::Stop {
                    detail: Some(d), ..
                } => stack.push(d),
                ExecExpr::Lit(_)
                | ExecExpr::Var(_)
                | ExecExpr::ConstRef(_)
                | ExecExpr::TableLit { .. }
                | ExecExpr::Rel(_)
                | ExecExpr::CheckPromise { .. }
                | ExecExpr::Stop { detail: None, .. } => {}
            }
        }
    }
    fn_bindings
}

fn collect_local_db_plans(
    expr: &crate::runtime::ExecExpr,
    prog: &crate::runtime::ExecProgram,
    initial: &HashMap<String, crate::runtime::ExecPlan>,
) -> HashMap<String, crate::runtime::ExecPlan> {
    use crate::runtime::ExecExpr;
    let mut map = initial.clone();
    let mut stack = vec![expr];
    while let Some(cur) = stack.pop() {
        if let ExecExpr::LetE {
            name, bound, body, ..
        } = cur
        {
            if let ExecExpr::Rel(plan) = bound.as_ref() {
                let resolved = bind_exec_plan_sources(plan, &map);
                if !exec_plan_db_names(&resolved, prog).is_empty() {
                    map.insert(name.clone(), resolved);
                }
            }
            stack.push(body);
            stack.push(bound);
        }
    }
    map
}

/// Render a complete `dana explain` report (logical plan, optimized plan, parameterized SQL
/// pushdown, boundary reasons, local VM suffix, and sensitivity provenance) for `prog`.
#[must_use]
pub fn render_explain_report(
    prog: &crate::runtime::ExecProgram,
    explicit_dialect: Option<SqlDialect>,
    schema_lock: Option<&SchemaLockFile>,
    display_path: &Path,
) -> String {
    let (opt_prog, _) = crate::plan::optimize_exec_program(prog);
    let prog = &opt_prog;
    let fn_bindings = collect_call_db_bindings(prog);
    let mut out = String::new();
    let mut found_any = false;

    for include_spec in [false, true] {
        if include_spec && found_any {
            break;
        }
        for f in &prog.funs {
            if f.kind.is_spec() != include_spec {
                continue;
            }
            let mut base_var_tags = HashMap::new();
            let mut base_table_vars = HashMap::new();
            for (pname, plty) in &f.params {
                bind_lty_in_scope(pname, plty, &mut base_var_tags, &mut base_table_vars);
            }
            let mut plans = Vec::new();
            collect_exec_plans_with_scope(&f.body, &base_var_tags, &base_table_vars, &mut plans);
            if plans.is_empty() {
                continue;
            }
            found_any = true;
            let base_bindings = fn_bindings.get(&f.name).cloned().unwrap_or_default();
            let combined = collect_local_db_plans(&f.body, prog, &base_bindings);
            let _ = writeln!(out, "== fn {} ==", f.name);
            for (idx, scoped) in plans.iter().enumerate() {
                let bound = if combined.is_empty() {
                    scoped.plan.clone()
                } else {
                    bind_exec_plan_sources(scoped.plan, &combined)
                };
                let db_names = exec_plan_db_names(&bound, prog);
                let db_name = db_names.first().cloned().unwrap_or_default();
                let dialect = explicit_dialect
                    .or_else(|| {
                        schema_lock
                            .and_then(|l| {
                                if !db_name.is_empty() {
                                    l.find_db(&db_name)
                                } else {
                                    None
                                }
                                .or_else(|| l.dbs.first())
                            })
                            .map(|d| d.dialect)
                    })
                    .unwrap_or(SqlDialect::Postgres);
                let _ = writeln!(out, "-- plan #{idx} (dialect: {dialect}) --");
                let explained = explain_exec_plan_with_pushdown_scoped(
                    &bound,
                    prog,
                    &db_name,
                    dialect,
                    schema_lock,
                    &scoped.var_tags,
                    &scoped.table_vars,
                );
                out.push_str(&explained);
            }
        }
    }

    if !found_any {
        let _ = writeln!(out, "no relational plans in {}", display_path.display());
    }
    out
}

fn cmd_explain(args: &[String]) -> i32 {
    let mut policy_path: Option<PathBuf> = None;
    let mut lock_path: Option<PathBuf> = None;
    let mut explicit_dialect: Option<SqlDialect> = None;
    let mut script_path: Option<PathBuf> = None;
    let mut i = 0;
    while i < args.len() {
        let arg = args[i].as_str();
        if let Some(val) = arg.strip_prefix("--policy=") {
            policy_path = Some(PathBuf::from(val));
        } else if let Some(val) = arg.strip_prefix("--schema-lock=") {
            lock_path = Some(PathBuf::from(val));
        } else if let Some(val) = arg.strip_prefix("--dialect=") {
            match parse_dialect(val) {
                Ok(d) => explicit_dialect = Some(d),
                Err(e) => {
                    eprintln!("dana explain: {e}");
                    return 2;
                }
            }
        } else {
            match arg {
                "--policy" => {
                    i += 1;
                    let Some(p) = args.get(i) else {
                        eprintln!("dana explain: `--policy` requires a file path");
                        return 2;
                    };
                    policy_path = Some(PathBuf::from(p));
                }
                "--schema-lock" => {
                    i += 1;
                    let Some(p) = args.get(i) else {
                        eprintln!("dana explain: `--schema-lock` requires a file path");
                        return 2;
                    };
                    lock_path = Some(PathBuf::from(p));
                }
                "--dialect" => {
                    i += 1;
                    let Some(raw) = args.get(i) else {
                        eprintln!("dana explain: `--dialect` requires `sqlite` or `postgres`");
                        return 2;
                    };
                    match parse_dialect(raw) {
                        Ok(d) => explicit_dialect = Some(d),
                        Err(e) => {
                            eprintln!("dana explain: {e}");
                            return 2;
                        }
                    }
                }
                "--help" | "-h" => {
                    println!(
                        "usage: dana explain [--dialect sqlite|postgres] [--schema-lock FILE] [--policy FILE] <FILE>"
                    );
                    return 0;
                }
                flag if flag.starts_with('-') => {
                    eprintln!("dana explain: unknown flag `{flag}`");
                    return 2;
                }
                p if script_path.is_none() => script_path = Some(PathBuf::from(p)),
                other => {
                    eprintln!("dana explain: unexpected argument `{other}`");
                    return 2;
                }
            }
        }
        i += 1;
    }
    let Some(path) = script_path else {
        eprintln!("dana explain: missing `.dana` file path");
        return 2;
    };
    let mut sm = SourceMap::new();
    let policy = match load_policy_for(&path, policy_path.as_deref(), &mut sm) {
        Ok(p) => p,
        Err(d) => {
            eprint!("{}", render_diagnostic(&d, &sm));
            return 1;
        }
    };
    let schema_lock = match load_schema_lock_for(&path, lock_path.as_deref()) {
        Ok(l) => l,
        Err(d) => {
            eprint!("{}", render_diagnostic(&d, &sm));
            return 1;
        }
    };
    let resolved = match resolve_path(&path, policy, &mut sm) {
        Ok(r) => r,
        Err(ds) => {
            for d in &ds {
                eprint!("{}", render_diagnostic(d, &sm));
            }
            return 1;
        }
    };
    let checked = match check_resolved_with_lock(&resolved, &sm, schema_lock.as_ref()) {
        Ok(c) => c,
        Err(ds) => {
            for d in &ds {
                eprint!("{}", render_diagnostic(d, &sm));
            }
            return 1;
        }
    };
    let lowered = match lower_program(checked) {
        Ok(l) => l,
        Err(d) => {
            eprint!("{}", render_diagnostic(&d, &sm));
            return 1;
        }
    };

    let report =
        render_explain_report(&lowered.exec, explicit_dialect, schema_lock.as_ref(), &path);
    print!("{report}");
    0
}

fn cmd_vendor(args: &[String]) -> i32 {
    let Some(sub) = args.first().map(String::as_str) else {
        eprintln!(
            "dana vendor: expected subcommand `pin` or `verify` (`dana vendor pin|verify [--dir PATH]`)"
        );
        return 2;
    };
    if matches!(sub, "--help" | "-h" | "help") {
        println!("usage: dana vendor pin|verify [--dir PATH]");
        return 0;
    }
    if !matches!(sub, "pin" | "verify") {
        eprintln!("dana vendor: unknown subcommand `{sub}` (expected `pin` or `verify`)");
        return 2;
    }

    let mut vendor_dir = PathBuf::from("vendor");
    let mut i = 1usize;
    while i < args.len() {
        let arg = args[i].as_str();
        if let Some(val) = arg.strip_prefix("--dir=") {
            vendor_dir = PathBuf::from(val);
        } else if arg == "--dir" {
            i += 1;
            let Some(p) = args.get(i) else {
                eprintln!("dana vendor {sub}: `--dir` requires a directory path");
                return 2;
            };
            vendor_dir = PathBuf::from(p);
        } else if arg.starts_with('-') {
            eprintln!("dana vendor {sub}: unknown flag `{arg}`");
            return 2;
        } else {
            eprintln!("dana vendor {sub}: unexpected argument `{arg}`");
            return 2;
        }
        i += 1;
    }

    match sub {
        "pin" => match pin_vendor_dir(&vendor_dir) {
            Ok((lock, paths)) => {
                for entry in &lock.entries {
                    let expected = expected_vendor_module_rel_path(&entry.module);
                    if entry.path != expected {
                        eprintln!(
                            "warning: vendored module `{}` is at `{}`, but `use {}` expects `{expected}`",
                            entry.module, entry.path, entry.module
                        );
                    }
                }
                for p in &paths {
                    println!("pinned {p}");
                }
                println!(
                    "wrote {} ({} module(s))",
                    vendor_dir.join("vendor.lock").display(),
                    lock.entries.len()
                );
                0
            }
            Err(msg) => {
                eprintln!("dana vendor pin: {msg}");
                1
            }
        },
        "verify" => match verify_vendor_dir(&vendor_dir) {
            Ok(paths) => {
                println!(
                    "ok: verified {} vendored module(s) in {}",
                    paths.len(),
                    vendor_dir.join("vendor.lock").display()
                );
                0
            }
            Err(errs) => {
                for err in errs {
                    eprintln!("dana vendor verify: {err}");
                }
                1
            }
        },
        _ => 2,
    }
}

fn cmd_repl(args: &[String]) -> i32 {
    let mut policy_path: Option<PathBuf> = None;
    let mut lock_path: Option<PathBuf> = None;
    let mut db_bindings: Vec<(String, String)> = Vec::new();
    let mut sqlite_attachments: Vec<(Option<String>, String, String)> = Vec::new();
    let mut allowed_show_tags = TagSet::empty();
    let mut eval_expr: Option<String> = None;
    let mut i = 0usize;

    while i < args.len() {
        let arg = args[i].as_str();
        if let Some(val) = arg.strip_prefix("--policy=") {
            policy_path = Some(PathBuf::from(val));
        } else if let Some(val) = arg.strip_prefix("--schema-lock=") {
            lock_path = Some(PathBuf::from(val));
        } else if let Some(val) = arg.strip_prefix("--db=") {
            match parse_db_binding(val) {
                Ok(pair) => db_bindings.push(pair),
                Err(e) => {
                    eprintln!("dana repl: {e}");
                    return 2;
                }
            }
        } else if let Some(val) = arg.strip_prefix("--attach=") {
            match parse_attach_spec(val) {
                Ok(spec) => sqlite_attachments.push(spec),
                Err(e) => {
                    eprintln!("dana repl: {e}");
                    return 2;
                }
            }
        } else if let Some(val) = arg.strip_prefix("--show-sensitive=") {
            match parse_comma_tags(val) {
                Ok(tags) => allowed_show_tags = allowed_show_tags.union(&tags),
                Err(e) => {
                    eprintln!("dana repl: invalid `--show-sensitive`: {e}");
                    return 2;
                }
            }
        } else if let Some(val) = arg.strip_prefix("--eval=") {
            eval_expr = Some(val.to_string());
        } else {
            match arg {
                "--policy" => {
                    i += 1;
                    let Some(p) = args.get(i) else {
                        eprintln!("dana repl: `--policy` requires a file path");
                        return 2;
                    };
                    policy_path = Some(PathBuf::from(p));
                }
                "--schema-lock" => {
                    i += 1;
                    let Some(p) = args.get(i) else {
                        eprintln!("dana repl: `--schema-lock` requires a file path");
                        return 2;
                    };
                    lock_path = Some(PathBuf::from(p));
                }
                "--db" => {
                    i += 1;
                    let Some(raw) = args.get(i) else {
                        eprintln!("dana repl: `--db` requires `Name=URI`");
                        return 2;
                    };
                    match parse_db_binding(raw) {
                        Ok(pair) => db_bindings.push(pair),
                        Err(e) => {
                            eprintln!("dana repl: {e}");
                            return 2;
                        }
                    }
                }
                "--attach" => {
                    i += 1;
                    let Some(raw) = args.get(i) else {
                        eprintln!("dana repl: `--attach` requires `[DB:]schema=PATH`");
                        return 2;
                    };
                    match parse_attach_spec(raw) {
                        Ok(spec) => sqlite_attachments.push(spec),
                        Err(e) => {
                            eprintln!("dana repl: {e}");
                            return 2;
                        }
                    }
                }
                "--show-sensitive" => {
                    i += 1;
                    let Some(ts) = args.get(i) else {
                        eprintln!("dana repl: `--show-sensitive` requires comma-separated tags");
                        return 2;
                    };
                    match parse_comma_tags(ts) {
                        Ok(tags) => allowed_show_tags = allowed_show_tags.union(&tags),
                        Err(e) => {
                            eprintln!("dana repl: invalid `--show-sensitive`: {e}");
                            return 2;
                        }
                    }
                }
                "--eval" => {
                    i += 1;
                    let Some(expr) = args.get(i) else {
                        eprintln!("dana repl: `--eval` requires an expression");
                        return 2;
                    };
                    eval_expr = Some(expr.clone());
                }
                "--help" | "-h" => {
                    println!(
                        "usage: dana repl [--policy FILE] [--db Name=URI]... [--attach [DB:]schema=PATH]... [--schema-lock FILE] [--show-sensitive TAGS] [--eval EXPR]"
                    );
                    return 0;
                }
                flag if flag.starts_with('-') => {
                    eprintln!("dana repl: unknown flag `{flag}`");
                    return 2;
                }
                other => {
                    eprintln!("dana repl: unexpected argument `{other}`");
                    return 2;
                }
            }
        }
        i += 1;
    }

    let cwd = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
    let mut sm = SourceMap::new();
    let policy = match load_policy_from_dir_or_ancestors(&cwd, policy_path.as_deref(), &mut sm) {
        Ok(p) => p,
        Err(d) => {
            eprint!("{}", render_diagnostic(&d, &sm));
            return 1;
        }
    };
    let schema_lock = match load_schema_lock_for(&cwd.join("repl.dana"), lock_path.as_deref()) {
        Ok(l) => l,
        Err(d) => {
            eprint!("{}", render_diagnostic(&d, &sm));
            return 1;
        }
    };

    let cfg = ReplConfig {
        policy,
        db_bindings,
        sqlite_attachments,
        schema_lock,
        allowed_show_tags,
        work_dir: cwd,
        vm_cfg: VmConfig::default(),
    };
    let mut session = match ReplSession::new(cfg) {
        Ok(s) => s,
        Err(d) => {
            eprint!("{}", render_diagnostic(&d, &sm));
            return 1;
        }
    };

    if let Some(expr) = eval_expr {
        let stdout = io::stdout();
        let stderr = io::stderr();
        let mut out = stdout.lock();
        let mut err = stderr.lock();
        run_repl_reader(
            &mut session,
            Cursor::new(format!("{expr}\n").into_bytes()),
            &mut out,
            &mut err,
            false,
            true,
        )
    } else {
        let interactive = io::stdin().is_terminal();
        run_repl_stdio(&mut session, interactive)
    }
}

fn cmd_infer_schema(args: &[String]) -> i32 {
    enum CliInferFormat {
        Text(InferFormat),
        Parquet,
        Xlsx,
    }

    let mut data_path: Option<PathBuf> = None;
    let mut schema_name: Option<String> = None;
    let mut sample_rows: usize = 10_000;
    let mut format_override: Option<CliInferFormat> = None;
    let mut i = 0;

    while i < args.len() {
        match args[i].as_str() {
            "--name" => {
                i += 1;
                let Some(n) = args.get(i) else {
                    eprintln!("dana infer-schema: `--name` requires a schema identifier");
                    return 2;
                };
                schema_name = Some(n.clone());
            }
            "--sample-rows" => {
                i += 1;
                let Some(raw) = args.get(i) else {
                    eprintln!("dana infer-schema: `--sample-rows` requires a positive integer");
                    return 2;
                };
                match raw.parse::<usize>() {
                    Ok(n) if n > 0 => sample_rows = n,
                    _ => {
                        eprintln!("dana infer-schema: invalid `--sample-rows` `{raw}`");
                        return 2;
                    }
                }
            }
            "--format" => {
                i += 1;
                let Some(raw) = args.get(i) else {
                    eprintln!(
                        "dana infer-schema: `--format` requires csv, tsv, jsonl, parquet, or xlsx"
                    );
                    return 2;
                };
                format_override = match raw.to_ascii_lowercase().as_str() {
                    "csv" => Some(CliInferFormat::Text(InferFormat::Csv)),
                    "tsv" => Some(CliInferFormat::Text(InferFormat::Tsv)),
                    "jsonl" | "ndjson" => Some(CliInferFormat::Text(InferFormat::Jsonl)),
                    "parquet" => Some(CliInferFormat::Parquet),
                    "xlsx" => Some(CliInferFormat::Xlsx),
                    other => {
                        eprintln!("dana infer-schema: unsupported format `{other}`");
                        return 2;
                    }
                };
            }
            "--help" | "-h" => {
                println!(
                    "usage: dana infer-schema <DATA_FILE> [--name Schema] [--sample-rows N] [--format csv|tsv|jsonl|parquet|xlsx]"
                );
                return 0;
            }
            flag if flag.starts_with('-') => {
                eprintln!("dana infer-schema: unknown flag `{flag}`");
                return 2;
            }
            p if data_path.is_none() => data_path = Some(PathBuf::from(p)),
            other => {
                eprintln!("dana infer-schema: unexpected argument `{other}`");
                return 2;
            }
        }
        i += 1;
    }

    let Some(path) = data_path else {
        eprintln!("dana infer-schema: missing data file path");
        return 2;
    };
    let name = match schema_name {
        Some(n) => {
            if !is_valid_schema_cap_name(&n) {
                eprintln!(
                    "dana infer-schema: invalid schema name `{n}` (must match `[A-Z][A-Za-z0-9_]*`)"
                );
                return 2;
            }
            n
        }
        None => default_schema_name_from_path(&path),
    };
    let lower_inner = strip_compression_ext(&path.to_string_lossy()).to_ascii_lowercase();
    let res = match format_override {
        Some(CliInferFormat::Parquet) => infer_parquet_schema_from_file(&path, &name),
        Some(CliInferFormat::Xlsx) => infer_xlsx_schema_from_file(&path, None, &name),
        Some(CliInferFormat::Text(fmt)) => {
            infer_schema_from_file(&path, &name, Some(fmt), sample_rows)
        }
        None if lower_inner.ends_with(".parquet") => infer_parquet_schema_from_file(&path, &name),
        None if lower_inner.ends_with(".xlsx") => infer_xlsx_schema_from_file(&path, None, &name),
        None => infer_schema_from_file(&path, &name, None, sample_rows),
    };
    match res {
        Ok(schema) => {
            print!("{}", schema.render_dana());
            0
        }
        Err(msg) => {
            eprintln!("dana infer-schema: {msg}");
            1
        }
    }
}

fn is_valid_schema_cap_name(name: &str) -> bool {
    let mut chars = name.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    first.is_ascii_uppercase() && chars.all(|c| c.is_ascii_alphanumeric() || c == '_')
}

fn cmd_fake(args: &[String]) -> i32 {
    let mut script_path: Option<PathBuf> = None;
    let mut schema_name: Option<String> = None;
    let mut rows: usize = 100;
    let mut seed: u64 = 1;
    let mut format: Option<FakeFormat> = None;
    let mut out_path: Option<PathBuf> = None;
    let mut i = 0;

    while i < args.len() {
        match args[i].as_str() {
            "--schema" => {
                i += 1;
                let Some(s) = args.get(i) else {
                    eprintln!("dana fake: `--schema` requires a schema name");
                    return 2;
                };
                schema_name = Some(s.clone());
            }
            "--rows" => {
                i += 1;
                let Some(raw) = args.get(i) else {
                    eprintln!("dana fake: `--rows` requires a non-negative integer");
                    return 2;
                };
                match raw.parse::<usize>() {
                    Ok(n) => rows = n,
                    Err(_) => {
                        eprintln!("dana fake: invalid `--rows` `{raw}`");
                        return 2;
                    }
                }
            }
            "--seed" => {
                i += 1;
                let Some(raw) = args.get(i) else {
                    eprintln!("dana fake: `--seed` requires a u64 integer");
                    return 2;
                };
                match raw.parse::<u64>() {
                    Ok(s) => seed = s,
                    Err(_) => {
                        eprintln!("dana fake: invalid `--seed` `{raw}`");
                        return 2;
                    }
                }
            }
            "--format" => {
                i += 1;
                let Some(raw) = args.get(i) else {
                    eprintln!("dana fake: `--format` requires csv, tsv, or jsonl");
                    return 2;
                };
                format = match raw.to_ascii_lowercase().as_str() {
                    "csv" => Some(FakeFormat::Csv),
                    "tsv" => Some(FakeFormat::Tsv),
                    "jsonl" | "ndjson" => Some(FakeFormat::Jsonl),
                    other => {
                        eprintln!("dana fake: unsupported format `{other}`");
                        return 2;
                    }
                };
            }
            "--out" => {
                i += 1;
                let Some(p) = args.get(i) else {
                    eprintln!("dana fake: `--out` requires an output path");
                    return 2;
                };
                out_path = Some(PathBuf::from(p));
            }
            "--help" | "-h" => {
                println!(
                    "usage: dana fake <FILE.dana> [--schema Name] [--rows N] [--seed S] [--format csv|tsv|jsonl] [--out PATH]"
                );
                return 0;
            }
            flag if flag.starts_with('-') => {
                eprintln!("dana fake: unknown flag `{flag}`");
                return 2;
            }
            p if script_path.is_none() => script_path = Some(PathBuf::from(p)),
            other => {
                eprintln!("dana fake: unexpected argument `{other}`");
                return 2;
            }
        }
        i += 1;
    }

    let Some(path) = script_path else {
        eprintln!("dana fake: missing `.dana` file path");
        return 2;
    };

    let mut sm = SourceMap::new();
    let policy = match load_policy_for(&path, None, &mut sm) {
        Ok(p) => p,
        Err(d) => {
            eprint!("{}", render_diagnostic(&d, &sm));
            return 1;
        }
    };
    let resolved = match resolve_path(&path, policy, &mut sm) {
        Ok(r) => r,
        Err(ds) => {
            for d in &ds {
                eprint!("{}", render_diagnostic(d, &sm));
            }
            return 1;
        }
    };
    let checked = match check_resolved(&resolved, &sm) {
        Ok(c) => c,
        Err(ds) => {
            for d in &ds {
                eprint!("{}", render_diagnostic(d, &sm));
            }
            return 1;
        }
    };
    let lowered = match lower_program(checked) {
        Ok(l) => l,
        Err(d) => {
            eprint!("{}", render_diagnostic(&d, &sm));
            return 1;
        }
    };

    let target_schema = match &schema_name {
        Some(name) => match lowered.exec.find_schema(name) {
            Some(s) => s,
            None => {
                eprintln!("dana fake: unknown schema `{name}` in `{}`", path.display());
                return 1;
            }
        },
        None => match lowered.exec.schemas.first() {
            Some(s) => s,
            None => {
                eprintln!(
                    "dana fake: no `schema` declarations found in `{}`",
                    path.display()
                );
                return 1;
            }
        },
    };

    let chosen_fmt = format.unwrap_or_else(|| {
        if let Some(op) = &out_path {
            let inner = crate::formats::compress::strip_compression_ext(&op.to_string_lossy())
                .to_ascii_lowercase();
            if inner.ends_with(".tsv") {
                FakeFormat::Tsv
            } else if inner.ends_with(".jsonl") || inner.ends_with(".ndjson") {
                FakeFormat::Jsonl
            } else {
                FakeFormat::Csv
            }
        } else {
            FakeFormat::Csv
        }
    });

    if let Some(op) = out_path {
        let comp = detect_compression_path(&op.to_string_lossy());
        let res = File::create(&op).and_then(|f| {
            let mut enc = AutoEncodeWriter::new(BufWriter::new(f), comp)?;
            write_fake_rows(&mut enc, target_schema, rows, seed, chosen_fmt)?;
            enc.finish()?;
            Ok(())
        });
        if let Err(e) = res {
            eprintln!("dana fake: failed writing `{}`: {e}", op.display());
            return 1;
        }
        0
    } else {
        let stdout = io::stdout();
        let mut handle = BufWriter::new(stdout.lock());
        if let Err(e) = write_fake_rows(&mut handle, target_schema, rows, seed, chosen_fmt) {
            eprintln!("dana fake: write error: {e}");
            return 1;
        }
        if let Err(e) = std::io::Write::flush(&mut handle) {
            eprintln!("dana fake: flush error: {e}");
            return 1;
        }
        0
    }
}

fn parse_db_binding(raw: &str) -> Result<(String, String), String> {
    let Some((name, uri)) = raw.split_once('=') else {
        return Err(format!(
            "invalid `--db` argument `{raw}` (expected `Name=URI`)"
        ));
    };
    let name = name.trim();
    let uri = uri.trim();
    if name.is_empty() || uri.is_empty() {
        return Err(format!(
            "invalid `--db` argument `{raw}` (both database name and URI must be non-empty)"
        ));
    }
    Ok((name.to_string(), uri.to_string()))
}

fn parse_dialect(raw: &str) -> Result<SqlDialect, String> {
    match raw.to_ascii_lowercase().as_str() {
        "sqlite" => Ok(SqlDialect::Sqlite),
        "postgres" | "postgresql" | "pg" => Ok(SqlDialect::Postgres),
        other => Err(format!(
            "unsupported dialect `{other}` (expected `sqlite` or `postgres`)"
        )),
    }
}

/// Load explicit `--schema-lock` file, or auto-discover `schema.lock` beside `script_path`
/// or in an ancestor directory (stopping at a `.git` root).
fn load_schema_lock_for(
    script_path: &Path,
    explicit: Option<&Path>,
) -> Result<Option<SchemaLockFile>, Diagnostic> {
    let chosen = match explicit {
        Some(p) => Some(p.to_path_buf()),
        None => {
            let mut found = None;
            let start_dir = script_path.parent().and_then(|d| {
                if d.as_os_str().is_empty() {
                    std::env::current_dir().ok()
                } else {
                    Some(d.to_path_buf())
                }
            });
            if let Some(dir) = start_dir {
                for anc in dir.ancestors() {
                    let candidate = anc.join("schema.lock");
                    if candidate.is_file() {
                        found = Some(candidate);
                        break;
                    }
                    if anc.join(".git").exists() {
                        break;
                    }
                }
            }
            found
        }
    };
    let Some(p) = chosen else {
        return Ok(None);
    };
    let src = fs::read_to_string(&p).map_err(|e| {
        Diagnostic::error(
            DiagCode::IoError,
            format!("cannot read schema.lock `{}`: {e}", p.display()),
        )
    })?;
    parse_schema_lock(&src).map(Some).map_err(|e| {
        Diagnostic::error(
            DiagCode::SchemaError,
            format!("invalid schema.lock `{}`: {e}", p.display()),
        )
    })
}

/// Load explicit `--policy` file, or auto-discover a sibling `dana.policy` beside `script_path`.
fn load_policy_for(
    script_path: &Path,
    explicit: Option<&Path>,
    sm: &mut SourceMap,
) -> Result<Option<Policy>, Diagnostic> {
    let chosen = match explicit {
        Some(p) => Some(p.to_path_buf()),
        None => script_path
            .parent()
            .map(|dir| dir.join("dana.policy"))
            .filter(|p| p.is_file()),
    };
    let Some(p) = chosen else {
        return Ok(None);
    };
    let src = fs::read_to_string(&p).map_err(|e| {
        Diagnostic::error(
            DiagCode::IoError,
            format!("cannot read policy `{}`: {e}", p.display()),
        )
    })?;
    let fid = sm.add_file(p.display().to_string(), src.clone());
    parse_policy(fid, &src).map(Some)
}

/// Load explicit `--policy` file, or auto-discover `dana.policy` in `start_dir` or an ancestor
/// directory (stopping at a `.git` root).
fn load_policy_from_dir_or_ancestors(
    start_dir: &Path,
    explicit: Option<&Path>,
    sm: &mut SourceMap,
) -> Result<Option<Policy>, Diagnostic> {
    let chosen = match explicit {
        Some(p) => Some(p.to_path_buf()),
        None => {
            let mut found = None;
            for anc in start_dir.ancestors() {
                let candidate = anc.join("dana.policy");
                if candidate.is_file() {
                    found = Some(candidate);
                    break;
                }
                if anc.join(".git").exists() {
                    break;
                }
            }
            found
        }
    };
    let Some(p) = chosen else {
        return Ok(None);
    };
    let src = fs::read_to_string(&p).map_err(|e| {
        Diagnostic::error(
            DiagCode::IoError,
            format!("cannot read policy `{}`: {e}", p.display()),
        )
    })?;
    let fid = sm.add_file(p.display().to_string(), src.clone());
    parse_policy(fid, &src).map(Some)
}

fn expand_dana_paths(inputs: &[PathBuf]) -> Result<Vec<PathBuf>, String> {
    let mut out = Vec::new();
    for p in inputs {
        if p.is_dir() {
            let entries =
                fs::read_dir(p).map_err(|e| format!("cannot read dir `{}`: {e}", p.display()))?;
            let mut sub = Vec::new();
            for entry in entries.flatten() {
                let ep = entry.path();
                if ep.is_file() && ep.extension().and_then(|s| s.to_str()) == Some("dana") {
                    sub.push(ep);
                }
            }
            sub.sort();
            out.extend(sub);
        } else {
            out.push(p.clone());
        }
    }
    Ok(out)
}
