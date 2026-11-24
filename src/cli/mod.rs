//! Zero-crate CLI entry point for the `dana` toolchain binary.
//!
//! Subcommands:
//! - `dana check [--policy PATH] [--json] <FILE...>`
//! - `dana run [--oracle] [--policy PATH] [--allow-export TAGS] [--emit-core] <FILE> [-- ARGS...]`
//! - `dana test [--oracle] [--policy PATH] [--filter SUBSTR] [PATH...]`
//! - `dana format [--check] <PATH...>`
//! - `dana guide [SECTION]`
//! - `dana infer-schema` / `dana fake` (Slice 2B)

use std::fs::{self, File};
use std::io::{self, BufWriter};
use std::path::{Path, PathBuf};

use crate::base::{DiagCode, Diagnostic, SourceMap, render_diagnostic, render_diagnostics_json};
use crate::check::{check_resolved, parse_policy, resolve_path};
use crate::core::syntax::{Policy, TagSet};
use crate::core::text::print_program;
use crate::formats::compress::{AutoEncodeWriter, detect_compression_path};
use crate::formats::fake::{FakeFormat, write_fake_rows};
use crate::formats::infer::{InferFormat, infer_schema_from_file};
use crate::lower::lower_program;
use crate::oracle::cli::parse_comma_tags;
use crate::plan::{explain_exec_plan, optimize_exec_plan};
use crate::runtime::{RunConfig, RunResult, run_exec_program, run_program_tests};
use crate::syntax::{format_module, parse_module};
use crate::vm::{VmConfig, run_exec_program_vm, run_program_tests_vm};

/// Authoritative Dana Language Reference v0.1 embedded for offline `dana guide`.
pub const EMBEDDED_GUIDE: &str = include_str!("../../docs/reference/README.md");

const USAGE: &str = "\
dana — fast, private, database-native data language toolchain (Phase 2)

USAGE:
  dana <COMMAND> [OPTIONS]

COMMANDS:
  check [--policy FILE] [--json] <FILE...>
      Parse, type-check, privacy-check, and verify Dana source file(s).
  run [--oracle] [--policy FILE] [--allow-export TAGS] [--emit-core] <FILE> [-- ARGS...]
      Compile and execute a Dana program's `main` function (vectorized columnar VM by default;
      pass `--oracle` for the reference row-by-row engine).
  test [--oracle] [--policy FILE] [--filter SUBSTR] [PATH...]
      Run all inline `examples` and `test` blocks across file(s) or directory.
  explain [--policy FILE] <FILE>
      Show logical vs. optimized relational plans for every function in a `.dana` module.
  format [--check] <PATH...>
      Format Dana source file(s) canonically with 2-space indentation.
  guide [SECTION]
      Print the embedded Dana Language Reference v0.1 (optionally filtered by section).
  infer-schema <DATA_FILE> [--name Schema] [--sample-rows N] [--format csv|tsv|jsonl]
      Infer a typed Dana schema from CSV/TSV/JSONL (supports .gz and .zst transparently).
  fake <FILE.dana> [--schema Name] [--rows N] [--seed S] [--format csv|tsv|jsonl] [--out PATH]
      Generate deterministic synthetic constraint-satisfying test data.
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
        "guide" => cmd_guide(rest),
        "format" => cmd_format(rest),
        "check" => cmd_check(rest),
        "test" => cmd_test(rest),
        "run" => cmd_run(rest),
        "explain" => cmd_explain(rest),
        "infer-schema" => cmd_infer_schema(rest),
        "fake" => cmd_fake(rest),
        other => {
            eprintln!("dana: unknown command `{other}`\n\n{USAGE}");
            2
        }
    }
}

fn cmd_guide(args: &[String]) -> i32 {
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
        if a == "--check" {
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
            } else if let Err(e) = fs::write(&path, formatted) {
                eprintln!("dana format: cannot write `{}`: {e}", path.display());
                return 2;
            }
        }
    }
    if check_only && any_diff { 1 } else { 0 }
}

fn cmd_check(args: &[String]) -> i32 {
    let mut policy_path: Option<PathBuf> = None;
    let mut json_out = false;
    let mut files = Vec::new();
    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--policy" => {
                i += 1;
                let Some(p) = args.get(i) else {
                    eprintln!("dana check: `--policy` requires a file path");
                    return 2;
                };
                policy_path = Some(PathBuf::from(p));
            }
            "--json" => json_out = true,
            flag if flag.starts_with('-') => {
                eprintln!("dana check: unknown flag `{flag}`");
                return 2;
            }
            path => files.push(PathBuf::from(path)),
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
        match resolve_path(&path, policy, &mut sm) {
            Ok(resolved) => match check_resolved(&resolved, &sm) {
                Ok(checked) => {
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
    if all_diags.is_empty() { 0 } else { 1 }
}

fn cmd_test(args: &[String]) -> i32 {
    let mut use_oracle = false;
    let mut policy_path: Option<PathBuf> = None;
    let mut filter: Option<String> = None;
    let mut paths = Vec::new();
    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--oracle" => use_oracle = true,
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
            flag if flag.starts_with('-') => {
                eprintln!("dana test: unknown flag `{flag}`");
                return 2;
            }
            p => paths.push(PathBuf::from(p)),
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
    let cfg = RunConfig::default();
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

fn cmd_run(args: &[String]) -> i32 {
    let mut use_oracle = false;
    let mut policy_path: Option<PathBuf> = None;
    let mut allow_export = TagSet::empty();
    let mut emit_core = false;
    let mut script_path: Option<PathBuf> = None;
    let mut prog_args = Vec::new();
    let mut i = 0;

    while i < args.len() {
        match args[i].as_str() {
            "--" => {
                prog_args.extend(args[i + 1..].iter().cloned());
                break;
            }
            "--oracle" => use_oracle = true,
            "--emit-core" => emit_core = true,
            "--policy" => {
                i += 1;
                let Some(p) = args.get(i) else {
                    eprintln!("dana run: `--policy` requires a file path");
                    return 2;
                };
                policy_path = Some(PathBuf::from(p));
            }
            "--allow-export" => {
                i += 1;
                let Some(ts) = args.get(i) else {
                    eprintln!("dana run: `--allow-export` requires comma-separated tags");
                    return 2;
                };
                match parse_comma_tags(ts) {
                    Ok(tags) => allow_export = allow_export.union(&tags),
                    Err(e) => {
                        eprintln!("dana run: invalid `--allow-export`: {e}");
                        return 2;
                    }
                }
            }
            flag if flag.starts_with('-') => {
                eprintln!("dana run: unknown flag `{flag}`");
                return 2;
            }
            p if script_path.is_none() => script_path = Some(PathBuf::from(p)),
            other => prog_args.push(other.to_string()),
        }
        i += 1;
    }

    let Some(path) = script_path else {
        eprintln!("dana run: missing `.dana` file path");
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

    if emit_core {
        match &lowered.verified_core {
            Some(cp) => {
                println!("{}", print_program(cp));
                return 0;
            }
            None => {
                eprintln!(
                    "dana run --emit-core: program uses Phase 2 runtime extensions outside Core IR v0.1"
                );
                return 1;
            }
        }
    }

    let cfg = RunConfig {
        args: prog_args,
        allow_export,
        work_dir: None,
        live_io: true,
        ..RunConfig::default()
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

fn collect_exec_plans<'a>(
    expr: &'a crate::runtime::ExecExpr,
    out: &mut Vec<&'a crate::runtime::ExecPlan>,
) {
    use crate::runtime::ExecExpr;
    match expr {
        ExecExpr::Rel(plan) => out.push(plan),
        ExecExpr::LetE { bound, body, .. }
        | ExecExpr::Join {
            rhs: bound, body, ..
        } => {
            collect_exec_plans(bound, out);
            collect_exec_plans(body, out);
        }
        ExecExpr::IfE {
            cond,
            then_br,
            else_br,
        } => {
            collect_exec_plans(cond, out);
            collect_exec_plans(then_br, out);
            collect_exec_plans(else_br, out);
        }
        ExecExpr::CaseE { scrut, arms } => {
            collect_exec_plans(scrut, out);
            for a in arms {
                collect_exec_plans(&a.body, out);
            }
        }
        ExecExpr::ForLoop {
            iter_expr,
            body,
            after,
            ..
        } => {
            collect_exec_plans(iter_expr, out);
            collect_exec_plans(body, out);
            collect_exec_plans(after, out);
        }
        ExecExpr::WhileLoop {
            cond, body, after, ..
        } => {
            collect_exec_plans(cond, out);
            collect_exec_plans(body, out);
            collect_exec_plans(after, out);
        }
        ExecExpr::App { fn_expr, args } => {
            collect_exec_plans(fn_expr, out);
            for a in args {
                collect_exec_plans(a, out);
            }
        }
        ExecExpr::Call { args, .. }
        | ExecExpr::Jump { args, .. }
        | ExecExpr::Tuple(args)
        | ExecExpr::Ctor { args, .. }
        | ExecExpr::Prim { args, .. }
        | ExecExpr::Host { args, .. } => {
            for a in args {
                collect_exec_plans(a, out);
            }
        }
        ExecExpr::Proj { tup: e, .. } | ExecExpr::Assert { cond: e, .. } | ExecExpr::Fail(e) => {
            collect_exec_plans(e, out);
        }
        ExecExpr::Lam { body, .. } => collect_exec_plans(body, out),
        ExecExpr::Stop { detail, .. } => {
            if let Some(d) = detail {
                collect_exec_plans(d, out);
            }
        }
        ExecExpr::Lit(_)
        | ExecExpr::Var(_)
        | ExecExpr::ConstRef(_)
        | ExecExpr::TableLit { .. }
        | ExecExpr::CheckPromise { .. } => {}
    }
}

fn cmd_explain(args: &[String]) -> i32 {
    let mut policy_path: Option<PathBuf> = None;
    let mut script_path: Option<PathBuf> = None;
    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--policy" => {
                i += 1;
                let Some(p) = args.get(i) else {
                    eprintln!("dana explain: `--policy` requires a file path");
                    return 2;
                };
                policy_path = Some(PathBuf::from(p));
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

    let mut found_any = false;
    for f in &lowered.exec.funs {
        let mut plans = Vec::new();
        collect_exec_plans(&f.body, &mut plans);
        if plans.is_empty() {
            continue;
        }
        found_any = true;
        println!("== fn {} ==", f.name);
        for (idx, p) in plans.iter().enumerate() {
            let (opt, stats) = optimize_exec_plan(p, &lowered.exec);
            println!("-- plan #{idx} (logical) --");
            print!("{}", explain_exec_plan(p));
            println!(
                "-- plan #{idx} (optimized: fused={}, pushed={}, pruned={}, dead={}, limits={}) --",
                stats.filters_fused,
                stats.predicates_pushed,
                stats.derive_items_pruned,
                stats.dead_ops_eliminated,
                stats.limits_folded
            );
            print!("{}", explain_exec_plan(&opt));
        }
    }
    if !found_any {
        println!("no relational plans in {}", path.display());
    }
    0
}

fn cmd_infer_schema(args: &[String]) -> i32 {
    let mut data_path: Option<PathBuf> = None;
    let mut schema_name: Option<String> = None;
    let mut sample_rows: usize = 10_000;
    let mut format_override: Option<InferFormat> = None;
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
                    eprintln!("dana infer-schema: `--format` requires csv, tsv, or jsonl");
                    return 2;
                };
                format_override = match raw.to_ascii_lowercase().as_str() {
                    "csv" => Some(InferFormat::Csv),
                    "tsv" => Some(InferFormat::Tsv),
                    "jsonl" | "ndjson" => Some(InferFormat::Jsonl),
                    other => {
                        eprintln!("dana infer-schema: unsupported format `{other}`");
                        return 2;
                    }
                };
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
    match infer_schema_from_file(&path, &name, format_override, sample_rows) {
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

fn default_schema_name_from_path(path: &Path) -> String {
    let raw = path.to_string_lossy();
    let stripped = crate::formats::compress::strip_compression_ext(&raw);
    let stem = Path::new(stripped)
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or("Record");
    let mut out = String::new();
    for part in stem.split(|c: char| !c.is_ascii_alphanumeric()) {
        let mut chars = part.chars();
        if let Some(first) = chars.next() {
            out.push(first.to_ascii_uppercase());
            for ch in chars {
                out.push(ch.to_ascii_lowercase());
            }
        }
    }
    if out.is_empty() || !out.as_bytes()[0].is_ascii_uppercase() {
        "Record".to_string()
    } else {
        out
    }
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
