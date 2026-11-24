//! End-to-end tests for Slice 2A:
//! - `dana check --policy examples/dana.policy` passes on ALL 10 `examples/*.dana`
//! - `dana test --policy examples/dana.policy` passes every `examples` and `test` block across ALL 10 `examples/*.dana`
//! - Negative privacy & policy enforcement tests (unauthorized PII console leak, below-floor suppression,
//!   non-blending median leak under `suppress_small_groups`, policy ceiling violation, spec-only fake isolation)
//! - Live `dana run examples/expenses.dana` on a temporary CSV file with valid + quarantined rows.

use std::fs;
use std::path::PathBuf;

use dana::base::{DiagCode, FileId, SourceMap, render_diagnostic};
use dana::check::{check_module, check_resolved, parse_policy, resolve_path};
use dana::lower::lower_program;
use dana::runtime::{RunConfig, RunResult, run_exec_program, run_program_tests};
use dana::syntax::parse_module;

fn repo_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

#[test]
fn all_ten_examples_check_and_pass_all_tests() -> Result<(), String> {
    let root = repo_root();
    let examples_dir = root.join("examples");
    let policy_path = examples_dir.join("dana.policy");
    let policy_src = fs::read_to_string(&policy_path).map_err(|e| format!("read policy: {e}"))?;

    let mut sm = SourceMap::new();
    let pfid = sm.add_file(policy_path.display().to_string(), policy_src.clone());
    let policy = parse_policy(pfid, &policy_src)
        .map_err(|d| format!("parse dana.policy:\n{}", render_diagnostic(&d, &sm)))?;

    let mut files: Vec<PathBuf> = fs::read_dir(&examples_dir)
        .map_err(|e| format!("read_dir: {e}"))?
        .filter_map(|e| e.ok().map(|de| de.path()))
        .filter(|p| p.extension().and_then(|s| s.to_str()) == Some("dana"))
        .collect();
    files.sort();
    assert_eq!(files.len(), 10, "expected 10 example programs");

    let cfg = RunConfig::default();
    let mut total_tests = 0usize;

    for path in files {
        let resolved = resolve_path(&path, Some(policy.clone()), &mut sm).map_err(|ds| {
            let rendered: String = ds.iter().map(|d| render_diagnostic(d, &sm)).collect();
            format!("resolve {} failed:\n{rendered}", path.display())
        })?;
        let checked = check_resolved(&resolved, &sm).map_err(|ds| {
            let rendered: String = ds.iter().map(|d| render_diagnostic(d, &sm)).collect();
            format!("check {} failed:\n{rendered}", path.display())
        })?;
        let lowered = lower_program(checked).map_err(|d| {
            format!(
                "lower {} failed:\n{}",
                path.display(),
                render_diagnostic(&d, &sm)
            )
        })?;

        let outcomes = run_program_tests(&lowered.exec, None, &cfg);
        assert!(
            !outcomes.is_empty(),
            "expected at least 1 test/example in {}",
            path.display()
        );
        for o in outcomes {
            total_tests += 1;
            assert!(
                o.passed,
                "test `{}` in {} failed: {:?}",
                o.name,
                path.display(),
                o.message
            );
        }
    }
    assert!(
        total_tests >= 12,
        "expected >= 12 tests/examples across 10 programs, ran {total_tests}"
    );
    Ok(())
}

#[test]
fn privacy_violations_are_statically_rejected() -> Result<(), String> {
    let cases: &[(&str, &str, DiagCode)] = &[
        (
            "direct_pii_to_console",
            r#"
module LeakPii

schema Student
  id: Int [pii]
  name: Text [pii]
end

fn main(s: Table(Student), console: Console) : Int
  console.print_table(s)
  0
end
"#,
            DiagCode::PrivacyError,
        ),
        (
            "non_blending_median_still_tagged_after_suppress",
            r#"
module LeakMedian

schema Patient
  id: Int [pii]
  dept: Text
  score: Float [health]
end

fn main(p: Table(Patient), console: Console) : Int
  summary = p
    |> group_by(.dept)
    |> summarize(n: count_distinct(.id), med: median(.score))
    |> suppress_small_groups(min: 5, distinct_by: .id)
  console.print_table(summary)
  0
end
"#,
            DiagCode::PrivacyError,
        ),
        (
            "suppress_below_floor_rejected",
            r#"
module LowK

schema Patient
  id: Int [pii]
  dept: Text
end

fn main(p: Table(Patient), console: Console) : Int
  summary = p
    |> group_by(.dept)
    |> summarize(n: count_distinct(.id))
    |> suppress_small_groups(min: 3, distinct_by: .id)
  console.print_table(summary)
  0
end
"#,
            DiagCode::PrivacyError,
        ),
        (
            "fake_capability_forbidden_outside_spec",
            r#"
module FakeLeak

fn main() : Int
  c = Console.fake()
  c.print("hi")
  0
end
"#,
            DiagCode::CapabilityError,
        ),
        (
            "join_column_collision_without_suffixes",
            r#"
module JoinCollide

schema A
  id: Int
  val: Int
end

schema B
  id: Int
  val: Int
end

fn merge(a: Table(A), b: Table(B))
  a |> join_one(b, on: .id)
end
"#,
            DiagCode::TypeError,
        ),
        (
            "struct_field_pii_laundering_rejected",
            r#"
module LaunderStruct

struct Boxed
  val: Int
end

fn leak(x: Int [pii]) : Boxed
  Boxed(val: x)
end
"#,
            DiagCode::PrivacyError,
        ),
        (
            "return_type_pii_laundering_rejected",
            r#"
module LaunderReturn

fn leak(x: Int [pii]) : Int
  x
end
"#,
            DiagCode::PrivacyError,
        ),
        (
            "implicit_flow_pc_branch_console_leak_rejected",
            r#"
module ImplicitLeak

fn leak(flag: Bool [pii], console: Console) : Int
  if flag
    console.print("secret branch taken")
  end
  0
end
"#,
            DiagCode::PrivacyError,
        ),
    ];

    for (name, src, expected_code) in cases {
        let mut sm = SourceMap::new();
        let fid = sm.add_file(format!("{name}.dana"), (*src).to_string());
        let module = parse_module(fid, src)
            .map_err(|d| format!("{name} parse error:\n{}", render_diagnostic(&d, &sm)))?;
        let res = check_module(fid, module, None, &sm);
        match res {
            Ok(_) => {
                return Err(format!(
                    "case `{name}` unexpectedly passed type/privacy check"
                ));
            }
            Err(diags) => {
                assert!(
                    diags.iter().any(|d| d.code() == *expected_code),
                    "case `{name}` expected {:?}, got {:?}",
                    expected_code,
                    diags
                        .iter()
                        .map(|d| (d.code(), d.message()))
                        .collect::<Vec<_>>()
                );
            }
        }
    }
    Ok(())
}

#[test]
fn live_expenses_run_on_temp_csv() -> Result<(), String> {
    let root = repo_root();
    let exp_path = root.join("examples/expenses.dana");
    let mut sm = SourceMap::new();
    let resolved = resolve_path(&exp_path, None, &mut sm).map_err(|ds| format!("{ds:?}"))?;
    let checked = check_resolved(&resolved, &sm).map_err(|ds| format!("{ds:?}"))?;
    let lowered = lower_program(checked).map_err(|d| format!("{d:?}"))?;

    let tmp_dir = std::env::temp_dir().join(format!("dana_e2e_{}", std::process::id()));
    fs::create_dir_all(&tmp_dir).map_err(|e| e.to_string())?;
    let csv_path = tmp_dir.join("sample.csv");
    fs::write(
        &csv_path,
        "date,category,amount\n2026-10-01,food,12.50\n2026-10-02,food,bad\n2026-10-03,rent,900\n",
    )
    .map_err(|e| e.to_string())?;

    let cfg = RunConfig {
        args: vec![csv_path.display().to_string()],
        live_io: true,
        ..RunConfig::default()
    };
    let res = run_exec_program(&lowered.exec, &cfg);
    let _ = fs::remove_dir_all(&tmp_dir);

    match res {
        RunResult::Ok {
            exit_code,
            stdout,
            stderr,
        } => {
            assert_eq!(
                exit_code, 1,
                "expected exit code 1 with 1 quarantined bad row"
            );
            assert_eq!(stderr.len(), 1);
            assert!(stderr[0].contains("line 3"), "stderr={stderr:?}");
            let out_joined = stdout.join("\n");
            assert!(
                out_joined.contains("rent") && out_joined.contains("900.0"),
                "stdout={out_joined}"
            );
            assert!(
                out_joined.contains("food") && out_joined.contains("12.5"),
                "stdout={out_joined}"
            );
        }
        other => return Err(format!("expected RunResult::Ok, got {other:?}")),
    }
    Ok(())
}

#[test]
fn policy_ceiling_rejects_unauthorized_export() -> Result<(), String> {
    let mut sm = SourceMap::new();
    let p_src = "version 1\nmin_group_size 5\nallow export \"reports/\" tags []\n";
    let pfid = sm.add_file("dana.policy", p_src);
    let policy = parse_policy(pfid, p_src).map_err(|d| format!("{d:?}"))?;

    let src = r#"
module BadExport

fn main(out: WriteFiles("reports/", allows: [pii])) : Int
  0
end
"#;
    let fid = FileId(1);
    let m = parse_module(fid, src).map_err(|d| format!("{d:?}"))?;
    let res = check_module(fid, m, Some(policy), &sm);
    assert!(
        res.is_err(),
        "WriteFiles allows [pii] must be rejected when dana.policy allows []"
    );
    Ok(())
}

#[test]
fn runtime_stop_redacts_tagged_values() -> Result<(), String> {
    let src = r#"
module StopRedacted

schema SecretUser
  id: Int [pii]
  ssn: Text [pii]
end

fn main(console: Console) : Int
  0
end

fn trigger(u: Table(SecretUser)) : Int
  stop u.first!.ssn
  0
end

test "stop redacts pii"
  users = table
    | id | ssn           |
    | 1  | "123-45-6789" |
  end
  trigger(users)
end
"#;
    let mut sm = SourceMap::new();
    let fid = sm.add_file("stop_redacted.dana", src);
    let m = parse_module(fid, src).map_err(|d| format!("{d:?}"))?;
    let checked = check_module(fid, m, None, &sm).map_err(|ds| format!("{ds:?}"))?;
    let lowered = lower_program(checked).map_err(|d| format!("{d:?}"))?;
    let outcomes = run_program_tests(&lowered.exec, None, &RunConfig::default());
    assert_eq!(outcomes.len(), 1);
    assert!(!outcomes[0].passed);
    let msg = outcomes[0].message.as_deref().unwrap_or("");
    assert!(
        msg.contains("[REDACTED:pii]"),
        "expected redacted tag in stop diagnostic, got: {msg}"
    );
    assert!(
        !msg.contains("123-45-6789"),
        "raw PII leaked into stop diagnostic: {msg}"
    );
    Ok(())
}

#[test]
fn mask_complementary_suppresses_smallest_surviving_group() -> Result<(), String> {
    let src = r#"
module MaskTest

schema Visit
  pid: Int [pii]
  dept: Text
end

fn summary(v: Table(Visit))
  v
    |> group_by(.dept)
    |> summarize(n: count_distinct(.pid))
    |> suppress_small_groups(min: 5, distinct_by: .pid, mode: :mask)
    |> sort_by(.dept)
end

test "complementary suppression masks both size-2 and smallest survivor size-5"
  rows = table
    | pid | dept |
    | 1   | "A"  |
    | 2   | "A"  |
    | 3   | "B"  |
    | 4   | "B"  |
    | 5   | "B"  |
    | 6   | "B"  |
    | 7   | "B"  |
    | 8   | "C"  |
    | 9   | "C"  |
    | 10  | "C"  |
    | 11  | "C"  |
    | 12  | "C"  |
    | 13  | "C"  |
  end
  out = summary(rows)
  assert out.count() == 3
  assert out == table
    | dept | n    |
    | "A"  | none |
    | "B"  | none |
    | "C"  | 6    |
  end
end
"#;
    let mut sm = SourceMap::new();
    let fid = sm.add_file("mask_test.dana", src);
    let m = parse_module(fid, src).map_err(|d| format!("{d:?}"))?;
    let checked = check_module(fid, m, None, &sm).map_err(|ds| format!("{ds:?}"))?;
    let lowered = lower_program(checked).map_err(|d| format!("{d:?}"))?;
    let outcomes = run_program_tests(&lowered.exec, None, &RunConfig::default());
    assert_eq!(outcomes.len(), 1);
    assert!(
        outcomes[0].passed,
        "mask_complementary test failed: {:?}",
        outcomes[0].message
    );
    Ok(())
}

#[test]
fn pure_core_v01_program_verifies_and_runs_on_core_oracle() -> Result<(), String> {
    let src = r#"
module PureCore

schema Item
  group_name: Text
  qty: Int
end

fn total_by_group(items: Table(Item)) : Table(group_name: Text, total: Int)
  items
    |> where(.qty > 0)
    |> group_by(.group_name)
    |> summarize(total: sum(.qty))
    |> sort_desc(.total)
end

fn main(console: Console) : Int
  sample = table
    | group_name | qty |
    | "a"        | 10  |
    | "b"        | 25  |
    | "a"        | 5   |
  end
  out = total_by_group(sample)
  console.print_table(out)
  0
end
"#;
    let mut sm = SourceMap::new();
    let fid = sm.add_file("pure_core.dana", src);
    let m = parse_module(fid, src).map_err(|d| format!("{d:?}"))?;
    let checked = check_module(fid, m, None, &sm).map_err(|ds| format!("{ds:?}"))?;
    let lowered = lower_program(checked).map_err(|d| format!("{d:?}"))?;
    let core_prog = lowered
        .verified_core
        .as_ref()
        .ok_or_else(|| "expected pure Core IR v0.1 program to extract verified_core".to_string())?;

    // Verify canonical wire round-trip and Core IR oracle execution.
    let wire = dana::core::print_program(core_prog);
    let reparsed = dana::core::parse_program(&wire).map_err(|e| format!("wire reparse: {e}"))?;
    dana::core::check_program(&reparsed).map_err(|e| format!("core check: {e}"))?;
    let report = dana::oracle::run_program(50_000, &reparsed, dana::oracle::World::default())
        .map_err(|e| format!("oracle run: {e:?}"))?;
    assert_eq!(report.status, dana::oracle::ExitStatus::Ok);
    assert!(!report.stdout.is_empty());
    Ok(())
}

#[test]
fn cli_guide_check_json_and_format_commands() {
    assert_eq!(
        dana::cli::run_cli(&["guide".to_string(), "Privacy".to_string()]),
        0
    );
    assert_eq!(
        dana::cli::run_cli(&[
            "check".to_string(),
            "--policy".to_string(),
            repo_root()
                .join("examples/dana.policy")
                .display()
                .to_string(),
            "--json".to_string(),
            repo_root()
                .join("examples/expenses.dana")
                .display()
                .to_string(),
        ]),
        0
    );
}
