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
use dana::vm::{VmConfig, run_core_program_vm, run_program_tests_vm};

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
    let vm_default = VmConfig::default();
    let vm_par_low = VmConfig {
        batch_size: 4,
        parallel_threshold_rows: 4,
        max_threads: Some(4),
        optimize: true,
        ..VmConfig::default()
    };
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

        let oracle_outcomes = run_program_tests(&lowered.exec, None, &cfg);
        let vm_def_outcomes = run_program_tests_vm(&lowered.exec, None, &cfg, &vm_default);
        let vm_par_outcomes = run_program_tests_vm(&lowered.exec, None, &cfg, &vm_par_low);

        assert!(
            !oracle_outcomes.is_empty(),
            "expected at least 1 test/example in {}",
            path.display()
        );
        assert_eq!(
            oracle_outcomes.len(),
            vm_def_outcomes.len(),
            "oracle vs vm(default) test count mismatch in {}",
            path.display()
        );
        assert_eq!(
            oracle_outcomes.len(),
            vm_par_outcomes.len(),
            "oracle vs vm(par_low) test count mismatch in {}",
            path.display()
        );
        for ((o, vd), vp) in oracle_outcomes
            .iter()
            .zip(&vm_def_outcomes)
            .zip(&vm_par_outcomes)
        {
            total_tests += 1;
            assert!(
                o.passed,
                "oracle test `{}` in {} failed: {:?}",
                o.name,
                path.display(),
                o.message
            );
            assert!(
                vd.passed,
                "vm(default) test `{}` in {} failed: {:?}",
                vd.name,
                path.display(),
                vd.message
            );
            assert!(
                vp.passed,
                "vm(par_low) test `{}` in {} failed: {:?}",
                vp.name,
                path.display(),
                vp.message
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
        (
            "guarded_return_laundering_rejected",
            r#"
module GuardedReturnLeak

schema S
  id: Int [pii]
end

fn leak(t: Table(S)) : Int
  return 1 if t.first!.id > 5
  0
end
"#,
            DiagCode::PrivacyError,
        ),
        (
            "guarded_return_inferred_signature_tainted",
            r##"
module GuardedReturnInferred

schema S
  id: Int [pii]
end

fn f(t: Table(S))
  return 1 if t.first!.id > 5
  0
end

fn main(t: Table(S), console: Console) : Int
  console.print("#{f(t)}")
  0
end
"##,
            DiagCode::PrivacyError,
        ),
        (
            "guarded_return_post_statement_pc_leak_rejected",
            r#"
module GuardedReturnPostPc

schema S
  id: Int [pii]
end

fn leak(t: Table(S), console: Console) : Int [pii]
  return 1 if t.first!.id > 5
  console.print("small")
  0
end
"#,
            DiagCode::PrivacyError,
        ),
        (
            "if_early_return_post_statement_pc_leak_rejected",
            r#"
module IfEarlyReturnPostPc

schema S
  id: Int [pii]
end

fn leak(t: Table(S), console: Console) : Int [pii]
  if t.first!.id > 5
    return 1
  end
  console.print("small")
  0
end
"#,
            DiagCode::PrivacyError,
        ),
        (
            "guarded_break_full_value_leak_rejected",
            r#"
module GuardedBreakLeak

schema S
  id: Int [pii]
end

fn leak(t: Table(S)) : Int
  var n = 0
  for i in [40, 41, 42, 43]
    n = i
    break if i == t.first!.id
  end
  n
end
"#,
            DiagCode::PrivacyError,
        ),
        (
            "guarded_continue_leak_rejected",
            r#"
module GuardedContinueLeak

schema S
  id: Int [pii]
end

fn leak(t: Table(S)) : Int
  var n = 0
  for i in [1, 2, 3]
    continue if i == t.first!.id
    n = n + i
  end
  n
end
"#,
            DiagCode::PrivacyError,
        ),
        (
            "or_return_post_statement_pc_leak_rejected",
            r#"
module OrReturnLeak

fn leak(x: Int? [pii], console: Console) : Int [pii]
  _ = x.or_return(0)
  console.print("was some")
  1
end
"#,
            DiagCode::PrivacyError,
        ),
        (
            "if_block_var_assign_implicit_leak_rejected",
            r##"
module IfAssignLeak

schema S
  id: Int [pii]
end

fn leak(t: Table(S), console: Console) : Int
  var leaked = 0
  if t.first!.id > 5
    leaked = 1
  end
  console.print("#{leaked}")
  0
end
"##,
            DiagCode::PrivacyError,
        ),
        (
            "if_else_block_var_assign_implicit_leak_rejected",
            r##"
module IfElseAssignLeak

schema S
  id: Int [pii]
end

fn leak(t: Table(S), console: Console) : Int
  var leaked = 0
  if t.first!.id > 5
    _ = 0
  else
    leaked = 1
  end
  console.print("#{leaked}")
  0
end
"##,
            DiagCode::PrivacyError,
        ),
        (
            "case_block_var_assign_implicit_leak_rejected",
            r##"
module CaseAssignLeak

schema S
  id: Int [pii]
end

fn leak(t: Table(S), console: Console) : Int
  var leaked = 0
  case t.first!.id
    1:
      leaked = 1
    _:
      leaked = 2
  end
  console.print("#{leaked}")
  0
end
"##,
            DiagCode::PrivacyError,
        ),
        (
            "loop_cross_iteration_fixpoint_leak_rejected",
            r##"
module LoopFixpointLeak

schema S
  id: Int [pii]
end

fn leak(t: Table(S), console: Console) : Int
  var a = 0
  var b = 0
  var c = 0
  for _ in [1, 2, 3]
    c = b
    b = a
    a = t.first!.id
  end
  console.print("#{c}")
  0
end
"##,
            DiagCode::PrivacyError,
        ),
        (
            "while_indirect_condition_taint_fixpoint_rejected",
            r#"
module WhileIndirectLeak

fn leak(secret: Bool [pii], console: Console) : Int
  var flag = true
  while flag
    console.print("tick")
    flag = secret
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

#[test]
fn mutable_var_semantics_across_loops_ifs_and_cases() -> Result<(), String> {
    let src = r#"
module VarSemantics

fn sum_for() : Int
  var s = 0
  for i in [1, 2, 3]
    s = s + i
  end
  s
end

fn count_while() : Int
  var n = 0
  while n < 10
    n = n + 1
  end
  n
end

fn if_mut(c: Bool) : Int
  var x = 0
  if c
    x = 1
  end
  x
end

fn if_else_mut(c: Bool) : Int
  var x = 0
  if c
    x = 1
  else
    x = 2
  end
  x
end

fn if_elif_mut(k: Int) : Int
  var x = 0
  if k == 1
    x = 10
  else if k == 2
    x = 20
  else
    x = 30
  end
  x
end

fn nested_if_mut(a: Bool, b: Bool) : Int
  var x = 0
  if a
    if b
      x = 42
    end
  end
  x
end

fn cont_for() : Int
  var s = 0
  for i in [1, 2, 3, 4]
    continue if i == 2
    s = s + i
  end
  s
end

fn brk_while() : Int
  var n = 0
  while true
    break if n == 4
    n = n + 1
  end
  n
end

fn local_var_with_break() : Int
  var z = 0
  for i in [1, 2, 3, 4]
    var a = 999
    z = z + i
    break if i == 3
  end
  z
end

fn paginate_sim() : Int
  var pages = []
  var page = 1
  while true
    pages = pages.append(page * 10)
    break if page >= 3
    page = page + 1
  end
  var total = 0
  for p in pages
    total = total + p
  end
  total + page
end

fn case_mut(k: Int) : Int
  var x = 0
  case k
    1:
      x = 11
    2:
      x = 22
    _:
      x = 33
  end
  x
end

test "all var mutation paths execute accurately"
  assert sum_for() == 6
  assert count_while() == 10
  assert if_mut(true) == 1
  assert if_mut(false) == 0
  assert if_else_mut(true) == 1
  assert if_else_mut(false) == 2
  assert if_elif_mut(1) == 10
  assert if_elif_mut(2) == 20
  assert if_elif_mut(9) == 30
  assert nested_if_mut(true, true) == 42
  assert nested_if_mut(true, false) == 0
  assert cont_for() == 8
  assert brk_while() == 4
  assert local_var_with_break() == 6
  assert paginate_sim() == 63
  assert case_mut(1) == 11
  assert case_mut(2) == 22
  assert case_mut(9) == 33

  # Also exercise loops & if-mutations directly inside `test` blocks.
  var local_s = 0
  for i in [10, 20, 30]
    local_s = local_s + i
  end
  assert local_s == 60
  if true
    local_s = local_s + 5
  end
  assert local_s == 65
end
"#;
    let mut sm = SourceMap::new();
    let fid = sm.add_file("var_sem.dana", src);
    let m = parse_module(fid, src)
        .map_err(|d| format!("parse failed:\n{}", render_diagnostic(&d, &sm)))?;
    let checked = check_module(fid, m, None, &sm).map_err(|ds| {
        ds.iter()
            .map(|d| render_diagnostic(d, &sm))
            .collect::<String>()
    })?;
    let lowered = lower_program(checked)
        .map_err(|d| format!("lower failed:\n{}", render_diagnostic(&d, &sm)))?;
    let outcomes = run_program_tests(&lowered.exec, None, &RunConfig::default());
    assert_eq!(outcomes.len(), 1);
    assert!(
        outcomes[0].passed,
        "var mutation semantics test failed: {:?}",
        outcomes[0].message
    );
    Ok(())
}

#[test]
fn long_left_associative_chains_never_overflow_stack() -> Result<(), String> {
    // 1. 2,500-term arithmetic chain: parse, format, check, lower, verify Core IR, and execute!
    let terms: String = std::iter::repeat_n("1", 2_500)
        .collect::<Vec<_>>()
        .join(" + ");
    let src = format!(
        "module LongAdd\n\nfn main() : Int\n  {terms}\nend\n\ntest \"add2500\"\n  assert main() == 2500\nend\n"
    );
    let mut sm = SourceMap::new();
    let fid = sm.add_file("long_add.dana", src.clone());
    let m = parse_module(fid, &src).map_err(|d| render_diagnostic(&d, &sm))?;
    let formatted = dana::syntax::format_module(&m);
    assert_eq!(formatted, src);
    let checked = check_module(fid, m, None, &sm).map_err(|ds| {
        ds.iter()
            .map(|d| render_diagnostic(d, &sm))
            .collect::<String>()
    })?;
    let lowered = lower_program(checked).map_err(|d| render_diagnostic(&d, &sm))?;
    let outcomes = run_program_tests(&lowered.exec, None, &RunConfig::default());
    assert_eq!(outcomes.len(), 1);
    assert!(outcomes[0].passed, "{:?}", outcomes[0].message);

    // 2. 5,000-stage generic pipe chain: parse, format, check, lower, and execute!
    let stages = " |> inc()".repeat(5_000);
    let pipe_src = format!(
        "module LongPipe\n\nfn inc(x: Int) : Int\n  x + 1\nend\n\nfn main() : Int\n  0{stages}\nend\n\ntest \"pipe5000\"\n  assert main() == 5000\nend\n"
    );
    let fid2 = sm.add_file("long_pipe.dana", pipe_src.clone());
    let m2 = parse_module(fid2, &pipe_src).map_err(|d| render_diagnostic(&d, &sm))?;
    let _ = dana::syntax::format_module(&m2);
    let checked2 = check_module(fid2, m2, None, &sm).map_err(|ds| {
        ds.iter()
            .map(|d| render_diagnostic(d, &sm))
            .collect::<String>()
    })?;
    let lowered2 = lower_program(checked2).map_err(|d| render_diagnostic(&d, &sm))?;
    let outcomes2 = run_program_tests(&lowered2.exec, None, &RunConfig::default());
    assert_eq!(outcomes2.len(), 1);
    assert!(outcomes2[0].passed, "{:?}", outcomes2[0].message);

    // 3. 2,500-term row expression inside `derive` + 2,500-stage table pipeline!
    let row_terms: String = std::iter::repeat_n("1", 2_500)
        .collect::<Vec<_>>()
        .join(" + ");
    let table_src = format!(
        "module LongRow\n\nfn calc()\n  t = table\n    | x |\n    | 0 |\n  end\n  t |> derive(y: .x + {row_terms})\nend\n\ntest \"row2500\"\n  out = calc()\n  assert out.first!.y == 2500\nend\n"
    );
    let fid3 = sm.add_file("long_row.dana", table_src.clone());
    let m3 = parse_module(fid3, &table_src).map_err(|d| render_diagnostic(&d, &sm))?;
    let checked3 = check_module(fid3, m3, None, &sm).map_err(|ds| {
        ds.iter()
            .map(|d| render_diagnostic(d, &sm))
            .collect::<String>()
    })?;
    let lowered3 = lower_program(checked3).map_err(|d| render_diagnostic(&d, &sm))?;
    let outcomes3 = run_program_tests(&lowered3.exec, None, &RunConfig::default());
    assert_eq!(outcomes3.len(), 1);
    assert!(outcomes3[0].passed, "{:?}", outcomes3[0].message);

    // 4. Deep postfix chains (`append`, `.abs`, `.round(1)`, `()()`, `[1][1]`) and 5,000-arm `else if` chains.
    let append_src = format!(
        "module LongAppend\n\nfn f() : List(Int)\n  xs = [0]{}\n  xs\nend\n",
        ".append(1)".repeat(5_000)
    );
    let fid4 = sm.add_file("long_append.dana", append_src.clone());
    let m4 = parse_module(fid4, &append_src).map_err(|d| render_diagnostic(&d, &sm))?;
    let fmt4 = dana::syntax::format_module(&m4);
    let fid4b = sm.add_file("long_append_fmt.dana", fmt4.clone());
    let m4b = parse_module(fid4b, &fmt4).map_err(|d| render_diagnostic(&d, &sm))?;
    assert_eq!(dana::syntax::format_module(&m4b), fmt4);
    let checked4 = check_module(fid4, m4, None, &sm).map_err(|ds| format!("{ds:?}"))?;
    let _ = lower_program(checked4).map_err(|d| render_diagnostic(&d, &sm))?;

    let abs_src = format!(
        "module LongAbs\n\nfn f(x: Int) : Int\n  x{}\nend\n",
        ".abs".repeat(5_000)
    );
    let fid5 = sm.add_file("long_abs.dana", abs_src.clone());
    let m5 = parse_module(fid5, &abs_src).map_err(|d| render_diagnostic(&d, &sm))?;
    let _ = dana::syntax::format_module(&m5);
    let _ = check_module(fid5, m5, None, &sm).map_err(|ds| format!("{ds:?}"))?;

    let app_src = format!(
        "module LongApp\n\nfn f(x: Int) : Int\n  x{}\nend\n",
        "()".repeat(5_000)
    );
    let fid6 = sm.add_file("long_app.dana", app_src.clone());
    let m6 = parse_module(fid6, &app_src).map_err(|d| render_diagnostic(&d, &sm))?;
    let _ = dana::syntax::format_module(&m6);
    assert!(check_module(fid6, m6, None, &sm).is_err());

    let idx_src = format!(
        "module LongIdx\n\nfn f(m: Map(Int, Int)) : Int\n  m{}\nend\n",
        "[1]".repeat(5_000)
    );
    let fid7 = sm.add_file("long_idx.dana", idx_src.clone());
    let m7 = parse_module(fid7, &idx_src).map_err(|d| render_diagnostic(&d, &sm))?;
    let _ = dana::syntax::format_module(&m7);
    assert!(check_module(fid7, m7, None, &sm).is_err());

    let mut elif_blk =
        String::from("module LongElifBlk\n\nfn f(x: Int) : Int\n  if x == 0\n    0\n");
    for i in 1..5_000 {
        use std::fmt::Write as _;
        let _ = writeln!(elif_blk, "  else if x == {i}\n    {i}");
    }
    elif_blk.push_str("  else\n    5000\n  end\nend\n");
    let fid8 = sm.add_file("long_elif_blk.dana", elif_blk.clone());
    let m8 = parse_module(fid8, &elif_blk).map_err(|d| render_diagnostic(&d, &sm))?;
    let _ = dana::syntax::format_module(&m8);
    let checked8 = check_module(fid8, m8, None, &sm).map_err(|ds| format!("{ds:?}"))?;
    let _ = lower_program(checked8).map_err(|d| render_diagnostic(&d, &sm))?;

    let mut elif_inl = String::from("module LongElifInl\n\nfn f(x: Int) : Int\n  y = if x == 0: 0");
    for i in 1..5_000 {
        use std::fmt::Write as _;
        let _ = write!(elif_inl, " else if x == {i}: {i}");
    }
    elif_inl.push_str(" else: 5000\n  y\nend\n");
    let fid9 = sm.add_file("long_elif_inl.dana", elif_inl.clone());
    let m9 = parse_module(fid9, &elif_inl).map_err(|d| render_diagnostic(&d, &sm))?;
    let _ = dana::syntax::format_module(&m9);
    let checked9 = check_module(fid9, m9, None, &sm).map_err(|ds| format!("{ds:?}"))?;
    let _ = lower_program(checked9).map_err(|d| render_diagnostic(&d, &sm))?;
    Ok(())
}

#[test]
fn impure_calls_short_circuit_and_closures_rejected_in_noncore_modules() -> Result<(), String> {
    let cases: &[(&str, &str, DiagCode)] = &[
        (
            "impure_call_under_if_pc_noncore",
            r#"
module ImpureIf
schema S
  id: Int [pii]
end
fn helper(console: Console) : Unit
  console.print("big")
end
fn leak(t: Table(S), console: Console) : Unit
  var k = 0
  while k < 1
    k = k + 1
  end
  if t.first!.id > 5
    helper(console)
  end
end
"#,
            DiagCode::PrivacyError,
        ),
        (
            "impure_call_after_guarded_return_noncore",
            r#"
module ImpureGret
schema S
  id: Int [pii]
end
fn helper(console: Console) : Unit
  console.print("small")
end
fn leak(t: Table(S), console: Console) : Int
  var k = 0
  while k < 1
    k = k + 1
  end
  return 1 if t.first!.id > 5
  helper(console)
  0
end
"#,
            DiagCode::PrivacyError,
        ),
        (
            "impure_call_after_guarded_break_noncore",
            r#"
module ImpureBrk
schema S
  id: Int [pii]
end
fn helper(console: Console) : Unit
  console.print("hit")
end
fn leak(t: Table(S), console: Console) : Unit
  for i in [1, 2]
    break if t.first!.id == i
    helper(console)
  end
end
"#,
            DiagCode::PrivacyError,
        ),
        (
            "impure_pipe_call_under_pc_noncore",
            r#"
module ImpurePipe
schema S
  id: Int [pii]
end
fn helper(console: Console) : Unit
  console.print("pipe")
end
fn leak(t: Table(S), console: Console) : Unit
  var k = 0
  while k < 1
    k = k + 1
  end
  if t.first!.id > 5
    console |> helper()
  end
end
"#,
            DiagCode::PrivacyError,
        ),
        (
            "impure_call_short_circuit_and_noncore",
            r#"
module ImpureAnd
fn helper(console: Console) : Bool
  console.print("and")
  true
end
fn leak(secret: Bool [pii], console: Console) : Int
  var k = 0
  while k < 1
    k = k + 1
  end
  _ = secret and helper(console)
  0
end
"#,
            DiagCode::PrivacyError,
        ),
        (
            "impure_call_short_circuit_coalesce_noncore",
            r#"
module ImpureCoal
fn helper(console: Console) : Int
  console.print("coal")
  0
end
fn leak(x: Int? [pii], console: Console) : Int
  var k = 0
  while k < 1
    k = k + 1
  end
  _ = x ?? helper(console)
  0
end
"#,
            DiagCode::PrivacyError,
        ),
        (
            "closure_arg_launder",
            r#"
module LamArg
schema S
  id: Int [pii]
end
fn leak(t: Table(S)) : Int
  f = fn(x)
    x
  end
  f(t.first!.id)
end
"#,
            DiagCode::PrivacyError,
        ),
        (
            "closure_pipe_arg_launder",
            r#"
module LamArgPipe
schema S
  id: Int [pii]
end
fn leak(t: Table(S)) : Int
  f = fn(x)
    x
  end
  t.first!.id |> f()
end
"#,
            DiagCode::PrivacyError,
        ),
        (
            "closure_under_sensitive_pc",
            r#"
module LamPc
schema S
  id: Int [pii]
end
fn leak(t: Table(S), console: Console) : Unit
  f = fn(x)
    console.print("hi")
  end
  if t.first!.id > 5
    f(1)
  end
end
"#,
            DiagCode::PrivacyError,
        ),
        (
            "closure_mutable_capture_rejected",
            r#"
module LamMutCap
fn f() : Int
  var leaked = 0
  g = fn(x)
    leaked + x
  end
  g(1)
end
"#,
            DiagCode::PrivacyError,
        ),
        (
            "main_non_capability_param_frontend_error",
            r#"
module BadMain
fn main(k: Int) : Int
  k
end
"#,
            DiagCode::CapabilityError,
        ),
    ];

    for (name, src, expected_code) in cases {
        let mut sm = SourceMap::new();
        let fid = sm.add_file(format!("{name}.dana"), (*src).to_string());
        let m = parse_module(fid, src)
            .map_err(|d| format!("{name} parse error:\n{}", render_diagnostic(&d, &sm)))?;
        match check_module(fid, m, None, &sm) {
            Ok(_) => {
                return Err(format!("case `{name}` unexpectedly passed check_module"));
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
fn core_extractable_control_flow_and_mut_vars_verify_cleanly() -> Result<(), String> {
    let cases: &[(&str, &str)] = &[
        (
            "if_only",
            "module CoreIfOnly\nfn f(k: Int) : Int\n  var x = 0\n  if k == 0\n    x = 7\n  end\n  x\nend\n",
        ),
        (
            "if_else",
            "module CoreIfElse\nfn f(k: Int) : Int\n  var x = 0\n  if k == 0\n    x = 7\n  else\n    x = 9\n  end\n  x\nend\n",
        ),
        (
            "if_else_2var",
            "module CoreIf2Var\nfn f(k: Int) : Int\n  var x = 0\n  var y = 1\n  if k == 0\n    x = 7\n    y = 2\n  else\n    x = 9\n  end\n  x + y\nend\n",
        ),
        (
            "elif_else",
            "module CoreElif\nfn f(k: Int) : Int\n  var x = 0\n  if k == 0\n    x = 1\n  else if k == 1\n    x = 2\n  else\n    x = 3\n  end\n  x\nend\n",
        ),
        (
            "ret_guard",
            "module CoreRetGuard\nfn f(k: Int) : Int\n  return 5 if k == 0\n  0\nend\n",
        ),
        (
            "if_ret",
            "module CoreIfRet\nfn f(k: Int) : Int\n  if k == 0\n    return 5\n  end\n  0\nend\n",
        ),
        (
            "if_pub_mut_secret",
            "module CoreIfAsym\nfn f(k: Int, s: Int [pii]) : Int [pii]\n  var x = 0\n  if k == 0\n    x = s\n  else\n    x = 1\n  end\n  x\nend\n",
        ),
        (
            "if_secret_mut_pub",
            "module CoreIfSecret\nfn f(b: Bool [pii]) : Int [pii]\n  var x = 0\n  if b\n    x = 1\n  end\n  x\nend\n",
        ),
        (
            "elif_mixed_tags",
            "module CoreElifMixed\nfn f(a: Bool, b: Bool [pii]) : Int [pii]\n  var x = 0\n  if a\n    x = 1\n  else if b\n    x = 2\n  end\n  x\nend\n",
        ),
        (
            "gret_secret_mut",
            "module CoreGretSecret\nfn f(k: Int [pii]) : Int [pii]\n  var x = 0\n  return 1 if k == 0\n  x = 2\n  x\nend\n",
        ),
        (
            "case_mut_asym",
            "module CoreCaseAsym\nfn f(o: Int?, s: Int [pii]) : Int [pii]\n  var x = 0\n  case o\n    Some(v):\n      x = s\n    None:\n      x = 1\n  end\n  x\nend\n",
        ),
        (
            "or_return_core",
            "module CoreOrRet\nfn f(x: Int?) : Int\n  v = x.or_return(0)\n  v + 1\nend\n",
        ),
        (
            "try_core",
            "module CoreTry\nfn f(r: Result(Int, Text)) : Result(Int, Text)\n  x = try r\n  Ok(x + 1)\nend\n",
        ),
    ];

    for (name, src) in cases {
        let mut sm = SourceMap::new();
        let fid = sm.add_file(format!("{name}.dana"), (*src).to_string());
        let m = parse_module(fid, src)
            .map_err(|d| format!("{name} parse error:\n{}", render_diagnostic(&d, &sm)))?;
        let checked = check_module(fid, m, None, &sm).map_err(|ds| {
            format!(
                "{name} check error:\n{}",
                ds.iter()
                    .map(|d| render_diagnostic(d, &sm))
                    .collect::<String>()
            )
        })?;
        let lowered = lower_program(checked)
            .map_err(|d| format!("{name} lower error:\n{}", render_diagnostic(&d, &sm)))?;
        let core = lowered
            .verified_core
            .as_ref()
            .ok_or_else(|| format!("{name} expected verified_core extraction"))?;
        dana::core::check_program(core)
            .map_err(|e| format!("{name} core::check_program failed: {e}"))?;
    }
    Ok(())
}

#[test]
fn cli_run_test_and_explain_vm_vs_oracle() -> Result<(), String> {
    let root = repo_root();
    let policy_str = root.join("examples/dana.policy").display().to_string();
    let expenses_str = root.join("examples/expenses.dana").display().to_string();
    let examples_dir_str = root.join("examples").display().to_string();

    // 1. `dana explain --policy examples/dana.policy examples/expenses.dana`
    assert_eq!(
        dana::cli::run_cli(&[
            "explain".to_string(),
            "--policy".to_string(),
            policy_str.clone(),
            expenses_str.clone(),
        ]),
        0,
        "dana explain failed"
    );

    // 2. `dana test` (default VM) and `dana test --oracle` across all examples
    assert_eq!(
        dana::cli::run_cli(&[
            "test".to_string(),
            "--policy".to_string(),
            policy_str.clone(),
            examples_dir_str.clone(),
        ]),
        0,
        "dana test (VM) failed"
    );
    assert_eq!(
        dana::cli::run_cli(&[
            "test".to_string(),
            "--oracle".to_string(),
            "--policy".to_string(),
            policy_str.clone(),
            examples_dir_str,
        ]),
        0,
        "dana test --oracle failed"
    );

    // 3. `dana run` (default VM) and `dana run --oracle` on both clean and quarantined CSVs
    let tmp_dir = std::env::temp_dir().join(format!("dana_cli_e2e_{}", std::process::id()));
    fs::create_dir_all(&tmp_dir).map_err(|e| format!("create tmp dir: {e}"))?;
    let clean_csv = tmp_dir.join("clean.csv");
    let bad_csv = tmp_dir.join("bad.csv");
    fs::write(
        &clean_csv,
        "date,category,amount\n2026-10-01,food,12.50\n2026-10-02,rent,900.00\n",
    )
    .map_err(|e| format!("write clean csv: {e}"))?;
    fs::write(
        &bad_csv,
        "date,category,amount\n2026-10-01,food,12.50\n2026-10-02,food,not_a_num\n",
    )
    .map_err(|e| format!("write bad csv: {e}"))?;

    let clean_str = clean_csv.display().to_string();
    let bad_str = bad_csv.display().to_string();

    let vm_clean = dana::cli::run_cli(&[
        "run".to_string(),
        "--policy".to_string(),
        policy_str.clone(),
        expenses_str.clone(),
        "--".to_string(),
        clean_str.clone(),
    ]);
    let oracle_clean = dana::cli::run_cli(&[
        "run".to_string(),
        "--oracle".to_string(),
        "--policy".to_string(),
        policy_str.clone(),
        expenses_str.clone(),
        "--".to_string(),
        clean_str,
    ]);
    let vm_bad = dana::cli::run_cli(&[
        "run".to_string(),
        "--policy".to_string(),
        policy_str.clone(),
        expenses_str.clone(),
        "--".to_string(),
        bad_str.clone(),
    ]);
    let oracle_bad = dana::cli::run_cli(&[
        "run".to_string(),
        "--oracle".to_string(),
        "--policy".to_string(),
        policy_str,
        expenses_str,
        "--".to_string(),
        bad_str,
    ]);
    let _ = fs::remove_dir_all(&tmp_dir);

    assert_eq!(vm_clean, 0, "dana run clean CSV expected exit 0");
    assert_eq!(
        oracle_clean, 0,
        "dana run --oracle clean CSV expected exit 0"
    );
    assert_eq!(vm_bad, 1, "dana run quarantined CSV expected exit 1");
    assert_eq!(
        oracle_bad, 1,
        "dana run --oracle quarantined CSV expected exit 1"
    );
    Ok(())
}

#[test]
fn pure_core_rename_verified_core_oracle_and_vm_parity() -> Result<(), String> {
    let src = r#"
module PureRename

schema RawMetric
  old_col: Text
  qty: Int
end

fn transform(t: Table(RawMetric)) : Table(new_col: Text, total: Int)
  t
    |> rename(new_col: .old_col)
    |> where(.qty > 0)
    |> group_by(.new_col)
    |> summarize(total: sum(.qty))
    |> sort_by(.new_col)
end

fn main(console: Console) : Int
  sample = table
    | old_col | qty |
    | "b"     | 10  |
    | "a"     | 25  |
    | "b"     | 0   |
    | "a"     | 5   |
  end
  out = transform(sample)
  console.print_table(out)
  0
end
"#;
    let mut sm = SourceMap::new();
    let fid = sm.add_file("pure_rename.dana", src);
    let m = parse_module(fid, src)
        .map_err(|d| format!("parse error:\n{}", render_diagnostic(&d, &sm)))?;
    let checked = check_module(fid, m, None, &sm).map_err(|ds| {
        ds.iter()
            .map(|d| render_diagnostic(d, &sm))
            .collect::<String>()
    })?;
    let lowered = lower_program(checked)
        .map_err(|d| format!("lower error:\n{}", render_diagnostic(&d, &sm)))?;
    let core_prog = lowered.verified_core.as_ref().ok_or_else(|| {
        "expected rename(new_col: .old_col) program to extract verified_core".to_string()
    })?;

    dana::core::check_program(core_prog).map_err(|e| format!("core::check_program failed: {e}"))?;

    let oracle_rep = dana::oracle::run_program(50_000, core_prog, dana::oracle::World::default())
        .map_err(|e| format!("oracle run: {e:?}"))?;
    let vm_su = run_core_program_vm(
        50_000,
        core_prog,
        dana::oracle::World::default(),
        &VmConfig::sequential_unoptimized(),
    )
    .map_err(|e| format!("vm seq unopt: {e:?}"))?;
    let vm_so = run_core_program_vm(
        50_000,
        core_prog,
        dana::oracle::World::default(),
        &VmConfig::sequential_optimized(),
    )
    .map_err(|e| format!("vm seq opt: {e:?}"))?;
    let vm_po = run_core_program_vm(
        50_000,
        core_prog,
        dana::oracle::World::default(),
        &VmConfig {
            batch_size: 2,
            parallel_threshold_rows: 2,
            max_threads: Some(2),
            optimize: true,
            ..VmConfig::parallel_optimized(2, 2)
        },
    )
    .map_err(|e| format!("vm par opt: {e:?}"))?;

    assert_eq!(oracle_rep.status, dana::oracle::ExitStatus::Ok);
    let s_o = dana::core::print_report(&oracle_rep);
    assert!(s_o.contains("new_col"), "expected renamed header in {s_o}");
    assert_eq!(s_o, dana::core::print_report(&vm_su));
    assert_eq!(s_o, dana::core::print_report(&vm_so));
    assert_eq!(s_o, dana::core::print_report(&vm_po));
    Ok(())
}
