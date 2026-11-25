#![forbid(unsafe_code)]

//! Dana v0.6 verification suite (Slices 6.1 & 6.2):
//! - `.ceil`, `.floor`, `.trunc`, `.to_int` on `Float` & `Decimal` (scalar, row, Oracle/VM/SQL, traps)
//! - `.round([n], [mode: :half_away | :half_even])` and `.round_to(step, [mode:])` (banker's ties, privacy bucket clearance)
//! - General post-aggregate expressions inside `summarize(...)` + `SuppressSmallGroups` (`:drop`/`:mask`, SQL pushdown, negative privacy probes)
//! - CLI `--version` / `-V`
//! - All-`none` `table` literal unification with `T?` schemas (and rejection of non-optional `T`)
//! - Multiline `if cond:\n  ...\nelse if ...:\n  ...\nelse:\n  ...` expressions
//! - CSV `coerce_integral_floats: Bool` & `on_bad_rows: :quarantine | :error` (Oracle/VM parity & privacy-safe errors)
//! - Unused non-underscore `bad_rows` `Severity::Warning` (typechecker & CLI `dana check`)
//! - Audited `coarsen(.col, allow: [...], other: "...")` (Oracle/VM/SQLite/PG pushdown, `explain`, `[ferpa]` clearance, negative probes)
//! - CLI `--oracle-steps N` step-budget flag & `OutsideBoundary` hint

use std::collections::HashMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};

use dana::base::{DiagCode, Severity, SourceMap};
use dana::check::check_module;
use dana::core::syntax::BugKind;
use dana::db::{SqlDialect, SqlParam, open_connection};
use dana::plan::{SplitPlan, split_exec_plan_pushdown};
use dana::runtime::{RunConfig, RunResult, run_exec_program};
use dana::syntax::parse_module;
use dana::vm::{VmConfig, run_exec_program_vm};

type TestResult<T = ()> = Result<T, Box<dyn std::error::Error>>;

static TMP_COUNTER: AtomicU64 = AtomicU64::new(0);

struct TempDir {
    path: PathBuf,
}

impl TempDir {
    fn new(prefix: &str) -> TestResult<Self> {
        let id = TMP_COUNTER.fetch_add(1, Ordering::Relaxed);
        let pid = std::process::id();
        let path = std::env::temp_dir().join(format!("dana_v06_{prefix}_{pid}_{id}"));
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

fn find_first_plan(expr: &dana::runtime::ir::ExecExpr) -> Option<&dana::runtime::ir::ExecPlan> {
    let mut stack = vec![expr];
    while let Some(cur) = stack.pop() {
        match cur {
            dana::runtime::ir::ExecExpr::Rel(p) => return Some(p.as_ref()),
            dana::runtime::ir::ExecExpr::LetE { bound, body, .. } => {
                stack.push(body);
                stack.push(bound);
            }
            dana::runtime::ir::ExecExpr::IfE {
                cond,
                then_br,
                else_br,
            } => {
                stack.push(else_br);
                stack.push(then_br);
                stack.push(cond);
            }
            dana::runtime::ir::ExecExpr::Prim { args, .. }
            | dana::runtime::ir::ExecExpr::Host { args, .. }
            | dana::runtime::ir::ExecExpr::Call { args, .. } => {
                stack.extend(args.iter());
            }
            _ => {}
        }
    }
    None
}

fn sqlite_uri(db_path: &Path) -> String {
    format!("sqlite://{}", db_path.display())
}

fn check_src(src: &str) -> TestResult<dana::check::CheckedProgram> {
    let mut sm = SourceMap::new();
    let fid = sm.add_file("test_v06.dana", src.to_string());
    let m = parse_module(fid, src).map_err(|d| format!("parse error: {d:?}"))?;
    check_module(fid, m, None, &sm).map_err(|ds| format!("check error: {ds:?}").into())
}

fn check_src_diags(src: &str) -> Result<Vec<dana::base::Diagnostic>, Box<dyn std::error::Error>> {
    let mut sm = SourceMap::new();
    let fid = sm.add_file("neg_v06.dana", src.to_string());
    let m = parse_module(fid, src).map_err(|d| format!("parse error: {d:?}"))?;
    match check_module(fid, m, None, &sm) {
        Ok(_) => Err("expected compile diagnostic, succeeded unexpectedly".into()),
        Err(ds) => Ok(ds),
    }
}

fn assert_oracle_vm_parity(src: &str, db_uri: Option<(&str, &str)>) -> TestResult<Vec<String>> {
    let checked = check_src(src)?;
    let mut db_bindings = HashMap::new();
    if let Some((name, uri)) = db_uri {
        db_bindings.insert(name.to_string(), uri.to_string());
    }
    let cfg = RunConfig {
        live_io: true,
        db_bindings,
        ..RunConfig::default()
    };
    let ora = run_exec_program(&checked.exec, &cfg);
    let vm = run_exec_program_vm(&checked.exec, &cfg, &VmConfig::default());
    match (ora, vm) {
        (
            RunResult::Ok {
                exit_code: oc,
                stdout: os,
                stderr: oe,
            },
            RunResult::Ok {
                exit_code: vc,
                stdout: vs,
                stderr: ve,
            },
        ) => {
            assert_eq!(oc, vc, "exit code mismatch oracle={oc} vm={vc}");
            assert_eq!(os, vs, "stdout mismatch\noracle={os:?}\nvm={vs:?}");
            assert_eq!(oe, ve, "stderr mismatch\noracle={oe:?}\nvm={ve:?}");
            Ok(os)
        }
        (RunResult::Stopped { bug: ob, .. }, RunResult::Stopped { bug: vb, .. }) => {
            Err(format!("unexpected engine stop:\noracle={ob:?}\nvm={vb:?}").into())
        }
        (o, v) => Err(format!("engine outcome mismatch:\noracle={o:?}\nvm={v:?}").into()),
    }
}

fn assert_oracle_vm_trap_kind(src: &str, expected: BugKind) -> TestResult {
    let checked = check_src(src)?;
    let cfg = RunConfig {
        live_io: true,
        ..RunConfig::default()
    };
    let ora = run_exec_program(&checked.exec, &cfg);
    let vm = run_exec_program_vm(&checked.exec, &cfg, &VmConfig::default());
    match (ora, vm) {
        (RunResult::Stopped { bug: ob, .. }, RunResult::Stopped { bug: vb, .. }) => {
            assert_eq!(ob.kind, expected, "oracle bug={ob:?}");
            assert_eq!(vb.kind, expected, "vm bug={vb:?}");
            Ok(())
        }
        (o, v) => {
            Err(format!("expected {expected:?} trap in both engines:\nora={o:?}\nvm={v:?}").into())
        }
    }
}

#[test]
fn v06_ceil_floor_trunc_to_int_parity_sql_and_traps() -> TestResult {
    let tmp = TempDir::new("ceil_floor_trunc")?;
    let db_path = tmp.path().join("nums.db");
    let uri = sqlite_uri(&db_path);
    let mut conn = open_connection(&uri)?;
    conn.execute(
        r#"CREATE TABLE "vals" ("id" INTEGER PRIMARY KEY NOT NULL, "f" REAL NOT NULL, "d" TEXT NOT NULL)"#,
        &[],
    )?;
    for (id, f, d) in [
        (1i64, 3.7f64, "3.7"),
        (2, -3.7, "-3.7"),
        (3, 3.0, "3.0"),
        (4, -0.0, "-0.0"),
        (5, -0.2, "-0.2"),
    ] {
        conn.execute(
            r#"INSERT INTO "vals" VALUES (?, ?, ?)"#,
            &[
                SqlParam::Int(id),
                SqlParam::Float(dana::core::syntax::Float64::from_f64(f)),
                SqlParam::Text(d.to_string()),
            ],
        )?;
    }
    drop(conn);

    let src = r##"module CeilFloorTrunc

schema ValRow
  id: Int
  f: Float
  d: Decimal
end

fn main(db: ReadDB(DB), console: Console) : Int
  console.print("#{(3.7.to_float).ceil}:#{(3.7.to_float).floor}:#{(3.7.to_float).trunc}:#{(3.7.to_float).to_int}")
  console.print("#{(-3.7).to_float.ceil}:#{(-3.7).to_float.floor}:#{(-3.7).to_float.trunc}:#{(-3.7).to_float.to_int}")
  console.print("#{3.7.ceil}:#{3.7.floor}:#{3.7.trunc}:#{3.7.to_int}|#{(-3.7).ceil}:#{(-3.7).floor}:#{(-3.7).trunc}:#{(-3.7).to_int}")
  console.print("#{(-0.2).ceil()}:#{(-0.2).floor()}:#{(-0.2).trunc()}:#{(-0.2).to_int()}")

  t = db.table(ValRow, from: "vals")
    |> derive(
         fc: .f.ceil,
         ff: .f.floor,
         ft: .f.trunc,
         fi: .f.to_int,
         dc: .d.ceil(),
         df: .d.floor(),
         dt: .d.trunc(),
         di: .d.to_int()
       )
    |> sort_by(.id)
  console.print_table(t)
  0
end
"##;
    let out = assert_oracle_vm_parity(src, Some(("DB", &uri)))?;
    assert_eq!(out[0], "4:3:3:3");
    assert_eq!(out[1], "-3:-4:-3:-3");
    assert_eq!(out[2], "4:3:3:3|-3:-4:-3:-3");
    assert_eq!(out[3], "0:-1:0:0");
    let joined = out.join("\n");
    assert!(joined.contains("| 1  | 3.7  | 3.7  | 4  | 3  | 3  | 3  | 4  | 3  | 3  | 3  |"));
    assert!(joined.contains("| 2  | -3.7 | -3.7 | -3 | -4 | -3 | -3 | -3 | -4 | -3 | -3 |"));

    // Verify SQLite pushdown breaks safely at local VM boundary for Float/Decimal int conversions.
    let checked = check_src(src)?;
    let main_fn = checked.exec.find_fun("main").ok_or("missing main")?;
    let p = find_first_plan(&main_fn.body).ok_or("missing ExecPlan")?;
    let plan = dana::plan::explain_exec_plan_with_pushdown(
        p,
        &checked.exec,
        "DB",
        SqlDialect::Sqlite,
        None,
    );
    assert!(plan.contains("[LOCAL VM SUFFIX]"), "plan=\n{plan}");

    // Domain/Overflow traps on non-finite Float and out-of-i64 Float/Decimal.
    let nan_trap = r#"module NanTrap
fn main() : Int
  b = 1000000000000000.0.to_float
  b2 = b * b
  b4 = b2 * b2
  b8 = b4 * b4
  inf = b8 * b8 * b8
  nan = inf - inf
  nan.ceil
end
"#;
    assert_oracle_vm_trap_kind(nan_trap, BugKind::OutsideBoundary)?;

    let float_ovf = r#"module FloatOvf
fn main() : Int
  b = 1000000000000000.0.to_float
  big = b * b
  big.to_int
end
"#;
    assert_oracle_vm_trap_kind(float_ovf, BugKind::IntOverflow)?;

    let dec_ovf = r#"module DecOvf
fn main() : Int
  d = 100000000000000000000.0
  d.floor
end
"#;
    assert_oracle_vm_trap_kind(dec_ovf, BugKind::IntOverflow)?;

    Ok(())
}

#[test]
fn v06_round_and_round_to_bankers_modes_and_privacy() -> TestResult {
    let src = r##"module RoundModes

fn main(console: Console) : Int
  # Float banker's ties vs half_away
  f05 = 0.5.to_float
  f15 = 1.5.to_float
  f25 = 2.5.to_float
  fn15 = (-1.5).to_float
  fn25 = (-2.5).to_float
  console.print("#{f05.round(mode: :half_even)}:#{f15.round(mode: :half_even)}:#{f25.round(mode: :half_even)}:#{fn15.round(mode: :half_even)}:#{fn25.round(mode: :half_even)}")
  console.print("#{f05.round(0, mode: :half_away)}:#{f15.round(0, mode: :half_away)}:#{f25.round(0, mode: :half_away)}:#{fn15.round(mode: :half_away)}:#{fn25.round(mode: :half_away)}")

  # Decimal exact base-10 banker's ties
  console.print("#{0.5.round(mode: :half_even)}:#{1.5.round(mode: :half_even)}:#{2.5.round(mode: :half_even)}")
  console.print("#{2.675.round(2, mode: :half_even)}:#{2.685.round(2, mode: :half_even)}:#{(-2.685).round(2, mode: :half_even)}")
  console.print("#{2.675.round(2, mode: :half_away)}:#{2.685.round(2, mode: :half_away)}:#{(-2.685).round(2, mode: :half_away)}")

  # Large finite float must stay finite under .round(2)
  b = 1000000000000000.0.to_float
  huge = (b * b) * (b * b) * (b * b) * (b * b)
  console.print("#{huge.round(2)}")

  # Scalar .round_to with half_even & half_away
  console.print("#{0.25.to_float.round_to(0.5, mode: :half_even)}:#{0.75.to_float.round_to(0.5, mode: :half_even)}:#{1.25.to_float.round_to(0.5, mode: :half_even)}:#{1.75.to_float.round_to(0.5, mode: :half_even)}")
  console.print("#{0.25.to_float.round_to(step: 0.5, mode: :half_away)}:#{0.75.to_float.round_to(step: 0.5, mode: :half_away)}")

  # Row expressions + bucketed=true privacy declassification via round_to(mode: :half_even)
  t = table
    | x | d | dept |
    | 0.25 | 2.685 | "a" |
    | 0.75 | 2.675 | "a" |
    | 1.25 | 2.685 | "a" |
    | 1.75 | 2.675 | "a" |
    | 2.25 | 2.685 | "a" |
  end
    |> derive(
         rt_even: .x.to_float.round_to(0.5, mode: :half_even),
         r_even: .d.round(2, mode: :half_even),
         f_even: .x.to_float.round(1, mode: :half_even)
       )
  console.print_table(t)
  0
end
"##;
    let out = assert_oracle_vm_parity(src, None)?;
    assert_eq!(out[0], "0:2:2:-2:-2");
    assert_eq!(out[1], "1:2:3:-2:-3");
    assert_eq!(out[2], "0.0:2.0:2.0");
    assert_eq!(out[3], "2.68:2.68:-2.68");
    assert_eq!(out[4], "2.68:2.69:-2.69");
    assert!(
        out[5].contains("1000") || out[5].contains("1e300") || !out[5].contains("inf"),
        "large float round must stay finite, got {}",
        out[5]
    );
    assert_eq!(out[6], "0:1:1:2");
    assert_eq!(out[7], "0.5:1");

    // Privacy clearance: round_to(step, mode: :half_even) marks col bucketed=true
    let priv_ok = r#"module PrivRoundToEven

tag pii

fn check_release(tbl: Table(uid: Int, salary: Float [pii]), console: Console) : Int
  s = tbl
    |> derive(sal_band: .salary.round_to(0.5, mode: :half_even))
    |> group_by(.sal_band)
    |> summarize(n: count())
    |> suppress_small_groups(min: 5)
  console.print_table(s)
  0
end

fn main(console: Console) : Int
  s = table
    | uid | salary |
    | 1   | 0.25   |
    | 2   | 0.75   |
    | 3   | 1.25   |
    | 4   | 1.75   |
    | 5   | 2.25   |
  end
  check_release(s, console)
end
"#;
    let _ = assert_oracle_vm_parity(priv_ok, None)?;

    // Invalid rounding mode must fail type-checking with TypeError.
    let bad_mode = r#"module BadMode
fn main() : Int
  _x = 1.5.round(mode: :bogus)
  0
end
"#;
    let diags = check_src_diags(bad_mode)?;
    assert!(diags.iter().any(|d| d.code() == DiagCode::TypeError));

    // Step <= 0 trap on round_to(..., mode: :half_even).
    let step_trap = r#"module StepTrap
fn main() : Int
  _x = 1.5.to_float.round_to(0.0, mode: :half_even)
  0
end
"#;
    assert_oracle_vm_trap_kind(step_trap, BugKind::OutsideBoundary)?;
    Ok(())
}

#[test]
fn v06_summarize_post_agg_expressions_sql_masking_and_negative_privacy() -> TestResult {
    let tmp = TempDir::new("summarize_post_agg")?;
    let db_path = tmp.path().join("summary.db");
    let uri = sqlite_uri(&db_path);
    let mut conn = open_connection(&uri)?;
    conn.execute(
        r#"CREATE TABLE "events" ("dept" TEXT NOT NULL, "uid" INTEGER NOT NULL, "hrs" REAL NOT NULL, "ok" INTEGER NOT NULL)"#,
        &[],
    )?;
    // Dept "ops": 6 distinct uids (survives); "eng": 5 distinct uids (complementary masked when sum(small)<5);
    // Dept "hr": 2 distinct uids (<5, primary masked).
    for (dept, uid, hrs, ok) in [
        ("eng", 1i64, 10.0f64, 1i64),
        ("eng", 1, 20.0, 0),
        ("eng", 2, 15.0, 1),
        ("eng", 3, 25.0, 1),
        ("eng", 4, 30.0, 0),
        ("eng", 5, 20.0, 1),
        ("ops", 101, 10.0, 1),
        ("ops", 102, 10.0, 1),
        ("ops", 103, 10.0, 1),
        ("ops", 104, 10.0, 1),
        ("ops", 105, 10.0, 1),
        ("ops", 106, 10.0, 1),
        ("hr", 10, 5.0, 1),
        ("hr", 11, 15.0, 0),
    ] {
        conn.execute(
            r#"INSERT INTO "events" VALUES (?, ?, ?, ?)"#,
            &[
                SqlParam::Text(dept.to_string()),
                SqlParam::Int(uid),
                SqlParam::Float(dana::core::syntax::Float64::from_f64(hrs)),
                SqlParam::Bool(ok != 0),
            ],
        )?;
    }
    drop(conn);

    // 1) Direct SQL pushdown + post-agg arithmetic, conditionals, coalesce, rounding, multi-agg
    let src_push = r#"module PostAggSql

schema Event
  dept: Text
  uid: Int
  hrs: Float
  ok: Bool
end

fn main(db: ReadDB(DB), console: Console) : Int
  summary = db.table(Event, from: "events")
    |> group_by(.dept)
    |> summarize(
         n: count(),
         pct_ok: (count_if(.ok) * 100).to_float / count().to_float,
         avg_hrs: (mean(.hrs) ?? 0.0).round(2, mode: :half_even),
         avg_div: sum(.hrs) / count().to_float,
         band: if count() >= 5:
           "major:" + .dept
         else:
           "minor:" + .dept
       )
    |> sort_by(.dept)
  console.print_table(summary)
  0
end
"#;
    let out_push = assert_oracle_vm_parity(src_push, Some(("DB", &uri)))?;
    let joined_push = out_push.join("\n");
    assert!(joined_push.contains("major:eng"), "got:\n{joined_push}");
    assert!(joined_push.contains("minor:hr"), "got:\n{joined_push}");
    assert!(joined_push.contains("20"), "got:\n{joined_push}");

    // 2) With suppress_small_groups(min: 5, distinct_by: .uid, mode: :mask):
    //    must keep local group_meta across Drop(Derive(Summarize)) AND mask post-derived summary cols!
    let src_suppress = r#"module PostAggSuppressMask

tag pii

schema Event
  dept: Text
  uid: Int
  hrs: Float [pii]
  ok: Bool
end

fn main(db: ReadDB(DB), console: Console) : Int
  masked = db.table(Event, from: "events")
    |> group_by(.dept)
    |> summarize(
         n: count_distinct(.uid),
         total_hrs: sum(.hrs),
         pct: (count() * 100).to_float / 8.0
       )
    |> suppress_small_groups(min: 5, distinct_by: .uid, mode: :mask)
    |> sort_by(.dept)
  console.print_table(masked)
  0
end
"#;
    let out_mask = assert_oracle_vm_parity(src_suppress, Some(("DB", &uri)))?;
    let joined_mask = out_mask.join("\n");
    // "ops" (6 distinct uids) survives with unmasked pct; "hr" (primary <5) and "eng" (complementary smallest survivor) mask ALL summary cols including post-derived `pct`!
    assert!(joined_mask.contains("| ops  | 6"), "got:\n{joined_mask}");
    assert!(
        joined_mask.contains("| hr   | none | none      | none |"),
        "small group's post-derived summary col must be masked to `none`, got:\n{joined_mask}"
    );
    assert!(
        joined_mask.contains("| eng  | none | none      | none |"),
        "complementary suppressed group's post-derived summary col must be masked to `none`, got:\n{joined_mask}"
    );

    // 3) Check SQLite plan pushdown breaks BEFORE SuppressSmallGroups (not stripping GroupMeta!).
    let checked = check_src(src_suppress)?;
    let main_fn = checked.exec.find_fun("main").ok_or("missing main")?;
    let plan = find_first_plan(&main_fn.body).ok_or("missing ExecPlan")?;
    let split = split_exec_plan_pushdown(plan, &checked.exec, "DB", SqlDialect::Sqlite, None);
    assert!(
        matches!(split, SplitPlan::Hybrid { .. }),
        "Drop(Derive(Summarize)) under SuppressSmallGroups must stay Hybrid, not FullyPushed"
    );

    // 4) Negative privacy probe: NonBlending aggregate arithmetic cannot be declassified by suppress_small_groups.
    let neg_pii_med = r#"module NegPiiMed
tag pii
schema Emp
  dept: Text
  salary: Float [pii]
end
fn main(db: ReadDB(DB), console: Console) : Int
  t = db.table(Emp, from: "e")
    |> group_by(.dept)
    |> summarize(n: count(), dbl_med: (median(.salary) ?? 0.0) * 2.0)
    |> suppress_small_groups(min: 5)
  console.print_table(t)
  0
end
"#;
    let diags_med = check_src_diags(neg_pii_med)?;
    assert!(
        diags_med.iter().any(|d| d.code() == DiagCode::PrivacyError),
        "expected PrivacyError for NonBlending post-agg, got: {diags_med:?}"
    );

    // 5) Negative privacy probe: Outer sensitive variable mixed into Blending count() cannot be laundered!
    let neg_outer_launder = r#"module NegOuterLaunder
tag pii
fn main(secret_offset: Float [pii], console: Console) : Int
  t = table
    | dept |
    | "a"  |
    | "a"  |
    | "a"  |
    | "a"  |
    | "a"  |
  end
    |> group_by(.dept)
    |> summarize(leaked: count().to_float + secret_offset)
    |> suppress_small_groups(min: 5)
  console.print_table(t)
  0
end
"#;
    let diags_launder = check_src_diags(neg_outer_launder)?;
    assert!(
        diags_launder
            .iter()
            .any(|d| d.code() == DiagCode::PrivacyError),
        "expected PrivacyError preventing outer tag laundering in summarize, got: {diags_launder:?}"
    );

    // 6) Negative type probes: raw ungrouped col or nested agg inside agg
    let neg_raw_col = r#"module NegRawCol
fn main() : Int
  _t = table
    | d   | v |
    | "a" | 1 |
  end
    |> group_by(.d)
    |> summarize(bad: count() + .v)
  0
end
"#;
    assert!(
        check_src_diags(neg_raw_col)?
            .iter()
            .any(|d| d.code() == DiagCode::TypeError)
    );

    let neg_nested_agg = r#"module NegNestedAgg
fn main() : Int
  _t = table
    | d   | v |
    | "a" | 1 |
  end
    |> group_by(.d)
    |> summarize(bad: sum(count()))
  0
end
"#;
    assert!(
        check_src_diags(neg_nested_agg)?
            .iter()
            .any(|d| d.code() == DiagCode::TypeError)
    );

    Ok(())
}

#[test]
fn v06_cli_version_all_none_tables_and_multiline_if_inline() -> TestResult {
    let bin = env!("CARGO_BIN_EXE_dana");
    let expected = format!("dana v{}", env!("CARGO_PKG_VERSION"));
    for flag in ["--version", "-V"] {
        let out = Command::new(bin).arg(flag).output()?;
        assert_eq!(out.status.code(), Some(0), "{flag} should exit 0");
        let stdout = String::from_utf8(out.stdout)?;
        assert_eq!(stdout.trim(), expected, "{flag} output mismatch");
    }

    // All-`none` table literals unifying with `Float?`, `Int?`, `Date?`, `Text?`
    let none_table_src = r##"module NoneTableUnify

schema MetricOpt
  id: Int
  f: Float?
  i: Int?
  d: Date?
  s: Text?
end

fn accept(t: Table(id: Int, f: Float?, i: Int?, d: Date?, s: Text?)) : Int
  t.count()
end

fn ret_typed() : Table(id: Int, f: Float?, i: Int?, d: Date?, s: Text?)
  untyped = table
    | id | f    | i    | d    | s    |
    | 1  | none | none | none | none |
  end
  untyped
end

fn main(console: Console) : Int
  lit = table
    | id | f    | i    | d    | s    |
    | 1  | none | none | none | none |
  end
  typed = ret_typed()
  console.print("#{accept(lit)}:#{lit == typed}:#{typed == lit}")
  console.print_table(typed)
  0
end
"##;
    let out = assert_oracle_vm_parity(none_table_src, None)?;
    assert_eq!(out[0], "1:true:true");

    // Negative: all-none `table` must NOT unify with non-optional `Float`!
    let neg_non_opt = r#"module NegNonOpt
fn need_float(t: Table(id: Int, f: Float)) : Int
  t.count()
end
fn main() : Int
  lit = table
    | id | f    |
    | 1  | none |
  end
  need_float(lit)
end
"#;
    let diags = check_src_diags(neg_non_opt)?;
    assert!(diags.iter().any(|d| d.code() == DiagCode::TypeError));

    // Multiline `if cond:\n  ...\nelse if ...:\n  ...\nelse:\n  ...` in scalar, derive, summarize
    let multiline_src = r##"module MultilineIfRuntime

fn score_label(x: Int) : Text
  if x > 10:
    if x > 20:
      "very_high"
    else:
      "high"
  else if x > 0:
    "pos"
  else:
    "non_pos"
end

fn main(console: Console) : Int
  t = table
    | dept | x |
    | "a"  | 25 |
    | "a"  | 5  |
    | "b"  | -2 |
  end
    |> derive(
         tag: if .x > 10:
           "big"
         else if .x > 0:
           "mid"
         else:
           "low"
       )
    |> group_by(.dept)
    |> summarize(
         n: count(),
         summary_tier: if count() > 1:
           "multi"
         else:
           "single"
       )
    |> sort_by(.dept)
  console.print("#{score_label(25)}:#{score_label(15)}:#{score_label(3)}:#{score_label(-1)}")
  console.print_table(t)
  0
end
"##;
    let m_out = assert_oracle_vm_parity(multiline_src, None)?;
    assert_eq!(m_out[0], "very_high:high:pos:non_pos");
    let m_joined = m_out.join("\n");
    assert!(m_joined.contains("| a    | 2 | multi"), "got:\n{m_joined}");
    assert!(m_joined.contains("| b    | 1 | single"), "got:\n{m_joined}");

    Ok(())
}

fn assert_oracle_vm_parity_in_dir(src: &str, work_dir: &Path) -> TestResult<Vec<String>> {
    let checked = check_src(src)?;
    let cfg = RunConfig {
        work_dir: Some(work_dir.to_path_buf()),
        live_io: true,
        ..RunConfig::default()
    };
    let ora = run_exec_program(&checked.exec, &cfg);
    let vm = run_exec_program_vm(&checked.exec, &cfg, &VmConfig::default());
    match (ora, vm) {
        (
            RunResult::Ok {
                exit_code: oc,
                stdout: os,
                stderr: oe,
            },
            RunResult::Ok {
                exit_code: vc,
                stdout: vs,
                stderr: ve,
            },
        ) => {
            assert_eq!(oc, vc, "exit code mismatch oracle={oc} vm={vc}");
            assert_eq!(os, vs, "stdout mismatch\noracle={os:?}\nvm={vs:?}");
            assert_eq!(oe, ve, "stderr mismatch\noracle={oe:?}\nvm={ve:?}");
            Ok(os)
        }
        (o, v) => Err(format!("engine outcome mismatch:\noracle={o:?}\nvm={v:?}").into()),
    }
}

#[test]
fn v06_csv_coerce_integral_floats_and_on_bad_rows_error() -> TestResult {
    let tmp = TempDir::new("csv_opts")?;
    let coerce_csv = tmp.path().join("coerce.csv");
    fs::write(
        &coerce_csv,
        "id,opt\n5.0,-42.00\n+0.0,\n5.5,1\n.0,2\n5.,3\n9223372036854775808.0,4\n",
    )?;
    let clean_csv = tmp.path().join("clean.csv");
    fs::write(&clean_csv, "id,secret_val\n1,\"alpha\"\n2.0,\"beta\"\n")?;
    let bad_pii_csv = tmp.path().join("bad_pii.csv");
    fs::write(
        &bad_pii_csv,
        "id,secret_val\n1,\"AliceSafe\"\n\"SECRET_RAW_VAL_999\",\"AliceSensitiveRowLine\"\n",
    )?;

    // 1. coerce_integral_floats: true vs default (false) with Oracle == VM parity
    let src_coerce = r##"module CsvCoerceOpts

schema NumRow
  id: Int
  opt: Int?
end

fn main(files: ReadFiles, console: Console) : Int
  (good_coerced, bad_coerced) = try files.read_csv(
    "coerce.csv",
    as: NumRow,
    coerce_integral_floats: true
  )
  (good_strict, bad_strict) = try files.read_csv("coerce.csv", as: NumRow)
  console.print("coerced=#{good_coerced.count()}:bad=#{bad_coerced.count()}|strict=#{good_strict.count()}:bad=#{bad_strict.count()}")
  console.print_table(good_coerced)
  console.print_table(bad_coerced)
  0
end
"##;
    let out = assert_oracle_vm_parity_in_dir(src_coerce, tmp.path())?;
    assert_eq!(out[0], "coerced=2:bad=4|strict=0:bad=6");
    let joined = out.join("\n");
    assert!(joined.contains("| 5  | -42  |"), "got:\n{joined}");
    assert!(joined.contains("| 0  | none |"), "got:\n{joined}");
    assert!(
        joined.contains("| 4    | id     | BadInt"),
        "got:\n{joined}"
    );
    assert!(
        joined.contains("| 5    | id     | BadInt"),
        "got:\n{joined}"
    );
    assert!(
        joined.contains("| 6    | id     | BadInt"),
        "got:\n{joined}"
    );
    assert!(
        joined.contains("| 7    | id     | BadInt"),
        "got:\n{joined}"
    );

    // 2. on_bad_rows: :error returning Ok(Table) directly on clean data and privacy-safe Err(Text) on malformed rows
    let src_on_err = r##"module CsvOnError

tag pii
tag ferpa

schema SensitiveRow
  id: Int [ferpa]
  secret_val: Text [pii]
end

fn main(files: ReadFiles, console: Console) : Int
  clean_tbl = try files.read_csv(
    "clean.csv",
    as: SensitiveRow,
    on_bad_rows: :error,
    coerce_integral_floats: true
  )
  console.print("clean_rows=#{clean_tbl.count()}")
  case files.read_csv("bad_pii.csv", as: SensitiveRow, on_bad_rows: :error)
    Ok(t): console.print("unexpected_ok=#{t.count()}")
    Error(msg): console.print("err=#{msg}")
  end
  0
end
"##;
    let err_out = assert_oracle_vm_parity_in_dir(src_on_err, tmp.path())?;
    assert_eq!(err_out[0], "clean_rows=2");
    assert!(err_out[1].starts_with("err="), "got: {:?}", err_out);
    assert!(
        err_out[1].contains("bad_pii.csv")
            && err_out[1].contains("1 invalid CSV row(s)")
            && err_out[1].contains("line 3")
            && err_out[1].contains("column `id`")
            && err_out[1].contains("BadInt"),
        "missing expected error details in `{}`",
        err_out[1]
    );
    assert!(
        !err_out[1].contains("SECRET_RAW_VAL_999") && !err_out[1].contains("AliceSensitiveRowLine"),
        "on_bad_rows: :error must not leak sensitive raw_value or raw_line, got `{}`",
        err_out[1]
    );

    // 3. Negative compile-time option probes
    let neg_bad_mode = r##"module NegBadMode
schema R
  x: Int
end
fn main(files: ReadFiles) : Int
  t = try files.read_csv("a.csv", as: R, on_bad_rows: :skip)
  t.count()
end
"##;
    assert!(
        check_src_diags(neg_bad_mode)?
            .iter()
            .any(|d| d.code() == DiagCode::TypeError)
    );

    let neg_non_bool = r##"module NegNonBool
schema R
  x: Int
end
fn main(files: ReadFiles) : Int
  (t, _b) = try files.read_csv("a.csv", as: R, coerce_integral_floats: 1)
  t.count()
end
"##;
    assert!(
        check_src_diags(neg_non_bool)?
            .iter()
            .any(|d| d.code() == DiagCode::TypeError)
    );

    let neg_unknown = r##"module NegUnknownCsvOpt
schema R
  x: Int
end
fn main(files: ReadFiles) : Int
  (t, _b) = try files.read_csv("a.csv", as: R, delimiter: ";")
  t.count()
end
"##;
    assert!(
        check_src_diags(neg_unknown)?
            .iter()
            .any(|d| d.code() == DiagCode::TypeError)
    );

    let neg_jsonl = r##"module NegJsonlOpt
schema R
  x: Int
end
fn main(files: ReadFiles) : Int
  (t, _b) = try files.read_jsonl("a.jsonl", as: R, on_bad_rows: :error)
  t.count()
end
"##;
    assert!(
        check_src_diags(neg_jsonl)?
            .iter()
            .any(|d| d.code() == DiagCode::TypeError)
    );

    let neg_xlsx = r##"module NegXlsxOpt
schema R
  x: Int
end
fn main(files: ReadFiles) : Int
  (t, _b) = try files.read_xlsx("a.xlsx", as: R, coerce_integral_floats: true)
  t.count()
end
"##;
    assert!(
        check_src_diags(neg_xlsx)?
            .iter()
            .any(|d| d.code() == DiagCode::TypeError)
    );

    Ok(())
}

#[test]
fn v06_unused_quarantine_bad_rows_warning_and_cli_check() -> TestResult {
    let src_unused = r##"module UnusedBadRows
schema Item
  id: Int
end
fn main(files: ReadFiles) : Int
  (rows, bad) = try files.read_csv("items.csv", as: Item)
  rows.count()
end
"##;
    let checked_warn = check_src(src_unused)?;
    assert_eq!(checked_warn.warnings.len(), 1);
    assert_eq!(checked_warn.warnings[0].severity(), Severity::Warning);
    assert!(
        checked_warn.warnings[0].message().contains("`bad`")
            && checked_warn.warnings[0].message().contains("`_bad`")
            && checked_warn.warnings[0]
                .message()
                .contains("on_bad_rows: :error")
    );

    // Overwriting `bad` without reading the first quarantine binding still warns once.
    let src_overwrite = r##"module OverwriteBadRows
schema Item
  id: Int
end
fn main(files: ReadFiles, console: Console) : Int
  (r1, bad) = try files.read_csv("a.csv", as: Item)
  (r2, bad) = try files.read_csv("b.csv", as: Item)
  console.print("#{r1.count()}:#{r2.count()}:#{bad.count()}")
  0
end
"##;
    let checked_overwrite = check_src(src_overwrite)?;
    assert_eq!(checked_overwrite.warnings.len(), 1);

    // `_bad`, `_`, inspecting `bad.count()`, and `on_bad_rows: :error` all produce 0 warnings,
    // even inside a `while` loop fixpoint pass.
    let src_clean = r##"module UsedOrIgnoredBadRows
schema Item
  id: Int
end
fn main(files: ReadFiles, console: Console) : Int
  (r1, _bad) = try files.read_csv("a.csv", as: Item)
  (r2, _) = try files.read_csv("b.csv", as: Item)
  (r3, bad_inspected) = try files.read_csv("c.csv", as: Item)
  r4 = try files.read_csv("d.csv", as: Item, on_bad_rows: :error)
  var i = 0
  while i < 1
    (_r5, bad_in_loop) = try files.read_csv("e.csv", as: Item)
    console.print("#{bad_in_loop.count()}")
    i = i + 1
  end
  console.print("#{r1.count()}:#{r2.count()}:#{r3.count()}:#{bad_inspected.count()}:#{r4.count()}")
  0
end
"##;
    let checked_clean = check_src(src_clean)?;
    assert!(
        checked_clean.warnings.is_empty(),
        "unexpected warnings: {:?}",
        checked_clean.warnings
    );

    // Verify `dana check` (text + --json) exits 0 while reporting the warning.
    let tmp = TempDir::new("cli_warn")?;
    let script_path = tmp.path().join("warn_bad.dana");
    fs::write(&script_path, src_unused)?;
    let bin = env!("CARGO_BIN_EXE_dana");

    let text_out = Command::new(bin).arg("check").arg(&script_path).output()?;
    assert_eq!(
        text_out.status.code(),
        Some(0),
        "dana check with only warnings must exit 0"
    );
    let stderr_text = String::from_utf8(text_out.stderr)?;
    assert!(
        stderr_text.contains("warning") && stderr_text.contains("unused quarantine table `bad`"),
        "unexpected stderr:\n{stderr_text}"
    );

    let json_out = Command::new(bin)
        .args(["check", "--json"])
        .arg(&script_path)
        .output()?;
    assert_eq!(
        json_out.status.code(),
        Some(0),
        "dana check --json with only warnings must exit 0"
    );
    let combined_json = format!(
        "{}{}",
        String::from_utf8(json_out.stdout)?,
        String::from_utf8(json_out.stderr)?
    );
    assert!(
        combined_json.contains("\"severity\":\"warning\"")
            && combined_json.contains("unused quarantine table `bad`"),
        "unexpected json output:\n{combined_json}"
    );

    Ok(())
}

#[test]
fn v06_coarsen_parity_pushdown_explain_privacy_and_negative_probes() -> TestResult {
    let tmp = TempDir::new("coarsen")?;
    let db_path = tmp.path().join("coarsen.db");
    let uri = sqlite_uri(&db_path);
    let mut conn = open_connection(&uri)?;
    conn.execute(
        r#"CREATE TABLE "events" ("id" INTEGER PRIMARY KEY NOT NULL, "dept" TEXT, "uid" INTEGER NOT NULL)"#,
        &[],
    )?;
    for (id, dept, uid) in [
        (1i64, Some("eng"), 101i64),
        (2, Some("eng"), 102),
        (3, Some("ops"), 103),
        (4, Some("ops"), 104),
        (5, Some("sales"), 105),
        (6, None, 106),
        (7, Some("marketing"), 107),
        (8, Some("eng"), 108),
        (9, Some("eng"), 109),
        (10, Some("eng"), 110),
        (11, Some("ops"), 111),
        (12, Some("ops"), 112),
        (13, Some("ops"), 113),
        (14, Some("legal"), 114),
        (15, Some("support"), 115),
    ] {
        let p_dept = match dept {
            Some(s) => SqlParam::Text(s.to_string()),
            None => SqlParam::Null,
        };
        conn.execute(
            r#"INSERT INTO "events" VALUES (?, ?, ?)"#,
            &[SqlParam::Int(id), p_dept, SqlParam::Int(uid)],
        )?;
    }
    drop(conn);

    // 1. Text & Text? coarsen (`none` -> "Other"), overwriting existing col, Oracle == VM == SQLite pushdown
    let src_parity = r##"module CoarsenParity

schema EventRow
  id: Int
  dept: Text?
  uid: Int
end

fn main(db: ReadDB(DB), console: Console) : Int
  rows = db.table(EventRow, from: "events")
    |> derive(
         dept_c: coarsen(.dept, allow: ["eng", "ops"], other: "Other"),
         dept: coarsen(.dept, allow: ["eng", "ops"], other: "Other")
       )
    |> sort_by(.id)
  console.print_table(rows)
  0
end
"##;
    let out = assert_oracle_vm_parity(src_parity, Some(("DB", &uri)))?;
    let joined = out.join("\n");
    assert!(joined.contains("| 1  | eng   | 101 | eng    |"));
    assert!(joined.contains("| 3  | ops   | 103 | ops    |"));
    assert!(joined.contains("| 5  | Other | 105 | Other  |"));
    assert!(joined.contains("| 6  | Other | 106 | Other  |"));

    let checked_parity = check_src(src_parity)?;
    let main_fn = checked_parity.exec.find_fun("main").ok_or("missing main")?;
    let plan = find_first_plan(&main_fn.body).ok_or("missing ExecPlan")?;

    let sqlite_split =
        split_exec_plan_pushdown(plan, &checked_parity.exec, "DB", SqlDialect::Sqlite, None);
    match sqlite_split {
        SplitPlan::Hybrid { ref pushdown, .. } => {
            assert!(
                pushdown
                    .pushed_ops
                    .iter()
                    .any(|op| op.starts_with("Derive(")),
                "expected SQLite Derive pushdown for coarsen, got {:?}",
                pushdown.pushed_ops
            );
            assert!(
                pushdown.sql.contains("CASE WHEN") && pushdown.sql.contains("ELSE"),
                "unexpected SQLite coarsen SQL:\n{}",
                pushdown.sql
            );
        }
        other => {
            return Err(format!(
                "expected Hybrid SQLite plan (derive pushed before non-unique sort), got {other:?}"
            )
            .into());
        }
    }

    let src_no_sort = r#"module CoarsenPgPushdown
schema EventRow
  id: Int
  dept: Text?
  uid: Int
end
fn main(db: ReadDB(DB)) : Int
  rows = db.table(EventRow, from: "events")
    |> derive(dept_c: coarsen(.dept, allow: ["eng", "ops"], other: "Other"))
  rows.count()
end
"#;
    let checked_pg = check_src(src_no_sort)?;
    let pg_main = checked_pg.exec.find_fun("main").ok_or("missing main")?;
    let pg_plan = find_first_plan(&pg_main.body).ok_or("missing ExecPlan")?;
    let pg_split =
        split_exec_plan_pushdown(pg_plan, &checked_pg.exec, "DB", SqlDialect::Postgres, None);
    match pg_split {
        SplitPlan::FullyPushed(q) => {
            assert!(
                q.sql.contains("CASE WHEN")
                    && q.sql.contains("COLLATE \"C\"")
                    && q.sql.contains("ELSE")
                    && q.sql.contains("END"),
                "unexpected Postgres coarsen SQL:\n{}",
                q.sql
            );
        }
        other => return Err(format!("expected FullyPushed Postgres SQL, got {other:?}").into()),
    }

    // 2. `[ferpa]` clearance under both `suppress_small_groups` and `suppress_small_cells` + `dana explain`
    let src_ferpa = r##"module CoarsenFerpaClearance

tag ferpa

schema StudentEvent
  id: Int
  dept: Text? [ferpa]
  uid: Int
end

fn main(db: ReadDB(DB), console: Console) : Int
  grouped = db.table(StudentEvent, from: "events")
    |> derive(dept_c: coarsen(.dept, allow: ["eng", "ops"], other: "Other"))
    |> group_by(.dept_c)
    |> summarize(n: count_distinct(.uid))
    |> suppress_small_groups(min: 5, distinct_by: .uid)
    |> sort_by(.dept_c)
  console.print_table(grouped)

  cells = db.table(StudentEvent, from: "events")
    |> derive(dept_c: coarsen(.dept, allow: ["eng", "ops"], other: "Other"))
    |> select(.id, .dept_c)
    |> suppress_small_cells(by: [.dept_c], min: 2)
    |> sort_by(.id)
  console.print_table(cells)
  0
end
"##;
    let ferpa_out = assert_oracle_vm_parity(src_ferpa, Some(("DB", &uri)))?;
    let ferpa_joined = ferpa_out.join("\n");
    assert!(
        ferpa_joined.contains("| Other  | 5 |"),
        "got:\n{ferpa_joined}"
    );
    assert!(
        ferpa_joined.contains("| eng    | 5 |"),
        "got:\n{ferpa_joined}"
    );
    assert!(
        ferpa_joined.contains("| ops    | 5 |"),
        "got:\n{ferpa_joined}"
    );
    assert!(
        ferpa_joined.contains("| 6  | Other  |"),
        "got:\n{ferpa_joined}"
    );

    let ferpa_path = tmp.path().join("coarsen_ferpa.dana");
    fs::write(&ferpa_path, src_ferpa)?;
    let explain_out = Command::new(env!("CARGO_BIN_EXE_dana"))
        .arg("explain")
        .arg(&ferpa_path)
        .output()?;
    assert_eq!(explain_out.status.code(), Some(0));
    let explain_stdout = String::from_utf8(explain_out.stdout)?;
    assert!(
        explain_stdout.contains("COARSEN Derive("),
        "explain missing COARSEN provenance:\n{explain_stdout}"
    );

    // 3. Negative privacy & compile probes
    // Raw uncoarsened [ferpa] column cannot be printed after suppress_small_groups
    let neg_raw_ferpa_db = r##"module NegRawFerpaDb
tag ferpa
schema S
  id: Int
  dept: Text [ferpa]
  uid: Int
end
fn main(db: ReadDB(DB), console: Console) : Int
  t = db.table(S, from: "events")
    |> group_by(.dept)
    |> summarize(n: count_distinct(.uid))
    |> suppress_small_groups(min: 5, distinct_by: .uid)
  console.print_table(t)
  0
end
"##;
    assert!(
        check_src_diags(neg_raw_ferpa_db)?
            .iter()
            .any(|d| d.code() == DiagCode::PrivacyError)
    );

    let neg_non_text = r##"module NegCoarsenInt
schema R
  id: Int
end
fn main() : Int
  t = table
    | id |
    | 1  |
  end
    |> derive(c: coarsen(.id, allow: ["1"], other: "Other"))
  t.count()
end
"##;
    assert!(
        check_src_diags(neg_non_text)?
            .iter()
            .any(|d| d.code() == DiagCode::TypeError)
    );

    let neg_empty_allow = r##"module NegCoarsenEmpty
fn main() : Int
  t = table
    | dept |
    | "a"  |
  end
    |> derive(c: coarsen(.dept, allow: [], other: "Other"))
  t.count()
end
"##;
    assert!(
        check_src_diags(neg_empty_allow)?
            .iter()
            .any(|d| d.code() == DiagCode::TypeError)
    );

    let neg_var_allow = r##"module NegCoarsenVarAllow
fn main() : Int
  x = "a"
  t = table
    | dept |
    | "a"  |
  end
    |> derive(c: coarsen(.dept, allow: [x], other: "Other"))
  t.count()
end
"##;
    assert!(
        check_src_diags(neg_var_allow)?
            .iter()
            .any(|d| d.code() == DiagCode::PrivacyError)
    );

    let neg_var_other = r##"module NegCoarsenVarOther
fn main() : Int
  o = "Other"
  t = table
    | dept |
    | "a"  |
  end
    |> derive(c: coarsen(.dept, allow: ["a"], other: o))
  t.count()
end
"##;
    assert!(
        check_src_diags(neg_var_other)?
            .iter()
            .any(|d| d.code() == DiagCode::PrivacyError)
    );

    let neg_missing_args = r##"module NegCoarsenMissing
fn main() : Int
  t = table
    | dept |
    | "a"  |
  end
    |> derive(c: coarsen(.dept, allow: ["a"]))
  t.count()
end
"##;
    assert!(
        check_src_diags(neg_missing_args)?
            .iter()
            .any(|d| d.code() == DiagCode::TypeError)
    );

    let neg_row_expr = r##"module NegCoarsenRowExpr
fn main() : Int
  t = table
    | dept |
    | "a"  |
  end
    |> where(coarsen(.dept, allow: ["a"], other: "Other") == "a")
  t.count()
end
"##;
    let row_diags = check_src_diags(neg_row_expr)?;
    assert!(
        row_diags
            .iter()
            .any(|d| d.code() == DiagCode::TypeError
                && d.hints().iter().any(|h| h.contains("derive"))),
        "expected derive hint in {row_diags:?}"
    );

    Ok(())
}

#[test]
fn v06_cli_oracle_steps_flag_and_hint() -> TestResult {
    let tmp = TempDir::new("oracle_steps")?;
    let script = tmp.path().join("loop_budget.dana");
    fs::write(
        &script,
        r##"module LoopBudget

fn main(console: Console) : Int
  var i = 0
  var sum = 0
  while i < 50
    sum = sum + i
    i = i + 1
  end
  console.print("sum=#{sum}")
  0
end

test "loop budget test"
  var i = 0
  while i < 50
    i = i + 1
  end
  assert(i == 50)
end
"##,
    )?;
    let bin = env!("CARGO_BIN_EXE_dana");

    // 1. Small budget traps with `--oracle-steps` hint
    let low_run = Command::new(bin)
        .args(["run", "--oracle", "--oracle-steps", "20"])
        .arg(&script)
        .output()?;
    assert_ne!(low_run.status.code(), Some(0));
    let low_err = format!(
        "{}{}",
        String::from_utf8(low_run.stdout)?,
        String::from_utf8(low_run.stderr)?
    );
    assert!(
        low_err.contains("execution step limit exceeded (20 steps)")
            && low_err.contains("--oracle-steps"),
        "expected step limit hint, got:\n{low_err}"
    );

    // 2. Sufficient budget via `--oracle-steps=N` succeeds on both `run` and `test`
    let ok_run = Command::new(bin)
        .args(["run", "--oracle", "--oracle-steps=50000"])
        .arg(&script)
        .output()?;
    assert_eq!(ok_run.status.code(), Some(0));
    assert_eq!(String::from_utf8(ok_run.stdout)?.trim(), "sum=1225");

    let low_test = Command::new(bin)
        .args(["test", "--oracle", "--oracle-steps", "20"])
        .arg(&script)
        .output()?;
    assert_ne!(low_test.status.code(), Some(0));
    let low_test_out = format!(
        "{}{}",
        String::from_utf8(low_test.stdout)?,
        String::from_utf8(low_test.stderr)?
    );
    assert!(
        low_test_out.contains("--oracle-steps"),
        "expected step limit hint in test output:\n{low_test_out}"
    );

    let ok_test = Command::new(bin)
        .args(["test", "--oracle", "--oracle-steps=50000"])
        .arg(&script)
        .output()?;
    assert_eq!(ok_test.status.code(), Some(0));

    // 3. Invalid CLI flag usage exits 2
    for bad_args in [
        vec!["run", "--oracle-steps=0"],
        vec!["run", "--oracle-steps", "abc"],
        vec!["run", "--oracle-steps", "10", "--oracle-steps", "20"],
        vec!["test", "--oracle-steps=0"],
    ] {
        let mut cmd = Command::new(bin);
        cmd.args(&bad_args).arg(&script);
        let out = cmd.output()?;
        assert_eq!(
            out.status.code(),
            Some(2),
            "expected exit 2 for {bad_args:?}, got {:?}",
            out.status.code()
        );
    }

    Ok(())
}
