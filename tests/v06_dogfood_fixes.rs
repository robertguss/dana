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

fn check_src_with_lock(
    src: &str,
    lock: &dana::db::schema_lock::SchemaLockFile,
) -> TestResult<dana::check::CheckedProgram> {
    let mut sm = SourceMap::new();
    let fid = sm.add_file("test_v06_lock.dana", src.to_string());
    let m = parse_module(fid, src).map_err(|d| format!("parse error: {d:?}"))?;
    dana::check::check_module_with_lock(fid, m, None, &sm, Some(lock))
        .map_err(|ds| format!("check error: {ds:?}").into())
}

// ===========================================================================
// Slice 6.3 Tests: SQLite --attach / fallback, TryParseDate pushdown, dedupe_by
// ===========================================================================

#[test]
fn v06_sqlite_attach_and_unattached_schema_table_fallback() -> TestResult {
    assert_eq!(env!("CARGO_PKG_VERSION"), "0.6.4");
    let tmp = TempDir::new("sqlite_attach")?;
    let main_db = tmp.path().join("main.db");
    let populi_db = tmp.path().join("populi.db");
    let canvas_db = tmp.path().join("canvas.db");

    {
        let mut mc = open_connection(&sqlite_uri(&main_db))?;
        mc.execute(
            r#"CREATE TABLE "local_meta" ("k" TEXT PRIMARY KEY NOT NULL, "v" TEXT NOT NULL)"#,
            &[],
        )?;
        mc.execute(r#"INSERT INTO "local_meta" VALUES ('env', 'dogfood')"#, &[])?;
    }
    {
        let mut pc = open_connection(&sqlite_uri(&populi_db))?;
        pc.execute(
            r#"CREATE TABLE "enrollments" ("id" INTEGER PRIMARY KEY NOT NULL, "uid" INTEGER NOT NULL, "cid" INTEGER NOT NULL, "status" TEXT NOT NULL)"#,
            &[],
        )?;
        for (id, uid, cid, st) in [(1i64, 10i64, 100i64, "ENROLLED"), (2, 20, 200, "WITHDRAWN")] {
            pc.execute(
                r#"INSERT INTO "enrollments" VALUES (?, ?, ?, ?)"#,
                &[
                    SqlParam::Int(id),
                    SqlParam::Int(uid),
                    SqlParam::Int(cid),
                    SqlParam::Text(st.to_string()),
                ],
            )?;
        }
    }
    {
        let mut cc = open_connection(&sqlite_uri(&canvas_db))?;
        cc.execute(
            r#"CREATE TABLE "courses" ("cid" INTEGER PRIMARY KEY NOT NULL, "code" TEXT NOT NULL)"#,
            &[],
        )?;
        for (cid, code) in [(100i64, "CS101"), (200, "TH201")] {
            cc.execute(
                r#"INSERT INTO "courses" VALUES (?, ?)"#,
                &[SqlParam::Int(cid), SqlParam::Text(code.to_string())],
            )?;
        }
    }

    // 1. URI `?attach=schema:path&attach=schema=path` + cross-schema join parity & pushdown
    let attach_uri = format!(
        "sqlite://{}?attach=populi:{}&attach=canvas={}",
        main_db.display(),
        populi_db.display(),
        canvas_db.display()
    );
    let join_src = r##"module AttachJoin

schema Enroll
  id: Int
  uid: Int
  cid: Int
  status: Text
end

schema Course
  cid: Int
  code: Text
end

fn main(db: ReadDB(Lake), console: Console) : Int
  joined = db.table(Enroll, from: "populi.enrollments")
    |> join_many_to_one(db.table(Course, from: "canvas.courses"), on: .cid)
    |> group_by(.code)
    |> summarize(n: count())
    |> sort_by(.code)
  console.print_table(joined)
  0
end
"##;
    let uri_out = assert_oracle_vm_parity(join_src, Some(("Lake", &attach_uri)))?;
    let uri_joined = uri_out.join("\n");
    assert!(
        uri_joined.contains("CS101") && uri_joined.contains("TH201"),
        "expected cross-schema attached join output:\n{uri_joined}"
    );

    let join_sq_lock = dana::db::schema_lock::SchemaLockFile {
        dbs: vec![dana::db::schema_lock::LockedDb {
            name: "Lake".to_string(),
            dialect: SqlDialect::Sqlite,
            tables: vec![
                dana::db::schema_lock::LockedTable {
                    name: "populi.enrollments".to_string(),
                    cols: vec![
                        dana::db::schema_lock::LockedCol {
                            name: "id".to_string(),
                            ty: dana::core::syntax::ScalarTy::Int,
                            nullable: false,
                            pk: true,
                            tags: dana::core::syntax::TagSet::empty(),
                        },
                        dana::db::schema_lock::LockedCol {
                            name: "uid".to_string(),
                            ty: dana::core::syntax::ScalarTy::Int,
                            nullable: false,
                            pk: false,
                            tags: dana::core::syntax::TagSet::empty(),
                        },
                        dana::db::schema_lock::LockedCol {
                            name: "cid".to_string(),
                            ty: dana::core::syntax::ScalarTy::Int,
                            nullable: false,
                            pk: false,
                            tags: dana::core::syntax::TagSet::empty(),
                        },
                        dana::db::schema_lock::LockedCol {
                            name: "status".to_string(),
                            ty: dana::core::syntax::ScalarTy::Text,
                            nullable: false,
                            pk: false,
                            tags: dana::core::syntax::TagSet::empty(),
                        },
                    ],
                },
                dana::db::schema_lock::LockedTable {
                    name: "canvas.courses".to_string(),
                    cols: vec![
                        dana::db::schema_lock::LockedCol {
                            name: "cid".to_string(),
                            ty: dana::core::syntax::ScalarTy::Int,
                            nullable: false,
                            pk: true,
                            tags: dana::core::syntax::TagSet::empty(),
                        },
                        dana::db::schema_lock::LockedCol {
                            name: "code".to_string(),
                            ty: dana::core::syntax::ScalarTy::Text,
                            nullable: false,
                            pk: false,
                            tags: dana::core::syntax::TagSet::empty(),
                        },
                    ],
                },
            ],
        }],
        ..dana::db::schema_lock::SchemaLockFile::default()
    };
    let mut join_pg_lock = join_sq_lock.clone();
    join_pg_lock.dbs[0].dialect = SqlDialect::Postgres;

    let checked_join = check_src_with_lock(join_src, &join_sq_lock)?;
    let main_fn = checked_join.exec.find_fun("main").ok_or("missing main")?;
    let plan = find_first_plan(&main_fn.body).ok_or("missing ExecPlan")?;
    for (dialect, lk) in [
        (SqlDialect::Sqlite, &join_sq_lock),
        (SqlDialect::Postgres, &join_pg_lock),
    ] {
        let split = split_exec_plan_pushdown(plan, &checked_join.exec, "Lake", dialect, Some(lk));
        match split {
            SplitPlan::FullyPushed(q) => {
                assert!(
                    q.sql.contains(r#"FROM "populi"."enrollments""#)
                        && q.sql.contains(r#"FROM "canvas"."courses""#)
                        && q.sql.contains("INNER JOIN")
                        && q.sql.contains("GROUP BY")
                        && q.sql.contains("ORDER BY"),
                    "expected FullyPushed qualified cross-schema join aggregate SQL for {dialect:?}, got:\n{}",
                    q.sql
                );
            }
            other => {
                return Err(format!(
                    "expected FullyPushed SQL pushdown for {dialect:?}, got {other:?}"
                )
                .into());
            }
        }
    }

    let join_dedupe_src = r##"module AttachJoinDedupe

schema Enroll
  id: Int
  uid: Int
  cid: Int
  status: Text
end

schema Course
  cid: Int
  code: Text
end

fn main(db: ReadDB(Lake), console: Console) : Int
  joined = db.table(Enroll, from: "populi.enrollments")
    |> join_many_to_one(db.table(Course, from: "canvas.courses"), on: .cid)
    |> dedupe_by(.uid, order_by: [desc(.id)])
    |> sort_by(.uid)
  console.print_table(joined)
  0
end
"##;
    let checked_join_dedupe = check_src_with_lock(join_dedupe_src, &join_sq_lock)?;
    let jd_plan = find_first_plan(
        &checked_join_dedupe
            .exec
            .find_fun("main")
            .ok_or("main")?
            .body,
    )
    .ok_or("missing ExecPlan")?;
    for (dialect, lk, expect_frag) in [
        (SqlDialect::Sqlite, &join_sq_lock, "ROW_NUMBER() OVER"),
        (SqlDialect::Postgres, &join_pg_lock, "SELECT DISTINCT ON"),
    ] {
        let jd_split = split_exec_plan_pushdown(
            jd_plan,
            &checked_join_dedupe.exec,
            "Lake",
            dialect,
            Some(lk),
        );
        match jd_split {
            SplitPlan::FullyPushed(q) => {
                assert!(
                    q.sql.contains("INNER JOIN") && q.sql.contains(expect_frag),
                    "expected FullyPushed join+dedupe SQL for {dialect:?}, got:\n{}",
                    q.sql
                );
            }
            other => {
                return Err(format!(
                    "expected FullyPushed join+dedupe SQL for {dialect:?}, got {other:?}"
                )
                .into());
            }
        }
    }

    // 2. CLI `--db`, `--attach schema=PATH`, `--attach DB:schema=PATH`, `schema-sync`, `check`, `run`
    let script_path = tmp.path().join("attach_join.dana");
    fs::write(&script_path, join_src)?;
    let lock_path = tmp.path().join("schema.lock");
    let bin = env!("CARGO_BIN_EXE_dana");
    let main_uri = sqlite_uri(&main_db);
    let db_arg = format!("Lake={main_uri}");
    let attach_populi = format!("populi={}", populi_db.display());
    let attach_canvas = format!("Lake:canvas={}", canvas_db.display());

    let sync_out = Command::new(bin)
        .args(["schema-sync", "--db", &db_arg, "--attach", &attach_populi])
        .arg(format!("--attach={attach_canvas}"))
        .arg("--out")
        .arg(&lock_path)
        .output()?;
    assert_eq!(
        sync_out.status.code(),
        Some(0),
        "schema-sync --attach failed: {}",
        String::from_utf8_lossy(&sync_out.stderr)
    );
    let lock_text = fs::read_to_string(&lock_path)?;
    assert!(
        lock_text.contains("populi.enrollments") && lock_text.contains("canvas.courses"),
        "expected attached tables in schema.lock:\n{lock_text}"
    );

    let check_out = Command::new(bin)
        .args(["check", "--db", &db_arg, "--attach", &attach_populi])
        .arg("--schema-lock")
        .arg(&lock_path)
        .arg(&script_path)
        .output()?;
    assert_eq!(
        check_out.status.code(),
        Some(0),
        "check --attach failed: {}",
        String::from_utf8_lossy(&check_out.stderr)
    );

    let vm_run = Command::new(bin)
        .args(["run", "--db", &db_arg, "--attach", &attach_populi])
        .arg(format!("--attach={attach_canvas}"))
        .arg("--schema-lock")
        .arg(&lock_path)
        .arg(&script_path)
        .output()?;
    assert_eq!(
        vm_run.status.code(),
        Some(0),
        "run --attach VM failed: {}",
        String::from_utf8_lossy(&vm_run.stderr)
    );
    let ora_run = Command::new(bin)
        .args([
            "run",
            "--oracle",
            "--db",
            &db_arg,
            "--attach",
            &attach_populi,
            "--attach",
            &attach_canvas,
            "--schema-lock",
        ])
        .arg(&lock_path)
        .arg(&script_path)
        .output()?;
    assert_eq!(ora_run.status.code(), Some(0));
    assert_eq!(vm_run.stdout, ora_run.stdout);

    // 3. Attached SQLite `WriteTable(Lake, "populi.enrollments").upsert(...)` (`dry-run` + live)
    let upsert_src = r##"module AttachUpsert

schema EnrollRow
  id: Int
  uid: Int
  cid: Int
  status: Text
end

fn main(wt: WriteTable(Lake, "populi.enrollments"), console: Console) : Int
  rows = table
    | id | uid | cid | status      |
    | 1  | 10  | 100 | "COMPLETED" |
    | 3  | 30  | 100 | "ENROLLED"  |
  end
  stats = try wt.upsert(rows, key: .id)
  console.print("ins=#{stats.inserted}:upd=#{stats.updated}:unch=#{stats.unchanged}")
  0
end
"##;
    let upsert_path = tmp.path().join("attach_upsert.dana");
    fs::write(&upsert_path, upsert_src)?;

    let dry_out = Command::new(bin)
        .args(["dry-run", "--db", &db_arg, "--attach", &attach_populi])
        .arg(&upsert_path)
        .output()?;
    assert_eq!(
        dry_out.status.code(),
        Some(0),
        "dry-run upsert --attach failed: {}",
        String::from_utf8_lossy(&dry_out.stderr)
    );
    let mut pc_check = open_connection(&sqlite_uri(&populi_db))?;
    let pre_lock = pc_check.introspect_schema("populi")?;
    let pre_rows = pre_lock
        .find_table("enrollments")
        .ok_or("missing enrollments")?;
    assert_eq!(pre_rows.cols.len(), 4);
    let check_schema = dana::core::syntax::TableTy {
        cols: vec![
            dana::core::syntax::ColSpec {
                name: "id".to_string(),
                ty: dana::core::syntax::ScalarTy::Int,
                tags: dana::core::syntax::TagSet::empty(),
                bucketed: false,
                agg_kind: dana::core::syntax::AggKind::Raw,
            },
            dana::core::syntax::ColSpec {
                name: "status".to_string(),
                ty: dana::core::syntax::ScalarTy::Text,
                tags: dana::core::syntax::TagSet::empty(),
                bucketed: false,
                agg_kind: dana::core::syntax::AggKind::Raw,
            },
        ],
        ..dana::core::syntax::TableTy::default()
    };
    let mut pc_raw = open_connection(&sqlite_uri(&populi_db))?;
    let pre_tbl = pc_raw.query_rows(
        r#"SELECT "id", "status" FROM "enrollments" ORDER BY "id""#,
        &[],
        &check_schema,
    )?;
    assert_eq!(pre_tbl.rows.len(), 2, "dry-run must not mutate attached DB");
    assert!(
        matches!(&pre_tbl.rows[0].cells[1], dana::oracle::value::Val::Text(s) if s == "ENROLLED")
    );

    let live_out = Command::new(bin)
        .args(["run", "--db", &db_arg, "--attach", &attach_populi])
        .arg(&upsert_path)
        .output()?;
    assert_eq!(
        live_out.status.code(),
        Some(0),
        "live upsert --attach failed: {}",
        String::from_utf8_lossy(&live_out.stderr)
    );
    assert_eq!(
        String::from_utf8(live_out.stdout)?.trim(),
        "ins=1:upd=1:unch=0"
    );
    let post_tbl = pc_raw.query_rows(
        r#"SELECT "id", "status" FROM "enrollments" ORDER BY "id""#,
        &[],
        &check_schema,
    )?;
    assert_eq!(post_tbl.rows.len(), 3);
    assert!(
        matches!(&post_tbl.rows[0].cells[1], dana::oracle::value::Val::Text(s) if s == "COMPLETED")
    );

    // 4. Unattached SQLite `"schema.table"` resolution priority:
    //    literal `"populi.enrollments"` in `main` beats `"populi_enrollments"`,
    //    and `"populi_enrollments"` in `main` works as fallback when literal does not exist.
    let both_db = tmp.path().join("both.db");
    {
        let mut bc = open_connection(&sqlite_uri(&both_db))?;
        bc.execute(
            r#"CREATE TABLE "populi.enrollments" ("id" INTEGER PRIMARY KEY NOT NULL, "src_tag" TEXT NOT NULL)"#,
            &[],
        )?;
        bc.execute(
            r#"INSERT INTO "populi.enrollments" VALUES (1, 'literal_won')"#,
            &[],
        )?;
        bc.execute(
            r#"CREATE TABLE "populi_enrollments" ("id" INTEGER PRIMARY KEY NOT NULL, "src_tag" TEXT NOT NULL)"#,
            &[],
        )?;
        bc.execute(
            r#"INSERT INTO "populi_enrollments" VALUES (1, 'flat_lost')"#,
            &[],
        )?;
    }
    let flat_only_db = tmp.path().join("flat_only.db");
    {
        let mut fc = open_connection(&sqlite_uri(&flat_only_db))?;
        fc.execute(
            r#"CREATE TABLE "populi_enrollments" ("id" INTEGER PRIMARY KEY NOT NULL, "src_tag" TEXT NOT NULL)"#,
            &[],
        )?;
        fc.execute(
            r#"INSERT INTO "populi_enrollments" VALUES (1, 'flat_fallback')"#,
            &[],
        )?;
    }
    let fallback_src = r##"module FallbackTest

schema Item
  id: Int
  src_tag: Text
end

fn main(db: ReadDB(Lake), console: Console) : Int
  rows = db.table(Item, from: "populi.enrollments") |> sort_by(.id)
  console.print("#{rows.first!.src_tag}")
  0
end
"##;
    let both_out = assert_oracle_vm_parity(fallback_src, Some(("Lake", &sqlite_uri(&both_db))))?;
    assert_eq!(both_out, vec!["literal_won".to_string()]);
    let flat_out =
        assert_oracle_vm_parity(fallback_src, Some(("Lake", &sqlite_uri(&flat_only_db))))?;
    assert_eq!(flat_out, vec!["flat_fallback".to_string()]);

    // 5. Invalid `--attach` CLI flags exit with code 2
    for bad_args in [
        vec!["run", "--attach", "missing_equals"],
        vec!["run", "--attach=populi="],
        vec!["run", "--attach=main=other.db"],
        vec!["run", "--attach", "TEMP=other.db"],
        vec!["run", "--attach=bad-schema=other.db"],
        vec!["run", "--attach=:populi=other.db"],
        vec!["check", "--attach=bad-schema=other.db"],
        vec![
            "schema-sync",
            "--db",
            &db_arg,
            "--attach=bad-schema=other.db",
        ],
        vec!["run", "--attach"],
    ] {
        let out = Command::new(bin).args(&bad_args).output()?;
        assert_eq!(
            out.status.code(),
            Some(2),
            "expected exit 2 for {bad_args:?}, got {:?} ({})",
            out.status.code(),
            String::from_utf8_lossy(&out.stderr)
        );
    }

    Ok(())
}

#[test]
fn v06_try_parse_date_exact_sql_pushdown_sqlite_and_postgres() -> TestResult {
    let tmp = TempDir::new("try_parse_date_pushdown")?;
    let db_path = tmp.path().join("dates.db");
    let uri = sqlite_uri(&db_path);
    {
        let mut conn = open_connection(&uri)?;
        conn.execute(
            r#"CREATE TABLE "dates" ("id" INTEGER PRIMARY KEY NOT NULL, "raw" TEXT NOT NULL)"#,
            &[],
        )?;
        let cases = [
            (1i64, "2024-02-29"),
            (2, "2023-02-29"),
            (3, "1900-02-29"),
            (4, "2000-02-29"),
            (5, "0000-02-29"),
            (6, " 1999-12-31 \r\n"),
            (7, "\u{00A0}2024-01-01"),
            (8, "+999-+1-+1"),
            (9, "-100-01-01"),
            (10, "2024-00-10"),
            (11, "2024-13-01"),
            (12, "2024-04-31"),
            (13, "2024-1-5"),
            (14, ""),
            (15, "2026-01-12T00:00:00Z"),
        ];
        for (id, raw) in cases {
            conn.execute(
                r#"INSERT INTO "dates" VALUES (?, ?)"#,
                &[SqlParam::Int(id), SqlParam::Text(raw.to_string())],
            )?;
        }
    }

    let direct_src = r##"module DatePushdown

schema RawDate
  id: Int
  raw: Text
end

fn main(db: ReadDB(DB), console: Console) : Int
  out = db.table(RawDate, from: "dates")
    |> derive(d: .raw.try_parse_date)
    |> sort_by(.id)
  for r in out
    console.print("#{r.id}:#{r.d}")
  end
  0
end
"##;
    let lines = assert_oracle_vm_parity(direct_src, Some(("DB", &uri)))?;
    assert_eq!(
        lines,
        vec![
            "1:2024-02-29",
            "2:none",
            "3:none",
            "4:2000-02-29",
            "5:none",
            "6:1999-12-31",
            "7:none",
            "8:none",
            "9:none",
            "10:none",
            "11:none",
            "12:none",
            "13:none",
            "14:none",
            "15:none",
        ]
    );

    let dates_sq_lock = dana::db::schema_lock::SchemaLockFile {
        dbs: vec![dana::db::schema_lock::LockedDb {
            name: "DB".to_string(),
            dialect: SqlDialect::Sqlite,
            tables: vec![dana::db::schema_lock::LockedTable {
                name: "dates".to_string(),
                cols: vec![
                    dana::db::schema_lock::LockedCol {
                        name: "id".to_string(),
                        ty: dana::core::syntax::ScalarTy::Int,
                        nullable: false,
                        pk: true,
                        tags: dana::core::syntax::TagSet::empty(),
                    },
                    dana::db::schema_lock::LockedCol {
                        name: "raw".to_string(),
                        ty: dana::core::syntax::ScalarTy::Text,
                        nullable: false,
                        pk: false,
                        tags: dana::core::syntax::TagSet::empty(),
                    },
                ],
            }],
        }],
        ..dana::db::schema_lock::SchemaLockFile::default()
    };
    let mut dates_pg_lock = dates_sq_lock.clone();
    dates_pg_lock.dbs[0].dialect = SqlDialect::Postgres;

    let checked_direct = check_src_with_lock(direct_src, &dates_sq_lock)?;
    let main_fn = checked_direct.exec.find_fun("main").ok_or("missing main")?;
    let plan = find_first_plan(&main_fn.body).ok_or("missing ExecPlan")?;
    let sq_split = split_exec_plan_pushdown(
        plan,
        &checked_direct.exec,
        "DB",
        SqlDialect::Sqlite,
        Some(&dates_sq_lock),
    );
    match sq_split {
        SplitPlan::FullyPushed(q) => {
            assert!(
                q.sql
                    .contains("GLOB '[0-9][0-9][0-9][0-9]-[0-9][0-9]-[0-9][0-9]'")
                    && q.sql.contains("<> '0000'"),
                "unexpected SQLite TryParseIsoDate SQL:\n{}",
                q.sql
            );
        }
        other => return Err(format!("expected SQLite FullyPushed, got {other:?}").into()),
    }
    let pg_split = split_exec_plan_pushdown(
        plan,
        &checked_direct.exec,
        "DB",
        SqlDialect::Postgres,
        Some(&dates_pg_lock),
    );
    match pg_split {
        SplitPlan::FullyPushed(q) => {
            assert!(
                q.sql.contains("BTRIM(")
                    && q.sql.contains("CHR(32)")
                    && q.sql.contains("~ '^[0-9]{4}-[0-9]{2}-[0-9]{2}$'")
                    && q.sql.contains("<> '0000'")
                    && q.sql.contains("AS DATE)"),
                "unexpected Postgres TryParseIsoDate SQL:\n{}",
                q.sql
            );
        }
        other => return Err(format!("expected Postgres FullyPushed, got {other:?}").into()),
    }

    // Slice + try_parse_date (P4 timestamp prefix pattern) also pushes cleanly end-to-end
    let slice_src = r##"module DateSlicePushdown

schema RawDate
  id: Int
  raw: Text
end

fn main(db: ReadDB(DB), console: Console) : Int
  out = db.table(RawDate, from: "dates")
    |> derive(ds: .raw.slice(0, 10).try_parse_date)
    |> where(.ds.some?)
    |> sort_by(.id)
  for r in out
    console.print("#{r.id}:#{r.ds}")
  end
  0
end
"##;
    let slice_lines = assert_oracle_vm_parity(slice_src, Some(("DB", &uri)))?;
    assert_eq!(
        slice_lines,
        vec!["1:2024-02-29", "4:2000-02-29", "15:2026-01-12",]
    );
    let checked_slice = check_src_with_lock(slice_src, &dates_sq_lock)?;
    let slice_plan = find_first_plan(&checked_slice.exec.find_fun("main").ok_or("main")?.body)
        .ok_or("missing ExecPlan")?;
    for (dialect, lk) in [
        (SqlDialect::Sqlite, &dates_sq_lock),
        (SqlDialect::Postgres, &dates_pg_lock),
    ] {
        let sp = split_exec_plan_pushdown(slice_plan, &checked_slice.exec, "DB", dialect, Some(lk));
        assert!(
            matches!(sp, SplitPlan::FullyPushed(_)),
            "expected slice+try_parse_date+where to push fully on {dialect:?}, got {sp:?}"
        );
    }

    Ok(())
}

#[test]
fn v06_dedupe_by_parity_pushdown_privacy_and_negative_probes() -> TestResult {
    // 1. In-memory dedupe_by without order_by (`:first` default & `:last`), preserving winner input order
    let no_order_src = r##"module DedupeNoOrder

fn main(console: Console) : Int
  rows = table
    | id | uid | seq | tag |
    | 1  | 10  | 1   | "a" |
    | 2  | 20  | 1   | "b" |
    | 3  | 10  | 2   | "c" |
    | 4  | 30  | 1   | "d" |
    | 5  | 20  | 2   | "e" |
  end
  first_kept = rows |> dedupe_by(.uid)
  last_kept = rows |> dedupe_by(.uid, keep: :last)
  for r in first_kept
    console.print("F:#{r.id}:#{r.uid}:#{r.tag}")
  end
  for r in last_kept
    console.print("L:#{r.id}:#{r.uid}:#{r.tag}")
  end
  0
end
"##;
    let no_ord_out = assert_oracle_vm_parity(no_order_src, None)?;
    assert_eq!(
        no_ord_out,
        vec![
            "F:1:10:a", "F:2:20:b", "F:4:30:d", "L:3:10:c", "L:4:30:d", "L:5:20:e",
        ]
    );

    // 2. Multi-key `dedupe_by(.uid, .cid, order_by: [desc(.active), desc(.updated_at), desc(.id)], keep: :first/:last)`
    //    with `none`s and ties
    let ordered_src = r##"module DedupeOrdered

fn main(console: Console) : Int
  rows = table
    | id | uid | cid | active | updated_at   | note |
    | 1  | 10  | 100 | false  | "2026-01-05" | "old-false" |
    | 2  | 10  | 100 | true   | none         | "active-null" |
    | 3  | 10  | 100 | true   | "2026-01-02" | "active-date-older" |
    | 4  | 10  | 100 | true   | "2026-01-02" | "active-date-newer-id" |
    | 5  | 20  | 200 | false  | none         | "u20-null" |
    | 6  | 20  | 200 | false  | "2025-12-01" | "u20-date" |
  end
  f = rows |> dedupe_by(.uid, .cid, order_by: [desc(.active), desc(.updated_at), desc(.id)], keep: :first) |> sort_by(.id)
  l = rows |> dedupe_by(.uid, .cid, order_by: [desc(.active), desc(.updated_at), desc(.id)], keep: :last) |> sort_by(.id)
  for r in f
    console.print("F:#{r.id}:#{r.note}")
  end
  for r in l
    console.print("L:#{r.id}:#{r.note}")
  end
  0
end
"##;
    let ord_out = assert_oracle_vm_parity(ordered_src, None)?;
    assert_eq!(
        ord_out,
        vec![
            "F:4:active-date-newer-id",
            "F:6:u20-date",
            "L:1:old-false",
            "L:5:u20-null",
        ]
    );

    // 3. SQLite & Postgres pushdown with PK tie-breaker + Hybrid fallback without unique tie-breaker
    let tmp = TempDir::new("dedupe_sql")?;
    let db_path = tmp.path().join("dedupe.db");
    let uri = sqlite_uri(&db_path);
    {
        let mut conn = open_connection(&uri)?;
        conn.execute(
            r#"CREATE TABLE "enrollments" (
                "id" INTEGER PRIMARY KEY NOT NULL,
                "uid" TEXT NOT NULL,
                "cid" INTEGER NOT NULL,
                "active" INTEGER NOT NULL,
                "updated_at" TEXT
            )"#,
            &[],
        )?;
        for (id, uid, cid, active, upd) in [
            (1i64, "u1", 100i64, 0i64, Some("2026-02-01")),
            (2, "u1", 100, 1, None),
            (3, "u1", 100, 1, Some("2026-01-10")),
            (4, "u1", 100, 1, Some("2026-01-10")),
            (5, "u2", 200, 0, None),
            (6, "u2", 200, 1, Some("2025-11-01")),
        ] {
            let upd_param = match upd {
                Some(s) => SqlParam::Text(s.to_string()),
                None => SqlParam::Null,
            };
            conn.execute(
                r#"INSERT INTO "enrollments" VALUES (?, ?, ?, ?, ?)"#,
                &[
                    SqlParam::Int(id),
                    SqlParam::Text(uid.to_string()),
                    SqlParam::Int(cid),
                    SqlParam::Int(active),
                    upd_param,
                ],
            )?;
        }
    }

    let lock = dana::db::schema_lock::SchemaLockFile {
        dbs: vec![dana::db::schema_lock::LockedDb {
            name: "DB".to_string(),
            dialect: SqlDialect::Sqlite,
            tables: vec![dana::db::schema_lock::LockedTable {
                name: "enrollments".to_string(),
                cols: vec![
                    dana::db::schema_lock::LockedCol {
                        name: "id".to_string(),
                        ty: dana::core::syntax::ScalarTy::Int,
                        nullable: false,
                        pk: true,
                        tags: dana::core::syntax::TagSet::empty(),
                    },
                    dana::db::schema_lock::LockedCol {
                        name: "uid".to_string(),
                        ty: dana::core::syntax::ScalarTy::Text,
                        nullable: false,
                        pk: false,
                        tags: dana::core::syntax::TagSet::empty(),
                    },
                    dana::db::schema_lock::LockedCol {
                        name: "cid".to_string(),
                        ty: dana::core::syntax::ScalarTy::Int,
                        nullable: false,
                        pk: false,
                        tags: dana::core::syntax::TagSet::empty(),
                    },
                    dana::db::schema_lock::LockedCol {
                        name: "active".to_string(),
                        ty: dana::core::syntax::ScalarTy::Bool,
                        nullable: false,
                        pk: false,
                        tags: dana::core::syntax::TagSet::empty(),
                    },
                    dana::db::schema_lock::LockedCol {
                        name: "updated_at".to_string(),
                        ty: dana::core::syntax::ScalarTy::Text,
                        nullable: true,
                        pk: false,
                        tags: dana::core::syntax::TagSet::empty(),
                    },
                ],
            }],
        }],
        ..dana::db::schema_lock::SchemaLockFile::default()
    };
    let mut pg_lock = lock.clone();
    pg_lock.dbs[0].dialect = SqlDialect::Postgres;

    let db_push_src = r##"module DedupeSql

schema Enroll
  id: Int
  uid: Text
  cid: Int
  active: Bool
  updated_at: Text?
end

fn main(db: ReadDB(DB), console: Console) : Int
  res = db.table(Enroll, from: "enrollments")
    |> dedupe_by(.uid, .cid, order_by: [desc(.active), desc(.updated_at), desc(.id)])
    |> where(.cid >= 100)
    |> sort_by(.id)
  for r in res
    console.print("#{r.id}:#{r.uid}:#{r.cid}:#{r.active}:#{r.updated_at}")
  end
  0
end
"##;
    let checked_push = check_src_with_lock(db_push_src, &lock)?;
    let main_fn = checked_push.exec.find_fun("main").ok_or("missing main")?;
    let plan = find_first_plan(&main_fn.body).ok_or("missing ExecPlan")?;
    let sq_split = split_exec_plan_pushdown(
        plan,
        &checked_push.exec,
        "DB",
        SqlDialect::Sqlite,
        Some(&lock),
    );
    match &sq_split {
        SplitPlan::FullyPushed(q) => {
            assert!(
                q.sql.contains("ROW_NUMBER() OVER (PARTITION BY")
                    && q.sql.contains("= 1")
                    && q.sql.contains("WHERE"),
                "unexpected SQLite dedupe_by SQL:\n{}",
                q.sql
            );
        }
        other => {
            return Err(format!("expected SQLite FullyPushed with PK lock, got {other:?}").into());
        }
    }
    let pg_split = split_exec_plan_pushdown(
        plan,
        &checked_push.exec,
        "DB",
        SqlDialect::Postgres,
        Some(&pg_lock),
    );
    match &pg_split {
        SplitPlan::FullyPushed(q) => {
            assert!(
                q.sql.contains("SELECT DISTINCT ON (")
                    && q.sql.contains(r#""uid" COLLATE "C""#)
                    && q.sql.contains("ORDER BY")
                    && q.sql.contains("WHERE"),
                "unexpected Postgres dedupe_by SQL:\n{}",
                q.sql
            );
        }
        other => {
            return Err(
                format!("expected Postgres FullyPushed with PK lock, got {other:?}").into(),
            );
        }
    }

    // Without unique tie-breaker (no PK lock), SQL pushdown must fall back cleanly to Hybrid
    let checked_nolock = check_src(db_push_src)?;
    let nolock_plan = find_first_plan(&checked_nolock.exec.find_fun("main").ok_or("main")?.body)
        .ok_or("missing ExecPlan")?;
    let hybrid_split = split_exec_plan_pushdown(
        nolock_plan,
        &checked_nolock.exec,
        "DB",
        SqlDialect::Sqlite,
        None,
    );
    assert!(
        matches!(hybrid_split, SplitPlan::Hybrid { .. }),
        "expected Hybrid fallback without unique tie-breaker, got {hybrid_split:?}"
    );

    // Live SQLite pushdown (with lock) == VM (without lock) == Oracle parity
    let no_lock_out = assert_oracle_vm_parity(db_push_src, Some(("DB", &uri)))?;
    let mut lock_db_map = HashMap::new();
    lock_db_map.insert("DB".to_string(), uri.clone());
    let lock_cfg = RunConfig {
        live_io: true,
        db_bindings: lock_db_map,
        schema_lock: Some(lock),
        ..RunConfig::default()
    };
    let vm_pushed_out =
        match run_exec_program_vm(&checked_push.exec, &lock_cfg, &VmConfig::default()) {
            RunResult::Ok {
                exit_code: 0,
                stdout,
                ..
            } => stdout,
            other => return Err(format!("VM locked run failed: {other:?}").into()),
        };
    let ora_pushed_out = match run_exec_program(&checked_push.exec, &lock_cfg) {
        RunResult::Ok {
            exit_code: 0,
            stdout,
            ..
        } => stdout,
        other => return Err(format!("Oracle locked run failed: {other:?}").into()),
    };
    let expected_db_rows = vec![
        "4:u1:100:true:2026-01-10".to_string(),
        "6:u2:200:true:2025-11-01".to_string(),
    ];
    assert_eq!(no_lock_out, expected_db_rows);
    assert_eq!(vm_pushed_out, expected_db_rows);
    assert_eq!(ora_pushed_out, expected_db_rows);

    // 4. `dana explain` reports `DEDUPE DedupeBy(`
    let explain_path = tmp.path().join("dedupe_explain.dana");
    fs::write(&explain_path, db_push_src)?;
    let exp_out = Command::new(env!("CARGO_BIN_EXE_dana"))
        .args(["explain", "--dialect", "postgres"])
        .arg(&explain_path)
        .output()?;
    assert_eq!(exp_out.status.code(), Some(0));
    let exp_stdout = String::from_utf8(exp_out.stdout)?;
    assert!(
        exp_stdout.contains("DEDUPE DedupeBy("),
        "expected DEDUPE DedupeBy in explain output:\n{exp_stdout}"
    );

    // 5. Privacy taint: `dedupe_by` on [pii]/[ferpa] column taints row_tags (`E0201` on public console),
    //    and `summarize` + `suppress_small_groups` clears it.
    let taint_leak_src = r##"module DedupeTaintLeak

schema Rec
  uid: Int [pii]
  dept: Text
  score: Int
end

fn leak_check(rows: Table(Rec), console: Console) : Int
  d = rows |> dedupe_by(.uid) |> select(.dept)
  console.print("#{d.count()}")
  0
end
"##;
    let leak_diags = check_src_diags(taint_leak_src)?;
    assert!(
        leak_diags
            .iter()
            .any(|d| d.code() == DiagCode::PrivacyError),
        "expected E0201 PrivacyError on dedupe_by(.uid [pii]) count, got {leak_diags:?}"
    );

    let taint_cleared_src = r##"module DedupeTaintCleared

schema StudentRow
  uid: Int [pii]
  cid: Int [ferpa]
  dept: Text
end

fn summarize_safe(rows: Table(StudentRow), console: Console) : Int
  res = rows
    |> dedupe_by(.uid, .cid, order_by: [desc(.cid)])
    |> group_by(.dept)
    |> summarize(n: count_distinct(.uid))
    |> suppress_small_groups(min: 5, distinct_by: .uid)
  console.print_table(res)
  0
end

fn main(db: ReadDB(DB), console: Console) : Int
  _ = db.table(StudentRow, from: "enrollments")
  rows = table
    | uid | cid | dept  |
    | 1   | 10  | "eng" |
    | 2   | 10  | "eng" |
    | 3   | 10  | "eng" |
    | 4   | 10  | "eng" |
    | 5   | 10  | "eng" |
    | 5   | 10  | "eng" |
  end
  _ = rows
  0
end
"##;
    // Also verify runtime execution using schema tags via DB scan on the clean seeded rows
    let taint_run_src = r##"module DedupeTaintClearedRun

schema EnrollTag
  id: Int
  uid: Text [pii]
  cid: Int [ferpa]
  active: Bool
  updated_at: Text?
end

fn main(db: ReadDB(DB), console: Console) : Int
  res = db.table(EnrollTag, from: "enrollments")
    |> dedupe_by(.uid, .cid, order_by: [desc(.cid)])
    |> summarize(n: count_distinct(.uid))
    |> suppress_small_groups(min: 2, distinct_by: .uid)
  0
end
"##;
    let _ = taint_run_src;
    let cleared_checked = check_src(taint_cleared_src)?;
    assert!(cleared_checked.warnings.is_empty());

    let taint_runtime_src = r##"module DedupeTaintClearedRuntime

schema RawEnr
  uid: Int [pii]
  cid: Int [ferpa]
  dept: Text
end

fn run_safe(db: ReadDB(DB), console: Console) : Int
  rows = db.table(RawEnr, from: "taint_enr")
  res = rows
    |> dedupe_by(.uid, .cid, order_by: [desc(.cid)])
    |> group_by(.dept)
    |> summarize(n: count_distinct(.uid))
    |> suppress_small_groups(min: 5, distinct_by: .uid)
  console.print_table(res)
  0
end

fn main(db: ReadDB(DB), console: Console) : Int
  run_safe(db, console)
end
"##;
    {
        let mut conn = open_connection(&uri)?;
        conn.execute(
            r#"CREATE TABLE "taint_enr" ("uid" INTEGER NOT NULL, "cid" INTEGER NOT NULL, "dept" TEXT NOT NULL)"#,
            &[],
        )?;
        for (uid, cid) in [(1i64, 10i64), (2, 10), (3, 10), (4, 10), (5, 10), (5, 10)] {
            conn.execute(
                r#"INSERT INTO "taint_enr" VALUES (?, ?, 'eng')"#,
                &[SqlParam::Int(uid), SqlParam::Int(cid)],
            )?;
        }
    }
    let cleared_out = assert_oracle_vm_parity(taint_runtime_src, Some(("DB", &uri)))?;
    assert!(
        cleared_out.join("\n").contains('5'),
        "expected cleared dedupe+suppress summary, got {cleared_out:?}"
    );

    // 6. Negative compile probes + row-expr hint
    for bad_src in [
        "module D1\nfn main() : Int\n  t = table\n    | a |\n    | 1 |\n  end\n  _ = t |> dedupe_by()\n  0\nend\n",
        "module D2\nfn main() : Int\n  t = table\n    | a |\n    | 1 |\n  end\n  _ = t |> dedupe_by(.a, .a)\n  0\nend\n",
        "module D3\nfn main() : Int\n  t = table\n    | a |\n    | 1 |\n  end\n  _ = t |> dedupe_by(.missing)\n  0\nend\n",
        "module D4\nfn main() : Int\n  t = table\n    | a |\n    | 1 |\n  end\n  _ = t |> dedupe_by(.a, order_by: .missing)\n  0\nend\n",
        "module D5\nfn main() : Int\n  t = table\n    | a |\n    | 1 |\n  end\n  _ = t |> dedupe_by(.a, order_by: [])\n  0\nend\n",
        "module D6\nfn main() : Int\n  t = table\n    | a |\n    | 1 |\n  end\n  _ = t |> dedupe_by(.a, keep: :middle)\n  0\nend\n",
        "module D7\nfn main() : Int\n  t = table\n    | a |\n    | 1 |\n  end\n  _ = t |> dedupe_by(.a, order_by: [.a + 1])\n  0\nend\n",
    ] {
        let ds = check_src_diags(bad_src)?;
        assert!(
            ds.iter().any(|d| d.code() == DiagCode::TypeError),
            "expected TypeError for:\n{bad_src}\ngot: {ds:?}"
        );
    }
    let hint_src = r##"module DedupeInDerive
fn main() : Int
  t = table
    | a |
    | 1 |
  end
  _ = t |> derive(x: dedupe_by(.a))
  0
end
"##;
    let hint_diags = check_src_diags(hint_src)?;
    assert!(
        hint_diags.iter().any(|d| {
            d.code() == DiagCode::TypeError
                && d.hints()
                    .iter()
                    .any(|h| h.contains("pipeline") && h.contains("|>"))
        }),
        "expected pipeline verb hint for dedupe_by inside derive, got {hint_diags:?}"
    );

    Ok(())
}

#[test]
fn v061_chained_summarize_and_bound_groupby_parity() -> TestResult {
    // 1. Inline & bound chained summarize + bound group_by variable (VM == Oracle parity)
    let chained_src = r##"module ChainedSummarize

fn main(console: Console) : Int
  rows = table
    | id | yr   | val |
    | 1  | 2024 | 10  |
    | 2  | 2024 | 20  |
    | 3  | 2025 | 30  |
    | 4  | 2025 | 40  |
    | 5  | 2025 | 50  |
  end

  inline_min = (rows
    |> group_by(.yr)
    |> summarize(n: count())
    |> summarize(min_k: min(.n), max_k: max(.n))).first!.min_k

  grouped_counts = rows
    |> group_by(.yr)
    |> summarize(n: count())
  bound_agg = grouped_counts |> summarize(min_k: min(.n), max_k: max(.n))
  bound_row = bound_agg.first!

  grouped_only = rows |> group_by(.yr)
  by_year = grouped_only |> summarize(n: count(), tot: sum(.val)) |> sort_by(.yr)
  first_yr = by_year.first!

  console.print("inline=#{inline_min ?? 0} bound=#{bound_row.min_k ?? 0}:#{bound_row.max_k ?? 0} yr=#{first_yr.yr}:#{first_yr.n}:#{first_yr.tot}")
  0
end
"##;
    let chained_out = assert_oracle_vm_parity(chained_src, None)?;
    assert_eq!(chained_out, vec!["inline=2 bound=2:3 yr=2024:2:30"]);

    // 2. Verify Core IR lowering produces valid Lean-checked Core IR for chained summarize
    let core_src = r##"module ChainedCore

fn calc(t: Table(yr: Int, val: Int))
  t |> group_by(.yr) |> summarize(n: count()) |> summarize(min_k: min(.n))
end

fn main(console: Console) : Int
  t = table
    | yr   | val |
    | 2024 | 10  |
    | 2024 | 20  |
    | 2025 | 30  |
  end
  console.print_table(calc(t))
  0
end
"##;
    let checked_core = check_src(core_src)?;
    let lowered = dana::lower::lower_program(checked_core)
        .map_err(|d| format!("lower_program failed: {d:?}"))?;
    assert!(
        lowered.verified_core.is_some(),
        "expected chained group_by |> summarize |> summarize to lower to verified Core IR v0.1"
    );
    let core_out = assert_oracle_vm_parity(core_src, None)?;
    assert!(
        core_out.join("\n").contains("min_k") && core_out.join("\n").contains('1'),
        "unexpected ChainedCore output: {core_out:?}"
    );

    // 3. Privacy: suppress_small_groups right after group_by |> summarize stays valid,
    //    while inserting an extra group_by before suppress_small_groups is rejected.
    let valid_priv_src = r##"module ValidSuppressAfterGroupSummarize

schema Item
  id: Int [pii]
  yr: Int
end

fn pub_check(rows: Table(Item)) : Int
  s = rows
    |> group_by(.yr)
    |> summarize(n: count_distinct(.id))
    |> suppress_small_groups(min: 5, distinct_by: .id)
  s.count()
end

fn main() : Int
  0
end
"##;
    let priv_checked = check_src(valid_priv_src)?;
    assert!(priv_checked.warnings.is_empty());

    let bad_priv_src = r##"module RejectReGroupedBeforeSuppress

schema Item
  id: Int [pii]
  yr: Int
end

fn pub_check(rows: Table(Item)) : Int
  s = rows
    |> group_by(.yr)
    |> summarize(n: count())
    |> group_by(.yr)
    |> suppress_small_groups(min: 5)
  s.count()
end

fn main() : Int
  0
end
"##;
    let bad_diags = check_src_diags(bad_priv_src)?;
    assert!(
        bad_diags.iter().any(|d| d.code() == DiagCode::PrivacyError),
        "expected PrivacyError after re-grouping summarized table, got {bad_diags:?}"
    );

    // 4. SQLite & Postgres pushdown + live SQLite == Oracle parity for chained summarize
    let tmp = TempDir::new("chained_sum_sql")?;
    let db_path = tmp.path().join("chained.db");
    let uri = sqlite_uri(&db_path);
    {
        let mut conn = open_connection(&uri)?;
        conn.execute(
            r#"CREATE TABLE "events" ("id" INTEGER PRIMARY KEY NOT NULL, "yr" INTEGER NOT NULL)"#,
            &[],
        )?;
        for (id, yr) in [(1i64, 2024i64), (2, 2024), (3, 2025), (4, 2025), (5, 2025)] {
            conn.execute(
                r#"INSERT INTO "events" VALUES (?, ?)"#,
                &[SqlParam::Int(id), SqlParam::Int(yr)],
            )?;
        }
    }
    let db_src = r##"module ChainedSummarizeSql

schema EventRow
  id: Int
  yr: Int
end

fn main(db: ReadDB(DB), console: Console) : Int
  res = db.table(EventRow, from: "events")
    |> group_by(.yr)
    |> summarize(n: count())
    |> summarize(min_k: min(.n))
  console.print("#{res.first!.min_k ?? 0}")
  0
end
"##;
    let checked_db = check_src(db_src)?;
    let db_plan = find_first_plan(&checked_db.exec.find_fun("main").ok_or("main")?.body)
        .ok_or("missing ExecPlan")?;
    for dialect in [SqlDialect::Sqlite, SqlDialect::Postgres] {
        let split = split_exec_plan_pushdown(db_plan, &checked_db.exec, "DB", dialect, None);
        match split {
            SplitPlan::FullyPushed(q) => {
                assert!(
                    q.sql.contains("MIN(") && q.sql.contains("GROUP BY"),
                    "expected FullyPushed chained summarize SQL for {dialect:?}, got:\n{}",
                    q.sql
                );
            }
            other => {
                return Err(format!(
                    "expected FullyPushed chained summarize for {dialect:?}, got {other:?}"
                )
                .into());
            }
        }
    }
    let db_out = assert_oracle_vm_parity(db_src, Some(("DB", &uri)))?;
    assert_eq!(db_out, vec!["2"]);

    // 5. CLI --version prints `dana v0.6.4`
    let ver = Command::new(env!("CARGO_BIN_EXE_dana"))
        .arg("--version")
        .output()?;
    assert_eq!(ver.status.code(), Some(0));
    assert_eq!(String::from_utf8_lossy(&ver.stdout).trim(), "dana v0.6.4");

    Ok(())
}

// ===========================================================================
// Patch v0.6.2 Tests: Option(T)==T row coercion, PG ENUM/TEXT casts, ISO date dedup
// ===========================================================================

#[test]
fn v062_option_eq_ne_row_coercion_parity_and_pushdown() -> TestResult {
    let tmp = TempDir::new("v062_opt_eq")?;
    let db_path = tmp.path().join("opt_eq.db");
    let uri = sqlite_uri(&db_path);
    {
        let mut conn = open_connection(&uri)?;
        conn.execute(
            r#"CREATE TABLE "items" (
                "id" INTEGER PRIMARY KEY NOT NULL,
                "workflow_state" TEXT,
                "score" NUMERIC
            )"#,
            &[],
        )?;
        conn.execute(
            r#"INSERT INTO "items" VALUES (1, 'active', '1.00'), (2, 'deleted', '2.50'), (3, NULL, NULL), (4, 'invited', '1')"#,
            &[],
        )?;
    }

    let lock_sq = dana::db::schema_lock::SchemaLockFile {
        version: dana::db::schema_lock::SCHEMA_LOCK_VERSION,
        dbs: vec![dana::db::schema_lock::LockedDb {
            name: "DB".to_string(),
            dialect: SqlDialect::Sqlite,
            tables: vec![dana::db::schema_lock::LockedTable {
                name: "items".to_string(),
                cols: vec![
                    dana::db::schema_lock::LockedCol {
                        name: "id".to_string(),
                        ty: dana::core::ScalarTy::Int,
                        nullable: false,
                        pk: true,
                        tags: dana::core::TagSet::empty(),
                    },
                    dana::db::schema_lock::LockedCol {
                        name: "workflow_state".to_string(),
                        ty: dana::core::ScalarTy::Text,
                        nullable: true,
                        pk: false,
                        tags: dana::core::TagSet::empty(),
                    },
                    dana::db::schema_lock::LockedCol {
                        name: "score".to_string(),
                        ty: dana::core::ScalarTy::Decimal,
                        nullable: true,
                        pk: false,
                        tags: dana::core::TagSet::empty(),
                    },
                ],
            }],
        }],
    };
    let mut lock_pg = lock_sq.clone();
    lock_pg.dbs[0].dialect = SqlDialect::Postgres;

    // Crucial: None != "deleted" must evaluate true, Some("deleted") != "deleted" false,
    // symmetric LHS/RHS ("active" == .workflow_state), none == .workflow_state, and Int -> Option(Decimal).
    let src = r##"module OptionEqRowCoercion

schema Item
  id: Int
  workflow_state: Text?
  score: Decimal?
end

fn scalar_none() : Text?
  none
end

fn main(db: ReadDB(DB), console: Console) : Int
  opt_scalar = scalar_none()
  console.print("SC:#{opt_scalar == none}:#{none == opt_scalar}:#{opt_scalar == "deleted"}")
  rows = db.table(Item, from: "items")
    |> where(.workflow_state != "deleted")
    |> derive(
      is_active: .workflow_state == "active",
      sym_active: "active" == .workflow_state,
      sym_not_del: "deleted" != .workflow_state,
      is_none_r: .workflow_state == none,
      is_none_l: none == .workflow_state,
      not_none_l: none != .workflow_state,
      score_is_one: .score == 1,
      one_is_score: 1 == .score
    )
    |> sort_by(.id)
  for r in rows
    console.print("#{r.id}:#{r.is_active}:#{r.sym_active}:#{r.sym_not_del}:#{r.is_none_r}:#{r.is_none_l}:#{r.not_none_l}:#{r.score_is_one}:#{r.one_is_score}")
  end
  0
end
"##;
    let out = assert_oracle_vm_parity(src, Some(("DB", &uri)))?;
    assert_eq!(
        out,
        vec![
            "SC:true:true:false",
            // id=1: "active", 1.00
            "1:true:true:true:false:false:true:true:true",
            // id=3: None, None -> != "deleted" is true!
            "3:false:false:true:true:true:false:false:false",
            // id=4: "invited", 1
            "4:false:false:true:false:false:true:true:true",
        ]
    );

    let checked = check_src_with_lock(src, &lock_sq)?;
    let main_fn = checked.exec.find_fun("main").ok_or("missing main")?;
    let plan = find_first_plan(&main_fn.body).ok_or("missing ExecPlan")?;
    // On SQLite, `.workflow_state != "deleted"` pushes (`IS NOT ?`), while TEXT-encoded Decimal Eq/Ne
    // cleanly falls back to Hybrid VM so '1.00' == 1 stays exact; Postgres pushes everything (`NUMERIC`).
    match split_exec_plan_pushdown(
        plan,
        &checked.exec,
        "DB",
        SqlDialect::Sqlite,
        Some(&lock_sq),
    ) {
        SplitPlan::Hybrid { pushdown, .. } => {
            assert!(
                pushdown.sql.contains("IS NOT ?"),
                "expected `IS NOT ?` in SQLite Hybrid filter SQL:\n{}",
                pushdown.sql
            );
        }
        other => {
            return Err(format!("expected Hybrid for SQLite Decimal Eq/Ne, got {other:?}").into());
        }
    }
    match split_exec_plan_pushdown(
        plan,
        &checked.exec,
        "DB",
        SqlDialect::Postgres,
        Some(&lock_pg),
    ) {
        SplitPlan::FullyPushed(q) => {
            assert!(
                q.sql.contains("IS DISTINCT FROM CAST($"),
                "expected `IS DISTINCT FROM CAST($` in Postgres pushdown SQL:\n{}",
                q.sql
            );
        }
        other => {
            return Err(format!("expected FullyPushed for Postgres, got {other:?}").into());
        }
    }

    // Without Decimal Eq/Ne, Text? Option(T)==T / !=T / ==none pushes FullyPushed on BOTH SQLite and Postgres.
    let push_text_src = r##"module OptionTextFullyPushed

schema Item
  id: Int
  workflow_state: Text?
  score: Decimal?
end

fn main(db: ReadDB(DB), console: Console) : Int
  rows = db.table(Item, from: "items")
    |> where(.workflow_state != "deleted" and none != .workflow_state)
    |> derive(
      is_active: .workflow_state == "active",
      sym_active: "active" == .workflow_state
    )
    |> sort_by(.id)
  console.print_table(rows)
  0
end
"##;
    let checked_pt = check_src_with_lock(push_text_src, &lock_sq)?;
    let plan_pt = find_first_plan(&checked_pt.exec.find_fun("main").ok_or("missing main")?.body)
        .ok_or("missing ExecPlan")?;
    for (dialect, lk, expect_frag) in [
        (SqlDialect::Sqlite, &lock_sq, "IS NOT ?"),
        (SqlDialect::Postgres, &lock_pg, "IS DISTINCT FROM CAST($"),
    ] {
        let sp = split_exec_plan_pushdown(plan_pt, &checked_pt.exec, "DB", dialect, Some(lk));
        match sp {
            SplitPlan::FullyPushed(q) => {
                assert!(
                    q.sql.contains(expect_frag),
                    "expected `{expect_frag}` in {dialect:?} pushdown SQL:\n{}",
                    q.sql
                );
            }
            other => {
                return Err(format!("expected FullyPushed for {dialect:?}, got {other:?}").into());
            }
        }
    }

    // In-memory table expression also respects Option(T) == T / != T / none
    let mem_src = r##"module InMemOptionEq

fn main(console: Console) : Int
  rows = table
    | id | state |
    | 1 | "active" |
    | 2 | "deleted" |
    | 3 | none |
  end
    |> where(.state != "deleted" and .state != none)
    |> sort_by(.id)
  for r in rows
    console.print("#{r.id}:#{r.state}")
  end
  0
end
"##;
    let mem_out = assert_oracle_vm_parity(mem_src, None)?;
    assert_eq!(mem_out, vec!["1:active"]);

    Ok(())
}

#[test]
fn v062_postgres_text_cast_and_try_parse_date_param_dedup() -> TestResult {
    let tmp = TempDir::new("v062_dedup")?;
    let db_path = tmp.path().join("dedup.db");
    let uri = sqlite_uri(&db_path);
    {
        let mut conn = open_connection(&uri)?;
        conn.execute(
            r#"CREATE TABLE "terms" (
                "id" INTEGER PRIMARY KEY NOT NULL,
                "workflow_state" TEXT,
                "start_raw" TEXT,
                "end_raw" TEXT
            )"#,
            &[],
        )?;
        conn.execute(
            r#"INSERT INTO "terms" VALUES
                (1, 'active', '2024-02-29T00:00:00Z', '2024-05-15T23:59:59Z'),
                (2, 'deleted', '2024-01-01T00:00:00Z', '2024-02-01T00:00:00Z'),
                (3, NULL, '2023-02-29T00:00:00Z', '2026-01-12T05:00:00Z'),
                (4, 'active', NULL, '0000-01-01')"#,
            &[],
        )?;
    }

    let lock_sq = dana::db::schema_lock::SchemaLockFile {
        version: dana::db::schema_lock::SCHEMA_LOCK_VERSION,
        dbs: vec![dana::db::schema_lock::LockedDb {
            name: "DB".to_string(),
            dialect: SqlDialect::Sqlite,
            tables: vec![dana::db::schema_lock::LockedTable {
                name: "terms".to_string(),
                cols: vec![
                    dana::db::schema_lock::LockedCol {
                        name: "id".to_string(),
                        ty: dana::core::ScalarTy::Int,
                        nullable: false,
                        pk: true,
                        tags: dana::core::TagSet::empty(),
                    },
                    dana::db::schema_lock::LockedCol {
                        name: "workflow_state".to_string(),
                        ty: dana::core::ScalarTy::Text,
                        nullable: true,
                        pk: false,
                        tags: dana::core::TagSet::empty(),
                    },
                    dana::db::schema_lock::LockedCol {
                        name: "start_raw".to_string(),
                        ty: dana::core::ScalarTy::Text,
                        nullable: true,
                        pk: false,
                        tags: dana::core::TagSet::empty(),
                    },
                    dana::db::schema_lock::LockedCol {
                        name: "end_raw".to_string(),
                        ty: dana::core::ScalarTy::Text,
                        nullable: true,
                        pk: false,
                        tags: dana::core::TagSet::empty(),
                    },
                ],
            }],
        }],
    };
    let mut lock_pg = lock_sq.clone();
    lock_pg.dbs[0].dialect = SqlDialect::Postgres;

    let src = r##"module PgCastAndDateDedup

schema Term
  id: Int
  workflow_state: Text?
  start_raw: Text?
  end_raw: Text?
end

fn main(db: ReadDB(DB), console: Console) : Int
  rows = db.table(Term, from: "terms")
    |> where(.workflow_state != "deleted" and not .workflow_state.in?(["archived"]))
    |> derive(
      start_d: (.start_raw ?? "").slice(0, 10).try_parse_date,
      end_d: (.end_raw ?? "").slice(0, 10).try_parse_date
    )
    |> where((.end_raw ?? "").slice(0, 10).try_parse_date.some?)
    |> sort_by(.workflow_state, .id)
  for r in rows
    console.print("#{r.id}:#{r.workflow_state}:#{r.start_d}:#{r.end_d}")
  end
  0
end
"##;
    let out = assert_oracle_vm_parity(src, Some(("DB", &uri)))?;
    assert_eq!(
        out,
        vec!["3:none:none:2026-01-12", "1:active:2024-02-29:2024-05-15",]
    );

    let checked = check_src_with_lock(src, &lock_sq)?;
    let main_fn = checked.exec.find_fun("main").ok_or("missing main")?;
    let plan = find_first_plan(&main_fn.body).ok_or("missing ExecPlan")?;

    for (dialect, lk) in [
        (SqlDialect::Sqlite, &lock_sq),
        (SqlDialect::Postgres, &lock_pg),
    ] {
        let sp = split_exec_plan_pushdown(plan, &checked.exec, "DB", dialect, Some(lk));
        match sp {
            SplitPlan::FullyPushed(q) => {
                // Before v0.6.2, each TryParseIsoDate emitted 15x inner parameters (45 per date).
                // Now each hoisted TrimAscii emits its inner params once plus one whitespace literal (~4 per date).
                assert!(
                    q.param_slots.len() <= 20,
                    "expected deduplicated TryParseIsoDate params <= 20 for {dialect:?}, got {}:\n{}",
                    q.param_slots.len(),
                    q.sql
                );
                assert!(
                    !q.sql.contains("\"_dana_iso_")
                        || q.out_schema
                            .cols
                            .iter()
                            .all(|c| !c.name.starts_with("_dana_iso_")),
                    "hidden hoisted column leaked into output schema"
                );
                if dialect == SqlDialect::Postgres {
                    assert!(
                        q.sql
                            .contains(r#"CAST("workflow_state" AS TEXT) AS "workflow_state""#)
                            && q.sql.contains("COLLATE \"C\"")
                            && q.sql.contains("BTRIM("),
                        "expected Postgres CAST AS TEXT, COLLATE \"C\", and BTRIM in:\n{}",
                        q.sql
                    );
                }
            }
            other => {
                return Err(format!("expected FullyPushed for {dialect:?}, got {other:?}").into());
            }
        }
    }

    Ok(())
}

#[test]
#[ignore = "requires live PostgreSQL server via DANA_TEST_POSTGRES_URL"]
fn v062_postgres_live_custom_enum_pushdown() -> TestResult {
    let url = std::env::var("DANA_TEST_POSTGRES_URL").map_err(
        |_| "DANA_TEST_POSTGRES_URL must be set to run v062_postgres_live_custom_enum_pushdown",
    )?;
    let tmp = TempDir::new("v062_live_pg_enum")?;
    let schema_name = format!(
        "dana_v062_enum_{}_{}",
        std::process::id(),
        TMP_COUNTER.fetch_add(1, Ordering::Relaxed)
    );
    let lock_path = tmp.path().join("schema.lock");

    {
        let mut pg = open_connection(&url)?;
        pg.execute(
            &format!(r#"DROP SCHEMA IF EXISTS "{schema_name}" CASCADE"#),
            &[],
        )?;
        pg.execute(&format!(r#"CREATE SCHEMA "{schema_name}""#), &[])?;
        pg.execute(
            &format!(
                r#"CREATE TYPE "{schema_name}"."wf_state" AS ENUM ('active', 'deleted', 'invited')"#
            ),
            &[],
        )?;
        pg.execute(
            &format!(
                r#"CREATE TABLE "{schema_name}"."enrollments" (
                    "id" BIGINT PRIMARY KEY,
                    "uid" BIGINT NOT NULL,
                    "workflow_state" "{schema_name}"."wf_state",
                    "ext_id" UUID,
                    "meta" JSONB,
                    "start_raw" TEXT
                )"#
            ),
            &[],
        )?;
        pg.execute(
            &format!(
                r#"INSERT INTO "{schema_name}"."enrollments" VALUES
                    (1, 100, 'active', '11111111-1111-1111-1111-111111111111', '{{"k":1}}', '2025-01-15T12:00:00Z'),
                    (2, 100, 'deleted', '22222222-2222-2222-2222-222222222222', '{{"k":2}}', '2025-01-16T12:00:00Z'),
                    (3, 200, NULL, NULL, NULL, '2025-02-01'),
                    (4, 200, 'invited', '44444444-4444-4444-4444-444444444444', '{{"k":4}}', '2025-02-02'),
                    (5, 300, 'invited', '55555555-5555-5555-5555-555555555555', '{{"k":5}}', 'invalid')"#
            ),
            &[],
        )?;
    }

    let sync = Command::new(env!("CARGO_BIN_EXE_dana"))
        .args([
            "schema-sync",
            "--db",
            &format!("PG={url}"),
            "--schemas",
            &schema_name,
            "--out",
            &lock_path.display().to_string(),
        ])
        .output()?;
    if sync.status.code() != Some(0) {
        let _ = open_connection(&url).and_then(|mut pg| {
            pg.execute(
                &format!(r#"DROP SCHEMA IF EXISTS "{schema_name}" CASCADE"#),
                &[],
            )
        });
        return Err(format!(
            "dana schema-sync failed: {}",
            String::from_utf8_lossy(&sync.stderr)
        )
        .into());
    }

    let lock = dana::db::schema_lock::parse_schema_lock(&fs::read_to_string(&lock_path)?)?;
    let src = format!(
        r##"module LivePgEnumPushdown

schema Enroll
  id: Int
  uid: Int
  workflow_state: Text?
  ext_id: Text?
  meta: Text?
  start_raw: Text?
end

fn main(db: ReadDB(PG), console: Console) : Int
  res = db.table(Enroll, from: "{schema_name}.enrollments")
    |> where(.workflow_state != "deleted" and not .workflow_state.in?(["deleted"]))
    |> derive(start_d: (.start_raw ?? "").slice(0, 10).try_parse_date)
    |> where(.start_d.some?)
    |> dedupe_by(.uid, order_by: [asc(.workflow_state), desc(.id)])
    |> sort_by(.uid)
  for r in res
    console.print("#{{r.id}}:#{{r.uid}}:#{{r.workflow_state}}:#{{r.ext_id}}:#{{r.start_d}}")
  end
  0
end
"##
    );

    let test_res = (|| -> TestResult {
        let checked = check_src_with_lock(&src, &lock)?;
        let main_fn = checked.exec.find_fun("main").ok_or("missing main")?;
        let plan = find_first_plan(&main_fn.body).ok_or("missing ExecPlan")?;
        let sp =
            split_exec_plan_pushdown(plan, &checked.exec, "PG", SqlDialect::Postgres, Some(&lock));
        match sp {
            SplitPlan::FullyPushed(q) => {
                assert!(
                    q.sql.contains("SELECT DISTINCT ON")
                        && q.sql.contains(r#"CAST("workflow_state" AS TEXT)"#),
                    "expected FullyPushed custom-ENUM PG SQL:\n{}",
                    q.sql
                );
            }
            other => {
                return Err(format!("expected FullyPushed live PG SQL, got {other:?}").into());
            }
        }
        let out = assert_oracle_vm_parity(&src, Some(("PG", &url)))?;
        assert_eq!(
            out,
            vec![
                "1:100:active:11111111-1111-1111-1111-111111111111:2025-01-15",
                "3:200:none:none:2025-02-01",
            ]
        );
        Ok(())
    })();

    let _ = open_connection(&url).and_then(|mut pg| {
        pg.execute(
            &format!(r#"DROP SCHEMA IF EXISTS "{schema_name}" CASCADE"#),
            &[],
        )
    });

    test_res
}

// ===========================================================================
// Patch v0.6.3 Tests: Join RHS distinct, SuppressSmallGroups Summarize pushdown,
// and Pure Table-Helper Inlining / LetE DB-Plan Fusion
// ===========================================================================

#[test]
fn v063_join_right_distinct_suppress_small_groups_and_helper_inlining() -> TestResult {
    let tmp = TempDir::new("v063_single_query")?;
    let db_path = tmp.path().join("pilot.db");
    let uri = sqlite_uri(&db_path);
    let mut conn = open_connection(&uri)?;
    for stmt in [
        "CREATE TABLE enrollments (
            id INTEGER PRIMARY KEY,
            sid TEXT NOT NULL,
            oid TEXT NOT NULL,
            term_id TEXT NOT NULL,
            cutoff_day TEXT NOT NULL,
            failed INTEGER NOT NULL
        )",
        "CREATE TABLE canvas_users (
            uid INTEGER PRIMARY KEY,
            sid TEXT,
            state TEXT NOT NULL
        )",
        "CREATE TABLE canvas_courses (
            cid INTEGER PRIMARY KEY,
            oid TEXT,
            state TEXT NOT NULL
        )",
        "INSERT INTO enrollments VALUES
            (1, 'S1', 'O1', 'T1', '2025-10-01', 0),
            (2, 'S1', 'O2', 'T1', '2025-10-01', 1),
            (3, 'S2', 'O1', 'T1', '2025-10-01', 0),
            (4, 'S3', 'O9', 'T1', '2025-10-01', 1),
            (5, 'S4', 'O1', 'T1', '2025-10-01', 0),
            (6, 'S5', 'O1', 'T1', '2025-10-01', 0),
            (7, 'S6', 'O1', 'T2', '2025-10-01', 0),
            (8, 'S6', 'O2', 'T2', '2025-10-01', 0),
            (9, 'S7', 'O1', 'T3', '2025-10-01', 1),
            (10, 'S8', 'O1', 'T3', '2025-10-01', 0),
            (11, 'S9', 'O1', 'T3', '2025-10-01', 0),
            (12, 'S10', 'O1', 'T3', '2025-10-01', 0),
            (13, 'S11', 'O1', 'T3', '2025-10-01', 0),
            (14, 'S12', 'O1', 'T4', '2026-06-01', 1)",
        "INSERT INTO canvas_users VALUES
            (1, 'S1', 'active'),
            (2, 'S1', 'active'),
            (3, 'S2', 'active'),
            (4, 'S4', 'deleted'),
            (5, 'S5', 'active'),
            (6, 'S6', 'active'),
            (7, 'S7', 'active'),
            (8, 'S8', 'active'),
            (9, 'S9', 'active'),
            (10, 'S10', 'active')",
        "INSERT INTO canvas_courses VALUES
            (1, 'O1', 'available'),
            (2, 'O1', 'available'),
            (3, 'O2', 'available'),
            (4, 'O9', 'deleted')",
    ] {
        conn.execute(stmt, &[])?;
    }

    // 1. Helper with `let pseudo = ... |> distinct()` + `let cc = ... |> distinct()` +
    //    `left_join_many_to_one` inlined into ungrouped + grouped (Drop & MaskComplementary)
    //    and empty-result + all-NULL distinct_by cases.
    let src = r##"
module V063JoinSuppress

schema Enrollment
  id: Int
  sid: Text [pii]
  oid: Text
  term_id: Text
  cutoff_day: Text
  failed: Int
end

schema CanvasUser
  uid: Int
  sid: Text? [pii]
  state: Text
end

schema CanvasCourse
  cid: Int
  oid: Text?
  state: Text
end

fn joined_enrollments(db: ReadDB(DB), cutoff_date: Date)
  pseudo = (db.table(CanvasUser, from: "canvas_users")
    |> where(.sid.some? and .state != "deleted")
    |> derive(matched_sid: .sid ?? "")
    |> select(.matched_sid)
    |> distinct())

  cc = (db.table(CanvasCourse, from: "canvas_courses")
    |> where(.oid.some? and .state != "deleted")
    |> derive(matched_oid: .oid ?? "")
    |> select(.matched_oid)
    |> distinct())

  db.table(Enrollment, from: "enrollments")
    |> derive(cday_opt: .cutoff_day.try_parse_date)
    |> where(.cday_opt.some?)
    |> derive(cday: .cday_opt ?? 1970-01-01)
    |> where(.cday < cutoff_date)
    |> left_join_many_to_one(pseudo, on: left.sid == right.matched_sid)
    |> left_join_many_to_one(cc, on: left.oid == right.matched_oid)
    |> derive(has_u: .matched_sid.some?, has_c: .matched_oid.some?)
    |> select(.sid, .term_id, .failed, .has_u, .has_c)
end

fn compute_cov(db: ReadDB(DB), before: Date)
  joined_enrollments(db, before)
    |> summarize(
      uniq_s: count_distinct(.sid),
      rows_n: count(),
      u_hits: count_if(.has_u),
      c_hits: count_if(.has_c)
    )
    |> suppress_small_groups(min: 5, distinct_by: .sid)
end

fn compute_terms_drop(db: ReadDB(DB), before: Date)
  joined_enrollments(db, before)
    |> group_by(.term_id)
    |> summarize(uniq_s: count_distinct(.sid), rows_n: count())
    |> suppress_small_groups(min: 5, distinct_by: .sid)
    |> sort_by(.term_id)
end

fn compute_terms_mask(db: ReadDB(DB), before: Date)
  joined_enrollments(db, before)
    |> group_by(.term_id)
    |> summarize(uniq_s: count_distinct(.sid), rows_n: count())
    |> suppress_small_groups(min: 5, distinct_by: .sid, mode: :mask)
    |> sort_by(.term_id)
end

fn main(db: ReadDB(DB), console: Console) : Int
  cov = compute_cov(db, 2026-01-01)
  cov_empty = compute_cov(db, 2020-01-01)
  td = compute_terms_drop(db, 2026-01-01)
  tm = compute_terms_mask(db, 2026-01-01)
  for r in cov
    console.print("cov:#{r.uniq_s}:#{r.rows_n}:#{r.u_hits}:#{r.c_hits}")
  end
  console.print("empty:#{cov_empty.count()}")
  for r in td
    console.print("drop:#{r.term_id}:#{r.uniq_s}:#{r.rows_n}")
  end
  for r in tm
    console.print("mask:#{r.term_id}:#{r.uniq_s ?? -1}:#{r.rows_n ?? -1}")
  end
  0
end
"##;

    let out = assert_oracle_vm_parity(src, Some(("DB", &uri)))?;
    assert_eq!(
        out,
        vec![
            "cov:11:13:10:12",
            "empty:0",
            "drop:T1:5:6",
            "drop:T3:5:5",
            "mask:T1:-1:-1",
            "mask:T2:-1:-1",
            "mask:T3:5:5",
        ]
    );

    // Verify optimizer + pushdown produces a single pushed SQL query per pipeline
    let checked = check_src(src)?;
    let (opt_prog, _) = dana::plan::optimize_exec_program(&checked.exec);
    for (fn_name, expect_meta) in [
        ("compute_cov", true),
        ("compute_terms_drop", true),
        ("compute_terms_mask", true),
    ] {
        let f = opt_prog
            .find_fun(fn_name)
            .ok_or_else(|| format!("missing fn {fn_name}"))?;
        let plan = find_first_plan(&f.body).ok_or_else(|| format!("missing plan in {fn_name}"))?;
        let sp = split_exec_plan_pushdown(plan, &opt_prog, "DB", SqlDialect::Sqlite, None);
        match sp {
            SplitPlan::Hybrid {
                pushdown,
                local_suffix,
                ..
            } => {
                assert!(
                    pushdown.sql.contains("SELECT DISTINCT")
                        && pushdown.sql.contains("LEFT JOIN")
                        && pushdown.sql.contains("COUNT(*)"),
                    "expected single joined SQL query with DISTINCT & COUNT(*) in {fn_name}:\n{}",
                    pushdown.sql
                );
                if expect_meta {
                    assert!(
                        pushdown.sql.contains("__dana_gm_rows")
                            && pushdown.sql.contains("__dana_gm_dist"),
                        "expected hidden group meta columns in {fn_name}:\n{}",
                        pushdown.sql
                    );
                }
                assert!(
                    !pushdown
                        .boundary_reason
                        .as_deref()
                        .unwrap_or("")
                        .contains("order-preserving distinct"),
                    "unexpected distinct boundary in {fn_name}: {:?}",
                    pushdown.boundary_reason
                );
                assert!(
                    matches!(
                        local_suffix,
                        dana::runtime::ir::ExecPlan::SuppressSmallGroups { .. }
                            | dana::runtime::ir::ExecPlan::Sort { .. }
                    ),
                    "expected only SuppressSmallGroups/Sort in local suffix for {fn_name}"
                );
            }
            other => {
                return Err(format!(
                    "expected Hybrid single-query SQL in {fn_name}, got {other:?}"
                )
                .into());
            }
        }
    }

    // Verify `dana explain` CLI output uses optimized helper inlining and has no distinct boundary
    let explain_path = tmp.path().join("explain_v063.dana");
    fs::write(&explain_path, src)?;
    let explain_out = Command::new(env!("CARGO_BIN_EXE_dana"))
        .args(["explain", "--dialect", "sqlite"])
        .arg(&explain_path)
        .output()?;
    assert_eq!(explain_out.status.code(), Some(0));
    let explain_txt = String::from_utf8_lossy(&explain_out.stdout);
    assert!(
        explain_txt.contains("__dana_gm_rows") && explain_txt.contains("__dana_gm_dist"),
        "expected hidden group meta in dana explain:\n{explain_txt}"
    );
    assert!(
        !explain_txt.contains("order-preserving distinct requires local VM"),
        "unexpected distinct boundary in dana explain:\n{explain_txt}"
    );

    // 2. All-NULL distinct_by group suppresses cleanly (SQL COUNT(DISTINCT) == 0 == local tracker)
    let src_all_null = r##"
module V063AllNull

schema NullRec
  grp: Text
  uid: Int?
end

fn main(db: ReadDB(DB), console: Console) : Int
  res = (db.table(NullRec, from: "null_recs")
    |> group_by(.grp)
    |> summarize(u: count_distinct(.uid), n: count())
    |> suppress_small_groups(min: 5, distinct_by: .uid)
    |> sort_by(.grp))
  for r in res
    console.print("#{r.grp}:#{r.u}:#{r.n}")
  end
  0
end
"##;
    conn.execute(
        "CREATE TABLE null_recs (grp TEXT NOT NULL, uid INTEGER)",
        &[],
    )?;
    conn.execute(
        "INSERT INTO null_recs VALUES ('A', NULL), ('A', NULL), ('A', NULL), ('A', NULL), ('A', NULL), ('B', 1), ('B', 2), ('B', 3), ('B', 4), ('B', 5)",
        &[],
    )?;
    let null_out = assert_oracle_vm_parity(src_all_null, Some(("DB", &uri)))?;
    assert_eq!(null_out, vec!["B:5:5"]);

    // 3. Function with failing `promise` must NOT be bypassed by inlining
    let src_promise = r#"
module V063Promise

fn checked_pos() : Table(x: Int)
  promise all(.x > 0)
  table
    | x |
    | -1 |
  end
end

fn main() : Int
  t = checked_pos() |> summarize(n: count())
  t.count()
end
"#;
    assert_oracle_vm_trap_kind(src_promise, BugKind::PromiseViolation)?;

    Ok(())
}

#[test]
#[ignore = "requires live PostgreSQL instance (DANA_TEST_POSTGRES_URL)"]
fn v063_postgres_live_single_query_join_suppress_pushdown() -> TestResult {
    let url = std::env::var("DANA_TEST_POSTGRES_URL").map_err(
        |_| "DANA_TEST_POSTGRES_URL must be set to run live PostgreSQL v0.6.3 pushdown test",
    )?;
    let schema_name = format!("dana_v063_pg_{}", std::process::id());
    {
        let mut pg = open_connection(&url)?;
        pg.execute(
            &format!(r#"DROP SCHEMA IF EXISTS "{schema_name}" CASCADE"#),
            &[],
        )?;
        pg.execute(&format!(r#"CREATE SCHEMA "{schema_name}""#), &[])?;
        pg.execute(
            &format!(r#"CREATE TYPE "{schema_name}".wf_state AS ENUM ('active', 'deleted')"#),
            &[],
        )?;
        pg.execute(
            &format!(
                r#"CREATE TABLE "{schema_name}".enrollments (
                    id INTEGER PRIMARY KEY,
                    sid TEXT NOT NULL,
                    oid TEXT NOT NULL,
                    term_id TEXT NOT NULL,
                    term_end TEXT NOT NULL
                )"#
            ),
            &[],
        )?;
        pg.execute(
            &format!(
                r#"CREATE TABLE "{schema_name}".canvas_users (
                    uid INTEGER PRIMARY KEY,
                    sid TEXT,
                    state "{schema_name}".wf_state NOT NULL
                )"#
            ),
            &[],
        )?;
        pg.execute(
            &format!(
                r#"CREATE TABLE "{schema_name}".canvas_courses (
                    cid INTEGER PRIMARY KEY,
                    oid TEXT,
                    state "{schema_name}".wf_state NOT NULL
                )"#
            ),
            &[],
        )?;
        pg.execute(
            &format!(
                r#"INSERT INTO "{schema_name}".enrollments VALUES
                    (1, 'S1', 'O1', 'T1', '2025-11-15'),
                    (2, 'S2', 'O1', 'T1', '2025-11-15'),
                    (3, 'S3', 'O2', 'T1', '2025-11-15'),
                    (4, 'S4', 'O1', 'T1', '2025-11-15'),
                    (5, 'S5', 'O1', 'T1', '2025-11-15'),
                    (6, 'S6', 'O1', 'T2', '2025-11-15'),
                    (7, 'S7', 'O1', 'T3', '2026-05-01')"#
            ),
            &[],
        )?;
        pg.execute(
            &format!(
                r#"INSERT INTO "{schema_name}".canvas_users VALUES
                    (1, 'S1', 'active'),
                    (2, 'S1', 'active'),
                    (3, 'S2', 'active'),
                    (4, 'S4', 'deleted'),
                    (5, 'S5', 'active')"#
            ),
            &[],
        )?;
        pg.execute(
            &format!(
                r#"INSERT INTO "{schema_name}".canvas_courses VALUES
                    (1, 'O1', 'active'),
                    (2, 'O1', 'active'),
                    (3, 'O2', 'deleted')"#
            ),
            &[],
        )?;
    }

    let test_res: TestResult = (|| {
        let src = format!(
            r##"
module V063PgLive

schema Enrollment
  id: Int
  sid: Text [pii]
  oid: Text
  term_id: Text
  term_end: Text
end

schema CanvasUser
  uid: Int
  sid: Text? [pii]
  state: Text
end

schema CanvasCourse
  cid: Int
  oid: Text?
  state: Text
end

fn online_enr(db: ReadDB(PG), cutoff: Date)
  pseudo = (db.table(CanvasUser, from: "{schema_name}.canvas_users")
    |> where(.sid.some? and .state != "deleted")
    |> derive(matched_sid: .sid ?? "")
    |> select(.matched_sid)
    |> distinct())

  cc = (db.table(CanvasCourse, from: "{schema_name}.canvas_courses")
    |> where(.oid.some? and .state != "deleted")
    |> derive(matched_oid: .oid ?? "")
    |> select(.matched_oid)
    |> distinct())

  db.table(Enrollment, from: "{schema_name}.enrollments")
    |> derive(end_opt: .term_end.try_parse_date)
    |> where(.end_opt.some?)
    |> derive(term_end_d: .end_opt ?? 1970-01-01)
    |> where(.term_end_d < cutoff)
    |> left_join_many_to_one(pseudo, on: left.sid == right.matched_sid)
    |> left_join_many_to_one(cc, on: left.oid == right.matched_oid)
    |> derive(has_u: .matched_sid.some?, has_c: .matched_oid.some?)
    |> select(.sid, .term_id, .has_u, .has_c)
end

fn coverage(db: ReadDB(PG), before: Date)
  online_enr(db, before)
    |> summarize(
      uniq_s: count_distinct(.sid),
      rows_n: count(),
      u_hits: count_if(.has_u),
      c_hits: count_if(.has_c)
    )
    |> suppress_small_groups(min: 5, distinct_by: .sid)
end

fn terms_sorted(db: ReadDB(PG), before: Date)
  online_enr(db, before)
    |> group_by(.term_id)
    |> summarize(uniq_s: count_distinct(.sid), rows_n: count())
    |> suppress_small_groups(min: 5, distinct_by: .sid)
    |> sort_by(.term_id)
end

fn main(db: ReadDB(PG), console: Console) : Int
  cov = coverage(db, 2026-01-01)
  trm = terms_sorted(db, 2026-01-01)
  for r in cov
    console.print("cov:#{{r.uniq_s}}:#{{r.rows_n}}:#{{r.u_hits}}:#{{r.c_hits}}")
  end
  for r in trm
    console.print("term:#{{r.term_id}}:#{{r.uniq_s}}:#{{r.rows_n}}")
  end
  0
end
"##
        );

        let checked = check_src(&src)?;
        let (opt_prog, _) = dana::plan::optimize_exec_program(&checked.exec);
        for fn_name in ["coverage", "terms_sorted"] {
            let f = opt_prog
                .find_fun(fn_name)
                .ok_or_else(|| format!("missing fn {fn_name}"))?;
            let plan =
                find_first_plan(&f.body).ok_or_else(|| format!("missing plan in {fn_name}"))?;
            let sp = split_exec_plan_pushdown(plan, &opt_prog, "PG", SqlDialect::Postgres, None);
            match sp {
                SplitPlan::Hybrid { pushdown, .. } => {
                    assert!(
                        pushdown.sql.contains("SELECT DISTINCT")
                            && pushdown.sql.contains("LEFT JOIN")
                            && pushdown.sql.contains("__dana_gm_rows")
                            && pushdown.sql.contains("__dana_gm_dist"),
                        "expected single PG query with DISTINCT & hidden meta in {fn_name}:\n{}",
                        pushdown.sql
                    );
                }
                other => {
                    return Err(format!(
                        "expected Hybrid single PG query in {fn_name}, got {other:?}"
                    )
                    .into());
                }
            }
        }

        let out = assert_oracle_vm_parity(&src, Some(("PG", &url)))?;
        assert_eq!(out, vec!["cov:6:6:3:5", "term:T1:5:5"]);
        Ok(())
    })();

    let _ = open_connection(&url).and_then(|mut pg| {
        pg.execute(
            &format!(r#"DROP SCHEMA IF EXISTS "{schema_name}" CASCADE"#),
            &[],
        )
    });

    test_res
}

#[test]
fn v063_deep_pipeline_cte_linearization_sqlite_and_postgres() -> TestResult {
    let tmp = TempDir::new("v063_cte_linearize")?;
    let db_path = tmp.path().join("deep.db");
    let uri = sqlite_uri(&db_path);
    let mut conn = open_connection(&uri)?;
    for stmt in [
        "CREATE TABLE populi_enr (
            sid TEXT NOT NULL,
            tid TEXT NOT NULL,
            tname TEXT NOT NULL,
            tstart TEXT NOT NULL,
            tend TEXT NOT NULL,
            oid TEXT NOT NULL,
            campus TEXT NOT NULL,
            status TEXT NOT NULL,
            grade TEXT,
            finalized TEXT NOT NULL
        )",
        "CREATE TABLE canvas_users (sid TEXT, state TEXT)",
        "CREATE TABLE canvas_courses (oid TEXT, state TEXT)",
        "INSERT INTO populi_enr VALUES
            ('S1', '201', 'Fall', '2025-09-01T00:00:00Z', '2025-11-15T00:00:00Z', 'O1', 'Online Campus', 'ENROLLED', 'A', '1'),
            ('S2', '201', 'Fall', '2025-09-01T00:00:00Z', '2025-11-15T00:00:00Z', 'O1', 'Online Campus', 'ENROLLED', 'F', '1'),
            ('S3', '201', 'Fall', '2025-09-01T00:00:00Z', '2025-11-15T00:00:00Z', 'O2', 'Online Campus', 'WITHDRAWN', NULL, '0'),
            ('S4', '201', 'Fall', '2025-09-01T00:00:00Z', '2025-11-15T00:00:00Z', 'O1', 'Online Campus', 'ENROLLED', 'B', '1'),
            ('S5', '201', 'Fall', '2025-09-01T00:00:00Z', '2025-11-15T00:00:00Z', 'O1', 'Online Campus', 'ENROLLED', 'D', '1'),
            ('S6', '202', 'Spring', '2026-09-01T00:00:00Z', '2026-12-15T00:00:00Z', 'O1', 'Online Campus', 'ENROLLED', 'A', '1')",
        "INSERT INTO canvas_users VALUES ('S1', 'active'), ('S1', 'active'), ('S2', 'active'), ('S4', 'deleted')",
        "INSERT INTO canvas_courses VALUES ('O1', 'available'), ('O1', 'completed'), ('O2', 'deleted')",
    ] {
        conn.execute(stmt, &[])?;
    }

    let src = r##"
module V063DeepCte

schema Enr
  sid: Text? [pii]
  tid: Text?
  tname: Text?
  tstart: Text?
  tend: Text?
  oid: Text?
  campus: Text?
  status: Text? [ferpa]
  grade: Text? [ferpa]
  finalized: Text? [ferpa]
end

schema CUser
  sid: Text? [pii]
  state: Text?
end

schema CCourse
  oid: Text?
  state: Text?
end

fn online(db: ReadDB(DB), cutoff: Date)
  pseudo = (db.table(CUser, from: "canvas_users")
    |> where(.sid.some? and (.sid ?? "") != "" and .state.some? and .state != "deleted")
    |> derive(matched_sid: .sid ?? "")
    |> select(.matched_sid)
    |> distinct())

  cc = (db.table(CCourse, from: "canvas_courses")
    |> where(.oid.some? and (.oid ?? "") != "" and .state.some? and .state != "deleted")
    |> derive(matched_oid: .oid ?? "")
    |> select(.matched_oid)
    |> distinct())

  db.table(Enr, from: "populi_enr")
    |> where(
      (.campus ?? "") == "Online Campus"
        and (.status ?? "").in?(["ENROLLED", "WITHDRAWN", "INCOMPLETE"])
        and not (.grade ?? "").in?(["NGC", "PN", "WAIV", "APPR"])
    )
    |> derive(
      s_id: .sid ?? "",
      t_id: .tid ?? "",
      t_name: .tname ?? "",
      t_start_opt: (.tstart ?? "").slice(0, 10).try_parse_date,
      t_end_opt: (.tend ?? "").slice(0, 10).try_parse_date,
      o_id: .oid ?? "",
      is_dfw: (.status ?? "") == "WITHDRAWN" or ((.finalized ?? "") == "1" and (.grade ?? "").in?(["F", "UF", "D+", "D", "D-"])),
      is_wd: (.status ?? "") == "WITHDRAWN",
      is_fail: (.finalized ?? "") == "1" and (.grade ?? "").in?(["F", "UF"])
    )
    |> where(.t_start_opt.some? and .t_end_opt.some?)
    |> derive(term_start: .t_start_opt ?? 1970-01-01, term_end: .t_end_opt ?? 1970-01-01)
    |> where(.term_end < cutoff)
    |> left_join_many_to_one(pseudo, on: left.s_id == right.matched_sid)
    |> left_join_many_to_one(cc, on: left.o_id == right.matched_oid)
    |> derive(has_u: .matched_sid.some?, has_c: .matched_oid.some?)
    |> select(.sid, .tid, .t_id, .t_name, .term_start, .term_end, .is_dfw, .is_wd, .is_fail, .has_u, .has_c)
end

fn main(db: ReadDB(DB), console: Console) : Int
  cov = (online(db, 2026-06-01)
    |> summarize(
      uniq_s: count_distinct(.sid),
      rows_n: count(),
      dfw_n: count_if(.is_dfw),
      u_hits: count_if(.has_u),
      c_hits: count_if(.has_c)
    )
    |> suppress_small_groups(min: 5, distinct_by: .sid))
  for r in cov
    console.print("cov:#{r.uniq_s}:#{r.rows_n}:#{r.dfw_n}:#{r.u_hits}:#{r.c_hits}")
  end
  0
end
"##;

    let checked = check_src(src)?;
    let (opt_prog, _) = dana::plan::optimize_exec_program(&checked.exec);
    let f = opt_prog.find_fun("main").ok_or("missing main")?;
    let plan = find_first_plan(&f.body).ok_or("missing plan")?;
    for dialect in [SqlDialect::Sqlite, SqlDialect::Postgres] {
        match split_exec_plan_pushdown(plan, &opt_prog, "DB", dialect, None) {
            SplitPlan::Hybrid { pushdown, .. } => {
                assert!(
                    pushdown.sql.starts_with(r#"WITH "_cte_0" AS ("#),
                    "expected flat WITH CTE SQL for {dialect}:\n{}",
                    pushdown.sql
                );
            }
            other => return Err(format!("expected Hybrid SQL for {dialect}, got {other:?}").into()),
        }
    }

    let out = assert_oracle_vm_parity(src, Some(("DB", &uri)))?;
    assert_eq!(out, vec!["cov:5:5:3:2:4"]);
    Ok(())
}

// ===========================================================================
// Patch v0.6.4 Tests: PostgreSQL Materialized ISO CTEs, Derive Wave Coalescing,
// and MCV-Histogram-Friendly COALESCE Predicates
// ===========================================================================

#[test]
fn v064_postgres_materialized_iso_batch_derive_and_coalesce_mcv_rewrite() -> TestResult {
    let tmp = TempDir::new("v064_pushdown")?;
    let db_path = tmp.path().join("v064.db");
    let uri = sqlite_uri(&db_path);
    {
        let mut conn = open_connection(&uri)?;
        for stmt in [
            "CREATE TABLE populi_enr (
                sid TEXT,
                campus TEXT,
                status TEXT,
                grade TEXT,
                tstart TEXT,
                tend TEXT,
                oid TEXT,
                a INTEGER,
                b INTEGER
            )",
            "CREATE TABLE canvas_users (sid TEXT, state TEXT)",
            "CREATE TABLE canvas_courses (oid TEXT, state TEXT)",
            // Exercises NULL, \"\", matching, and non-matching values across all COALESCE 3VL cases.
            "INSERT INTO populi_enr VALUES
                ('S1', 'Online Campus', 'ENROLLED', 'A', '2025-09-01', '2025-11-15', 'O1', 10, 20),
                ('S2', 'Online Campus', 'WITHDRAWN', NULL, '2025-09-01', '2025-11-15', 'O1', 3, 4),
                ('S3', 'Online Campus', 'ENROLLED', '', '2025-09-01', '2025-11-15', 'O2', 5, 6),
                ('S4', 'Online Campus', 'ENROLLED', 'NGC', '2025-09-01', '2025-11-15', 'O1', 1, 2),
                ('S5', NULL, 'ENROLLED', 'A', '2025-09-01', '2025-11-15', 'O1', 2, 2),
                ('S6', '', 'ENROLLED', 'A', '2025-09-01', '2025-11-15', 'O1', 4, 2),
                ('S7', 'Online Campus', NULL, 'A', '2025-09-01', '2025-11-15', 'O1', 6, 2),
                ('S8', 'Online Campus', '', 'A', '2025-09-01', '2025-11-15', 'O1', 7, 2)",
            "INSERT INTO canvas_users VALUES ('S1', 'active'), ('S2', 'active'), ('S3', 'deleted')",
            "INSERT INTO canvas_courses VALUES ('O1', 'available'), ('O2', 'deleted')",
        ] {
            conn.execute(stmt, &[])?;
        }
    }

    let src = r##"
module V064Pushdown

schema Enr
  sid: Text?
  campus: Text?
  status: Text?
  grade: Text?
  tstart: Text?
  tend: Text?
  oid: Text?
  a: Int
  b: Int
end

schema CUser
  sid: Text?
  state: Text?
end

schema CCourse
  oid: Text?
  state: Text?
end

fn wts_like(db: ReadDB(DB), cutoff: Date)
  pseudo = (db.table(CUser, from: "canvas_users")
    |> where(.sid.some? and (.sid ?? "") != "" and .state.some? and .state != "deleted")
    |> derive(matched_sid: .sid ?? "")
    |> select(.matched_sid)
    |> distinct())

  cc = (db.table(CCourse, from: "canvas_courses")
    |> where(.oid.some? and (.oid ?? "") != "" and .state.some? and .state != "deleted")
    |> derive(matched_oid: .oid ?? "")
    |> select(.matched_oid)
    |> distinct())

  db.table(Enr, from: "populi_enr")
    |> where(
      (.campus ?? "") == "Online Campus"
        and (.status ?? "").in?(["ENROLLED", "WITHDRAWN", "INCOMPLETE"])
        and not (.grade ?? "").in?(["NGC", "PN", "WAIV", "APPR"])
    )
    |> derive(
      s_id: .sid ?? "",
      o_id: .oid ?? "",
      t_start_opt: (.tstart ?? "").slice(0, 10).try_parse_date,
      t_end_opt: (.tend ?? "").slice(0, 10).try_parse_date,
      flag_a: (.status ?? "") == "WITHDRAWN",
      flag_b: (.grade ?? "") == "A",
      tag_x: (.status ?? "").lower,
      dep_match: .tag_x == "enrolled" and .s_id == "S1",
      status: "OVERWRITTEN"
    )
    |> where(.t_start_opt.some? and .t_end_opt.some?)
    |> derive(term_start: .t_start_opt ?? 1970-01-01, term_end: .t_end_opt ?? 1970-01-01)
    |> where(.term_end < cutoff)
    |> left_join_many_to_one(pseudo, on: left.s_id == right.matched_sid)
    |> left_join_many_to_one(cc, on: left.o_id == right.matched_oid)
    |> derive(has_u: .matched_sid.some?, has_c: .matched_oid.some?)
    |> select(.flag_a, .flag_b, .dep_match, .status, .has_u, .has_c)
end

fn wts_summary(db: ReadDB(DB), cutoff: Date)
  wts_like(db, cutoff)
    |> summarize(
      n: count(),
      dfw_n: count_if(.flag_a),
      a_grade_n: count_if(.flag_b),
      dep_n: count_if(.dep_match),
      ov_n: count_if(.status == "OVERWRITTEN"),
      u_hits: count_if(.has_u),
      c_hits: count_if(.has_c)
    )
end

fn three_vl_probe(db: ReadDB(DB))
  # Tests all 6 COALESCE 3VL combinations: d==t / d!=t across =, !=, IN, and NOT(IN).
  db.table(Enr, from: "populi_enr")
    |> where(
      ((.campus ?? "") == "" or (.campus ?? "") == "Online Campus")
        and (.status ?? "") != ""
        and (.campus ?? "") != "Main Campus"
        and not (.grade ?? "").in?(["NGC", ""])
    )
    |> select(.a, .campus, .status, .grade)
    |> sort_by(.a)
end

fn main(db: ReadDB(DB), console: Console) : Int
  for r in wts_summary(db, 2026-06-01)
    console.print("s:#{r.n}:#{r.dfw_n}:#{r.a_grade_n}:#{r.dep_n}:#{r.ov_n}:#{r.u_hits}:#{r.c_hits}")
  end
  for r in three_vl_probe(db)
    console.print("p:#{r.campus}:#{r.status}:#{r.grade}")
  end
  0
end
"##;

    let checked = check_src(src)?;
    let (opt_prog, _) = dana::plan::optimize_exec_program(&checked.exec);

    let f_wts = opt_prog
        .find_fun("wts_summary")
        .ok_or("missing wts_summary")?;
    let p_wts = find_first_plan(&f_wts.body).ok_or("missing wts_summary plan")?;

    let pg_q = match split_exec_plan_pushdown(p_wts, &opt_prog, "DB", SqlDialect::Postgres, None) {
        SplitPlan::FullyPushed(q) => q,
        other => return Err(format!("expected FullyPushed for Postgres, got {other:?}").into()),
    };
    let sq_q = match split_exec_plan_pushdown(p_wts, &opt_prog, "DB", SqlDialect::Sqlite, None) {
        SplitPlan::FullyPushed(q) => q,
        other => return Err(format!("expected FullyPushed for SQLite, got {other:?}").into()),
    };

    // 1. SQLite must never emit PostgreSQL's `AS MATERIALIZED (`.
    assert!(
        !sq_q.sql.contains("MATERIALIZED"),
        "SQLite SQL must not contain MATERIALIZED:\n{}",
        sq_q.sql
    );

    // 2. Postgres must materialize the batched `_dana_iso_*` CTE once with both BTRIM expressions.
    assert_eq!(
        pg_q.sql.matches("AS MATERIALIZED (").count(),
        1,
        "expected exactly 1 AS MATERIALIZED CTE bundling both ISO date trims in Postgres:\n{}",
        pg_q.sql
    );
    let mat_body = pg_q
        .sql
        .split("AS MATERIALIZED (")
        .nth(1)
        .and_then(|s| s.split("), \"").next())
        .ok_or("missing materialized CTE body")?;
    assert_eq!(
        mat_body.matches("BTRIM(").count(),
        2,
        "expected both ISO date BTRIMs bundled inside single AS MATERIALIZED CTE:\n{mat_body}"
    );
    assert_eq!(
        mat_body.matches("\"_dana_iso_").count(),
        2,
        "expected 2 hoisted _dana_iso_* aliases inside single AS MATERIALIZED CTE:\n{mat_body}"
    );

    // 3. Independent derive wave coalescing keeps CTE count well below uncoalesced count (~26+).
    let cte_defs =
        pg_q.sql.matches(" AS (").count() + pg_q.sql.matches("AS MATERIALIZED (").count();
    assert!(
        cte_defs <= 20,
        "expected coalesced CTE count <= 20, got {cte_defs}:\n{}",
        pg_q.sql
    );

    // 4. COALESCE filter predicates were simplified away from COALESCE(...) for MCV stats.
    assert!(
        !pg_q.sql.contains("COALESCE(\"campus\"")
            && pg_q.sql.contains("\"campus\" IS NOT NULL")
            && pg_q.sql.contains("\"status\" IS NOT NULL")
            && pg_q.sql.contains("\"grade\" IS NOT NULL"),
        "expected COALESCE equality/IN predicates simplified to MCV-friendly IS NOT NULL/IS NULL:\n{}",
        pg_q.sql
    );

    let f_probe = opt_prog
        .find_fun("three_vl_probe")
        .ok_or("missing three_vl_probe")?;
    let p_probe = find_first_plan(&f_probe.body).ok_or("missing three_vl_probe plan")?;
    let probe_pg =
        match split_exec_plan_pushdown(p_probe, &opt_prog, "DB", SqlDialect::Postgres, None) {
            SplitPlan::Hybrid { pushdown, .. } => pushdown,
            other => {
                return Err(format!("expected Hybrid pushdown for probe, got {other:?}").into());
            }
        };
    assert!(
        !probe_pg.sql.contains("COALESCE(")
            && probe_pg.sql.contains("\"campus\" IS NULL")
            && probe_pg.sql.contains("\"status\" IS NOT NULL")
            && probe_pg.sql.contains("\"grade\" IS NULL"),
        "expected zero COALESCE(...) calls in three_vl_probe Postgres WHERE SQL:\n{}",
        probe_pg.sql
    );

    // 5. Exact Oracle == VM == SQLite Pushdown parity across wts_summary and 6-way 3VL probe.
    let out = assert_oracle_vm_parity(src, Some(("DB", &uri)))?;
    assert_eq!(
        out,
        vec![
            "s:3:1:1:1:3:2:2",
            // three_vl_probe: only S1, S5, S6 survive:
            // S2 (grade=NULL) and S3 (grade='') are excluded because `""` is in `["NGC", ""]`,
            // testing `d in list` under `NOT`; S4 has 'NGC'; S7 (status=NULL) & S8 (status='') fail `!= ""`.
            // Sorted by `a`: S5 (a=2), S6 (a=4), S1 (a=10).
            "p:none:ENROLLED:A",
            "p::ENROLLED:A",
            "p:Online Campus:ENROLLED:A",
        ]
    );
    Ok(())
}

#[test]
#[ignore = "requires live PostgreSQL instance (DANA_TEST_POSTGRES_URL)"]
fn v064_postgres_live_hash_join_no_nested_loop_regression() -> TestResult {
    let url = std::env::var("DANA_TEST_POSTGRES_URL").map_err(
        |_| "DANA_TEST_POSTGRES_URL must be set to run live PostgreSQL v0.6.4 regression test",
    )?;
    let schema_name = format!("dana_v064_pg_{}", std::process::id());
    {
        let mut pg = open_connection(&url)?;
        pg.execute(
            &format!(r#"DROP SCHEMA IF EXISTS "{schema_name}" CASCADE"#),
            &[],
        )?;
        pg.execute(&format!(r#"CREATE SCHEMA "{schema_name}""#), &[])?;
        pg.execute(
            &format!(
                r#"CREATE TYPE "{schema_name}".wf_state AS ENUM ('active', 'available', 'deleted')"#
            ),
            &[],
        )?;
        pg.execute(
            &format!(
                r#"CREATE TABLE "{schema_name}".enrollments (
                    id INTEGER PRIMARY KEY,
                    sid VARCHAR(64),
                    tid VARCHAR(32),
                    tname VARCHAR(64),
                    tstart VARCHAR(32),
                    tend VARCHAR(32),
                    oid VARCHAR(64),
                    campus VARCHAR(64),
                    status VARCHAR(32),
                    grade VARCHAR(16),
                    finalized VARCHAR(8)
                )"#
            ),
            &[],
        )?;
        pg.execute(
            &format!(
                r#"CREATE TABLE "{schema_name}".canvas_users (
                    uid INTEGER PRIMARY KEY,
                    sid VARCHAR(64),
                    state "{schema_name}".wf_state
                )"#
            ),
            &[],
        )?;
        pg.execute(
            &format!(
                r#"CREATE TABLE "{schema_name}".canvas_courses (
                    cid INTEGER PRIMARY KEY,
                    oid VARCHAR(64),
                    state "{schema_name}".wf_state
                )"#
            ),
            &[],
        )?;
        pg.execute(
            &format!(
                r#"INSERT INTO "{schema_name}".enrollments
                   SELECT
                     g,
                     'S' || (1 + (g % 800))::text,
                     CASE WHEN g % 3 = 0 THEN 'T1' ELSE 'T2' END,
                     CASE WHEN g % 3 = 0 THEN '2025 Fall' ELSE '2026 Winter' END,
                     '2025-09-01T00:00:00Z',
                     CASE WHEN g % 10 = 0 THEN '2026-12-15T00:00:00Z' ELSE '2025-11-15T00:00:00Z' END,
                     'O' || (1 + (g % 300))::text,
                     CASE WHEN g % 4 = 0 THEN 'Main Campus' ELSE 'Online Campus' END,
                     CASE WHEN g % 5 = 0 THEN 'WITHDRAWN' ELSE 'ENROLLED' END,
                     CASE WHEN g % 7 = 0 THEN NULL WHEN g % 11 = 0 THEN 'NGC' ELSE 'A' END,
                     '1'
                   FROM generate_series(1, 5000) AS g"#
            ),
            &[],
        )?;
        pg.execute(
            &format!(
                r#"INSERT INTO "{schema_name}".canvas_users
                   SELECT
                     g,
                     'S' || (1 + (g % 700))::text,
                     (CASE WHEN g % 10 = 0 THEN 'deleted' ELSE 'active' END)::"{schema_name}".wf_state
                   FROM generate_series(1, 2000) AS g"#
            ),
            &[],
        )?;
        pg.execute(
            &format!(
                r#"INSERT INTO "{schema_name}".canvas_courses
                   SELECT
                     g,
                     'O' || (1 + (g % 250))::text,
                     (CASE WHEN g % 8 = 0 THEN 'deleted' ELSE 'available' END)::"{schema_name}".wf_state
                   FROM generate_series(1, 1000) AS g"#
            ),
            &[],
        )?;
        pg.execute(&format!(r#"ANALYZE "{schema_name}".enrollments"#), &[])?;
        pg.execute(&format!(r#"ANALYZE "{schema_name}".canvas_users"#), &[])?;
        pg.execute(&format!(r#"ANALYZE "{schema_name}".canvas_courses"#), &[])?;
    }

    let test_res: TestResult = (|| {
        let src = format!(
            r##"
module V064PgLiveHashJoin

schema Enrollment
  sid: Text? [pii]
  tid: Text?
  tname: Text?
  tstart: Text?
  tend: Text?
  oid: Text?
  campus: Text?
  status: Text? [ferpa]
  grade: Text? [ferpa]
  finalized: Text? [ferpa]
end

schema CanvasUser
  sid: Text? [pii]
  state: Text?
end

schema CanvasCourse
  oid: Text?
  state: Text?
end

fn online_enr(db: ReadDB(PG), completed_before: Date)
  pseudo = (db.table(CanvasUser, from: "{schema_name}.canvas_users")
    |> where(.sid.some? and (.sid ?? "") != "" and .state.some? and .state != "deleted")
    |> derive(matched_sid: .sid ?? "")
    |> select(.matched_sid)
    |> distinct())

  cc = (db.table(CanvasCourse, from: "{schema_name}.canvas_courses")
    |> where(.oid.some? and (.oid ?? "") != "" and .state.some? and .state != "deleted")
    |> derive(matched_oid: .oid ?? "")
    |> select(.matched_oid)
    |> distinct())

  db.table(Enrollment, from: "{schema_name}.enrollments")
    |> where(
      (.campus ?? "") == "Online Campus"
        and (.status ?? "").in?(["ENROLLED", "WITHDRAWN", "INCOMPLETE"])
        and not (.grade ?? "").in?(["NGC", "PN", "WAIV", "APPR"])
    )
    |> derive(
      s_id: .sid ?? "",
      t_id: .tid ?? "",
      t_name: .tname ?? "",
      t_start_opt: (.tstart ?? "").slice(0, 10).try_parse_date,
      t_end_opt: (.tend ?? "").slice(0, 10).try_parse_date,
      o_id: .oid ?? "",
      is_dfw: (.status ?? "") == "WITHDRAWN" or ((.finalized ?? "") == "1" and (.grade ?? "").in?(["F", "UF", "D+", "D", "D-"])),
      is_wd: (.status ?? "") == "WITHDRAWN",
      is_fail: (.finalized ?? "") == "1" and (.grade ?? "").in?(["F", "UF"])
    )
    |> where(.t_start_opt.some? and .t_end_opt.some?)
    |> derive(term_start: .t_start_opt ?? 1970-01-01, term_end: .t_end_opt ?? 1970-01-01)
    |> where(.term_end < completed_before)
    |> left_join_many_to_one(pseudo, on: left.s_id == right.matched_sid)
    |> left_join_many_to_one(cc, on: left.o_id == right.matched_oid)
    |> derive(has_u: .matched_sid.some?, has_c: .matched_oid.some?)
    |> select(.sid, .t_id, .t_name, .term_start, .term_end, .is_dfw, .has_u, .has_c)
end

fn coverage(db: ReadDB(PG), completed_before: Date)
  online_enr(db, completed_before)
    |> summarize(
      uniq_s: count_distinct(.sid),
      rows_n: count(),
      u_hits: count_if(.has_u),
      c_hits: count_if(.has_c)
    )
    |> suppress_small_groups(min: 10, distinct_by: .sid)
end

fn main(db: ReadDB(PG), console: Console) : Int
  for r in coverage(db, 2026-06-01)
    console.print("cov:#{{r.uniq_s}}:#{{r.rows_n}}:#{{r.u_hits}}:#{{r.c_hits}}")
  end
  0
end
"##
        );

        let checked = check_src(&src)?;
        let (opt_prog, _) = dana::plan::optimize_exec_program(&checked.exec);
        let cov_fn = opt_prog.find_fun("coverage").ok_or("missing coverage")?;
        let plan = find_first_plan(&cov_fn.body).ok_or("missing coverage plan")?;
        let sp = split_exec_plan_pushdown(plan, &opt_prog, "PG", SqlDialect::Postgres, None);
        let pushdown = match sp {
            SplitPlan::Hybrid { pushdown, .. } => pushdown,
            other => return Err(format!("expected Hybrid pushdown, got {other:?}").into()),
        };

        let cutoff_days = dana::formats::time::parse_iso_date("2026-06-01")?;
        let params = pushdown.resolve_params(
            |name| match name {
                "completed_before" => Some(dana::oracle::value::Val::Date(cutoff_days.into())),
                _ => None,
            },
            |_| None,
        )?;
        let explain_schema = dana::core::syntax::TableTy {
            cols: vec![dana::core::syntax::ColSpec {
                name: "QUERY PLAN".to_string(),
                ty: dana::core::syntax::ScalarTy::Text,
                tags: dana::core::syntax::TagSet::empty(),
                bucketed: false,
                agg_kind: dana::core::syntax::AggKind::Raw,
            }],
            row_tags: dana::core::syntax::TagSet::empty(),
            order_tags: dana::core::syntax::TagSet::empty(),
            grouped_by: None,
            summarized: false,
            distinct_by: None,
        };
        let mut pg = open_connection(&url)?;
        let explain_tbl = pg.query_rows(
            &format!("EXPLAIN (FORMAT TEXT) {}", pushdown.sql),
            &params,
            &explain_schema,
        )?;
        let plan_text: Vec<String> = explain_tbl
            .rows
            .iter()
            .filter_map(|r| match r.cells.first() {
                Some(dana::oracle::value::Val::Text(line)) => Some(line.clone()),
                _ => None,
            })
            .collect();
        let joined_plan = plan_text.join("\n");
        assert!(
            joined_plan.contains("Hash Left Join")
                || joined_plan.contains("Hash Right Join")
                || joined_plan.contains("Hash Join"),
            "expected PostgreSQL planner to choose Hash Join:\n{joined_plan}\nSQL:\n{}",
            pushdown.sql
        );
        assert!(
            !joined_plan.contains("Nested Loop"),
            "PostgreSQL planner regressed to Nested Loop:\n{joined_plan}\nSQL:\n{}",
            pushdown.sql
        );

        let out = assert_oracle_vm_parity(&src, Some(("PG", &url)))?;
        assert_eq!(out.len(), 1);
        assert!(out[0].starts_with("cov:"), "unexpected output: {out:?}");
        Ok(())
    })();

    let _ = open_connection(&url).and_then(|mut pg| {
        pg.execute(
            &format!(r#"DROP SCHEMA IF EXISTS "{schema_name}" CASCADE"#),
            &[],
        )
    });

    test_res
}
