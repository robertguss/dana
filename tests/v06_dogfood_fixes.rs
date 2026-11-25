#![forbid(unsafe_code)]

//! Dana v0.6 Slice 6.1 verification suite:
//! - `.ceil`, `.floor`, `.trunc`, `.to_int` on `Float` & `Decimal` (scalar, row, Oracle/VM/SQL, traps)
//! - `.round([n], [mode: :half_away | :half_even])` and `.round_to(step, [mode:])` (banker's ties, privacy bucket clearance)
//! - General post-aggregate expressions inside `summarize(...)` + `SuppressSmallGroups` (`:drop`/`:mask`, SQL pushdown, negative privacy probes)
//! - CLI `--version` / `-V`
//! - All-`none` `table` literal unification with `T?` schemas (and rejection of non-optional `T`)
//! - Multiline `if cond:\n  ...\nelse if ...:\n  ...\nelse:\n  ...` expressions

use std::collections::HashMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};

use dana::base::{DiagCode, SourceMap};
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
