#![forbid(unsafe_code)]

//! Phase 3C — End-to-End Database Runtime, Vectorized VM Pushdown, `WriteTable.upsert`,
//! Redacted `dana dry-run`, `dana schema-sync`, Offline `schema.lock`, Enhanced `dana explain`,
//! `RawReadDB.raw_sql`, and Cross-Source Hybrid Pipeline Verification.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};

use dana::base::{DiagCode, SourceMap};
use dana::check::{check_module, check_module_with_lock};
use dana::cli::run_cli;
use dana::db::schema_lock::parse_schema_lock;
use dana::db::{SqlParam, open_connection};
use dana::oracle::value::val_eq;
use dana::syntax::parse_module;

type TestResult<T = ()> = Result<T, Box<dyn std::error::Error>>;

static TMP_COUNTER: AtomicU64 = AtomicU64::new(0);

struct TempDir {
    path: PathBuf,
}

impl TempDir {
    fn new(prefix: &str) -> TestResult<Self> {
        let id = TMP_COUNTER.fetch_add(1, Ordering::Relaxed);
        let pid = std::process::id();
        let path = std::env::temp_dir().join(format!("dana_phase3c_{prefix}_{pid}_{id}"));
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

fn run_dana_cmd(args: &[&str], cwd: Option<&Path>) -> TestResult<(i32, String, String)> {
    let mut cmd = Command::new(dana_bin());
    cmd.args(args);
    if let Some(dir) = cwd {
        cmd.current_dir(dir);
    }
    let out = cmd.output()?;
    let code = out.status.code().unwrap_or(-1);
    let stdout = String::from_utf8(out.stdout)?;
    let stderr = String::from_utf8(out.stderr)?;
    Ok((code, stdout, stderr))
}

fn sqlite_uri(db_path: &Path) -> String {
    format!("sqlite://{}", db_path.display())
}

// ===========================================================================
// 1. Live SQLite Multi-Table Pipeline: VM + SQL Pushdown == Oracle Parity
// ===========================================================================

#[test]
fn e2e_sqlite_enrollment_pipeline_vm_pushdown_matches_oracle() -> TestResult {
    let tmp = TempDir::new("enroll")?;
    let db_path = tmp.path().join("seminary.db");
    let uri = sqlite_uri(&db_path);

    let mut conn = open_connection(&uri)?;
    conn.execute(
        r#"CREATE TABLE "Student" (
            "student_id" INTEGER PRIMARY KEY NOT NULL,
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

    // 6 MDiv active students, 1 inactive MDiv student, 1 ThM active student (takes 5 courses -> must suppress!)
    let students: &[(i64, &str, &str, i64, bool)] = &[
        (1, "a@sem.edu", "MDiv", 2025, true),
        (2, "b@sem.edu", "MDiv", 2025, true),
        (3, "c@sem.edu", "MDiv", 2025, true),
        (4, "d@sem.edu", "MDiv", 2025, true),
        (5, "e@sem.edu", "MDiv", 2025, true),
        (6, "f@sem.edu", "MDiv", 2026, true),
        (7, "inactive@sem.edu", "MDiv", 2024, false),
        (8, "thm@sem.edu", "ThM", 2025, true),
    ];
    for &(id, email, prog, yr, active) in students {
        conn.execute(
            r#"INSERT INTO "Student" ("student_id", "email", "program", "cohort_year", "active?") VALUES (?, ?, ?, ?, ?)"#,
            &[
                SqlParam::Int(id),
                SqlParam::Text(email.to_string()),
                SqlParam::Text(prog.to_string()),
                SqlParam::Int(yr),
                SqlParam::Bool(active),
            ],
        )?;
    }

    // Fall 2025: 5 MDiv students (1..5), Spring 2026: 6 MDiv students (1..6), plus inactive #7 and ThM #8 (5 rows, 1 distinct)
    let enrollments: &[(i64, &str, &str, &str, Option<&str>)] = &[
        (1, "2025-Fall", "2025-09-01", "3.00", Some("3.80")),
        (2, "2025-Fall", "2025-09-01", "3.00", Some("3.60")),
        (3, "2025-Fall", "2025-09-01", "3.00", Some("3.40")),
        (4, "2025-Fall", "2025-09-01", "3.00", Some("4.00")),
        (5, "2025-Fall", "2025-09-01", "3.00", Some("3.20")),
        (7, "2025-Fall", "2025-09-01", "3.00", Some("2.00")),
        (1, "2026-Spring", "2026-01-15", "3.00", Some("3.90")),
        (2, "2026-Spring", "2026-01-15", "3.00", Some("3.70")),
        (3, "2026-Spring", "2026-01-15", "3.00", Some("3.50")),
        (4, "2026-Spring", "2026-01-15", "3.00", Some("4.00")),
        (5, "2026-Spring", "2026-01-15", "3.00", Some("3.50")),
        (6, "2026-Spring", "2026-01-15", "3.00", None),
        (8, "2025-Fall", "2025-09-01", "3.00", Some("3.90")),
        (8, "2025-Fall", "2025-09-01", "3.00", Some("3.90")),
        (8, "2025-Fall", "2025-09-01", "3.00", Some("3.90")),
        (8, "2025-Fall", "2025-09-01", "3.00", Some("3.90")),
        (8, "2025-Fall", "2025-09-01", "3.00", Some("3.90")),
    ];
    for &(sid, term, start, credits, gpa) in enrollments {
        let gpa_p = match gpa {
            Some(g) => SqlParam::Text(g.to_string()),
            None => SqlParam::Null,
        };
        conn.execute(
            r#"INSERT INTO "CourseEnrollment" ("student_id", "term", "term_start", "credits", "grade_points") VALUES (?, ?, ?, ?, ?)"#,
            &[
                SqlParam::Int(sid),
                SqlParam::Text(term.to_string()),
                SqlParam::Text(start.to_string()),
                SqlParam::Text(credits.to_string()),
                gpa_p,
            ],
        )?;
    }
    drop(conn);

    // Script performs the entire relational pipeline directly on `db.table(...)` so SQL pushdown
    // lowers Filter + Select + Join into a single parameterized SQLite query and runs
    // GroupBy + Summarize + SuppressSmallGroups + Sort + Window on the vectorized VM.
    let script = tmp.path().join("enroll_live.dana");
    fs::write(
        &script,
        r#"module LiveEnrollment

schema Student
  student_id: Int [pii]
  email: Text [pii]
  program: Text
  cohort_year: Int
  active?: Bool
end

schema CourseEnrollment
  student_id: Int [pii]
  term: Text
  term_start: Date
  credits: Decimal
  grade_points: Decimal? [ferpa]
end

fn main(db: ReadDB(Seminary), console: Console) : Int
  metrics = db.table(Student)
    |> where(.active?)
    |> select(.student_id, .program)
    |> join_many(db.table(CourseEnrollment), on: .student_id)
    |> group_by(.program, .term, .term_start)
    |> summarize(
         students: count_distinct(.student_id),
         avg_gpa: mean(.grade_points)
       )
    |> suppress_small_groups(min: 5, distinct_by: .student_id)
    |> sort_by(.program, .term_start)
    |> window(
         headcount_change: .students - lag(.students, 1),
         over: [.program],
         order: .term_start
       )

  console.print("rows=#{metrics.count()}")
  console.print_table(metrics)
  0
end
"#,
    )?;

    let db_arg = format!("Seminary={uri}");
    let script_str = script.to_string_lossy().to_string();

    let (vm_code, vm_out, vm_err) = run_dana_cmd(&["run", "--db", &db_arg, &script_str], None)?;
    assert_eq!(
        vm_code, 0,
        "VM run failed:\nstderr={vm_err}\nstdout={vm_out}"
    );

    let (ora_code, ora_out, ora_err) =
        run_dana_cmd(&["run", "--oracle", "--db", &db_arg, &script_str], None)?;
    assert_eq!(
        ora_code, 0,
        "Oracle run failed:\nstderr={ora_err}\nstdout={ora_out}"
    );

    assert_eq!(
        vm_out, ora_out,
        "VM + SQL pushdown output diverged from --oracle:\nVM:\n{vm_out}\nORACLE:\n{ora_out}"
    );
    assert!(
        vm_out.contains("rows=2"),
        "expected 2 published cells:\n{vm_out}"
    );
    assert!(
        vm_out.contains("MDiv"),
        "expected MDiv in output:\n{vm_out}"
    );
    assert!(
        vm_out.contains("2025-Fall") && vm_out.contains("2026-Spring"),
        "expected both terms:\n{vm_out}"
    );
    assert!(
        !vm_out.contains("ThM"),
        "small ThM cohort (1 distinct student) must be suppressed:\n{vm_out}"
    );
    assert!(
        !vm_out.contains("sem.edu"),
        "PII emails must never appear in published report:\n{vm_out}"
    );
    Ok(())
}

// ===========================================================================
// 2. Live SQLite WriteTable.upsert & Export-Gate Enforcement
// ===========================================================================

#[test]
fn e2e_sqlite_write_table_upsert_and_export_gate() -> TestResult {
    let tmp = TempDir::new("upsert")?;
    let db_path = tmp.path().join("registrar.db");
    let uri = sqlite_uri(&db_path);

    let mut conn = open_connection(&uri)?;
    conn.execute(
        r#"CREATE TABLE "students" (
            "student_id" INTEGER PRIMARY KEY NOT NULL,
            "email" TEXT NOT NULL,
            "program" TEXT NOT NULL,
            "gpa" TEXT,
            "active?" INTEGER NOT NULL
        )"#,
        &[],
    )?;
    // Existing rows: 101 will be updated, 102 will be unchanged
    conn.execute(
        r#"INSERT INTO "students" ("student_id", "email", "program", "gpa", "active?") VALUES (?, ?, ?, ?, ?)"#,
        &[
            SqlParam::Int(101),
            SqlParam::Text("alice@sem.edu".to_string()),
            SqlParam::Text("MDiv".to_string()),
            SqlParam::Text("3.80".to_string()),
            SqlParam::Bool(true),
        ],
    )?;
    conn.execute(
        r#"INSERT INTO "students" ("student_id", "email", "program", "gpa", "active?") VALUES (?, ?, ?, ?, ?)"#,
        &[
            SqlParam::Int(102),
            SqlParam::Text("bob@sem.edu".to_string()),
            SqlParam::Text("MAR".to_string()),
            SqlParam::Text("3.40".to_string()),
            SqlParam::Bool(true),
        ],
    )?;
    drop(conn);

    let script = tmp.path().join("sync.dana");
    fs::write(
        &script,
        r#"module SyncTest

schema DbStudent
  student_id: Int [pii]
  email: Text [pii]
  program: Text
  gpa: Decimal? [ferpa]
  active?: Bool
end

fn main(
  db_write: WriteTable(Seminary, "students", allows: [pii, ferpa]),
  console: Console
) : Int
  rows = table
    | student_id | email           | program | gpa  | active? |
    | 101        | "alice@sem.edu" | "MDiv"  | 3.95 | true    |
    | 102        | "bob@sem.edu"   | "MAR"   | 3.40 | true    |
    | 103        | "carol@sem.edu" | "ThM"   | 3.70 | true    |
  end
  stats = try db_write.upsert(rows, key: .student_id)
  console.print("ins=#{stats.inserted} upd=#{stats.updated} unch=#{stats.unchanged}")
  0
end
"#,
    )?;

    let db_arg = format!("Seminary={uri}");
    let script_str = script.to_string_lossy().to_string();

    // (a) Missing `--allow-export` MUST reject with ExportGateDenied and leave DB untouched!
    let (deny_code, deny_out, deny_err) =
        run_dana_cmd(&["run", "--db", &db_arg, &script_str], None)?;
    assert_ne!(
        deny_code, 0,
        "expected non-zero exit without --allow-export"
    );
    assert!(
        deny_err.contains("ExportGateDenied"),
        "expected ExportGateDenied diagnostic:\nstderr={deny_err}\nstdout={deny_out}"
    );

    // Verify 0 mutations occurred in SQLite
    let mut verify = open_connection(&uri)?;
    let count_schema = dana::core::TableTy {
        cols: vec![dana::core::ColSpec {
            name: "cnt".to_string(),
            ty: dana::core::ScalarTy::Int,
            tags: dana::core::TagSet::empty(),
            bucketed: false,
            agg_kind: dana::core::AggKind::Raw,
        }],
        ..dana::core::TableTy::default()
    };
    let cnt_before = verify.query_rows(
        r#"SELECT COUNT(*) AS "cnt" FROM "students""#,
        &[],
        &count_schema,
    )?;
    assert!(val_eq(
        &cnt_before.rows[0].cells[0],
        &dana::oracle::Val::Int(dana::core::BigInt::from(2))
    ));
    drop(verify);

    // (b) With `--allow-export=pii,ferpa`, upsert commits and reports exact counts!
    let (ok_code, ok_out, ok_err) = run_dana_cmd(
        &[
            "run",
            "--db",
            &db_arg,
            "--allow-export=pii,ferpa",
            &script_str,
        ],
        None,
    )?;
    assert_eq!(
        ok_code, 0,
        "authorized upsert failed:\nstderr={ok_err}\nstdout={ok_out}"
    );
    assert!(
        ok_out.contains("ins=1 upd=1 unch=1"),
        "expected ins=1 upd=1 unch=1:\n{ok_out}"
    );

    // Verify persisted rows in SQLite
    let mut verify2 = open_connection(&uri)?;
    let cnt_after = verify2.query_rows(
        r#"SELECT COUNT(*) AS "cnt" FROM "students""#,
        &[],
        &count_schema,
    )?;
    assert!(val_eq(
        &cnt_after.rows[0].cells[0],
        &dana::oracle::Val::Int(dana::core::BigInt::from(3))
    ));
    let gpa_schema = dana::core::TableTy {
        cols: vec![dana::core::ColSpec {
            name: "gpa".to_string(),
            ty: dana::core::ScalarTy::Text,
            tags: dana::core::TagSet::empty(),
            bucketed: false,
            agg_kind: dana::core::AggKind::Raw,
        }],
        ..dana::core::TableTy::default()
    };
    let updated_gpa = verify2.query_rows(
        r#"SELECT "gpa" FROM "students" WHERE "student_id" = ?"#,
        &[SqlParam::Int(101)],
        &gpa_schema,
    )?;
    assert!(val_eq(
        &updated_gpa.rows[0].cells[0],
        &dana::oracle::Val::Text("3.95".to_string())
    ));

    // (c) Static check rejects nonexistent upsert key column
    let bad_key_src = r#"module BadKey
schema S
  id: Int
  name: Text
end
fn main(w: WriteTable(Seminary, "s")) : Int
  rows = table
    | id | name |
    | 1  | "a"  |
  end
  _ = try w.upsert(rows, key: .missing_col)
  0
end
"#;
    let mut sm = SourceMap::new();
    let fid = sm.add_file("bad_key.dana", bad_key_src.to_string());
    let parsed = parse_module(fid, bad_key_src).map_err(|d| format!("{d:?}"))?;
    let err = check_module(fid, parsed, None, &sm).expect_err("expected missing key error");
    assert!(
        err.iter().any(|d| d.code() == DiagCode::TypeError),
        "expected TypeError for missing upsert key, got: {err:?}"
    );

    Ok(())
}

// ===========================================================================
// 3. `dana dry-run` on PII/FERPA WriteTable.upsert & WriteFiles
// ===========================================================================

#[test]
fn e2e_dry_run_redacts_pii_ferpa_and_mutates_nothing() -> TestResult {
    let tmp = TempDir::new("dryrun")?;
    let db_path = tmp.path().join("registrar_dry.db");
    let uri = sqlite_uri(&db_path);

    let mut conn = open_connection(&uri)?;
    conn.execute(
        r#"CREATE TABLE "students" (
            "student_id" INTEGER PRIMARY KEY NOT NULL,
            "email" TEXT NOT NULL,
            "program" TEXT NOT NULL,
            "gpa" TEXT,
            "active?" INTEGER NOT NULL
        )"#,
        &[],
    )?;
    conn.execute(
        r#"INSERT INTO "students" ("student_id", "email", "program", "gpa", "active?") VALUES (?, ?, ?, ?, ?)"#,
        &[
            SqlParam::Int(101),
            SqlParam::Text("alice@sem.edu".to_string()),
            SqlParam::Text("MDiv".to_string()),
            SqlParam::Text("3.80".to_string()),
            SqlParam::Bool(true),
        ],
    )?;
    drop(conn);

    let script = tmp.path().join("dry_sync.dana");
    fs::write(
        &script,
        r#"module DrySync

schema Students
  student_id: Int [pii]
  email: Text [pii]
  program: Text
  gpa: Decimal? [ferpa]
  active?: Bool
end

fn main(
  db_read: ReadDB(Seminary),
  db_write: WriteTable(Seminary, "students", allows: [pii, ferpa]),
  out: WriteFiles("out_dir/"),
  console: Console
) : Int
  existing = db_read.table(Students)
  updates = existing |> derive(gpa: 3.99)
  extra = table
    | student_id | email           | program | gpa  | active? |
    | 202        | "secret@sem.edu" | "ThM"   | 3.75 | true    |
  end
  combined = updates |> union(extra)
  stats = try db_write.upsert(combined, key: .student_id)
  try out.write_text("summary.txt", "should not be written to disk")
  console.print("preview: ins=#{stats.inserted} upd=#{stats.updated} unch=#{stats.unchanged}")
  0
end
"#,
    )?;

    let db_arg = format!("Seminary={uri}");
    let script_str = script.to_string_lossy().to_string();
    let (code, stdout, stderr) =
        run_dana_cmd(&["dry-run", "--db", &db_arg, &script_str], Some(tmp.path()))?;
    assert_eq!(code, 0, "dry-run failed:\nstderr={stderr}\nstdout={stdout}");

    // Exact insert/update counts printed
    assert!(
        stdout.contains("1 inserted, 1 updated, 0 unchanged")
            && stdout.contains("preview: ins=1 upd=1 unch=0"),
        "expected exact dry-run counts:\n{stdout}"
    );
    // Sensitivity redaction markers present
    assert!(
        stdout.contains("[REDACTED:pii]") && stdout.contains("[REDACTED:ferpa]"),
        "expected [REDACTED:pii] and [REDACTED:ferpa] in dry-run output:\n{stdout}"
    );
    // Raw PII / FERPA values MUST NEVER appear in stdout or stderr!
    for secret in ["alice@sem.edu", "secret@sem.edu", "3.99", "3.80", "3.75"] {
        assert!(
            !stdout.contains(secret) && !stderr.contains(secret),
            "raw sensitive value `{secret}` leaked in dry-run output!\nstdout={stdout}\nstderr={stderr}"
        );
    }
    // WriteFiles disk write suppressed
    assert!(
        !tmp.path().join("out_dir").exists(),
        "dry-run must NOT create files on disk"
    );
    assert!(
        stdout.contains("[DRY-RUN] would write file"),
        "expected suppressed file write summary:\n{stdout}"
    );

    // Verify 0 rows mutated in SQLite!
    let mut verify = open_connection(&uri)?;
    let check_schema = dana::core::TableTy {
        cols: vec![
            dana::core::ColSpec {
                name: "student_id".to_string(),
                ty: dana::core::ScalarTy::Int,
                tags: dana::core::TagSet::empty(),
                bucketed: false,
                agg_kind: dana::core::AggKind::Raw,
            },
            dana::core::ColSpec {
                name: "gpa".to_string(),
                ty: dana::core::ScalarTy::Text,
                tags: dana::core::TagSet::empty(),
                bucketed: false,
                agg_kind: dana::core::AggKind::Raw,
            },
        ],
        ..dana::core::TableTy::default()
    };
    let rows = verify.query_rows(
        r#"SELECT "student_id", "gpa" FROM "students""#,
        &[],
        &check_schema,
    )?;
    assert_eq!(
        rows.rows.len(),
        1,
        "dry-run must NOT insert rows into SQLite"
    );
    assert!(
        val_eq(
            &rows.rows[0].cells[1],
            &dana::oracle::Val::Text("3.80".to_string()),
        ),
        "dry-run must NOT update rows in SQLite"
    );
    Ok(())
}

// ===========================================================================
// 4. `dana schema-sync`, Tag Preservation, & Offline `dana check --schema-lock`
// ===========================================================================

#[test]
fn e2e_schema_sync_preserves_tags_and_check_enforces_lock() -> TestResult {
    let tmp = TempDir::new("schemalock")?;
    let db_path = tmp.path().join("school.db");
    let lock_path = tmp.path().join("schema.lock");
    let uri = sqlite_uri(&db_path);

    let mut conn = open_connection(&uri)?;
    conn.execute(
        r#"CREATE TABLE "students" (
            "student_id" INTEGER PRIMARY KEY NOT NULL,
            "email" TEXT NOT NULL,
            "program" TEXT NOT NULL,
            "gpa" NUMERIC
        )"#,
        &[],
    )?;
    drop(conn);

    let db_arg = format!("Seminary={uri}");
    let lock_str = lock_path.to_string_lossy().to_string();

    // 1. Initial `dana schema-sync`
    let (code1, out1, err1) =
        run_dana_cmd(&["schema-sync", "--db", &db_arg, "--out", &lock_str], None)?;
    assert_eq!(
        code1, 0,
        "schema-sync failed:\nstderr={err1}\nstdout={out1}"
    );
    assert!(
        out1.contains("+ table \"students\""),
        "missing sync report:\n{out1}"
    );

    // 2. Manually annotate sensitivity tags `[pii]` and `[ferpa]` in `schema.lock`
    let lock_src = fs::read_to_string(&lock_path)?;
    let tagged_lock = lock_src
        .replace(
            "col student_id: Int pk",
            "col student_id: Int pk tags [pii]",
        )
        .replace("col email: Text", "col email: Text tags [pii]")
        .replace("col gpa: Decimal?", "col gpa: Decimal? tags [ferpa]");
    fs::write(&lock_path, &tagged_lock)?;

    // 3. Evolve SQLite schema (add column `cohort_year`) and re-run `dana schema-sync`
    let mut conn2 = open_connection(&uri)?;
    conn2.execute(
        r#"ALTER TABLE "students" ADD COLUMN "cohort_year" INTEGER NOT NULL DEFAULT 2026"#,
        &[],
    )?;
    drop(conn2);

    let (code2, out2, err2) =
        run_dana_cmd(&["schema-sync", "--db", &db_arg, "--out", &lock_str], None)?;
    assert_eq!(code2, 0, "re-sync failed:\nstderr={err2}\nstdout={out2}");
    assert!(
        out2.contains("+ col students.cohort_year")
            && out2.contains("sensitivity tags preserved: 3"),
        "expected column addition + 3 preserved tags:\n{out2}"
    );

    let resynced = fs::read_to_string(&lock_path)?;
    assert!(
        resynced.contains("col student_id: Int pk tags [pii]")
            && resynced.contains("col email: Text tags [pii]")
            && resynced.contains("col gpa: Decimal? tags [ferpa]")
            && resynced.contains("col cohort_year: Int"),
        "tags or new col missing after re-sync:\n{resynced}"
    );

    let parsed_lock = parse_schema_lock(&resynced)?;

    // 4. Valid script passes `dana check --schema-lock`
    let ok_script = tmp.path().join("valid.dana");
    fs::write(
        &ok_script,
        r#"module ValidLock

schema Students
  student_id: Int [pii]
  email: Text [pii]
  program: Text
  gpa: Decimal? [ferpa]
  cohort_year: Int
end

fn main(
  db: ReadDB(Seminary),
  w: WriteTable(Seminary, "students", allows: [pii, ferpa])
) : Int
  rows = db.table(Students)
  _ = try w.upsert(rows, key: .student_id)
  0
end
"#,
    )?;
    let (chk_ok, _, chk_err) = run_dana_cmd(
        &[
            "check",
            "--schema-lock",
            &lock_str,
            &ok_script.to_string_lossy(),
        ],
        None,
    )?;
    assert_eq!(
        chk_ok, 0,
        "expected valid script to pass schema.lock check:\n{chk_err}"
    );

    // 5(a). Drifted column type -> DiagCode::SchemaError
    let drift_type_src = r#"module DriftType
schema Students
  student_id: Text [pii]
  email: Text [pii]
end
fn main(db: ReadDB(Seminary)) : Int
  _ = db.table(Students)
  0
end
"#;
    let drift_type_path = tmp.path().join("drift_type.dana");
    fs::write(&drift_type_path, drift_type_src)?;
    let (c_dt, _, e_dt) = run_dana_cmd(
        &[
            "check",
            "--schema-lock",
            &lock_str,
            &drift_type_path.to_string_lossy(),
        ],
        None,
    )?;
    assert_ne!(c_dt, 0, "expected drifted column type to fail `dana check`");
    assert!(
        e_dt.contains("type drift"),
        "expected type drift message:\n{e_dt}"
    );

    let mut sm = SourceMap::new();
    let fid_dt = sm.add_file("drift_type.dana", drift_type_src.to_string());
    let mod_dt = parse_module(fid_dt, drift_type_src).map_err(|d| format!("{d:?}"))?;
    let diags_dt = check_module_with_lock(fid_dt, mod_dt, None, &sm, Some(&parsed_lock))
        .expect_err("expected SchemaError for drifted type");
    assert!(
        diags_dt.iter().any(|d| d.code() == DiagCode::SchemaError),
        "expected SchemaError, got: {diags_dt:?}"
    );

    // 5(b). Missing column -> DiagCode::SchemaError
    let missing_col_src = r#"module MissingCol
schema Students
  student_id: Int [pii]
  nonexistent_col: Text
end
fn main(db: ReadDB(Seminary)) : Int
  _ = db.table(Students)
  0
end
"#;
    let fid_mc = sm.add_file("missing_col.dana", missing_col_src.to_string());
    let mod_mc = parse_module(fid_mc, missing_col_src).map_err(|d| format!("{d:?}"))?;
    let diags_mc = check_module_with_lock(fid_mc, mod_mc, None, &sm, Some(&parsed_lock))
        .expect_err("expected SchemaError for missing column");
    assert!(
        diags_mc.iter().any(|d| d.code() == DiagCode::SchemaError),
        "expected SchemaError, got: {diags_mc:?}"
    );

    // 5(c). Column-by-column WriteTable sensitivity tag violation -> DiagCode::PrivacyError!
    // Writing `[pii]` data into `program` (which is UNTAGGED in schema.lock) MUST be rejected
    // even when `WriteTable` has `allows: [pii, ferpa]`!
    let bad_tag_write_src = r#"module BadTagWrite
schema BadDest
  student_id: Int [pii]
  program: Text [pii]
end
fn main(w: WriteTable(Seminary, "students", allows: [pii, ferpa])) : Int
  rows = table
    | student_id | program |
    | 1          | "MDiv"  |
  end
  # Coerce via a schema-tagged table by deriving `program` from `student_id` ([pii])
  tainted = rows |> derive(program: "P")
  # Tag `program` as [pii] via schema BadDest
  _ = try w.upsert(
    table
      | student_id | program |
      | 1          | "MDiv"  |
    end,
    key: .student_id
  )
  _ = tainted
  0
end
"#;
    // Construct a table where `program` is explicitly tagged `[pii]` (coming from a `[pii]` schema)
    let bad_tag_write_real = r#"module BadTagWriteReal
schema TaggedProgram
  student_id: Int [pii]
  program: Text [pii]
end
fn sync_bad(
  rows: Table(TaggedProgram),
  w: WriteTable(Seminary, "students", allows: [pii, ferpa])
) : Int
  _ = try w.upsert(rows, key: .student_id)
  0
end
"#;
    let _ = bad_tag_write_src;
    let fid_bt = sm.add_file("bad_tag_write.dana", bad_tag_write_real.to_string());
    let mod_bt = parse_module(fid_bt, bad_tag_write_real).map_err(|d| format!("{d:?}"))?;
    let diags_bt = check_module_with_lock(fid_bt, mod_bt, None, &sm, Some(&parsed_lock))
        .expect_err("expected PrivacyError for column-by-column tag violation");
    assert!(
        diags_bt.iter().any(|d| d.code() == DiagCode::PrivacyError),
        "expected PrivacyError when writing [pii] column into untagged locked column, got: {diags_bt:?}"
    );

    let bad_tag_path = tmp.path().join("bad_tag_write.dana");
    fs::write(&bad_tag_path, bad_tag_write_real)?;
    let (c_bt, _, e_bt) = run_dana_cmd(
        &[
            "check",
            "--schema-lock",
            &lock_str,
            &bad_tag_path.to_string_lossy(),
        ],
        None,
    )?;
    assert_ne!(
        c_bt, 0,
        "expected CLI `dana check` to reject column tag violation"
    );
    assert!(
        e_bt.contains("unauthorized tags") || e_bt.contains("PrivacyError") || e_bt.contains("E04"),
        "expected privacy diagnostic:\n{e_bt}"
    );

    Ok(())
}

// ===========================================================================
// 5. `dana explain --dialect sqlite|postgres` on `examples/enrollment-report.dana`
// ===========================================================================

#[test]
fn e2e_explain_enrollment_report_sqlite_and_postgres() -> TestResult {
    let root = repo_root();
    let policy = root.join("examples/dana.policy");
    let script = root.join("examples/enrollment-report.dana");
    let policy_str = policy.to_string_lossy().to_string();
    let script_str = script.to_string_lossy().to_string();

    for dialect in ["sqlite", "postgres"] {
        // Verify direct `run_cli` entry point returns 0
        let cli_exit = run_cli(&[
            "explain".to_string(),
            "--dialect".to_string(),
            dialect.to_string(),
            "--policy".to_string(),
            policy_str.clone(),
            script_str.clone(),
        ]);
        assert_eq!(cli_exit, 0, "run_cli explain failed for dialect {dialect}");

        // Capture full stdout via compiled `dana` CLI binary and verify every section
        let (code, stdout, stderr) = run_dana_cmd(
            &[
                "explain",
                "--dialect",
                dialect,
                "--policy",
                &policy_str,
                &script_str,
            ],
            None,
        )?;
        assert_eq!(
            code, 0,
            "dana explain --dialect {dialect} failed:\nstderr={stderr}\nstdout={stdout}"
        );
        assert!(
            stdout.contains("[LOGICAL PLAN]") && stdout.contains("[OPTIMIZED PLAN]"),
            "missing logical/optimized plans for {dialect}:\n{stdout}"
        );
        assert!(
            stdout.contains(&format!("[SQL PUSHDOWN -> {dialect}]")),
            "missing SQL pushdown section for {dialect}:\n{stdout}"
        );
        assert!(
            stdout.contains("\"Student\"")
                && stdout.contains("\"CourseEnrollment\"")
                && stdout.contains("INNER JOIN"),
            "expected pushed Student INNER JOIN CourseEnrollment SQL for {dialect}:\n{stdout}"
        );
        assert!(
            stdout.contains("[PUSHDOWN BOUNDARY:") && stdout.contains("suppress_small_groups"),
            "expected suppress_small_groups boundary reason for {dialect}:\n{stdout}"
        );
        assert!(
            stdout.contains("[LOCAL VM SUFFIX]") && stdout.contains("SuppressSmallGroups"),
            "expected local VM suffix for {dialect}:\n{stdout}"
        );
        assert!(
            stdout.contains("[SENSITIVITY PROVENANCE]")
                && stdout.contains("pii")
                && stdout.contains("ferpa")
                && stdout.contains("CLEAR SuppressSmallGroups")
                && stdout.contains("OUTPUT: PUBLIC"),
            "expected [pii]/[ferpa] sensitivity provenance trace clearing to PUBLIC for {dialect}:\n{stdout}"
        );
    }

    Ok(())
}

// ===========================================================================
// 6. `RawReadDB.raw_sql`: Parameterized Execution, Injection Safety & Static Gate
// ===========================================================================

#[test]
fn e2e_raw_sql_parameterized_and_injection_proof() -> TestResult {
    let tmp = TempDir::new("rawsql")?;
    let db_path = tmp.path().join("raw.db");
    let uri = sqlite_uri(&db_path);

    let mut conn = open_connection(&uri)?;
    conn.execute(
        r#"CREATE TABLE "courses" (
            "code" TEXT PRIMARY KEY NOT NULL,
            "dept" TEXT NOT NULL,
            "credits" INTEGER NOT NULL
        )"#,
        &[],
    )?;
    for &(code, dept, credits) in &[
        ("OT101", "Biblical", 3_i64),
        ("NT201", "Biblical", 4),
        ("ST301", "Theology", 3),
    ] {
        conn.execute(
            r#"INSERT INTO "courses" ("code", "dept", "credits") VALUES (?, ?, ?)"#,
            &[
                SqlParam::Text(code.to_string()),
                SqlParam::Text(dept.to_string()),
                SqlParam::Int(credits),
            ],
        )?;
    }
    drop(conn);

    // (a) Live parameterized query + SQL injection payload in `params` stays harmless
    let script = tmp.path().join("raw_query.dana");
    fs::write(
        &script,
        r#"module RawSqlDemo

schema CourseRow
  code: Text
  dept: Text
  credits: Int
end

fn main(raw: RawReadDB(Catalog), console: Console) : Int
  min_credits = 3
  normal = try raw.raw_sql(
    "SELECT code, dept, credits FROM courses WHERE dept = ? AND credits >= ? ORDER BY code",
    params: ["Biblical", min_credits],
    as: CourseRow
  )
  injected = try raw.raw_sql(
    "SELECT code, dept, credits FROM courses WHERE dept = ?",
    params: ["' OR '1'='1'; DROP TABLE courses; --"],
    as: CourseRow
  )
  after_attack = try raw.raw_sql(
    "SELECT code, dept, credits FROM courses ORDER BY code",
    as: CourseRow
  )
  console.print("normal=#{normal.count()} injected=#{injected.count()} total=#{after_attack.count()}")
  0
end
"#,
    )?;

    let db_arg = format!("Catalog={uri}");
    let script_str = script.to_string_lossy().to_string();
    let (code, stdout, stderr) = run_dana_cmd(&["run", "--db", &db_arg, &script_str], None)?;
    assert_eq!(code, 0, "raw_sql failed:\nstderr={stderr}\nstdout={stdout}");
    assert!(
        stdout.contains("normal=2 injected=0 total=3"),
        "expected normal=2 injected=0 total=3:\n{stdout}"
    );

    // (b) Static rejection of interpolated SQL string (`#{...}`)
    let mut sm = SourceMap::new();
    let interp_src = r#"module BadRawInterp
schema Row
  code: Text
end
fn main(raw: RawReadDB(Catalog)) : Int
  dept = "Biblical"
  _ = try raw.raw_sql("SELECT code FROM courses WHERE dept = '#{dept}'", as: Row)
  0
end
"#;
    let fid1 = sm.add_file("bad_raw_interp.dana", interp_src.to_string());
    let m1 = parse_module(fid1, interp_src).map_err(|d| format!("{d:?}"))?;
    let d1 = check_module(fid1, m1, None, &sm)
        .expect_err("interpolated SQL in raw_sql must be statically rejected");
    assert!(
        d1.iter().any(|d| d.code() == DiagCode::CapabilityError),
        "expected CapabilityError for interpolated SQL, got: {d1:?}"
    );

    // (c) Static rejection of variable / dynamic SQL string
    let var_src = r#"module BadRawVar
schema Row
  code: Text
end
fn main(raw: RawReadDB(Catalog)) : Int
  q = "SELECT code FROM courses"
  _ = try raw.raw_sql(q, as: Row)
  0
end
"#;
    let fid2 = sm.add_file("bad_raw_var.dana", var_src.to_string());
    let m2 = parse_module(fid2, var_src).map_err(|d| format!("{d:?}"))?;
    let d2 = check_module(fid2, m2, None, &sm)
        .expect_err("dynamic variable SQL in raw_sql must be statically rejected");
    assert!(
        d2.iter().any(|d| d.code() == DiagCode::CapabilityError),
        "expected CapabilityError for dynamic SQL variable, got: {d2:?}"
    );

    // (d) Static sensitivity propagation: passing a `[pii]` param taints output table's `row_tags`
    let tainted_param_src = r#"module RawParamTaint
schema SecretRow
  email: Text [pii]
end
schema OutRow
  code: Text
end
fn leak(
  s: Table(SecretRow),
  raw: RawReadDB(Catalog),
  console: Console
) : Int
  first_email = s.first!.email
  rows = try raw.raw_sql("SELECT code FROM courses WHERE code = ?", params: [first_email], as: OutRow)
  console.print_table(rows)
  0
end
"#;
    let fid3 = sm.add_file("raw_param_taint.dana", tainted_param_src.to_string());
    let m3 = parse_module(fid3, tainted_param_src).map_err(|d| format!("{d:?}"))?;
    let d3 = check_module(fid3, m3, None, &sm)
        .expect_err("raw_sql with [pii] param must taint returned table");
    assert!(
        d3.iter().any(|d| d.code() == DiagCode::PrivacyError),
        "expected PrivacyError when printing table queried with [pii] param, got: {d3:?}"
    );

    Ok(())
}

// ===========================================================================
// 7. Hybrid Cross-Source Pipeline: Live SQLite ReadDB Joined with Local CSV
// ===========================================================================

#[test]
fn e2e_hybrid_sqlite_db_joined_with_local_csv() -> TestResult {
    let tmp = TempDir::new("hybrid")?;
    let db_path = tmp.path().join("orders.db");
    let csv_path = tmp.path().join("regions.csv");
    let uri = sqlite_uri(&db_path);

    let mut conn = open_connection(&uri)?;
    conn.execute(
        r#"CREATE TABLE "OrderRow" (
            "order_id" INTEGER PRIMARY KEY NOT NULL,
            "region_code" TEXT NOT NULL,
            "amount" TEXT NOT NULL,
            "paid?" INTEGER NOT NULL
        )"#,
        &[],
    )?;
    for &(oid, reg, amt, paid) in &[
        (1_i64, "US", "100.00", true),
        (2, "US", "50.00", true),
        (3, "EU", "200.00", true),
        (4, "EU", "999.00", false),
        (5, "AP", "75.00", true),
    ] {
        conn.execute(
            r#"INSERT INTO "OrderRow" ("order_id", "region_code", "amount", "paid?") VALUES (?, ?, ?, ?)"#,
            &[
                SqlParam::Int(oid),
                SqlParam::Text(reg.to_string()),
                SqlParam::Text(amt.to_string()),
                SqlParam::Bool(paid),
            ],
        )?;
    }
    drop(conn);

    fs::write(
        &csv_path,
        "region_code,region_name,tax_rate\nUS,United States,0.08\nEU,Europe,0.20\n",
    )?;

    let script = tmp.path().join("hybrid_join.dana");
    fs::write(
        &script,
        r#"module HybridJoin

schema OrderRow
  order_id: Int
  region_code: Text
  amount: Decimal
  paid?: Bool
end

schema RegionRow
  region_code: Text
  region_name: Text
  tax_rate: Decimal
end

fn main(
  db: ReadDB(Sales),
  files: ReadFiles,
  console: Console
) : Int
  (regions, _bad) = try files.read_csv("regions.csv", as: RegionRow)

  summary = db.table(OrderRow)
    |> where(.paid?)
    |> join_many_to_one(regions, on: .region_code)
    |> group_by(.region_name)
    |> summarize(
         order_count: count(),
         revenue: sum(.amount)
       )
    |> sort_by(.region_name)

  console.print_table(summary)
  0
end
"#,
    )?;

    let db_arg = format!("Sales={uri}");
    let script_str = script.to_string_lossy().to_string();

    let (vm_code, vm_out, vm_err) =
        run_dana_cmd(&["run", "--db", &db_arg, &script_str], Some(tmp.path()))?;
    assert_eq!(
        vm_code, 0,
        "hybrid VM run failed:\nstderr={vm_err}\nstdout={vm_out}"
    );

    let (ora_code, ora_out, ora_err) = run_dana_cmd(
        &["run", "--oracle", "--db", &db_arg, &script_str],
        Some(tmp.path()),
    )?;
    assert_eq!(
        ora_code, 0,
        "hybrid oracle run failed:\nstderr={ora_err}\nstdout={ora_out}"
    );

    assert_eq!(vm_out, ora_out, "hybrid VM vs oracle output mismatch");
    assert!(
        vm_out.contains("Europe")
            && vm_out.contains("200")
            && vm_out.contains("United States")
            && vm_out.contains("150"),
        "expected joined Europe (200) & United States (150):\n{vm_out}"
    );
    assert!(
        !vm_out.contains("999"),
        "unpaid order must be filtered out:\n{vm_out}"
    );
    Ok(())
}

#[test]
fn e2e_schema_sync_schemas_cli_validation_and_multi_schema_explain() -> TestResult {
    let tmp = TempDir::new("v05_schemas_cli")?;
    let db_path = tmp.path().join("app.db");
    let uri = sqlite_uri(&db_path);
    let mut conn = open_connection(&uri)?;
    conn.execute(
        r#"CREATE TABLE "users" ("id" INTEGER PRIMARY KEY NOT NULL, "email" TEXT NOT NULL)"#,
        &[],
    )?;
    drop(conn);

    let db_arg = format!("App={uri}");
    let lock_path = tmp.path().join("schema.lock");
    let lock_str = lock_path.to_string_lossy().to_string();

    // Invalid empty `--schemas`
    let (bad_empty_code, _, bad_empty_err) = run_dana_cmd(
        &[
            "schema-sync",
            "--db",
            &db_arg,
            "--schemas",
            "",
            "--out",
            &lock_str,
        ],
        Some(tmp.path()),
    )?;
    assert_ne!(bad_empty_code, 0);
    assert!(
        bad_empty_err.contains("--schemas"),
        "expected `--schemas` validation error, got: {bad_empty_err}"
    );

    // Invalid whitespace schema name in `--schemas=...`
    let (bad_ws_code, _, bad_ws_err) = run_dana_cmd(
        &[
            "schema-sync",
            "--db",
            &db_arg,
            "--schemas=populi,bad schema",
            "--out",
            &lock_str,
        ],
        Some(tmp.path()),
    )?;
    assert_ne!(bad_ws_code, 0);
    assert!(
        bad_ws_err.contains("invalid schema name"),
        "expected invalid schema name error, got: {bad_ws_err}"
    );

    // Valid `--schemas` succeeds on SQLite fallback and creates lock file
    let (ok_code, _, ok_err) = run_dana_cmd(
        &[
            "schema-sync",
            "--db",
            &db_arg,
            "--schemas",
            "public,analytics",
            "--out",
            &lock_str,
        ],
        Some(tmp.path()),
    )?;
    assert_eq!(ok_code, 0, "schema-sync --schemas failed:\n{ok_err}");
    let synced = parse_schema_lock(&fs::read_to_string(&lock_path)?)?;
    assert_eq!(synced.dbs.len(), 1);

    // Offline Postgres schema.lock with qualified `populi.enrollments` + `from:` + `count_if`
    let pg_lock = tmp.path().join("pg_schema.lock");
    fs::write(
        &pg_lock,
        r#"version 1

db Wts dialect postgres
  table "populi.enrollments"
    col id: Int pk
    col student_email: Text tags [pii]
    col term: Text
    col score: Int
    col fee: Decimal tags [financial]
  end
end
"#,
    )?;
    let parsed_pg = parse_schema_lock(&fs::read_to_string(&pg_lock)?)?;

    let good_src = r#"module WtsExplain

schema Enrollment
  id: Int
  student_email: Text [pii]
  term: Text
  score: Int
  fee: Decimal [financial]
end

fn main(db: ReadDB(Wts), c: Console) : Int
  res = db.table(Enrollment, from: "populi.enrollments")
    |> where(.term.in?(["2026FA", "2027SP"]))
    |> derive(bounded_score: .score.clamp(0, 100), clamped_fee: .fee.clamp(0.0, 5000.0))
    |> group_by(.term)
    |> summarize(
         total: count(),
         high_count: count_if(.bounded_score >= 90)
       )
    |> sort_by(.term)
  c.print("ok")
  0
end
"#;
    let mut sm = SourceMap::new();
    let fid_good = sm.add_file("wts_explain.dana", good_src.to_string());
    let good_mod = parse_module(fid_good, good_src).map_err(|e| format!("{e:?}"))?;
    let checked = check_module_with_lock(fid_good, good_mod, None, &sm, Some(&parsed_pg));
    assert!(
        checked.is_ok(),
        "expected good multi-schema `from:` module to pass lock check: {:?}",
        checked.err()
    );

    // Verify missing table or type drift fails against lock
    let bad_src = r#"module WtsBad

schema Enrollment
  id: Int
  student_email: Text
  term: Text
  score: Text
  fee: Decimal [financial]
end

fn main(db: ReadDB(Wts)) : Int
  _rows = db.table(Enrollment, from: "populi.enrollments")
  0
end
"#;
    let fid_bad = sm.add_file("wts_bad.dana", bad_src.to_string());
    let bad_mod = parse_module(fid_bad, bad_src).map_err(|e| format!("{e:?}"))?;
    let bad_res = check_module_with_lock(fid_bad, bad_mod, None, &sm, Some(&parsed_pg));
    let diags = bad_res.err().ok_or("expected SchemaError on drift")?;
    assert!(
        diags.iter().any(|d| d.code() == DiagCode::SchemaError),
        "expected SchemaError diagnostic, got: {diags:?}"
    );

    // Run `dana explain --dialect postgres` and inspect pushed SQL & CountIf name
    let script_path = tmp.path().join("wts_explain.dana");
    fs::write(&script_path, good_src)?;
    let pg_lock_str = pg_lock.to_string_lossy().to_string();
    let script_str = script_path.to_string_lossy().to_string();
    let (exp_code, exp_out, exp_err) = run_dana_cmd(
        &[
            "explain",
            "--dialect",
            "postgres",
            "--schema-lock",
            &pg_lock_str,
            &script_str,
        ],
        Some(tmp.path()),
    )?;
    assert_eq!(
        exp_code, 0,
        "dana explain failed:\nstderr={exp_err}\nstdout={exp_out}"
    );
    assert!(
        exp_out.contains(r#"FROM "populi"."enrollments""#),
        "expected qualified PG table ref in explain:\n{exp_out}"
    );
    assert!(
        exp_out.contains(r#""term" IN (CAST($"#),
        "expected parameterized IN (...) in explain:\n{exp_out}"
    );
    assert!(
        exp_out.contains("COALESCE(SUM((CASE WHEN"),
        "expected pushed count_if COALESCE(SUM((CASE WHEN ...))) in explain:\n{exp_out}"
    );
    assert!(
        exp_out.contains("CountIf"),
        "expected CountIf op label in explain:\n{exp_out}"
    );

    Ok(())
}
