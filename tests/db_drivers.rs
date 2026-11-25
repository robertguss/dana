//! Phase 3A integration tests:
//! - Audited `src/ffi/sqlite.rs` & `src/db/sqlite.rs` (all scalar types, Option nulls, exact 18-digit Decimal,
//!   multi-batch 2,048-row `query_batches`, schema drift rejection, `introspect_schema`, transactional upsert,
//!   strictly read-only `dry_run` + `[REDACTED:pii]` diff rendering)
//! - Audited `src/ffi/tls.rs` (real OpenSSL 3 handshakes, SNI, `VerifyFull`, `VerifyCa`, untrusted CA & bad-host rejection)
//! - Native zero-crate PostgreSQL v3.0 wire protocol client (`src/db/postgres.rs`) verified against a full
//!   in-process PostgreSQL v3.0 + real OpenSSL TLS + real SCRAM-SHA-256 + MD5 + Cleartext + Extended Query
//!   wire test server backed by `SqliteConn`, plus an opt-in live Postgres test (`DANA_TEST_POSTGRES_URL`)
//! - Offline `schema.lock` (`src/db/schema_lock.rs`) round-trip, tag-preserving merge, and drift verification.

use std::collections::HashMap;
use std::fs;
use std::io::{Read, Write};
use std::net::{TcpListener, TcpStream};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};
use std::thread;

use dana::core::bigint::BigInt;
use dana::core::syntax::{AggKind, ColSpec, Float64, ScalarTy, TableTy, TagSet};
use dana::db::postgres::{
    PostgresDriver, base64_decode, base64_encode, map_pg_type_name, md5_digest, oid,
    pg_md5_password, scram_pbkdf2_hmac_sha256,
};
use dana::db::schema_lock::{
    LockedCol, LockedDb, LockedTable, SchemaLock, format_schema_lock, merge_schema_lock,
    parse_schema_lock, verify_table_against_lock,
};
use dana::db::sqlite::SqliteDriver;
use dana::db::{
    DbConnection, DbError, DbRegistry, DbUri, RowDiffKind, SqlDialect, SqlParam, SslMode,
    open_connection, quote_sql_table_ref,
};
use dana::ffi::sqlite::{SqliteConn, SqliteValueType, StepResult};
use dana::ffi::tls::{TlsClientConfig, TlsServerAcceptor, TlsStream};
use dana::formats::crypto::{hmac_sha256, sha256, to_hex_lower};
use dana::formats::time::{days_from_civil, parse_decimal_bigint_strict, parse_iso_timestamp};
use dana::oracle::value::{TableRow, TableVal, Val, val_eq};
use dana::vm::BATCH_SIZE;

type TestResult<T = ()> = Result<T, Box<dyn std::error::Error>>;

fn unique_temp_dir(prefix: &str) -> TestResult<PathBuf> {
    static SEQ: AtomicU64 = AtomicU64::new(1);
    let n = SEQ.fetch_add(1, Ordering::Relaxed);
    let dir = std::env::temp_dir().join(format!(
        "dana_phase3a_{prefix}_{}_{}",
        std::process::id(),
        n
    ));
    fs::create_dir_all(&dir)?;
    Ok(dir)
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

// ===========================================================================
// 1. URI Parser & Pure-Rust Crypto Tests
// ===========================================================================

#[test]
fn db_uri_parsing_and_percent_decoding() -> TestResult {
    let mem = DbUri::parse("sqlite::memory:")?;
    assert_eq!(mem.dialect(), SqlDialect::Sqlite);
    match mem {
        DbUri::Sqlite(s) => {
            assert_eq!(s.path, ":memory:");
            assert!(!s.read_only);
        }
        DbUri::Postgres(_) => return Err("expected sqlite URI".into()),
    }

    let file_uri = DbUri::parse("sqlite:///tmp/my%20data/app.db?mode=ro")?;
    match file_uri {
        DbUri::Sqlite(s) => {
            assert_eq!(s.path, "/tmp/my data/app.db");
            assert!(s.read_only);
        }
        DbUri::Postgres(_) => return Err("expected sqlite URI".into()),
    }

    let pg_uri = DbUri::parse(
        "postgresql://alice:p%40ss%3A123@db.internal:5433/analytics?sslmode=verify-full&sslrootcert=%2Fetc%2Fca.pem&connect_timeout=15",
    )?;
    assert_eq!(pg_uri.dialect(), SqlDialect::Postgres);
    match pg_uri {
        DbUri::Postgres(p) => {
            assert_eq!(p.user, "alice");
            assert_eq!(p.password.as_deref(), Some("p@ss:123"));
            assert_eq!(p.host, "db.internal");
            assert_eq!(p.port, 5433);
            assert_eq!(p.database, "analytics");
            assert_eq!(p.sslmode, SslMode::VerifyFull);
            assert_eq!(p.sslrootcert.as_deref(), Some("/etc/ca.pem"));
            assert_eq!(p.connect_timeout_secs, Some(15));
            // Debug output must redact the password!
            let dbg = format!("{p:?}");
            assert!(!dbg.contains("p@ss:123"));
            assert!(dbg.contains("[REDACTED:secret]"));
        }
        DbUri::Sqlite(_) => return Err("expected postgres URI".into()),
    }

    let ipv6 = DbUri::parse("postgres://u@[::1]:5440/mydb?sslmode=disable")?;
    match ipv6 {
        DbUri::Postgres(p) => {
            assert_eq!(p.host, "::1");
            assert_eq!(p.port, 5440);
            assert_eq!(p.database, "mydb");
            assert_eq!(p.sslmode, SslMode::Disable);
        }
        DbUri::Sqlite(_) => return Err("expected postgres URI".into()),
    }

    assert!(matches!(
        DbUri::parse("mysql://localhost/db"),
        Err(DbError::InvalidUri(_))
    ));
    assert!(matches!(
        DbUri::parse("postgres://localhost/db?sslmode=bogus"),
        Err(DbError::InvalidUri(_))
    ));
    Ok(())
}

#[test]
fn md5_rfc1321_and_base64_vectors() -> TestResult {
    assert_eq!(
        to_hex_lower(&md5_digest(b"")),
        "d41d8cd98f00b204e9800998ecf8427e"
    );
    assert_eq!(
        to_hex_lower(&md5_digest(b"abc")),
        "900150983cd24fb0d6963f7d28e17f72"
    );
    assert_eq!(
        to_hex_lower(&md5_digest(b"message digest")),
        "f96b697d7cb7938d525a2f31aaf161d0"
    );

    let pg_hash = pg_md5_password("dana", "secret", [0x01, 0x02, 0x03, 0x04]);
    assert!(pg_hash.starts_with("md5"));
    assert_eq!(pg_hash.len(), 35);

    for sample in [&b""[..], b"f", b"fo", b"foo", b"foob", b"fooba", b"foobar"] {
        let enc = base64_encode(sample);
        let dec = base64_decode(&enc)?;
        assert_eq!(dec, sample);
    }
    Ok(())
}

// ===========================================================================
// 2. SQLite Driver Integration Tests
// ===========================================================================

#[test]
fn sqlite_all_scalar_types_option_nulls_and_exact_18_digit_decimal() -> TestResult {
    assert!(!SqliteConn::libversion().is_empty());
    let mut drv = SqliteDriver::open_in_memory()?;
    drv.execute_batch(
        "CREATE TABLE records (
            id INTEGER PRIMARY KEY,
            active BOOLEAN NOT NULL,
            amount DECIMAL_TEXT NOT NULL,
            score REAL NOT NULL,
            label TEXT NOT NULL,
            payload BLOB NOT NULL,
            born DATE NOT NULL,
            created_at TIMESTAMP NOT NULL,
            elapsed DURATION NOT NULL,
            note TEXT,
            opt_dec DECIMAL_TEXT
        );",
    )?;

    let dec_exact = parse_decimal_bigint_strict("123456789012345678.123456789012345678")?;
    let dec_neg = parse_decimal_bigint_strict("-0.000000000000000001")?;
    let date_val = days_from_civil(2025, 3, 15);
    let ts_val = parse_iso_timestamp("2025-03-15T14:30:45.123456Z")?;
    let dur_val = 9_876_543i64;

    let insert_sql = "INSERT INTO records VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)";
    let changed = drv.execute(
        insert_sql,
        &[
            SqlParam::Int(1),
            SqlParam::Bool(true),
            SqlParam::Decimal(dec_exact.clone()),
            SqlParam::Float(Float64::from_f64(3.25)),
            SqlParam::Text("alpha".to_string()),
            SqlParam::Bytes(vec![0xDE, 0xAD, 0xBE, 0xEF]),
            SqlParam::Date(date_val),
            SqlParam::Timestamp(ts_val),
            SqlParam::Duration(dur_val),
            SqlParam::Text("present".to_string()),
            SqlParam::Decimal(dec_neg.clone()),
        ],
    )?;
    assert_eq!(changed, 1);

    // Row 2 tests Option::None nulls AND empty string/empty blob edge cases.
    drv.execute(
        insert_sql,
        &[
            SqlParam::Int(2),
            SqlParam::Bool(false),
            SqlParam::Decimal(dec_neg.clone()),
            SqlParam::Float(Float64::from_f64(-0.5)),
            SqlParam::Text(String::new()),
            SqlParam::Bytes(Vec::new()),
            SqlParam::Date(0),
            SqlParam::Timestamp(0),
            SqlParam::Duration(-42),
            SqlParam::Null,
            SqlParam::Null,
        ],
    )?;

    let schema = table_ty(vec![
        col("id", ScalarTy::Int, &[]),
        col("active", ScalarTy::Bool, &[]),
        col("amount", ScalarTy::Decimal, &[]),
        col("score", ScalarTy::Float, &[]),
        col("label", ScalarTy::Text, &[]),
        col("payload", ScalarTy::Bytes, &[]),
        col("born", ScalarTy::Date, &[]),
        col("created_at", ScalarTy::Timestamp, &[]),
        col("elapsed", ScalarTy::Duration, &[]),
        col("note", opt(ScalarTy::Text), &[]),
        col("opt_dec", opt(ScalarTy::Decimal), &[]),
    ]);

    let tv = drv.query_rows(
        "SELECT id, active, amount, score, label, payload, born, created_at, elapsed, note, opt_dec \
         FROM records ORDER BY id",
        &[],
        &schema,
    )?;
    assert_eq!(tv.rows.len(), 2);

    let r0 = &tv.rows[0].cells;
    assert!(val_eq(&r0[0], &Val::Int(BigInt::from(1))));
    assert!(val_eq(&r0[1], &Val::Bool(true)));
    assert!(val_eq(&r0[2], &Val::Decimal(dec_exact)));
    assert!(val_eq(&r0[3], &Val::Float(Float64::from_f64(3.25))));
    assert!(val_eq(&r0[4], &Val::Text("alpha".to_string())));
    assert!(val_eq(&r0[5], &Val::Bytes(vec![0xDE, 0xAD, 0xBE, 0xEF])));
    assert!(val_eq(&r0[6], &Val::Date(BigInt::from(date_val))));
    assert!(val_eq(&r0[7], &Val::Timestamp(BigInt::from(ts_val))));
    assert!(val_eq(&r0[8], &Val::Duration(BigInt::from(dur_val))));
    assert!(val_eq(
        &r0[9],
        &Val::OptSome(Box::new(Val::Text("present".to_string())))
    ));
    assert!(val_eq(
        &r0[10],
        &Val::OptSome(Box::new(Val::Decimal(dec_neg.clone())))
    ));

    let r1 = &tv.rows[1].cells;
    assert!(val_eq(&r1[0], &Val::Int(BigInt::from(2))));
    assert!(val_eq(&r1[1], &Val::Bool(false)));
    assert!(val_eq(&r1[2], &Val::Decimal(dec_neg)));
    assert!(val_eq(&r1[4], &Val::Text(String::new())));
    assert!(val_eq(&r1[5], &Val::Bytes(Vec::new())));
    assert!(val_eq(&r1[9], &Val::OptNone));
    assert!(val_eq(&r1[10], &Val::OptNone));
    Ok(())
}

#[test]
fn sqlite_multi_batch_2560_rows_and_schema_drift() -> TestResult {
    let mut drv = SqliteDriver::open_in_memory()?;
    drv.execute_batch(
        "CREATE TABLE metrics (id INTEGER PRIMARY KEY, bucket TEXT NOT NULL, val INTEGER);",
    )?;
    drv.execute("BEGIN IMMEDIATE", &[])?;
    for i in 0..2_560i64 {
        let opt_val = if i % 5 == 0 {
            SqlParam::Null
        } else {
            SqlParam::Int(i * 10)
        };
        drv.execute(
            "INSERT INTO metrics (id, bucket, val) VALUES (?, ?, ?)",
            &[
                SqlParam::Int(i),
                SqlParam::Text(format!("b{}", i % 7)),
                opt_val,
            ],
        )?;
    }
    drv.execute("COMMIT", &[])?;

    let schema = table_ty(vec![
        col("id", ScalarTy::Int, &[]),
        col("bucket", ScalarTy::Text, &[]),
        col("val", opt(ScalarTy::Int), &[]),
    ]);
    let vm_tbl = drv.query_batches(
        "SELECT id, bucket, val FROM metrics ORDER BY id",
        &[],
        &schema,
        BATCH_SIZE,
    )?;
    assert_eq!(vm_tbl.total_rows(), 2_560);
    assert_eq!(vm_tbl.batches.len(), 2);
    assert_eq!(vm_tbl.batches[0].len, 2_048);
    assert_eq!(vm_tbl.batches[1].len, 512);

    let materialized = vm_tbl.into_table_val();
    let row_tbl = drv.query_rows(
        "SELECT id, bucket, val FROM metrics ORDER BY id",
        &[],
        &schema,
    )?;
    assert_eq!(materialized.rows.len(), row_tbl.rows.len());
    for (a, b) in materialized.rows.iter().zip(&row_tbl.rows) {
        for (ca, cb) in a.cells.iter().zip(&b.cells) {
            assert!(val_eq(ca, cb));
        }
    }

    // Schema drift 1: wrong column count
    let short_schema = table_ty(vec![col("id", ScalarTy::Int, &[])]);
    assert!(matches!(
        drv.query_rows("SELECT id, bucket FROM metrics LIMIT 1", &[], &short_schema),
        Err(DbError::SchemaDrift(_))
    ));

    // Schema drift 2: wrong storage class (Text where Int expected)
    let wrong_ty_schema = table_ty(vec![col("bucket", ScalarTy::Int, &[])]);
    assert!(matches!(
        drv.query_rows("SELECT bucket FROM metrics LIMIT 1", &[], &wrong_ty_schema),
        Err(DbError::SchemaDrift(_))
    ));

    // Schema drift 3: unexpected NULL in non-nullable column
    let non_null_schema = table_ty(vec![col("val", ScalarTy::Int, &[])]);
    assert!(matches!(
        drv.query_rows(
            "SELECT val FROM metrics WHERE id = 0",
            &[],
            &non_null_schema
        ),
        Err(DbError::SchemaDrift(_))
    ));
    Ok(())
}

#[test]
fn sqlite_introspect_transactional_upsert_and_redacted_dry_run() -> TestResult {
    let dir = unique_temp_dir("sqlite_upsert")?;
    let db_path = dir.join("students.db");
    let uri = format!("sqlite://{}", db_path.display());

    let mut registry = DbRegistry::new();
    registry.register("SIS", uri);
    let conn = registry.open("SIS")?;
    assert_eq!(conn.dialect(), SqlDialect::Sqlite);

    conn.execute(
        "CREATE TABLE students (
            id INTEGER PRIMARY KEY,
            email TEXT NOT NULL,
            gpa DECIMAL NOT NULL,
            advisor TEXT
        )",
        &[],
    )?;
    conn.execute(
        "INSERT INTO students (id, email, gpa, advisor) VALUES (?, ?, ?, ?)",
        &[
            SqlParam::Int(1),
            SqlParam::Text("alice@uni.edu".to_string()),
            SqlParam::Decimal(parse_decimal_bigint_strict("3.80")?),
            SqlParam::Text("Dr. Smith".to_string()),
        ],
    )?;
    conn.execute(
        "INSERT INTO students (id, email, gpa, advisor) VALUES (?, ?, ?, ?)",
        &[
            SqlParam::Int(2),
            SqlParam::Text("bob@uni.edu".to_string()),
            SqlParam::Decimal(parse_decimal_bigint_strict("3.50")?),
            SqlParam::Null,
        ],
    )?;

    // Introspect schema
    let locked = conn.introspect_schema("SIS")?;
    assert_eq!(locked.dialect, SqlDialect::Sqlite);
    assert_eq!(locked.tables.len(), 1);
    let tbl = &locked.tables[0];
    assert_eq!(tbl.name, "students");
    assert_eq!(tbl.cols.len(), 4);
    assert_eq!(tbl.cols[0].name, "id");
    assert_eq!(tbl.cols[0].ty, ScalarTy::Int);
    assert!(tbl.cols[0].pk);
    assert!(!tbl.cols[0].nullable);
    assert_eq!(tbl.cols[2].ty, ScalarTy::Decimal);
    assert!(!tbl.cols[2].nullable);
    assert_eq!(tbl.cols[3].name, "advisor");
    assert!(tbl.cols[3].nullable);

    // Prepare incoming upsert table:
    // - id=1 unchanged
    // - id=2 updated email & advisor (email carries `pii` tag!)
    // - id=3 inserted (email carries `pii` tag!)
    let incoming_cols = vec![
        col("id", ScalarTy::Int, &[]),
        col("email", ScalarTy::Text, &["pii"]),
        col("gpa", ScalarTy::Decimal, &["ferpa"]),
        col("advisor", opt(ScalarTy::Text), &[]),
    ];
    let incoming = TableVal {
        cols: incoming_cols.clone(),
        rows: vec![
            TableRow {
                cells: vec![
                    Val::Int(BigInt::from(1)),
                    Val::Text("alice@uni.edu".to_string()),
                    Val::Decimal(parse_decimal_bigint_strict("3.80")?),
                    Val::OptSome(Box::new(Val::Text("Dr. Smith".to_string()))),
                ],
                group_meta: None,
            },
            TableRow {
                cells: vec![
                    Val::Int(BigInt::from(2)),
                    Val::Text("bob.new@uni.edu".to_string()),
                    Val::Decimal(parse_decimal_bigint_strict("3.95")?),
                    Val::OptSome(Box::new(Val::Text("Dr. Ada".to_string()))),
                ],
                group_meta: None,
            },
            TableRow {
                cells: vec![
                    Val::Int(BigInt::from(3)),
                    Val::Text("carol@uni.edu".to_string()),
                    Val::Decimal(parse_decimal_bigint_strict("4.00")?),
                    Val::OptNone,
                ],
                group_meta: None,
            },
        ],
    };

    // Dry-run MUST NOT mutate the database!
    let dry_diff = conn.upsert_table("students", "id", &incoming, true)?;
    assert_eq!(dry_diff.inserted, 1);
    assert_eq!(dry_diff.updated, 1);
    assert_eq!(dry_diff.unchanged, 1);
    assert_eq!(dry_diff.sample_diffs.len(), 2);
    assert_eq!(dry_diff.sample_diffs[0].kind, RowDiffKind::Update);
    assert_eq!(dry_diff.sample_diffs[1].kind, RowDiffKind::Insert);

    // Default rendering (empty allow_export) MUST redact all `pii` and `ferpa` values!
    let redacted = dry_diff.render_redacted(&TagSet::empty());
    assert!(redacted.contains("[REDACTED:pii]"));
    assert!(redacted.contains("[REDACTED:ferpa]"));
    assert!(!redacted.contains("bob@uni.edu"));
    assert!(!redacted.contains("bob.new@uni.edu"));
    assert!(!redacted.contains("carol@uni.edu"));
    assert!(!redacted.contains("3.95"));
    assert!(redacted.contains("Dr. Ada")); // untagged column is visible

    // Explicit allow_export for `pii` reveals `pii` while keeping `ferpa` redacted.
    let partial = dry_diff.render_redacted(&TagSet::singleton("pii"));
    assert!(partial.contains("bob.new@uni.edu"));
    assert!(partial.contains("carol@uni.edu"));
    assert!(partial.contains("[REDACTED:ferpa]"));
    assert!(!partial.contains("3.95"));

    // Confirm 0 rows changed in DB after dry-run.
    let check_schema = table_ty(incoming_cols.clone());
    let before_commit = conn.query_rows(
        "SELECT id, email, gpa, advisor FROM students ORDER BY id",
        &[],
        &check_schema,
    )?;
    assert_eq!(before_commit.rows.len(), 2);
    assert!(val_eq(
        &before_commit.rows[1].cells[1],
        &Val::Text("bob@uni.edu".to_string())
    ));

    // Real upsert applies changes transactionally.
    let live_diff = conn.upsert_table("students", "id", &incoming, false)?;
    assert_eq!(live_diff.inserted, 1);
    assert_eq!(live_diff.updated, 1);
    assert_eq!(live_diff.unchanged, 1);

    let after_commit = conn.query_rows(
        "SELECT id, email, gpa, advisor FROM students ORDER BY id",
        &[],
        &check_schema,
    )?;
    assert_eq!(after_commit.rows.len(), 3);
    assert!(val_eq(
        &after_commit.rows[1].cells[1],
        &Val::Text("bob.new@uni.edu".to_string())
    ));
    assert!(val_eq(
        &after_commit.rows[2].cells[1],
        &Val::Text("carol@uni.edu".to_string())
    ));

    let _ = fs::remove_dir_all(&dir);
    Ok(())
}

// ===========================================================================
// 3. OpenSSL TLS Integration Tests (VerifyFull, VerifyCa, Untrusted Rejection)
// ===========================================================================

#[test]
fn openssl_tls_handshake_verify_full_verify_ca_and_rejections() -> TestResult {
    let dir = unique_temp_dir("openssl_tls")?;
    let (cert_path, key_path) = generate_self_signed_cert(&dir)?;

    let listener = TcpListener::bind("127.0.0.1:0")?;
    let port = listener.local_addr()?.port();
    let acceptor = TlsServerAcceptor::from_pem_files(&cert_path, &key_path)
        .map_err(|e| format!("TlsServerAcceptor failed: {e}"))?;

    // Serve 4 sequential connections (VerifyFull, VerifyCa, untrusted CA, wrong hostname).
    let srv = thread::spawn(move || {
        for _ in 0..4 {
            if let Ok((tcp, _)) = listener.accept()
                && let Ok(mut tls) = acceptor.accept(tcp)
            {
                let mut buf = [0u8; 64];
                if let Ok(n) = tls.read(&mut buf)
                    && n > 0
                {
                    let _ = tls.write_all(&buf[..n]);
                }
            }
        }
    });

    // Case 1: VerifyFull with matching SAN (`localhost`) + trusted CA succeeds.
    {
        let tcp = TcpStream::connect(("127.0.0.1", port))?;
        let mut tls = TlsStream::connect(
            tcp,
            "localhost",
            &TlsClientConfig {
                verify_peer: true,
                verify_hostname: true,
                ca_cert_path: Some(cert_path.clone()),
            },
        )?;
        tls.write_all(b"hello-tls-full")?;
        let mut echo = [0u8; 14];
        tls.read_exact(&mut echo)?;
        assert_eq!(&echo, b"hello-tls-full");
    }

    // Case 2: VerifyCa with CA (no hostname check) succeeds even for arbitrary name.
    {
        let tcp = TcpStream::connect(("127.0.0.1", port))?;
        let mut tls = TlsStream::connect(
            tcp,
            "other.local",
            &TlsClientConfig {
                verify_peer: true,
                verify_hostname: false,
                ca_cert_path: Some(cert_path.clone()),
            },
        )?;
        tls.write_all(b"hello-ca")?;
        let mut echo = [0u8; 8];
        tls.read_exact(&mut echo)?;
        assert_eq!(&echo, b"hello-ca");
    }

    // Case 3: Untrusted self-signed cert without `ca_cert_path` MUST be rejected!
    {
        let tcp = TcpStream::connect(("127.0.0.1", port))?;
        let res = TlsStream::connect(
            tcp,
            "localhost",
            &TlsClientConfig {
                verify_peer: true,
                verify_hostname: true,
                ca_cert_path: None,
            },
        );
        assert!(res.is_err(), "untrusted self-signed cert must fail verify");
    }

    // Case 4: VerifyFull with mismatched hostname MUST be rejected!
    {
        let tcp = TcpStream::connect(("127.0.0.1", port))?;
        let res = TlsStream::connect(
            tcp,
            "wrong.example.test",
            &TlsClientConfig {
                verify_peer: true,
                verify_hostname: true,
                ca_cert_path: Some(cert_path),
            },
        );
        assert!(res.is_err(), "mismatched hostname must fail VerifyFull");
    }

    let _ = srv.join();
    let _ = fs::remove_dir_all(&dir);
    Ok(())
}

// ===========================================================================
// 4. Full In-Process PostgreSQL v3.0 Wire Test Server (TLS + Auth + Extended Query)
// ===========================================================================

#[derive(Clone, Copy)]
enum PgTestAuth {
    Cleartext,
    Md5,
    ScramSha256,
}

enum ServerStream {
    Plain(TcpStream),
    Tls(TlsStream),
}

impl Read for ServerStream {
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        match self {
            Self::Plain(s) => s.read(buf),
            Self::Tls(s) => s.read(buf),
        }
    }
}

impl Write for ServerStream {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        match self {
            Self::Plain(s) => s.write(buf),
            Self::Tls(s) => s.write(buf),
        }
    }

    fn flush(&mut self) -> std::io::Result<()> {
        match self {
            Self::Plain(s) => s.flush(),
            Self::Tls(s) => s.flush(),
        }
    }
}

fn srv_write_msg(stream: &mut ServerStream, tag: u8, payload: &[u8]) -> std::io::Result<()> {
    let len = (payload.len() + 4) as i32;
    let mut frame = Vec::with_capacity(5 + payload.len());
    frame.push(tag);
    frame.extend_from_slice(&len.to_be_bytes());
    frame.extend_from_slice(payload);
    stream.write_all(&frame)?;
    stream.flush()
}

fn srv_send_error(stream: &mut ServerStream, code: &str, msg: &str) -> std::io::Result<()> {
    let mut payload = Vec::new();
    payload.push(b'S');
    payload.extend_from_slice(b"ERROR\0");
    payload.push(b'C');
    payload.extend_from_slice(code.as_bytes());
    payload.push(0);
    payload.push(b'M');
    payload.extend_from_slice(msg.as_bytes());
    payload.push(0);
    payload.push(0);
    srv_write_msg(stream, b'E', &payload)
}

fn srv_read_msg(stream: &mut ServerStream) -> std::io::Result<Option<(u8, Vec<u8>)>> {
    let mut hdr = [0u8; 5];
    match stream.read_exact(&mut hdr) {
        Ok(()) => {}
        Err(e) if e.kind() == std::io::ErrorKind::UnexpectedEof => return Ok(None),
        Err(e) => return Err(e),
    }
    let tag = hdr[0];
    let len = i32::from_be_bytes([hdr[1], hdr[2], hdr[3], hdr[4]]);
    let body_len = (len - 4).max(0) as usize;
    let mut body = vec![0u8; body_len];
    if body_len > 0 {
        stream.read_exact(&mut body)?;
    }
    Ok(Some((tag, body)))
}

fn rewrite_pg_placeholders_to_sqlite(sql: &str) -> String {
    let bytes = sql.as_bytes();
    let mut out = String::with_capacity(sql.len());
    let mut i = 0;
    let mut in_single = false;
    let mut in_double = false;
    while i < bytes.len() {
        let b = bytes[i];
        if b == b'\'' && !in_double {
            in_single = !in_single;
            out.push('\'');
            i += 1;
        } else if b == b'"' && !in_single {
            in_double = !in_double;
            out.push('"');
            i += 1;
        } else if b == b'$' && !in_single && !in_double {
            let start = i + 1;
            let mut end = start;
            while end < bytes.len() && bytes[end].is_ascii_digit() {
                end += 1;
            }
            if end > start {
                out.push('?');
                out.push_str(&sql[start..end]);
                i = end;
            } else {
                out.push('$');
                i += 1;
            }
        } else {
            out.push(b as char);
            i += 1;
        }
    }
    out
}

fn srv_send_row_desc(stream: &mut ServerStream, cols: &[(&str, u32)]) -> std::io::Result<()> {
    let mut p = Vec::new();
    p.extend_from_slice(&(cols.len() as i16).to_be_bytes());
    for &(name, type_oid) in cols {
        p.extend_from_slice(name.as_bytes());
        p.push(0);
        p.extend_from_slice(&0u32.to_be_bytes()); // table_oid
        p.extend_from_slice(&0i16.to_be_bytes()); // attr_num
        p.extend_from_slice(&type_oid.to_be_bytes());
        p.extend_from_slice(&(-1i16).to_be_bytes()); // type_size
        p.extend_from_slice(&(-1i32).to_be_bytes()); // type_mod
        p.extend_from_slice(&0i16.to_be_bytes()); // text format
    }
    srv_write_msg(stream, b'T', &p)
}

fn srv_send_data_row(stream: &mut ServerStream, cells: &[Option<Vec<u8>>]) -> std::io::Result<()> {
    let mut p = Vec::new();
    p.extend_from_slice(&(cells.len() as i16).to_be_bytes());
    for cell in cells {
        match cell {
            None => p.extend_from_slice(&(-1i32).to_be_bytes()),
            Some(bytes) => {
                p.extend_from_slice(&(bytes.len() as i32).to_be_bytes());
                p.extend_from_slice(bytes);
            }
        }
    }
    srv_write_msg(stream, b'D', &p)
}

fn sqlite_decl_to_pg_meta(decl: &str) -> (&'static str, &'static str, u32) {
    let u = decl.trim().to_ascii_uppercase();
    if u.contains("BOOL") {
        ("boolean", "bool", oid::BOOL)
    } else if u.contains("INT") {
        ("bigint", "int8", oid::INT8)
    } else if u.contains("DEC") || u.contains("NUM") {
        ("numeric", "numeric", oid::NUMERIC)
    } else if u.contains("REAL") || u.contains("FLOA") || u.contains("DOUB") {
        ("double precision", "float8", oid::FLOAT8)
    } else if u.contains("BLOB") || u.contains("BYTE") {
        ("bytea", "bytea", oid::BYTEA)
    } else if u.contains("TIMESTAMP") {
        ("timestamp with time zone", "timestamptz", oid::TIMESTAMPTZ)
    } else if u.contains("DATE") {
        ("date", "date", oid::DATE)
    } else if u.contains("DURATION") || u.contains("INTERVAL") {
        ("interval", "interval", oid::INTERVAL)
    } else {
        ("text", "text", oid::TEXT)
    }
}

struct PgServerConfig {
    auth: PgTestAuth,
    user: String,
    password: String,
    tls_pem: Option<(String, String)>,
    init_sql: String,
    max_connections: usize,
}

fn spawn_pg_test_server(cfg: PgServerConfig) -> TestResult<(u16, thread::JoinHandle<()>)> {
    let listener = TcpListener::bind("127.0.0.1:0")?;
    let port = listener.local_addr()?.port();

    let handle = thread::spawn(move || {
        let Ok(sqlite) = SqliteConn::open_in_memory() else {
            return;
        };
        if !cfg.init_sql.is_empty() && sqlite.execute_batch(&cfg.init_sql).is_err() {
            return;
        }
        let acceptor = cfg
            .tls_pem
            .as_ref()
            .and_then(|(c, k)| TlsServerAcceptor::from_pem_files(c, k).ok());

        for _ in 0..cfg.max_connections {
            let Ok((tcp, _)) = listener.accept() else {
                break;
            };
            let _ = handle_pg_connection(tcp, &sqlite, acceptor.as_ref(), &cfg);
        }
    });

    Ok((port, handle))
}

fn handle_pg_connection(
    mut tcp: TcpStream,
    sqlite: &SqliteConn,
    acceptor: Option<&TlsServerAcceptor>,
    cfg: &PgServerConfig,
) -> std::io::Result<()> {
    // Read first 8 bytes: either SSLRequest (len=8, code=80877103) or StartupMessage.
    let mut len_buf = [0u8; 4];
    tcp.read_exact(&mut len_buf)?;
    let mut startup_len = i32::from_be_bytes(len_buf) as usize;
    let mut code_buf = [0u8; 4];
    tcp.read_exact(&mut code_buf)?;
    let mut code = i32::from_be_bytes(code_buf);

    let mut stream = if startup_len == 8 && code == 80_877_103 {
        if let Some(acc) = acceptor {
            tcp.write_all(b"S")?;
            tcp.flush()?;
            let tls = match acc.accept(tcp) {
                Ok(t) => t,
                Err(_) => return Ok(()),
            };
            let mut s = ServerStream::Tls(tls);
            s.read_exact(&mut len_buf)?;
            startup_len = i32::from_be_bytes(len_buf) as usize;
            s.read_exact(&mut code_buf)?;
            code = i32::from_be_bytes(code_buf);
            s
        } else {
            tcp.write_all(b"N")?;
            tcp.flush()?;
            let mut s = ServerStream::Plain(tcp);
            match s.read_exact(&mut len_buf) {
                Ok(()) => {}
                Err(_) => return Ok(()),
            }
            startup_len = i32::from_be_bytes(len_buf) as usize;
            s.read_exact(&mut code_buf)?;
            code = i32::from_be_bytes(code_buf);
            s
        }
    } else {
        ServerStream::Plain(tcp)
    };

    if code != 196_608 {
        let _ = srv_send_error(&mut stream, "08P01", "unsupported protocol version");
        return Ok(());
    }
    let rest_len = startup_len.saturating_sub(8);
    let mut startup_body = vec![0u8; rest_len];
    stream.read_exact(&mut startup_body)?;

    // Parse startup user.
    let mut startup_params = HashMap::new();
    let mut pos = 0;
    while pos < startup_body.len() && startup_body[pos] != 0 {
        let k_end = startup_body[pos..]
            .iter()
            .position(|&b| b == 0)
            .unwrap_or(startup_body.len() - pos);
        let k = String::from_utf8_lossy(&startup_body[pos..pos + k_end]).into_owned();
        pos += k_end + 1;
        if pos >= startup_body.len() {
            break;
        }
        let v_end = startup_body[pos..]
            .iter()
            .position(|&b| b == 0)
            .unwrap_or(startup_body.len() - pos);
        let v = String::from_utf8_lossy(&startup_body[pos..pos + v_end]).into_owned();
        pos += v_end + 1;
        startup_params.insert(k, v);
    }
    let client_user = startup_params.get("user").cloned().unwrap_or_default();

    // Perform requested authentication handshake.
    let authed = match cfg.auth {
        PgTestAuth::Cleartext => {
            srv_write_msg(&mut stream, b'R', &3i32.to_be_bytes())?;
            match srv_read_msg(&mut stream)? {
                Some((b'p', body)) => {
                    let end = body.iter().position(|&b| b == 0).unwrap_or(body.len());
                    let pass = String::from_utf8_lossy(&body[..end]);
                    client_user == cfg.user && pass == cfg.password
                }
                _ => false,
            }
        }
        PgTestAuth::Md5 => {
            let salt = [0x42u8, 0x19, 0xA7, 0x5C];
            let mut p = Vec::with_capacity(8);
            p.extend_from_slice(&5i32.to_be_bytes());
            p.extend_from_slice(&salt);
            srv_write_msg(&mut stream, b'R', &p)?;
            match srv_read_msg(&mut stream)? {
                Some((b'p', body)) => {
                    let end = body.iter().position(|&b| b == 0).unwrap_or(body.len());
                    let resp = String::from_utf8_lossy(&body[..end]);
                    let expected = pg_md5_password(&cfg.user, &cfg.password, salt);
                    client_user == cfg.user && resp == expected
                }
                _ => false,
            }
        }
        PgTestAuth::ScramSha256 => {
            // Send AuthenticationSASL offering SCRAM-SHA-256.
            let mut init_p = Vec::new();
            init_p.extend_from_slice(&10i32.to_be_bytes());
            init_p.extend_from_slice(b"SCRAM-SHA-256\0\0");
            srv_write_msg(&mut stream, b'R', &init_p)?;

            let Some((b'p', resp1)) = srv_read_msg(&mut stream)? else {
                return Ok(());
            };
            let Some(mech_nul) = resp1.iter().position(|&b| b == 0) else {
                return Ok(());
            };
            if &resp1[..mech_nul] != b"SCRAM-SHA-256" || resp1.len() < mech_nul + 5 {
                let _ = srv_send_error(&mut stream, "28000", "invalid SASL mechanism");
                return Ok(());
            }
            let c_len = i32::from_be_bytes([
                resp1[mech_nul + 1],
                resp1[mech_nul + 2],
                resp1[mech_nul + 3],
                resp1[mech_nul + 4],
            ]) as usize;
            let client_first = String::from_utf8_lossy(
                &resp1[mech_nul + 5..(mech_nul + 5 + c_len).min(resp1.len())],
            )
            .into_owned();
            let client_first_bare = client_first
                .strip_prefix("n,,")
                .unwrap_or(client_first.as_str());
            let client_nonce = client_first_bare
                .split(',')
                .find_map(|p| p.strip_prefix("r="))
                .unwrap_or("");

            let salt = b"dana_scram_salt!";
            let iter: u32 = 128;
            let combined_nonce = format!("{client_nonce}srvNonce987654");
            let server_first = format!("r={combined_nonce},s={},i={iter}", base64_encode(salt));

            let mut cont_p = Vec::new();
            cont_p.extend_from_slice(&11i32.to_be_bytes());
            cont_p.extend_from_slice(server_first.as_bytes());
            srv_write_msg(&mut stream, b'R', &cont_p)?;

            let Some((b'p', resp2)) = srv_read_msg(&mut stream)? else {
                return Ok(());
            };
            let client_final = String::from_utf8_lossy(&resp2).into_owned();
            let Some((cf_no_proof, proof_b64)) = client_final.rsplit_once(",p=") else {
                let _ = srv_send_error(&mut stream, "28P01", "malformed SCRAM client-final");
                return Ok(());
            };

            let salted = scram_pbkdf2_hmac_sha256(cfg.password.as_bytes(), salt, iter);
            let client_key = hmac_sha256(&salted, b"Client Key");
            let stored_key = sha256(&client_key);
            let server_key = hmac_sha256(&salted, b"Server Key");
            let auth_msg = format!("{client_first_bare},{server_first},{cf_no_proof}");
            let client_sig = hmac_sha256(&stored_key, auth_msg.as_bytes());
            let Ok(proof_bytes) = base64_decode(proof_b64) else {
                let _ = srv_send_error(&mut stream, "28P01", "invalid base64 proof");
                return Ok(());
            };
            let valid = client_user == cfg.user && proof_bytes.len() == 32 && {
                let mut recovered_key = [0u8; 32];
                for i in 0..32 {
                    recovered_key[i] = proof_bytes[i] ^ client_sig[i];
                }
                sha256(&recovered_key) == stored_key
            };

            if valid {
                let server_sig = hmac_sha256(&server_key, auth_msg.as_bytes());
                let server_final = format!("v={}", base64_encode(&server_sig));
                let mut fin_p = Vec::new();
                fin_p.extend_from_slice(&12i32.to_be_bytes());
                fin_p.extend_from_slice(server_final.as_bytes());
                srv_write_msg(&mut stream, b'R', &fin_p)?;
                true
            } else {
                false
            }
        }
    };

    if !authed {
        srv_send_error(&mut stream, "28P01", "password authentication failed")?;
        return Ok(());
    }

    srv_write_msg(&mut stream, b'R', &0i32.to_be_bytes())?;
    for (k, v) in [
        ("server_version", "16.0-dana-test"),
        ("client_encoding", "UTF8"),
        ("TimeZone", "UTC"),
    ] {
        let mut p = Vec::new();
        p.extend_from_slice(k.as_bytes());
        p.push(0);
        p.extend_from_slice(v.as_bytes());
        p.push(0);
        srv_write_msg(&mut stream, b'S', &p)?;
    }
    srv_write_msg(&mut stream, b'Z', b"I")?;

    // Extended Query Protocol state loop.
    let mut parsed_sql = String::new();
    let mut bound_params: Vec<(i16, Option<Vec<u8>>)> = Vec::new();

    while let Some((tag, body)) = srv_read_msg(&mut stream)? {
        match tag {
            b'P' => {
                // Parse: stmt_name\0 query\0 n_oids ...
                let nul1 = body.iter().position(|&b| b == 0).unwrap_or(0);
                let after1 = &body[nul1 + 1..];
                let nul2 = after1.iter().position(|&b| b == 0).unwrap_or(after1.len());
                parsed_sql = String::from_utf8_lossy(&after1[..nul2]).into_owned();
                srv_write_msg(&mut stream, b'1', &[])?;
            }
            b'B' => {
                // Bind: portal\0 stmt\0 n_fmt fmt[] n_params (len val)[] ...
                let nul1 = body.iter().position(|&b| b == 0).unwrap_or(0);
                let mut p = nul1 + 1;
                let nul2 = body[p..].iter().position(|&b| b == 0).unwrap_or(0);
                p += nul2 + 1;
                let n_fmt = i16::from_be_bytes([body[p], body[p + 1]]) as usize;
                p += 2;
                let mut fmts = Vec::with_capacity(n_fmt);
                for _ in 0..n_fmt {
                    fmts.push(i16::from_be_bytes([body[p], body[p + 1]]));
                    p += 2;
                }
                let n_params = i16::from_be_bytes([body[p], body[p + 1]]) as usize;
                p += 2;
                bound_params.clear();
                for idx in 0..n_params {
                    let fmt = if fmts.len() == 1 {
                        fmts[0]
                    } else {
                        fmts.get(idx).copied().unwrap_or(0)
                    };
                    let len = i32::from_be_bytes([body[p], body[p + 1], body[p + 2], body[p + 3]]);
                    p += 4;
                    if len == -1 {
                        bound_params.push((fmt, None));
                    } else {
                        let ulen = len as usize;
                        bound_params.push((fmt, Some(body[p..p + ulen].to_vec())));
                        p += ulen;
                    }
                }
                srv_write_msg(&mut stream, b'2', &[])?;
            }
            b'D' => {
                // Describe portal: emit RowDescription / NoData during Execute or here.
                // Deferring actual execution to Execute; if non-SELECT we emit NoData in Execute.
            }
            b'E' => {
                if let Err(err_msg) =
                    execute_pg_on_sqlite(&mut stream, sqlite, &parsed_sql, &bound_params)
                {
                    srv_send_error(&mut stream, "42000", &err_msg)?;
                }
            }
            b'S' => {
                srv_write_msg(&mut stream, b'Z', b"I")?;
            }
            b'X' => break,
            _ => {}
        }
    }
    Ok(())
}

fn execute_pg_on_sqlite(
    stream: &mut ServerStream,
    sqlite: &SqliteConn,
    pg_sql: &str,
    params: &[(i16, Option<Vec<u8>>)],
) -> Result<(), String> {
    let trimmed = pg_sql.trim();
    let requested_schemas: Vec<String> = params
        .iter()
        .filter_map(|(_, bytes_opt)| {
            bytes_opt
                .as_ref()
                .map(|b| String::from_utf8_lossy(b).into_owned())
        })
        .collect();
    let collect_sqlite_schemas = || -> Result<Vec<(String, String)>, String> {
        let mut db_stmt = sqlite
            .prepare("PRAGMA database_list")
            .map_err(|e| e.to_string())?;
        let mut out = Vec::new();
        while db_stmt.step().map_err(|e| e.to_string())? == StepResult::Row {
            let sqlite_db = db_stmt.column_text(1).map_err(|e| e.to_string())?;
            if sqlite_db == "temp" {
                continue;
            }
            let pg_schema = if sqlite_db == "main" {
                "public".to_string()
            } else {
                sqlite_db.clone()
            };
            if requested_schemas.is_empty() || requested_schemas.iter().any(|s| s == &pg_schema) {
                out.push((sqlite_db, pg_schema));
            }
        }
        out.sort_by(|a, b| a.1.cmp(&b.1));
        Ok(out)
    };

    // Handle `information_schema` introspection queries against real SQLite catalog metadata!
    if trimmed.contains("information_schema.table_constraints") {
        srv_send_row_desc(
            stream,
            &[
                ("table_schema", oid::TEXT),
                ("table_name", oid::TEXT),
                ("column_name", oid::TEXT),
            ],
        )
        .map_err(|e| e.to_string())?;
        let mut count = 0usize;
        for (sqlite_db, pg_schema) in collect_sqlite_schemas()? {
            let master_sql = format!(
                "SELECT name FROM \"{sqlite_db}\".sqlite_master \
                 WHERE type = 'table' AND name NOT LIKE 'sqlite_%' ORDER BY name"
            );
            let mut t_stmt = sqlite.prepare(&master_sql).map_err(|e| e.to_string())?;
            let mut tables = Vec::new();
            while t_stmt.step().map_err(|e| e.to_string())? == StepResult::Row {
                tables.push(t_stmt.column_text(0).map_err(|e| e.to_string())?);
            }
            for t in tables {
                let mut p_stmt = sqlite
                    .prepare(&format!("PRAGMA \"{sqlite_db}\".table_info(\"{t}\")"))
                    .map_err(|e| e.to_string())?;
                while p_stmt.step().map_err(|e| e.to_string())? == StepResult::Row {
                    let cname = p_stmt.column_text(1).map_err(|e| e.to_string())?;
                    let pk = p_stmt.column_int64(5) > 0;
                    if pk {
                        srv_send_data_row(
                            stream,
                            &[
                                Some(pg_schema.as_bytes().to_vec()),
                                Some(t.as_bytes().to_vec()),
                                Some(cname.into_bytes()),
                            ],
                        )
                        .map_err(|e| e.to_string())?;
                        count += 1;
                    }
                }
            }
        }
        srv_write_msg(stream, b'C', format!("SELECT {count}\0").as_bytes())
            .map_err(|e| e.to_string())?;
        return Ok(());
    }

    if trimmed.contains("information_schema.columns") {
        srv_send_row_desc(
            stream,
            &[
                ("table_schema", oid::TEXT),
                ("table_name", oid::TEXT),
                ("column_name", oid::TEXT),
                ("data_type", oid::TEXT),
                ("udt_name", oid::TEXT),
                ("is_nullable", oid::TEXT),
            ],
        )
        .map_err(|e| e.to_string())?;
        let mut count = 0usize;
        for (sqlite_db, pg_schema) in collect_sqlite_schemas()? {
            let master_sql = format!(
                "SELECT name FROM \"{sqlite_db}\".sqlite_master \
                 WHERE type = 'table' AND name NOT LIKE 'sqlite_%' ORDER BY name"
            );
            let mut t_stmt = sqlite.prepare(&master_sql).map_err(|e| e.to_string())?;
            let mut tables = Vec::new();
            while t_stmt.step().map_err(|e| e.to_string())? == StepResult::Row {
                tables.push(t_stmt.column_text(0).map_err(|e| e.to_string())?);
            }
            for t in tables {
                let mut p_stmt = sqlite
                    .prepare(&format!("PRAGMA \"{sqlite_db}\".table_info(\"{t}\")"))
                    .map_err(|e| e.to_string())?;
                while p_stmt.step().map_err(|e| e.to_string())? == StepResult::Row {
                    let cname = p_stmt.column_text(1).map_err(|e| e.to_string())?;
                    let decl = p_stmt.column_text(2).map_err(|e| e.to_string())?;
                    let notnull = p_stmt.column_int64(3) != 0;
                    let pk = p_stmt.column_int64(5) > 0;
                    let (dt, udt, _) = sqlite_decl_to_pg_meta(&decl);
                    let nullable = if !notnull && !pk { "YES" } else { "NO" };
                    srv_send_data_row(
                        stream,
                        &[
                            Some(pg_schema.as_bytes().to_vec()),
                            Some(t.as_bytes().to_vec()),
                            Some(cname.into_bytes()),
                            Some(dt.as_bytes().to_vec()),
                            Some(udt.as_bytes().to_vec()),
                            Some(nullable.as_bytes().to_vec()),
                        ],
                    )
                    .map_err(|e| e.to_string())?;
                    count += 1;
                }
            }
        }
        srv_write_msg(stream, b'C', format!("SELECT {count}\0").as_bytes())
            .map_err(|e| e.to_string())?;
        return Ok(());
    }

    // Build column-name -> OID lookup from SQLite schema for accurate Postgres RowDescriptions.
    let mut col_oids: HashMap<String, u32> = HashMap::new();
    {
        let mut t_stmt = sqlite
            .prepare(
                "SELECT name FROM sqlite_master WHERE type = 'table' AND name NOT LIKE 'sqlite_%'",
            )
            .map_err(|e| e.to_string())?;
        let mut tables = Vec::new();
        while t_stmt.step().map_err(|e| e.to_string())? == StepResult::Row {
            tables.push(t_stmt.column_text(0).map_err(|e| e.to_string())?);
        }
        for t in tables {
            let mut p_stmt = sqlite
                .prepare(&format!("PRAGMA table_info(\"{t}\")"))
                .map_err(|e| e.to_string())?;
            while p_stmt.step().map_err(|e| e.to_string())? == StepResult::Row {
                let cname = p_stmt.column_text(1).map_err(|e| e.to_string())?;
                let decl = p_stmt.column_text(2).map_err(|e| e.to_string())?;
                let (_, _, type_oid) = sqlite_decl_to_pg_meta(&decl);
                col_oids.insert(cname, type_oid);
            }
        }
    }

    let sqlite_sql = rewrite_pg_placeholders_to_sqlite(trimmed);
    let mut stmt = sqlite.prepare(&sqlite_sql).map_err(|e| e.to_string())?;

    for (idx, (fmt, val)) in params.iter().enumerate() {
        let bind_idx = (idx + 1) as i32;
        match val {
            None => stmt.bind_null(bind_idx).map_err(|e| e.to_string())?,
            Some(bytes) if *fmt == 1 => {
                stmt.bind_blob(bind_idx, bytes).map_err(|e| e.to_string())?
            }
            Some(bytes) => {
                let s = String::from_utf8_lossy(bytes);
                if let Ok(n) = s.parse::<i64>() {
                    stmt.bind_int64(bind_idx, n).map_err(|e| e.to_string())?;
                } else if s == "true" {
                    stmt.bind_int64(bind_idx, 1).map_err(|e| e.to_string())?;
                } else if s == "false" {
                    stmt.bind_int64(bind_idx, 0).map_err(|e| e.to_string())?;
                } else {
                    stmt.bind_text(bind_idx, &s).map_err(|e| e.to_string())?;
                }
            }
        }
    }

    let n_cols = stmt.column_count();
    if n_cols == 0 {
        while stmt.step().map_err(|e| e.to_string())? == StepResult::Row {}
        srv_write_msg(stream, b'n', &[]).map_err(|e| e.to_string())?;
        let changes = sqlite.changes();
        let cmd = if trimmed.to_ascii_uppercase().starts_with("INSERT") {
            format!("INSERT 0 {changes}\0")
        } else if trimmed.to_ascii_uppercase().starts_with("UPDATE") {
            format!("UPDATE {changes}\0")
        } else if trimmed.to_ascii_uppercase().starts_with("DELETE") {
            format!("DELETE {changes}\0")
        } else {
            "OK\0".to_string()
        };
        srv_write_msg(stream, b'C', cmd.as_bytes()).map_err(|e| e.to_string())?;
        return Ok(());
    }

    let col_names: Vec<String> = (0..n_cols)
        .map(|i| stmt.column_name(i).unwrap_or_else(|| format!("col{i}")))
        .collect();
    let col_desc: Vec<(&str, u32)> = col_names
        .iter()
        .map(|n| (n.as_str(), col_oids.get(n).copied().unwrap_or(0)))
        .collect();
    srv_send_row_desc(stream, &col_desc).map_err(|e| e.to_string())?;

    let mut row_count = 0usize;
    while stmt.step().map_err(|e| e.to_string())? == StepResult::Row {
        let mut cells = Vec::with_capacity(n_cols);
        for (ci, &(_, type_oid)) in col_desc.iter().enumerate() {
            let v = match stmt.column_type(ci) {
                SqliteValueType::Null => None,
                SqliteValueType::Integer => {
                    let n = stmt.column_int64(ci);
                    if type_oid == oid::BOOL {
                        Some(if n != 0 { b"t".to_vec() } else { b"f".to_vec() })
                    } else {
                        Some(n.to_string().into_bytes())
                    }
                }
                SqliteValueType::Float => Some(stmt.column_double(ci).to_string().into_bytes()),
                SqliteValueType::Text => {
                    let s = stmt.column_text(ci).map_err(|e| e.to_string())?;
                    Some(s.into_bytes())
                }
                SqliteValueType::Blob => {
                    let bs = stmt.column_blob(ci);
                    Some(format!("\\x{}", to_hex_lower(&bs)).into_bytes())
                }
            };
            cells.push(v);
        }
        srv_send_data_row(stream, &cells).map_err(|e| e.to_string())?;
        row_count += 1;
    }

    srv_write_msg(stream, b'C', format!("SELECT {row_count}\0").as_bytes())
        .map_err(|e| e.to_string())?;
    Ok(())
}

#[test]
fn postgres_auth_cleartext_md5_scram_and_tls_modes() -> TestResult {
    let dir = unique_temp_dir("pg_auth_tls")?;
    let (cert_path, key_path) = generate_self_signed_cert(&dir)?;

    // 1. Cleartext auth (plaintext + bad password rejection)
    {
        let (port, srv) = spawn_pg_test_server(PgServerConfig {
            auth: PgTestAuth::Cleartext,
            user: "dana".to_string(),
            password: "clear-pass!".to_string(),
            tls_pem: None,
            init_sql: String::new(),
            max_connections: 2,
        })?;

        let ok_uri = format!("postgres://dana:clear-pass!@127.0.0.1:{port}/app?sslmode=disable");
        let DbUri::Postgres(p_ok) = DbUri::parse(&ok_uri)? else {
            return Err("expected postgres uri".into());
        };
        let drv = PostgresDriver::connect(&p_ok)?;
        assert!(!drv.is_tls());
        assert_eq!(drv.server_param("TimeZone"), Some("UTC"));
        drop(drv);

        let bad_uri = format!("postgres://dana:wrong@127.0.0.1:{port}/app?sslmode=disable");
        let DbUri::Postgres(p_bad) = DbUri::parse(&bad_uri)? else {
            return Err("expected postgres uri".into());
        };
        assert!(matches!(
            PostgresDriver::connect(&p_bad),
            Err(DbError::Auth(_))
        ));
        let _ = srv.join();
    }

    // 2. MD5 auth (with Prefer fallback to plaintext + bad password rejection)
    {
        let (port, srv) = spawn_pg_test_server(PgServerConfig {
            auth: PgTestAuth::Md5,
            user: "dana".to_string(),
            password: "md5-password".to_string(),
            tls_pem: None,
            init_sql: String::new(),
            max_connections: 2,
        })?;

        let ok_uri = format!("postgres://dana:md5-password@127.0.0.1:{port}/app?sslmode=prefer");
        let DbUri::Postgres(p_ok) = DbUri::parse(&ok_uri)? else {
            return Err("expected postgres uri".into());
        };
        let drv = PostgresDriver::connect(&p_ok)?;
        assert!(!drv.is_tls());
        drop(drv);

        let bad_uri = format!("postgres://dana:nope@127.0.0.1:{port}/app?sslmode=disable");
        let DbUri::Postgres(p_bad) = DbUri::parse(&bad_uri)? else {
            return Err("expected postgres uri".into());
        };
        assert!(matches!(
            PostgresDriver::connect(&p_bad),
            Err(DbError::Auth(_))
        ));
        let _ = srv.join();
    }

    // 3. SCRAM-SHA-256 + real OpenSSL TLS (VerifyCa, VerifyFull, untrusted CA rejection, bad password)
    {
        let (port, srv) = spawn_pg_test_server(PgServerConfig {
            auth: PgTestAuth::ScramSha256,
            user: "dana".to_string(),
            password: "scram-secret-42".to_string(),
            tls_pem: Some((cert_path.clone(), key_path)),
            init_sql: String::new(),
            max_connections: 4,
        })?;

        // VerifyCa succeeds over real TLS + SCRAM-SHA-256
        let ca_uri = format!(
            "postgres://dana:scram-secret-42@127.0.0.1:{port}/app?sslmode=verify-ca&sslrootcert={cert_path}"
        );
        let DbUri::Postgres(p_ca) = DbUri::parse(&ca_uri)? else {
            return Err("expected postgres uri".into());
        };
        let drv_ca = PostgresDriver::connect(&p_ca)?;
        assert!(drv_ca.is_tls());
        drop(drv_ca);

        // VerifyFull to `localhost` succeeds over real TLS + SCRAM-SHA-256
        let full_uri = format!(
            "postgres://dana:scram-secret-42@localhost:{port}/app?sslmode=verify-full&sslrootcert={cert_path}"
        );
        let DbUri::Postgres(p_full) = DbUri::parse(&full_uri)? else {
            return Err("expected postgres uri".into());
        };
        let drv_full = PostgresDriver::connect(&p_full)?;
        assert!(drv_full.is_tls());
        drop(drv_full);

        // VerifyCa WITHOUT sslrootcert rejects self-signed cert
        let untrusted_uri =
            format!("postgres://dana:scram-secret-42@127.0.0.1:{port}/app?sslmode=verify-ca");
        let DbUri::Postgres(p_untrusted) = DbUri::parse(&untrusted_uri)? else {
            return Err("expected postgres uri".into());
        };
        assert!(matches!(
            PostgresDriver::connect(&p_untrusted),
            Err(DbError::Tls(_))
        ));

        // Wrong password rejected under SCRAM-SHA-256 over TLS
        let bad_pass_uri = format!(
            "postgres://dana:wrong-pass@127.0.0.1:{port}/app?sslmode=verify-ca&sslrootcert={cert_path}"
        );
        let DbUri::Postgres(p_bad) = DbUri::parse(&bad_pass_uri)? else {
            return Err("expected postgres uri".into());
        };
        assert!(matches!(
            PostgresDriver::connect(&p_bad),
            Err(DbError::Auth(_))
        ));

        let _ = srv.join();
    }

    let _ = fs::remove_dir_all(&dir);
    Ok(())
}

#[test]
fn postgres_extended_query_all_types_introspect_upsert_and_dry_run() -> TestResult {
    let dir = unique_temp_dir("pg_e2e")?;
    let (cert_path, key_path) = generate_self_signed_cert(&dir)?;

    let init_sql = "
        CREATE TABLE orders (
            id INTEGER PRIMARY KEY,
            paid BOOLEAN NOT NULL,
            amount DECIMAL_TEXT NOT NULL,
            rate REAL NOT NULL,
            customer_email TEXT NOT NULL,
            sig BLOB NOT NULL,
            order_date DATE NOT NULL,
            created_at TIMESTAMP NOT NULL,
            sla DURATION NOT NULL,
            memo TEXT
        );
    ";
    let (port, srv) = spawn_pg_test_server(PgServerConfig {
        auth: PgTestAuth::ScramSha256,
        user: "dana".to_string(),
        password: "pg-test-pw".to_string(),
        tls_pem: Some((cert_path.clone(), key_path)),
        init_sql: init_sql.to_string(),
        max_connections: 1,
    })?;

    let uri = format!(
        "postgres://dana:pg-test-pw@localhost:{port}/shop?sslmode=verify-full&sslrootcert={cert_path}"
    );
    let mut conn = open_connection(&uri)?;
    assert_eq!(conn.dialect(), SqlDialect::Postgres);

    // 1. Parameterized inserts across all scalar types & Option null
    let dec1 = parse_decimal_bigint_strict("9876543210.123456789012345678")?;
    let dec2 = parse_decimal_bigint_strict("42.50")?;
    let d1 = days_from_civil(2025, 11, 24);
    let ts1 = parse_iso_timestamp("2025-11-24T18:45:00.500000Z")?;
    let dur1 = 3_600_000_000i64; // 1 hour in micros

    let ins_sql = "INSERT INTO orders (id, paid, amount, rate, customer_email, sig, order_date, created_at, sla, memo) \
                   VALUES ($1, $2, $3, $4, $5, $6, $7, $8, $9, $10)";
    let n1 = conn.execute(
        ins_sql,
        &[
            SqlParam::Int(101),
            SqlParam::Bool(true),
            SqlParam::Decimal(dec1.clone()),
            SqlParam::Float(Float64::from_f64(1.25)),
            SqlParam::Text("ada@example.org".to_string()),
            SqlParam::Bytes(vec![0xCA, 0xFE, 0xBA, 0xBE]),
            SqlParam::Date(d1),
            SqlParam::Timestamp(ts1),
            SqlParam::Duration(dur1),
            SqlParam::Text("rush".to_string()),
        ],
    )?;
    assert_eq!(n1, 1);

    let n2 = conn.execute(
        ins_sql,
        &[
            SqlParam::Int(102),
            SqlParam::Bool(false),
            SqlParam::Decimal(dec2.clone()),
            SqlParam::Float(Float64::from_f64(0.5)),
            SqlParam::Text("grace@example.org".to_string()),
            SqlParam::Bytes(vec![0x01, 0x02]),
            SqlParam::Date(d1),
            SqlParam::Timestamp(ts1),
            SqlParam::Duration(500_000),
            SqlParam::Null,
        ],
    )?;
    assert_eq!(n2, 1);

    // 2. Parameterized Extended Query read (query_rows + query_batches)
    let schema_cols = vec![
        col("id", ScalarTy::Int, &[]),
        col("paid", ScalarTy::Bool, &[]),
        col("amount", ScalarTy::Decimal, &["financial"]),
        col("rate", ScalarTy::Float, &[]),
        col("customer_email", ScalarTy::Text, &["pii"]),
        col("sig", ScalarTy::Bytes, &[]),
        col("order_date", ScalarTy::Date, &[]),
        col("created_at", ScalarTy::Timestamp, &[]),
        col("sla", ScalarTy::Duration, &[]),
        col("memo", opt(ScalarTy::Text), &[]),
    ];
    let schema = table_ty(schema_cols.clone());

    let tv = conn.query_rows(
        "SELECT id, paid, amount, rate, customer_email, sig, order_date, created_at, sla, memo \
         FROM orders WHERE id >= $1 ORDER BY id",
        &[SqlParam::Int(101)],
        &schema,
    )?;
    assert_eq!(tv.rows.len(), 2);
    assert!(val_eq(&tv.rows[0].cells[0], &Val::Int(BigInt::from(101))));
    assert!(val_eq(&tv.rows[0].cells[1], &Val::Bool(true)));
    assert!(val_eq(&tv.rows[0].cells[2], &Val::Decimal(dec1.clone())));
    assert!(val_eq(
        &tv.rows[0].cells[3],
        &Val::Float(Float64::from_f64(1.25))
    ));
    assert!(val_eq(
        &tv.rows[0].cells[4],
        &Val::Text("ada@example.org".to_string())
    ));
    assert!(val_eq(
        &tv.rows[0].cells[5],
        &Val::Bytes(vec![0xCA, 0xFE, 0xBA, 0xBE])
    ));
    assert!(val_eq(&tv.rows[0].cells[6], &Val::Date(BigInt::from(d1))));
    assert!(val_eq(
        &tv.rows[0].cells[7],
        &Val::Timestamp(BigInt::from(ts1))
    ));
    assert!(val_eq(
        &tv.rows[0].cells[8],
        &Val::Duration(BigInt::from(dur1))
    ));
    assert!(val_eq(
        &tv.rows[0].cells[9],
        &Val::OptSome(Box::new(Val::Text("rush".to_string())))
    ));
    assert!(val_eq(&tv.rows[1].cells[9], &Val::OptNone));

    // Batch streaming with batch_size=1 produces 2 batches matching `query_rows`.
    let batched = conn.query_batches(
        "SELECT id, paid, amount, rate, customer_email, sig, order_date, created_at, sla, memo \
         FROM orders ORDER BY id",
        &[],
        &schema,
        1,
    )?;
    assert_eq!(batched.batches.len(), 2);
    assert_eq!(batched.total_rows(), 2);

    // 3. Schema introspection via `information_schema`
    let locked = conn.introspect_schema("Shop")?;
    assert_eq!(locked.dialect, SqlDialect::Postgres);
    assert_eq!(locked.tables.len(), 1);
    let orders_tbl = &locked.tables[0];
    assert_eq!(orders_tbl.name, "orders");
    assert_eq!(orders_tbl.cols.len(), 10);
    assert!(orders_tbl.cols[0].pk);
    assert_eq!(orders_tbl.cols[1].ty, ScalarTy::Bool);
    assert_eq!(orders_tbl.cols[2].ty, ScalarTy::Decimal);
    assert_eq!(orders_tbl.cols[5].ty, ScalarTy::Bytes);
    assert_eq!(orders_tbl.cols[6].ty, ScalarTy::Date);
    assert_eq!(orders_tbl.cols[7].ty, ScalarTy::Timestamp);
    assert_eq!(orders_tbl.cols[8].ty, ScalarTy::Duration);
    assert!(orders_tbl.cols[9].nullable);

    // 4. Strictly read-only `dry_run` + transactional `upsert_table`
    let upsert_data = TableVal {
        cols: schema_cols,
        rows: vec![
            // Unchanged row 101
            tv.rows[0].clone(),
            // Updated row 102 (amount + customer_email + memo)
            TableRow {
                cells: vec![
                    Val::Int(BigInt::from(102)),
                    Val::Bool(true),
                    Val::Decimal(parse_decimal_bigint_strict("99.99")?),
                    Val::Float(Float64::from_f64(0.5)),
                    Val::Text("grace.updated@example.org".to_string()),
                    Val::Bytes(vec![0x01, 0x02]),
                    Val::Date(BigInt::from(d1)),
                    Val::Timestamp(BigInt::from(ts1)),
                    Val::Duration(BigInt::from(500_000)),
                    Val::OptSome(Box::new(Val::Text("upgraded".to_string()))),
                ],
                group_meta: None,
            },
            // New row 103
            TableRow {
                cells: vec![
                    Val::Int(BigInt::from(103)),
                    Val::Bool(true),
                    Val::Decimal(dec2),
                    Val::Float(Float64::from_f64(2.0)),
                    Val::Text("linus@example.org".to_string()),
                    Val::Bytes(vec![0xFF]),
                    Val::Date(BigInt::from(d1)),
                    Val::Timestamp(BigInt::from(ts1)),
                    Val::Duration(BigInt::from(1_000_000)),
                    Val::OptNone,
                ],
                group_meta: None,
            },
        ],
    };

    let dry = conn.upsert_table("orders", "id", &upsert_data, true)?;
    assert_eq!(dry.inserted, 1);
    assert_eq!(dry.updated, 1);
    assert_eq!(dry.unchanged, 1);
    let rendered = dry.render_redacted(&TagSet::empty());
    assert!(rendered.contains("[REDACTED:pii]"));
    assert!(rendered.contains("[REDACTED:financial]"));
    assert!(!rendered.contains("grace.updated@example.org"));
    assert!(!rendered.contains("linus@example.org"));
    assert!(!rendered.contains("99.99"));

    // Verify 0 DB changes after dry-run
    let still_two = conn.query_rows(
        "SELECT id, paid, amount, rate, customer_email, sig, order_date, created_at, sla, memo \
         FROM orders ORDER BY id",
        &[],
        &schema,
    )?;
    assert_eq!(still_two.rows.len(), 2);
    assert!(val_eq(
        &still_two.rows[1].cells[4],
        &Val::Text("grace@example.org".to_string())
    ));

    // Commit upsert and confirm 3 rows in DB
    let committed = conn.upsert_table("orders", "id", &upsert_data, false)?;
    assert_eq!(committed.inserted, 1);
    assert_eq!(committed.updated, 1);
    assert_eq!(committed.unchanged, 1);

    let after = conn.query_rows(
        "SELECT id, paid, amount, rate, customer_email, sig, order_date, created_at, sla, memo \
         FROM orders ORDER BY id",
        &[],
        &schema,
    )?;
    assert_eq!(after.rows.len(), 3);
    assert!(val_eq(
        &after.rows[1].cells[4],
        &Val::Text("grace.updated@example.org".to_string())
    ));
    assert!(val_eq(
        &after.rows[2].cells[4],
        &Val::Text("linus@example.org".to_string())
    ));

    drop(conn);
    let _ = srv.join();
    let _ = fs::remove_dir_all(&dir);
    Ok(())
}

/// Opt-in live PostgreSQL verification gated on `DANA_TEST_POSTGRES_URL`.
/// When unset, returns immediately without failing; when set, runs real queries & introspection.
#[test]
fn postgres_live_server_opt_in() -> TestResult {
    let Ok(url) = std::env::var("DANA_TEST_POSTGRES_URL") else {
        return Ok(());
    };
    if url.trim().is_empty() {
        return Ok(());
    }
    let mut conn = open_connection(&url)?;
    assert_eq!(conn.dialect(), SqlDialect::Postgres);

    let schema = table_ty(vec![
        col("n", ScalarTy::Int, &[]),
        col("msg", ScalarTy::Text, &[]),
    ]);
    let tv = conn.query_rows(
        "SELECT $1::bigint AS n, $2::text AS msg",
        &[SqlParam::Int(42), SqlParam::Text("dana-live".to_string())],
        &schema,
    )?;
    assert_eq!(tv.rows.len(), 1);
    assert!(val_eq(&tv.rows[0].cells[0], &Val::Int(BigInt::from(42))));
    assert!(val_eq(
        &tv.rows[0].cells[1],
        &Val::Text("dana-live".to_string())
    ));

    let _locked = conn.introspect_schema("LivePG")?;
    Ok(())
}

// ===========================================================================
// 5. Offline `schema.lock` Round-Trip, Tag-Preserving Merge & Drift Checks
// ===========================================================================

#[test]
fn schema_lock_roundtrip_merge_and_drift_verification() -> TestResult {
    let initial = SchemaLock {
        version: 1,
        dbs: vec![LockedDb {
            name: "Analytics".to_string(),
            dialect: SqlDialect::Postgres,
            tables: vec![
                LockedTable {
                    name: "orders".to_string(),
                    cols: vec![
                        LockedCol {
                            name: "id".to_string(),
                            ty: ScalarTy::Int,
                            nullable: false,
                            pk: true,
                            tags: TagSet::empty(),
                        },
                        LockedCol {
                            name: "customer_email".to_string(),
                            ty: ScalarTy::Text,
                            nullable: false,
                            pk: false,
                            tags: TagSet::singleton("pii"),
                        },
                        LockedCol {
                            name: "amount".to_string(),
                            ty: ScalarTy::Decimal,
                            nullable: false,
                            pk: false,
                            tags: TagSet::of_list(vec!["financial".to_string(), "pii".to_string()]),
                        },
                        LockedCol {
                            name: "legacy_note".to_string(),
                            ty: ScalarTy::Text,
                            nullable: true,
                            pk: false,
                            tags: TagSet::empty(),
                        },
                    ],
                },
                LockedTable {
                    name: "temp_stage".to_string(),
                    cols: vec![LockedCol {
                        name: "k".to_string(),
                        ty: ScalarTy::Int,
                        nullable: false,
                        pk: true,
                        tags: TagSet::empty(),
                    }],
                },
            ],
        }],
    };

    // Canonical format + parse round-trip
    let text = format_schema_lock(&initial);
    let reparsed = parse_schema_lock(&text)?;
    assert_eq!(reparsed, initial);
    assert_eq!(format_schema_lock(&reparsed), text);

    // Fresh introspection drops `temp_stage`, drops `legacy_note`, widens `amount` to nullable,
    // adds `orders.currency` and new table `customers`, and has EMPTY tags (DB doesn't store Dana tags).
    let fresh = LockedDb {
        name: "Analytics".to_string(),
        dialect: SqlDialect::Postgres,
        tables: vec![
            LockedTable {
                name: "orders".to_string(),
                cols: vec![
                    LockedCol {
                        name: "id".to_string(),
                        ty: ScalarTy::Int,
                        nullable: false,
                        pk: true,
                        tags: TagSet::empty(),
                    },
                    LockedCol {
                        name: "customer_email".to_string(),
                        ty: ScalarTy::Text,
                        nullable: false,
                        pk: false,
                        tags: TagSet::empty(),
                    },
                    LockedCol {
                        name: "amount".to_string(),
                        ty: ScalarTy::Decimal,
                        nullable: true,
                        pk: false,
                        tags: TagSet::empty(),
                    },
                    LockedCol {
                        name: "currency".to_string(),
                        ty: ScalarTy::Text,
                        nullable: false,
                        pk: false,
                        tags: TagSet::empty(),
                    },
                ],
            },
            LockedTable {
                name: "customers".to_string(),
                cols: vec![LockedCol {
                    name: "id".to_string(),
                    ty: ScalarTy::Int,
                    nullable: false,
                    pk: true,
                    tags: TagSet::empty(),
                }],
            },
        ],
    };

    let (merged, report) = merge_schema_lock(&reparsed, &fresh);
    assert_eq!(report.tables_added, vec!["customers".to_string()]);
    assert_eq!(report.tables_removed, vec!["temp_stage".to_string()]);
    assert_eq!(
        report.cols_added,
        vec![("orders".to_string(), "currency".to_string())]
    );
    assert_eq!(
        report.cols_removed,
        vec![("orders".to_string(), "legacy_note".to_string())]
    );
    assert_eq!(report.cols_changed.len(), 1);
    assert_eq!(report.cols_changed[0].col, "amount");
    assert_eq!(report.tags_preserved, 3); // `pii` on email + `financial`,`pii` on amount
    let report_str = report.to_string();
    assert!(report_str.contains("+ table \"customers\""));
    assert!(report_str.contains("- table \"temp_stage\""));
    assert!(report_str.contains("sensitivity tags preserved: 3"));

    // Verify human-authored tags survived re-sync!
    let merged_orders = merged
        .find_db("Analytics")
        .and_then(|d| d.find_table("orders"))
        .ok_or("merged orders table missing")?;
    assert_eq!(
        merged_orders
            .find_col("customer_email")
            .ok_or("customer_email missing")?
            .tags,
        TagSet::singleton("pii")
    );
    assert_eq!(
        merged_orders
            .find_col("amount")
            .ok_or("amount missing")?
            .tags,
        TagSet::of_list(vec!["financial".to_string(), "pii".to_string()])
    );

    // `verify_table_against_lock`: valid subset passes
    let ok_expected = table_ty(vec![
        col("id", ScalarTy::Int, &[]),
        col("customer_email", ScalarTy::Text, &["pii"]),
        col("amount", opt(ScalarTy::Decimal), &["financial", "pii"]),
    ]);
    verify_table_against_lock(&merged, "Analytics", "orders", &ok_expected)?;

    // Drift 1: non-nullable `Decimal` where lock has nullable `Decimal?`
    let bad_nullability = table_ty(vec![col(
        "amount",
        ScalarTy::Decimal,
        &["financial", "pii"],
    )]);
    assert!(matches!(
        verify_table_against_lock(&merged, "Analytics", "orders", &bad_nullability),
        Err(DbError::SchemaDrift(_))
    ));

    // Drift 2: dropped sensitivity tag `pii` from `customer_email` MUST fail!
    let dropped_tag = table_ty(vec![col("customer_email", ScalarTy::Text, &[])]);
    assert!(matches!(
        verify_table_against_lock(&merged, "Analytics", "orders", &dropped_tag),
        Err(DbError::SchemaDrift(_))
    ));

    // Drift 3: missing column
    let missing_col = table_ty(vec![col("nonexistent", ScalarTy::Int, &[])]);
    assert!(matches!(
        verify_table_against_lock(&merged, "Analytics", "orders", &missing_col),
        Err(DbError::SchemaDrift(_))
    ));

    Ok(())
}

#[test]
fn quote_sql_table_ref_and_multi_schema_lock_roundtrip() -> TestResult {
    assert_eq!(quote_sql_table_ref("enrollments"), r#""enrollments""#);
    assert_eq!(
        quote_sql_table_ref("populi.enrollments"),
        r#""populi"."enrollments""#
    );
    assert_eq!(
        quote_sql_table_ref(r#"my"schema.my"tbl"#),
        r#""my""schema"."my""tbl""#
    );
    assert_eq!(quote_sql_table_ref("a.b.c"), r#""a.b.c""#);
    assert_eq!(quote_sql_table_ref(".leading"), r#"".leading""#);
    assert_eq!(quote_sql_table_ref("trailing."), r#""trailing.""#);

    let lock = SchemaLock {
        version: 1,
        dbs: vec![LockedDb {
            name: "Wts".to_string(),
            dialect: SqlDialect::Postgres,
            tables: vec![
                LockedTable {
                    name: "populi.course_enrollments".to_string(),
                    cols: vec![
                        LockedCol {
                            name: "id".to_string(),
                            ty: ScalarTy::Int,
                            nullable: false,
                            pk: true,
                            tags: TagSet::empty(),
                        },
                        LockedCol {
                            name: "student_email".to_string(),
                            ty: ScalarTy::Text,
                            nullable: false,
                            pk: false,
                            tags: TagSet::singleton("pii"),
                        },
                    ],
                },
                LockedTable {
                    name: "public_only".to_string(),
                    cols: vec![],
                },
            ],
        }],
    };
    let rendered = format_schema_lock(&lock);
    let reparsed = parse_schema_lock(&rendered)?;
    assert_eq!(reparsed, lock);

    let db = &reparsed.dbs[0];
    assert_eq!(
        db.resolve_table("populi.course_enrollments")?.name,
        "populi.course_enrollments"
    );
    assert_eq!(
        db.resolve_table("POPULI.COURSE_ENROLLMENTS")?.name,
        "populi.course_enrollments"
    );
    assert_eq!(
        db.resolve_table("populi.CourseEnrollments")?.name,
        "populi.course_enrollments"
    );

    Ok(())
}

#[test]
fn pg_type_mapping_and_extended_oid_decoding() -> TestResult {
    assert_eq!(map_pg_type_name("json", "json"), ScalarTy::Text);
    assert_eq!(map_pg_type_name("jsonb", "jsonb"), ScalarTy::Text);
    assert_eq!(map_pg_type_name("uuid", "uuid"), ScalarTy::Text);
    assert_eq!(
        map_pg_type_name("character varying", "varchar"),
        ScalarTy::Text
    );
    assert_eq!(map_pg_type_name("character", "bpchar"), ScalarTy::Text);
    assert_eq!(map_pg_type_name("USER-DEFINED", "citext"), ScalarTy::Text);
    assert_eq!(map_pg_type_name("name", "name"), ScalarTy::Text);
    assert_eq!(map_pg_type_name("date", "date"), ScalarTy::Date);
    assert_eq!(
        map_pg_type_name("timestamp without time zone", "timestamp"),
        ScalarTy::Timestamp
    );
    assert_eq!(
        map_pg_type_name("timestamp with time zone", "timestamptz"),
        ScalarTy::Timestamp
    );
    assert_eq!(map_pg_type_name("numeric", "numeric"), ScalarTy::Decimal);
    assert_eq!(map_pg_type_name("decimal", "numeric"), ScalarTy::Decimal);

    // Wire test with custom PostgreSQL RowDescriptions covering JSON, JSONB, UUID, CHAR/NAME, and citext (>= 16384)
    let listener = TcpListener::bind("127.0.0.1:0")?;
    let port = listener.local_addr()?.port();
    let srv_thread = thread::spawn(move || -> Result<(), String> {
        let (mut tcp, _) = listener.accept().map_err(|e| e.to_string())?;
        let mut len_buf = [0u8; 4];
        tcp.read_exact(&mut len_buf).map_err(|e| e.to_string())?;
        let startup_len = i32::from_be_bytes(len_buf) as usize;
        let rest_len = startup_len.saturating_sub(4);
        let mut rest = vec![0u8; rest_len];
        tcp.read_exact(&mut rest).map_err(|e| e.to_string())?;
        let mut stream = ServerStream::Plain(tcp);
        srv_write_msg(&mut stream, b'R', &0i32.to_be_bytes()).map_err(|e| e.to_string())?;
        srv_write_msg(&mut stream, b'Z', b"I").map_err(|e| e.to_string())?;

        while let Ok(Some((tag, _payload))) = srv_read_msg(&mut stream) {
            match tag {
                b'P' => {
                    srv_write_msg(&mut stream, b'1', &[]).map_err(|e| e.to_string())?;
                }
                b'B' => {
                    srv_write_msg(&mut stream, b'2', &[]).map_err(|e| e.to_string())?;
                }
                b'D' => {}
                b'Q' | b'E' => {
                    srv_send_row_desc(
                        &mut stream,
                        &[
                            ("j", oid::JSON),
                            ("jb", oid::JSONB),
                            ("u", oid::UUID),
                            ("c", oid::CHAR),
                            ("nm", oid::NAME),
                            ("ci", 16_450),
                            ("opt_u", oid::UUID),
                        ],
                    )
                    .map_err(|e| e.to_string())?;
                    srv_send_data_row(
                        &mut stream,
                        &[
                            Some(br#"{"ok":true}"#.to_vec()),
                            Some(br#"{"k":1}"#.to_vec()),
                            Some(b"550e8400-e29b-41d4-a716-446655440000".to_vec()),
                            Some(b"A".to_vec()),
                            Some(b"pg_class".to_vec()),
                            Some(b"CaseText".to_vec()),
                            None,
                        ],
                    )
                    .map_err(|e| e.to_string())?;
                    srv_write_msg(&mut stream, b'C', b"SELECT 1\0").map_err(|e| e.to_string())?;
                    if tag == b'Q' {
                        srv_write_msg(&mut stream, b'Z', b"I").map_err(|e| e.to_string())?;
                    }
                }
                b'S' => {
                    srv_write_msg(&mut stream, b'Z', b"I").map_err(|e| e.to_string())?;
                }
                b'X' => break,
                _ => {}
            }
        }
        Ok(())
    });

    let uri = format!("postgres://u@127.0.0.1:{port}/app?sslmode=disable");
    let mut conn = open_connection(&uri)?;
    let schema = table_ty(vec![
        col("j", ScalarTy::Text, &[]),
        col("jb", ScalarTy::Text, &[]),
        col("u", ScalarTy::Text, &[]),
        col("c", ScalarTy::Text, &[]),
        col("nm", ScalarTy::Text, &[]),
        col("ci", ScalarTy::Text, &[]),
        col("opt_u", opt(ScalarTy::Text), &[]),
    ]);
    let tv = conn.query_rows("SELECT j, jb, u, c, nm, ci, opt_u FROM t", &[], &schema)?;
    assert_eq!(tv.rows.len(), 1);
    assert!(val_eq(
        &tv.rows[0].cells[0],
        &Val::Text(r#"{"ok":true}"#.to_string())
    ));
    assert!(val_eq(
        &tv.rows[0].cells[1],
        &Val::Text(r#"{"k":1}"#.to_string())
    ));
    assert!(val_eq(
        &tv.rows[0].cells[2],
        &Val::Text("550e8400-e29b-41d4-a716-446655440000".to_string())
    ));
    assert!(val_eq(&tv.rows[0].cells[3], &Val::Text("A".to_string())));
    assert!(val_eq(
        &tv.rows[0].cells[4],
        &Val::Text("pg_class".to_string())
    ));
    assert!(val_eq(
        &tv.rows[0].cells[5],
        &Val::Text("CaseText".to_string())
    ));
    assert!(val_eq(&tv.rows[0].cells[6], &Val::OptNone));
    drop(conn);
    let _ = srv_thread.join();

    Ok(())
}
