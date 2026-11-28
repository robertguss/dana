//! Phase 3B — Parameterized SQL Pushdown Splitter, Sensitivity-Aware Plan Explainer &
//! 1,000+ Differential Verification Gate (`Oracle == VM == SQLite Pushdown == Postgres Pushdown`).
//!
//! Covers:
//! 1. **1,125+ generated DB-backed Core IR relational pipelines** across 15 families:
//!    - Filter + Select/Drop/Rename (literals, OuterVar, ConstRef, AND/OR/NOT, IS NULL, COALESCE, IF, text ops)
//!    - Total Derive + BucketCol + multi-stage sequential Derive
//!    - Total/unique Sort + Limit (`ASC NULLS FIRST` / `DESC NULLS LAST`, Limit 0/small/large)
//!    - Non-unique Sort with ties (soundly stays local in VM)
//!    - GroupBy + Summarize (`Count`, `CountDistinct` with nulls, `Min`, `Max`, grouped & ungrouped, empty tables)
//!    - Hybrid GroupBy + Summarize with local VM aggs (`Sum`, `Mean`, `Median`, `Stddev`, `First`, `Last`)
//!    - Local-VM traps & pure UDFs (`CallPure`, `AddInt`/`DivInt`/`ModInt`, `UnwrapBang`, `Float` NaN/-0.0, SQLite `Decimal` ordering)
//!    - Same-DB `InnerMany` / `Semi` / `Anti` joins (including nullable join keys & suffixes)
//!    - Checked cardinality joins (`InnerOne`, `InnerManyToOne`, `LeftOne`, `LeftManyToOne`):
//!      pushed when `SchemaLockFile` PK proves uniqueness; local VM with redacted `[pii]` diagnostics when unchecked
//!    - Same-DB `Union` (`UNION ALL`)
//!    - `Distinct` (all-column order-insensitive pushed vs subset/order-sensitive local)
//!    - `Redact` on `[pii]` `Text` and `Option(Text)` columns
//!    - `SuppressSmallGroups` (`Drop` and `MaskComplementary`) local suffix
//!    - `Window` (`RowNumber`, `Rank`, `Lag`, `Lead`, `RunningSum`, `RollingMean`) local suffix
//!    - Hybrid DB-vs-local `Join` (`SourceDB` joined with in-memory `TableLit`)
//! 2. **SQL Injection Resistance** test on SQLite and Postgres wire server.
//! 3. **Explainer & Sensitivity Provenance** test on `examples/enrollment-report.dana` + `examples/dana.policy`
//!    for both `Sqlite` and `Postgres` dialects.
//! 4. **Multi-Branch Pushdown Collection** (`collect_core_plan_pushdowns`, `collect_exec_plan_pushdowns`)
//!    and **Postgres vs SQLite Dialect Rules** (`Decimal` / `Timestamp` / `Float`).
//! 5. **Opt-in Live PostgreSQL Differential Test (`#[ignore]`)** reading `DANA_TEST_POSTGRES_URL`.

use std::collections::HashMap;
use std::fs;
use std::io::{Read, Write};
use std::net::{TcpListener, TcpStream};
use std::path::PathBuf;
use std::thread;

use dana::base::{SourceMap, render_diagnostic};
use dana::check::{check_resolved, parse_policy, resolve_path};
use dana::core::{
    AggItem, AggKind, AggOp, BigInt, ColSpec, ConstDecl, DEC_SCALE, DeriveItem, Expr, Float64,
    FunDecl, FunKind, HostOp, Ident, JoinKind, JoinOn, LTy, Literal, Plan, Policy, PrimOp, Program,
    RowExpr, RowLit, ScalarTy, SortDir, SuppressMode, TableTy, TagSet, Ty, WindowFn, WindowItem,
    check_program,
};
use dana::db::postgres::{PostgresDriver, oid};
use dana::db::schema_lock::{LockedCol, LockedDb, LockedTable, SchemaLockFile};
use dana::db::sqlite::SqliteDriver;
use dana::db::{DbConnection, DbUri, SqlDialect, SqlParam, quote_sql_ident};
use dana::ffi::sqlite::{SqliteConn, SqliteValueType, StepResult};
use dana::formats::crypto::to_hex_lower;
use dana::formats::time::{days_from_civil, format_iso_date, format_iso_timestamp};
use dana::lower::lower_program;
use dana::oracle::eval::eval_literal;
use dana::oracle::value::{EnvEntry, EnvList, TableVal, render_public_val};
use dana::oracle::{ExecReport, ExitStatus, StoredTable, Val, World, run_program};
use dana::plan::{
    SplitPlan, bind_exec_plan_sources, collect_core_plan_pushdowns, collect_exec_plan_pushdowns,
    explain_core_plan_with_pushdown, explain_exec_plan_with_pushdown, optimize_plan,
    split_core_plan_pushdown,
};
use dana::runtime::ir::{ExecExpr, ExecPlan};
use dana::vm::{BATCH_SIZE, OpErr, VmConfig, eval_core_plan_batches_with_env, run_core_program_vm};

type TestResult<T = ()> = Result<T, Box<dyn std::error::Error>>;

// ===========================================================================
// Deterministic SplitMix64 PRNG
// ===========================================================================

struct SplitMix64 {
    state: u64,
}

impl SplitMix64 {
    const fn new(seed: u64) -> Self {
        Self { state: seed }
    }

    fn next_u64(&mut self) -> u64 {
        self.state = self.state.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.state;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    fn gen_range(&mut self, bound: usize) -> usize {
        if bound <= 1 {
            0
        } else {
            (self.next_u64() as usize) % bound
        }
    }

    fn gen_bool(&mut self, num: usize, den: usize) -> bool {
        self.gen_range(den) < num
    }

    fn pick_small_int(&mut self) -> i64 {
        const POOL: &[i64] = &[-10, -3, -1, 0, 1, 2, 4, 7, 10, 15, 25, 42];
        POOL[self.gen_range(POOL.len())]
    }

    fn pick_group(&mut self) -> String {
        const POOL: &[&str] = &["A", "B", "C", "D"];
        POOL[self.gen_range(POOL.len())].to_string()
    }

    fn pick_text(&mut self) -> String {
        const POOL: &[&str] = &[
            "alpha",
            "Beta",
            "  gamma\t",
            "\ndelta ",
            "AlPhA_1",
            "",
            "42",
            "true",
            "a%b_c",
            "it's ok",
        ];
        POOL[self.gen_range(POOL.len())].to_string()
    }

    fn pick_date(&mut self) -> i64 {
        const POOL: &[(i64, u32, u32)] = &[
            (2024, 1, 15),
            (2024, 6, 30),
            (2025, 3, 1),
            (2025, 9, 15),
            (2026, 12, 31),
        ];
        let (y, m, d) = POOL[self.gen_range(POOL.len())];
        days_from_civil(y, m, d)
    }

    fn pick_dec(&mut self) -> i128 {
        const POOL: &[i128] = &[
            -12 * DEC_SCALE,
            -DEC_SCALE / 2,
            0,
            DEC_SCALE / 4,
            2 * DEC_SCALE,
            10 * DEC_SCALE + DEC_SCALE / 2,
            100 * DEC_SCALE,
        ];
        POOL[self.gen_range(POOL.len())]
    }

    fn pick_float(&mut self) -> Float64 {
        // SQLite binds IEEE NaN as SQL NULL and canonicalizes -0.0 to +0.0 on REAL storage,
        // so DB-stored NOT NULL REAL columns use finite non-negative-zero floats that round-trip
        // identically across SQLite and Postgres. (Float comparisons/sorts still stay local in VM.)
        const POOL: &[f64] = &[-5.5, -1.25, 0.0, 1.5, 10.0, 42.25];
        Float64::from_f64(POOL[self.gen_range(POOL.len())])
    }
}

// ===========================================================================
// Schema & Core IR Builders
// ===========================================================================

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

fn items_schema() -> TableTy {
    TableTy {
        cols: vec![
            col("id", ScalarTy::Int, &[]),
            col("grp", ScalarTy::Text, &[]),
            col("val", ScalarTy::Int, &[]),
            col("opt_val", opt(ScalarTy::Int), &[]),
            col("flag", ScalarTy::Bool, &[]),
            col("name", ScalarTy::Text, &["pii"]),
            col("opt_note", opt(ScalarTy::Text), &["pii"]),
            col("day", ScalarTy::Date, &[]),
            col("dur", ScalarTy::Duration, &[]),
            col("amt", ScalarTy::Decimal, &["ferpa"]),
            col("score", ScalarTy::Float, &[]),
        ],
        ..TableTy::default()
    }
}

fn dim_schema() -> TableTy {
    TableTy {
        cols: vec![
            col("id", ScalarTy::Int, &[]),
            col("grp", ScalarTy::Text, &[]),
            col("region", ScalarTy::Text, &[]),
            col("weight", ScalarTy::Int, &[]),
            col("opt_k", opt(ScalarTy::Int), &[]),
            col("secret_key", ScalarTy::Text, &["pii"]),
        ],
        ..TableTy::default()
    }
}

fn build_schema_lock(db_name: &str, dialect: SqlDialect, include_pks: bool) -> SchemaLockFile {
    let make_cols = |tt: &TableTy, pk_name: Option<&str>| -> Vec<LockedCol> {
        tt.cols
            .iter()
            .map(|c| {
                let (base, nullable) = match &c.ty {
                    ScalarTy::Option(inner) => ((**inner).clone(), true),
                    other => (other.clone(), false),
                };
                LockedCol {
                    name: c.name.clone(),
                    ty: base,
                    nullable,
                    pk: include_pks && pk_name == Some(c.name.as_str()),
                    tags: c.tags.clone(),
                }
            })
            .collect()
    };
    SchemaLockFile {
        version: 1,
        dbs: vec![LockedDb {
            name: db_name.to_string(),
            dialect,
            tables: vec![
                LockedTable {
                    name: "items".to_string(),
                    cols: make_cols(&items_schema(), Some("id")),
                },
                LockedTable {
                    name: "items2".to_string(),
                    cols: make_cols(&items_schema(), Some("id")),
                },
                LockedTable {
                    name: "dim_uniq".to_string(),
                    cols: make_cols(&dim_schema(), Some("id")),
                },
                LockedTable {
                    name: "dim_dup".to_string(),
                    cols: make_cols(&dim_schema(), None),
                },
            ],
        }],
    }
}

fn gen_items_rows(rng: &mut SplitMix64, n: usize, id_offset: i64) -> Vec<Vec<Val>> {
    let mut rows = Vec::with_capacity(n);
    for i in 0..n {
        let id = id_offset + (i as i64) + 1;
        let grp = rng.pick_group();
        let val = rng.pick_small_int();
        let opt_val = if rng.gen_bool(1, 3) {
            Val::OptNone
        } else {
            Val::OptSome(Box::new(Val::Int(BigInt::from(rng.pick_small_int()))))
        };
        let flag = Val::Bool(rng.gen_bool(1, 2));
        let name = Val::Text(rng.pick_text());
        let opt_note = if rng.gen_bool(2, 5) {
            Val::OptNone
        } else {
            Val::OptSome(Box::new(Val::Text(rng.pick_text())))
        };
        let day = Val::Date(BigInt::from(rng.pick_date()));
        let dur = Val::Duration(BigInt::from(rng.pick_small_int() * 1_000_000));
        let amt = Val::Decimal(BigInt::from(rng.pick_dec()));
        let score = Val::Float(rng.pick_float());
        rows.push(vec![
            Val::Int(BigInt::from(id)),
            Val::Text(grp),
            Val::Int(BigInt::from(val)),
            opt_val,
            flag,
            name,
            opt_note,
            day,
            dur,
            amt,
            score,
        ]);
    }
    rows
}

fn gen_dim_rows(rng: &mut SplitMix64, n: usize, unique_id: bool) -> Vec<Vec<Val>> {
    let mut rows = Vec::with_capacity(n);
    for i in 0..n {
        let id = if unique_id {
            (i as i64) + 1
        } else {
            ((i % 3) as i64) + 1
        };
        let grp = rng.pick_group();
        let region = match rng.gen_range(3) {
            0 => "north",
            1 => "south",
            _ => "west",
        };
        let weight = rng.pick_small_int();
        let opt_k = if rng.gen_bool(1, 3) {
            Val::OptNone
        } else {
            Val::OptSome(Box::new(Val::Int(BigInt::from(rng.pick_small_int()))))
        };
        let secret_key = if unique_id {
            format!("sk_{i}")
        } else {
            format!("sk_{}", i % 2)
        };
        rows.push(vec![
            Val::Int(BigInt::from(id)),
            Val::Text(grp),
            Val::Text(region.to_string()),
            Val::Int(BigInt::from(weight)),
            opt_k,
            Val::Text(secret_key),
        ]);
    }
    rows
}

fn render_core_table_text(tv: &TableVal) -> String {
    let hdr = tv
        .cols
        .iter()
        .map(|c| c.name.as_str())
        .collect::<Vec<_>>()
        .join(" | ");
    let mut lines = Vec::with_capacity(tv.rows.len() + 1);
    lines.push(hdr);
    for r in &tv.rows {
        let cells: Vec<String> = r.cells.iter().map(render_public_val).collect();
        lines.push(cells.join(" | "));
    }
    lines.join("\n")
}

// ===========================================================================
// SQLite Table Loader (Preserves Exact Insertion Order via `INT PRIMARY KEY`)
// ===========================================================================

fn sqlite_col_ddl(ty: &ScalarTy) -> &'static str {
    let base = match ty {
        ScalarTy::Option(inner) => inner.as_ref(),
        other => other,
    };
    match base {
        ScalarTy::Bool => "BOOLEAN",
        ScalarTy::Int => "INT",
        ScalarTy::Decimal => "DECIMAL_TEXT",
        ScalarTy::Float => "REAL",
        ScalarTy::Text => "TEXT",
        ScalarTy::Bytes => "BLOB",
        ScalarTy::Date => "DATE",
        ScalarTy::Timestamp => "TIMESTAMP",
        ScalarTy::Duration => "DURATION",
        ScalarTy::Unit | ScalarTy::Data(_) | ScalarTy::Option(_) => "TEXT",
    }
}

fn load_tables_into_sqlite(
    drv: &mut SqliteDriver,
    tables: &[StoredTable],
    pk_tables: &[(&str, &str)],
) -> TestResult {
    for st in tables {
        let pk_col = pk_tables
            .iter()
            .find(|(t, _)| *t == st.table_name)
            .map(|(_, c)| *c);
        let col_defs: Vec<String> = st
            .schema
            .cols
            .iter()
            .map(|c| {
                let q = quote_sql_ident(&c.name);
                let sql_ty = sqlite_col_ddl(&c.ty);
                let not_null = if c.ty.is_option() { "" } else { " NOT NULL" };
                let pk = if pk_col == Some(c.name.as_str()) {
                    " PRIMARY KEY"
                } else {
                    ""
                };
                format!("{q} {sql_ty}{not_null}{pk}")
            })
            .collect();
        let create_sql = format!(
            "DROP TABLE IF EXISTS {}; CREATE TABLE {} ({});",
            quote_sql_ident(&st.table_name),
            quote_sql_ident(&st.table_name),
            col_defs.join(", ")
        );
        drv.execute_batch(&create_sql)?;

        if !st.rows.is_empty() {
            let row_ph = format!("({})", vec!["?"; st.schema.cols.len()].join(", "));
            let all_ph = vec![row_ph; st.rows.len()].join(", ");
            let insert_sql = format!(
                "INSERT INTO {} VALUES {all_ph}",
                quote_sql_ident(&st.table_name)
            );
            let mut params = Vec::with_capacity(st.rows.len() * st.schema.cols.len());
            for row in &st.rows {
                for cell in row {
                    params.push(SqlParam::from_val(cell)?);
                }
            }
            drv.execute(&insert_sql, &params)?;
        }
    }
    Ok(())
}

// ===========================================================================
// Reusable In-Process PostgreSQL v3.0 Wire Server (Loopback TCP, Extended Query)
// ===========================================================================

fn srv_write_msg(stream: &mut TcpStream, tag: u8, payload: &[u8]) -> std::io::Result<()> {
    let len = (payload.len() + 4) as i32;
    let mut frame = Vec::with_capacity(5 + payload.len());
    frame.push(tag);
    frame.extend_from_slice(&len.to_be_bytes());
    frame.extend_from_slice(payload);
    stream.write_all(&frame)?;
    stream.flush()
}

fn srv_read_msg(stream: &mut TcpStream) -> std::io::Result<Option<(u8, Vec<u8>)>> {
    let mut hdr = [0u8; 5];
    match stream.read_exact(&mut hdr) {
        Ok(()) => {}
        Err(e) if e.kind() == std::io::ErrorKind::UnexpectedEof => return Ok(None),
        Err(e) => return Err(e),
    }
    let tag = hdr[0];
    let len = i32::from_be_bytes([hdr[1], hdr[2], hdr[3], hdr[4]]) as usize;
    let body_len = len.saturating_sub(4);
    let mut body = vec![0u8; body_len];
    if body_len > 0 {
        stream.read_exact(&mut body)?;
    }
    Ok(Some((tag, body)))
}

fn srv_send_error(stream: &mut TcpStream, code: &str, message: &str) -> std::io::Result<()> {
    let mut body = Vec::new();
    body.extend_from_slice(b"SERROR\0");
    body.push(b'C');
    body.extend_from_slice(code.as_bytes());
    body.push(0);
    body.push(b'M');
    body.extend_from_slice(message.as_bytes());
    body.push(0);
    body.push(0);
    srv_write_msg(stream, b'E', &body)
}

fn srv_send_row_desc(stream: &mut TcpStream, cols: &[(&str, u32)]) -> std::io::Result<()> {
    let mut body = Vec::new();
    body.extend_from_slice(&(cols.len() as i16).to_be_bytes());
    for &(name, type_oid) in cols {
        body.extend_from_slice(name.as_bytes());
        body.push(0);
        body.extend_from_slice(&0i32.to_be_bytes()); // table_oid
        body.extend_from_slice(&0i16.to_be_bytes()); // col_attr
        body.extend_from_slice(&type_oid.to_be_bytes());
        body.extend_from_slice(&(-1i16).to_be_bytes());
        body.extend_from_slice(&(-1i32).to_be_bytes());
        body.extend_from_slice(&0i16.to_be_bytes()); // text format
    }
    srv_write_msg(stream, b'T', &body)
}

fn srv_send_data_row(stream: &mut TcpStream, cells: &[Option<Vec<u8>>]) -> std::io::Result<()> {
    let mut body = Vec::new();
    body.extend_from_slice(&(cells.len() as i16).to_be_bytes());
    for cell in cells {
        match cell {
            None => body.extend_from_slice(&(-1i32).to_be_bytes()),
            Some(bytes) => {
                body.extend_from_slice(&(bytes.len() as i32).to_be_bytes());
                body.extend_from_slice(bytes);
            }
        }
    }
    srv_write_msg(stream, b'D', &body)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum PgParamHint {
    Text,
    Int,
    Bool,
    Float,
    Bytes,
    Interval,
    Date,
    Timestamp,
    Numeric,
    Unknown,
}

fn parse_pg_interval_seconds_to_micros(s: &str) -> Option<i64> {
    let trimmed = s.trim().strip_suffix(" seconds")?.trim();
    let (neg, rest) = match trimmed.strip_prefix('-') {
        Some(r) => (true, r),
        None => (false, trimmed),
    };
    let (secs_str, frac_str) = rest.split_once('.').unwrap_or((rest, "0"));
    let secs: i64 = secs_str.parse().ok()?;
    let mut frac_padded = frac_str.to_string();
    while frac_padded.len() < 6 {
        frac_padded.push('0');
    }
    let micros: i64 = frac_padded[..6].parse().ok()?;
    let total = secs.checked_mul(1_000_000)?.checked_add(micros)?;
    Some(if neg { -total } else { total })
}

/// Rewrite PostgreSQL dialect pushdown SQL into SQLite-executable SQL while capturing the
/// exact declared `CAST($k AS <TYPE>)` hint for every `$1..$n` parameter so `"42"` or `"true"`
/// text parameters are NEVER mis-bound as integers!
fn translate_pg_sql_to_sqlite(pg_sql: &str) -> (String, HashMap<usize, PgParamHint>) {
    let mut hints: HashMap<usize, PgParamHint> = HashMap::new();
    let mut out = String::with_capacity(pg_sql.len());
    let bytes = pg_sql.as_bytes();
    let mut i = 0usize;
    let mut in_single = false;
    let mut in_double = false;

    while i < bytes.len() {
        let b = bytes[i];
        if in_single {
            out.push(b as char);
            if b == b'\'' {
                if i + 1 < bytes.len() && bytes[i + 1] == b'\'' {
                    out.push('\'');
                    i += 2;
                    continue;
                }
                in_single = false;
            }
            i += 1;
            continue;
        }
        if in_double {
            out.push(b as char);
            if b == b'"' {
                if i + 1 < bytes.len() && bytes[i + 1] == b'"' {
                    out.push('"');
                    i += 2;
                    continue;
                }
                in_double = false;
            }
            i += 1;
            continue;
        }

        if b == b'\'' {
            in_single = true;
            out.push('\'');
            i += 1;
            continue;
        }
        if b == b'"' {
            in_double = true;
            out.push('"');
            i += 1;
            continue;
        }

        let rest = &pg_sql[i..];
        if let Some(after_cast) = rest.strip_prefix("CAST($") {
            let digits_len = after_cast.bytes().take_while(u8::is_ascii_digit).count();
            if digits_len > 0
                && let Some(after_as) = after_cast[digits_len..].strip_prefix(" AS ")
                && let Some(close_rel) = after_as.find(')')
            {
                let idx: usize = after_cast[..digits_len].parse().unwrap_or(0);
                let ty_str = &after_as[..close_rel];
                let hint = match ty_str {
                    "TEXT" => PgParamHint::Text,
                    "BIGINT" | "INTEGER" => PgParamHint::Int,
                    "BOOLEAN" => PgParamHint::Bool,
                    "DOUBLE PRECISION" => PgParamHint::Float,
                    "BYTEA" => PgParamHint::Bytes,
                    "INTERVAL" => PgParamHint::Interval,
                    "DATE" => PgParamHint::Date,
                    "TIMESTAMPTZ" | "TIMESTAMP" => PgParamHint::Timestamp,
                    "NUMERIC" => PgParamHint::Numeric,
                    _ => PgParamHint::Unknown,
                };
                if idx > 0 {
                    hints.insert(idx, hint);
                }
                out.push('?');
                i += "CAST($".len() + digits_len + " AS ".len() + close_rel + 1;
                continue;
            }
        }
        if rest.starts_with("IS NOT DISTINCT FROM") {
            out.push_str("IS");
            i += "IS NOT DISTINCT FROM".len();
            continue;
        }
        if rest.starts_with("IS DISTINCT FROM") {
            out.push_str("IS NOT");
            i += "IS DISTINCT FROM".len();
            continue;
        }
        if rest.starts_with("COLLATE \"C\"") {
            out.push_str("COLLATE BINARY");
            i += "COLLATE \"C\"".len();
            continue;
        }
        if rest.starts_with("BTRIM(") {
            out.push_str("TRIM(");
            i += "BTRIM(".len();
            continue;
        }
        if rest.starts_with("STRPOS(") {
            out.push_str("INSTR(");
            i += "STRPOS(".len();
            continue;
        }
        if b == b'$' && i + 1 < bytes.len() && bytes[i + 1].is_ascii_digit() {
            let mut j = i + 1;
            while j < bytes.len() && bytes[j].is_ascii_digit() {
                j += 1;
            }
            out.push('?');
            i = j;
            continue;
        }
        let ch = rest.chars().next().unwrap_or(' ');
        out.push(ch);
        i += ch.len_utf8();
    }

    (out, hints)
}

fn spawn_pg_pushdown_server() -> TestResult<(u16, thread::JoinHandle<()>)> {
    let listener = TcpListener::bind("127.0.0.1:0")?;
    let port = listener.local_addr()?.port();

    let handle = thread::spawn(move || {
        let Ok((mut stream, _)) = listener.accept() else {
            return;
        };
        let Ok(sqlite) = SqliteConn::open_in_memory() else {
            return;
        };

        // Read StartupMessage (plain TCP, sslmode=disable).
        let mut len_buf = [0u8; 4];
        let mut code_buf = [0u8; 4];
        if stream.read_exact(&mut len_buf).is_err() || stream.read_exact(&mut code_buf).is_err() {
            return;
        }
        let startup_len = i32::from_be_bytes(len_buf) as usize;
        let rest_len = startup_len.saturating_sub(8);
        let mut startup_body = vec![0u8; rest_len];
        if stream.read_exact(&mut startup_body).is_err() {
            return;
        }

        // AuthenticationOk + ParameterStatus + ReadyForQuery.
        let _ = srv_write_msg(&mut stream, b'R', &0i32.to_be_bytes());
        for (k, v) in [
            ("server_version", "16.0-dana-pushdown-test"),
            ("client_encoding", "UTF8"),
            ("TimeZone", "UTC"),
        ] {
            let mut p = Vec::new();
            p.extend_from_slice(k.as_bytes());
            p.push(0);
            p.extend_from_slice(v.as_bytes());
            p.push(0);
            let _ = srv_write_msg(&mut stream, b'S', &p);
        }
        let _ = srv_write_msg(&mut stream, b'Z', b"I");

        let mut parsed_sql = String::new();
        let mut bound_params: Vec<(i16, Option<Vec<u8>>)> = Vec::new();

        while let Ok(Some((tag, body))) = srv_read_msg(&mut stream) {
            match tag {
                b'P' => {
                    let nul1 = body.iter().position(|&b| b == 0).unwrap_or(0);
                    let after1 = &body[nul1 + 1..];
                    let nul2 = after1.iter().position(|&b| b == 0).unwrap_or(after1.len());
                    parsed_sql = String::from_utf8_lossy(&after1[..nul2]).into_owned();
                    let _ = srv_write_msg(&mut stream, b'1', &[]);
                }
                b'B' => {
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
                        let len =
                            i32::from_be_bytes([body[p], body[p + 1], body[p + 2], body[p + 3]]);
                        p += 4;
                        if len == -1 {
                            bound_params.push((fmt, None));
                        } else {
                            let ulen = len as usize;
                            bound_params.push((fmt, Some(body[p..p + ulen].to_vec())));
                            p += ulen;
                        }
                    }
                    let _ = srv_write_msg(&mut stream, b'2', &[]);
                }
                b'D' => {}
                b'E' => {
                    if let Err(err_msg) =
                        exec_pg_query_on_sqlite(&mut stream, &sqlite, &parsed_sql, &bound_params)
                    {
                        let _ = srv_send_error(&mut stream, "42000", &err_msg);
                    }
                }
                b'S' => {
                    let _ = srv_write_msg(&mut stream, b'Z', b"I");
                }
                b'X' => break,
                _ => {}
            }
        }
    });

    Ok((port, handle))
}

fn exec_pg_query_on_sqlite(
    stream: &mut TcpStream,
    sqlite: &SqliteConn,
    pg_sql: &str,
    params: &[(i16, Option<Vec<u8>>)],
) -> Result<(), String> {
    let trimmed = pg_sql.trim();
    if trimmed.to_ascii_uppercase().starts_with("DROP TABLE")
        || trimmed.to_ascii_uppercase().starts_with("CREATE TABLE")
    {
        sqlite.execute_batch(trimmed).map_err(|e| e.to_string())?;
        srv_write_msg(stream, b'n', &[]).map_err(|e| e.to_string())?;
        srv_write_msg(stream, b'C', b"OK\0").map_err(|e| e.to_string())?;
        return Ok(());
    }

    let (sqlite_sql, hints) = translate_pg_sql_to_sqlite(trimmed);
    let mut stmt = sqlite.prepare(&sqlite_sql).map_err(|e| e.to_string())?;

    for (idx, (fmt, val)) in params.iter().enumerate() {
        let param_no = idx + 1;
        let bind_idx = param_no as i32;
        let hint = hints
            .get(&param_no)
            .copied()
            .unwrap_or(PgParamHint::Unknown);
        match val {
            None => stmt.bind_null(bind_idx).map_err(|e| e.to_string())?,
            Some(bytes) if *fmt == 1 || hint == PgParamHint::Bytes => {
                stmt.bind_blob(bind_idx, bytes).map_err(|e| e.to_string())?
            }
            Some(bytes) => {
                let s = String::from_utf8_lossy(bytes);
                match hint {
                    PgParamHint::Text
                    | PgParamHint::Date
                    | PgParamHint::Timestamp
                    | PgParamHint::Numeric => {
                        stmt.bind_text(bind_idx, &s).map_err(|e| e.to_string())?;
                    }
                    PgParamHint::Int => {
                        let n: i64 = s.parse().map_err(|e| format!("bad int param `{s}`: {e}"))?;
                        stmt.bind_int64(bind_idx, n).map_err(|e| e.to_string())?;
                    }
                    PgParamHint::Bool => {
                        let b = if s == "true" || s == "t" || s == "1" {
                            1
                        } else {
                            0
                        };
                        stmt.bind_int64(bind_idx, b).map_err(|e| e.to_string())?;
                    }
                    PgParamHint::Float => {
                        let f: f64 = s
                            .parse()
                            .map_err(|e| format!("bad float param `{s}`: {e}"))?;
                        stmt.bind_double(bind_idx, f).map_err(|e| e.to_string())?;
                    }
                    PgParamHint::Interval => {
                        let us = parse_pg_interval_seconds_to_micros(&s)
                            .ok_or_else(|| format!("bad interval param `{s}`"))?;
                        stmt.bind_int64(bind_idx, us).map_err(|e| e.to_string())?;
                    }
                    PgParamHint::Unknown => {
                        // Used for INSERT DDL setup where params carry raw values.
                        if let Some(us) = parse_pg_interval_seconds_to_micros(&s) {
                            stmt.bind_int64(bind_idx, us).map_err(|e| e.to_string())?;
                        } else if s == "true" {
                            stmt.bind_int64(bind_idx, 1).map_err(|e| e.to_string())?;
                        } else if s == "false" {
                            stmt.bind_int64(bind_idx, 0).map_err(|e| e.to_string())?;
                        } else {
                            stmt.bind_text(bind_idx, &s).map_err(|e| e.to_string())?;
                        }
                    }
                    PgParamHint::Bytes => unreachable!("handled above"),
                }
            }
        }
    }

    let n_cols = stmt.column_count();
    if n_cols == 0 {
        while stmt.step().map_err(|e| e.to_string())? == StepResult::Row {}
        srv_write_msg(stream, b'n', &[]).map_err(|e| e.to_string())?;
        srv_write_msg(stream, b'C', b"INSERT 0 1\0").map_err(|e| e.to_string())?;
        return Ok(());
    }

    let col_names: Vec<String> = (0..n_cols)
        .map(|i| stmt.column_name(i).unwrap_or_else(|| format!("c{i}")))
        .collect();
    // OID 0 allows PostgresDriver to decode according to expected Dana TableTy.
    let col_desc: Vec<(&str, u32)> = col_names.iter().map(|n| (n.as_str(), 0u32)).collect();
    srv_send_row_desc(stream, &col_desc).map_err(|e| e.to_string())?;

    let mut row_count = 0usize;
    while stmt.step().map_err(|e| e.to_string())? == StepResult::Row {
        let mut cells = Vec::with_capacity(n_cols);
        for ci in 0..n_cols {
            let v = match stmt.column_type(ci) {
                SqliteValueType::Null => None,
                SqliteValueType::Integer => Some(stmt.column_int64(ci).to_string().into_bytes()),
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

fn load_tables_into_pg_mock(
    pg: &mut PostgresDriver,
    tables: &[StoredTable],
    pk_tables: &[(&str, &str)],
) -> TestResult {
    for st in tables {
        let pk_col = pk_tables
            .iter()
            .find(|(t, _)| *t == st.table_name)
            .map(|(_, c)| *c);
        let col_defs: Vec<String> = st
            .schema
            .cols
            .iter()
            .map(|c| {
                let q = quote_sql_ident(&c.name);
                let sql_ty = sqlite_col_ddl(&c.ty);
                let not_null = if c.ty.is_option() { "" } else { " NOT NULL" };
                let pk = if pk_col == Some(c.name.as_str()) {
                    " PRIMARY KEY"
                } else {
                    ""
                };
                format!("{q} {sql_ty}{not_null}{pk}")
            })
            .collect();
        let ddl = format!(
            "DROP TABLE IF EXISTS {}; CREATE TABLE {} ({});",
            quote_sql_ident(&st.table_name),
            quote_sql_ident(&st.table_name),
            col_defs.join(", ")
        );
        pg.execute(&ddl, &[])?;

        if !st.rows.is_empty() {
            // Emit explicit CAST($k AS <TYPE>) so text values like "42" or "true" bind strictly as TEXT.
            let pg_types: Vec<&str> = st
                .schema
                .cols
                .iter()
                .map(|c| match c.ty {
                    ScalarTy::Bool => "BOOLEAN",
                    ScalarTy::Int => "BIGINT",
                    ScalarTy::Decimal => "NUMERIC",
                    ScalarTy::Float => "DOUBLE PRECISION",
                    ScalarTy::Text => "TEXT",
                    ScalarTy::Bytes => "BYTEA",
                    ScalarTy::Date => "DATE",
                    ScalarTy::Timestamp => "TIMESTAMPTZ",
                    ScalarTy::Duration => "INTERVAL",
                    ScalarTy::Option(ref inner) => match inner.as_ref() {
                        ScalarTy::Bool => "BOOLEAN",
                        ScalarTy::Int => "BIGINT",
                        ScalarTy::Decimal => "NUMERIC",
                        ScalarTy::Float => "DOUBLE PRECISION",
                        ScalarTy::Text => "TEXT",
                        ScalarTy::Bytes => "BYTEA",
                        ScalarTy::Date => "DATE",
                        ScalarTy::Timestamp => "TIMESTAMPTZ",
                        ScalarTy::Duration => "INTERVAL",
                        _ => "TEXT",
                    },
                    _ => "TEXT",
                })
                .collect();
            let mut row_clauses = Vec::with_capacity(st.rows.len());
            let mut params = Vec::with_capacity(st.rows.len() * st.schema.cols.len());
            let mut k = 1usize;
            for row in &st.rows {
                let mut cols_ph = Vec::with_capacity(st.schema.cols.len());
                for (cell, pg_ty) in row.iter().zip(pg_types.iter()) {
                    cols_ph.push(format!("CAST(${k} AS {pg_ty})"));
                    params.push(SqlParam::from_val(cell)?);
                    k += 1;
                }
                row_clauses.push(format!("({})", cols_ph.join(", ")));
            }
            let insert_sql = format!(
                "INSERT INTO {} VALUES {}",
                quote_sql_ident(&st.table_name),
                row_clauses.join(", ")
            );
            pg.execute(&insert_sql, &params)?;
        }
    }
    Ok(())
}

// ===========================================================================
// Generated Pipeline Specification & Execution Helpers
// ===========================================================================

struct GeneratedCase {
    family: &'static str,
    plan: Plan,
    prog: Program,
    world: World,
    outer_vars: Vec<(Ident, LTy, Val)>,
    use_pk_lock: bool,
    pg_mock_compatible: bool,
}

fn db_source(table_name: &str, schema: TableTy) -> Plan {
    Plan::SourceDB {
        cap: Box::new(Expr::Var("db".to_string())),
        table_name: table_name.to_string(),
        schema,
    }
}

fn wrap_core_program(plan: &Plan, outer_vars: &[(Ident, LTy, Val)], include_udf: bool) -> Program {
    let all_tags = TagSet::of_list(vec!["pii".to_string(), "ferpa".to_string()]);
    let mut body = Expr::Host {
        op: HostOp::ConsolePrintTable,
        args: vec![
            Expr::Var("console".to_string()),
            Expr::Rel(Box::new(plan.clone())),
        ],
    };
    for (vname, vlty, vval) in outer_vars.iter().rev() {
        let lit = val_to_literal(vval, &vlty.ty);
        body = Expr::LetE {
            name: vname.clone(),
            lty: vlty.clone(),
            bound: Box::new(Expr::Lit(lit)),
            body: Box::new(body),
        };
    }
    let mut funs = Vec::new();
    if include_udf {
        // Pure UDF: `fn boost(x: Int) : Int = x + 3`
        funs.push(FunDecl {
            name: "boost".to_string(),
            kind: FunKind::Function,
            is_pure: true,
            params: vec![("x".to_string(), LTy::public(Ty::Int))],
            pc: TagSet::empty(),
            ret: LTy::public(Ty::Int),
            body: Expr::Prim {
                op: PrimOp::AddInt,
                args: vec![Expr::Var("x".to_string()), Expr::Lit(Literal::int(3i64))],
            },
        });
    }
    funs.push(FunDecl {
        name: "main".to_string(),
        kind: FunKind::Function,
        is_pure: false,
        params: vec![
            (
                "db".to_string(),
                LTy::public(Ty::ReadDB("Analytics".to_string())),
            ),
            (
                "console".to_string(),
                LTy::public(Ty::Console(all_tags.clone())),
            ),
        ],
        pc: TagSet::empty(),
        ret: LTy::public(Ty::Unit),
        body,
    });

    Program {
        version: Default::default(),
        tags: Vec::new(),
        policy: Some(Policy {
            min_group_size: BigInt::from(5u64),
            forbid_manual_declassify: false,
            forbid_repl_sensitive: false,
            allow_console: all_tags,
            allow_export: Vec::new(),
            allow_https: Vec::new(),
            allow_write: Vec::new(),
            ..Policy::default()
        }),
        datas: Vec::new(),
        schemas: Vec::new(),
        consts: vec![
            ConstDecl {
                name: "CUTOFF_INT".to_string(),
                lty: LTy::public(Ty::Int),
                value: Literal::int(5i64),
            },
            ConstDecl {
                name: "TARGET_GRP".to_string(),
                lty: LTy::public(Ty::Text),
                value: Literal::Text("B".to_string()),
            },
        ],
        funs,
        entry: Some("main".to_string()),
        metadata: Default::default(),
    }
}

fn val_to_literal(v: &Val, ty: &Ty) -> Literal {
    match v {
        Val::Bool(b) => Literal::Bool(*b),
        Val::Int(n) => Literal::Int(n.clone()),
        Val::Decimal(d) => Literal::Decimal(d.clone()),
        Val::Float(f) => Literal::Float(*f),
        Val::Text(s) => Literal::Text(s.clone()),
        Val::Date(d) => Literal::Date(d.clone()),
        Val::Timestamp(t) => Literal::Timestamp(t.clone()),
        Val::Duration(d) => Literal::Duration(d.clone()),
        Val::OptNone => match ty {
            Ty::Option(inner) => Literal::NoneLit((**inner).clone()),
            _ => Literal::NoneLit(Ty::Int),
        },
        _ => Literal::Unit,
    }
}

fn gen_pushable_pred(rng: &mut SplitMix64, p_int: i64, p_txt: &str) -> RowExpr {
    match rng.gen_range(12) {
        0 => RowExpr::Prim {
            op: PrimOp::Gt,
            args: vec![
                RowExpr::Col("val".to_string()),
                RowExpr::OuterVar("p_int".to_string()),
            ],
        },
        1 => RowExpr::Prim {
            op: PrimOp::Le,
            args: vec![
                RowExpr::Col("val".to_string()),
                RowExpr::ConstRef("CUTOFF_INT".to_string()),
            ],
        },
        2 => RowExpr::Prim {
            op: PrimOp::AndBool,
            args: vec![
                RowExpr::Col("flag".to_string()),
                RowExpr::Prim {
                    op: PrimOp::Ne,
                    args: vec![
                        RowExpr::Col("grp".to_string()),
                        RowExpr::ConstRef("TARGET_GRP".to_string()),
                    ],
                },
            ],
        },
        3 => RowExpr::Prim {
            op: PrimOp::OrBool,
            args: vec![
                RowExpr::Prim {
                    op: PrimOp::IsNone,
                    args: vec![RowExpr::Col("opt_val".to_string())],
                },
                RowExpr::Prim {
                    op: PrimOp::Ge,
                    args: vec![
                        RowExpr::Coalesce {
                            opt_expr: Box::new(RowExpr::Col("opt_val".to_string())),
                            default_expr: Box::new(RowExpr::Lit(Literal::int(0i64))),
                        },
                        RowExpr::Lit(Literal::int(p_int)),
                    ],
                },
            ],
        },
        4 => RowExpr::Prim {
            op: PrimOp::IsSome,
            args: vec![RowExpr::Col("opt_note".to_string())],
        },
        5 => RowExpr::Prim {
            op: PrimOp::ContainsText,
            args: vec![
                RowExpr::Prim {
                    op: PrimOp::LowerAsciiText,
                    args: vec![RowExpr::Prim {
                        op: PrimOp::TrimText,
                        args: vec![RowExpr::Col("name".to_string())],
                    }],
                },
                RowExpr::OuterVar("p_txt".to_string()),
            ],
        },
        6 => RowExpr::Prim {
            op: PrimOp::NotBool,
            args: vec![RowExpr::Prim {
                op: PrimOp::EmptyText,
                args: vec![RowExpr::Col("name".to_string())],
            }],
        },
        7 => RowExpr::Prim {
            op: PrimOp::Eq,
            args: vec![
                RowExpr::Col("opt_val".to_string()),
                RowExpr::Lit(Literal::NoneLit(Ty::Int)),
            ],
        },
        8 => RowExpr::Prim {
            op: PrimOp::Ne,
            args: vec![
                RowExpr::Col("opt_note".to_string()),
                RowExpr::Prim {
                    op: PrimOp::SomeVal(Ty::Text),
                    args: vec![RowExpr::Lit(Literal::Text(p_txt.to_string()))],
                },
            ],
        },
        9 => RowExpr::Prim {
            op: PrimOp::Ge,
            args: vec![
                RowExpr::Col("day".to_string()),
                RowExpr::Lit(Literal::date(days_from_civil(2025, 1, 1))),
            ],
        },
        10 => RowExpr::Prim {
            op: PrimOp::Lt,
            args: vec![
                RowExpr::Col("dur".to_string()),
                RowExpr::Lit(Literal::duration(5_000_000i64)),
            ],
        },
        _ => RowExpr::IfE {
            cond: Box::new(RowExpr::Col("flag".to_string())),
            then_br: Box::new(RowExpr::Prim {
                op: PrimOp::Gt,
                args: vec![
                    RowExpr::Col("val".to_string()),
                    RowExpr::Lit(Literal::int(0i64)),
                ],
            }),
            else_br: Box::new(RowExpr::Prim {
                op: PrimOp::Eq,
                args: vec![
                    RowExpr::Col("grp".to_string()),
                    RowExpr::Lit(Literal::Text("A".to_string())),
                ],
            }),
        },
    }
}

fn generate_case(rng: &mut SplitMix64, idx: usize) -> GeneratedCase {
    let family_id = idx % 15;
    let n_rows = if idx.is_multiple_of(37) {
        0 // Explicitly exercise empty-table behavior across every family!
    } else {
        4 + rng.gen_range(14)
    };
    let items_rows = gen_items_rows(rng, n_rows, 0);
    let n_items2 = rng.gen_range(7);
    let items2_rows = gen_items_rows(rng, n_items2, 100);
    let n_dim_uniq = 2 + rng.gen_range(8);
    let dim_uniq_rows = gen_dim_rows(rng, n_dim_uniq, true);
    let n_dim_dup = 5 + rng.gen_range(5);
    let dim_dup_rows = gen_dim_rows(rng, n_dim_dup, false);

    let p_int = rng.pick_small_int();
    let p_txt_choices = ["a", "b", "42", "", "alpha", "%"];
    let p_txt = p_txt_choices[rng.gen_range(p_txt_choices.len())].to_string();
    let outer_vars = vec![
        (
            "p_int".to_string(),
            LTy::public(Ty::Int),
            Val::Int(BigInt::from(p_int)),
        ),
        (
            "p_txt".to_string(),
            LTy::public(Ty::Text),
            Val::Text(p_txt.clone()),
        ),
    ];

    let all_tags = TagSet::of_list(vec!["pii".to_string(), "ferpa".to_string()]);
    let world = World {
        runtime_allow_export: all_tags,
        real_db_tables: vec![
            StoredTable {
                db: "Analytics".to_string(),
                table_name: "items".to_string(),
                schema: items_schema(),
                rows: items_rows,
            },
            StoredTable {
                db: "Analytics".to_string(),
                table_name: "items2".to_string(),
                schema: items_schema(),
                rows: items2_rows,
            },
            StoredTable {
                db: "Analytics".to_string(),
                table_name: "dim_uniq".to_string(),
                schema: dim_schema(),
                rows: dim_uniq_rows,
            },
            StoredTable {
                db: "Analytics".to_string(),
                table_name: "dim_dup".to_string(),
                schema: dim_schema(),
                rows: dim_dup_rows,
            },
        ],
        ..World::default()
    };

    let base = db_source("items", items_schema());
    let mut use_pk_lock = true;
    let mut include_udf = false;
    let mut pg_mock_compatible = true;

    let (family, plan) = match family_id {
        // Family 0: Filter + Select / Drop / Rename (FullyPushed)
        0 => {
            let p1 = gen_pushable_pred(rng, p_int, &p_txt);
            let p2 = gen_pushable_pred(rng, p_int, &p_txt);
            let mut pl = Plan::Filter {
                input: Box::new(base),
                pred: p1,
            };
            if rng.gen_bool(1, 2) {
                pl = Plan::Filter {
                    input: Box::new(pl),
                    pred: p2,
                };
            }
            match rng.gen_range(3) {
                0 => {
                    pl = Plan::Select {
                        input: Box::new(pl),
                        cols: vec![
                            "id".to_string(),
                            "grp".to_string(),
                            "val".to_string(),
                            "opt_val".to_string(),
                            "name".to_string(),
                            "day".to_string(),
                        ],
                    };
                }
                1 => {
                    pl = Plan::Drop {
                        input: Box::new(pl),
                        cols: vec!["score".to_string(), "amt".to_string()],
                    };
                }
                _ => {
                    pl = Plan::Rename {
                        input: Box::new(pl),
                        pairs: vec![
                            ("group_code".to_string(), "grp".to_string()),
                            ("value_int".to_string(), "val".to_string()),
                        ],
                    };
                    pl = Plan::Select {
                        input: Box::new(pl),
                        cols: vec![
                            "id".to_string(),
                            "group_code".to_string(),
                            "value_int".to_string(),
                            "dur".to_string(),
                        ],
                    };
                }
            }
            ("filter_proj_rename", pl)
        }
        // Family 1: Total Derive + BucketCol + Post-Derive Filter (FullyPushed)
        1 => {
            let filtered = Plan::Filter {
                input: Box::new(base),
                pred: gen_pushable_pred(rng, p_int, &p_txt),
            };
            let derived = Plan::Derive {
                input: Box::new(filtered),
                items: vec![
                    DeriveItem::ColExpr {
                        name: "clean_name".to_string(),
                        expr: Box::new(RowExpr::Prim {
                            op: PrimOp::LowerAsciiText,
                            args: vec![RowExpr::Prim {
                                op: PrimOp::TrimText,
                                args: vec![RowExpr::Col("name".to_string())],
                            }],
                        }),
                    },
                    DeriveItem::ColExpr {
                        name: "tagged".to_string(),
                        expr: Box::new(RowExpr::Prim {
                            op: PrimOp::ConcatText,
                            args: vec![
                                RowExpr::Col("clean_name".to_string()),
                                RowExpr::Prim {
                                    op: PrimOp::IntToText,
                                    args: vec![RowExpr::Col("val".to_string())],
                                },
                            ],
                        }),
                    },
                    DeriveItem::BucketCol {
                        name: "val_band".to_string(),
                        source: "val".to_string(),
                        cuts: vec![Literal::int(0i64), Literal::int(10i64)],
                        labels: vec!["neg".to_string(), "low".to_string(), "high".to_string()],
                    },
                ],
            };
            let post_filtered = Plan::Filter {
                input: Box::new(derived),
                pred: RowExpr::Prim {
                    op: PrimOp::Ne,
                    args: vec![
                        RowExpr::Col("val_band".to_string()),
                        RowExpr::Lit(Literal::Text("neg".to_string())),
                    ],
                },
            };
            let pl = Plan::Select {
                input: Box::new(post_filtered),
                cols: vec![
                    "id".to_string(),
                    "tagged".to_string(),
                    "val_band".to_string(),
                ],
            };
            ("derive_bucket", pl)
        }
        // Family 2: Tie-Free Sort (with PK) + Limit (FullyPushed)
        2 => {
            let filtered = Plan::Filter {
                input: Box::new(base),
                pred: gen_pushable_pred(rng, p_int, &p_txt),
            };
            let dir1 = if rng.gen_bool(1, 2) {
                SortDir::Asc
            } else {
                SortDir::Desc
            };
            let dir2 = if rng.gen_bool(1, 2) {
                SortDir::Asc
            } else {
                SortDir::Desc
            };
            let sort_col = match rng.gen_range(4) {
                0 => "opt_val",
                1 => "opt_note",
                2 => "day",
                _ => "grp",
            };
            let sorted = Plan::Sort {
                input: Box::new(filtered),
                keys: vec![(sort_col.to_string(), dir1), ("id".to_string(), dir2)],
            };
            let lim = match rng.gen_range(4) {
                0 => 0i64,
                1 => 2,
                2 => 5,
                _ => 50,
            };
            let pl = Plan::Limit {
                input: Box::new(sorted),
                n: BigInt::from(lim),
            };
            ("sort_pk_limit", pl)
        }
        // Family 3: Non-unique Sort with ties + Limit (Hybrid — tie-breaking stays local)
        3 => {
            let filtered = Plan::Filter {
                input: Box::new(base),
                pred: gen_pushable_pred(rng, p_int, &p_txt),
            };
            let sorted = Plan::Sort {
                input: Box::new(filtered),
                keys: vec![(
                    "grp".to_string(),
                    if rng.gen_bool(1, 2) {
                        SortDir::Asc
                    } else {
                        SortDir::Desc
                    },
                )],
            };
            let pl = Plan::Limit {
                input: Box::new(sorted),
                n: BigInt::from((1 + rng.gen_range(6)) as i64),
            };
            ("sort_ties_local", pl)
        }
        // Family 4: GroupBy + Pushable Summarize (Count, CountDistinct, Min, Max) (FullyPushed)
        4 => {
            let filtered = Plan::Filter {
                input: Box::new(base),
                pred: gen_pushable_pred(rng, p_int, &p_txt),
            };
            let grouped = match rng.gen_range(3) {
                0 => filtered, // Ungrouped (tests empty-table 1-row behavior!)
                1 => Plan::GroupBy {
                    input: Box::new(filtered),
                    keys: vec!["grp".to_string()],
                },
                _ => Plan::GroupBy {
                    input: Box::new(filtered),
                    keys: vec!["flag".to_string(), "grp".to_string()], // Out of schema order!
                },
            };
            let aggs = vec![
                AggItem {
                    name: "n_rows".to_string(),
                    op: AggOp::Count,
                    arg: None,
                },
                AggItem {
                    name: "n_opt".to_string(),
                    op: AggOp::CountDistinct,
                    arg: Some(RowExpr::Col("opt_val".to_string())),
                },
                AggItem {
                    name: "min_v".to_string(),
                    op: AggOp::Min,
                    arg: Some(RowExpr::Col("val".to_string())),
                },
                AggItem {
                    name: "max_txt".to_string(),
                    op: AggOp::Max,
                    arg: Some(RowExpr::Col("opt_note".to_string())),
                },
            ];
            let mut pl = Plan::Summarize {
                input: Box::new(grouped),
                aggs,
                distinct_key: None,
            };
            if rng.gen_bool(1, 2) {
                pl = Plan::Limit {
                    input: Box::new(pl),
                    n: BigInt::from(3i64),
                };
            }
            ("groupby_summarize_pushed", pl)
        }
        // Family 5: Hybrid GroupBy + Summarize with Local Aggs (Sum/Mean/Median/First/Last)
        5 => {
            let filtered = Plan::Filter {
                input: Box::new(base),
                pred: gen_pushable_pred(rng, p_int, &p_txt),
            };
            let grouped = Plan::GroupBy {
                input: Box::new(filtered),
                keys: vec!["grp".to_string()],
            };
            let local_agg = match rng.gen_range(5) {
                0 => AggItem {
                    name: "s".to_string(),
                    op: AggOp::Sum,
                    arg: Some(RowExpr::Col("val".to_string())),
                },
                1 => AggItem {
                    name: "m".to_string(),
                    op: AggOp::Mean,
                    arg: Some(RowExpr::Col("amt".to_string())),
                },
                2 => AggItem {
                    name: "med".to_string(),
                    op: AggOp::Median,
                    arg: Some(RowExpr::Col("val".to_string())),
                },
                3 => AggItem {
                    name: "fst".to_string(),
                    op: AggOp::First,
                    arg: Some(RowExpr::Col("opt_val".to_string())),
                },
                _ => AggItem {
                    name: "lst".to_string(),
                    op: AggOp::Last,
                    arg: Some(RowExpr::Col("name".to_string())),
                },
            };
            let pl = Plan::Summarize {
                input: Box::new(grouped),
                aggs: vec![
                    AggItem {
                        name: "cnt".to_string(),
                        op: AggOp::Count,
                        arg: None,
                    },
                    local_agg,
                ],
                distinct_key: None,
            };
            ("groupby_summarize_hybrid", pl)
        }
        // Family 6: Local-VM Traps, Pure UDF, Float NaN/-0.0, SQLite Decimal Ordering (Hybrid)
        6 => {
            include_udf = true;
            let filtered = Plan::Filter {
                input: Box::new(base),
                pred: RowExpr::Prim {
                    op: PrimOp::Gt,
                    args: vec![
                        RowExpr::Col("id".to_string()),
                        RowExpr::Lit(Literal::int(0i64)),
                    ],
                },
            };
            let pl = match rng.gen_range(5) {
                0 => Plan::Derive {
                    input: Box::new(filtered),
                    items: vec![DeriveItem::ColExpr {
                        name: "boosted".to_string(),
                        expr: Box::new(RowExpr::CallPure {
                            fn_name: "boost".to_string(),
                            args: vec![RowExpr::Col("val".to_string())],
                        }),
                    }],
                },
                1 => Plan::Derive {
                    input: Box::new(filtered),
                    items: vec![DeriveItem::ColExpr {
                        name: "q".to_string(),
                        expr: Box::new(RowExpr::Prim {
                            op: PrimOp::DivInt,
                            args: vec![
                                RowExpr::Col("id".to_string()),
                                RowExpr::Col("val".to_string()), // May trap DivByZero!
                            ],
                        }),
                    }],
                },
                2 => Plan::Derive {
                    input: Box::new(filtered),
                    items: vec![DeriveItem::ColExpr {
                        name: "u".to_string(),
                        expr: Box::new(RowExpr::Prim {
                            op: PrimOp::UnwrapBang,
                            args: vec![RowExpr::Col("opt_val".to_string())], // May trap UnwrapNone!
                        }),
                    }],
                },
                3 => Plan::Sort {
                    input: Box::new(filtered),
                    keys: vec![
                        ("score".to_string(), SortDir::Asc),
                        ("id".to_string(), SortDir::Asc),
                    ],
                },
                _ => {
                    // Decimal comparison stays local on SQLite (and pushes on PG; skip mock PG for numeric TEXT ordering).
                    pg_mock_compatible = false;
                    Plan::Filter {
                        input: Box::new(filtered),
                        pred: RowExpr::Prim {
                            op: PrimOp::Ge,
                            args: vec![
                                RowExpr::Col("amt".to_string()),
                                RowExpr::Lit(Literal::decimal(0i128)),
                            ],
                        },
                    }
                }
            };
            ("udf_trap_float_dec", pl)
        }
        // Family 7: Same-DB InnerMany / Semi / Anti Joins + Outer Order (FullyPushed)
        7 => {
            let left = Plan::Select {
                input: Box::new(Plan::Filter {
                    input: Box::new(base),
                    pred: gen_pushable_pred(rng, p_int, &p_txt),
                }),
                cols: vec![
                    "id".to_string(),
                    "grp".to_string(),
                    "val".to_string(),
                    "opt_val".to_string(),
                ],
            };
            let right = db_source("dim_dup", dim_schema());
            let kind = match rng.gen_range(3) {
                0 => JoinKind::InnerMany,
                1 => JoinKind::Semi,
                _ => JoinKind::Anti,
            };
            let (on, suffixes) = if rng.gen_bool(1, 3) {
                // Nullable key join testing `None == None` parity!
                (
                    JoinOn::Pairs(vec![("opt_val".to_string(), "opt_k".to_string())]),
                    Some(("_l".to_string(), "_r".to_string())),
                )
            } else {
                (
                    JoinOn::SameKeys(vec!["grp".to_string()]),
                    Some(("_l".to_string(), "_r".to_string())),
                )
            };
            let grp_col = if matches!(kind, JoinKind::InnerMany) && matches!(on, JoinOn::Pairs(_)) {
                "grp_l".to_string()
            } else {
                "grp".to_string()
            };
            let joined = Plan::Join {
                kind,
                left: Box::new(left),
                right: Box::new(right),
                on,
                suffixes,
            };
            // Wrap in Summarize (order-insensitive!) so SQL INNER JOIN / EXISTS / NOT EXISTS pushes cleanly!
            let pl = Plan::Summarize {
                input: Box::new(Plan::GroupBy {
                    input: Box::new(joined),
                    keys: vec![grp_col],
                }),
                aggs: vec![
                    AggItem {
                        name: "n".to_string(),
                        op: AggOp::Count,
                        arg: None,
                    },
                    AggItem {
                        name: "max_v".to_string(),
                        op: AggOp::Max,
                        arg: Some(RowExpr::Col("val".to_string())),
                    },
                ],
                distinct_key: None,
            };
            ("join_many_semi_anti", pl)
        }
        // Family 8: Checked Joins (PK-proven -> FullyPushed; unchecked/dup -> LocalOnly with redacted [pii] trap!)
        8 => {
            let left = Plan::Select {
                input: Box::new(base),
                cols: vec!["id".to_string(), "grp".to_string(), "val".to_string()],
            };
            if rng.gen_bool(2, 3) {
                // Proven unique via SchemaLockFile PK on `dim_uniq.id` and `items.id`!
                let right = db_source("dim_uniq", dim_schema());
                let kind = match rng.gen_range(4) {
                    0 => JoinKind::InnerOne,
                    1 => JoinKind::InnerManyToOne,
                    2 => JoinKind::LeftOne,
                    _ => JoinKind::LeftManyToOne,
                };
                let joined = Plan::Join {
                    kind,
                    left: Box::new(left),
                    right: Box::new(right),
                    on: JoinOn::SameKeys(vec!["id".to_string()]),
                    suffixes: Some(("_l".to_string(), "_r".to_string())),
                };
                let pl = Plan::Sort {
                    input: Box::new(joined),
                    keys: vec![("id".to_string(), SortDir::Asc)],
                };
                ("join_checked_pk_pushed", pl)
            } else {
                // Unchecked duplicate keys on `[pii]` column `secret_key` -> MUST stop locally with redacted Bug!
                use_pk_lock = false;
                let left_pii = Plan::Select {
                    input: Box::new(db_source("dim_dup", dim_schema())),
                    cols: vec!["id".to_string(), "secret_key".to_string()],
                };
                let right_pii = Plan::Select {
                    input: Box::new(db_source("dim_dup", dim_schema())),
                    cols: vec!["secret_key".to_string(), "weight".to_string()],
                };
                let kind = if rng.gen_bool(1, 2) {
                    JoinKind::InnerOne
                } else {
                    JoinKind::LeftManyToOne
                };
                let pl = Plan::Join {
                    kind,
                    left: Box::new(left_pii),
                    right: Box::new(right_pii),
                    on: JoinOn::SameKeys(vec!["secret_key".to_string()]),
                    suffixes: None,
                };
                ("join_checked_dup_local", pl)
            }
        }
        // Family 9: Same-DB Union (`UNION ALL`) + Sort/Summarize (FullyPushed)
        9 => {
            let l = Plan::Select {
                input: Box::new(Plan::Filter {
                    input: Box::new(base),
                    pred: gen_pushable_pred(rng, p_int, &p_txt),
                }),
                cols: vec!["id".to_string(), "grp".to_string(), "val".to_string()],
            };
            let r = Plan::Select {
                input: Box::new(Plan::Filter {
                    input: Box::new(db_source("items2", items_schema())),
                    pred: gen_pushable_pred(rng, p_int, &p_txt),
                }),
                cols: vec!["id".to_string(), "grp".to_string(), "val".to_string()],
            };
            let u = Plan::Union {
                left: Box::new(l),
                right: Box::new(r),
            };
            let pl = Plan::Summarize {
                input: Box::new(Plan::GroupBy {
                    input: Box::new(u),
                    keys: vec!["grp".to_string()],
                }),
                aggs: vec![
                    AggItem {
                        name: "n".to_string(),
                        op: AggOp::Count,
                        arg: None,
                    },
                    AggItem {
                        name: "min_id".to_string(),
                        op: AggOp::Min,
                        arg: Some(RowExpr::Col("id".to_string())),
                    },
                ],
                distinct_key: None,
            };
            ("union_all", pl)
        }
        // Family 10: Distinct (all-col + Sort -> FullyPushed; subset/bare -> Hybrid)
        10 => {
            let sel = Plan::Select {
                input: Box::new(Plan::Filter {
                    input: Box::new(base),
                    pred: gen_pushable_pred(rng, p_int, &p_txt),
                }),
                cols: vec!["grp".to_string(), "flag".to_string()],
            };
            let pl = if rng.gen_bool(2, 3) {
                let d = Plan::Distinct {
                    input: Box::new(sel),
                    cols: Vec::new(),
                };
                Plan::Sort {
                    input: Box::new(d),
                    keys: vec![
                        ("grp".to_string(), SortDir::Asc),
                        ("flag".to_string(), SortDir::Desc),
                    ],
                }
            } else {
                Plan::Distinct {
                    input: Box::new(sel),
                    cols: vec!["grp".to_string()],
                }
            };
            ("distinct", pl)
        }
        // Family 11: Redact on Text and Option(Text) [pii] columns (FullyPushed)
        11 => {
            let filtered = Plan::Filter {
                input: Box::new(base),
                pred: gen_pushable_pred(rng, p_int, &p_txt),
            };
            let target_col = if rng.gen_bool(1, 2) {
                "name"
            } else {
                "opt_note"
            };
            let redacted = Plan::Redact {
                input: Box::new(filtered),
                col: target_col.to_string(),
                replacement: "[REDACTED]".to_string(),
            };
            let pl = Plan::Select {
                input: Box::new(redacted),
                cols: vec!["id".to_string(), "grp".to_string(), target_col.to_string()],
            };
            ("redact", pl)
        }
        // Family 12: SuppressSmallGroups (`Drop` & `MaskComplementary`) local suffix (Hybrid)
        12 => {
            let filtered = Plan::Filter {
                input: Box::new(base),
                pred: RowExpr::Prim {
                    op: PrimOp::Ge,
                    args: vec![
                        RowExpr::Col("val".to_string()),
                        RowExpr::Lit(Literal::int(-5i64)),
                    ],
                },
            };
            let mode = if rng.gen_bool(1, 2) {
                SuppressMode::Drop
            } else {
                SuppressMode::MaskComplementary
            };
            let distinct_by = if rng.gen_bool(1, 2) {
                Some("id".to_string())
            } else {
                None
            };
            let summ = Plan::Summarize {
                input: Box::new(Plan::GroupBy {
                    input: Box::new(filtered),
                    keys: vec!["grp".to_string()],
                }),
                aggs: vec![
                    AggItem {
                        name: "n".to_string(),
                        op: AggOp::Count,
                        arg: None,
                    },
                    AggItem {
                        name: "nd".to_string(),
                        op: AggOp::CountDistinct,
                        arg: Some(RowExpr::Col("id".to_string())),
                    },
                ],
                distinct_key: distinct_by.clone(),
            };
            let pl = Plan::SuppressSmallGroups {
                input: Box::new(summ),
                min_k: BigInt::from(5u64),
                distinct_by,
                mode,
            };
            ("suppress_small_groups_hybrid", pl)
        }
        // Family 13: Window local suffix over pushed DB Filter/Select/Derive (Hybrid)
        13 => {
            let filtered = Plan::Select {
                input: Box::new(Plan::Filter {
                    input: Box::new(base),
                    pred: gen_pushable_pred(rng, p_int, &p_txt),
                }),
                cols: vec!["id".to_string(), "grp".to_string(), "val".to_string()],
            };
            let win_fn = match rng.gen_range(6) {
                0 => WindowFn::RowNumber,
                1 => WindowFn::Rank {
                    col: "val".to_string(),
                },
                2 => WindowFn::Lag {
                    col: "val".to_string(),
                    offset: BigInt::from(1u64),
                },
                3 => WindowFn::Lead {
                    col: "val".to_string(),
                    offset: BigInt::from(1u64),
                },
                4 => WindowFn::RunningSum {
                    col: "val".to_string(),
                },
                _ => WindowFn::RollingMean {
                    col: "val".to_string(),
                    window_size: BigInt::from(2u64),
                },
            };
            let pl = Plan::Window {
                input: Box::new(filtered),
                items: vec![WindowItem {
                    name: "w".to_string(),
                    win_fn,
                    over: vec!["grp".to_string()],
                    order: vec![("id".to_string(), SortDir::Asc)],
                }],
            };
            ("window_hybrid", pl)
        }
        // Family 14: Hybrid DB-vs-Local TableLit Join (Hybrid)
        _ => {
            let db_left = Plan::Select {
                input: Box::new(Plan::Filter {
                    input: Box::new(base),
                    pred: gen_pushable_pred(rng, p_int, &p_txt),
                }),
                cols: vec!["id".to_string(), "grp".to_string(), "val".to_string()],
            };
            let local_right = Plan::SourceExpr(Box::new(Expr::TableLit {
                schema: TableTy {
                    cols: vec![
                        col("grp", ScalarTy::Text, &[]),
                        col("label", ScalarTy::Text, &[]),
                    ],
                    ..TableTy::default()
                },
                rows: vec![
                    RowLit {
                        cells: vec![
                            Literal::Text("A".to_string()),
                            Literal::Text("Group-A".to_string()),
                        ],
                    },
                    RowLit {
                        cells: vec![
                            Literal::Text("B".to_string()),
                            Literal::Text("Group-B".to_string()),
                        ],
                    },
                    RowLit {
                        cells: vec![
                            Literal::Text("C".to_string()),
                            Literal::Text("Group-C".to_string()),
                        ],
                    },
                ],
            }));
            let pl = Plan::Join {
                kind: JoinKind::LeftManyToOne,
                left: Box::new(db_left),
                right: Box::new(local_right),
                on: JoinOn::SameKeys(vec!["grp".to_string()]),
                suffixes: None,
            };
            ("db_vs_local_join_hybrid", pl)
        }
    };

    let prog = wrap_core_program(&plan, &outer_vars, include_udf);
    GeneratedCase {
        family,
        plan,
        prog,
        world,
        outer_vars,
        use_pk_lock,
        pg_mock_compatible,
    }
}

#[derive(Default)]
struct PushdownStats {
    fully_pushed: usize,
    hybrid: usize,
    local_only: usize,
}

type SplitOutcome = (ExitStatus, Option<String>, Option<String>);

fn execute_split_against_conn(
    conn: &mut dyn DbConnection,
    case: &GeneratedCase,
    opt_plan: &Plan,
    dialect: SqlDialect,
    lock: Option<&SchemaLockFile>,
    stats: &mut PushdownStats,
) -> Result<Option<SplitOutcome>, String> {
    let split = split_core_plan_pushdown(opt_plan, &case.prog, "Analytics", dialect, lock);
    let var_map: HashMap<&str, Val> = case
        .outer_vars
        .iter()
        .map(|(n, _, v)| (n.as_str(), v.clone()))
        .collect();
    let lookup_var = |name: &str| var_map.get(name).cloned();
    let lookup_const = |name: &str| case.prog.find_const(name).map(|c| eval_literal(&c.value));

    let env_entries: Vec<EnvEntry> = case
        .outer_vars
        .iter()
        .map(|(n, lty, v)| EnvEntry {
            name: n.clone(),
            lty: lty.clone(),
            val: v.clone(),
        })
        .collect();
    let outer_env = EnvList::from_vec(env_entries);
    let vm_cfg = VmConfig::sequential_optimized();

    match split {
        SplitPlan::FullyPushed(q) => {
            stats.fully_pushed += 1;
            let params = q.resolve_params(lookup_var, lookup_const)?;
            let vm_tbl = conn
                .query_batches(&q.sql, &params, &q.out_schema, BATCH_SIZE)
                .map_err(|e| format!("DB query_batches failed on `{}`: {e}", q.sql))?;
            let rendered = render_core_table_text(&vm_tbl.into_table_val());
            Ok(Some((ExitStatus::Ok, None, Some(rendered))))
        }
        SplitPlan::Hybrid {
            pushdown,
            placeholder_var,
            local_suffix,
        } => {
            stats.hybrid += 1;
            let params = pushdown.resolve_params(lookup_var, lookup_const)?;
            let pushed_tbl = conn
                .query_batches(&pushdown.sql, &params, &pushdown.out_schema, BATCH_SIZE)
                .map_err(|e| {
                    format!("DB hybrid query_batches failed on `{}`: {e}", pushdown.sql)
                })?;
            match eval_core_plan_batches_with_env(
                &case.prog,
                &outer_env,
                &placeholder_var,
                pushed_tbl,
                &local_suffix,
                &vm_cfg,
            ) {
                Ok(final_tbl) => {
                    let rendered = render_core_table_text(&final_tbl.into_table_val());
                    Ok(Some((ExitStatus::Ok, None, Some(rendered))))
                }
                Err(OpErr::Stopped(bug)) => {
                    Ok(Some((ExitStatus::Stopped, Some(bug.message), None)))
                }
                Err(OpErr::Failed(msg)) => Ok(Some((ExitStatus::Failed, Some(msg), None))),
                Err(OpErr::Wrong) => Err(format!(
                    "local suffix returned OpErr::Wrong on family `{}`",
                    case.family
                )),
            }
        }
        SplitPlan::LocalOnly { .. } => {
            stats.local_only += 1;
            // LocalOnly executes directly on the local VM (already verified against oracle).
            Ok(None)
        }
    }
}

fn assert_matches_oracle(
    label: &str,
    idx: usize,
    family: &str,
    oracle: &ExecReport,
    actual: (ExitStatus, Option<String>, Option<String>),
) -> Result<(), String> {
    let (status, diag, table_out) = actual;
    if status != oracle.status {
        return Err(format!(
            "case #{idx} ({family}) [{label}] status mismatch: oracle={:?} ({:?}) vs actual={:?} ({:?})",
            oracle.status, oracle.diagnostic, status, diag
        ));
    }
    if status == ExitStatus::Ok {
        let expected_out = oracle.stdout.first().cloned().unwrap_or_default();
        let actual_out = table_out.unwrap_or_default();
        if actual_out != expected_out {
            return Err(format!(
                "case #{idx} ({family}) [{label}] table mismatch!\n--- ORACLE ---\n{expected_out}\n--- {label} ---\n{actual_out}"
            ));
        }
    } else if diag != oracle.diagnostic {
        return Err(format!(
            "case #{idx} ({family}) [{label}] diagnostic mismatch: oracle={:?} vs actual={:?}",
            oracle.diagnostic, diag
        ));
    }
    Ok(())
}

// ===========================================================================
// 1. 1,000+ Differential Verification Gate (Oracle == VM == SQLite == Postgres)
// ===========================================================================

#[test]
fn differential_1000_oracle_vm_sqlite_postgres_pushdown() -> TestResult {
    const TOTAL_CASES: usize = 1_125;
    let mut rng = SplitMix64::new(0xDADA_3B00_2026_0001);

    let mut sqlite_drv = SqliteDriver::open_in_memory()?;
    let (pg_port, pg_srv) = spawn_pg_pushdown_server()?;
    let pg_uri = format!("postgres://dana@127.0.0.1:{pg_port}/testdb?sslmode=disable");
    let DbUri::Postgres(pg_parsed) = DbUri::parse(&pg_uri)? else {
        return Err("expected postgres uri".into());
    };
    let mut pg_drv = PostgresDriver::connect(&pg_parsed)?;

    let sqlite_lock_pk = build_schema_lock("Analytics", SqlDialect::Sqlite, true);
    let sqlite_lock_nopk = build_schema_lock("Analytics", SqlDialect::Sqlite, false);
    let pg_lock_pk = build_schema_lock("Analytics", SqlDialect::Postgres, true);
    let pg_lock_nopk = build_schema_lock("Analytics", SqlDialect::Postgres, false);

    let mut sqlite_stats = PushdownStats::default();
    let mut pg_stats = PushdownStats::default();
    let mut pg_cases_run = 0usize;
    let mut trap_cases_verified = 0usize;

    for idx in 0..TOTAL_CASES {
        let case = generate_case(&mut rng, idx);

        // 1. Static check_program must succeed.
        check_program(&case.prog)
            .map_err(|e| format!("case #{idx} ({}) failed check_program: {e}", case.family))?;

        // 2. Naive reference oracle.
        let oracle_report = run_program(200_000, &case.prog, case.world.clone())
            .map_err(|e| format!("case #{idx} ({}) oracle failed: {}", case.family, e.message))?;
        if oracle_report.status == ExitStatus::Stopped {
            trap_cases_verified += 1;
        }

        // 3. Vectorized columnar VM (optimized) == oracle.
        let vm_report = run_core_program_vm(
            200_000,
            &case.prog,
            case.world.clone(),
            &VmConfig::sequential_optimized(),
        )
        .map_err(|e| format!("case #{idx} ({}) VM failed: {}", case.family, e.message))?;
        assert_eq!(
            vm_report, oracle_report,
            "case #{idx} ({}) VM diverged from oracle",
            case.family
        );

        let (opt_plan, _) = optimize_plan(&case.plan, &case.prog);
        let pk_specs: &[(&str, &str)] = if case.use_pk_lock {
            &[("items", "id"), ("items2", "id"), ("dim_uniq", "id")]
        } else {
            &[]
        };

        // 4. Live SQLite pushdown + local VM suffix == oracle (ALL 1,125 cases!).
        load_tables_into_sqlite(&mut sqlite_drv, &case.world.real_db_tables, pk_specs)?;
        let sq_lock = if case.use_pk_lock {
            Some(&sqlite_lock_pk)
        } else {
            Some(&sqlite_lock_nopk)
        };
        if let Some(sq_res) = execute_split_against_conn(
            &mut sqlite_drv,
            &case,
            &opt_plan,
            SqlDialect::Sqlite,
            sq_lock,
            &mut sqlite_stats,
        )? {
            assert_matches_oracle("SQLite", idx, case.family, &oracle_report, sq_res)?;
        }

        // 5. Live loopback Postgres v3.0 wire protocol pushdown + local VM suffix == oracle (>= 350 cases covering every family!).
        if case.pg_mock_compatible && idx % 3 == 0 {
            load_tables_into_pg_mock(&mut pg_drv, &case.world.real_db_tables, pk_specs)?;
            let pg_lock = if case.use_pk_lock {
                Some(&pg_lock_pk)
            } else {
                Some(&pg_lock_nopk)
            };
            if let Some(pg_res) = execute_split_against_conn(
                &mut pg_drv,
                &case,
                &opt_plan,
                SqlDialect::Postgres,
                pg_lock,
                &mut pg_stats,
            )? {
                assert_matches_oracle("Postgres", idx, case.family, &oracle_report, pg_res)?;
            }
            pg_cases_run += 1;
        }
    }

    drop(pg_drv);
    let _ = pg_srv.join();

    println!(
        "Phase 3B Differential Gate Summary ({TOTAL_CASES} cases, {trap_cases_verified} stop/trap cases):\n  \
         SQLite   -> FullyPushed={}, Hybrid={}, LocalOnly={}\n  \
         Postgres -> {pg_cases_run} cases: FullyPushed={}, Hybrid={}, LocalOnly={}",
        sqlite_stats.fully_pushed,
        sqlite_stats.hybrid,
        sqlite_stats.local_only,
        pg_stats.fully_pushed,
        pg_stats.hybrid,
        pg_stats.local_only,
    );

    assert!(
        sqlite_stats.fully_pushed >= 500,
        "expected >= 500 FullyPushed SQLite pipelines, got {}",
        sqlite_stats.fully_pushed
    );
    assert!(
        sqlite_stats.hybrid >= 400,
        "expected >= 400 Hybrid SQLite pipelines, got {}",
        sqlite_stats.hybrid
    );
    assert!(
        sqlite_stats.local_only <= 100,
        "too many LocalOnly SQLite pipelines: {}",
        sqlite_stats.local_only
    );
    assert!(
        pg_cases_run >= 350,
        "expected >= 350 Postgres wire differential cases, ran {pg_cases_run}"
    );
    assert!(
        pg_stats.fully_pushed >= 150 && pg_stats.hybrid >= 130,
        "expected strong Postgres pushdown coverage, got full={} hybrid={}",
        pg_stats.fully_pushed,
        pg_stats.hybrid
    );
    assert!(
        trap_cases_verified >= 30,
        "expected >= 30 stop/trap parity cases verified, got {trap_cases_verified}"
    );
    Ok(())
}

// ===========================================================================
// 2. SQL Injection Resistance (SQLite & Postgres Wire Protocol)
// ===========================================================================

#[test]
fn sql_injection_resistance_sqlite_and_postgres() -> TestResult {
    let payloads = [
        "'; DROP TABLE items; --",
        "' OR '1'='1",
        "\" UNION SELECT 1, 2, 3 --",
        "a%b_c\\d'\"",
    ];

    let schema = TableTy {
        cols: vec![
            col("id", ScalarTy::Int, &[]),
            col("name", ScalarTy::Text, &[]),
        ],
        ..TableTy::default()
    };
    let rows = vec![
        vec![Val::Int(BigInt::from(1)), Val::Text("alice".to_string())],
        vec![
            Val::Int(BigInt::from(2)),
            Val::Text("'; DROP TABLE items; --".to_string()),
        ],
        vec![
            Val::Int(BigInt::from(3)),
            Val::Text("' OR '1'='1".to_string()),
        ],
        vec![
            Val::Int(BigInt::from(4)),
            Val::Text("a%b_c\\d'\"".to_string()),
        ],
    ];
    let stored = vec![StoredTable {
        db: "Analytics".to_string(),
        table_name: "items".to_string(),
        schema: schema.clone(),
        rows: rows.clone(),
    }];

    let mut sqlite = SqliteDriver::open_in_memory()?;
    load_tables_into_sqlite(&mut sqlite, &stored, &[("items", "id")])?;

    let (pg_port, pg_srv) = spawn_pg_pushdown_server()?;
    let DbUri::Postgres(pg_uri) = DbUri::parse(&format!(
        "postgres://dana@127.0.0.1:{pg_port}/app?sslmode=disable"
    ))?
    else {
        return Err("expected postgres uri".into());
    };
    let mut pg = PostgresDriver::connect(&pg_uri)?;
    load_tables_into_pg_mock(&mut pg, &stored, &[("items", "id")])?;

    for payload in payloads {
        // Test BOTH literal filter AND OuterVar filter + ContainsText filter!
        let plan = Plan::Filter {
            input: Box::new(db_source("items", schema.clone())),
            pred: RowExpr::Prim {
                op: PrimOp::OrBool,
                args: vec![
                    RowExpr::Prim {
                        op: PrimOp::Eq,
                        args: vec![
                            RowExpr::Col("name".to_string()),
                            RowExpr::OuterVar("user_input".to_string()),
                        ],
                    },
                    RowExpr::Prim {
                        op: PrimOp::ContainsText,
                        args: vec![
                            RowExpr::Col("name".to_string()),
                            RowExpr::Lit(Literal::Text(payload.to_string())),
                        ],
                    },
                ],
            },
        };
        let outer_vars = vec![(
            "user_input".to_string(),
            LTy::public(Ty::Text),
            Val::Text(payload.to_string()),
        )];
        let prog = wrap_core_program(&plan, &outer_vars, false);
        check_program(&prog)?;

        let world = World {
            runtime_allow_export: TagSet::of_list(vec!["pii".to_string(), "ferpa".to_string()]),
            real_db_tables: stored.clone(),
            ..World::default()
        };
        let oracle_rep = run_program(50_000, &prog, world.clone())
            .map_err(|e| format!("oracle failed: {}", e.message))?;
        assert_eq!(oracle_rep.status, ExitStatus::Ok);

        for (dialect, conn) in [
            (SqlDialect::Sqlite, &mut sqlite as &mut dyn DbConnection),
            (SqlDialect::Postgres, &mut pg as &mut dyn DbConnection),
        ] {
            let SplitPlan::FullyPushed(q) =
                split_core_plan_pushdown(&plan, &prog, "Analytics", dialect, None)
            else {
                return Err(format!("expected FullyPushed for injection test on {dialect}").into());
            };
            // SQL text MUST NEVER contain interpolated payload characters!
            assert!(
                !q.sql.contains("DROP TABLE") && !q.sql.contains("OR '1'='1"),
                "SQL injection payload leaked into SQL text on {dialect}: {}",
                q.sql
            );
            let params = q.resolve_params(
                |v| {
                    if v == "user_input" {
                        Some(Val::Text(payload.to_string()))
                    } else {
                        None
                    }
                },
                |_| None,
            )?;
            let vm_tbl = conn.query_batches(&q.sql, &params, &q.out_schema, BATCH_SIZE)?;
            let rendered = render_core_table_text(&vm_tbl.into_table_val());
            assert_eq!(rendered, oracle_rep.stdout[0]);
        }

        // Confirm `items` table is still completely intact with all 4 rows!
        let check_sq = sqlite.query_rows(
            "SELECT \"id\", \"name\" FROM \"items\" ORDER BY \"id\"",
            &[],
            &schema,
        )?;
        assert_eq!(check_sq.rows.len(), 4);
        let check_pg = pg.query_rows(
            "SELECT \"id\", \"name\" FROM \"items\" ORDER BY \"id\"",
            &[],
            &schema,
        )?;
        assert_eq!(check_pg.rows.len(), 4);
    }

    drop(pg);
    let _ = pg_srv.join();
    Ok(())
}

// ===========================================================================
// 3. Explainer & Sensitivity Provenance on `examples/enrollment-report.dana`
// ===========================================================================

fn find_first_exec_plan(expr: &ExecExpr) -> Option<&ExecPlan> {
    match expr {
        ExecExpr::Rel(p) => Some(p),
        ExecExpr::LetE { bound, body, .. }
        | ExecExpr::Join {
            rhs: bound, body, ..
        } => find_first_exec_plan(bound).or_else(|| find_first_exec_plan(body)),
        ExecExpr::IfE {
            cond,
            then_br,
            else_br,
        } => find_first_exec_plan(cond)
            .or_else(|| find_first_exec_plan(then_br))
            .or_else(|| find_first_exec_plan(else_br)),
        ExecExpr::Call { args, .. }
        | ExecExpr::Tuple(args)
        | ExecExpr::Prim { args, .. }
        | ExecExpr::Host { args, .. } => args.iter().find_map(find_first_exec_plan),
        _ => None,
    }
}

#[test]
fn explain_enrollment_report_sqlite_and_postgres() -> TestResult {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let policy_path = root.join("examples/dana.policy");
    let script_path = root.join("examples/enrollment-report.dana");
    let policy_src = fs::read_to_string(&policy_path)?;

    let mut sm = SourceMap::new();
    let pfid = sm.add_file(policy_path.display().to_string(), policy_src.clone());
    let policy = parse_policy(pfid, &policy_src)
        .map_err(|d| format!("parse policy:\n{}", render_diagnostic(&d, &sm)))?;
    let resolved = resolve_path(&script_path, Some(policy), &mut sm).map_err(|ds| {
        ds.iter()
            .map(|d| render_diagnostic(d, &sm))
            .collect::<String>()
    })?;
    let checked = check_resolved(&resolved, &sm).map_err(|ds| {
        ds.iter()
            .map(|d| render_diagnostic(d, &sm))
            .collect::<String>()
    })?;
    let lowered = lower_program(checked)
        .map_err(|d| format!("lower failed:\n{}", render_diagnostic(&d, &sm)))?;

    let metrics_fn = lowered
        .exec
        .find_fun("program_term_metrics")
        .ok_or("missing program_term_metrics")?;
    let raw_plan =
        find_first_exec_plan(&metrics_fn.body).ok_or("missing ExecPlan in program_term_metrics")?;

    // Bind `students` -> `SourceDB(Student)` and `enrollments` -> `SourceDB(CourseEnrollment)`
    // just as `main` invokes `program_term_metrics(db.table(Student), db.table(CourseEnrollment))`.
    let student_schema = lowered
        .exec
        .find_schema("Student")
        .ok_or("missing Student schema")?
        .decl
        .schema
        .clone();
    let enroll_schema = lowered
        .exec
        .find_schema("CourseEnrollment")
        .ok_or("missing CourseEnrollment schema")?
        .decl
        .schema
        .clone();

    let mut bindings = HashMap::new();
    bindings.insert(
        "students".to_string(),
        ExecPlan::SourceDB {
            cap: Box::new(ExecExpr::Var("db".to_string())),
            table_name: "Student".to_string(),
            schema: student_schema,
        },
    );
    bindings.insert(
        "enrollments".to_string(),
        ExecPlan::SourceDB {
            cap: Box::new(ExecExpr::Var("db".to_string())),
            table_name: "CourseEnrollment".to_string(),
            schema: enroll_schema,
        },
    );
    let bound_plan = bind_exec_plan_sources(raw_plan, &bindings);

    for dialect in [SqlDialect::Sqlite, SqlDialect::Postgres] {
        let explained =
            explain_exec_plan_with_pushdown(&bound_plan, &lowered.exec, "Seminary", dialect, None);
        assert!(
            explained.contains("[LOGICAL PLAN]") && explained.contains("[OPTIMIZED PLAN]"),
            "missing plan trees for {dialect}:\n{explained}"
        );
        assert!(
            explained.contains(&format!("[SQL PUSHDOWN -> {dialect}]")),
            "missing SQL pushdown header for {dialect}:\n{explained}"
        );
        assert!(
            explained.contains("\"Student\"")
                && explained.contains("\"CourseEnrollment\"")
                && explained.contains("INNER JOIN"),
            "expected Student INNER JOIN CourseEnrollment pushdown on {dialect}:\n{explained}"
        );
        assert!(
            explained.contains("[PUSHDOWN BOUNDARY:")
                && explained.contains("suppress_small_groups"),
            "expected suppress_small_groups pushdown boundary on {dialect}:\n{explained}"
        );
        assert!(
            explained.contains("[LOCAL VM SUFFIX]")
                && explained.contains("SuppressSmallGroups")
                && explained.contains("Window"),
            "expected local VM suffix with SuppressSmallGroups & Window on {dialect}:\n{explained}"
        );
        assert!(
            explained.contains("[SENSITIVITY PROVENANCE]")
                && explained.contains("ENTER SourceDB(Student)")
                && explained.contains("ENTER SourceDB(CourseEnrollment)")
                && explained.contains("pii")
                && explained.contains("ferpa")
                && explained.contains("CLEAR SuppressSmallGroups")
                && explained.contains("OUTPUT: PUBLIC"),
            "expected full [pii]/[ferpa] provenance trace clearing to PUBLIC on {dialect}:\n{explained}"
        );
    }

    Ok(())
}

// ===========================================================================
// 4. Multi-Branch Pushdown Collection & Postgres vs SQLite Dialect Rules
// ===========================================================================

#[test]
fn collect_multi_branch_and_dialect_exactness_rules() -> TestResult {
    // 1. Cross-DB join: collect_core_plan_pushdowns extracts BOTH DB branches independently!
    let s1 = TableTy {
        cols: vec![
            col("id", ScalarTy::Int, &[]),
            col("email", ScalarTy::Text, &["pii"]),
        ],
        ..TableTy::default()
    };
    let s2 = TableTy {
        cols: vec![
            col("id", ScalarTy::Int, &[]),
            col("amt", ScalarTy::Decimal, &["ferpa"]),
        ],
        ..TableTy::default()
    };
    let cross_db_plan = Plan::Join {
        kind: JoinKind::InnerMany,
        left: Box::new(Plan::Filter {
            input: Box::new(Plan::SourceDB {
                cap: Box::new(Expr::Var("db_a".to_string())),
                table_name: "users".to_string(),
                schema: s1.clone(),
            }),
            pred: RowExpr::Prim {
                op: PrimOp::Gt,
                args: vec![
                    RowExpr::Col("id".to_string()),
                    RowExpr::Lit(Literal::int(0i64)),
                ],
            },
        }),
        right: Box::new(Plan::SourceDB {
            cap: Box::new(Expr::Var("db_b".to_string())),
            table_name: "orders".to_string(),
            schema: s2.clone(),
        }),
        on: JoinOn::SameKeys(vec!["id".to_string()]),
        suffixes: None,
    };
    let prog = Program {
        funs: vec![FunDecl {
            name: "main".to_string(),
            kind: FunKind::Function,
            is_pure: false,
            params: vec![
                (
                    "db_a".to_string(),
                    LTy::public(Ty::ReadDB("UsersDB".to_string())),
                ),
                (
                    "db_b".to_string(),
                    LTy::public(Ty::ReadDB("OrdersDB".to_string())),
                ),
            ],
            pc: TagSet::empty(),
            ret: LTy::public(Ty::Unit),
            body: Expr::Lit(Literal::Unit),
        }],
        ..Program::default()
    };

    let collected = collect_core_plan_pushdowns(&cross_db_plan, &prog, SqlDialect::Postgres, None);
    assert_eq!(collected.branches.len(), 2);
    assert_eq!(collected.branches[0].pushdown.db_name, "UsersDB");
    assert_eq!(collected.branches[1].pushdown.db_name, "OrdersDB");
    assert_ne!(
        collected.branches[0].placeholder_var,
        collected.branches[1].placeholder_var
    );

    // Also verify explain_core_plan_with_pushdown renders multi-branch pushdown + provenance.
    let explained = explain_core_plan_with_pushdown(
        &cross_db_plan,
        &prog,
        "UsersDB",
        SqlDialect::Postgres,
        None,
    );
    assert!(explained.contains("UsersDB") && explained.contains("OrdersDB"));
    assert!(explained.contains("[SENSITIVITY PROVENANCE]") && explained.contains("pii"));

    // 2. Dialect exactness rules:
    //    - Decimal comparison pushes on Postgres (`NUMERIC`), stays local on SQLite (`TEXT`).
    //    - Timestamp ordering pushes on Postgres (`TIMESTAMPTZ`), stays local on SQLite (`TEXT`).
    //    - Float comparison stays local on BOTH SQLite and Postgres (`NaN` / `-0.0`).
    let dec_ts_schema = TableTy {
        cols: vec![
            col("id", ScalarTy::Int, &[]),
            col("amt", ScalarTy::Decimal, &[]),
            col("ts", ScalarTy::Timestamp, &[]),
            col("f", ScalarTy::Float, &[]),
        ],
        ..TableTy::default()
    };
    let dec_plan = Plan::Filter {
        input: Box::new(db_source("t", dec_ts_schema.clone())),
        pred: RowExpr::Prim {
            op: PrimOp::Gt,
            args: vec![
                RowExpr::Col("amt".to_string()),
                RowExpr::Lit(Literal::decimal(10 * DEC_SCALE)),
            ],
        },
    };
    let float_plan = Plan::Filter {
        input: Box::new(db_source("t", dec_ts_schema.clone())),
        pred: RowExpr::Prim {
            op: PrimOp::Eq,
            args: vec![
                RowExpr::Col("f".to_string()),
                RowExpr::Lit(Literal::Float(Float64::from_f64(0.0))),
            ],
        },
    };
    let simple_prog = wrap_core_program(&dec_plan, &[], false);

    assert!(matches!(
        split_core_plan_pushdown(
            &dec_plan,
            &simple_prog,
            "Analytics",
            SqlDialect::Sqlite,
            None
        ),
        SplitPlan::Hybrid { .. }
    ));
    assert!(matches!(
        split_core_plan_pushdown(
            &dec_plan,
            &simple_prog,
            "Analytics",
            SqlDialect::Postgres,
            None
        ),
        SplitPlan::FullyPushed(_)
    ));
    assert!(matches!(
        split_core_plan_pushdown(
            &float_plan,
            &simple_prog,
            "Analytics",
            SqlDialect::Sqlite,
            None
        ),
        SplitPlan::Hybrid { .. }
    ));
    assert!(matches!(
        split_core_plan_pushdown(
            &float_plan,
            &simple_prog,
            "Analytics",
            SqlDialect::Postgres,
            None
        ),
        SplitPlan::Hybrid { .. }
    ));

    // Also exercise `collect_exec_plan_pushdowns` directly on an unchecked ExecPlan join.
    let exec_join = ExecPlan::Join {
        kind: JoinKind::InnerOne,
        left: Box::new(ExecPlan::SourceDB {
            cap: Box::new(ExecExpr::Var("db".to_string())),
            table_name: "a".to_string(),
            schema: s1,
        }),
        right: Box::new(ExecPlan::SourceDB {
            cap: Box::new(ExecExpr::Var("db".to_string())),
            table_name: "b".to_string(),
            schema: s2,
        }),
        on: JoinOn::SameKeys(vec!["id".to_string()]),
        suffixes: None,
    };
    let exec_collected =
        collect_exec_plan_pushdowns(&exec_join, &Default::default(), SqlDialect::Sqlite, None);
    assert_eq!(exec_collected.branches.len(), 2);
    assert!(
        exec_collected
            .boundary_reasons
            .iter()
            .any(|r| r.contains("cardinality"))
    );

    // Confirm `oid` module stays reachable for Postgres driver verification.
    assert_eq!(oid::NUMERIC, 1700);
    Ok(())
}

// ===========================================================================
// 5. Opt-in Live PostgreSQL Differential Test (`DANA_TEST_POSTGRES_URL`)
// ===========================================================================

#[test]
#[ignore = "requires live PostgreSQL server via DANA_TEST_POSTGRES_URL"]
fn live_postgres_differential_pushdown() -> TestResult {
    let url = std::env::var("DANA_TEST_POSTGRES_URL").map_err(
        |_| "DANA_TEST_POSTGRES_URL must be set to run live_postgres_differential_pushdown",
    )?;
    let DbUri::Postgres(pg_uri) = DbUri::parse(&url)? else {
        return Err("DANA_TEST_POSTGRES_URL must be a postgres:// URI".into());
    };
    let mut pg = PostgresDriver::connect(&pg_uri)?;
    let lock_pk = build_schema_lock("Analytics", SqlDialect::Postgres, true);

    let mut rng = SplitMix64::new(0x11CE_9057_69E5_3B01);
    let mut stats = PushdownStats::default();

    for idx in 0..60 {
        let case = generate_case(&mut rng, idx);
        check_program(&case.prog)?;
        let oracle_rep = run_program(200_000, &case.prog, case.world.clone())
            .map_err(|e| format!("oracle failed: {}", e.message))?;

        for st in &case.world.real_db_tables {
            let pk_col = if case.use_pk_lock && st.table_name != "dim_dup" {
                Some("id")
            } else {
                None
            };
            let cols_ddl: Vec<String> = st
                .schema
                .cols
                .iter()
                .map(|c| {
                    let q = quote_sql_ident(&c.name);
                    let base = match &c.ty {
                        ScalarTy::Option(inner) => inner.as_ref(),
                        other => other,
                    };
                    let pg_ty = match base {
                        ScalarTy::Bool => "BOOLEAN",
                        ScalarTy::Int => "BIGINT",
                        ScalarTy::Decimal => "NUMERIC",
                        ScalarTy::Float => "DOUBLE PRECISION",
                        ScalarTy::Text => "TEXT",
                        ScalarTy::Bytes => "BYTEA",
                        ScalarTy::Date => "DATE",
                        ScalarTy::Timestamp => "TIMESTAMPTZ",
                        ScalarTy::Duration => "INTERVAL",
                        _ => "TEXT",
                    };
                    let nn = if c.ty.is_option() { "" } else { " NOT NULL" };
                    let pk = if pk_col == Some(c.name.as_str()) {
                        " PRIMARY KEY"
                    } else {
                        ""
                    };
                    format!("{q} {pg_ty}{nn}{pk}")
                })
                .collect();
            let qtbl = quote_sql_ident(&st.table_name);
            pg.execute(&format!("DROP TABLE IF EXISTS {qtbl}"), &[])?;
            pg.execute(
                &format!("CREATE TABLE {qtbl} ({})", cols_ddl.join(", ")),
                &[],
            )?;
            if !st.rows.is_empty() {
                let phs: Vec<String> = (1..=st.schema.cols.len())
                    .map(|i| format!("${i}"))
                    .collect();
                let ins = format!("INSERT INTO {qtbl} VALUES ({})", phs.join(", "));
                for r in &st.rows {
                    let mut ps = Vec::with_capacity(r.len());
                    for cell in r {
                        ps.push(SqlParam::from_val(cell)?);
                    }
                    pg.execute(&ins, &ps)?;
                }
            }
        }

        let (opt_plan, _) = optimize_plan(&case.plan, &case.prog);
        let lock_opt = if case.use_pk_lock {
            Some(&lock_pk)
        } else {
            None
        };
        if let Some(pg_res) = execute_split_against_conn(
            &mut pg,
            &case,
            &opt_plan,
            SqlDialect::Postgres,
            lock_opt,
            &mut stats,
        )? {
            assert_matches_oracle("LivePostgres", idx, case.family, &oracle_rep, pg_res)?;
        }
    }

    assert!(stats.fully_pushed > 0 && stats.hybrid > 0);
    // Keep unused helper reference clean if compiled with all targets.
    let _ = (format_iso_date(0), format_iso_timestamp(0));
    Ok(())
}
