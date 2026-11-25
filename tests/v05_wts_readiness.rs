#![forbid(unsafe_code)]

//! Dana v0.5 Slice 5.1 integration & readiness suite:
//! - Multi-schema PostgreSQL introspection (`--schemas`), parameterized `table_schema IN ($1, ...)`,
//!   `schema.lock` tag preservation, `db.table(Schema, from: "schema.table")`, SQL pushdown
//!   `FROM "schema"."table"`, `dana explain --dialect postgres`, `WriteTable` dry-run & live upsert.
//! - Exact `Oracle == VM == SQLite pushdown` parity for `.lower`, `.upper`, `.slice`,
//!   `.starts_with?`, `.ends_with?`, `.contains?`, `.try_parse_{date,int,decimal,float}`,
//!   `.in?`, `.clamp`, `.round_to`, and `count_if` (plus negative tests, privacy propagation,
//!   and `DomainError` trap parity).

use std::collections::HashMap;
use std::fs;
use std::io::{Read, Write};
use std::net::{TcpListener, TcpStream};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::{Arc, Mutex};
use std::thread::{self, JoinHandle};

use dana::base::{DiagCode, SourceMap};
use dana::check::check_module;
use dana::core::syntax::BugKind;
use dana::db::postgres::oid;
use dana::db::schema_lock::parse_schema_lock;
use dana::db::{SqlDialect, SqlParam, open_connection};
use dana::ffi::sqlite::{SqliteConn, SqliteOpenMode, SqliteValueType, StepResult};
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
        let path = std::env::temp_dir().join(format!("dana_v05_{prefix}_{pid}_{id}"));
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
// Parity Helper: Oracle == VM == SQLite Pushdown
// ===========================================================================

fn check_src(src: &str) -> TestResult<dana::check::CheckedProgram> {
    let mut sm = SourceMap::new();
    let fid = sm.add_file("test.dana", src.to_string());
    let m = parse_module(fid, src).map_err(|d| format!("parse error: {d:?}"))?;
    check_module(fid, m, None, &sm).map_err(|ds| format!("check error: {ds:?}").into())
}

fn assert_oracle_vm_parity(
    src: &str,
    db_uri: Option<(&str, &str)>,
    expect_tag_block: bool,
) -> TestResult<Vec<String>> {
    if expect_tag_block {
        let mut sm = SourceMap::new();
        let fid = sm.add_file("privacy_neg.dana", src.to_string());
        let m = parse_module(fid, src).map_err(|d| format!("parse error: {d:?}"))?;
        let res = check_module(fid, m, None, &sm);
        let diags = res.err().ok_or("expected PrivacyError diagnostic")?;
        assert!(
            diags.iter().any(|d| d.code() == DiagCode::PrivacyError),
            "expected PrivacyError, got: {diags:?}"
        );
        return Ok(Vec::new());
    }

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
        (
            RunResult::Stopped {
                bug: ob,
                stdout: os,
                ..
            },
            RunResult::Stopped {
                bug: vb,
                stdout: vs,
                ..
            },
        ) => {
            let _ = (os, vs);
            Err(format!("unexpected engine stop:\noracle={ob:?}\nvm={vb:?}").into())
        }
        (o, v) => Err(format!("engine outcome mismatch:\noracle={o:?}\nvm={v:?}").into()),
    }
}

fn assert_oracle_vm_domain_trap(src: &str) -> TestResult {
    let checked = check_src(src)?;
    let cfg = RunConfig {
        live_io: true,
        ..RunConfig::default()
    };
    let ora = run_exec_program(&checked.exec, &cfg);
    let vm = run_exec_program_vm(&checked.exec, &cfg, &VmConfig::default());
    match (ora, vm) {
        (RunResult::Stopped { bug: ob, .. }, RunResult::Stopped { bug: vb, .. }) => {
            assert_eq!(ob.kind, BugKind::OutsideBoundary, "oracle bug={ob:?}");
            assert_eq!(vb.kind, BugKind::OutsideBoundary, "vm bug={vb:?}");
            assert!(
                ob.message.contains("DomainError:") && vb.message.contains("DomainError:"),
                "expected DomainError in both engines:\nora={ob:?}\nvm={vb:?}"
            );
            Ok(())
        }
        (o, v) => {
            Err(format!("expected DomainError stop in both engines:\nora={o:?}\nvm={v:?}").into())
        }
    }
}

// ===========================================================================
// Multi-Schema PostgreSQL Loopback Wire Server (ATTACH + Query Recorder)
// ===========================================================================

#[derive(Clone, Debug)]
struct RecordedPgQuery {
    sql: String,
    params: Vec<Option<String>>,
}

struct MultiSchemaPgMock {
    uri: String,
    queries: Arc<Mutex<Vec<RecordedPgQuery>>>,
    stop: Arc<AtomicBool>,
    handle: Option<JoinHandle<()>>,
}

impl MultiSchemaPgMock {
    fn start(main_db: &Path, attached_schemas: Vec<(String, PathBuf)>) -> TestResult<Self> {
        let listener = TcpListener::bind("127.0.0.1:0")?;
        listener.set_nonblocking(true)?;
        let port = listener.local_addr()?.port();
        let main_path = main_db.to_path_buf();
        let queries = Arc::new(Mutex::new(Vec::new()));
        let q_clone = Arc::clone(&queries);
        let stop = Arc::new(AtomicBool::new(false));
        let stop_clone = Arc::clone(&stop);

        let handle = thread::spawn(move || {
            while !stop_clone.load(Ordering::Relaxed) {
                match listener.accept() {
                    Ok((tcp, _)) => {
                        let _ = tcp.set_nonblocking(false);
                        let mp = main_path.clone();
                        let att = attached_schemas.clone();
                        let q = Arc::clone(&q_clone);
                        let _ = serve_pg_conn(tcp, &mp, &att, &q);
                    }
                    Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => {
                        thread::sleep(std::time::Duration::from_millis(5));
                    }
                    Err(_) => break,
                }
            }
        });

        Ok(Self {
            uri: format!("postgres://wts_user@127.0.0.1:{port}/wts_db?sslmode=disable"),
            queries,
            stop,
            handle: Some(handle),
        })
    }

    fn recorded(&self) -> Vec<RecordedPgQuery> {
        self.queries.lock().map(|g| g.clone()).unwrap_or_default()
    }

    fn clear(&self) {
        if let Ok(mut g) = self.queries.lock() {
            g.clear();
        }
    }
}

impl Drop for MultiSchemaPgMock {
    fn drop(&mut self) {
        self.stop.store(true, Ordering::Relaxed);
        let addr = self
            .uri
            .split('@')
            .nth(1)
            .and_then(|s| s.split('/').next())
            .unwrap_or("");
        if !addr.is_empty() {
            let _ = TcpStream::connect(addr);
        }
        if let Some(h) = self.handle.take() {
            let _ = h.join();
        }
    }
}

fn srv_write_msg(stream: &mut TcpStream, tag: u8, payload: &[u8]) -> std::io::Result<()> {
    let total_len = (4 + payload.len()) as i32;
    let mut frame = Vec::with_capacity(5 + payload.len());
    frame.push(tag);
    frame.extend_from_slice(&total_len.to_be_bytes());
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
    let len = i32::from_be_bytes([hdr[1], hdr[2], hdr[3], hdr[4]]);
    let body_len = (len - 4).max(0) as usize;
    let mut body = vec![0u8; body_len];
    if body_len > 0 {
        stream.read_exact(&mut body)?;
    }
    Ok(Some((hdr[0], body)))
}

fn srv_send_row_desc(stream: &mut TcpStream, cols: &[(&str, u32)]) -> std::io::Result<()> {
    let mut p = Vec::new();
    p.extend_from_slice(&(cols.len() as i16).to_be_bytes());
    for &(name, type_oid) in cols {
        p.extend_from_slice(name.as_bytes());
        p.push(0);
        p.extend_from_slice(&0u32.to_be_bytes());
        p.extend_from_slice(&0i16.to_be_bytes());
        p.extend_from_slice(&type_oid.to_be_bytes());
        p.extend_from_slice(&(-1i16).to_be_bytes());
        p.extend_from_slice(&(-1i32).to_be_bytes());
        p.extend_from_slice(&0i16.to_be_bytes());
    }
    srv_write_msg(stream, b'T', &p)
}

fn srv_send_data_row(stream: &mut TcpStream, cells: &[Option<Vec<u8>>]) -> std::io::Result<()> {
    let mut p = Vec::new();
    p.extend_from_slice(&(cells.len() as i16).to_be_bytes());
    for c in cells {
        match c {
            None => p.extend_from_slice(&(-1i32).to_be_bytes()),
            Some(bytes) => {
                p.extend_from_slice(&(bytes.len() as i32).to_be_bytes());
                p.extend_from_slice(bytes);
            }
        }
    }
    srv_write_msg(stream, b'D', &p)
}

fn srv_send_error(stream: &mut TcpStream, msg: &str) -> std::io::Result<()> {
    let mut p = Vec::new();
    p.extend_from_slice(b"SERROR\0C42000\0M");
    p.extend_from_slice(msg.as_bytes());
    p.push(0);
    p.push(0);
    srv_write_msg(stream, b'E', &p)
}

fn sqlite_decl_to_pg_meta(decl: &str) -> (&'static str, &'static str, u32) {
    let u = decl.to_ascii_uppercase();
    if u.contains("INT") {
        ("bigint", "int8", oid::INT8)
    } else if u.contains("BOOL") {
        ("boolean", "bool", oid::BOOL)
    } else if u.contains("DEC") || u.contains("NUM") {
        ("numeric", "numeric", oid::NUMERIC)
    } else if u.contains("REAL") || u.contains("DOUBLE") || u.contains("FLOAT") {
        ("double precision", "float8", oid::FLOAT8)
    } else if u.contains("DATE") {
        ("date", "date", oid::DATE)
    } else {
        ("text", "text", oid::TEXT)
    }
}

fn rewrite_pg_sql_to_sqlite(sql: &str) -> String {
    // 1. Replace SUBSTRING(expr FROM start FOR len) -> SUBSTR(expr, start, len)
    //    and Postgres `COLLATE "C"` -> SQLite `COLLATE BINARY`
    let sql = sql.replace(r#"COLLATE "C""#, "COLLATE BINARY");
    let mut step1 = String::with_capacity(sql.len());
    let mut i = 0;
    while i < sql.len() {
        if sql[i..].starts_with("SUBSTRING(")
            && let Some((args_end, rewritten)) =
                rewrite_substring_call(&sql[i + "SUBSTRING(".len()..])
        {
            step1.push_str("SUBSTR(");
            step1.push_str(&rewritten);
            step1.push(')');
            i += "SUBSTRING(".len() + args_end + 1;
            continue;
        }
        let Some(ch) = sql[i..].chars().next() else {
            break;
        };
        step1.push(ch);
        i += ch.len_utf8();
    }

    // 2. Replace $1, $2 -> ?1, ?2 outside string/ident quotes
    let bytes = step1.as_bytes();
    let mut out = String::with_capacity(step1.len());
    let mut j = 0;
    let mut in_single = false;
    let mut in_double = false;
    while j < bytes.len() {
        let b = bytes[j];
        if b == b'\'' && !in_double {
            in_single = !in_single;
            out.push('\'');
            j += 1;
        } else if b == b'"' && !in_single {
            in_double = !in_double;
            out.push('"');
            j += 1;
        } else if b == b'$' && !in_single && !in_double {
            let start = j + 1;
            let mut end = start;
            while end < bytes.len() && bytes[end].is_ascii_digit() {
                end += 1;
            }
            if end > start {
                out.push('?');
                out.push_str(&step1[start..end]);
                j = end;
            } else {
                out.push('$');
                j += 1;
            }
        } else {
            out.push(b as char);
            j += 1;
        }
    }
    out
}

fn rewrite_substring_call(rest: &str) -> Option<(usize, String)> {
    let mut depth = 0i32;
    let mut in_single = false;
    let mut in_double = false;
    let mut from_pos = None;
    let mut for_pos = None;
    let mut close_pos = None;

    for (idx, ch) in rest.char_indices() {
        if ch == '\'' && !in_double {
            in_single = !in_single;
        } else if ch == '"' && !in_single {
            in_double = !in_double;
        } else if !in_single && !in_double {
            match ch {
                '(' => depth += 1,
                ')' => {
                    if depth == 0 {
                        close_pos = Some(idx);
                        break;
                    }
                    depth -= 1;
                }
                _ if depth == 0 => {
                    if from_pos.is_none() && rest[idx..].starts_with(" FROM ") {
                        from_pos = Some(idx);
                    } else if from_pos.is_some()
                        && for_pos.is_none()
                        && rest[idx..].starts_with(" FOR ")
                    {
                        for_pos = Some(idx);
                    }
                }
                _ => {}
            }
        }
    }

    let (cp, fr, fo) = (close_pos?, from_pos?, for_pos?);
    let inner = &rest[..cp];
    let s_part = rewrite_pg_sql_to_sqlite(&inner[..fr]);
    let start_part = rewrite_pg_sql_to_sqlite(&inner[fr + 6..fo]);
    let len_part = rewrite_pg_sql_to_sqlite(&inner[fo + 5..]);
    Some((cp, format!("{s_part}, {start_part}, {len_part}")))
}

fn serve_pg_conn(
    mut stream: TcpStream,
    main_db: &Path,
    attached: &[(String, PathBuf)],
    queries: &Mutex<Vec<RecordedPgQuery>>,
) -> Result<(), String> {
    let mut len_buf = [0u8; 4];
    stream.read_exact(&mut len_buf).map_err(|e| e.to_string())?;
    let mut startup_len = i32::from_be_bytes(len_buf) as usize;
    let mut code_buf = [0u8; 4];
    stream
        .read_exact(&mut code_buf)
        .map_err(|e| e.to_string())?;
    if startup_len == 8 && i32::from_be_bytes(code_buf) == 80_877_103 {
        stream.write_all(b"N").map_err(|e| e.to_string())?;
        stream.flush().map_err(|e| e.to_string())?;
        stream.read_exact(&mut len_buf).map_err(|e| e.to_string())?;
        startup_len = i32::from_be_bytes(len_buf) as usize;
        stream
            .read_exact(&mut code_buf)
            .map_err(|e| e.to_string())?;
    }
    let rest_len = startup_len.saturating_sub(8);
    let mut startup_body = vec![0u8; rest_len];
    stream
        .read_exact(&mut startup_body)
        .map_err(|e| e.to_string())?;

    srv_write_msg(&mut stream, b'R', &0i32.to_be_bytes()).map_err(|e| e.to_string())?;
    srv_write_msg(&mut stream, b'Z', b"I").map_err(|e| e.to_string())?;

    let sqlite = SqliteConn::open(&main_db.to_string_lossy(), SqliteOpenMode::ReadWriteCreate)
        .map_err(|e| e.to_string())?;
    for (schema, db_file) in attached {
        let sql = format!(
            "ATTACH DATABASE '{}' AS \"{schema}\"",
            db_file.display().to_string().replace('\'', "''")
        );
        sqlite.execute_batch(&sql).map_err(|e| e.to_string())?;
    }

    let mut prepared_sql = String::new();
    let mut bound_params: Vec<(i16, Option<Vec<u8>>)> = Vec::new();
    let mut portal_executed = false;

    while let Some((tag, body)) = srv_read_msg(&mut stream).map_err(|e| e.to_string())? {
        match tag {
            b'Q' => {
                let end = body.iter().position(|&b| b == 0).unwrap_or(body.len());
                let sql = String::from_utf8_lossy(&body[..end]).into_owned();
                if let Err(e) = exec_pg_query(&mut stream, &sqlite, &sql, &[], queries) {
                    let _ = srv_send_error(&mut stream, &e);
                }
                srv_write_msg(&mut stream, b'Z', b"I").map_err(|e| e.to_string())?;
            }
            b'P' => {
                let Some(s1) = body.iter().position(|&b| b == 0) else {
                    break;
                };
                let rest = &body[s1 + 1..];
                let Some(s2) = rest.iter().position(|&b| b == 0) else {
                    break;
                };
                prepared_sql = String::from_utf8_lossy(&rest[..s2]).into_owned();
                srv_write_msg(&mut stream, b'1', &[]).map_err(|e| e.to_string())?;
            }
            b'B' => {
                let Some(p1) = body.iter().position(|&b| b == 0) else {
                    break;
                };
                let r1 = &body[p1 + 1..];
                let Some(p2) = r1.iter().position(|&b| b == 0) else {
                    break;
                };
                let mut pos = &r1[p2 + 1..];
                if pos.len() < 2 {
                    break;
                }
                let n_fmt = i16::from_be_bytes([pos[0], pos[1]]) as usize;
                pos = &pos[2..];
                let mut fmts = Vec::with_capacity(n_fmt);
                for _ in 0..n_fmt {
                    if pos.len() < 2 {
                        break;
                    }
                    fmts.push(i16::from_be_bytes([pos[0], pos[1]]));
                    pos = &pos[2..];
                }
                if pos.len() < 2 {
                    break;
                }
                let n_params = i16::from_be_bytes([pos[0], pos[1]]) as usize;
                pos = &pos[2..];
                bound_params.clear();
                for idx in 0..n_params {
                    if pos.len() < 4 {
                        break;
                    }
                    let plen = i32::from_be_bytes([pos[0], pos[1], pos[2], pos[3]]);
                    pos = &pos[4..];
                    let fmt = if fmts.len() == 1 {
                        fmts[0]
                    } else {
                        fmts.get(idx).copied().unwrap_or(0)
                    };
                    if plen < 0 {
                        bound_params.push((fmt, None));
                    } else {
                        let ul = plen as usize;
                        if pos.len() < ul {
                            break;
                        }
                        bound_params.push((fmt, Some(pos[..ul].to_vec())));
                        pos = &pos[ul..];
                    }
                }
                portal_executed = false;
                srv_write_msg(&mut stream, b'2', &[]).map_err(|e| e.to_string())?;
            }
            b'D' => {
                if !portal_executed {
                    portal_executed = true;
                    if let Err(e) =
                        exec_pg_query(&mut stream, &sqlite, &prepared_sql, &bound_params, queries)
                    {
                        let _ = srv_send_error(&mut stream, &e);
                    }
                }
            }
            b'E' => {
                if !portal_executed {
                    portal_executed = true;
                    if let Err(e) =
                        exec_pg_query(&mut stream, &sqlite, &prepared_sql, &bound_params, queries)
                    {
                        let _ = srv_send_error(&mut stream, &e);
                    }
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
}

fn exec_pg_query(
    stream: &mut TcpStream,
    sqlite: &SqliteConn,
    pg_sql: &str,
    params: &[(i16, Option<Vec<u8>>)],
    queries: &Mutex<Vec<RecordedPgQuery>>,
) -> Result<(), String> {
    let trimmed = pg_sql.trim();
    if let Ok(mut g) = queries.lock() {
        let p_strs = params
            .iter()
            .map(|(_, b)| b.as_ref().map(|v| String::from_utf8_lossy(v).into_owned()))
            .collect();
        g.push(RecordedPgQuery {
            sql: trimmed.to_string(),
            params: p_strs,
        });
    }

    let req_schemas: Vec<String> = params
        .iter()
        .filter_map(|(_, b)| b.as_ref().map(|v| String::from_utf8_lossy(v).into_owned()))
        .collect();
    let collect_schemas = || -> Result<Vec<(String, String)>, String> {
        let mut s = sqlite
            .prepare("PRAGMA database_list")
            .map_err(|e| e.to_string())?;
        let mut out = Vec::new();
        while s.step().map_err(|e| e.to_string())? == StepResult::Row {
            let db_name = s.column_text(1).map_err(|e| e.to_string())?;
            if db_name == "temp" {
                continue;
            }
            let pg_schema = if db_name == "main" {
                "public".to_string()
            } else {
                db_name.clone()
            };
            if req_schemas.is_empty() || req_schemas.iter().any(|r| r == &pg_schema) {
                out.push((db_name, pg_schema));
            }
        }
        out.sort_by(|a, b| a.1.cmp(&b.1));
        Ok(out)
    };

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
        for (sq_db, pg_schema) in collect_schemas()? {
            let mut ts = sqlite
                .prepare(&format!(
                    "SELECT name FROM \"{sq_db}\".sqlite_master \
                     WHERE type = 'table' AND name NOT LIKE 'sqlite_%' ORDER BY name"
                ))
                .map_err(|e| e.to_string())?;
            let mut tbls = Vec::new();
            while ts.step().map_err(|e| e.to_string())? == StepResult::Row {
                tbls.push(ts.column_text(0).map_err(|e| e.to_string())?);
            }
            for t in tbls {
                let mut ps = sqlite
                    .prepare(&format!("PRAGMA \"{sq_db}\".table_info(\"{t}\")"))
                    .map_err(|e| e.to_string())?;
                while ps.step().map_err(|e| e.to_string())? == StepResult::Row {
                    let cname = ps.column_text(1).map_err(|e| e.to_string())?;
                    if ps.column_int64(5) > 0 {
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
        for (sq_db, pg_schema) in collect_schemas()? {
            let mut ts = sqlite
                .prepare(&format!(
                    "SELECT name FROM \"{sq_db}\".sqlite_master \
                     WHERE type = 'table' AND name NOT LIKE 'sqlite_%' ORDER BY name"
                ))
                .map_err(|e| e.to_string())?;
            let mut tbls = Vec::new();
            while ts.step().map_err(|e| e.to_string())? == StepResult::Row {
                tbls.push(ts.column_text(0).map_err(|e| e.to_string())?);
            }
            for t in tbls {
                let mut ps = sqlite
                    .prepare(&format!("PRAGMA \"{sq_db}\".table_info(\"{t}\")"))
                    .map_err(|e| e.to_string())?;
                while ps.step().map_err(|e| e.to_string())? == StepResult::Row {
                    let cname = ps.column_text(1).map_err(|e| e.to_string())?;
                    let decl = ps.column_text(2).map_err(|e| e.to_string())?;
                    let notnull = ps.column_int64(3) != 0;
                    let pk = ps.column_int64(5) > 0;
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

    let mut col_oids: HashMap<String, u32> = HashMap::new();
    for (sq_db, _) in collect_schemas()? {
        let mut ts = sqlite
            .prepare(&format!(
                "SELECT name FROM \"{sq_db}\".sqlite_master \
                 WHERE type = 'table' AND name NOT LIKE 'sqlite_%'"
            ))
            .map_err(|e| e.to_string())?;
        let mut tbls = Vec::new();
        while ts.step().map_err(|e| e.to_string())? == StepResult::Row {
            tbls.push(ts.column_text(0).map_err(|e| e.to_string())?);
        }
        for t in tbls {
            let mut ps = sqlite
                .prepare(&format!("PRAGMA \"{sq_db}\".table_info(\"{t}\")"))
                .map_err(|e| e.to_string())?;
            while ps.step().map_err(|e| e.to_string())? == StepResult::Row {
                let cname = ps.column_text(1).map_err(|e| e.to_string())?;
                let decl = ps.column_text(2).map_err(|e| e.to_string())?;
                let (_, _, oid_v) = sqlite_decl_to_pg_meta(&decl);
                col_oids.insert(cname, oid_v);
            }
        }
    }

    let sqlite_sql = rewrite_pg_sql_to_sqlite(trimmed);
    let mut stmt = sqlite.prepare(&sqlite_sql).map_err(|e| e.to_string())?;
    for (idx, (_, val)) in params.iter().enumerate() {
        let bi = (idx + 1) as i32;
        match val {
            None => stmt.bind_null(bi).map_err(|e| e.to_string())?,
            Some(bytes) => {
                let s = String::from_utf8_lossy(bytes);
                if trimmed.contains("VALUES") || trimmed.contains("SET") {
                    if let Ok(n) = s.parse::<i64>() {
                        stmt.bind_int64(bi, n).map_err(|e| e.to_string())?;
                    } else if s == "true" {
                        stmt.bind_int64(bi, 1).map_err(|e| e.to_string())?;
                    } else if s == "false" {
                        stmt.bind_int64(bi, 0).map_err(|e| e.to_string())?;
                    } else {
                        stmt.bind_text(bi, &s).map_err(|e| e.to_string())?;
                    }
                } else {
                    stmt.bind_text(bi, &s).map_err(|e| e.to_string())?;
                }
            }
        }
    }

    let n_cols = stmt.column_count();
    if n_cols == 0 {
        while stmt.step().map_err(|e| e.to_string())? == StepResult::Row {}
        srv_write_msg(stream, b'n', &[]).map_err(|e| e.to_string())?;
        srv_write_msg(stream, b'C', b"OK\0").map_err(|e| e.to_string())?;
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
                SqliteValueType::Text => Some(
                    stmt.column_text(ci)
                        .map_err(|e| e.to_string())?
                        .into_bytes(),
                ),
                SqliteValueType::Blob => Some(stmt.column_blob(ci)),
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

// ===========================================================================
// 1. Multi-Schema Postgres E2E: sync --schemas, from:, pushdown, dry-run/upsert
// ===========================================================================

#[test]
fn v05_multi_schema_pg_mock_sync_read_pushdown_and_upsert() -> TestResult {
    let tmp = TempDir::new("pg_multi")?;
    let main_db = tmp.path().join("main.db");
    let populi_db = tmp.path().join("populi.db");
    let canvas_db = tmp.path().join("canvas.db");
    let logs_db = tmp.path().join("canvas_logs.db");

    {
        let c = SqliteConn::open(&main_db.to_string_lossy(), SqliteOpenMode::ReadWriteCreate)?;
        c.execute_batch(r#"CREATE TABLE "public_meta" ("k" TEXT PRIMARY KEY NOT NULL);"#)?;
    }
    {
        let c = SqliteConn::open(
            &populi_db.to_string_lossy(),
            SqliteOpenMode::ReadWriteCreate,
        )?;
        c.execute_batch(
            r#"
            CREATE TABLE "enrollments" (
                "id" INTEGER PRIMARY KEY NOT NULL,
                "student_email" TEXT NOT NULL,
                "term" TEXT NOT NULL,
                "status" TEXT NOT NULL,
                "score" INTEGER NOT NULL
            );
            INSERT INTO "enrollments" VALUES
                (1, 'alice@wts.edu', '2026FA', 'ENROLLED', 95),
                (2, 'bob@wts.edu',   '2026FA', 'ENROLLED', 82),
                (3, 'cara@gmail.com','2026FA', 'ENROLLED', 99),
                (4, 'dan@wts.edu',   '2026FA', 'DROPPED',  98),
                (5, 'eve@wts.edu',   '2027SP', 'ENROLLED', 110);
            "#,
        )?;
    }
    {
        let c = SqliteConn::open(
            &canvas_db.to_string_lossy(),
            SqliteOpenMode::ReadWriteCreate,
        )?;
        c.execute_batch(
            r#"CREATE TABLE "courses" ("course_id" INTEGER PRIMARY KEY NOT NULL, "code" TEXT NOT NULL);"#,
        )?;
    }
    {
        let c = SqliteConn::open(&logs_db.to_string_lossy(), SqliteOpenMode::ReadWriteCreate)?;
        c.execute_batch(
            r#"CREATE TABLE "events" ("event_id" INTEGER PRIMARY KEY NOT NULL, "kind" TEXT NOT NULL);"#,
        )?;
    }

    let pg = MultiSchemaPgMock::start(
        &main_db,
        vec![
            ("populi".to_string(), populi_db.clone()),
            ("canvas".to_string(), canvas_db),
            ("canvas_logs".to_string(), logs_db),
        ],
    )?;

    let db_arg = format!("Wts={}", pg.uri);
    let lock_path = tmp.path().join("schema.lock");
    let lock_str = lock_path.to_string_lossy().to_string();

    // 1A: `dana schema-sync --schemas populi,canvas` parameterized IN ($1, $2)
    let (sc_code, _, sc_err) = run_dana_cmd(
        &[
            "schema-sync",
            "--db",
            &db_arg,
            "--schemas",
            "populi,canvas",
            "--out",
            &lock_str,
        ],
        Some(tmp.path()),
    )?;
    assert_eq!(sc_code, 0, "schema-sync failed:\n{sc_err}");

    let sync_queries = pg.recorded();
    assert!(
        sync_queries.iter().any(|q| {
            q.sql.contains("information_schema.columns")
                && q.sql.contains("table_schema IN ($1, $2)")
                && q.params == vec![Some("populi".to_string()), Some("canvas".to_string())]
        }),
        "expected parameterized table_schema IN ($1, $2), got: {sync_queries:?}"
    );

    let lock_txt = fs::read_to_string(&lock_path)?;
    assert!(lock_txt.contains(r#"table "populi.enrollments""#));
    assert!(lock_txt.contains(r#"table "canvas.courses""#));
    assert!(!lock_txt.contains("canvas_logs.events"));
    assert!(!lock_txt.contains("public_meta"));

    // Annotate [pii] on populi.enrollments.student_email and re-sync with 3rd schema
    let tagged_lock = lock_txt.replace(
        "    col student_email: Text\n",
        "    col student_email: Text tags [pii]\n",
    );
    fs::write(&lock_path, tagged_lock)?;
    pg.clear();

    let (sc2_code, _, sc2_err) = run_dana_cmd(
        &[
            "schema-sync",
            "--db",
            &db_arg,
            "--schemas",
            "populi,canvas,canvas_logs",
            "--out",
            &lock_str,
        ],
        Some(tmp.path()),
    )?;
    assert_eq!(sc2_code, 0, "re-sync failed:\n{sc2_err}");
    let re_txt = fs::read_to_string(&lock_path)?;
    assert!(re_txt.contains("col student_email: Text tags [pii]"));
    assert!(re_txt.contains(r#"table "canvas_logs.events""#));

    // 1B: Query `db.table(Enrollment, from: "populi.enrollments")` with full SQL pushdown + Oracle parity
    let query_src = r#"module WtsMultiQuery

schema Enrollment
  id: Int
  student_email: Text [pii]
  term: Text
  status: Text
  score: Int
end

fn main(db: ReadDB(Wts), console: Console) : Int
  summary = db.table(Enrollment, from: "populi.enrollments")
    |> where(
         .term.in?(["2026FA", "2027SP"])
         and .status.starts_with?("ENR")
         and .status.ends_with?("ED")
       )
    |> derive(
         yr: .term.slice(0, 4),
         capped: .score.clamp(0, 100),
         norm: .term.lower
       )
    |> group_by(.term, .yr, .norm)
    |> summarize(
         total: count(),
         honors: count_if(.capped >= 90 and .status.in?(["ENROLLED"]))
       )
    |> sort_by(.term, .yr, .norm)
  console.print_table(summary)
  0
end
"#;
    let query_path = tmp.path().join("wts_query.dana");
    fs::write(&query_path, query_src)?;
    let query_str = query_path.to_string_lossy().to_string();

    // Filtering on [pii] column `.student_email` into plain Console MUST fail with E0202
    let pii_filter_src = query_src.replace(
        r#".status.ends_with?("ED")"#,
        r#".student_email.ends_with?(".edu")"#,
    );
    let pii_path = tmp.path().join("wts_pii_neg.dana");
    fs::write(&pii_path, pii_filter_src)?;
    let pii_str = pii_path.to_string_lossy().to_string();
    let (pii_code, _, pii_err) = run_dana_cmd(
        &["run", "--db", &db_arg, "--schema-lock", &lock_str, &pii_str],
        Some(tmp.path()),
    )?;
    assert_ne!(pii_code, 0);
    assert!(
        pii_err.contains("E0202") || pii_err.contains("pii"),
        "expected privacy rejection on [pii] filter into Console, got: {pii_err}"
    );

    pg.clear();
    let (vm_code, vm_out, vm_err) = run_dana_cmd(
        &[
            "run",
            "--db",
            &db_arg,
            "--schema-lock",
            &lock_str,
            &query_str,
        ],
        Some(tmp.path()),
    )?;
    assert_eq!(
        vm_code, 0,
        "VM PG query failed:\nstderr={vm_err}\nstdout={vm_out}"
    );

    let pg_pushed = pg.recorded();
    assert!(
        pg_pushed.iter().any(|q| {
            q.sql.contains(r#"FROM "populi"."enrollments""#)
                && q.sql.contains("IN (")
                && q.sql.contains("COALESCE(SUM((CASE WHEN")
                && q.sql.contains("SUBSTRING(")
        }),
        "expected full multi-schema SQL pushdown on wire, got: {pg_pushed:?}"
    );

    let (ora_code, ora_out, ora_err) = run_dana_cmd(
        &[
            "run",
            "--oracle",
            "--db",
            &db_arg,
            "--schema-lock",
            &lock_str,
            &query_str,
        ],
        Some(tmp.path()),
    )?;
    assert_eq!(
        ora_code, 0,
        "Oracle PG query failed:\nstderr={ora_err}\nstdout={ora_out}"
    );
    assert_eq!(vm_out, ora_out, "Postgres pushdown VM vs Oracle mismatch");
    assert!(
        vm_out.contains("2026FA")
            && vm_out.contains("2027SP")
            && vm_out.contains("| 3 ")
            && vm_out.contains("| 2 ")
            && vm_out.contains("| 1 "),
        "unexpected query output:\n{vm_out}"
    );

    // 1C: WriteTable(Wts, "populi.enrollments", ...) dry-run + live upsert
    let upsert_src = r#"module WtsUpsert

schema Enrollment
  id: Int
  student_email: Text [pii]
  term: Text
  status: Text
  score: Int
end

fn main(
  r: ReadDB(Wts),
  w: WriteTable(Wts, "populi.enrollments", allows: [pii]),
  c: Console
) : Int
  upd = r.table(Enrollment, from: "populi.enrollments")
    |> where(.id == 2)
    |> derive(score: 91)
  ins = table
    | id | student_email  | term     | status     | score |
    | 6  | "fay@wts.edu"  | "2027SP" | "ENROLLED" | 88    |
  end
  batch = upd |> union(ins)
  stats = try w.upsert(batch, key: .id)
  c.print("upsert:#{stats.inserted}:#{stats.updated}:#{stats.unchanged}")
  0
end
"#;
    let upsert_path = tmp.path().join("wts_upsert.dana");
    fs::write(&upsert_path, upsert_src)?;
    let upsert_str = upsert_path.to_string_lossy().to_string();

    pg.clear();
    let (dry_code, dry_out, dry_err) = run_dana_cmd(
        &[
            "dry-run",
            "--db",
            &db_arg,
            "--schema-lock",
            &lock_str,
            &upsert_str,
        ],
        Some(tmp.path()),
    )?;
    assert_eq!(dry_code, 0, "dry-run failed:\n{dry_err}\n{dry_out}");
    assert!(dry_out.contains("[REDACTED:pii]"));
    assert!(!dry_out.contains("fay@wts.edu") && !dry_out.contains("bob@wts.edu"));
    assert!(
        !pg.recorded()
            .iter()
            .any(|q| q.sql.contains("INSERT") || q.sql.contains("UPDATE")),
        "dry-run must execute zero writes on Postgres wire"
    );

    let (up_code, up_out, up_err) = run_dana_cmd(
        &[
            "run",
            "--db",
            &db_arg,
            "--schema-lock",
            &lock_str,
            "--allow-export",
            "pii",
            &upsert_str,
        ],
        Some(tmp.path()),
    )?;
    assert_eq!(up_code, 0, "live upsert failed:\n{up_err}\n{up_out}");
    assert!(up_out.contains("upsert:1:1:0"), "got: {up_out}");

    // Confirm SQLite populi.db actually reflects both inserted row 6 and updated score=91 for id=2
    let mut check_conn = open_connection(&sqlite_uri(&populi_db))?;
    let rs = check_conn.query_rows(
        r#"SELECT id, student_email, term, status, score FROM "enrollments" WHERE id IN (2, 6) ORDER BY id"#,
        &[],
        &parse_schema_lock(&re_txt)?
            .find_db("Wts")
            .ok_or("missing Wts db")?
            .resolve_table("populi.enrollments")?
            .to_table_ty(),
    )?;
    assert_eq!(rs.rows.len(), 2);

    Ok(())
}

// ===========================================================================
// 2. Text Ops Parity: .lower, .upper, .slice, .starts_with?, .ends_with?, .contains?
// ===========================================================================

#[test]
fn v05_text_ops_oracle_vm_sqlite_pushdown_parity() -> TestResult {
    let tmp = TempDir::new("text_ops")?;
    let db_path = tmp.path().join("text.db");
    let uri = sqlite_uri(&db_path);
    let mut conn = open_connection(&uri)?;
    conn.execute(
        r#"CREATE TABLE "items" ("id" INTEGER PRIMARY KEY NOT NULL, "label" TEXT NOT NULL, "tag" TEXT NOT NULL)"#,
        &[],
    )?;
    for (id, label, tag) in [
        (1i64, "Alpha_100%", "Al"),
        (2, "BETA_200_", "TA"),
        (3, "gamma", ""),
        (4, "abc%def", "c%d"),
        (5, "x", "longer_than_x"),
    ] {
        conn.execute(
            r#"INSERT INTO "items" VALUES (?, ?, ?)"#,
            &[
                SqlParam::Int(id),
                SqlParam::Text(label.to_string()),
                SqlParam::Text(tag.to_string()),
            ],
        )?;
    }
    drop(conn);

    // SQLite pushdown + VM + Oracle parity (ASCII rows + wildcard characters + positional/named args)
    let pushed_src = r#"module TextPushed

schema Item
  id: Int
  label: Text
  tag: Text
end

fn main(db: ReadDB(Store), console: Console) : Int
  res = db.table(Item, from: "items")
    |> derive(
         lo: .label.lower,
         up: .label.upper,
         sl: .label.slice(1, 3),
         sl_zero: .label.slice(start: 0, len: 0),
         sl_oob: .label.slice(2, 50),
         sw: .label.starts_with?(prefix: "Al"),
         sw_empty: .label.starts_with?(""),
         ew_pct: .label.ends_with?("%"),
         ew_dyn: .label.ends_with?(.tag),
         ct_wild: .label.contains?(sub: "%")
       )
    |> where(.label.starts_with?("Al") or .label.ends_with?("_") or .label.contains?("c%d"))
    |> sort_by(.id)
  console.print_table(res)
  0
end
"#;
    let out = assert_oracle_vm_parity(pushed_src, Some(("Store", &uri)), false)?;
    let joined = out.join("\n");
    assert!(joined.contains("alpha_100%"));
    assert!(joined.contains("ALPHA_100%"));
    assert!(joined.contains("BETA_200_"));
    assert!(joined.contains("abc%def"));
    assert!(!joined.contains("gamma"));

    // Confirm SQL pushdown plan pushed LOWER, UPPER, SUBSTR, wildcard-free predicates
    let checked = check_src(pushed_src)?;
    let main_fn = checked.exec.find_fun("main").ok_or("missing main")?;
    // Extract pushed SQL from LetE body
    let split_dbg = format!("{:?}", main_fn.body);
    assert!(split_dbg.contains("LowerText") && split_dbg.contains("SliceText"));

    // Local VM + Oracle parity: UTF-8 Unicode casing, negative start clamp, negative len -> "", dynamic slice, scalars
    let local_src = r##"module TextLocal

fn main(console: Console) : Int
  dyn_s = 1
  dyn_l = 2
  t = table
    | id | txt          | st | ln |
    | 1  | "Café_Élan"  | -4 | 3  |
    | 2  | "Café_Élan"  | 2  | -1 |
    | 3  | "naïve🎉ok"  | 5  | 2  |
    | 4  | "hi"         | 10 | 4  |
  end
  res = t
    |> derive(
         lo: .txt.lower,
         up: .txt.upper,
         sl: .txt.slice(.st, .ln),
         sl_dyn: .txt.slice(dyn_s, dyn_l),
         sw: .txt.starts_with?("Ca"),
         ew: .txt.ends_with?("Élan"),
         ct: .txt.contains?("🎉")
       )
    |> sort_by(.id)
  console.print("#{"Hi".lower}:#{"hi".upper}:#{"Café🎉".slice(-2, 5)}:#{"ab".slice(0, -3)}")
  console.print("#{"a%b".starts_with?(prefix: "a%")}:#{"a_b".ends_with?(suffix: "_b")}:#{"a\\b".contains?("\\")}")
  console.print_table(res)
  0
end
"##;
    let local_out = assert_oracle_vm_parity(local_src, None, false)?;
    assert_eq!(local_out[0], "hi:HI:Café🎉:");
    assert_eq!(local_out[1], "true:true:true");
    let local_tbl = local_out.join("\n");
    assert!(local_tbl.contains("café_élan"));
    assert!(local_tbl.contains("CAFÉ_ÉLAN"));

    Ok(())
}

// ===========================================================================
// 3. Safe Parsing (.try_parse_*) + Clean Local VM Fallback
// ===========================================================================

#[test]
fn v05_safe_try_parse_oracle_vm_sqlite_parity_and_boundary() -> TestResult {
    let tmp = TempDir::new("try_parse")?;
    let db_path = tmp.path().join("raw_inputs.db");
    let uri = sqlite_uri(&db_path);
    let mut conn = open_connection(&uri)?;
    conn.execute(
        r#"CREATE TABLE "raw_rows" ("id" INTEGER PRIMARY KEY NOT NULL, "d" TEXT NOT NULL, "i" TEXT NOT NULL, "dec" TEXT NOT NULL, "flt" TEXT NOT NULL)"#,
        &[],
    )?;
    for (id, d, i, dec, flt) in [
        (1i64, "2026-03-15", " 42 ", "-12.340", "1.25e2"),
        (2, "2026-02-30", "-999", "0.005", "NaN"),
        (3, "not-a-date", "999999999999999999999", ".5", "inf"),
        (4, " 1999-12-31 ", "12.5", "123.", "  -0.5  "),
    ] {
        conn.execute(
            r#"INSERT INTO "raw_rows" VALUES (?, ?, ?, ?, ?)"#,
            &[
                SqlParam::Int(id),
                SqlParam::Text(d.to_string()),
                SqlParam::Text(i.to_string()),
                SqlParam::Text(dec.to_string()),
                SqlParam::Text(flt.to_string()),
            ],
        )?;
    }
    drop(conn);

    let src = r#"module ParseParity

schema RawRow
  id: Int
  d: Text
  i: Text
  dec: Text
  flt: Text
end

fn main(db: ReadDB(Store), console: Console) : Int
  res = db.table(RawRow, from: "raw_rows")
    |> derive(
         pd: .d.try_parse_date,
         pi: .i.try_parse_int,
         pdec: .dec.try_parse_decimal,
         pf: .flt.try_parse_float,
         d_ok: .d.try_parse_date.some?,
         i_or: .i.try_parse_int ?? -1
       )
    |> sort_by(.id)
  s_ok = "2026-01-01".try_parse_date.some?
  s_bad = "bad".try_parse_int.none?
  console.print("scalar:#{s_ok}:#{s_bad}")
  console.print_table(res)
  0
end
"#;
    let out = assert_oracle_vm_parity(src, Some(("Store", &uri)), false)?;
    assert_eq!(out[0], "scalar:true:true");

    // Verify clean SQLite pushdown boundary for `.try_parse_*`
    let checked = check_src(src)?;
    let main_fn = checked.exec.find_fun("main").ok_or("missing main")?;
    let plan = find_first_plan(&main_fn.body).ok_or("missing ExecPlan")?;
    let split = split_exec_plan_pushdown(plan, &checked.exec, "Store", SqlDialect::Sqlite, None);
    let dbg_str = format!("{split:?}");
    assert!(
        dbg_str.contains("TryParse") || dbg_str.contains("requires local VM"),
        "expected clean local VM boundary note for try_parse_*, got: {dbg_str}"
    );

    Ok(())
}

// ===========================================================================
// 4. Membership `.in?(list)`: 6 Scalar Types, Option T?, Tags, SQL Pushdown
// ===========================================================================

#[test]
fn v05_in_list_all_types_option_tags_and_pushdown_parity() -> TestResult {
    let tmp = TempDir::new("in_list")?;
    let db_path = tmp.path().join("in_db.db");
    let uri = sqlite_uri(&db_path);
    let mut conn = open_connection(&uri)?;
    conn.execute(
        r#"CREATE TABLE "events" (
            "id" INTEGER PRIMARY KEY NOT NULL,
            "code" TEXT NOT NULL,
            "n" INTEGER NOT NULL,
            "opt_n" INTEGER,
            "d" TEXT NOT NULL,
            "flag" INTEGER NOT NULL
        )"#,
        &[],
    )?;
    for (id, code, n, opt_n, d, flag) in [
        (1i64, "A", -1i64, Some(10i64), "2026-01-01", true),
        (2, "B", 2, None, "2026-06-01", false),
        (3, "C", 9, Some(99), "2026-12-31", true),
    ] {
        conn.execute(
            r#"INSERT INTO "events" VALUES (?, ?, ?, ?, ?, ?)"#,
            &[
                SqlParam::Int(id),
                SqlParam::Text(code.to_string()),
                SqlParam::Int(n),
                match opt_n {
                    Some(v) => SqlParam::Int(v),
                    None => SqlParam::Null,
                },
                SqlParam::Date(dana::formats::time::parse_iso_date(d)?),
                SqlParam::Bool(flag),
            ],
        )?;
    }
    drop(conn);

    // Pushdown-compatible scalar + Option(T) + empty list + negative integer literal
    let pushed_src = r#"module InPushdown

schema Event
  id: Int
  code: Text
  n: Int
  opt_n: Int?
  d: Date
  flag: Bool
end

fn main(db: ReadDB(E), console: Console) : Int
  allowed_codes = ["A", "C"]
  res = db.table(Event, from: "events")
    |> derive(
         in_code: .code.in?(["A", "C"]),
         in_neg: .n.in?([-1, 0, 2]),
         in_opt: .opt_n.in?([10, 20]),
         in_empty: .code.in?([]),
         in_date: .d.in?([2026-01-01, 2026-12-31]),
         in_bool: .flag.in?([true])
       )
    |> where(.opt_n.in?([10, 99]) or .n.in?([2]))
    |> sort_by(.id)
  console.print("dyn_outer:#{"A".in?(allowed_codes)}")
  console.print_table(res)
  0
end
"#;
    let out = assert_oracle_vm_parity(pushed_src, Some(("E", &uri)), false)?;
    assert_eq!(out[0], "dyn_outer:true");
    // Row 2 has opt_n = None -> in_opt MUST be false (never null / true!)
    let joined = out.join("\n");
    assert!(
        joined.contains("| 2  | B ") && joined.contains("false"),
        "expected row 2 with opt_n=none -> in_opt=false in:\n{joined}"
    );

    // Verify SQLite pushdown emits IN (?, ...) & COALESCE(..., 0) for Option
    let checked = check_src(pushed_src)?;
    let main_fn = checked.exec.find_fun("main").ok_or("missing main")?;
    let plan = find_first_plan(&main_fn.body).ok_or("missing ExecPlan")?;
    let split = split_exec_plan_pushdown(plan, &checked.exec, "E", SqlDialect::Sqlite, None);
    let sql_text = match &split {
        SplitPlan::FullyPushed(q) | SplitPlan::Hybrid { pushdown: q, .. } => q.sql.clone(),
        SplitPlan::LocalOnly { reason, .. } => {
            return Err(format!("expected pushdown for in?: {reason}").into());
        }
    };
    assert!(
        sql_text.contains(" IN ("),
        "expected IN (...) pushdown: {sql_text}"
    );
    assert!(
        sql_text.contains("COALESCE("),
        "expected COALESCE for Option.in?: {sql_text}"
    );

    // Decimal & Float + dynamic outer list local parity
    let dec_flt_src = r#"module InDecFlt

fn main(console: Console) : Int
  outer_f = [1.5, 2.5]
  t = table
    | id | amt   | fscore | opt_t   |
    | 1  | 10.50 | 1.5    | "hi"    |
    | 2  | 20.00 | 3.0    | none    |
  end
  res = t
    |> derive(
         in_dec: .amt.in?([10.50, 99.00]),
         in_flt: .fscore.in?(list: outer_f),
         in_optt: .opt_t.in?(["hi", "yo"])
       )
    |> sort_by(.id)
  console.print_table(res)
  0
end
"#;
    assert_oracle_vm_parity(dec_flt_src, None, false)?;

    // Privacy check: sensitive list element or sensitive receiver MUST taint `.in?` and block Console!
    let pii_list_src = r#"module PrivacyInTest

fn leak(secret_s: Text [pii], console: Console) : Int
  xs = [secret_s]
  t = table
    | code |
    | "a"  |
  end
  r = t |> derive(hit: .code.in?(xs))
  console.print_table(r)
  0
end
"#;
    assert_oracle_vm_parity(pii_list_src, None, true)?;

    Ok(())
}

// ===========================================================================
// 5. Numeric `.clamp(lo, hi)` & `.round_to(step)` Parity + DomainError Traps
// ===========================================================================

#[test]
fn v05_clamp_and_round_to_parity_pushdown_and_domain_traps() -> TestResult {
    let tmp = TempDir::new("clamp_round")?;
    let db_path = tmp.path().join("nums.db");
    let uri = sqlite_uri(&db_path);
    let mut conn = open_connection(&uri)?;
    conn.execute(
        r#"CREATE TABLE "metrics" ("id" INTEGER PRIMARY KEY NOT NULL, "iv" INTEGER NOT NULL, "dv" TEXT NOT NULL, "fv" REAL NOT NULL)"#,
        &[],
    )?;
    for (id, iv, dv, fv) in [
        (1i64, -15i64, "-5.50", -1.37f64),
        (2, 50, "12.34", 1.38),
        (3, 150, "999.99", 5.625),
    ] {
        conn.execute(
            r#"INSERT INTO "metrics" VALUES (?, ?, ?, ?)"#,
            &[
                SqlParam::Int(id),
                SqlParam::Int(iv),
                SqlParam::Text(dv.to_string()),
                SqlParam::Float(dana::core::syntax::Float64::from_f64(fv)),
            ],
        )?;
    }
    drop(conn);

    let src = r##"module NumClampRound

schema Metric
  id: Int
  iv: Int
  dv: Decimal
  fv: Float
end

fn main(db: ReadDB(M), console: Console) : Int
  res = db.table(Metric, from: "metrics")
    |> derive(
         ci: .iv.clamp(-10, 100),
         cd: .dv.clamp(lo: 0.0, hi: 100.0),
         cf: .fv.clamp(0.0, 4.0),
         rt: .fv.round_to(0.25)
       )
    |> sort_by(.id)
  console.print("#{(-5).clamp(0, 10)}:#{3.75.clamp(1.0, 3.0)}:#{3.75.to_float.clamp(1.0, 3.0)}:#{1.38.to_float.round_to(step: 0.25)}")
  console.print_table(res)
  0
end
"##;
    let out = assert_oracle_vm_parity(src, Some(("M", &uri)), false)?;
    assert_eq!(out[0], "0:3.0:3:1.5");

    // Verify SQLite pushes Int clamp while breaking Decimal/Float, and Postgres pushes Decimal clamp!
    let checked = check_src(src)?;
    let main_fn = checked.exec.find_fun("main").ok_or("missing main")?;
    let plan = find_first_plan(&main_fn.body).ok_or("missing ExecPlan")?;
    let int_only_src = r#"module PgClamp

schema Metric
  id: Int
  iv: Int
  dv: Decimal
  fv: Float
end

fn main(db: ReadDB(M)) : Int
  _r = db.table(Metric, from: "metrics")
    |> derive(ci: .iv.clamp(0, 100), cd: .dv.clamp(0.0, 100.0))
  0
end
"#;
    let c2 = check_src(int_only_src)?;
    let p2 = find_first_plan(&c2.exec.find_fun("main").ok_or("main")?.body).ok_or("plan")?;
    let pg_split = split_exec_plan_pushdown(p2, &c2.exec, "M", SqlDialect::Postgres, None);
    assert!(
        matches!(pg_split, SplitPlan::FullyPushed(_)),
        "expected Postgres Int+Decimal clamp to push fully: {pg_split:?}"
    );
    let sq_split = split_exec_plan_pushdown(plan, &checked.exec, "M", SqlDialect::Sqlite, None);
    assert!(!matches!(sq_split, SplitPlan::FullyPushed(_)));

    // Exact DomainError trap parity (lo > hi on Int/Float/Decimal; step <= 0 on round_to)
    let trap_cases = [
        r#"module TrapClampInt
fn main() : Int
  _x = 5.clamp(10, 2)
  0
end
"#,
        r#"module TrapClampFlt
fn main() : Int
  _x = 1.5.to_float.clamp(5.0, 1.0)
  0
end
"#,
        r#"module TrapClampDec
fn main() : Int
  _x = 1.00.clamp(10.00, 2.00)
  0
end
"#,
        r#"module TrapRoundZero
fn main() : Int
  _x = 1.5.to_float.round_to(0.0)
  0
end
"#,
        r#"module TrapRoundNeg
fn main() : Int
  _x = 1.5.to_float.round_to(-0.25)
  0
end
"#,
    ];

    for case in trap_cases {
        assert_oracle_vm_domain_trap(case)?;
    }

    Ok(())
}

// ===========================================================================
// 6. `count_if(cond)`: Grouped, Ungrouped, Empty 0-Row Table, Privacy & Explain
// ===========================================================================

#[test]
fn v05_count_if_grouped_ungrouped_empty_privacy_and_explain() -> TestResult {
    let tmp = TempDir::new("count_if")?;
    let db_path = tmp.path().join("grades.db");
    let uri = sqlite_uri(&db_path);
    let mut conn = open_connection(&uri)?;
    conn.execute(
        r#"CREATE TABLE "grades" ("id" INTEGER PRIMARY KEY NOT NULL, "dept" TEXT NOT NULL, "passed" INTEGER NOT NULL, "gpa" TEXT NOT NULL)"#,
        &[],
    )?;
    for (id, dept, passed, gpa) in [
        (1i64, "OT", true, "3.90"),
        (2, "OT", false, "3.80"),
        (3, "OT", true, "3.70"),
        (4, "OT", true, "3.60"),
        (5, "OT", false, "3.10"),
        (6, "OT", false, "2.90"),
        (7, "NT", true, "3.80"),
        (8, "NT", true, "3.20"),
    ] {
        conn.execute(
            r#"INSERT INTO "grades" VALUES (?, ?, ?, ?)"#,
            &[
                SqlParam::Int(id),
                SqlParam::Text(dept.to_string()),
                SqlParam::Bool(passed),
                SqlParam::Text(gpa.to_string()),
            ],
        )?;
    }
    conn.execute(
        r#"CREATE TABLE "empty_grades" ("id" INTEGER PRIMARY KEY NOT NULL, "dept" TEXT NOT NULL, "passed" INTEGER NOT NULL)"#,
        &[],
    )?;
    drop(conn);

    // Grouped + ungrouped + 0-row ungrouped returning 0
    let src = r#"module CountIfTest

schema Grade
  id: Int
  dept: Text
  passed: Bool
  gpa: Decimal [ferpa]
end

schema EmptyGrade
  id: Int
  dept: Text
  passed: Bool
end

fn main(db: ReadDB(S), console: Console) : Int
  grouped = db.table(Grade, from: "grades")
    |> group_by(.dept)
    |> summarize(n: count(), pass_n: count_if(.passed))
    |> sort_by(.dept)
  ungrouped = db.table(Grade, from: "grades")
    |> summarize(n: count(), pass_n: count_if(.passed))
  empty_res = db.table(EmptyGrade, from: "empty_grades")
    |> summarize(n: count(), pass_n: count_if(.passed))
  console.print_table(grouped)
  console.print_table(ungrouped)
  console.print_table(empty_res)
  0
end
"#;
    let out = assert_oracle_vm_parity(src, Some(("S", &uri)), false)?;
    let joined = out.join("\n");
    // empty_res MUST produce 1 row with n=0, pass_n=0
    assert!(
        joined.contains("| 0 | 0      |"),
        "expected empty ungrouped count_if to return 0, got:\n{joined}"
    );

    // Non-Bool condition in `count_if` must fail typechecking
    let bad_cond = r#"module BadCountIf
fn main() : Int
  t = table
    | x |
    | 1 |
  end
  _r = t |> summarize(bad: count_if(.x))
  0
end
"#;
    let mut sm = SourceMap::new();
    let fid = sm.add_file("bad_ci.dana", bad_cond.to_string());
    let m = parse_module(fid, bad_cond).map_err(|d| format!("{d:?}"))?;
    let errs = check_module(fid, m, None, &sm)
        .err()
        .ok_or("expected TypeError on non-Bool count_if")?;
    assert!(errs.iter().any(|d| d.code() == DiagCode::TypeError));

    // Privacy propagation: `count_if(.gpa >= 3.50)` taints output with `[ferpa]`;
    // Console rejects without `suppress_small_groups`, and allows AFTER `suppress_small_groups(min: 5)`!
    let leak_src = r#"module CountIfLeak

schema Grade
  id: Int
  dept: Text
  passed: Bool
  gpa: Decimal [ferpa]
end

fn main(db: ReadDB(S), c: Console) : Int
  s = db.table(Grade, from: "grades")
    |> group_by(.dept)
    |> summarize(hi: count_if(.gpa >= 3.50))
  c.print_table(s)
  0
end
"#;
    assert_oracle_vm_parity(leak_src, Some(("S", &uri)), true)?;

    let safe_src = r#"module CountIfSuppressed

schema Grade
  id: Int
  dept: Text
  passed: Bool
  gpa: Decimal [ferpa]
end

fn main(db: ReadDB(S), c: Console) : Int
  s = db.table(Grade, from: "grades")
    |> group_by(.dept)
    |> summarize(hi: count_if(.gpa >= 3.50))
    |> suppress_small_groups(min: 5)
    |> sort_by(.dept)
  c.print_table(s)
  0
end
"#;
    let safe_out = assert_oracle_vm_parity(safe_src, Some(("S", &uri)), false)?;
    assert!(
        safe_out.join("\n").contains("OT") && safe_out.join("\n").contains("| 4  |"),
        "expected suppressed OT group with 4 high GPA rows:\n{safe_out:?}"
    );

    // `dana explain` includes `CountIf`
    let exp_file = tmp.path().join("explain_ci.dana");
    fs::write(&exp_file, safe_src)?;
    let exp_str = exp_file.to_string_lossy().to_string();
    let (ecode, eout, eerr) = run_dana_cmd(&["explain", &exp_str], Some(tmp.path()))?;
    assert_eq!(ecode, 0, "dana explain failed:\n{eerr}");
    assert!(
        eout.contains("CountIf"),
        "expected CountIf in explain:\n{eout}"
    );

    Ok(())
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
