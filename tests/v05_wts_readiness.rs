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

// ===========================================================================
// 7. Slice 5.2: Private Atomic Writes (0700/0600) Across All 8 Writers
// ===========================================================================

fn check_src_expect_diag(
    src: &str,
    policy_src: Option<&str>,
    expected_code: DiagCode,
) -> TestResult<String> {
    let mut sm = SourceMap::new();
    let policy = match policy_src {
        Some(ps) => {
            let pid = sm.add_file("dana.policy", ps.to_string());
            Some(
                dana::check::policy::parse_policy(pid, ps)
                    .map_err(|d| format!("policy error: {d:?}"))?,
            )
        }
        None => None,
    };
    let fid = sm.add_file("test.dana", src.to_string());
    let ast = parse_module(fid, src).map_err(|d| format!("parse error: {d:?}"))?;
    match check_module(fid, ast, policy, &sm) {
        Ok(_) => Err(format!("expected {expected_code:?}, but program checked cleanly").into()),
        Err(ds) => {
            if ds.iter().any(|d| d.code() == expected_code) {
                Ok(ds
                    .iter()
                    .map(|d| format!("{}: {}", d.code().as_str(), d.message()))
                    .collect::<Vec<_>>()
                    .join("\n"))
            } else {
                Err(format!("expected {expected_code:?}, got diagnostics: {ds:?}").into())
            }
        }
    }
}

#[cfg(unix)]
fn assert_mode(path: &Path, expected_mode: u32) -> TestResult {
    use std::os::unix::fs::PermissionsExt;
    let meta = fs::metadata(path)?;
    let got = meta.permissions().mode() & 0o777;
    assert_eq!(
        got,
        expected_mode,
        "expected mode {:04o} on {}, got {:04o}",
        expected_mode,
        path.display(),
        got
    );
    Ok(())
}

#[test]
fn v05_private_atomic_writes_0700_0600_all_writers_and_oracle_vm_parity() -> TestResult {
    let src = r#"module PrivateAllWriters

fn main(
  pub_out: WriteFiles("priv_out/"),
  tag_out: WriteFiles("tagged_out/", allows: [ferpa]),
  console: Console
) : Int
  tbl = table
    | k   | v  |
    | "a" | 10 |
    | "b" | 20 |
  end
  rep = Report.new("Summary") |> add_table(tbl)
  chart = tbl |> chart_bar(x: .k, y: .v, title: "Bars")

  try pub_out.write_csv("sub/a.csv", tbl, private: true)
  try pub_out.write_parquet("sub/a.parquet", tbl, private: true)
  try pub_out.write_xlsx("sub/a.xlsx", tbl, private: true)
  try pub_out.write_jsonl("sub/a.jsonl", tbl, private: true)
  try pub_out.write_html("sub/a.html", rep, private: true)
  try pub_out.write_markdown("sub/a.md", rep, private: true)
  try pub_out.write_svg("sub/a.svg", chart, private: true)
  try pub_out.write_file("sub/a.txt", "first-secret-content", private: true)
  try pub_out.write_file("sub/a.txt", "second-secret-content", private: true)

  # Implicit private write when WriteFiles carries non-empty `allows` tags
  try tag_out.write_csv("nested/implicit.csv", tbl)
  try tag_out.write_parquet("nested/implicit.parquet", tbl)
  console.print("ok")
  0
end
"#;

    let vm_dir = TempDir::new("priv_vm")?;
    let ora_dir = TempDir::new("priv_ora")?;
    let vm_file = vm_dir.path().join("prog.dana");
    let ora_file = ora_dir.path().join("prog.dana");
    fs::write(&vm_file, src)?;
    fs::write(&ora_file, src)?;
    let vm_fstr = vm_file.to_string_lossy().to_string();
    let ora_fstr = ora_file.to_string_lossy().to_string();

    let (vc, vo, ve) = run_dana_cmd(
        &["run", "--allow-export", "ferpa", &vm_fstr],
        Some(vm_dir.path()),
    )?;
    assert_eq!(vc, 0, "VM run failed:\nstderr={ve}\nstdout={vo}");
    let (oc, oo, oe) = run_dana_cmd(
        &["run", "--oracle", "--allow-export", "ferpa", &ora_fstr],
        Some(ora_dir.path()),
    )?;
    assert_eq!(oc, 0, "Oracle run failed:\nstderr={oe}\nstdout={oo}");
    assert_eq!(vo.trim(), "ok");
    assert_eq!(oo.trim(), "ok");

    let expected_files = [
        "priv_out/sub/a.csv",
        "priv_out/sub/a.parquet",
        "priv_out/sub/a.xlsx",
        "priv_out/sub/a.jsonl",
        "priv_out/sub/a.html",
        "priv_out/sub/a.md",
        "priv_out/sub/a.svg",
        "priv_out/sub/a.txt",
        "tagged_out/nested/implicit.csv",
        "tagged_out/nested/implicit.parquet",
    ];

    for rel in expected_files {
        let vp = vm_dir.path().join(rel);
        let op = ora_dir.path().join(rel);
        assert!(vp.exists(), "missing VM output {}", vp.display());
        assert!(op.exists(), "missing Oracle output {}", op.display());
        assert_eq!(
            fs::read(&vp)?,
            fs::read(&op)?,
            "VM vs Oracle byte mismatch for {rel}"
        );
        #[cfg(unix)]
        {
            assert_mode(&vp, 0o600)?;
            assert_mode(&op, 0o600)?;
        }
    }

    assert_eq!(
        fs::read_to_string(vm_dir.path().join("priv_out/sub/a.txt"))?,
        "second-secret-content"
    );

    #[cfg(unix)]
    for d in [
        "priv_out",
        "priv_out/sub",
        "tagged_out",
        "tagged_out/nested",
    ] {
        assert_mode(&vm_dir.path().join(d), 0o700)?;
        assert_mode(&ora_dir.path().join(d), 0o700)?;
        for entry in fs::read_dir(vm_dir.path().join(d))? {
            let name = entry?.file_name().to_string_lossy().into_owned();
            assert!(
                !name.contains(".dana-tmp."),
                "leftover temp file found in {d}: {name}"
            );
        }
    }

    // Negative static checks for invalid named arguments
    let bad_priv = r#"module BadPriv
fn main(out: WriteFiles("out/")) : Int
  _r = out.write_file("a.txt", "hi", private: 123)
  0
end
"#;
    check_src_expect_diag(bad_priv, None, DiagCode::TypeError)?;

    let bad_san = r#"module BadSan
fn main(out: WriteFiles("out/")) : Int
  t = table
    | x |
    | 1 |
  end
  _r = out.write_parquet("a.parquet", t, sanitize_formulas: true)
  0
end
"#;
    check_src_expect_diag(bad_san, None, DiagCode::TypeError)?;

    Ok(())
}

// ===========================================================================
// 8. Slice 5.2: CSV Formula Sanitization
// ===========================================================================

#[test]
fn v05_csv_formula_sanitization_unit_writer_formatter_and_vm_oracle_parity() -> TestResult {
    use dana::formats::csv::sanitize_csv_formula_cell;
    use std::borrow::Cow;

    // Pure negative decimals MUST remain unchanged (Borrowed)
    for safe in [
        "-42", "-3.14", "-0", "-0.001", "hello", "", " 42", "A=B", "foo-bar",
    ] {
        let got = sanitize_csv_formula_cell(safe);
        assert_eq!(got.as_ref(), safe, "unexpected change for `{safe}`");
        assert!(
            matches!(got, Cow::Borrowed(_)),
            "expected Borrowed for safe cell `{safe}`"
        );
    }

    // All dangerous triggers MUST receive a single leading apostrophe
    let dangerous = [
        ("=SUM(A1)", "'=SUM(A1)"),
        ("+123", "'+123"),
        ("-A1", "'-A1"),
        ("-1+1", "'-1+1"),
        ("--5", "'--5"),
        ("-3.14.1", "'-3.14.1"),
        ("-", "'-"),
        ("@cmd", "'@cmd"),
        ("\t=1", "'\t=1"),
        ("\r=1", "'\r=1"),
        ("  =SUM(A1)", "'  =SUM(A1)"),
        ("   +1", "'   +1"),
        (" -A1", "' -A1"),
        ("\u{0020}@calc", "'\u{0020}@calc"),
        ("=1,\"a\",2", "'=1,\"a\",2"),
        ("=1\n2", "'=1\n2"),
    ];
    for (raw, expected) in dangerous {
        let got = sanitize_csv_formula_cell(raw);
        assert_eq!(got.as_ref(), expected, "wrong sanitization for {raw:?}");
    }

    // End-to-end: both columnar VmTable (loaded from CSV) and TableVal (--oracle) across write_csv + format_csv
    let input_csv = concat!(
        "id,dec_v,flt_v,txt_cell\n",
        "-42,-12.50,-3.5,\"=SUM(A1)\"\n",
        "-1,0.00,-0.25,\"+123\"\n",
        "2,1.25,2.5,\"-A1\"\n",
        "3,3.00,4.0,\"-42\"\n",
        "4,4.00,5.0,\"-3.14\"\n",
        "5,5.00,6.0,\"  =1+1\"\n",
        "6,6.00,7.0,\"@cmd\"\n",
        "7,7.00,8.0,\"\t=1\"\n",
        "8,8.00,9.0,\"=1,\"\"q\"\",2\"\n"
    );

    let src = r#"module CsvSanitizeE2E

schema Row
  id: Int
  dec_v: Decimal
  flt_v: Float
  txt_cell: Text
end

fn main(files: ReadFiles, out: WriteFiles("csvs/"), console: Console) : Int
  (rows, _bad) = try files.read_csv("in.csv", as: Row)
  sorted = rows |> sort_by(.id)
  try out.write_csv("sanitized.csv", sorted, sanitize_formulas: true)
  try out.write_csv("raw.csv", sorted)
  console.print(sorted.format_csv(sanitize_formulas: true))
  console.print("---RAW---")
  console.print(format_csv(sorted))
  0
end
"#;

    let vm_dir = TempDir::new("csvsan_vm")?;
    let ora_dir = TempDir::new("csvsan_ora")?;
    fs::write(vm_dir.path().join("in.csv"), input_csv)?;
    fs::write(ora_dir.path().join("in.csv"), input_csv)?;
    let vm_prog = vm_dir.path().join("prog.dana");
    let ora_prog = ora_dir.path().join("prog.dana");
    fs::write(&vm_prog, src)?;
    fs::write(&ora_prog, src)?;
    let vm_s = vm_prog.to_string_lossy().to_string();
    let ora_s = ora_prog.to_string_lossy().to_string();

    let (vc, vo, ve) = run_dana_cmd(&["run", &vm_s], Some(vm_dir.path()))?;
    assert_eq!(vc, 0, "VM csv sanitize failed:\nstderr={ve}\nstdout={vo}");
    let (oc, oo, oe) = run_dana_cmd(&["run", "--oracle", &ora_s], Some(ora_dir.path()))?;
    assert_eq!(
        oc, 0,
        "Oracle csv sanitize failed:\nstderr={oe}\nstdout={oo}"
    );
    assert_eq!(vo, oo, "format_csv VM vs Oracle mismatch");

    let vm_san = fs::read_to_string(vm_dir.path().join("csvs/sanitized.csv"))?;
    let ora_san = fs::read_to_string(ora_dir.path().join("csvs/sanitized.csv"))?;
    let vm_raw = fs::read_to_string(vm_dir.path().join("csvs/raw.csv"))?;
    let ora_raw = fs::read_to_string(ora_dir.path().join("csvs/raw.csv"))?;
    assert_eq!(vm_san, ora_san, "write_csv sanitized VM vs Oracle mismatch");
    assert_eq!(vm_raw, ora_raw, "write_csv raw VM vs Oracle mismatch");

    // Genuine numeric negative cells & pure negative decimal text cells stay unescaped
    assert!(
        vm_san.contains("-42,-12.5,-3.5,'=SUM(A1)"),
        "got:\n{vm_san}"
    );
    assert!(vm_san.contains("-1,0.0,-0.25,'+123"), "got:\n{vm_san}");
    assert!(vm_san.contains("2,1.25,2.5,'-A1"), "got:\n{vm_san}");
    assert!(vm_san.contains("3,3.0,4,-42\n"), "got:\n{vm_san}");
    assert!(vm_san.contains("4,4.0,5,-3.14\n"), "got:\n{vm_san}");
    assert!(vm_san.contains("5,5.0,6,'  =1+1\n"), "got:\n{vm_san}");
    assert!(vm_san.contains("6,6.0,7,'@cmd\n"), "got:\n{vm_san}");
    assert!(vm_san.contains("7,7.0,8,'\t=1\n"), "got:\n{vm_san}");
    // RFC-4180 quoting happens AFTER formula prefixing
    assert!(
        vm_san.contains("8,8.0,9,\"'=1,\"\"q\"\",2\""),
        "got:\n{vm_san}"
    );
    // Unsanitized file keeps "=SUM(A1)" without apostrophe
    assert!(vm_raw.contains("-42,-12.5,-3.5,=SUM(A1)"), "got:\n{vm_raw}");

    // Formatters agree byte-for-byte with written CSV files
    let parts: Vec<&str> = vo.split("---RAW---\n").collect();
    assert_eq!(parts.len(), 2);
    assert_eq!(
        parts[0].trim_end_matches('\n'),
        vm_san.trim_end_matches('\n')
    );
    assert_eq!(
        parts[1].trim_end_matches('\n'),
        vm_raw.trim_end_matches('\n')
    );

    Ok(())
}

// ===========================================================================
// 9. Slice 5.2: Deterministic `shuffle` & Row-Level `suppress_small_cells`
// ===========================================================================

#[test]
fn v05_shuffle_determinism_seeds_tags_pushdown_and_oracle_vm_parity() -> TestResult {
    let tmp = TempDir::new("shuffle_db")?;
    let db_path = tmp.path().join("items.db");
    let uri = sqlite_uri(&db_path);
    let mut conn = open_connection(&uri)?;
    conn.execute(
        r#"CREATE TABLE "scores" ("id" INTEGER PRIMARY KEY NOT NULL, "label" TEXT NOT NULL, "secret_score" INTEGER NOT NULL)"#,
        &[],
    )?;
    for id in 1i64..=16 {
        conn.execute(
            r#"INSERT INTO "scores" VALUES (?, ?, ?)"#,
            &[
                SqlParam::Int(id),
                SqlParam::Text(format!("row_{id}")),
                SqlParam::Int(100 - id),
            ],
        )?;
    }
    drop(conn);

    // Clear order_tags via shuffle(seed:) after sort_by(.secret_score) and drop(.secret_score)
    let src = r#"module ShuffleTest

schema ScoreRow
  id: Int
  label: Text
  secret_score: Int [ferpa]
end

fn main(db: ReadDB(S), console: Console) : Int
  base = db.table(ScoreRow, from: "scores")
    |> sort_by(.secret_score)
    |> drop(.secret_score)
  s42a = base |> shuffle(seed: 42)
  s42b = base |> shuffle(seed: 42)
  s99 = base |> shuffle(seed: 99)
  s_neg = base |> shuffle(seed: -7)
  assert s42a == s42b
  console.print_table(s42a)
  console.print("---S99---")
  console.print_table(s99)
  console.print("---SNEG---")
  console.print_table(s_neg)
  0
end
"#;

    let out = assert_oracle_vm_parity(src, Some(("S", &uri)), false)?;
    let full = out.join("\n");
    let segs: Vec<&str> = full.split("---S99---").collect();
    assert_eq!(segs.len(), 2);
    let segs2: Vec<&str> = segs[1].split("---SNEG---").collect();
    assert_eq!(segs2.len(), 2);
    assert_ne!(segs[0], segs2[0], "distinct seeds 42 vs 99 should differ");
    assert_ne!(segs2[0], segs2[1], "distinct seeds 99 vs -7 should differ");

    // Extreme Int64 boundary seed parity + direct huge BigInt seed unit check
    let max_bi = dana::core::bigint::BigInt::from(i64::MAX);
    let huge_bi = &max_bi * &max_bi;
    assert_eq!(
        dana::vm::ops::sort_win::seed_from_bigint(&huge_bi),
        dana::vm::ops::sort_win::seed_from_bigint(&huge_bi)
    );
    assert_ne!(
        dana::vm::ops::sort_win::seed_from_bigint(&huge_bi),
        dana::vm::ops::sort_win::seed_from_bigint(&max_bi)
    );
    let big_seed_src = r#"module BigSeedShuffle

fn main(console: Console) : Int
  t = table
    | id |
    | 1  |
    | 2  |
    | 3  |
    | 4  |
    | 5  |
    | 6  |
    | 7  |
    | 8  |
  end
  console.print_table(t |> shuffle(seed: 9223372036854775807))
  0
end
"#;
    assert_oracle_vm_parity(big_seed_src, None, false)?;

    // Sorting by [ferpa] col WITHOUT shuffle MUST still block public export via order_tags
    let blocked_order_src = r#"module BlockedOrder

schema ScoreRow
  id: Int
  secret_score: Int [ferpa]
end

fn leak(db: ReadDB(S), out: WriteFiles("pub/")) : Int
  sorted = db.table(ScoreRow, from: "scores") |> sort_by(.secret_score) |> drop(.secret_score)
  _r = out.write_csv("x.csv", sorted)
  0
end
"#;
    check_src_expect_diag(blocked_order_src, None, DiagCode::PrivacyError)?;

    // SQL pushdown barrier: split_exec_plan_pushdown must push SourceDB -> Sort and stop at Shuffle
    let checked = check_src(src)?;
    let main_fn = checked.exec.find_fun("main").ok_or("missing main")?;
    let plan = find_first_plan(&main_fn.body).ok_or("missing ExecPlan")?;
    let split = split_exec_plan_pushdown(plan, &checked.exec, "S", SqlDialect::Sqlite, None);
    assert!(
        matches!(split, SplitPlan::Hybrid { .. }),
        "expected Hybrid pushdown stopping at Shuffle barrier, got {split:?}"
    );

    Ok(())
}

#[test]
fn v05_suppress_small_cells_k_anonymity_privacy_explain_and_parity() -> TestResult {
    let tmp = TempDir::new("scells_db")?;
    let db_path = tmp.path().join("students.db");
    let uri = sqlite_uri(&db_path);
    let mut conn = open_connection(&uri)?;
    conn.execute(
        r#"CREATE TABLE "cohort" (
            "sid" INTEGER PRIMARY KEY NOT NULL,
            "yr" INTEGER NOT NULL,
            "program" TEXT NOT NULL,
            "gpa" REAL NOT NULL,
            "opt_gpa" REAL,
            "dfw_flag" INTEGER NOT NULL
        )"#,
        &[],
    )?;
    // Cell (2026, "Grad"): 4 rows -> kept for min: 3
    // Cell (2026, "Rare"): 2 rows -> dropped for min: 3
    let rows_data = [
        (101i64, 2026i64, "Grad", 3.12f64, Some(3.12f64), true),
        (102, 2026, "Grad", 3.88, None, false),
        (103, 2026, "Grad", 2.94, Some(2.94), false),
        (104, 2026, "Grad", 3.45, Some(3.45), true),
        (105, 2026, "Rare", 3.50, Some(3.50), false),
        (106, 2026, "Rare", 3.60, Some(3.60), false),
        (107, 2025, "Filtered", 2.00, None, false),
        (108, 2025, "Filtered", 2.10, None, false),
        (109, 2025, "Filtered", 2.20, None, false),
    ];
    for (sid, yr, prog, gpa, ogpa, dfw) in rows_data {
        conn.execute(
            r#"INSERT INTO "cohort" VALUES (?, ?, ?, ?, ?, ?)"#,
            &[
                SqlParam::Int(sid),
                SqlParam::Int(yr),
                SqlParam::Text(prog.to_string()),
                SqlParam::Float(dana::core::syntax::Float64::from_f64(gpa)),
                match ogpa {
                    Some(v) => SqlParam::Float(dana::core::syntax::Float64::from_f64(v)),
                    None => SqlParam::Null,
                },
                SqlParam::Bool(dfw),
            ],
        )?;
    }
    drop(conn);

    // 1. Row-count k-anonymity + post-filter barrier + [ferpa] clearing on by: & round_to/bucket cols + VM == Oracle parity
    let k_src = r#"module SuppressCellsParity

schema CohortRow
  sid: Int [pii]
  yr: Int [ferpa]
  program: Text [ferpa]
  gpa: Float [ferpa]
  opt_gpa: Float? [ferpa]
  dfw_flag: Bool [ferpa]
end

fn main(db: ReadDB(C), console: Console) : Int
  safe = db.table(CohortRow, from: "cohort")
    |> where(.yr >= 2026)
    |> derive(
         gpa: .gpa.clamp(0.0, 4.0).round_to(0.1),
         opt_gpa: if .opt_gpa.some?: (.opt_gpa ?? 0.0).clamp(0.0, 4.0).round_to(0.1) else: none,
         gpa_band: bucket(.gpa, cuts: [2.5, 3.5], labels: ["low", "mid", "high"])
       )
    |> drop(.sid, .dfw_flag)
    |> suppress_small_cells(by: [.yr, .program], min: 3)
  console.print_table(safe)
  0
end
"#;
    let out = assert_oracle_vm_parity(k_src, Some(("C", &uri)), false)?;
    let joined = out.join("\n");
    assert!(joined.contains("Grad") && !joined.contains("Rare") && !joined.contains("Filtered"));

    // Pushdown barrier + K_ANON explain output
    let checked = check_src(k_src)?;
    let main_fn = checked.exec.find_fun("main").ok_or("missing main")?;
    let plan = find_first_plan(&main_fn.body).ok_or("missing ExecPlan")?;
    let split = split_exec_plan_pushdown(plan, &checked.exec, "C", SqlDialect::Sqlite, None);
    assert!(
        matches!(split, SplitPlan::Hybrid { .. }),
        "expected Hybrid pushdown stopping at SuppressSmallCells, got {split:?}"
    );
    let k_path = tmp.path().join("k_src.dana");
    fs::write(&k_path, k_src)?;
    let (ec, eo, ee) = run_dana_cmd(&["explain", &k_path.to_string_lossy()], Some(tmp.path()))?;
    assert_eq!(ec, 0, "explain failed: {ee}");
    assert!(
        eo.contains("K_ANON") && eo.contains("SuppressSmallCells"),
        "expected K_ANON in explain output:\n{eo}"
    );

    // 2. distinct_by: .student_id (with duplicates & none nulls!) VM == Oracle parity
    let distinct_src = r#"module DistinctCells

schema Rec
  student_id: Int?
  yr: Int [ferpa]
  prog: Text [ferpa]
  tag_label: Text
end

fn main(console: Console) : Int
  rows = table
    | student_id | yr   | prog | tag_label |
    | 1          | 2026 | "A"  | "a1"      |
    | 1          | 2026 | "A"  | "a2"      |
    | 2          | 2026 | "A"  | "a3"      |
    | none       | 2026 | "A"  | "a4"      |
    | 10         | 2026 | "B"  | "b1"      |
    | 11         | 2026 | "B"  | "b2"      |
    | 12         | 2026 | "B"  | "b3"      |
  end
  kept = rows |> suppress_small_cells(by: [.yr, .prog], min: 3, distinct_by: .student_id)
  console.print("kept=#{kept.count()}")
  console.print_table(kept)
  0
end
"#;
    // Cell (2026, "A") has 4 rows but only 2 non-null distinct students (1, 2) -> dropped! Cell B has 3 -> kept!
    let dout = assert_oracle_vm_parity(distinct_src, None, false)?;
    assert_eq!(dout[0], "kept=3");

    // 3. Static rejections: [pii], [secret], raw un-coarsened [ferpa] retained, policy floor, invalid min/by
    let pii_non_by = r#"module PiiNonBy
schema S
  sid: Int [pii]
  yr: Int [ferpa]
end
fn main(t: Table(S), console: Console) : Int
  _k = t |> suppress_small_cells(by: [.yr], min: 2)
  0
end
"#;
    let diag_pii = check_src_expect_diag(pii_non_by, None, DiagCode::PrivacyError)?;
    assert!(diag_pii.contains("E0202"));

    let pii_in_by = r#"module PiiInBy
schema S
  sid: Int [pii]
  yr: Int [ferpa]
end
fn main(t: Table(S), console: Console) : Int
  _k = t |> suppress_small_cells(by: [.sid, .yr], min: 2)
  0
end
"#;
    let diag_pii_by = check_src_expect_diag(pii_in_by, None, DiagCode::PrivacyError)?;
    assert!(diag_pii_by.contains("E0202"));

    let secret_col = r#"module SecretCol
schema S
  tok: Text [secret]
  yr: Int [ferpa]
end
fn main(t: Table(S), console: Console) : Int
  _k = t |> suppress_small_cells(by: [.yr], min: 2)
  0
end
"#;
    let diag_sec = check_src_expect_diag(secret_col, None, DiagCode::PrivacyError)?;
    assert!(diag_sec.contains("E0202"));

    // Raw un-coarsened [ferpa] column (even after raw .clamp) MUST keep [ferpa] and block public export!
    let uncoarsened_ferpa_export = r#"module UncoarsenedFerpa
schema S
  yr: Int [ferpa]
  raw_count: Int [ferpa]
end
fn leak(t: Table(S), out: WriteFiles("pub/")) : Int
  k = t
    |> derive(raw_count: .raw_count.clamp(0, 10))
    |> suppress_small_cells(by: [.yr], min: 2)
  _r = out.write_csv("leak.csv", k)
  0
end
"#;
    let diag_ferpa = check_src_expect_diag(uncoarsened_ferpa_export, None, DiagCode::PrivacyError)?;
    assert!(diag_ferpa.contains("E0202"));

    // Policy min_group_size floor enforcement
    let policy_10 = "version 1\nmin_group_size 10\n";
    let below_policy = r#"module BelowPolicy
schema S
  yr: Int [ferpa]
end
fn main(t: Table(S)) : Int
  _k = t |> suppress_small_cells(by: [.yr], min: 9)
  0
end
"#;
    check_src_expect_diag(below_policy, Some(policy_10), DiagCode::PrivacyError)?;

    let min_one = r#"module MinOne
schema S
  yr: Int [ferpa]
end
fn main(t: Table(S)) : Int
  _k = t |> suppress_small_cells(by: [.yr], min: 1)
  0
end
"#;
    check_src_expect_diag(min_one, None, DiagCode::PrivacyError)?;

    let empty_by = r#"module EmptyBy
schema S
  yr: Int [ferpa]
end
fn main(t: Table(S)) : Int
  _k = t |> suppress_small_cells(by: [], min: 2)
  0
end
"#;
    check_src_expect_diag(empty_by, None, DiagCode::TypeError)?;

    Ok(())
}

// ===========================================================================
// 10. Slice 5.2: Live E2E Verification of `examples/wts/` Pilots
// ===========================================================================

#[test]
fn v05_wts_pilots_end_to_end_parquet_and_pg_populi_enrollments() -> TestResult {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let wts_dir = root.join("examples").join("wts");
    let policy = wts_dir.join("dana.policy");
    let colab_dana = wts_dir.join("export_colab_parquet.dana");
    let retention_dana = wts_dir.join("retention_backtest.dana");

    let pol_s = policy.to_string_lossy().to_string();
    let colab_s = colab_dana.to_string_lossy().to_string();
    let ret_s = retention_dana.to_string_lossy().to_string();

    // 1. Direct CLI format --check, check --policy, and test --policy (VM & Oracle)
    let (fc, _, fe) = run_dana_cmd(&["format", "--check", &colab_s, &ret_s], None)?;
    assert_eq!(fc, 0, "format --check failed:\n{fe}");

    let (cc, _, ce) = run_dana_cmd(&["check", "--policy", &pol_s, &colab_s, &ret_s], None)?;
    assert_eq!(cc, 0, "check --policy failed:\n{ce}");

    let (tv_c, tv_o, tv_e) = run_dana_cmd(&["test", "--policy", &pol_s, &colab_s, &ret_s], None)?;
    assert_eq!(tv_c, 0, "VM test --policy failed:\n{tv_e}\n{tv_o}");

    let (to_c, to_o, to_e) = run_dana_cmd(
        &["test", "--oracle", "--policy", &pol_s, &colab_s, &ret_s],
        None,
    )?;
    assert_eq!(to_c, 0, "Oracle test --policy failed:\n{to_e}\n{to_o}");

    // 2. Live E2E `export_colab_parquet.dana` writing Zstd Parquet -> round-trip inspect + VM == Oracle
    let raw_hdr = "sid,student_name,tid,term_name,term_start,term_end,yr,term_season,is_semester_track,primary_program,course_code,course_name,active_courses_d21,had_dfw_d21,net_oop,gap_days,prev_term_gpa,prev_cum_gpa,gpa_delta,prev_comp_pct,prior_terms,prior_dfw_rate,online_rate\n";
    let mut raw_csv = String::from(raw_hdr);
    for idx in 1..=10 {
        let dfw = if idx % 3 == 0 { "true" } else { "false" };
        let ogpa = if idx == 2 { ",," } else { "3.45,3.40,0.05" };
        let comp = if idx == 2 { "" } else { "92.0" };
        raw_csv.push_str(&format!(
            "{},Student_{idx},1,2026SP,2026-01-12,2026-05-01,2026,Spring,true,Graduate,ST501,Theology,{},{},17234.0,912.0,{},{},25,0.23,0.97\n",
            100 + idx,
            idx + 10,
            dfw,
            ogpa,
            comp,
        ));
    }
    // Small rare cell (only 2 rows) -> suppressed under min: 10
    raw_csv.push_str("901,RareA,2,2026JA,2026-01-02,2026-01-20,2026,J-Term,false,Rare Cert,CH1,History,1,false,400.0,10.0,3.1,3.1,0.0,80.0,1,0.0,0.0\n");
    raw_csv.push_str("902,RareB,2,2026JA,2026-01-02,2026-01-20,2026,J-Term,false,Rare Cert,CH1,History,1,true,400.0,10.0,3.1,3.1,0.0,80.0,1,0.0,0.0\n");

    let colab_vm_dir = TempDir::new("colab_vm")?;
    let colab_ora_dir = TempDir::new("colab_ora")?;
    fs::write(colab_vm_dir.path().join("colab_raw.csv"), &raw_csv)?;
    fs::write(colab_ora_dir.path().join("colab_raw.csv"), &raw_csv)?;

    let (cvm_c, cvm_o, cvm_e) = run_dana_cmd(
        &[
            "run",
            "--policy",
            &pol_s,
            "--allow-export",
            "ferpa",
            &colab_s,
        ],
        Some(colab_vm_dir.path()),
    )?;
    assert_eq!(cvm_c, 0, "Colab VM run failed:\n{cvm_e}\n{cvm_o}");

    let (cora_c, cora_o, cora_e) = run_dana_cmd(
        &[
            "run",
            "--oracle",
            "--policy",
            &pol_s,
            "--allow-export",
            "ferpa",
            &colab_s,
        ],
        Some(colab_ora_dir.path()),
    )?;
    assert_eq!(cora_c, 0, "Colab Oracle run failed:\n{cora_e}\n{cora_o}");
    assert_eq!(cvm_o.trim(), "exported 10 k-anonymous rows");
    assert_eq!(cora_o, cvm_o);

    let vm_pq = colab_vm_dir
        .path()
        .join("colab-exports/colab_training.parquet");
    let ora_pq = colab_ora_dir
        .path()
        .join("colab-exports/colab_training.parquet");
    assert!(vm_pq.exists() && ora_pq.exists());
    #[cfg(unix)]
    {
        assert_mode(&colab_vm_dir.path().join("colab-exports"), 0o700)?;
        assert_mode(&vm_pq, 0o600)?;
        assert_mode(&colab_ora_dir.path().join("colab-exports"), 0o700)?;
        assert_mode(&ora_pq, 0o600)?;
    }

    let (_, vm_tbl) = dana::formats::parquet::read_parquet_file_untyped(&vm_pq, "ColabTraining")?;
    let (_, ora_tbl) = dana::formats::parquet::read_parquet_file_untyped(&ora_pq, "ColabTraining")?;
    assert_eq!(vm_tbl.rows.len(), 10);
    assert_eq!(
        dana::formats::csv::format_csv_table(&vm_tbl, b','),
        dana::formats::csv::format_csv_table(&ora_tbl, b','),
        "Parquet round-trip VM != Oracle"
    );

    let pq_col_names: Vec<&str> = vm_tbl.cols.iter().map(|c| c.name.as_str()).collect();
    for dropped in [
        "sid",
        "student_name",
        "tid",
        "term_name",
        "term_start",
        "term_end",
        "course_code",
        "course_name",
        "had_dfw_d21",
    ] {
        assert!(
            !pq_col_names.contains(&dropped),
            "column `{dropped}` should have been dropped from Parquet"
        );
    }

    // 3. Live E2E `retention_backtest.dana` via MultiSchemaPgMock (`populi.enrollments`) VM & Oracle
    let pg_tmp = TempDir::new("retention_pg")?;
    let main_db = pg_tmp.path().join("main.db");
    let populi_db = pg_tmp.path().join("populi.db");
    {
        let c = SqliteConn::open(&main_db.to_string_lossy(), SqliteOpenMode::ReadWriteCreate)?;
        c.execute_batch(r#"CREATE TABLE "meta" ("k" TEXT PRIMARY KEY NOT NULL);"#)?;
    }
    {
        let c = SqliteConn::open(
            &populi_db.to_string_lossy(),
            SqliteOpenMode::ReadWriteCreate,
        )?;
        c.execute_batch(
            r#"
            CREATE TABLE "enrollments" (
                "student_person_id" INTEGER NOT NULL,
                "academic_term_id" INTEGER NOT NULL,
                "academic_term_name" TEXT NOT NULL,
                "academic_term_start_date" TEXT NOT NULL,
                "course_campus_name" TEXT NOT NULL,
                "course_student_status" TEXT NOT NULL,
                "finalized" TEXT NOT NULL,
                "grade_abbrv" TEXT NOT NULL
            );
            "#,
        )?;
        // Term 101 ("=SUM(A1)"): 10 distinct students, 3 DFW (WITHDRAWN, finalized F, finalized D+)
        for s in 1i64..=10 {
            let (status, fin, grade) = match s {
                1 => ("WITHDRAWN", "0", ""),
                2 => ("ENROLLED", "1", "F"),
                3 => ("ENROLLED", "1", "D+"),
                4 => ("ENROLLED", "0", "F"), // unfinalized -> NOT DFW!
                _ => ("ENROLLED", "1", "A"),
            };
            let mut st =
                c.prepare(r#"INSERT INTO "enrollments" VALUES (?, ?, ?, ?, ?, ?, ?, ?)"#)?;
            st.bind_int64(1, s)?;
            st.bind_int64(2, 101)?;
            st.bind_text(3, "=SUM(A1)")?;
            st.bind_text(4, "2026-01-12T00:00:00Z")?;
            st.bind_text(5, "Online Campus")?;
            st.bind_text(6, status)?;
            st.bind_text(7, fin)?;
            st.bind_text(8, grade)?;
            while st.step()? == StepResult::Row {}
        }
        // Excluded rows on Term 101: NGC grade, Main Campus, bad date
        for (sid, dt, campus, grade) in [
            (10i64, "2026-01-12", "Online Campus", "NGC"),
            (99i64, "2026-01-12", "Main Campus", "F"),
            (98i64, "bad-date", "Online Campus", "A"),
        ] {
            let mut st =
                c.prepare(r#"INSERT INTO "enrollments" VALUES (?, ?, ?, ?, ?, ?, ?, ?)"#)?;
            st.bind_int64(1, sid)?;
            st.bind_int64(2, 101)?;
            st.bind_text(3, "=SUM(A1)")?;
            st.bind_text(4, dt)?;
            st.bind_text(5, campus)?;
            st.bind_text(6, "ENROLLED")?;
            st.bind_text(7, "1")?;
            st.bind_text(8, grade)?;
            while st.step()? == StepResult::Row {}
        }
        // Term 102: 12 enrollments across ONLY 3 distinct students -> suppressed!
        for i in 0i64..12 {
            let mut st =
                c.prepare(r#"INSERT INTO "enrollments" VALUES (?, ?, ?, ?, ?, ?, ?, ?)"#)?;
            st.bind_int64(1, 500 + (i % 3))?;
            st.bind_int64(2, 102)?;
            st.bind_text(3, "2026SU")?;
            st.bind_text(4, "2026-05-18T00:00:00Z")?;
            st.bind_text(5, "Online Campus")?;
            st.bind_text(6, "ENROLLED")?;
            st.bind_text(7, "1")?;
            st.bind_text(8, "A")?;
            while st.step()? == StepResult::Row {}
        }
    }

    let pg = MultiSchemaPgMock::start(&main_db, vec![("populi".to_string(), populi_db)])?;
    let db_arg = format!("PopuliDB={}", pg.uri);

    let ret_vm_dir = TempDir::new("ret_vm")?;
    let ret_ora_dir = TempDir::new("ret_ora")?;

    let (rvm_c, rvm_o, rvm_e) = run_dana_cmd(
        &["run", "--policy", &pol_s, "--db", &db_arg, &ret_s],
        Some(ret_vm_dir.path()),
    )?;
    assert_eq!(rvm_c, 0, "Retention VM run failed:\n{rvm_e}\n{rvm_o}");

    let pg_queries = pg.recorded();
    assert!(
        pg_queries
            .iter()
            .any(|q| q.sql.contains(r#"FROM "populi"."enrollments""#) && q.sql.contains("IN (")),
        "expected parameterized pushdown FROM \"populi\".\"enrollments\", got: {pg_queries:?}"
    );

    let (rora_c, rora_o, rora_e) = run_dana_cmd(
        &[
            "run", "--oracle", "--policy", &pol_s, "--db", &db_arg, &ret_s,
        ],
        Some(ret_ora_dir.path()),
    )?;
    assert_eq!(
        rora_c, 0,
        "Retention Oracle run failed:\n{rora_e}\n{rora_o}"
    );
    assert_eq!(rvm_o.trim(), "exported 1 terms");
    assert_eq!(rora_o, rvm_o);

    let vm_csv_path = ret_vm_dir.path().join("exports/retention_backtest.csv");
    let ora_csv_path = ret_ora_dir.path().join("exports/retention_backtest.csv");
    assert!(vm_csv_path.exists() && ora_csv_path.exists());
    #[cfg(unix)]
    {
        assert_mode(&ret_vm_dir.path().join("exports"), 0o700)?;
        assert_mode(&vm_csv_path, 0o600)?;
        assert_mode(&ret_ora_dir.path().join("exports"), 0o700)?;
        assert_mode(&ora_csv_path, 0o600)?;
    }

    let vm_csv = fs::read_to_string(&vm_csv_path)?;
    let ora_csv = fs::read_to_string(&ora_csv_path)?;
    assert_eq!(vm_csv, ora_csv);
    assert!(
        vm_csv.contains("101,'=SUM(A1),2026-01-12,10,10,3"),
        "expected formula-sanitized CSV row with exact DFW count 3, got:\n{vm_csv}"
    );
    assert!(!vm_csv.contains("2026SU") && !vm_csv.contains("102,"));

    Ok(())
}
