//! Native zero-crate PostgreSQL Wire Protocol v3.0 driver implementing [`DbConnection`].
//!
//! Compiled strictly under `#[forbid(unsafe_code)]`. Features:
//! - `SSLRequest` negotiation honoring [`SslMode`] (`Disable`, `Prefer`, `Require`, `VerifyCa`, `VerifyFull`)
//!   over [`crate::ffi::tls::TlsStream`]
//! - Authentication: `AuthenticationOk`, `CleartextPassword`, RFC 1321 `MD5Password`, and full
//!   RFC 7677 `SCRAM-SHA-256` with server signature verification
//! - Parameterized-only Extended Query Protocol (`Parse`, `Bind`, `Describe`, `Execute`, `Sync`)
//! - Typed PostgreSQL OID decoding (both text and binary wire formats) including exact 10^18 `Decimal`
//! - `information_schema` introspection into [`LockedDb`]
//! - Transactional parameterized `upsert_table` and strictly read-only `dry_run` diffs.

use std::collections::{HashMap, HashSet};
use std::fmt;
use std::fs::File;
use std::io::{self, Read, Write};
use std::net::{TcpStream, ToSocketAddrs};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, SystemTime, UNIX_EPOCH};

use crate::core::bigint::BigInt;
use crate::core::syntax::{Float64, ScalarTy, TableTy, TagSet};
use crate::ffi::tls::{TlsClientConfig, TlsStream};
use crate::formats::crypto::{hmac_sha256, sha256, to_hex_lower};
use crate::formats::time::{
    MICROS_PER_DAY, MICROS_PER_HOUR, MICROS_PER_MINUTE, MICROS_PER_SECOND, format_iso_date,
    format_iso_timestamp, parse_decimal_bigint_strict, parse_iso_date,
};
use crate::oracle::value::{TableVal, Val};
use crate::vm::ops::VmTable;

use super::schema_lock::{LockedCol, LockedDb, LockedTable};
use super::{
    ColumnarBatchBuilder, DbConnection, DbError, PostgresUri, SqlDialect, SqlParam, SslMode,
    UpsertDiff, compute_upsert_diff, format_decimal_canonical, hex_nibble, make_table_row,
    parse_iso_timestamp_flexible, quote_sql_ident, quote_sql_table_ref,
};

const PG_PROTOCOL_V3: i32 = 196_608; // 3 << 16
const PG_SSL_REQUEST_CODE: i32 = 80_877_103;
/// Days between Unix epoch (`1970-01-01`) and PostgreSQL epoch (`2000-01-01`).
const PG_EPOCH_DAYS: i64 = 10_957;
const PG_EPOCH_MICROS: i64 = PG_EPOCH_DAYS * MICROS_PER_DAY;
const MAX_WIRE_MESSAGE_BYTES: usize = 64 * 1024 * 1024;
const PG_FIRST_NORMAL_OBJECT_ID: u32 = 16_384;

/// Standard PostgreSQL type OIDs.
pub mod oid {
    pub const BOOL: u32 = 16;
    pub const BYTEA: u32 = 17;
    pub const CHAR: u32 = 18;
    pub const NAME: u32 = 19;
    pub const INT8: u32 = 20;
    pub const INT2: u32 = 21;
    pub const INT4: u32 = 23;
    pub const TEXT: u32 = 25;
    pub const JSON: u32 = 114;
    pub const FLOAT4: u32 = 700;
    pub const FLOAT8: u32 = 701;
    pub const BPCHAR: u32 = 1042;
    pub const VARCHAR: u32 = 1043;
    pub const DATE: u32 = 1082;
    pub const TIMESTAMP: u32 = 1114;
    pub const TIMESTAMPTZ: u32 = 1184;
    pub const INTERVAL: u32 = 1186;
    pub const NUMERIC: u32 = 1700;
    pub const UUID: u32 = 2950;
    pub const JSONB: u32 = 3802;
}

enum PgTransport {
    Plain(TcpStream),
    Tls(TlsStream),
}

impl fmt::Debug for PgTransport {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Plain(_) => f.write_str("PgTransport::Plain"),
            Self::Tls(_) => f.write_str("PgTransport::Tls"),
        }
    }
}

impl Read for PgTransport {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        match self {
            Self::Plain(s) => s.read(buf),
            Self::Tls(s) => s.read(buf),
        }
    }
}

impl Write for PgTransport {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        match self {
            Self::Plain(s) => s.write(buf),
            Self::Tls(s) => s.write(buf),
        }
    }

    fn flush(&mut self) -> io::Result<()> {
        match self {
            Self::Plain(s) => s.flush(),
            Self::Tls(s) => s.flush(),
        }
    }
}

#[derive(Debug)]
struct PgFieldDesc {
    name: String,
    type_oid: u32,
    format_code: i16,
}

/// Native PostgreSQL Wire Protocol v3.0 database driver implementing [`DbConnection`].
#[derive(Debug)]
pub struct PostgresDriver {
    transport: PgTransport,
    read_buf: Vec<u8>,
    read_pos: usize,
    read_len: usize,
    server_params: HashMap<String, String>,
    in_tls: bool,
}

impl PostgresDriver {
    /// Connect to a PostgreSQL server specified by `uri`, negotiating TLS and authentication.
    ///
    /// # Errors
    /// Returns [`DbError`] on TCP connect failure, TLS rejection, auth failure, or protocol errors.
    pub fn connect(uri: &PostgresUri) -> Result<Self, DbError> {
        let tcp = connect_tcp(uri)?;
        let (transport, in_tls) = negotiate_tls(tcp, uri)?;

        let mut driver = Self {
            transport,
            read_buf: vec![0u8; 16 * 1024],
            read_pos: 0,
            read_len: 0,
            server_params: HashMap::new(),
            in_tls,
        };

        driver.send_startup(uri)?;
        driver.complete_auth(uri)?;
        Ok(driver)
    }

    /// Returns `true` if this connection was upgraded to TLS.
    #[must_use]
    pub const fn is_tls(&self) -> bool {
        self.in_tls
    }

    /// Read a server parameter announced via `ParameterStatus` during startup.
    #[must_use]
    pub fn server_param(&self, key: &str) -> Option<&str> {
        self.server_params.get(key).map(String::as_str)
    }

    /// Introspect tables across one or more PostgreSQL schemas using parameterized
    /// `information_schema` queries.
    ///
    /// Tables in `"public"` keep unqualified names (`"orders"`), while tables in any
    /// other schema are named `"<schema>.<table>"` (e.g. `"populi.enrollments"`).
    ///
    /// # Errors
    /// Returns [`DbError`] if `schemas` contains invalid identifiers or the catalog query fails.
    pub fn introspect_schema_with_schemas(
        &mut self,
        db_name: &str,
        schemas: &[String],
    ) -> Result<LockedDb, DbError> {
        let mut normalized: Vec<String> = Vec::new();
        if schemas.is_empty() {
            normalized.push("public".to_string());
        } else {
            for raw in schemas {
                let s = raw.trim();
                if s.is_empty()
                    || s.contains(char::is_whitespace)
                    || s.as_bytes().contains(&0)
                    || s.chars().any(char::is_control)
                {
                    return Err(DbError::Query(format!(
                        "invalid PostgreSQL schema name `{raw}`"
                    )));
                }
                if !normalized.iter().any(|existing| existing == s) {
                    normalized.push(s.to_string());
                }
            }
        }

        let placeholders: Vec<String> = (1..=normalized.len()).map(|i| format!("${i}")).collect();
        let in_list = placeholders.join(", ");
        let schema_params: Vec<SqlParam> = normalized.into_iter().map(SqlParam::Text).collect();

        let mut pk_set: HashSet<(String, String, String)> = HashSet::new();
        let pk_sql = format!(
            "SELECT tc.table_schema, tc.table_name, kcu.column_name \
             FROM information_schema.table_constraints tc \
             JOIN information_schema.key_column_usage kcu \
               ON tc.constraint_name = kcu.constraint_name \
              AND tc.table_schema = kcu.table_schema \
              AND tc.table_name = kcu.table_name \
             WHERE tc.constraint_type = 'PRIMARY KEY' \
               AND tc.table_schema IN ({in_list})"
        );
        self.run_extended_query(&pk_sql, &schema_params, |_fields, cells| {
            if cells.len() >= 3
                && let (Some(s), Some(t), Some(c)) = (cells[0], cells[1], cells[2])
            {
                let sn = String::from_utf8_lossy(s).into_owned();
                let tn = String::from_utf8_lossy(t).into_owned();
                let cn = String::from_utf8_lossy(c).into_owned();
                pk_set.insert((sn, tn, cn));
            }
            Ok(())
        })?;

        let mut table_order: Vec<String> = Vec::new();
        let mut table_cols: HashMap<String, Vec<LockedCol>> = HashMap::new();

        let cols_sql = format!(
            "SELECT table_schema, table_name, column_name, data_type, udt_name, is_nullable \
             FROM information_schema.columns \
             WHERE table_schema IN ({in_list}) \
             ORDER BY table_schema, table_name, ordinal_position"
        );
        self.run_extended_query(&cols_sql, &schema_params, |_fields, cells| {
            if cells.len() < 6 {
                return Err(DbError::SchemaDrift(
                    "information_schema.columns returned fewer than 6 columns".to_string(),
                ));
            }
            let table_schema = decode_utf8_cell(cells[0], "table_schema")?;
            let table_name = decode_utf8_cell(cells[1], "table_name")?;
            let col_name = decode_utf8_cell(cells[2], "column_name")?;
            let data_type = decode_utf8_cell(cells[3], "data_type")?;
            let udt_name = decode_utf8_cell(cells[4], "udt_name")?;
            let is_nullable_str = decode_utf8_cell(cells[5], "is_nullable")?;
            let pk = pk_set.contains(&(table_schema.clone(), table_name.clone(), col_name.clone()));
            let nullable = is_nullable_str.eq_ignore_ascii_case("YES") && !pk;

            let qualified_name = if table_schema == "public" {
                table_name
            } else {
                format!("{table_schema}.{table_name}")
            };

            if !table_cols.contains_key(&qualified_name) {
                table_order.push(qualified_name.clone());
            }
            table_cols
                .entry(qualified_name)
                .or_default()
                .push(LockedCol {
                    name: col_name,
                    ty: map_pg_type_name(&data_type, &udt_name),
                    nullable,
                    pk,
                    tags: TagSet::empty(),
                });
            Ok(())
        })?;

        let tables = table_order
            .into_iter()
            .map(|name| LockedTable {
                cols: table_cols.remove(&name).unwrap_or_default(),
                name,
            })
            .collect();

        Ok(LockedDb {
            name: db_name.to_string(),
            dialect: SqlDialect::Postgres,
            tables,
        })
    }

    fn read_exact_buffered(&mut self, mut dst: &mut [u8]) -> Result<(), DbError> {
        while !dst.is_empty() {
            if self.read_pos < self.read_len {
                let avail = self.read_len - self.read_pos;
                let take = avail.min(dst.len());
                dst[..take].copy_from_slice(&self.read_buf[self.read_pos..self.read_pos + take]);
                self.read_pos += take;
                dst = &mut dst[take..];
            } else {
                let n = self
                    .transport
                    .read(&mut self.read_buf)
                    .map_err(|e| DbError::Io(format!("postgres read failed: {e}")))?;
                if n == 0 {
                    return Err(DbError::Io(
                        "unexpected EOF from PostgreSQL server".to_string(),
                    ));
                }
                self.read_pos = 0;
                self.read_len = n;
            }
        }
        Ok(())
    }

    fn read_message(&mut self) -> Result<(u8, Vec<u8>), DbError> {
        let mut hdr = [0u8; 5];
        self.read_exact_buffered(&mut hdr)?;
        let (tag, body_len) = parse_pg_frame_header(hdr)?;
        let mut body = vec![0u8; body_len];
        if body_len > 0 {
            self.read_exact_buffered(&mut body)?;
        }
        Ok((tag, body))
    }

    fn send_tagged(&mut self, tag: u8, payload: &[u8]) -> Result<(), DbError> {
        let len = i32::try_from(payload.len() + 4)
            .map_err(|_| DbError::Protocol("outgoing frame exceeds i32::MAX".to_string()))?;
        let mut frame = Vec::with_capacity(5 + payload.len());
        frame.push(tag);
        frame.extend_from_slice(&len.to_be_bytes());
        frame.extend_from_slice(payload);
        self.transport
            .write_all(&frame)
            .map_err(|e| DbError::Io(format!("postgres write failed: {e}")))?;
        self.transport
            .flush()
            .map_err(|e| DbError::Io(format!("postgres flush failed: {e}")))
    }

    fn send_startup(&mut self, uri: &PostgresUri) -> Result<(), DbError> {
        let mut body = Vec::new();
        body.extend_from_slice(&PG_PROTOCOL_V3.to_be_bytes());
        push_cstr(&mut body, "user")?;
        push_cstr(&mut body, &uri.user)?;
        push_cstr(&mut body, "database")?;
        push_cstr(&mut body, &uri.database)?;
        push_cstr(&mut body, "client_encoding")?;
        push_cstr(&mut body, "UTF8")?;
        push_cstr(&mut body, "TimeZone")?;
        push_cstr(&mut body, "UTC")?;
        push_cstr(&mut body, "DateStyle")?;
        push_cstr(&mut body, "ISO, YMD")?;
        body.push(0);

        let total_len = i32::try_from(body.len() + 4)
            .map_err(|_| DbError::Protocol("startup message too large".to_string()))?;
        let mut frame = Vec::with_capacity(body.len() + 4);
        frame.extend_from_slice(&total_len.to_be_bytes());
        frame.extend_from_slice(&body);
        self.transport
            .write_all(&frame)
            .map_err(|e| DbError::Io(format!("failed to send StartupMessage: {e}")))?;
        self.transport
            .flush()
            .map_err(|e| DbError::Io(format!("failed to flush StartupMessage: {e}")))
    }

    fn complete_auth(&mut self, uri: &PostgresUri) -> Result<(), DbError> {
        let mut scram_client_nonce: Option<String> = None;
        let mut scram_client_first_bare: Option<String> = None;
        let mut scram_expected_server_sig: Option<[u8; 32]> = None;

        loop {
            let (tag, body) = self.read_message()?;
            match tag {
                b'R' => {
                    if body.len() < 4 {
                        return Err(DbError::Protocol(
                            "truncated Authentication frame".to_string(),
                        ));
                    }
                    let auth_code = i32::from_be_bytes([body[0], body[1], body[2], body[3]]);
                    let rest = &body[4..];
                    match auth_code {
                        0 => {
                            // AuthenticationOk
                        }
                        3 => {
                            // AuthenticationCleartextPassword
                            let pass = uri.password.as_deref().ok_or_else(|| {
                                DbError::Auth(
                                    "server requested cleartext password but none was provided"
                                        .to_string(),
                                )
                            })?;
                            let mut payload = Vec::with_capacity(pass.len() + 1);
                            push_cstr(&mut payload, pass)?;
                            self.send_tagged(b'p', &payload)?;
                        }
                        5 => {
                            // AuthenticationMD5Password
                            if rest.len() < 4 {
                                return Err(DbError::Protocol(
                                    "truncated MD5 salt in AuthenticationMD5Password".to_string(),
                                ));
                            }
                            let salt = [rest[0], rest[1], rest[2], rest[3]];
                            let pass = uri.password.as_deref().ok_or_else(|| {
                                DbError::Auth(
                                    "server requested MD5 password but none was provided"
                                        .to_string(),
                                )
                            })?;
                            let response = pg_md5_password(&uri.user, pass, salt);
                            let mut payload = Vec::with_capacity(response.len() + 1);
                            push_cstr(&mut payload, &response)?;
                            self.send_tagged(b'p', &payload)?;
                        }
                        10 => {
                            // AuthenticationSASL
                            let mechs = parse_cstr_list(rest)?;
                            if !mechs.iter().any(|m| m == "SCRAM-SHA-256") {
                                return Err(DbError::Auth(format!(
                                    "server offered unsupported SASL mechanisms: {mechs:?}"
                                )));
                            }
                            let nonce = generate_scram_nonce();
                            let client_first_bare = format!("n=,r={nonce}");
                            let client_first_msg = format!("n,,{client_first_bare}");

                            let mut payload = Vec::new();
                            push_cstr(&mut payload, "SCRAM-SHA-256")?;
                            let msg_len = i32::try_from(client_first_msg.len()).map_err(|_| {
                                DbError::Protocol("SASL initial response too large".to_string())
                            })?;
                            payload.extend_from_slice(&msg_len.to_be_bytes());
                            payload.extend_from_slice(client_first_msg.as_bytes());
                            self.send_tagged(b'p', &payload)?;

                            scram_client_nonce = Some(nonce);
                            scram_client_first_bare = Some(client_first_bare);
                        }
                        11 => {
                            // AuthenticationSASLContinue
                            let server_first = std::str::from_utf8(rest).map_err(|_| {
                                DbError::Protocol("invalid UTF-8 in SASLContinue".to_string())
                            })?;
                            let client_nonce = scram_client_nonce.as_deref().ok_or_else(|| {
                                DbError::Protocol(
                                    "received SASLContinue before SASLInit".to_string(),
                                )
                            })?;
                            let client_first_bare =
                                scram_client_first_bare.as_deref().ok_or_else(|| {
                                    DbError::Protocol(
                                        "missing SCRAM client-first-bare state".to_string(),
                                    )
                                })?;
                            let pass = uri.password.as_deref().ok_or_else(|| {
                                DbError::Auth(
                                    "server requested SCRAM-SHA-256 password but none was provided"
                                        .to_string(),
                                )
                            })?;

                            let (combined_nonce, salt, iterations) =
                                parse_scram_server_first(server_first, client_nonce)?;

                            let salted_password =
                                scram_pbkdf2_hmac_sha256(pass.as_bytes(), &salt, iterations);
                            let client_key = hmac_sha256(&salted_password, b"Client Key");
                            let stored_key = sha256(&client_key);
                            let client_final_no_proof = format!("c=biws,r={combined_nonce}");
                            let auth_message = format!(
                                "{client_first_bare},{server_first},{client_final_no_proof}"
                            );
                            let client_sig = hmac_sha256(&stored_key, auth_message.as_bytes());
                            let mut client_proof = [0u8; 32];
                            for i in 0..32 {
                                client_proof[i] = client_key[i] ^ client_sig[i];
                            }

                            let server_key = hmac_sha256(&salted_password, b"Server Key");
                            let expected_sig = hmac_sha256(&server_key, auth_message.as_bytes());
                            scram_expected_server_sig = Some(expected_sig);

                            let client_final = format!(
                                "{client_final_no_proof},p={}",
                                base64_encode(&client_proof)
                            );
                            self.send_tagged(b'p', client_final.as_bytes())?;
                        }
                        12 => {
                            // AuthenticationSASLFinal
                            let server_final = std::str::from_utf8(rest).map_err(|_| {
                                DbError::Protocol("invalid UTF-8 in SASLFinal".to_string())
                            })?;
                            let expected = scram_expected_server_sig.ok_or_else(|| {
                                DbError::Protocol(
                                    "received SASLFinal before SASLContinue".to_string(),
                                )
                            })?;
                            verify_scram_server_final(server_final, &expected)?;
                        }
                        other => {
                            return Err(DbError::Auth(format!(
                                "unsupported PostgreSQL authentication type {other}"
                            )));
                        }
                    }
                }
                b'S' => {
                    if let Some((k, v)) = parse_param_status(&body) {
                        self.server_params.insert(k, v);
                    }
                }
                b'K' | b'N' => {
                    // BackendKeyData or NoticeResponse: safe to ignore during startup.
                }
                b'E' => {
                    let msg = parse_error_response(&body);
                    return Err(DbError::Auth(msg));
                }
                b'Z' => {
                    // ReadyForQuery
                    return Ok(());
                }
                other => {
                    return Err(DbError::Protocol(format!(
                        "unexpected PostgreSQL startup message tag `{}` ({other})",
                        other as char
                    )));
                }
            }
        }
    }

    fn run_extended_query<F>(
        &mut self,
        sql: &str,
        params: &[SqlParam],
        mut on_row: F,
    ) -> Result<(Vec<PgFieldDesc>, u64), DbError>
    where
        F: FnMut(&[PgFieldDesc], &[Option<&[u8]>]) -> Result<(), DbError>,
    {
        let mut wire = Vec::new();
        // 1. Parse ('P'): unnamed statement, SQL, 0 explicit param OIDs (server infers types).
        {
            let mut p = Vec::with_capacity(sql.len() + 4);
            p.push(0); // unnamed statement ""
            push_cstr(&mut p, sql)?;
            p.extend_from_slice(&0i16.to_be_bytes());
            append_tagged(&mut wire, b'P', &p)?;
        }
        // 2. Bind ('B'): unnamed portal & statement, typed text/binary param encodings.
        {
            let mut b = Vec::new();
            b.push(0); // portal ""
            b.push(0); // stmt ""
            let n_params = i16::try_from(params.len())
                .map_err(|_| DbError::Query("too many SQL parameters (> i16::MAX)".to_string()))?;
            // Parameter format codes: 1 (binary) for Bytes, 0 (text) for all other types.
            b.extend_from_slice(&n_params.to_be_bytes());
            for param in params {
                let fmt: i16 = if matches!(param, SqlParam::Bytes(_)) {
                    1
                } else {
                    0
                };
                b.extend_from_slice(&fmt.to_be_bytes());
            }
            // Parameter values.
            b.extend_from_slice(&n_params.to_be_bytes());
            for param in params {
                match encode_pg_param(param) {
                    None => b.extend_from_slice(&(-1i32).to_be_bytes()),
                    Some(bytes) => {
                        let len = i32::try_from(bytes.len()).map_err(|_| {
                            DbError::Query("parameter payload exceeds i32::MAX".to_string())
                        })?;
                        b.extend_from_slice(&len.to_be_bytes());
                        b.extend_from_slice(&bytes);
                    }
                }
            }
            // Result format codes: 1 code = 0 (text format for all columns).
            b.extend_from_slice(&1i16.to_be_bytes());
            b.extend_from_slice(&0i16.to_be_bytes());
            append_tagged(&mut wire, b'B', &b)?;
        }
        // 3. Describe ('D') portal "".
        {
            append_tagged(&mut wire, b'D', &[b'P', 0])?;
        }
        // 4. Execute ('E') portal "", max_rows = 0 (all rows).
        {
            let mut e = Vec::with_capacity(5);
            e.push(0);
            e.extend_from_slice(&0i32.to_be_bytes());
            append_tagged(&mut wire, b'E', &e)?;
        }
        // 5. Sync ('S').
        append_tagged(&mut wire, b'S', &[])?;

        self.transport
            .write_all(&wire)
            .map_err(|e| DbError::Io(format!("postgres extended query write failed: {e}")))?;
        self.transport
            .flush()
            .map_err(|e| DbError::Io(format!("postgres extended query flush failed: {e}")))?;

        let mut fields: Vec<PgFieldDesc> = Vec::new();
        let mut affected: u64 = 0;
        let mut deferred_err: Option<DbError> = None;

        loop {
            let (tag, body) = self.read_message()?;
            match tag {
                b'1' | b'2' | b'3' | b'n' | b'I' | b'N' | b'A' => {
                    // ParseComplete, BindComplete, CloseComplete, NoData, EmptyQueryResponse, Notice, Notification
                }
                b'S' => {
                    if let Some((k, v)) = parse_param_status(&body) {
                        self.server_params.insert(k, v);
                    }
                }
                b'T' => {
                    fields = parse_row_description(&body)?;
                }
                b'D' => {
                    if deferred_err.is_none() {
                        let raw_cells = parse_data_row(&body)?;
                        if let Err(e) = on_row(&fields, &raw_cells) {
                            deferred_err = Some(e);
                        }
                    }
                }
                b'C' => {
                    let cmd_tag = parse_single_cstr(&body);
                    affected = parse_command_complete_rows(&cmd_tag);
                }
                b'E' => {
                    let msg = parse_error_response(&body);
                    if deferred_err.is_none() {
                        deferred_err = Some(DbError::Query(msg));
                    }
                }
                b'Z' => {
                    // ReadyForQuery: protocol stream is now cleanly synchronized.
                    if let Some(e) = deferred_err {
                        return Err(e);
                    }
                    return Ok((fields, affected));
                }
                other => {
                    return Err(DbError::Protocol(format!(
                        "unexpected PostgreSQL message tag `{}` ({other})",
                        other as char
                    )));
                }
            }
        }
    }
}

impl Drop for PostgresDriver {
    fn drop(&mut self) {
        // Best-effort Terminate ('X') frame; ignore all I/O errors so Drop never panics.
        let terminate = [b'X', 0, 0, 0, 4];
        let _ = self.transport.write_all(&terminate);
        let _ = self.transport.flush();
    }
}

impl DbConnection for PostgresDriver {
    fn dialect(&self) -> SqlDialect {
        SqlDialect::Postgres
    }

    fn query_rows(
        &mut self,
        sql: &str,
        params: &[SqlParam],
        expected_schema: &TableTy,
    ) -> Result<TableVal, DbError> {
        let mut rows = Vec::new();
        let mut checked_header = false;

        let (fields, _) = self.run_extended_query(sql, params, |fields, raw_cells| {
            if !checked_header {
                validate_pg_schema(fields, expected_schema)?;
                checked_header = true;
            }
            let cells = decode_pg_row(fields, raw_cells, expected_schema)?;
            rows.push(make_table_row(cells));
            Ok(())
        })?;

        if !checked_header && !fields.is_empty() {
            validate_pg_schema(&fields, expected_schema)?;
        }

        Ok(TableVal {
            cols: expected_schema.cols.clone(),
            rows,
        })
    }

    fn query_batches(
        &mut self,
        sql: &str,
        params: &[SqlParam],
        expected_schema: &TableTy,
        batch_size: usize,
    ) -> Result<VmTable, DbError> {
        let mut builder = ColumnarBatchBuilder::new(expected_schema.cols.clone(), batch_size);
        let mut checked_header = false;

        let (fields, _) = self.run_extended_query(sql, params, |fields, raw_cells| {
            if !checked_header {
                validate_pg_schema(fields, expected_schema)?;
                checked_header = true;
            }
            let cells = decode_pg_row(fields, raw_cells, expected_schema)?;
            builder.push_row(cells)
        })?;

        if !checked_header && !fields.is_empty() {
            validate_pg_schema(&fields, expected_schema)?;
        }

        Ok(builder.finish())
    }

    fn introspect_schema(&mut self, db_name: &str) -> Result<LockedDb, DbError> {
        self.introspect_schema_with_schemas(db_name, &[String::from("public")])
    }

    fn introspect_schema_with_schemas(
        &mut self,
        db_name: &str,
        schemas: &[String],
    ) -> Result<LockedDb, DbError> {
        Self::introspect_schema_with_schemas(self, db_name, schemas)
    }

    fn upsert_table(
        &mut self,
        table: &str,
        key_col: &str,
        data: &TableVal,
        dry_run: bool,
    ) -> Result<UpsertDiff, DbError> {
        if data.cols.is_empty() {
            return Err(DbError::Query(
                "cannot upsert table with zero columns".to_string(),
            ));
        }
        let key_idx = data
            .cols
            .iter()
            .position(|c| c.name == key_col)
            .ok_or_else(|| {
                DbError::Query(format!(
                    "upsert key column `{key_col}` not found in table `{table}`"
                ))
            })?;

        let quoted_table = quote_sql_table_ref(table);
        let quoted_cols: Vec<String> = data.cols.iter().map(|c| quote_sql_ident(&c.name)).collect();
        let quoted_key = quote_sql_ident(key_col);

        let expected_schema = TableTy {
            cols: data.cols.clone(),
            ..TableTy::default()
        };
        let select_sql = format!(
            "SELECT {} FROM {quoted_table} WHERE {quoted_key} = $1",
            quoted_cols.join(", ")
        );

        let diff = compute_upsert_diff(table, key_idx, data, |key_val| {
            let key_param = SqlParam::from_val(key_val)?;
            let tv = self.query_rows(&select_sql, &[key_param], &expected_schema)?;
            Ok(tv.rows.into_iter().next().map(|r| r.cells))
        })?;

        if dry_run || data.rows.is_empty() {
            return Ok(diff);
        }

        let placeholders: Vec<String> = (1..=data.cols.len()).map(|i| format!("${i}")).collect();
        let update_assignments: Vec<String> = data
            .cols
            .iter()
            .filter(|c| c.name != key_col)
            .map(|c| {
                let q = quote_sql_ident(&c.name);
                format!("{q} = EXCLUDED.{q}")
            })
            .collect();
        let upsert_sql = if update_assignments.is_empty() {
            format!(
                "INSERT INTO {quoted_table} ({}) VALUES ({}) ON CONFLICT ({quoted_key}) DO NOTHING",
                quoted_cols.join(", "),
                placeholders.join(", ")
            )
        } else {
            format!(
                "INSERT INTO {quoted_table} ({}) VALUES ({}) \
                 ON CONFLICT ({quoted_key}) DO UPDATE SET {}",
                quoted_cols.join(", "),
                placeholders.join(", "),
                update_assignments.join(", ")
            )
        };

        self.execute("BEGIN", &[])?;
        let tx_res: Result<(), DbError> = (|| {
            for row in &data.rows {
                let mut params = Vec::with_capacity(row.cells.len());
                for cell in &row.cells {
                    params.push(SqlParam::from_val(cell)?);
                }
                self.execute(&upsert_sql, &params)?;
            }
            Ok(())
        })();

        match tx_res {
            Ok(()) => {
                self.execute("COMMIT", &[])?;
                Ok(diff)
            }
            Err(e) => {
                let _ = self.execute("ROLLBACK", &[]);
                Err(e)
            }
        }
    }

    fn execute(&mut self, sql: &str, params: &[SqlParam]) -> Result<u64, DbError> {
        let (_, affected) = self.run_extended_query(sql, params, |_, _| Ok(()))?;
        Ok(affected)
    }
}

// ===========================================================================
// TCP + TLS Handshake Helpers
// ===========================================================================

fn connect_tcp(uri: &PostgresUri) -> Result<TcpStream, DbError> {
    let addr_spec = (uri.host.as_str(), uri.port);
    let tcp = if let Some(secs) = uri.connect_timeout_secs {
        let timeout = Duration::from_secs(secs.max(1));
        let mut addrs = addr_spec.to_socket_addrs().map_err(|e| {
            DbError::Connection(format!("DNS resolution failed for `{}`: {e}", uri.host))
        })?;
        let mut last_err = None;
        let mut connected = None;
        for addr in addrs.by_ref() {
            match TcpStream::connect_timeout(&addr, timeout) {
                Ok(s) => {
                    connected = Some(s);
                    break;
                }
                Err(e) => last_err = Some(e),
            }
        }
        connected.ok_or_else(|| {
            DbError::Connection(format!(
                "failed to connect to {}:{}: {}",
                uri.host,
                uri.port,
                last_err.map_or_else(|| "no resolved addresses".to_string(), |e| e.to_string())
            ))
        })?
    } else {
        TcpStream::connect(addr_spec).map_err(|e| {
            DbError::Connection(format!(
                "failed to connect to {}:{}: {e}",
                uri.host, uri.port
            ))
        })?
    };
    let _ = tcp.set_nodelay(true);
    Ok(tcp)
}

fn negotiate_tls(mut tcp: TcpStream, uri: &PostgresUri) -> Result<(PgTransport, bool), DbError> {
    if uri.sslmode == SslMode::Disable {
        return Ok((PgTransport::Plain(tcp), false));
    }

    // PostgreSQL SSLRequest: Int32(8), Int32(80877103).
    let mut req = [0u8; 8];
    req[0..4].copy_from_slice(&8i32.to_be_bytes());
    req[4..8].copy_from_slice(&PG_SSL_REQUEST_CODE.to_be_bytes());
    tcp.write_all(&req)
        .map_err(|e| DbError::Io(format!("failed to send SSLRequest: {e}")))?;
    tcp.flush()
        .map_err(|e| DbError::Io(format!("failed to flush SSLRequest: {e}")))?;

    let mut resp = [0u8; 1];
    tcp.read_exact(&mut resp)
        .map_err(|e| DbError::Io(format!("failed to read SSLRequest response: {e}")))?;

    match resp[0] {
        b'S' => {
            let tls_cfg = match uri.sslmode {
                SslMode::Disable => unreachable!("handled above"),
                SslMode::Prefer | SslMode::Require => TlsClientConfig {
                    verify_peer: false,
                    verify_hostname: false,
                    ca_cert_path: None,
                },
                SslMode::VerifyCa => TlsClientConfig {
                    verify_peer: true,
                    verify_hostname: false,
                    ca_cert_path: uri.sslrootcert.clone(),
                },
                SslMode::VerifyFull => TlsClientConfig {
                    verify_peer: true,
                    verify_hostname: true,
                    ca_cert_path: uri.sslrootcert.clone(),
                },
            };
            let tls = TlsStream::connect(tcp, &uri.host, &tls_cfg)
                .map_err(|e| DbError::Tls(e.to_string()))?;
            Ok((PgTransport::Tls(tls), true))
        }
        b'N' => {
            if uri.sslmode == SslMode::Prefer {
                Ok((PgTransport::Plain(tcp), false))
            } else {
                Err(DbError::Tls(format!(
                    "PostgreSQL server rejected TLS upgrade (sslmode={:?})",
                    uri.sslmode
                )))
            }
        }
        other => Err(DbError::Protocol(format!(
            "unexpected byte 0x{other:02x} in response to PostgreSQL SSLRequest"
        ))),
    }
}

// ===========================================================================
// Wire Frame Helpers & OID Decoding
// ===========================================================================

fn parse_pg_frame_header(hdr: [u8; 5]) -> Result<(u8, usize), DbError> {
    let tag = hdr[0];
    let len_i32 = i32::from_be_bytes([hdr[1], hdr[2], hdr[3], hdr[4]]);
    if len_i32 < 4 {
        return Err(DbError::Protocol(format!(
            "invalid PostgreSQL frame length {len_i32} for tag `{}`",
            tag as char
        )));
    }
    let body_len = (len_i32 - 4) as usize;
    if body_len > MAX_WIRE_MESSAGE_BYTES {
        return Err(DbError::Protocol(format!(
            "PostgreSQL frame length {body_len} exceeds limit {MAX_WIRE_MESSAGE_BYTES}"
        )));
    }
    Ok((tag, body_len))
}

/// Parse a single tagged PostgreSQL v3.0 wire frame (`tag: u8 || len: i32_be || payload`)
/// from an in-memory byte slice, reusing the exact production header validation.
///
/// # Errors
/// Returns [`DbError::Protocol`] if the buffer is shorter than 5 bytes, the declared frame length
/// is `< 4` or exceeds `MAX_WIRE_MESSAGE_BYTES`, or the payload is truncated.
pub fn parse_pg_wire_frame(bytes: &[u8]) -> Result<(u8, Vec<u8>), DbError> {
    if bytes.len() < 5 {
        return Err(DbError::Protocol(
            "truncated PostgreSQL wire frame header".to_string(),
        ));
    }
    let hdr = [bytes[0], bytes[1], bytes[2], bytes[3], bytes[4]];
    let (tag, body_len) = parse_pg_frame_header(hdr)?;
    if bytes.len() - 5 < body_len {
        return Err(DbError::Protocol(format!(
            "truncated PostgreSQL wire frame body (expected {body_len} bytes, got {})",
            bytes.len() - 5
        )));
    }
    Ok((tag, bytes[5..5 + body_len].to_vec()))
}

/// Safe in-process fuzz entrypoint exercising every PostgreSQL v3.0 message payload parser,
/// SCRAM/Base64/interval/bytea parser, and binary/text OID cell decoder across all Dana
/// [`ScalarTy`]s and PostgreSQL OIDs.
pub fn fuzz_decode_pg_payload(tag: u8, payload: &[u8]) {
    const ALL_OIDS: &[u32] = &[
        0,
        oid::BOOL,
        oid::BYTEA,
        oid::CHAR,
        oid::NAME,
        oid::INT2,
        oid::INT4,
        oid::INT8,
        oid::FLOAT4,
        oid::FLOAT8,
        oid::TEXT,
        oid::JSON,
        oid::VARCHAR,
        oid::BPCHAR,
        oid::DATE,
        oid::TIMESTAMP,
        oid::TIMESTAMPTZ,
        oid::INTERVAL,
        oid::NUMERIC,
        oid::UUID,
        oid::JSONB,
        999_999,
    ];
    let all_tys = [
        ScalarTy::Unit,
        ScalarTy::Bool,
        ScalarTy::Int,
        ScalarTy::Decimal,
        ScalarTy::Float,
        ScalarTy::Text,
        ScalarTy::Bytes,
        ScalarTy::Date,
        ScalarTy::Timestamp,
        ScalarTy::Duration,
        ScalarTy::Data("FuzzAdt".to_string()),
    ];

    if let Ok(fields) = parse_row_description(payload) {
        for f in fields.iter().take(8) {
            for ty in &all_tys {
                let _ = oid_compatible_with_scalar(f.type_oid, ty);
            }
        }
        let cols: Vec<crate::core::syntax::ColSpec> = fields
            .iter()
            .take(8)
            .enumerate()
            .map(|(idx, f)| crate::core::syntax::ColSpec {
                name: f.name.clone(),
                ty: all_tys[idx % all_tys.len()].clone(),
                tags: TagSet::empty(),
                bucketed: false,
                agg_kind: crate::core::syntax::AggKind::Raw,
            })
            .collect();
        let expected = TableTy {
            cols,
            ..TableTy::default()
        };
        let _ = validate_pg_schema(&fields, &expected);
    }

    if let Ok(cells) = parse_data_row(payload) {
        for (idx, cell) in cells.iter().take(8).enumerate() {
            if let Some(raw) = cell {
                let oid_val = ALL_OIDS[idx % ALL_OIDS.len()];
                let ty = &all_tys[idx % all_tys.len()];
                let _ = decode_pg_binary(oid_val, raw, "fuzz_col", ty);
                let _ = decode_pg_text(oid_val, raw, "fuzz_col", ty);
                let field_bin = PgFieldDesc {
                    name: "fuzz_col".to_string(),
                    type_oid: oid_val,
                    format_code: 1,
                };
                let _ = decode_pg_cell(
                    &field_bin,
                    Some(raw),
                    "fuzz_col",
                    &ScalarTy::Option(Box::new(ty.clone())),
                );
            }
        }
    }

    let _ = parse_error_response(payload);
    let _ = parse_param_status(payload);
    let _ = parse_cstr_list(payload);
    let cmd = parse_single_cstr(payload);
    let _ = parse_command_complete_rows(&cmd);

    if tag == b'R' && payload.len() >= 4 {
        let rest = &payload[4..];
        let _ = parse_cstr_list(rest);
        if let Ok(s) = std::str::from_utf8(rest) {
            let _ = parse_scram_server_first(s, "clientnonce");
            let _ = verify_scram_server_final(s, &[0u8; 32]);
        }
    }

    if let Ok(s) = std::str::from_utf8(payload) {
        let _ = parse_scram_server_first(s, "clientnonce");
        let _ = verify_scram_server_final(s, &[0u8; 32]);
        let _ = base64_decode(s);
        let _ = parse_pg_interval_text(s, "fuzz_col");
        let _ = decode_pg_bytea_text(s, "fuzz_col");
    }

    let sel_oid = ALL_OIDS[usize::from(tag) % ALL_OIDS.len()];
    for ty in &all_tys {
        let _ = decode_pg_binary(sel_oid, payload, "fuzz_col", ty);
        let _ = decode_pg_text(sel_oid, payload, "fuzz_col", ty);
    }
    let _ = decode_pg_binary(oid::INTERVAL, payload, "fuzz_col", &ScalarTy::Duration);
}

fn push_cstr(buf: &mut Vec<u8>, s: &str) -> Result<(), DbError> {
    if s.as_bytes().contains(&0) {
        return Err(DbError::Protocol(
            "PostgreSQL wire string contains interior NUL byte".to_string(),
        ));
    }
    buf.extend_from_slice(s.as_bytes());
    buf.push(0);
    Ok(())
}

fn append_tagged(out: &mut Vec<u8>, tag: u8, payload: &[u8]) -> Result<(), DbError> {
    let len = i32::try_from(payload.len() + 4)
        .map_err(|_| DbError::Protocol("outgoing frame exceeds i32::MAX".to_string()))?;
    out.push(tag);
    out.extend_from_slice(&len.to_be_bytes());
    out.extend_from_slice(payload);
    Ok(())
}

fn parse_cstr_list(bytes: &[u8]) -> Result<Vec<String>, DbError> {
    let mut out = Vec::new();
    let mut start = 0;
    while start < bytes.len() {
        let Some(rel_nul) = bytes[start..].iter().position(|&b| b == 0) else {
            return Err(DbError::Protocol(
                "unterminated C string list in PostgreSQL message".to_string(),
            ));
        };
        if rel_nul == 0 {
            break;
        }
        let s = std::str::from_utf8(&bytes[start..start + rel_nul])
            .map_err(|_| DbError::Protocol("invalid UTF-8 in C string list".to_string()))?;
        out.push(s.to_string());
        start += rel_nul + 1;
    }
    Ok(out)
}

fn parse_single_cstr(bytes: &[u8]) -> String {
    let end = bytes.iter().position(|&b| b == 0).unwrap_or(bytes.len());
    String::from_utf8_lossy(&bytes[..end]).into_owned()
}

fn parse_param_status(bytes: &[u8]) -> Option<(String, String)> {
    let nul1 = bytes.iter().position(|&b| b == 0)?;
    let key = String::from_utf8_lossy(&bytes[..nul1]).into_owned();
    let rest = &bytes[nul1 + 1..];
    let nul2 = rest.iter().position(|&b| b == 0).unwrap_or(rest.len());
    let val = String::from_utf8_lossy(&rest[..nul2]).into_owned();
    Some((key, val))
}

fn parse_error_response(bytes: &[u8]) -> String {
    let mut severity = None;
    let mut code = None;
    let mut message = None;
    let mut detail = None;
    let mut i = 0;
    while i < bytes.len() {
        let field_type = bytes[i];
        i += 1;
        if field_type == 0 {
            break;
        }
        let nul = bytes[i..]
            .iter()
            .position(|&b| b == 0)
            .unwrap_or(bytes.len() - i);
        let val = String::from_utf8_lossy(&bytes[i..i + nul]).into_owned();
        i += nul + 1;
        match field_type {
            b'S' | b'V' => severity = Some(val),
            b'C' => code = Some(val),
            b'M' => message = Some(val),
            b'D' => detail = Some(val),
            _ => {}
        }
    }
    let mut out = String::new();
    if let Some(sev) = severity {
        out.push_str(&sev);
        out.push_str(": ");
    }
    if let Some(msg) = message {
        out.push_str(&msg);
    } else {
        out.push_str("PostgreSQL server error");
    }
    if let Some(c) = code {
        out.push_str(" [SQLSTATE ");
        out.push_str(&c);
        out.push(']');
    }
    if let Some(d) = detail {
        out.push_str(" (");
        out.push_str(&d);
        out.push(')');
    }
    out
}

fn parse_row_description(bytes: &[u8]) -> Result<Vec<PgFieldDesc>, DbError> {
    if bytes.len() < 2 {
        return Err(DbError::Protocol("truncated RowDescription".to_string()));
    }
    let count = i16::from_be_bytes([bytes[0], bytes[1]]);
    if count < 0 {
        return Err(DbError::Protocol(format!(
            "negative column count {count} in RowDescription"
        )));
    }
    let mut pos = 2usize;
    let mut fields = Vec::with_capacity((count as usize).min(bytes.len() / 19));
    for _ in 0..count {
        let Some(rel_nul) = bytes[pos..].iter().position(|&b| b == 0) else {
            return Err(DbError::Protocol(
                "unterminated column name in RowDescription".to_string(),
            ));
        };
        let name = String::from_utf8_lossy(&bytes[pos..pos + rel_nul]).into_owned();
        pos += rel_nul + 1;
        if pos + 18 > bytes.len() {
            return Err(DbError::Protocol(
                "truncated field descriptor in RowDescription".to_string(),
            ));
        }
        // table_oid (4), col_attr (2), type_oid (4), type_size (2), type_mod (4), format_code (2)
        let type_oid = u32::from_be_bytes([
            bytes[pos + 6],
            bytes[pos + 7],
            bytes[pos + 8],
            bytes[pos + 9],
        ]);
        let format_code = i16::from_be_bytes([bytes[pos + 16], bytes[pos + 17]]);
        pos += 18;
        fields.push(PgFieldDesc {
            name,
            type_oid,
            format_code,
        });
    }
    Ok(fields)
}

fn parse_data_row(bytes: &[u8]) -> Result<Vec<Option<&[u8]>>, DbError> {
    if bytes.len() < 2 {
        return Err(DbError::Protocol("truncated DataRow".to_string()));
    }
    let count = i16::from_be_bytes([bytes[0], bytes[1]]);
    if count < 0 {
        return Err(DbError::Protocol(format!(
            "negative field count {count} in DataRow"
        )));
    }
    let mut pos = 2usize;
    let mut out = Vec::with_capacity((count as usize).min(bytes.len() / 4));
    for _ in 0..count {
        if pos + 4 > bytes.len() {
            return Err(DbError::Protocol(
                "truncated DataRow field length".to_string(),
            ));
        }
        let len = i32::from_be_bytes([bytes[pos], bytes[pos + 1], bytes[pos + 2], bytes[pos + 3]]);
        pos += 4;
        if len == -1 {
            out.push(None);
        } else if len < 0 {
            return Err(DbError::Protocol(format!(
                "invalid DataRow field length {len}"
            )));
        } else {
            let ulen = len as usize;
            let Some(end) = pos.checked_add(ulen) else {
                return Err(DbError::Protocol(
                    "DataRow field length overflow".to_string(),
                ));
            };
            if end > bytes.len() {
                return Err(DbError::Protocol(
                    "truncated DataRow field payload".to_string(),
                ));
            }
            out.push(Some(&bytes[pos..end]));
            pos = end;
        }
    }
    Ok(out)
}

fn parse_command_complete_rows(tag: &str) -> u64 {
    tag.split_whitespace()
        .last()
        .and_then(|tok| tok.parse::<u64>().ok())
        .unwrap_or(0)
}

fn encode_pg_param(param: &SqlParam) -> Option<Vec<u8>> {
    match param {
        SqlParam::Null => None,
        SqlParam::Bool(b) => Some(if *b {
            b"true".to_vec()
        } else {
            b"false".to_vec()
        }),
        SqlParam::Int(i) => Some(i.to_string().into_bytes()),
        SqlParam::Decimal(d) => Some(format_decimal_canonical(d).into_bytes()),
        SqlParam::Float(f) => Some(f.to_f64().to_string().into_bytes()),
        SqlParam::Text(s) => Some(s.as_bytes().to_vec()),
        SqlParam::Bytes(bs) => Some(bs.clone()),
        SqlParam::Date(days) => Some(format_iso_date(*days).into_bytes()),
        SqlParam::Timestamp(us) => Some(format_iso_timestamp(*us).into_bytes()),
        SqlParam::Duration(us) => Some(format_pg_interval(*us).into_bytes()),
    }
}

fn format_pg_interval(micros: i64) -> String {
    let sign = if micros < 0 { "-" } else { "" };
    let abs = micros.unsigned_abs();
    let secs = abs / 1_000_000;
    let rem_us = abs % 1_000_000;
    if rem_us == 0 {
        format!("{sign}{secs} seconds")
    } else {
        format!("{sign}{secs}.{rem_us:06} seconds")
    }
}

fn validate_pg_schema(fields: &[PgFieldDesc], expected: &TableTy) -> Result<(), DbError> {
    if fields.len() != expected.cols.len() {
        return Err(DbError::SchemaDrift(format!(
            "PostgreSQL query returned {} columns, expected {}",
            fields.len(),
            expected.cols.len()
        )));
    }
    for (field, spec) in fields.iter().zip(&expected.cols) {
        let mut base = &spec.ty;
        while let ScalarTy::Option(inner) = base {
            base = inner;
        }
        if !oid_compatible_with_scalar(field.type_oid, base) {
            return Err(DbError::SchemaDrift(format!(
                "column `{}` (wire `{}`) OID {} incompatible with expected Dana type {:?}",
                spec.name, field.name, field.type_oid, spec.ty
            )));
        }
    }
    Ok(())
}

fn oid_compatible_with_scalar(type_oid: u32, base: &ScalarTy) -> bool {
    if type_oid == 0 {
        return true;
    }
    match base {
        ScalarTy::Unit => true,
        ScalarTy::Bool => matches!(type_oid, oid::BOOL | oid::INT2 | oid::INT4 | oid::INT8),
        ScalarTy::Int => matches!(type_oid, oid::INT2 | oid::INT4 | oid::INT8),
        ScalarTy::Decimal => matches!(
            type_oid,
            oid::NUMERIC
                | oid::INT2
                | oid::INT4
                | oid::INT8
                | oid::FLOAT4
                | oid::FLOAT8
                | oid::TEXT
        ),
        ScalarTy::Float => matches!(
            type_oid,
            oid::FLOAT4 | oid::FLOAT8 | oid::INT2 | oid::INT4 | oid::INT8 | oid::NUMERIC
        ),
        ScalarTy::Text => {
            matches!(
                type_oid,
                oid::TEXT
                    | oid::VARCHAR
                    | oid::BPCHAR
                    | oid::CHAR
                    | oid::NAME
                    | oid::JSON
                    | oid::JSONB
                    | oid::UUID
            ) || type_oid >= PG_FIRST_NORMAL_OBJECT_ID
        }
        ScalarTy::Bytes => type_oid == oid::BYTEA,
        ScalarTy::Date => matches!(type_oid, oid::DATE | oid::TEXT | oid::VARCHAR),
        ScalarTy::Timestamp => matches!(
            type_oid,
            oid::TIMESTAMP | oid::TIMESTAMPTZ | oid::TEXT | oid::VARCHAR
        ),
        ScalarTy::Duration => matches!(
            type_oid,
            oid::INTERVAL | oid::INT8 | oid::INT4 | oid::TEXT | oid::VARCHAR
        ),
        ScalarTy::Data(_) | ScalarTy::Option(_) => false,
    }
}

fn decode_pg_row(
    fields: &[PgFieldDesc],
    raw_cells: &[Option<&[u8]>],
    expected: &TableTy,
) -> Result<Vec<Val>, DbError> {
    if raw_cells.len() != expected.cols.len() {
        return Err(DbError::SchemaDrift(format!(
            "PostgreSQL DataRow had {} cells, expected {}",
            raw_cells.len(),
            expected.cols.len()
        )));
    }
    let mut out = Vec::with_capacity(expected.cols.len());
    for ((field, cell), spec) in fields.iter().zip(raw_cells).zip(&expected.cols) {
        out.push(decode_pg_cell(field, *cell, &spec.name, &spec.ty)?);
    }
    Ok(out)
}

fn decode_pg_cell(
    field: &PgFieldDesc,
    raw: Option<&[u8]>,
    col_name: &str,
    ty: &ScalarTy,
) -> Result<Val, DbError> {
    if let ScalarTy::Option(inner) = ty {
        return match raw {
            None => Ok(Val::OptNone),
            Some(bytes) => {
                let v = decode_pg_cell(field, Some(bytes), col_name, inner)?;
                Ok(Val::OptSome(Box::new(v)))
            }
        };
    }
    let Some(bytes) = raw else {
        return Err(DbError::SchemaDrift(format!(
            "unexpected NULL in non-nullable column `{col_name}` (expected {ty:?})"
        )));
    };
    if field.format_code == 1 {
        decode_pg_binary(field.type_oid, bytes, col_name, ty)
    } else {
        decode_pg_text(field.type_oid, bytes, col_name, ty)
    }
}

fn decode_pg_binary(
    type_oid: u32,
    bytes: &[u8],
    col_name: &str,
    ty: &ScalarTy,
) -> Result<Val, DbError> {
    match ty {
        ScalarTy::Unit => Ok(Val::Unit),
        ScalarTy::Bool => {
            if bytes.len() != 1 {
                return Err(DbError::TypeConversion(format!(
                    "column `{col_name}` binary BOOL expected 1 byte, got {}",
                    bytes.len()
                )));
            }
            Ok(Val::Bool(bytes[0] != 0))
        }
        ScalarTy::Int => {
            let n = match bytes.len() {
                2 => i64::from(i16::from_be_bytes([bytes[0], bytes[1]])),
                4 => i64::from(i32::from_be_bytes([bytes[0], bytes[1], bytes[2], bytes[3]])),
                8 => i64::from_be_bytes([
                    bytes[0], bytes[1], bytes[2], bytes[3], bytes[4], bytes[5], bytes[6], bytes[7],
                ]),
                n => {
                    return Err(DbError::TypeConversion(format!(
                        "column `{col_name}` binary INT expected 2/4/8 bytes, got {n}"
                    )));
                }
            };
            Ok(Val::Int(BigInt::from(n)))
        }
        ScalarTy::Float => {
            let f = match bytes.len() {
                4 => f64::from(f32::from_be_bytes([bytes[0], bytes[1], bytes[2], bytes[3]])),
                8 => f64::from_be_bytes([
                    bytes[0], bytes[1], bytes[2], bytes[3], bytes[4], bytes[5], bytes[6], bytes[7],
                ]),
                n => {
                    return Err(DbError::TypeConversion(format!(
                        "column `{col_name}` binary FLOAT expected 4/8 bytes, got {n}"
                    )));
                }
            };
            Ok(Val::Float(Float64::from_f64(f)))
        }
        ScalarTy::Bytes => Ok(Val::Bytes(bytes.to_vec())),
        ScalarTy::Text => {
            if type_oid == oid::JSONB && bytes.first() == Some(&1) {
                let s = std::str::from_utf8(&bytes[1..]).map_err(|e| {
                    DbError::TypeConversion(format!("column `{col_name}` JSONB UTF-8: {e}"))
                })?;
                return Ok(Val::Text(s.to_string()));
            }
            if type_oid == oid::UUID && bytes.len() == 16 {
                return Ok(Val::Text(format!(
                    "{:02x}{:02x}{:02x}{:02x}-{:02x}{:02x}-{:02x}{:02x}-{:02x}{:02x}-{:02x}{:02x}{:02x}{:02x}{:02x}{:02x}",
                    bytes[0],
                    bytes[1],
                    bytes[2],
                    bytes[3],
                    bytes[4],
                    bytes[5],
                    bytes[6],
                    bytes[7],
                    bytes[8],
                    bytes[9],
                    bytes[10],
                    bytes[11],
                    bytes[12],
                    bytes[13],
                    bytes[14],
                    bytes[15]
                )));
            }
            let s = std::str::from_utf8(bytes)
                .map_err(|e| DbError::TypeConversion(format!("column `{col_name}` UTF-8: {e}")))?;
            Ok(Val::Text(s.to_string()))
        }
        ScalarTy::Date => {
            if bytes.len() != 4 {
                return Err(DbError::TypeConversion(format!(
                    "column `{col_name}` binary DATE expected 4 bytes, got {}",
                    bytes.len()
                )));
            }
            let pg_days = i64::from(i32::from_be_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]));
            Ok(Val::Date(BigInt::from(pg_days + PG_EPOCH_DAYS)))
        }
        ScalarTy::Timestamp => {
            if bytes.len() != 8 {
                return Err(DbError::TypeConversion(format!(
                    "column `{col_name}` binary TIMESTAMP expected 8 bytes, got {}",
                    bytes.len()
                )));
            }
            let pg_us = i64::from_be_bytes([
                bytes[0], bytes[1], bytes[2], bytes[3], bytes[4], bytes[5], bytes[6], bytes[7],
            ]);
            let unix_us = pg_us.checked_add(PG_EPOCH_MICROS).ok_or_else(|| {
                DbError::TypeConversion(format!("column `{col_name}` binary TIMESTAMP overflow"))
            })?;
            Ok(Val::Timestamp(BigInt::from(unix_us)))
        }
        ScalarTy::Duration => {
            if bytes.len() == 16 && type_oid == oid::INTERVAL {
                let us = i64::from_be_bytes([
                    bytes[0], bytes[1], bytes[2], bytes[3], bytes[4], bytes[5], bytes[6], bytes[7],
                ]);
                let days = i64::from(i32::from_be_bytes([
                    bytes[8], bytes[9], bytes[10], bytes[11],
                ]));
                let months = i64::from(i32::from_be_bytes([
                    bytes[12], bytes[13], bytes[14], bytes[15],
                ]));
                let days_us = days.checked_mul(MICROS_PER_DAY);
                let months_us = months
                    .checked_mul(30)
                    .and_then(|m| m.checked_mul(MICROS_PER_DAY));
                let total = days_us
                    .and_then(|d| us.checked_add(d))
                    .and_then(|acc| months_us.and_then(|m| acc.checked_add(m)))
                    .ok_or_else(|| {
                        DbError::TypeConversion(format!(
                            "column `{col_name}` binary INTERVAL overflow"
                        ))
                    })?;
                Ok(Val::Duration(BigInt::from(total)))
            } else if bytes.len() == 8 {
                let us = i64::from_be_bytes([
                    bytes[0], bytes[1], bytes[2], bytes[3], bytes[4], bytes[5], bytes[6], bytes[7],
                ]);
                Ok(Val::Duration(BigInt::from(us)))
            } else {
                Err(DbError::TypeConversion(format!(
                    "column `{col_name}` unsupported binary INTERVAL length {}",
                    bytes.len()
                )))
            }
        }
        ScalarTy::Decimal => decode_pg_text(type_oid, bytes, col_name, ty),
        ScalarTy::Data(name) => Err(DbError::TypeConversion(format!(
            "unsupported ADT `{name}` in binary Postgres decoding"
        ))),
        ScalarTy::Option(_) => Err(DbError::TypeConversion(
            "unreachable nested option".to_string(),
        )),
    }
}

fn decode_pg_text(
    _type_oid: u32,
    bytes: &[u8],
    col_name: &str,
    ty: &ScalarTy,
) -> Result<Val, DbError> {
    let s = std::str::from_utf8(bytes)
        .map_err(|e| DbError::TypeConversion(format!("column `{col_name}` invalid UTF-8: {e}")))?;
    match ty {
        ScalarTy::Unit => Ok(Val::Unit),
        ScalarTy::Bool => match s.trim().to_ascii_lowercase().as_str() {
            "t" | "true" | "1" => Ok(Val::Bool(true)),
            "f" | "false" | "0" => Ok(Val::Bool(false)),
            _ => Err(DbError::TypeConversion(format!(
                "column `{col_name}` invalid Postgres bool `{s}`"
            ))),
        },
        ScalarTy::Int => {
            let n: i64 = s.trim().parse().map_err(|_| {
                DbError::TypeConversion(format!("column `{col_name}` invalid Int `{s}`"))
            })?;
            Ok(Val::Int(BigInt::from(n)))
        }
        ScalarTy::Decimal => {
            let d = parse_decimal_bigint_strict(s.trim())
                .map_err(|e| DbError::TypeConversion(format!("column `{col_name}`: {e}")))?;
            Ok(Val::Decimal(d))
        }
        ScalarTy::Float => {
            let f: f64 = s.trim().parse().map_err(|_| {
                DbError::TypeConversion(format!("column `{col_name}` invalid Float `{s}`"))
            })?;
            Ok(Val::Float(Float64::from_f64(f)))
        }
        ScalarTy::Text => Ok(Val::Text(s.to_string())),
        ScalarTy::Bytes => decode_pg_bytea_text(s, col_name).map(Val::Bytes),
        ScalarTy::Date => {
            let days = parse_iso_date(s.trim())
                .map_err(|e| DbError::TypeConversion(format!("column `{col_name}`: {e}")))?;
            Ok(Val::Date(BigInt::from(days)))
        }
        ScalarTy::Timestamp => {
            let us = parse_iso_timestamp_flexible(s)?;
            Ok(Val::Timestamp(BigInt::from(us)))
        }
        ScalarTy::Duration => {
            let us = parse_pg_interval_text(s.trim(), col_name)?;
            Ok(Val::Duration(BigInt::from(us)))
        }
        ScalarTy::Data(name) => Err(DbError::TypeConversion(format!(
            "unsupported ADT `{name}` in Postgres text decoding"
        ))),
        ScalarTy::Option(_) => Err(DbError::TypeConversion(
            "unreachable nested option".to_string(),
        )),
    }
}

fn decode_pg_bytea_text(s: &str, col_name: &str) -> Result<Vec<u8>, DbError> {
    if let Some(hex) = s.strip_prefix("\\x") {
        if !hex.len().is_multiple_of(2) {
            return Err(DbError::TypeConversion(format!(
                "column `{col_name}` odd-length bytea hex payload"
            )));
        }
        let mut out = Vec::with_capacity(hex.len() / 2);
        let b = hex.as_bytes();
        let mut i = 0;
        while i < b.len() {
            let hi = hex_nibble(b[i]).ok_or_else(|| {
                DbError::TypeConversion(format!("column `{col_name}` invalid bytea hex"))
            })?;
            let lo = hex_nibble(b[i + 1]).ok_or_else(|| {
                DbError::TypeConversion(format!("column `{col_name}` invalid bytea hex"))
            })?;
            out.push((hi << 4) | lo);
            i += 2;
        }
        return Ok(out);
    }
    Ok(s.as_bytes().to_vec())
}

fn parse_pg_interval_text(s: &str, col_name: &str) -> Result<i64, DbError> {
    if let Ok(us) = s.parse::<i64>() {
        return Ok(us);
    }
    // Support `<sec>[.<frac>] second[s]` (our own bind format) and Postgres `HH:MM:SS(.frac)?`.
    if let Some(num_str) = s
        .strip_suffix(" seconds")
        .or_else(|| s.strip_suffix(" second"))
        .or_else(|| s.strip_suffix(" secs"))
        .or_else(|| s.strip_suffix(" sec"))
    {
        return parse_seconds_to_micros(num_str.trim(), col_name);
    }
    let mut total_us = 0i64;
    let mut parts = s.split_whitespace().peekable();
    while let Some(tok) = parts.next() {
        if tok.contains(':') {
            let (neg, rest) = match tok.strip_prefix('-') {
                Some(r) => (true, r),
                None => (false, tok),
            };
            let comps: Vec<&str> = rest.split(':').collect();
            if comps.len() != 3 {
                return Err(DbError::TypeConversion(format!(
                    "column `{col_name}` invalid interval `{s}`"
                )));
            }
            let h: i64 = comps[0].parse().map_err(|_| {
                DbError::TypeConversion(format!("column `{col_name}` invalid interval `{s}`"))
            })?;
            let m: i64 = comps[1].parse().map_err(|_| {
                DbError::TypeConversion(format!("column `{col_name}` invalid interval `{s}`"))
            })?;
            let sec_us = parse_seconds_to_micros(comps[2], col_name)?;
            let h_us = h.checked_mul(MICROS_PER_HOUR);
            let m_us = m.checked_mul(MICROS_PER_MINUTE);
            let mag = h_us
                .and_then(|hu| m_us.and_then(|mu| hu.checked_add(mu)))
                .and_then(|acc| acc.checked_add(sec_us))
                .ok_or_else(|| {
                    DbError::TypeConversion(format!("column `{col_name}` interval overflow `{s}`"))
                })?;
            let signed_mag = if neg {
                mag.checked_neg().ok_or_else(|| {
                    DbError::TypeConversion(format!("column `{col_name}` interval overflow `{s}`"))
                })?
            } else {
                mag
            };
            total_us = total_us.checked_add(signed_mag).ok_or_else(|| {
                DbError::TypeConversion(format!("column `{col_name}` interval overflow `{s}`"))
            })?;
        } else if let Some(unit) = parts.next() {
            let unit_l = unit.to_ascii_lowercase();
            let delta = if unit_l.starts_with("day") {
                let d: i64 = tok.parse().map_err(|_| {
                    DbError::TypeConversion(format!("column `{col_name}` invalid interval `{s}`"))
                })?;
                d.checked_mul(MICROS_PER_DAY).ok_or_else(|| {
                    DbError::TypeConversion(format!("column `{col_name}` interval overflow `{s}`"))
                })?
            } else if unit_l.starts_with("hour") {
                let h: i64 = tok.parse().map_err(|_| {
                    DbError::TypeConversion(format!("column `{col_name}` invalid interval `{s}`"))
                })?;
                h.checked_mul(MICROS_PER_HOUR).ok_or_else(|| {
                    DbError::TypeConversion(format!("column `{col_name}` interval overflow `{s}`"))
                })?
            } else if unit_l.starts_with("min") {
                let m: i64 = tok.parse().map_err(|_| {
                    DbError::TypeConversion(format!("column `{col_name}` invalid interval `{s}`"))
                })?;
                m.checked_mul(MICROS_PER_MINUTE).ok_or_else(|| {
                    DbError::TypeConversion(format!("column `{col_name}` interval overflow `{s}`"))
                })?
            } else if unit_l.starts_with("sec") {
                parse_seconds_to_micros(tok, col_name)?
            } else {
                return Err(DbError::TypeConversion(format!(
                    "column `{col_name}` unsupported interval unit `{unit}` in `{s}`"
                )));
            };
            total_us = total_us.checked_add(delta).ok_or_else(|| {
                DbError::TypeConversion(format!("column `{col_name}` interval overflow `{s}`"))
            })?;
        } else {
            return Err(DbError::TypeConversion(format!(
                "column `{col_name}` invalid interval `{s}`"
            )));
        }
    }
    Ok(total_us)
}

fn parse_seconds_to_micros(s: &str, col_name: &str) -> Result<i64, DbError> {
    let (neg, rest) = match s.strip_prefix('-') {
        Some(r) => (true, r),
        None => (false, s),
    };
    let (whole_s, frac_s) = rest.split_once('.').unwrap_or((rest, ""));
    let whole: i64 = whole_s.parse().map_err(|_| {
        DbError::TypeConversion(format!("column `{col_name}` invalid seconds `{s}`"))
    })?;
    let mut frac_us = 0i64;
    for ch in frac_s.bytes().take(6) {
        if !ch.is_ascii_digit() {
            return Err(DbError::TypeConversion(format!(
                "column `{col_name}` invalid fractional seconds `{s}`"
            )));
        }
        frac_us = frac_us * 10 + i64::from(ch - b'0');
    }
    for _ in frac_s.len()..6 {
        frac_us *= 10;
    }
    let mag = whole
        .checked_mul(MICROS_PER_SECOND)
        .and_then(|w| w.checked_add(frac_us))
        .ok_or_else(|| {
            DbError::TypeConversion(format!("column `{col_name}` seconds overflow `{s}`"))
        })?;
    if neg {
        mag.checked_neg().ok_or_else(|| {
            DbError::TypeConversion(format!("column `{col_name}` seconds overflow `{s}`"))
        })
    } else {
        Ok(mag)
    }
}

fn decode_utf8_cell(cell: Option<&[u8]>, name: &str) -> Result<String, DbError> {
    let bytes = cell.ok_or_else(|| {
        DbError::SchemaDrift(format!("unexpected NULL in information_schema.{name}"))
    })?;
    String::from_utf8(bytes.to_vec())
        .map_err(|e| DbError::SchemaDrift(format!("invalid UTF-8 in {name}: {e}")))
}

/// Map PostgreSQL `information_schema.columns` (`data_type`, `udt_name`) pairs to Dana [`ScalarTy`].
#[must_use]
pub fn map_pg_type_name(data_type: &str, udt_name: &str) -> ScalarTy {
    let dt = data_type.trim().to_ascii_lowercase();
    let udt = udt_name.trim().to_ascii_lowercase();
    match (dt.as_str(), udt.as_str()) {
        ("boolean", _) | (_, "bool") => ScalarTy::Bool,
        ("smallint" | "integer" | "bigint", _) | (_, "int2" | "int4" | "int8") => ScalarTy::Int,
        ("numeric" | "decimal", _) | (_, "numeric") => ScalarTy::Decimal,
        ("real" | "double precision", _) | (_, "float4" | "float8") => ScalarTy::Float,
        ("bytea", _) | (_, "bytea") => ScalarTy::Bytes,
        ("date", _) | (_, "date") => ScalarTy::Date,
        (_, "timestamp" | "timestamptz") => ScalarTy::Timestamp,
        ("interval", _) | (_, "interval") => ScalarTy::Duration,
        (s, _) if s.starts_with("timestamp") => ScalarTy::Timestamp,
        (
            "text" | "character varying" | "character" | "varchar" | "bpchar" | "char" | "citext"
            | "name" | "uuid" | "json" | "jsonb",
            _,
        )
        | (
            _,
            "text" | "varchar" | "bpchar" | "char" | "citext" | "name" | "uuid" | "json" | "jsonb",
        ) => ScalarTy::Text,
        _ => ScalarTy::Text,
    }
}

// ===========================================================================
// Pure-Rust Crypto Helpers: RFC 1321 MD5, PBKDF2-HMAC-SHA256, SCRAM, Base64
// ===========================================================================

/// Pure-Rust RFC 1321 MD5 digest (used exclusively for legacy PostgreSQL `AuthenticationMD5Password`).
#[must_use]
pub fn md5_digest(data: &[u8]) -> [u8; 16] {
    const S: [u32; 64] = [
        7, 12, 17, 22, 7, 12, 17, 22, 7, 12, 17, 22, 7, 12, 17, 22, 5, 9, 14, 20, 5, 9, 14, 20, 5,
        9, 14, 20, 5, 9, 14, 20, 4, 11, 16, 23, 4, 11, 16, 23, 4, 11, 16, 23, 4, 11, 16, 23, 6, 10,
        15, 21, 6, 10, 15, 21, 6, 10, 15, 21, 6, 10, 15, 21,
    ];
    const K: [u32; 64] = [
        0xd76a_a478,
        0xe8c7_b756,
        0x2420_70db,
        0xc1bd_ceee,
        0xf57c_0faf,
        0x4787_c62a,
        0xa830_4613,
        0xfd46_9501,
        0x6980_98d8,
        0x8b44_f7af,
        0xffff_5bb1,
        0x895c_d7be,
        0x6b90_1122,
        0xfd98_7193,
        0xa679_438e,
        0x49b4_0821,
        0xf61e_2562,
        0xc040_b340,
        0x265e_5a51,
        0xe9b6_c7aa,
        0xd62f_105d,
        0x0244_1453,
        0xd8a1_e681,
        0xe7d3_fbc8,
        0x21e1_cde6,
        0xc337_07d6,
        0xf4d5_0d87,
        0x455a_14ed,
        0xa9e3_e905,
        0xfcef_a3f8,
        0x676f_02d9,
        0x8d2a_4c8a,
        0xfffa_3942,
        0x8771_f681,
        0x6d9d_6122,
        0xfde5_380c,
        0xa4be_ea44,
        0x4bde_cfa9,
        0xf6bb_4b60,
        0xbebf_bc70,
        0x289b_7ec6,
        0xeaa1_27fa,
        0xd4ef_3085,
        0x0488_1d05,
        0xd9d4_d039,
        0xe6db_99e5,
        0x1fa2_7cf8,
        0xc4ac_5665,
        0xf429_2244,
        0x432a_ff97,
        0xab94_23a7,
        0xfc93_a039,
        0x655b_59c3,
        0x8f0c_cc92,
        0xffef_f47d,
        0x8584_5dd1,
        0x6fa8_7e4f,
        0xfe2c_e6e0,
        0xa301_4314,
        0x4e08_11a1,
        0xf753_7e82,
        0xbd3a_f235,
        0x2ad7_d2bb,
        0xeb86_d391,
    ];

    let bit_len = (data.len() as u64).wrapping_mul(8);
    let mut padded = data.to_vec();
    padded.push(0x80);
    while padded.len() % 64 != 56 {
        padded.push(0);
    }
    padded.extend_from_slice(&bit_len.to_le_bytes());

    let mut a0: u32 = 0x6745_2301;
    let mut b0: u32 = 0xefcd_ab89;
    let mut c0: u32 = 0x98ba_dcfe;
    let mut d0: u32 = 0x1032_5476;

    for chunk in padded.as_chunks::<64>().0 {
        let mut m = [0u32; 16];
        for (slot, &word) in m.iter_mut().zip(chunk.as_chunks::<4>().0) {
            *slot = u32::from_le_bytes(word);
        }
        let (mut a, mut b, mut c, mut d) = (a0, b0, c0, d0);
        for i in 0..64 {
            let (f, g) = match i {
                0..=15 => ((b & c) | ((!b) & d), i),
                16..=31 => ((d & b) | ((!d) & c), (5 * i + 1) % 16),
                32..=47 => (b ^ c ^ d, (3 * i + 5) % 16),
                _ => (c ^ (b | (!d)), (7 * i) % 16),
            };
            let f_sum = f.wrapping_add(a).wrapping_add(K[i]).wrapping_add(m[g]);
            a = d;
            d = c;
            c = b;
            b = b.wrapping_add(f_sum.rotate_left(S[i]));
        }
        a0 = a0.wrapping_add(a);
        b0 = b0.wrapping_add(b);
        c0 = c0.wrapping_add(c);
        d0 = d0.wrapping_add(d);
    }

    let mut out = [0u8; 16];
    out[0..4].copy_from_slice(&a0.to_le_bytes());
    out[4..8].copy_from_slice(&b0.to_le_bytes());
    out[8..12].copy_from_slice(&c0.to_le_bytes());
    out[12..16].copy_from_slice(&d0.to_le_bytes());
    out
}

/// Compute PostgreSQL `AuthenticationMD5Password` response: `"md5" + hex(md5(hex(md5(pass + user)) + salt))`.
#[must_use]
pub fn pg_md5_password(user: &str, password: &str, salt: [u8; 4]) -> String {
    let mut inner_in = Vec::with_capacity(password.len() + user.len());
    inner_in.extend_from_slice(password.as_bytes());
    inner_in.extend_from_slice(user.as_bytes());
    let inner_hex = to_hex_lower(&md5_digest(&inner_in));

    let mut outer_in = Vec::with_capacity(inner_hex.len() + 4);
    outer_in.extend_from_slice(inner_hex.as_bytes());
    outer_in.extend_from_slice(&salt);
    let outer_hex = to_hex_lower(&md5_digest(&outer_in));
    format!("md5{outer_hex}")
}

/// Compute 32-byte PBKDF2-HMAC-SHA256 (`Hi` in RFC 5802 / RFC 7677 `SCRAM-SHA-256`).
#[must_use]
pub fn scram_pbkdf2_hmac_sha256(password: &[u8], salt: &[u8], iterations: u32) -> [u8; 32] {
    let mut salt_block = Vec::with_capacity(salt.len() + 4);
    salt_block.extend_from_slice(salt);
    salt_block.extend_from_slice(&1u32.to_be_bytes());

    let mut u = hmac_sha256(password, &salt_block);
    let mut acc = u;
    for _ in 1..iterations {
        u = hmac_sha256(password, &u);
        for i in 0..32 {
            acc[i] ^= u[i];
        }
    }
    acc
}

fn generate_scram_nonce() -> String {
    static COUNTER: AtomicU64 = AtomicU64::new(1);
    let mut raw = [0u8; 18];
    let filled = File::open("/dev/urandom")
        .and_then(|mut f| f.read_exact(&mut raw))
        .is_ok();
    if !filled {
        let nanos = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map_or(0u128, |d| d.as_nanos());
        let seq = COUNTER.fetch_add(1, Ordering::Relaxed);
        let pid = std::process::id();
        let mut seed = Vec::with_capacity(28);
        seed.extend_from_slice(&nanos.to_le_bytes());
        seed.extend_from_slice(&seq.to_le_bytes());
        seed.extend_from_slice(&pid.to_le_bytes());
        let h = sha256(&seed);
        raw.copy_from_slice(&h[..18]);
    }
    base64_encode(&raw)
}

fn parse_scram_server_first(
    msg: &str,
    client_nonce: &str,
) -> Result<(String, Vec<u8>, u32), DbError> {
    let mut combined_nonce = None;
    let mut salt_b64 = None;
    let mut iter = None;

    for part in msg.split(',') {
        if let Some(r) = part.strip_prefix("r=") {
            combined_nonce = Some(r.to_string());
        } else if let Some(s) = part.strip_prefix("s=") {
            salt_b64 = Some(s);
        } else if let Some(i) = part.strip_prefix("i=") {
            iter = Some(
                i.parse::<u32>()
                    .map_err(|_| DbError::Auth(format!("invalid SCRAM iteration count `{i}`")))?,
            );
        }
    }

    let r = combined_nonce.ok_or_else(|| {
        DbError::Auth("SCRAM server-first-message missing `r=` nonce".to_string())
    })?;
    if !r.starts_with(client_nonce) || r.len() <= client_nonce.len() {
        return Err(DbError::Auth(
            "SCRAM server nonce does not extend client nonce".to_string(),
        ));
    }
    let s_b64 = salt_b64
        .ok_or_else(|| DbError::Auth("SCRAM server-first-message missing `s=` salt".to_string()))?;
    let salt = base64_decode(s_b64)?;
    let iterations = iter.ok_or_else(|| {
        DbError::Auth("SCRAM server-first-message missing `i=` iteration count".to_string())
    })?;
    if iterations == 0 {
        return Err(DbError::Auth(
            "SCRAM iteration count must be positive".to_string(),
        ));
    }
    Ok((r, salt, iterations))
}

fn verify_scram_server_final(msg: &str, expected: &[u8; 32]) -> Result<(), DbError> {
    let mut verifier_b64 = None;
    for part in msg.split(',') {
        if let Some(e) = part.strip_prefix("e=") {
            return Err(DbError::Auth(format!("SCRAM server rejected auth: {e}")));
        }
        if let Some(v) = part.strip_prefix("v=") {
            verifier_b64 = Some(v);
        }
    }
    let v_b64 = verifier_b64.ok_or_else(|| {
        DbError::Auth("SCRAM server-final-message missing `v=` verifier".to_string())
    })?;
    let actual = base64_decode(v_b64)?;
    if actual.len() != 32 {
        return Err(DbError::Auth(
            "SCRAM server verifier has invalid length".to_string(),
        ));
    }
    let mut diff = 0u8;
    for i in 0..32 {
        diff |= actual[i] ^ expected[i];
    }
    if diff != 0 {
        return Err(DbError::Auth(
            "SCRAM-SHA-256 server signature verification failed".to_string(),
        ));
    }
    Ok(())
}

/// Standard RFC 4648 Base64 encoder.
#[must_use]
pub fn base64_encode(input: &[u8]) -> String {
    const TABLE: &[u8; 64] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
    let mut out = String::with_capacity(input.len().div_ceil(3) * 4);
    for chunk in input.chunks(3) {
        let b0 = u32::from(chunk[0]);
        let b1 = if chunk.len() > 1 {
            u32::from(chunk[1])
        } else {
            0
        };
        let b2 = if chunk.len() > 2 {
            u32::from(chunk[2])
        } else {
            0
        };
        let triple = (b0 << 16) | (b1 << 8) | b2;
        out.push(TABLE[((triple >> 18) & 0x3F) as usize] as char);
        out.push(TABLE[((triple >> 12) & 0x3F) as usize] as char);
        if chunk.len() > 1 {
            out.push(TABLE[((triple >> 6) & 0x3F) as usize] as char);
        } else {
            out.push('=');
        }
        if chunk.len() > 2 {
            out.push(TABLE[(triple & 0x3F) as usize] as char);
        } else {
            out.push('=');
        }
    }
    out
}

/// Standard RFC 4648 Base64 decoder.
///
/// # Errors
/// Returns [`DbError::Auth`] on invalid Base64 characters or padding.
pub fn base64_decode(input: &str) -> Result<Vec<u8>, DbError> {
    let bytes = input.as_bytes();
    if !bytes.len().is_multiple_of(4) {
        return Err(DbError::Auth(format!(
            "invalid base64 length {}",
            bytes.len()
        )));
    }
    let mut out = Vec::with_capacity(bytes.len() / 4 * 3);
    for chunk in bytes.as_chunks::<4>().0 {
        let mut vals = [0u32; 4];
        let mut pad = 0usize;
        for (val, &b) in vals.iter_mut().zip(chunk) {
            if b == b'=' {
                pad += 1;
                *val = 0;
            } else {
                if pad > 0 {
                    return Err(DbError::Auth("invalid base64 padding".to_string()));
                }
                *val = match b {
                    b'A'..=b'Z' => u32::from(b - b'A'),
                    b'a'..=b'z' => u32::from(b - b'a' + 26),
                    b'0'..=b'9' => u32::from(b - b'0' + 52),
                    b'+' => 62,
                    b'/' => 63,
                    _ => {
                        return Err(DbError::Auth(format!("invalid base64 byte 0x{b:02x}")));
                    }
                };
            }
        }
        if pad > 2 {
            return Err(DbError::Auth("excessive base64 padding".to_string()));
        }
        let triple = (vals[0] << 18) | (vals[1] << 12) | (vals[2] << 6) | vals[3];
        out.push(((triple >> 16) & 0xFF) as u8);
        if pad < 2 {
            out.push(((triple >> 8) & 0xFF) as u8);
        }
        if pad < 1 {
            out.push((triple & 0xFF) as u8);
        }
    }
    Ok(out)
}
