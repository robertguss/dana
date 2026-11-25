//! Database drivers, URI parsing, parameterized execution traits, offline `schema.lock`,
//! and privacy-redacted dry-run diffs.
//!
//! Compiled strictly under `#[forbid(unsafe_code)]` (enforced in `src/lib.rs`). All C FFI
//! interactions live behind safe RAII handles in `crate::ffi::{sqlite, tls}`.

pub mod postgres;
pub mod schema_lock;
pub mod sqlite;

use std::collections::HashMap;
use std::fmt::{self, Write as _};

use crate::core::bigint::{BigInt, DEC_MAX, DEC_MIN, DEC_SCALE};
use crate::core::syntax::{ColSpec, Float64, Ident, ScalarTy, TableTy, TagSet};
use crate::formats::time::{parse_decimal_bigint_strict, parse_iso_timestamp};
use crate::oracle::value::{
    TableRow, TableVal, Val, redact_tags, render_decimal, render_public_val, val_eq,
};
use crate::vm::batch::{Batch, Column, ColumnData, NullBitmap};
use crate::vm::ops::VmTable;

use self::postgres::PostgresDriver;
use self::schema_lock::LockedDb;
use self::sqlite::SqliteDriver;

/// Maximum number of sample row diffs retained in an [`UpsertDiff`].
pub const MAX_SAMPLE_DIFFS: usize = 20;

/// Supported SQL database dialects.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum SqlDialect {
    Sqlite,
    Postgres,
}

impl SqlDialect {
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Sqlite => "sqlite",
            Self::Postgres => "postgres",
        }
    }
}

impl fmt::Display for SqlDialect {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

/// PostgreSQL TLS negotiation & certificate verification mode.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub enum SslMode {
    Disable,
    #[default]
    Prefer,
    Require,
    VerifyCa,
    VerifyFull,
}

impl SslMode {
    /// Parse a libpq-compatible `sslmode` parameter value.
    ///
    /// # Errors
    /// Returns [`DbError::InvalidUri`] for unrecognized values.
    pub fn parse(raw: &str) -> Result<Self, DbError> {
        match raw.to_ascii_lowercase().as_str() {
            "disable" => Ok(Self::Disable),
            "prefer" => Ok(Self::Prefer),
            "require" => Ok(Self::Require),
            "verify-ca" => Ok(Self::VerifyCa),
            "verify-full" => Ok(Self::VerifyFull),
            other => Err(DbError::InvalidUri(format!(
                "unsupported sslmode `{other}` (expected disable, prefer, require, verify-ca, or verify-full)"
            ))),
        }
    }
}

/// Parsed SQLite connection URI.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SqliteUri {
    pub path: String,
    pub read_only: bool,
    pub attachments: Vec<(String, String)>,
}

/// Validate a SQLite `ATTACH DATABASE ... AS schema` alias (`[A-Za-z_][A-Za-z0-9_]*`,
/// excluding reserved `"main"` and `"temp"` namespaces).
///
/// # Errors
/// Returns [`DbError::InvalidUri`] if the schema identifier is invalid or reserved.
pub fn validate_sqlite_attach_schema(schema: &str) -> Result<(), DbError> {
    let mut chars = schema.chars();
    let Some(first) = chars.next() else {
        return Err(DbError::InvalidUri(
            "SQLite attach schema name cannot be empty".to_string(),
        ));
    };
    if !(first.is_ascii_alphabetic() || first == '_')
        || !chars.all(|c| c.is_ascii_alphanumeric() || c == '_')
    {
        return Err(DbError::InvalidUri(format!(
            "invalid SQLite attach schema name `{schema}` (expected ASCII identifier `[A-Za-z_][A-Za-z0-9_]*`)"
        )));
    }
    if schema.eq_ignore_ascii_case("main") || schema.eq_ignore_ascii_case("temp") {
        return Err(DbError::InvalidUri(format!(
            "SQLite attach schema name `{schema}` is reserved (`main`/`temp` cannot be attached)"
        )));
    }
    Ok(())
}

/// Parse a CLI `--attach [DB:]schema=PATH` specification.
///
/// # Errors
/// Returns [`DbError::InvalidUri`] if syntax, schema identifier, or path is invalid.
pub fn parse_attach_spec(raw: &str) -> Result<(Option<String>, String, String), DbError> {
    let Some((lhs, path)) = raw.split_once('=') else {
        return Err(DbError::InvalidUri(format!(
            "invalid `--attach` argument `{raw}` (expected `[DB:]schema=PATH`)"
        )));
    };
    if path.is_empty() {
        return Err(DbError::InvalidUri(format!(
            "empty SQLite file path in `--attach` argument `{raw}`"
        )));
    }
    if let Some((db_name, schema)) = lhs.split_once(':') {
        if db_name.is_empty() || schema.contains(':') {
            return Err(DbError::InvalidUri(format!(
                "invalid `--attach` target `{lhs}` in `{raw}` (expected `[DB:]schema=PATH`)"
            )));
        }
        validate_sqlite_attach_schema(schema)?;
        Ok((
            Some(db_name.to_string()),
            schema.to_string(),
            path.to_string(),
        ))
    } else {
        validate_sqlite_attach_schema(lhs)?;
        Ok((None, lhs.to_string(), path.to_string()))
    }
}

/// Parsed PostgreSQL connection URI.
#[derive(Clone, PartialEq, Eq)]
pub struct PostgresUri {
    pub host: String,
    pub port: u16,
    pub user: String,
    pub password: Option<String>,
    pub database: String,
    pub sslmode: SslMode,
    pub sslrootcert: Option<String>,
    pub connect_timeout_secs: Option<u64>,
}

impl fmt::Debug for PostgresUri {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("PostgresUri")
            .field("host", &self.host)
            .field("port", &self.port)
            .field("user", &self.user)
            .field(
                "password",
                &self.password.as_ref().map(|_| "[REDACTED:secret]"),
            )
            .field("database", &self.database)
            .field("sslmode", &self.sslmode)
            .field("sslrootcert", &self.sslrootcert)
            .field("connect_timeout_secs", &self.connect_timeout_secs)
            .finish()
    }
}

/// Parsed database connection URI (`sqlite:...` or `postgres://...`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DbUri {
    Sqlite(SqliteUri),
    Postgres(PostgresUri),
}

impl DbUri {
    /// Parse a database URI supporting:
    /// - `sqlite::memory:`
    /// - `sqlite:///abs/path`
    /// - `sqlite://rel/path`
    /// - `sqlite:path`
    /// - `postgres://[user[:password]@]host[:port][/database][?params]`
    /// - `postgresql://[user[:password]@]host[:port][/database][?params]`
    ///
    /// # Errors
    /// Returns [`DbError::InvalidUri`] on malformed URIs, invalid percent-escapes, or unknown schemes.
    pub fn parse(raw: &str) -> Result<Self, DbError> {
        let trimmed = raw.trim();
        if let Some(rest) = trimmed.strip_prefix("sqlite:") {
            return parse_sqlite_uri(rest).map(Self::Sqlite);
        }
        if let Some(rest) = trimmed
            .strip_prefix("postgres://")
            .or_else(|| trimmed.strip_prefix("postgresql://"))
        {
            return parse_postgres_uri(rest).map(Self::Postgres);
        }
        Err(DbError::InvalidUri(format!(
            "unsupported database URI scheme in `{}` (expected sqlite:, postgres://, or postgresql://)",
            redact_uri_credentials(trimmed)
        )))
    }

    #[must_use]
    pub const fn dialect(&self) -> SqlDialect {
        match self {
            Self::Sqlite(_) => SqlDialect::Sqlite,
            Self::Postgres(_) => SqlDialect::Postgres,
        }
    }
}

fn redact_uri_credentials(uri: &str) -> String {
    if let Some(scheme_end) = uri.find("://") {
        let after = &uri[scheme_end + 3..];
        let auth_end = after.find(['/', '?']).unwrap_or(after.len());
        if let Some(at) = after[..auth_end].rfind('@') {
            return format!(
                "{}://[REDACTED:secret]@{}",
                &uri[..scheme_end],
                &after[at + 1..]
            );
        }
    }
    uri.to_string()
}

fn percent_decode(input: &str) -> Result<String, DbError> {
    let bytes = input.as_bytes();
    let mut out = Vec::with_capacity(bytes.len());
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] == b'%' {
            if i + 2 >= bytes.len() {
                return Err(DbError::InvalidUri(format!(
                    "truncated percent-escape in URI component `{input}`"
                )));
            }
            let hi = hex_nibble(bytes[i + 1]).ok_or_else(|| {
                DbError::InvalidUri(format!("invalid percent-escape in `{input}`"))
            })?;
            let lo = hex_nibble(bytes[i + 2]).ok_or_else(|| {
                DbError::InvalidUri(format!("invalid percent-escape in `{input}`"))
            })?;
            out.push((hi << 4) | lo);
            i += 3;
        } else {
            out.push(bytes[i]);
            i += 1;
        }
    }
    String::from_utf8(out)
        .map_err(|e| DbError::InvalidUri(format!("invalid UTF-8 after percent-decoding: {e}")))
}

#[must_use]
pub(crate) const fn hex_nibble(b: u8) -> Option<u8> {
    match b {
        b'0'..=b'9' => Some(b - b'0'),
        b'a'..=b'f' => Some(b - b'a' + 10),
        b'A'..=b'F' => Some(b - b'A' + 10),
        _ => None,
    }
}

fn parse_sqlite_uri(rest: &str) -> Result<SqliteUri, DbError> {
    if rest == ":memory:" {
        return Ok(SqliteUri {
            path: ":memory:".to_string(),
            read_only: false,
            attachments: Vec::new(),
        });
    }
    let (path_part, query_part) = match rest.split_once('?') {
        Some((p, q)) => (p, Some(q)),
        None => (rest, None),
    };
    let raw_path = if let Some(after_slashes) = path_part.strip_prefix("//") {
        after_slashes
    } else {
        path_part
    };
    let decoded_path = percent_decode(raw_path)?;
    if decoded_path.is_empty() {
        return Err(DbError::InvalidUri(
            "empty sqlite database path".to_string(),
        ));
    }
    let mut read_only = false;
    let mut attachments = Vec::new();
    if let Some(q) = query_part {
        for pair in q.split('&') {
            if pair.is_empty() {
                continue;
            }
            let (k, v) = pair.split_once('=').unwrap_or((pair, ""));
            let key = percent_decode(k)?;
            let val = percent_decode(v)?;
            if (key == "mode" && val.eq_ignore_ascii_case("ro"))
                || (key == "read_only" && val.eq_ignore_ascii_case("true"))
            {
                read_only = true;
            } else if key == "attach" {
                let Some(sep) = val.find([':', '=']) else {
                    return Err(DbError::InvalidUri(format!(
                        "invalid sqlite `attach` query `{val}` (expected `schema:path` or `schema=path`)"
                    )));
                };
                let schema = &val[..sep];
                let attach_path = &val[sep + 1..];
                validate_sqlite_attach_schema(schema)?;
                if attach_path.is_empty() {
                    return Err(DbError::InvalidUri(format!(
                        "empty path in sqlite `attach` query `{val}`"
                    )));
                }
                attachments.push((schema.to_string(), attach_path.to_string()));
            }
        }
    }
    Ok(SqliteUri {
        path: decoded_path,
        read_only,
        attachments,
    })
}

fn parse_postgres_uri(rest: &str) -> Result<PostgresUri, DbError> {
    let (before_query, query_part) = match rest.split_once('?') {
        Some((a, q)) => (a, Some(q)),
        None => (rest, None),
    };
    let (authority, path_part) = match before_query.split_once('/') {
        Some((a, p)) => (a, Some(p)),
        None => (before_query, None),
    };

    let (userinfo, hostport) = match authority.rsplit_once('@') {
        Some((u, h)) => (Some(u), h),
        None => (None, authority),
    };

    let (user, password) = match userinfo {
        Some(ui) => match ui.split_once(':') {
            Some((u, p)) => (percent_decode(u)?, Some(percent_decode(p)?)),
            None => (percent_decode(ui)?, None),
        },
        None => {
            let default_user = std::env::var("USER").unwrap_or_else(|_| "postgres".to_string());
            (default_user, None)
        }
    };

    let (host, port) = if let Some(bracketed) = hostport.strip_prefix('[') {
        let Some((ipv6, after_bracket)) = bracketed.split_once(']') else {
            return Err(DbError::InvalidUri(
                "unclosed IPv6 literal in postgres URI".to_string(),
            ));
        };
        let port = if let Some(p_str) = after_bracket.strip_prefix(':') {
            p_str.parse::<u16>().map_err(|_| {
                DbError::InvalidUri(format!("invalid port `{p_str}` in postgres URI"))
            })?
        } else if after_bracket.is_empty() {
            5432
        } else {
            return Err(DbError::InvalidUri(format!(
                "unexpected characters `{after_bracket}` after IPv6 host"
            )));
        };
        (percent_decode(ipv6)?, port)
    } else if let Some((h, p_str)) = hostport.rsplit_once(':') {
        let port = p_str
            .parse::<u16>()
            .map_err(|_| DbError::InvalidUri(format!("invalid port `{p_str}` in postgres URI")))?;
        (percent_decode(h)?, port)
    } else {
        (percent_decode(hostport)?, 5432)
    };

    if host.is_empty() {
        return Err(DbError::InvalidUri(
            "missing host in postgres URI".to_string(),
        ));
    }

    let database = match path_part {
        Some(p) if !p.is_empty() => percent_decode(p)?,
        _ => user.clone(),
    };

    let mut sslmode = SslMode::Prefer;
    let mut sslrootcert = None;
    let mut connect_timeout_secs = None;

    if let Some(q) = query_part {
        for pair in q.split('&') {
            if pair.is_empty() {
                continue;
            }
            let (k, v) = pair.split_once('=').unwrap_or((pair, ""));
            let key = percent_decode(k)?;
            let val = percent_decode(v)?;
            match key.as_str() {
                "sslmode" => sslmode = SslMode::parse(&val)?,
                "sslrootcert" => {
                    if !val.is_empty() {
                        sslrootcert = Some(val);
                    }
                }
                "connect_timeout" => {
                    let secs = val.parse::<u64>().map_err(|_| {
                        DbError::InvalidUri(format!(
                            "invalid connect_timeout `{val}` (expected positive integer seconds)"
                        ))
                    })?;
                    connect_timeout_secs = Some(secs);
                }
                _ => {}
            }
        }
    }

    Ok(PostgresUri {
        host,
        port,
        user,
        password,
        database,
        sslmode,
        sslrootcert,
        connect_timeout_secs,
    })
}

/// Typed SQL bind parameter (parameterized queries only — never string-interpolated).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SqlParam {
    Null,
    Bool(bool),
    Int(i64),
    Decimal(BigInt),
    Float(Float64),
    Text(String),
    Bytes(Vec<u8>),
    Date(i64),
    Timestamp(i64),
    Duration(i64),
}

impl SqlParam {
    /// Convert a Dana runtime [`Val`] into a typed [`SqlParam`].
    ///
    /// Transparently unwraps `Option` (`OptNone => Null`, `OptSome(v) => from_val(v)`).
    ///
    /// # Errors
    /// Returns [`DbError::TypeConversion`] if the value is non-scalar or overflows 64-bit bounds.
    pub fn from_val(val: &Val) -> Result<Self, DbError> {
        let mut cur = val;
        while let Val::OptSome(inner) = cur {
            cur = inner.as_ref();
        }
        match cur {
            Val::OptNone | Val::Unit => Ok(Self::Null),
            Val::Bool(b) => Ok(Self::Bool(*b)),
            Val::Int(n) => n
                .to_i64()
                .map(Self::Int)
                .ok_or_else(|| DbError::TypeConversion(format!("Int `{n}` overflows i64"))),
            Val::Decimal(d) => Ok(Self::Decimal(d.clone())),
            Val::Float(f) => Ok(Self::Float(*f)),
            Val::Text(s) => Ok(Self::Text(s.clone())),
            Val::Bytes(bs) => Ok(Self::Bytes(bs.clone())),
            Val::Date(d) => d
                .to_i64()
                .map(Self::Date)
                .ok_or_else(|| DbError::TypeConversion(format!("Date `{d}` overflows i64"))),
            Val::Timestamp(t) => t
                .to_i64()
                .map(Self::Timestamp)
                .ok_or_else(|| DbError::TypeConversion(format!("Timestamp `{t}` overflows i64"))),
            Val::Duration(d) => d
                .to_i64()
                .map(Self::Duration)
                .ok_or_else(|| DbError::TypeConversion(format!("Duration `{d}` overflows i64"))),
            other => Err(DbError::TypeConversion(format!(
                "cannot bind non-scalar Dana value `{}` as SQL parameter",
                render_public_val(other)
            ))),
        }
    }
}

/// Structured database driver & schema-lock error type.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DbError {
    InvalidUri(String),
    Connection(String),
    Auth(String),
    Protocol(String),
    Query(String),
    SchemaDrift(String),
    TypeConversion(String),
    Io(String),
    Tls(String),
    LockParse(String),
    NotFound(String),
}

impl fmt::Display for DbError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidUri(m) => write!(f, "invalid database URI: {m}"),
            Self::Connection(m) => write!(f, "database connection error: {m}"),
            Self::Auth(m) => write!(f, "database authentication error: {m}"),
            Self::Protocol(m) => write!(f, "database protocol error: {m}"),
            Self::Query(m) => write!(f, "database query error: {m}"),
            Self::SchemaDrift(m) => write!(f, "database schema drift: {m}"),
            Self::TypeConversion(m) => write!(f, "database type conversion error: {m}"),
            Self::Io(m) => write!(f, "database I/O error: {m}"),
            Self::Tls(m) => write!(f, "database TLS error: {m}"),
            Self::LockParse(m) => write!(f, "schema.lock parse error: {m}"),
            Self::NotFound(m) => write!(f, "database resource not found: {m}"),
        }
    }
}

impl std::error::Error for DbError {}

impl From<std::io::Error> for DbError {
    fn from(err: std::io::Error) -> Self {
        Self::Io(err.to_string())
    }
}

/// One changed cell within a [`RowDiff`], retaining its sensitivity [`TagSet`].
#[derive(Clone, Debug)]
pub struct CellChange {
    pub col: Ident,
    pub old_val: Option<Val>,
    pub new_val: Val,
    pub tags: TagSet,
}

/// Kind of row-level change in an upsert dry-run or execution diff.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RowDiffKind {
    Insert,
    Update,
}

/// One sampled row change in an [`UpsertDiff`].
#[derive(Clone, Debug)]
pub struct RowDiff {
    pub kind: RowDiffKind,
    pub key_val: Val,
    pub key_tags: TagSet,
    pub changes: Vec<CellChange>,
}

/// Summary and privacy-aware sample diffs returned by [`DbConnection::upsert_table`].
#[derive(Clone, Debug)]
pub struct UpsertDiff {
    pub table: Ident,
    pub inserted: usize,
    pub updated: usize,
    pub unchanged: usize,
    pub sample_diffs: Vec<RowDiff>,
}

impl UpsertDiff {
    /// Render a deterministic human-readable diff summary that automatically redacts any cell
    /// or key value carrying sensitivity tags not authorized by `allow_export`.
    ///
    /// **Privacy invariant:** whenever `tags.diff(allow_export)` is non-empty, the underlying
    /// [`Val`] is NEVER inspected and is formatted strictly as `[REDACTED:<tags>]`.
    #[must_use]
    pub fn render_redacted(&self, allow_export: &TagSet) -> String {
        let mut out = String::new();
        let _ = writeln!(
            out,
            "table \"{}\": {} inserted, {} updated, {} unchanged",
            self.table, self.inserted, self.updated, self.unchanged
        );
        for row in &self.sample_diffs {
            let kind_str = match row.kind {
                RowDiffKind::Insert => "INSERT",
                RowDiffKind::Update => "UPDATE",
            };
            let key_str = render_val_with_export_gate(&row.key_val, &row.key_tags, allow_export);
            let _ = write!(out, "  [{kind_str}] key={key_str}");
            if !row.changes.is_empty() {
                out.push_str(" { ");
                for (idx, ch) in row.changes.iter().enumerate() {
                    if idx > 0 {
                        out.push_str(", ");
                    }
                    match &ch.old_val {
                        Some(old) => {
                            let old_s = render_val_with_export_gate(old, &ch.tags, allow_export);
                            let new_s =
                                render_val_with_export_gate(&ch.new_val, &ch.tags, allow_export);
                            let _ = write!(out, "{}: {} -> {}", ch.col, old_s, new_s);
                        }
                        None => {
                            let new_s =
                                render_val_with_export_gate(&ch.new_val, &ch.tags, allow_export);
                            let _ = write!(out, "{}: {}", ch.col, new_s);
                        }
                    }
                }
                out.push_str(" }");
            }
            out.push('\n');
        }
        out
    }
}

fn render_val_with_export_gate(val: &Val, tags: &TagSet, allow_export: &TagSet) -> String {
    let unauth = tags.diff(allow_export);
    if unauth.is_empty() {
        render_public_val(val)
    } else {
        redact_tags(&unauth)
    }
}

/// Uniform interface implemented by every Phase 3 SQL database driver (`SqliteDriver`, `PostgresDriver`).
pub trait DbConnection {
    fn dialect(&self) -> SqlDialect;

    /// Execute a parameterized query and materialize rows matching `expected_schema`.
    ///
    /// # Errors
    /// Returns [`DbError::SchemaDrift`] on column count/type mismatches, or query/protocol errors.
    fn query_rows(
        &mut self,
        sql: &str,
        params: &[SqlParam],
        expected_schema: &TableTy,
    ) -> Result<TableVal, DbError>;

    /// Execute a parameterized query and stream results directly into columnar `batch_size`-row
    /// [`Batch`]es wrapped in a [`VmTable`].
    ///
    /// # Errors
    /// Returns [`DbError::SchemaDrift`] on column count/type mismatches, or query/protocol errors.
    fn query_batches(
        &mut self,
        sql: &str,
        params: &[SqlParam],
        expected_schema: &TableTy,
        batch_size: usize,
    ) -> Result<VmTable, DbError>;

    /// Introspect tables, column types, nullability, and primary keys into a [`LockedDb`] snapshot.
    ///
    /// # Errors
    /// Returns [`DbError`] on query or schema decoding failure.
    fn introspect_schema(&mut self, db_name: &str) -> Result<LockedDb, DbError>;

    /// Introspect tables across an explicit list of schemas (PostgreSQL `table_schema IN (...)`).
    ///
    /// Drivers without schema namespaces (e.g. SQLite) ignore `schemas` and fall back to
    /// [`DbConnection::introspect_schema`].
    ///
    /// # Errors
    /// Returns [`DbError`] on query, schema-name validation, or schema decoding failure.
    fn introspect_schema_with_schemas(
        &mut self,
        db_name: &str,
        schemas: &[String],
    ) -> Result<LockedDb, DbError> {
        let _ = schemas;
        self.introspect_schema(db_name)
    }

    /// Compute an [`UpsertDiff`] against `table` keyed by `key_col`.
    ///
    /// When `dry_run` is `true`, **zero write SQL statements** are executed.
    /// When `dry_run` is `false`, performs a transactional parameterized upsert.
    ///
    /// # Errors
    /// Returns [`DbError`] if `key_col` is missing, queries fail, or the transaction aborts.
    fn upsert_table(
        &mut self,
        table: &str,
        key_col: &str,
        data: &TableVal,
        dry_run: bool,
    ) -> Result<UpsertDiff, DbError>;

    /// Execute a parameterized DDL/DML statement and return affected rows.
    ///
    /// # Errors
    /// Returns [`DbError`] on prepare, bind, or execution failure.
    fn execute(&mut self, sql: &str, params: &[SqlParam]) -> Result<u64, DbError>;

    /// Attach a secondary SQLite database file as schema namespace `schema`.
    ///
    /// # Errors
    /// Returns [`DbError::InvalidUri`] on non-SQLite drivers or connection failure.
    fn attach_database(&mut self, schema: &str, path: &str) -> Result<(), DbError> {
        let _ = (schema, path);
        Err(DbError::InvalidUri(
            "ATTACH DATABASE is only supported on SQLite connections".to_string(),
        ))
    }

    /// Resolve a Dana `from: "..."` table name to its properly quoted SQL relation reference.
    fn resolve_table_sql_ref(&mut self, table: &str) -> String {
        quote_sql_table_ref(table)
    }
}

/// Registry managing logical Dana database names, URI bindings, `DANA_DB_<UPPER>` environment
/// lookups, and cached live [`DbConnection`] handles.
#[derive(Default)]
pub struct DbRegistry {
    bindings: HashMap<String, String>,
    connections: HashMap<String, Box<dyn DbConnection>>,
    sqlite_attachments: Vec<(Option<String>, String, String)>,
}

impl fmt::Debug for DbRegistry {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut bound_names: Vec<&str> = self.bindings.keys().map(String::as_str).collect();
        bound_names.sort_unstable();
        let mut open_names: Vec<&str> = self.connections.keys().map(String::as_str).collect();
        open_names.sort_unstable();
        f.debug_struct("DbRegistry")
            .field("bound_dbs", &bound_names)
            .field("open_connections", &open_names)
            .finish()
    }
}

impl DbRegistry {
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Bind a logical Dana database name (e.g. `"Analytics"`) to a connection URI.
    pub fn register(&mut self, db_name: impl Into<String>, uri: impl Into<String>) {
        let name = db_name.into();
        self.connections.remove(&name);
        self.bindings.insert(name, uri.into());
    }

    /// Register a SQLite `ATTACH DATABASE` mapping (globally when `db_name` is `None`,
    /// or scoped to logical database `db_name`).
    pub fn attach_sqlite(
        &mut self,
        db_name: Option<String>,
        schema: impl Into<String>,
        path: impl Into<String>,
    ) {
        if let Some(ref target) = db_name {
            self.connections.remove(target);
        } else {
            self.connections.clear();
        }
        self.sqlite_attachments
            .push((db_name, schema.into(), path.into()));
    }

    /// Resolve a logical database name from explicit bindings or `DANA_DB_<UPPER>` env var.
    ///
    /// # Errors
    /// Returns [`DbError::NotFound`] if neither an explicit binding nor env variable exists.
    pub fn resolve_uri(&self, db_name: &str) -> Result<String, DbError> {
        if let Some(uri) = self.bindings.get(db_name) {
            return Ok(uri.clone());
        }
        let env_key = format!("DANA_DB_{}", db_name.to_ascii_uppercase());
        if let Ok(uri) = std::env::var(&env_key)
            && !uri.trim().is_empty()
        {
            return Ok(uri);
        }
        Err(DbError::NotFound(format!(
            "no URI binding for database `{db_name}` (register explicitly or set `{env_key}`)"
        )))
    }

    /// Open (or reuse a cached) connection for logical database `db_name`.
    ///
    /// # Errors
    /// Returns [`DbError`] if the URI is missing/invalid or the driver fails to connect.
    pub fn open(&mut self, db_name: &str) -> Result<&mut (dyn DbConnection + 'static), DbError> {
        if !self.connections.contains_key(db_name) {
            let uri = self.resolve_uri(db_name)?;
            let mut conn = open_connection(&uri)?;
            if conn.dialect() == SqlDialect::Sqlite {
                for (filter, schema, path) in &self.sqlite_attachments {
                    if filter.is_none() || filter.as_deref() == Some(db_name) {
                        conn.attach_database(schema, path)?;
                    }
                }
            }
            self.connections.insert(db_name.to_string(), conn);
        }
        self.connections
            .get_mut(db_name)
            .map(Box::as_mut)
            .ok_or_else(|| DbError::NotFound(format!("database `{db_name}` missing from cache")))
    }

    /// Close and drop a cached connection for `db_name`, if open.
    pub fn close(&mut self, db_name: &str) -> bool {
        self.connections.remove(db_name).is_some()
    }
}

/// Open a standalone [`DbConnection`] from a URI string.
///
/// # Errors
/// Returns [`DbError`] if URI parsing or connection establishment fails.
pub fn open_connection(uri: &str) -> Result<Box<dyn DbConnection>, DbError> {
    match DbUri::parse(uri)? {
        DbUri::Sqlite(s) => Ok(Box::new(SqliteDriver::open(&s)?)),
        DbUri::Postgres(p) => Ok(Box::new(PostgresDriver::connect(&p)?)),
    }
}

// ===========================================================================
// Shared SQL, Codec, Diff & Columnar Batch Helpers
// ===========================================================================

/// Strictly quote a SQL identifier using standard ANSI double quotes with `""` escaping.
#[must_use]
pub fn quote_sql_ident(ident: &str) -> String {
    let mut out = String::with_capacity(ident.len() + 2);
    out.push('"');
    for ch in ident.chars() {
        if ch == '"' {
            out.push_str("\"\"");
        } else {
            out.push(ch);
        }
    }
    out.push('"');
    out
}

/// Strictly quote a SQL table reference, splitting a single schema prefix (`schema.table`)
/// into `"schema"."table"` while delegating unqualified or malformed names to [`quote_sql_ident`].
///
/// **CRITICAL:** Use ONLY on table references (`FROM` / `JOIN` / `INSERT INTO` / `UPDATE`),
/// never on column names or aliases.
#[must_use]
pub fn quote_sql_table_ref(table: &str) -> String {
    if let Some((schema, rel)) = table.split_once('.')
        && !schema.is_empty()
        && !rel.is_empty()
        && !rel.contains('.')
    {
        return format!("{}.{}", quote_sql_ident(schema), quote_sql_ident(rel));
    }
    quote_sql_ident(table)
}

/// Format a `10^-18`-scaled [`BigInt`] `Decimal` into its lossless canonical ASCII string.
#[must_use]
pub fn format_decimal_canonical(scaled: &BigInt) -> String {
    render_decimal(scaled)
}

/// Parse an exact fixed-point `Decimal` from a finite `f64`, expanding scientific notation if needed.
///
/// # Errors
/// Returns [`DbError::TypeConversion`] for NaN, Infinity, or out-of-range values.
pub(crate) fn parse_decimal_from_f64(v: f64) -> Result<BigInt, DbError> {
    if !v.is_finite() {
        return Err(DbError::TypeConversion(format!(
            "cannot convert non-finite float `{v}` to Decimal"
        )));
    }
    let raw = format!("{v}");
    if !raw.contains(['e', 'E']) {
        return parse_decimal_bigint_strict(&raw)
            .map_err(|e| DbError::TypeConversion(e.to_string()));
    }
    // Expand scientific notation such as `1.25e-5` or `1.5e6` without float rounding.
    let (mantissa, exp_str) = raw
        .split_once(['e', 'E'])
        .ok_or_else(|| DbError::TypeConversion(format!("invalid float `{raw}`")))?;
    let exp: i32 = exp_str
        .parse()
        .map_err(|_| DbError::TypeConversion(format!("invalid float exponent in `{raw}`")))?;
    let (neg, unsigned) = match mantissa.strip_prefix('-') {
        Some(r) => (true, r),
        None => (false, mantissa),
    };
    let (int_p, frac_p) = unsigned.split_once('.').unwrap_or((unsigned, ""));
    let digits = format!("{int_p}{frac_p}");
    let dec_pos = int_p.len() as i32 + exp;
    let expanded = if dec_pos <= 0 {
        let zeros = (-dec_pos) as usize;
        format!("0.{}{digits}", "0".repeat(zeros))
    } else if (dec_pos as usize) >= digits.len() {
        let zeros = (dec_pos as usize) - digits.len();
        format!("{digits}{}", "0".repeat(zeros))
    } else {
        let split = dec_pos as usize;
        format!("{}.{}", &digits[..split], &digits[split..])
    };
    let signed = if neg {
        format!("-{expanded}")
    } else {
        expanded
    };
    parse_decimal_bigint_strict(&signed).map_err(|e| DbError::TypeConversion(e.to_string()))
}

/// Scale a 64-bit signed integer to a `10^-18`-scaled `Decimal` [`BigInt`].
///
/// # Errors
/// Returns [`DbError::TypeConversion`] if the scaled result leaves `[DEC_MIN, DEC_MAX]`.
pub(crate) fn decimal_from_i64(n: i64) -> Result<BigInt, DbError> {
    let scaled = &BigInt::from(n) * &BigInt::from(DEC_SCALE);
    if scaled < BigInt::from(DEC_MIN) || scaled > BigInt::from(DEC_MAX) {
        return Err(DbError::TypeConversion(format!(
            "integer `{n}` overflows Decimal range"
        )));
    }
    Ok(scaled)
}

/// Parse ISO-8601 and PostgreSQL-formatted timestamps into UTC microseconds since Unix epoch.
///
/// Supports:
/// - `YYYY-MM-DDTHH:MM:SS(.frac)?Z`
/// - `YYYY-MM-DD HH:MM:SS(.frac)?±HH:MM`
/// - `YYYY-MM-DD HH:MM:SS(.frac)?±HH` (PostgreSQL `TIMESTAMPTZ` shorthand like `+00`)
/// - `YYYY-MM-DD HH:MM:SS(.frac)?±HHMM`
/// - Bare `YYYY-MM-DD HH:MM:SS(.frac)?` (interpreted as UTC, matching session `TimeZone=UTC`)
///
/// # Errors
/// Returns [`DbError::TypeConversion`] if the string cannot be parsed as a valid timestamp.
pub(crate) fn parse_iso_timestamp_flexible(raw: &str) -> Result<i64, DbError> {
    let s = raw.trim();
    if let Ok(us) = parse_iso_timestamp(s) {
        return Ok(us);
    }
    if s.len() < 19 || !s.is_ascii() {
        return Err(DbError::TypeConversion(format!(
            "invalid timestamp `{raw}`"
        )));
    }
    let tail = &s[19..];
    // Find where fractional seconds end.
    let frac_end = if let Some(after_dot) = tail.strip_prefix('.') {
        1 + after_dot.bytes().take_while(u8::is_ascii_digit).count()
    } else {
        0
    };
    let tz_part = &tail[frac_end..];
    let normalized = if tz_part.is_empty() {
        format!("{s}Z")
    } else if tz_part.len() == 3
        && (tz_part.starts_with('+') || tz_part.starts_with('-'))
        && tz_part[1..3].bytes().all(|b| b.is_ascii_digit())
    {
        format!("{s}:00")
    } else if tz_part.len() == 5
        && (tz_part.starts_with('+') || tz_part.starts_with('-'))
        && tz_part[1..5].bytes().all(|b| b.is_ascii_digit())
    {
        format!(
            "{}{}:{}",
            &s[..19 + frac_end],
            &tz_part[0..3],
            &tz_part[3..5]
        )
    } else {
        return Err(DbError::TypeConversion(format!(
            "invalid timestamp timezone suffix in `{raw}`"
        )));
    };
    parse_iso_timestamp(&normalized).map_err(|e| DbError::TypeConversion(e.to_string()))
}

/// Compute an [`UpsertDiff`] comparing incoming `data` rows against an existing-row lookup map
/// (indexed by a canonical string key or linear scan via `val_eq` when needed).
pub(crate) fn compute_upsert_diff<F>(
    table: &str,
    key_idx: usize,
    data: &TableVal,
    mut fetch_existing: F,
) -> Result<UpsertDiff, DbError>
where
    F: FnMut(&Val) -> Result<Option<Vec<Val>>, DbError>,
{
    let key_tags = data.cols[key_idx].tags.clone();
    // Track state of keys already seen in this batch so repeated keys in `data` diff accurately.
    let mut seen: Vec<(Val, Vec<Val>)> = Vec::new();

    let mut inserted = 0usize;
    let mut updated = 0usize;
    let mut unchanged = 0usize;
    let mut sample_diffs = Vec::new();

    for row in &data.rows {
        let key_val = row
            .cells
            .get(key_idx)
            .ok_or_else(|| DbError::Query("row missing key column".to_string()))?;

        let existing_pos = seen.iter().position(|(k, _)| val_eq(k, key_val));
        let existing_cells = match existing_pos {
            Some(pos) => Some(seen[pos].1.clone()),
            None => fetch_existing(key_val)?,
        };

        match existing_cells {
            None => {
                inserted += 1;
                if sample_diffs.len() < MAX_SAMPLE_DIFFS {
                    let changes = data
                        .cols
                        .iter()
                        .zip(&row.cells)
                        .map(|(spec, val)| CellChange {
                            col: spec.name.clone(),
                            old_val: None,
                            new_val: val.clone(),
                            tags: spec.tags.clone(),
                        })
                        .collect();
                    sample_diffs.push(RowDiff {
                        kind: RowDiffKind::Insert,
                        key_val: key_val.clone(),
                        key_tags: key_tags.clone(),
                        changes,
                    });
                }
                seen.push((key_val.clone(), row.cells.clone()));
            }
            Some(old_cells) => {
                let mut changes = Vec::new();
                for ((spec, old_v), new_v) in data.cols.iter().zip(&old_cells).zip(&row.cells) {
                    if !val_eq(old_v, new_v) {
                        changes.push(CellChange {
                            col: spec.name.clone(),
                            old_val: Some(old_v.clone()),
                            new_val: new_v.clone(),
                            tags: spec.tags.clone(),
                        });
                    }
                }
                if changes.is_empty() {
                    unchanged += 1;
                } else {
                    updated += 1;
                    if sample_diffs.len() < MAX_SAMPLE_DIFFS {
                        sample_diffs.push(RowDiff {
                            kind: RowDiffKind::Update,
                            key_val: key_val.clone(),
                            key_tags: key_tags.clone(),
                            changes,
                        });
                    }
                }
                if let Some(pos) = existing_pos {
                    seen[pos].1 = row.cells.clone();
                } else {
                    seen.push((key_val.clone(), row.cells.clone()));
                }
            }
        }
    }

    Ok(UpsertDiff {
        table: table.to_string(),
        inserted,
        updated,
        unchanged,
        sample_diffs,
    })
}

// ===========================================================================
// Direct Streaming Columnar Batch Builder (for `query_batches`)
// ===========================================================================

enum ColBuf {
    Unit(usize),
    Bool(Vec<u8>),
    Int(Vec<i64>),
    Decimal(Vec<i128>),
    Float(Vec<u64>),
    Text { offsets: Vec<usize>, data: Vec<u8> },
    Bytes { offsets: Vec<usize>, data: Vec<u8> },
    Date(Vec<i64>),
    Timestamp(Vec<i64>),
    Duration(Vec<i64>),
    Generic(Vec<Val>),
}

impl ColBuf {
    fn new_for_scalar(ty: &ScalarTy, cap: usize) -> (Self, Option<NullBitmap>) {
        match ty {
            ScalarTy::Option(inner) if !inner.is_option() => {
                let buf = Self::new_leaf(inner, cap);
                if matches!(buf, Self::Generic(_)) {
                    (buf, None)
                } else {
                    (buf, Some(NullBitmap::with_capacity(cap)))
                }
            }
            other => (Self::new_leaf(other, cap), None),
        }
    }

    fn new_leaf(ty: &ScalarTy, cap: usize) -> Self {
        match ty {
            ScalarTy::Unit => Self::Unit(0),
            ScalarTy::Bool => Self::Bool(Vec::with_capacity(cap)),
            ScalarTy::Int => Self::Int(Vec::with_capacity(cap)),
            ScalarTy::Decimal => Self::Decimal(Vec::with_capacity(cap)),
            ScalarTy::Float => Self::Float(Vec::with_capacity(cap)),
            ScalarTy::Text => {
                let mut offsets = Vec::with_capacity(cap + 1);
                offsets.push(0);
                Self::Text {
                    offsets,
                    data: Vec::new(),
                }
            }
            ScalarTy::Bytes => {
                let mut offsets = Vec::with_capacity(cap + 1);
                offsets.push(0);
                Self::Bytes {
                    offsets,
                    data: Vec::new(),
                }
            }
            ScalarTy::Date => Self::Date(Vec::with_capacity(cap)),
            ScalarTy::Timestamp => Self::Timestamp(Vec::with_capacity(cap)),
            ScalarTy::Duration => Self::Duration(Vec::with_capacity(cap)),
            ScalarTy::Data(_) | ScalarTy::Option(_) => Self::Generic(Vec::with_capacity(cap)),
        }
    }

    fn push_null(&mut self) {
        match self {
            Self::Unit(n) => *n += 1,
            Self::Bool(v) => v.push(0),
            Self::Int(v) | Self::Date(v) | Self::Timestamp(v) | Self::Duration(v) => v.push(0),
            Self::Decimal(v) => v.push(0),
            Self::Float(v) => v.push(0),
            Self::Text { offsets, data } | Self::Bytes { offsets, data } => {
                offsets.push(data.len());
            }
            Self::Generic(v) => v.push(Val::OptNone),
        }
    }

    fn push_non_null(&mut self, val: &Val) -> Result<(), DbError> {
        match (self, val) {
            (Self::Unit(n), Val::Unit) => *n += 1,
            (Self::Bool(v), Val::Bool(b)) => v.push(u8::from(*b)),
            (Self::Int(v), Val::Int(n)) => {
                let i = n.to_i64().ok_or_else(|| {
                    DbError::TypeConversion(format!("Int `{n}` overflows i64 in batch"))
                })?;
                v.push(i);
            }
            (Self::Decimal(v), Val::Decimal(d)) => {
                let i = d.to_i128().ok_or_else(|| {
                    DbError::TypeConversion(format!("Decimal `{d}` overflows i128 in batch"))
                })?;
                v.push(i);
            }
            (Self::Float(v), Val::Float(f)) => v.push(f.bits),
            (Self::Text { offsets, data }, Val::Text(s)) => {
                data.extend_from_slice(s.as_bytes());
                offsets.push(data.len());
            }
            (Self::Bytes { offsets, data }, Val::Bytes(bs)) => {
                data.extend_from_slice(bs);
                offsets.push(data.len());
            }
            (Self::Date(v), Val::Date(d)) => {
                let i = d.to_i64().ok_or_else(|| {
                    DbError::TypeConversion(format!("Date `{d}` overflows i64 in batch"))
                })?;
                v.push(i);
            }
            (Self::Timestamp(v), Val::Timestamp(t)) => {
                let i = t.to_i64().ok_or_else(|| {
                    DbError::TypeConversion(format!("Timestamp `{t}` overflows i64 in batch"))
                })?;
                v.push(i);
            }
            (Self::Duration(v), Val::Duration(d)) => {
                let i = d.to_i64().ok_or_else(|| {
                    DbError::TypeConversion(format!("Duration `{d}` overflows i64 in batch"))
                })?;
                v.push(i);
            }
            (Self::Generic(v), any_val) => v.push(any_val.clone()),
            (_, unexpected) => {
                return Err(DbError::SchemaDrift(format!(
                    "mismatched value `{}` for columnar batch slot",
                    render_public_val(unexpected)
                )));
            }
        }
        Ok(())
    }

    fn into_column_data(self) -> ColumnData {
        match self {
            Self::Unit(n) => ColumnData::Unit(n),
            Self::Bool(v) => ColumnData::Bool(v),
            Self::Int(v) => ColumnData::Int(v),
            Self::Decimal(v) => ColumnData::Decimal(v),
            Self::Float(v) => ColumnData::Float(v),
            Self::Text { offsets, data } => ColumnData::Text { offsets, data },
            Self::Bytes { offsets, data } => ColumnData::Bytes { offsets, data },
            Self::Date(v) => ColumnData::Date(v),
            Self::Timestamp(v) => ColumnData::Timestamp(v),
            Self::Duration(v) => ColumnData::Duration(v),
            Self::Generic(v) => ColumnData::Generic(v),
        }
    }
}

/// Streaming columnar builder that packs incoming decoded rows directly into fixed-size [`Batch`]es.
pub(crate) struct ColumnarBatchBuilder {
    specs: Vec<ColSpec>,
    batch_size: usize,
    bufs: Vec<(ColBuf, Option<NullBitmap>)>,
    cur_len: usize,
    batches: Vec<Batch>,
}

impl ColumnarBatchBuilder {
    pub(crate) fn new(specs: Vec<ColSpec>, batch_size: usize) -> Self {
        let clamped = batch_size.clamp(1, usize::from(u16::MAX));
        let bufs = specs
            .iter()
            .map(|s| ColBuf::new_for_scalar(&s.ty, clamped))
            .collect();
        Self {
            specs,
            batch_size: clamped,
            bufs,
            cur_len: 0,
            batches: Vec::new(),
        }
    }

    pub(crate) fn push_row(&mut self, cells: Vec<Val>) -> Result<(), DbError> {
        if cells.len() != self.specs.len() {
            return Err(DbError::SchemaDrift(format!(
                "expected {} columns, got {}",
                self.specs.len(),
                cells.len()
            )));
        }
        for ((buf, validity), val) in self.bufs.iter_mut().zip(&cells) {
            if let Some(bm) = validity {
                match val {
                    Val::OptNone => {
                        bm.push(false);
                        buf.push_null();
                    }
                    Val::OptSome(inner) => {
                        bm.push(true);
                        buf.push_non_null(inner.as_ref())?;
                    }
                    other => {
                        bm.push(true);
                        buf.push_non_null(other)?;
                    }
                }
            } else {
                buf.push_non_null(val)?;
            }
        }
        self.cur_len += 1;
        if self.cur_len >= self.batch_size {
            self.flush_current();
        }
        Ok(())
    }

    fn flush_current(&mut self) {
        if self.cur_len == 0 {
            return;
        }
        let fresh_bufs = self
            .specs
            .iter()
            .map(|s| ColBuf::new_for_scalar(&s.ty, self.batch_size))
            .collect();
        let finished = std::mem::replace(&mut self.bufs, fresh_bufs);
        let cols = self
            .specs
            .iter()
            .cloned()
            .zip(finished)
            .map(|(spec, (buf, validity))| Column {
                spec,
                data: buf.into_column_data(),
                validity,
            })
            .collect();
        self.batches.push(Batch {
            cols,
            len: self.cur_len,
            selection: None,
            group_meta: None,
        });
        self.cur_len = 0;
    }

    pub(crate) fn finish(mut self) -> VmTable {
        self.flush_current();
        VmTable {
            cols: self.specs,
            batches: self.batches,
        }
    }
}

/// Helper to build a [`TableRow`] with `group_meta: None`.
#[must_use]
pub(crate) fn make_table_row(cells: Vec<Val>) -> TableRow {
    TableRow {
        cells,
        group_meta: None,
    }
}
