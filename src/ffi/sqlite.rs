//! Safe RAII wrapper around the allowlisted system `libsqlite3` C library.
//!
//! All raw `sqlite3*` and `sqlite3_stmt*` pointers are strictly confined to this module,
//! documented with explicit `// SAFETY:` invariants, and released deterministically via `Drop`.

#![expect(
    unsafe_code,
    reason = "isolated FFI bindings to allowlisted system sqlite3 (libsqlite3)"
)]

use std::ffi::{CStr, CString, c_char, c_int, c_void};
use std::fmt;
use std::ptr;
use std::slice;

const SQLITE_OK: c_int = 0;
const SQLITE_ROW: c_int = 100;
const SQLITE_DONE: c_int = 101;

const SQLITE_OPEN_READONLY: c_int = 0x0000_0001;
const SQLITE_OPEN_READWRITE: c_int = 0x0000_0002;
const SQLITE_OPEN_CREATE: c_int = 0x0000_0004;
const SQLITE_OPEN_FULLMUTEX: c_int = 0x0001_0000;

const SQLITE_INTEGER: c_int = 1;
const SQLITE_FLOAT: c_int = 2;
const SQLITE_TEXT: c_int = 3;
const SQLITE_BLOB: c_int = 4;
const SQLITE_NULL: c_int = 5;

const DEFAULT_BUSY_TIMEOUT_MS: c_int = 5_000;

/// Sentinel pointer representing C `SQLITE_TRANSIENT` (`((sqlite3_destructor_type)-1)`),
/// instructing SQLite to make its own private copy of bound text/blob buffers immediately.
#[inline]
fn sqlite_transient() -> *const c_void {
    ptr::without_provenance::<c_void>(usize::MAX)
}

#[repr(C)]
struct Sqlite3 {
    _opaque: [u8; 0],
}

#[repr(C)]
struct Sqlite3Stmt {
    _opaque: [u8; 0],
}

unsafe extern "C" {
    fn sqlite3_open_v2(
        filename: *const c_char,
        pp_db: *mut *mut Sqlite3,
        flags: c_int,
        z_vfs: *const c_char,
    ) -> c_int;
    fn sqlite3_close_v2(db: *mut Sqlite3) -> c_int;
    fn sqlite3_prepare_v2(
        db: *mut Sqlite3,
        z_sql: *const c_char,
        n_byte: c_int,
        pp_stmt: *mut *mut Sqlite3Stmt,
        pz_tail: *mut *const c_char,
    ) -> c_int;
    fn sqlite3_step(stmt: *mut Sqlite3Stmt) -> c_int;
    fn sqlite3_reset(stmt: *mut Sqlite3Stmt) -> c_int;
    fn sqlite3_clear_bindings(stmt: *mut Sqlite3Stmt) -> c_int;
    fn sqlite3_finalize(stmt: *mut Sqlite3Stmt) -> c_int;

    fn sqlite3_bind_null(stmt: *mut Sqlite3Stmt, idx: c_int) -> c_int;
    fn sqlite3_bind_int64(stmt: *mut Sqlite3Stmt, idx: c_int, val: i64) -> c_int;
    fn sqlite3_bind_double(stmt: *mut Sqlite3Stmt, idx: c_int, val: f64) -> c_int;
    fn sqlite3_bind_text(
        stmt: *mut Sqlite3Stmt,
        idx: c_int,
        val: *const c_char,
        n_bytes: c_int,
        destructor: *const c_void,
    ) -> c_int;
    fn sqlite3_bind_blob(
        stmt: *mut Sqlite3Stmt,
        idx: c_int,
        val: *const c_void,
        n_bytes: c_int,
        destructor: *const c_void,
    ) -> c_int;

    fn sqlite3_column_count(stmt: *mut Sqlite3Stmt) -> c_int;
    fn sqlite3_column_name(stmt: *mut Sqlite3Stmt, col: c_int) -> *const c_char;
    fn sqlite3_column_type(stmt: *mut Sqlite3Stmt, col: c_int) -> c_int;
    fn sqlite3_column_int64(stmt: *mut Sqlite3Stmt, col: c_int) -> i64;
    fn sqlite3_column_double(stmt: *mut Sqlite3Stmt, col: c_int) -> f64;
    fn sqlite3_column_text(stmt: *mut Sqlite3Stmt, col: c_int) -> *const u8;
    fn sqlite3_column_blob(stmt: *mut Sqlite3Stmt, col: c_int) -> *const c_void;
    fn sqlite3_column_bytes(stmt: *mut Sqlite3Stmt, col: c_int) -> c_int;

    fn sqlite3_changes(db: *mut Sqlite3) -> c_int;
    fn sqlite3_errmsg(db: *mut Sqlite3) -> *const c_char;
    fn sqlite3_busy_timeout(db: *mut Sqlite3, ms: c_int) -> c_int;
    fn sqlite3_libversion() -> *const c_char;
}

/// Typed error returned by the safe SQLite FFI layer.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SqliteFfiError {
    pub code: i32,
    pub message: String,
}

impl SqliteFfiError {
    #[must_use]
    pub fn new(code: i32, message: impl Into<String>) -> Self {
        Self {
            code,
            message: message.into(),
        }
    }
}

impl fmt::Display for SqliteFfiError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "sqlite error ({}): {}", self.code, self.message)
    }
}

impl std::error::Error for SqliteFfiError {}

/// Open mode for [`SqliteConn::open`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SqliteOpenMode {
    ReadWriteCreate,
    ReadOnly,
}

/// SQLite dynamic storage class returned by `sqlite3_column_type`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SqliteValueType {
    Integer,
    Float,
    Text,
    Blob,
    Null,
}

/// Outcome of stepping a prepared [`SqliteStmt`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StepResult {
    Row,
    Done,
}

/// Safe RAII owner of a `sqlite3*` database connection handle.
///
/// Closed automatically via `sqlite3_close_v2` on `Drop`.
pub struct SqliteConn {
    db: *mut Sqlite3,
}

// SAFETY: `SqliteConn` opens the SQLite handle with `SQLITE_OPEN_FULLMUTEX` (serialized mode),
// owns the `sqlite3*` exclusively (not `Clone`, not `Sync`), and cannot outlive borrowed
// `SqliteStmt<'conn>` handles due to Rust's borrow checker. Moving exclusive ownership across
// threads is explicitly permitted by SQLite's threading contract.
unsafe impl Send for SqliteConn {}

impl fmt::Debug for SqliteConn {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("SqliteConn").finish_non_exhaustive()
    }
}

impl SqliteConn {
    /// Return the linked `libsqlite3` version string (e.g. `"3.45.1"`).
    #[must_use]
    pub fn libversion() -> String {
        // SAFETY: `sqlite3_libversion` returns a static NUL-terminated ASCII version string.
        unsafe { CStr::from_ptr(sqlite3_libversion()) }
            .to_string_lossy()
            .into_owned()
    }

    /// Open a SQLite database at `path` (or `":memory:"`) with a 5,000 ms busy timeout.
    ///
    /// # Errors
    /// Returns [`SqliteFfiError`] if `path` contains an interior NUL byte or SQLite cannot open it.
    pub fn open(path: &str, mode: SqliteOpenMode) -> Result<Self, SqliteFfiError> {
        let c_path = CString::new(path)
            .map_err(|_| SqliteFfiError::new(-1, "sqlite path contains interior NUL byte"))?;
        let flags = match mode {
            SqliteOpenMode::ReadWriteCreate => {
                SQLITE_OPEN_READWRITE | SQLITE_OPEN_CREATE | SQLITE_OPEN_FULLMUTEX
            }
            SqliteOpenMode::ReadOnly => SQLITE_OPEN_READONLY | SQLITE_OPEN_FULLMUTEX,
        };
        let mut db: *mut Sqlite3 = ptr::null_mut();
        // SAFETY: `c_path` is a valid NUL-terminated C string, `db` is a valid out-pointer,
        // and `ptr::null()` selects the default VFS.
        let rc = unsafe { sqlite3_open_v2(c_path.as_ptr(), &mut db, flags, ptr::null()) };
        if rc != SQLITE_OK {
            let msg = if db.is_null() {
                format!("sqlite3_open_v2 failed with code {rc}")
            } else {
                // SAFETY: `db` is a valid (error-state) SQLite handle returned by `sqlite3_open_v2`.
                let s = unsafe { CStr::from_ptr(sqlite3_errmsg(db)) }
                    .to_string_lossy()
                    .into_owned();
                // SAFETY: SQLite requires closing even failed non-null handles from `sqlite3_open_v2`.
                let _ = unsafe { sqlite3_close_v2(db) };
                s
            };
            return Err(SqliteFfiError::new(rc, msg));
        }
        if db.is_null() {
            return Err(SqliteFfiError::new(
                -1,
                "sqlite3_open_v2 returned null handle with SQLITE_OK",
            ));
        }
        let conn = Self { db };
        conn.busy_timeout(DEFAULT_BUSY_TIMEOUT_MS)?;
        Ok(conn)
    }

    /// Open a fresh private in-memory SQLite database.
    ///
    /// # Errors
    /// Returns [`SqliteFfiError`] if SQLite fails to allocate the in-memory database.
    pub fn open_in_memory() -> Result<Self, SqliteFfiError> {
        Self::open(":memory:", SqliteOpenMode::ReadWriteCreate)
    }

    /// Configure the busy timeout in milliseconds.
    ///
    /// # Errors
    /// Returns [`SqliteFfiError`] if SQLite rejects the call.
    pub fn busy_timeout(&self, ms: i32) -> Result<(), SqliteFfiError> {
        // SAFETY: `self.db` is a live, non-null `sqlite3*` handle owned by `self`.
        let rc = unsafe { sqlite3_busy_timeout(self.db, ms as c_int) };
        if rc != SQLITE_OK {
            return Err(self.last_error(rc));
        }
        Ok(())
    }

    /// Prepare a single SQL statement bound to this connection's lifetime.
    ///
    /// # Errors
    /// Returns [`SqliteFfiError`] if `sql` is empty, exceeds `i32::MAX` bytes, or fails to compile.
    pub fn prepare(&self, sql: &str) -> Result<SqliteStmt<'_>, SqliteFfiError> {
        let len = c_int::try_from(sql.len())
            .map_err(|_| SqliteFfiError::new(-1, "SQL statement exceeds maximum length"))?;
        let mut stmt: *mut Sqlite3Stmt = ptr::null_mut();
        let mut tail: *const c_char = ptr::null();
        // SAFETY: `self.db` is live; `sql.as_ptr()` is valid for `len` bytes; `sqlite3_prepare_v2`
        // reads at most `len` bytes and writes the compiled statement to `stmt`.
        let rc = unsafe {
            sqlite3_prepare_v2(
                self.db,
                sql.as_ptr().cast::<c_char>(),
                len,
                &mut stmt,
                &mut tail,
            )
        };
        if rc != SQLITE_OK {
            return Err(self.last_error(rc));
        }
        if stmt.is_null() {
            return Err(SqliteFfiError::new(
                -1,
                "SQL string contained no executable statement",
            ));
        }
        Ok(SqliteStmt { conn: self, stmt })
    }

    /// Execute one or more semicolon-separated parameterless SQL statements.
    ///
    /// # Errors
    /// Returns [`SqliteFfiError`] if any statement fails to prepare or step.
    pub fn execute_batch(&self, sql: &str) -> Result<(), SqliteFfiError> {
        let mut rest = sql.as_bytes();
        while !rest.is_empty() {
            let len = c_int::try_from(rest.len())
                .map_err(|_| SqliteFfiError::new(-1, "SQL batch exceeds maximum length"))?;
            let mut stmt_ptr: *mut Sqlite3Stmt = ptr::null_mut();
            let mut tail: *const c_char = ptr::null();
            let start_ptr = rest.as_ptr().cast::<c_char>();
            // SAFETY: `self.db` is live and `start_ptr` points to `len` readable UTF-8 bytes.
            let rc =
                unsafe { sqlite3_prepare_v2(self.db, start_ptr, len, &mut stmt_ptr, &mut tail) };
            if rc != SQLITE_OK {
                return Err(self.last_error(rc));
            }
            if !stmt_ptr.is_null() {
                let mut stmt = SqliteStmt {
                    conn: self,
                    stmt: stmt_ptr,
                };
                while stmt.step()? == StepResult::Row {}
            }
            if tail.is_null() {
                break;
            }
            // SAFETY: `tail` points within `[start_ptr, start_ptr + len]` as guaranteed by
            // `sqlite3_prepare_v2`.
            let consumed = unsafe { tail.offset_from(start_ptr) };
            if consumed <= 0 || consumed as usize > rest.len() {
                break;
            }
            rest = &rest[consumed as usize..];
        }
        Ok(())
    }

    /// Return the number of rows modified by the most recent `INSERT`/`UPDATE`/`DELETE`.
    #[must_use]
    pub fn changes(&self) -> u64 {
        // SAFETY: `self.db` is a live `sqlite3*` handle.
        let n = unsafe { sqlite3_changes(self.db) };
        u64::try_from(n).unwrap_or(0)
    }

    fn last_error(&self, code: c_int) -> SqliteFfiError {
        // SAFETY: `self.db` is live; `sqlite3_errmsg` returns a valid NUL-terminated UTF-8 string
        // managed by the connection until the next SQLite API call on this connection.
        let ptr = unsafe { sqlite3_errmsg(self.db) };
        let msg = if ptr.is_null() {
            format!("sqlite error code {code}")
        } else {
            // SAFETY: checked non-null above.
            unsafe { CStr::from_ptr(ptr) }
                .to_string_lossy()
                .into_owned()
        };
        SqliteFfiError::new(code, msg)
    }
}

impl Drop for SqliteConn {
    fn drop(&mut self) {
        if !self.db.is_null() {
            // SAFETY: `self.db` was created by `sqlite3_open_v2` and is closed exactly once here.
            // `sqlite3_close_v2` safely defers deallocation if anything remains and never panics.
            let _ = unsafe { sqlite3_close_v2(self.db) };
            self.db = ptr::null_mut();
        }
    }
}

/// Safe RAII owner of a prepared `sqlite3_stmt*` borrowing its parent [`SqliteConn`].
///
/// Finalized automatically via `sqlite3_finalize` on `Drop`.
pub struct SqliteStmt<'conn> {
    conn: &'conn SqliteConn,
    stmt: *mut Sqlite3Stmt,
}

impl fmt::Debug for SqliteStmt<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("SqliteStmt").finish_non_exhaustive()
    }
}

impl SqliteStmt<'_> {
    /// Bind SQL `NULL` to 1-based parameter `idx`.
    ///
    /// # Errors
    /// Returns [`SqliteFfiError`] if `idx` is out of range or SQLite rejects the bind.
    pub fn bind_null(&mut self, idx: i32) -> Result<(), SqliteFfiError> {
        // SAFETY: `self.stmt` is a live prepared statement.
        let rc = unsafe { sqlite3_bind_null(self.stmt, idx as c_int) };
        if rc != SQLITE_OK {
            return Err(self.conn.last_error(rc));
        }
        Ok(())
    }

    /// Bind a 64-bit signed integer to 1-based parameter `idx`.
    ///
    /// # Errors
    /// Returns [`SqliteFfiError`] if `idx` is out of range or SQLite rejects the bind.
    pub fn bind_int64(&mut self, idx: i32, val: i64) -> Result<(), SqliteFfiError> {
        // SAFETY: `self.stmt` is a live prepared statement.
        let rc = unsafe { sqlite3_bind_int64(self.stmt, idx as c_int, val) };
        if rc != SQLITE_OK {
            return Err(self.conn.last_error(rc));
        }
        Ok(())
    }

    /// Bind an IEEE-754 `f64` to 1-based parameter `idx`.
    ///
    /// # Errors
    /// Returns [`SqliteFfiError`] if `idx` is out of range or SQLite rejects the bind.
    pub fn bind_double(&mut self, idx: i32, val: f64) -> Result<(), SqliteFfiError> {
        // SAFETY: `self.stmt` is a live prepared statement.
        let rc = unsafe { sqlite3_bind_double(self.stmt, idx as c_int, val) };
        if rc != SQLITE_OK {
            return Err(self.conn.last_error(rc));
        }
        Ok(())
    }

    /// Bind UTF-8 text to 1-based parameter `idx` (copied immediately via `SQLITE_TRANSIENT`).
    ///
    /// # Errors
    /// Returns [`SqliteFfiError`] if `val` exceeds `i32::MAX` bytes or SQLite rejects the bind.
    pub fn bind_text(&mut self, idx: i32, val: &str) -> Result<(), SqliteFfiError> {
        let len = c_int::try_from(val.len())
            .map_err(|_| SqliteFfiError::new(-1, "bound text exceeds i32::MAX bytes"))?;
        // Pass a valid non-null pointer even for empty strings so SQLite binds `''` instead of NULL.
        let ptr = if val.is_empty() {
            c"".as_ptr()
        } else {
            val.as_ptr().cast::<c_char>()
        };
        // SAFETY: `self.stmt` is live, `ptr` points to `len` valid UTF-8 bytes, and
        // `sqlite_transient()` makes SQLite copy the bytes before `bind_text` returns.
        let rc =
            unsafe { sqlite3_bind_text(self.stmt, idx as c_int, ptr, len, sqlite_transient()) };
        if rc != SQLITE_OK {
            return Err(self.conn.last_error(rc));
        }
        Ok(())
    }

    /// Bind raw bytes to 1-based parameter `idx` (copied immediately via `SQLITE_TRANSIENT`).
    ///
    /// # Errors
    /// Returns [`SqliteFfiError`] if `val` exceeds `i32::MAX` bytes or SQLite rejects the bind.
    pub fn bind_blob(&mut self, idx: i32, val: &[u8]) -> Result<(), SqliteFfiError> {
        let len = c_int::try_from(val.len())
            .map_err(|_| SqliteFfiError::new(-1, "bound blob exceeds i32::MAX bytes"))?;
        // Use a non-null sentinel for empty slices so SQLite binds an empty BLOB `X''` rather than NULL.
        static EMPTY_BLOB_SENTINEL: u8 = 0;
        let ptr = if val.is_empty() {
            ptr::from_ref(&EMPTY_BLOB_SENTINEL).cast::<c_void>()
        } else {
            val.as_ptr().cast::<c_void>()
        };
        // SAFETY: `self.stmt` is live, `ptr` is non-null and valid for `len` bytes, and
        // `sqlite_transient()` makes SQLite copy the bytes before `bind_blob` returns.
        let rc =
            unsafe { sqlite3_bind_blob(self.stmt, idx as c_int, ptr, len, sqlite_transient()) };
        if rc != SQLITE_OK {
            return Err(self.conn.last_error(rc));
        }
        Ok(())
    }

    /// Advance the prepared statement by one row.
    ///
    /// # Errors
    /// Returns [`SqliteFfiError`] on constraint, busy, I/O, or SQL runtime errors.
    pub fn step(&mut self) -> Result<StepResult, SqliteFfiError> {
        // SAFETY: `self.stmt` is a live prepared statement.
        match unsafe { sqlite3_step(self.stmt) } {
            SQLITE_ROW => Ok(StepResult::Row),
            SQLITE_DONE => Ok(StepResult::Done),
            other => Err(self.conn.last_error(other)),
        }
    }

    /// Reset the statement so it can be stepped again.
    ///
    /// # Errors
    /// Returns [`SqliteFfiError`] if SQLite reports an error from the previous run.
    pub fn reset(&mut self) -> Result<(), SqliteFfiError> {
        // SAFETY: `self.stmt` is a live prepared statement.
        let rc = unsafe { sqlite3_reset(self.stmt) };
        if rc != SQLITE_OK {
            return Err(self.conn.last_error(rc));
        }
        Ok(())
    }

    /// Reset all bound parameters to `NULL`.
    ///
    /// # Errors
    /// Returns [`SqliteFfiError`] if SQLite rejects clearing bindings.
    pub fn clear_bindings(&mut self) -> Result<(), SqliteFfiError> {
        // SAFETY: `self.stmt` is a live prepared statement.
        let rc = unsafe { sqlite3_clear_bindings(self.stmt) };
        if rc != SQLITE_OK {
            return Err(self.conn.last_error(rc));
        }
        Ok(())
    }

    /// Return the number of result columns in the current prepared statement.
    #[must_use]
    pub fn column_count(&self) -> usize {
        // SAFETY: `self.stmt` is a live prepared statement.
        let n = unsafe { sqlite3_column_count(self.stmt) };
        usize::try_from(n).unwrap_or(0)
    }

    /// Return the name of 0-based result column `col`, if valid.
    #[must_use]
    pub fn column_name(&self, col: usize) -> Option<String> {
        let idx = c_int::try_from(col).ok()?;
        // SAFETY: `self.stmt` is live; `sqlite3_column_name` returns NULL if `idx` is out of range,
        // otherwise a valid NUL-terminated UTF-8 string owned by the statement.
        let ptr = unsafe { sqlite3_column_name(self.stmt, idx) };
        if ptr.is_null() {
            return None;
        }
        // SAFETY: checked non-null above.
        Some(
            unsafe { CStr::from_ptr(ptr) }
                .to_string_lossy()
                .into_owned(),
        )
    }

    /// Return the dynamic storage class of 0-based column `col` in the current row.
    #[must_use]
    pub fn column_type(&self, col: usize) -> SqliteValueType {
        let Ok(idx) = c_int::try_from(col) else {
            return SqliteValueType::Null;
        };
        // SAFETY: `self.stmt` is a live prepared statement.
        match unsafe { sqlite3_column_type(self.stmt, idx) } {
            SQLITE_INTEGER => SqliteValueType::Integer,
            SQLITE_FLOAT => SqliteValueType::Float,
            SQLITE_TEXT => SqliteValueType::Text,
            SQLITE_BLOB => SqliteValueType::Blob,
            SQLITE_NULL => SqliteValueType::Null,
            _ => SqliteValueType::Null,
        }
    }

    /// Read 0-based column `col` as a signed 64-bit integer.
    #[must_use]
    pub fn column_int64(&self, col: usize) -> i64 {
        let Ok(idx) = c_int::try_from(col) else {
            return 0;
        };
        // SAFETY: `self.stmt` is a live prepared statement.
        unsafe { sqlite3_column_int64(self.stmt, idx) }
    }

    /// Read 0-based column `col` as an IEEE-754 `f64`.
    #[must_use]
    pub fn column_double(&self, col: usize) -> f64 {
        let Ok(idx) = c_int::try_from(col) else {
            return 0.0;
        };
        // SAFETY: `self.stmt` is a live prepared statement.
        unsafe { sqlite3_column_double(self.stmt, idx) }
    }

    /// Read 0-based column `col` as a UTF-8 `String`.
    ///
    /// # Errors
    /// Returns [`SqliteFfiError`] if the underlying bytes are not valid UTF-8.
    pub fn column_text(&self, col: usize) -> Result<String, SqliteFfiError> {
        let idx = c_int::try_from(col)
            .map_err(|_| SqliteFfiError::new(-1, "column index out of range"))?;
        // Per SQLite docs, call `sqlite3_column_text` before `sqlite3_column_bytes` so any
        // type conversion completes before measuring byte length.
        // SAFETY: `self.stmt` is live; returned pointer is valid until next step/reset/finalize.
        let ptr = unsafe { sqlite3_column_text(self.stmt, idx) };
        if ptr.is_null() {
            return Ok(String::new());
        }
        // SAFETY: `self.stmt` is live and `sqlite3_column_text` already ran for `idx`.
        let n_bytes = unsafe { sqlite3_column_bytes(self.stmt, idx) };
        let len = usize::try_from(n_bytes).unwrap_or(0);
        if len == 0 {
            return Ok(String::new());
        }
        // SAFETY: `ptr` is non-null and SQLite guarantees `len` valid readable bytes.
        let bytes = unsafe { slice::from_raw_parts(ptr, len) };
        std::str::from_utf8(bytes)
            .map(ToOwned::to_owned)
            .map_err(|e| SqliteFfiError::new(-1, format!("invalid UTF-8 in SQLite text: {e}")))
    }

    /// Read 0-based column `col` as a raw byte vector.
    #[must_use]
    pub fn column_blob(&self, col: usize) -> Vec<u8> {
        let Ok(idx) = c_int::try_from(col) else {
            return Vec::new();
        };
        // Per SQLite docs, call `sqlite3_column_blob` before `sqlite3_column_bytes`.
        // SAFETY: `self.stmt` is live; returned pointer is valid until next step/reset/finalize.
        let ptr = unsafe { sqlite3_column_blob(self.stmt, idx) };
        if ptr.is_null() {
            return Vec::new();
        }
        // SAFETY: `self.stmt` is live and `sqlite3_column_blob` already ran for `idx`.
        let n_bytes = unsafe { sqlite3_column_bytes(self.stmt, idx) };
        let len = usize::try_from(n_bytes).unwrap_or(0);
        if len == 0 {
            return Vec::new();
        }
        // SAFETY: `ptr` is non-null and SQLite guarantees `len` valid readable bytes.
        let bytes = unsafe { slice::from_raw_parts(ptr.cast::<u8>(), len) };
        bytes.to_vec()
    }
}

impl Drop for SqliteStmt<'_> {
    fn drop(&mut self) {
        if !self.stmt.is_null() {
            // SAFETY: `self.stmt` was created by `sqlite3_prepare_v2` on `self.conn` (which is
            // guaranteed still alive by `'conn`) and is finalized exactly once here.
            let _ = unsafe { sqlite3_finalize(self.stmt) };
            self.stmt = ptr::null_mut();
        }
    }
}
