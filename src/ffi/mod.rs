//! Audited, isolated FFI shims to allowlisted system C libraries (`zlib`, `libzstd`, `sqlite3`, `openssl`).
//!
//! All other modules in the `dana` crate compile under `#[forbid(unsafe_code)]`.
//! Every `unsafe` block in this module is documented with a `// SAFETY:` justification,
//! and all C resources are wrapped in safe RAII handles with deterministic cleanup.

pub mod sqlite;
pub mod tls;
pub mod zlib;
pub mod zstd;

pub use sqlite::{
    SqliteConn, SqliteFfiError, SqliteOpenMode, SqliteStmt, SqliteValueType, StepResult,
};
pub use tls::{TlsClientConfig, TlsServerAcceptor, TlsStream};
pub use zlib::{GzipReader, GzipWriter};
pub use zstd::{ZstdReader, ZstdWriter};
