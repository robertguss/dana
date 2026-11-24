//! Audited, isolated FFI shims to allowlisted system C libraries (`zlib`, `libzstd`).
//!
//! All other modules in the `dana` crate compile under `#[forbid(unsafe_code)]`.
//! Every `unsafe` block in this module is documented with a `// SAFETY:` justification,
//! and all C resources are wrapped in safe RAII handles with explicit fallible `finish()`.

pub mod zlib;
pub mod zstd;

pub use zlib::{GzipReader, GzipWriter};
pub use zstd::{ZstdReader, ZstdWriter};
