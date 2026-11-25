//! Dana programming language toolchain:
//! - `base`: source maps, spans, and privacy-safe diagnostics
//! - `syntax`: lexer, parser (100% Bison IELR(1) parity), Surface AST, and canonical formatter
//! - `check`: `dana.policy` parser, module resolver, structural Table + privacy/capability checker
//! - `lower`: surface-to-execution IR & Core IR v0.1 verifier bridge
//! - `ffi`: audited RAII FFI wrappers around allowlisted system `zlib`, `libzstd`, `sqlite3`, and OpenSSL TLS
//! - `db`: SQLite and native PostgreSQL v3.0 drivers, offline `schema.lock`, and privacy-redacted dry-run diffs
//! - `formats`: built-in calendar/TZif temporal math, HMAC-SHA256, streaming CSV/TSV, JSON/JSONL, PKZIP, XLSX, Parquet, schema inference & fake data generation
//! - `net`: capability-gated HTTP/1.1 HTTPS client (`HttpsAllow`) & `JsonResponse` helpers
//! - `stats`: statistical analytics stdlib (Pearson/Spearman correlation, OLS regression, Welch t-test, chi-square, outlier detection) & privacy-safe dataset profiler
//! - `viz`: zero-dependency standalone SVG & Unicode terminal charts, plus self-contained HTML5 & Markdown reports
//! - `plan`: relational query optimizer (filter fusion, predicate pushdown, dead-derive pruning) & plan explainer
//! - `vm`: 2,048-row vectorized columnar batch VM, compiled row bytecode (inlined pure UDFs), & deterministic parallel runner
//! - `repl`: safe read-only interactive REPL, privacy-redacted output, and `untyped` data explorer
//! - `runtime`: Phase 2 execution IR and reference runtime evaluator
//! - `cli`: `dana` CLI subcommand dispatcher
//! - `core`: Dana Core IR v0.1 AST, canonical wire codec, and decidable static verifier
//! - `oracle`: naive row-by-row differential reference oracle

#[forbid(unsafe_code)]
pub mod base;
#[forbid(unsafe_code)]
pub mod check;
#[forbid(unsafe_code)]
pub mod cli;
#[forbid(unsafe_code)]
pub mod core;
#[forbid(unsafe_code)]
pub mod db;
pub mod ffi;
#[forbid(unsafe_code)]
pub mod formats;
#[forbid(unsafe_code)]
pub mod lower;
#[forbid(unsafe_code)]
pub mod net;
#[forbid(unsafe_code)]
pub mod oracle;
#[forbid(unsafe_code)]
pub mod plan;
#[forbid(unsafe_code)]
pub mod repl;
#[forbid(unsafe_code)]
pub mod runtime;
#[forbid(unsafe_code)]
pub mod stats;
#[forbid(unsafe_code)]
pub mod syntax;
#[forbid(unsafe_code)]
pub mod viz;
#[forbid(unsafe_code)]
pub mod vm;
