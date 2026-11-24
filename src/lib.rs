#![forbid(unsafe_code)]

//! Dana programming language toolchain:
//! - `base`: source maps, spans, and privacy-safe diagnostics
//! - `syntax`: lexer, parser (100% Bison IELR(1) parity), Surface AST, and canonical formatter
//! - `check`: `dana.policy` parser, module resolver, structural Table + privacy/capability checker
//! - `lower`: surface-to-execution IR & Core IR v0.1 verifier bridge
//! - `formats`: built-in calendar/temporal math and RFC 4180 CSV/TSV quarantine codecs
//! - `runtime`: Phase 2 execution IR and reference runtime evaluator
//! - `cli`: `dana` CLI subcommand dispatcher
//! - `core`: Dana Core IR v0.1 AST, canonical wire codec, and decidable static verifier
//! - `oracle`: naive row-by-row differential reference oracle

pub mod base;
pub mod check;
pub mod cli;
pub mod core;
pub mod formats;
pub mod lower;
pub mod oracle;
pub mod runtime;
pub mod syntax;
