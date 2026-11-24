//! Shared compiler primitives: source maps, byte spans, line/column tables,
//! and privacy-safe structured diagnostics.

pub mod diag;
pub mod span;

pub use diag::{DiagCode, Diagnostic, Label, Severity, render_diagnostic, render_diagnostics_json};
pub use span::{FileId, LineCol, SourceFile, SourceMap, Span};
