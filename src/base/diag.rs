//! Structured, privacy-safe compiler and runtime diagnostics.
//!
//! Diagnostics NEVER include unredacted values from sensitivity-tagged columns or bindings.
//! Payload is heap-boxed (`size_of::<Diagnostic>() == 8`) so `Result<T, Diagnostic>` stays
//! pointer-sized across deep parser/checker call stacks.

use std::fmt::Write as _;

use crate::base::span::{SourceMap, Span};

/// Diagnostic severity level.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Severity {
    Error,
    Warning,
}

impl Severity {
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Error => "error",
            Self::Warning => "warning",
        }
    }
}

/// Stable diagnostic code identifying the compiler phase and error category.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum DiagCode {
    LexError,
    ParseError,
    PolicyError,
    ResolveError,
    SchemaError,
    TypeError,
    PrivacyError,
    CapabilityError,
    ExhaustivenessError,
    LowerError,
    CoreVerifyError,
    RuntimeStop,
    RuntimeFailure,
    IoError,
}

impl DiagCode {
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::LexError => "E0001",
            Self::ParseError => "E0002",
            Self::PolicyError => "E0100",
            Self::ResolveError => "E0101",
            Self::SchemaError => "E0200",
            Self::TypeError => "E0201",
            Self::PrivacyError => "E0202",
            Self::CapabilityError => "E0203",
            Self::ExhaustivenessError => "E0204",
            Self::LowerError => "E0300",
            Self::CoreVerifyError => "E0301",
            Self::RuntimeStop => "E0400",
            Self::RuntimeFailure => "E0401",
            Self::IoError => "E0500",
        }
    }
}

/// Span-anchored explanatory label attached to a [`Diagnostic`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Label {
    pub span: Span,
    pub message: String,
}

impl Label {
    #[must_use]
    pub fn new(span: Span, message: impl Into<String>) -> Self {
        Self {
            span,
            message: message.into(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct DiagnosticInner {
    code: DiagCode,
    severity: Severity,
    message: String,
    primary: Option<Label>,
    secondary: Vec<Label>,
    notes: Vec<String>,
    hints: Vec<String>,
}

/// A single structured compiler or runtime diagnostic (pointer-sized handle).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Diagnostic(Box<DiagnosticInner>);

impl Diagnostic {
    #[must_use]
    pub fn error(code: DiagCode, message: impl Into<String>) -> Self {
        Self(Box::new(DiagnosticInner {
            code,
            severity: Severity::Error,
            message: message.into(),
            primary: None,
            secondary: Vec::new(),
            notes: Vec::new(),
            hints: Vec::new(),
        }))
    }

    #[must_use]
    pub fn warning(code: DiagCode, message: impl Into<String>) -> Self {
        Self(Box::new(DiagnosticInner {
            code,
            severity: Severity::Warning,
            message: message.into(),
            primary: None,
            secondary: Vec::new(),
            notes: Vec::new(),
            hints: Vec::new(),
        }))
    }

    #[must_use]
    pub const fn code(&self) -> DiagCode {
        self.0.code
    }

    #[must_use]
    pub const fn severity(&self) -> Severity {
        self.0.severity
    }

    #[must_use]
    pub fn message(&self) -> &str {
        &self.0.message
    }

    #[must_use]
    pub fn primary(&self) -> Option<&Label> {
        self.0.primary.as_ref()
    }

    #[must_use]
    pub fn secondary(&self) -> &[Label] {
        &self.0.secondary
    }

    #[must_use]
    pub fn notes(&self) -> &[String] {
        &self.0.notes
    }

    #[must_use]
    pub fn hints(&self) -> &[String] {
        &self.0.hints
    }

    #[must_use]
    pub fn with_primary(mut self, span: Span, message: impl Into<String>) -> Self {
        self.0.primary = Some(Label::new(span, message));
        self
    }

    #[must_use]
    pub fn with_span(mut self, span: Span) -> Self {
        self.0.primary = Some(Label::new(span, String::new()));
        self
    }

    #[must_use]
    pub fn with_secondary(mut self, span: Span, message: impl Into<String>) -> Self {
        self.0.secondary.push(Label::new(span, message));
        self
    }

    #[must_use]
    pub fn with_note(mut self, note: impl Into<String>) -> Self {
        self.0.notes.push(note.into());
        self
    }

    #[must_use]
    pub fn with_hint(mut self, hint: impl Into<String>) -> Self {
        self.0.hints.push(hint.into());
        self
    }
}

/// Render a human-readable terminal diagnostic with source line snippet and carets.
#[must_use]
pub fn render_diagnostic(diag: &Diagnostic, sm: &SourceMap) -> String {
    let mut out = String::new();
    let _ = writeln!(
        out,
        "{}[{}]: {}",
        diag.severity().as_str(),
        diag.code().as_str(),
        diag.message()
    );
    if let Some(primary) = diag.primary() {
        render_label(&mut out, primary, sm, '^');
    }
    for sec in diag.secondary() {
        render_label(&mut out, sec, sm, '-');
    }
    for note in diag.notes() {
        let _ = writeln!(out, "  = note: {note}");
    }
    for hint in diag.hints() {
        let _ = writeln!(out, "  = hint: {hint}");
    }
    out
}

fn render_label(out: &mut String, label: &Label, sm: &SourceMap, marker: char) {
    let Some(file) = sm.file(label.span.file) else {
        return;
    };
    let start = file.line_col(label.span.start);
    let end = file.line_col(label.span.end);
    let _ = writeln!(out, "  --> {}:{}:{}", file.name, start.line, start.col);
    if let Some(line_str) = file.line_text(start.line) {
        let line_num = start.line.to_string();
        let pad = " ".repeat(line_num.len());
        let _ = writeln!(out, "  {pad} |");
        let _ = writeln!(out, "  {line_num} | {line_str}");
        let col0 = start.col.saturating_sub(1) as usize;
        let width = if end.line == start.line && end.col > start.col {
            (end.col - start.col) as usize
        } else {
            1
        };
        let spaces = " ".repeat(col0);
        let carets: String = std::iter::repeat_n(marker, width.max(1)).collect();
        if label.message.is_empty() {
            let _ = writeln!(out, "  {pad} | {spaces}{carets}");
        } else {
            let _ = writeln!(out, "  {pad} | {spaces}{carets} {}", label.message);
        }
    }
}

fn json_escape(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for ch in s.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => {
                let _ = write!(out, "\\u{:04x}", c as u32);
            }
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

/// Render a list of diagnostics as a self-contained RFC 8259 JSON array.
#[must_use]
pub fn render_diagnostics_json(diags: &[Diagnostic], sm: &SourceMap) -> String {
    let mut out = String::from("[");
    for (idx, d) in diags.iter().enumerate() {
        if idx > 0 {
            out.push(',');
        }
        out.push('{');
        let _ = write!(
            out,
            "\"code\":{},\"severity\":{},\"message\":{}",
            json_escape(d.code().as_str()),
            json_escape(d.severity().as_str()),
            json_escape(d.message()),
        );
        if let Some(p) = d.primary()
            && let Some(file) = sm.file(p.span.file)
        {
            let s = file.line_col(p.span.start);
            let e = file.line_col(p.span.end);
            let _ = write!(
                out,
                ",\"file\":{},\"start_line\":{},\"start_col\":{},\"end_line\":{},\"end_col\":{}",
                json_escape(&file.name),
                s.line,
                s.col,
                e.line,
                e.col
            );
        }
        if !d.notes().is_empty() {
            out.push_str(",\"notes\":[");
            for (i, n) in d.notes().iter().enumerate() {
                if i > 0 {
                    out.push(',');
                }
                out.push_str(&json_escape(n));
            }
            out.push(']');
        }
        if !d.hints().is_empty() {
            out.push_str(",\"hints\":[");
            for (i, h) in d.hints().iter().enumerate() {
                if i > 0 {
                    out.push(',');
                }
                out.push_str(&json_escape(h));
            }
            out.push(']');
        }
        out.push('}');
    }
    out.push(']');
    out
}
