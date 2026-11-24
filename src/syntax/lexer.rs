//! UTF-8 Dana lexer with 1-to-1 behavioral parity against `grammar/lexer.c`.
//!
//! Enforces strict UTF-8 and forbidden invisible/bidi/control character rejection,
//! automatic newline continuations, `#{...}` string interpolation, triple-quoted
//! multiline dedent, `?`/`!` name suffixes, contextual `:atom`, and ISO `Date`/`Timestamp`.

use crate::base::{DiagCode, Diagnostic, FileId, Span};
use crate::syntax::token::{Comment, Token, TokenKind};

/// Output of lexing a Dana source file or fragment.
#[derive(Clone, Debug)]
pub struct LexOutput {
    pub tokens: Vec<Token>,
    pub comments: Vec<Comment>,
}

#[derive(Clone, Copy, Debug)]
struct InterpFrame {
    saved_paren_depth: usize,
    multiline: bool,
}

struct Lexer<'a> {
    file: FileId,
    src: &'a str,
    bytes: &'a [u8],
    pos: usize,
    line: u32,
    paren_depth: usize,
    prev_token: Option<TokenKind>,
    prev_token_line: u32,
    interp_stack: Vec<InterpFrame>,
    tokens: Vec<Token>,
    comments: Vec<Comment>,
}

/// Validate raw bytes as UTF-8 and lex into tokens + comments.
///
/// # Errors
/// Returns a [`Diagnostic`] with [`DiagCode::LexError`] on invalid UTF-8, forbidden
/// invisible/control characters, unterminated strings/escapes, or unexpected tokens.
pub fn lex_bytes(file: FileId, bytes: &[u8]) -> Result<LexOutput, Diagnostic> {
    let src = std::str::from_utf8(bytes).map_err(|err| {
        let off = u32::try_from(err.valid_up_to()).unwrap_or(u32::MAX);
        Diagnostic::error(DiagCode::LexError, "invalid UTF-8 in source file")
            .with_primary(Span::point(file, off), "invalid UTF-8 byte sequence")
    })?;
    lex(file, src)
}

/// Lex a UTF-8 Dana source string into tokens + comments.
///
/// # Errors
/// Returns a [`Diagnostic`] with [`DiagCode::LexError`] on forbidden invisible/control
/// characters, malformed escapes/strings, or unexpected characters.
pub fn lex(file: FileId, src: &str) -> Result<LexOutput, Diagnostic> {
    validate_forbidden_chars(file, src)?;
    let mut lx = Lexer {
        file,
        src,
        bytes: src.as_bytes(),
        pos: 0,
        line: 1,
        paren_depth: 0,
        prev_token: None,
        prev_token_line: 0,
        interp_stack: Vec::new(),
        tokens: Vec::new(),
        comments: Vec::new(),
    };
    lx.run()?;
    Ok(LexOutput {
        tokens: lx.tokens,
        comments: lx.comments,
    })
}

/// Reject ASCII controls except `\t`, `\n`, `\r`, plus `0x7F` and bidi/zero-width characters
/// anywhere in source (Reference §2.1, mirrors `grammar/lexer.c:validate_utf8_and_chars`).
fn validate_forbidden_chars(file: FileId, src: &str) -> Result<(), Diagnostic> {
    for (byte_idx, ch) in src.char_indices() {
        let cp = ch as u32;
        let forbidden = (cp < 0x20 && ch != '\t' && ch != '\n' && ch != '\r')
            || cp == 0x7F
            || (0x200B..=0x200F).contains(&cp)
            || (0x202A..=0x202E).contains(&cp)
            || (0x2066..=0x2069).contains(&cp)
            || cp == 0xFEFF;
        if forbidden {
            let start = u32::try_from(byte_idx).unwrap_or(u32::MAX);
            let end = u32::try_from(byte_idx + ch.len_utf8()).unwrap_or(u32::MAX);
            return Err(Diagnostic::error(
                DiagCode::LexError,
                format!("forbidden invisible or control character U+{cp:04X} in source"),
            )
            .with_primary(
                Span::new(file, start, end),
                "use a Unicode escape (e.g. `\\u{...}`) inside a string instead",
            ));
        }
    }
    Ok(())
}

fn is_ident_start(b: u8) -> bool {
    b.is_ascii_alphabetic() || b == b'_'
}

fn is_ident_cont(b: u8) -> bool {
    b.is_ascii_alphanumeric() || b == b'_'
}

fn lookup_keyword(s: &str) -> Option<TokenKind> {
    match s {
        "and" => Some(TokenKind::KwAnd),
        "assert" => Some(TokenKind::KwAssert),
        "break" => Some(TokenKind::KwBreak),
        "case" => Some(TokenKind::KwCase),
        "const" => Some(TokenKind::KwConst),
        "continue" => Some(TokenKind::KwContinue),
        "else" => Some(TokenKind::KwElse),
        "end" => Some(TokenKind::KwEnd),
        "enum" => Some(TokenKind::KwEnum),
        "examples" => Some(TokenKind::KwExamples),
        "expose" => Some(TokenKind::KwExpose),
        "false" => Some(TokenKind::KwFalse),
        "fn" => Some(TokenKind::KwFn),
        "for" => Some(TokenKind::KwFor),
        "if" => Some(TokenKind::KwIf),
        "in" => Some(TokenKind::KwIn),
        "is" => Some(TokenKind::KwIs),
        "module" => Some(TokenKind::KwModule),
        "none" => Some(TokenKind::KwNone),
        "not" => Some(TokenKind::KwNot),
        "or" => Some(TokenKind::KwOr),
        "promise" => Some(TokenKind::KwPromise),
        "return" => Some(TokenKind::KwReturn),
        "schema" => Some(TokenKind::KwSchema),
        "stop" => Some(TokenKind::KwStop),
        "struct" => Some(TokenKind::KwStruct),
        "table" => Some(TokenKind::KwTable),
        "tag" => Some(TokenKind::KwTag),
        "test" => Some(TokenKind::KwTest),
        "true" => Some(TokenKind::KwTrue),
        "try" => Some(TokenKind::KwTry),
        "use" => Some(TokenKind::KwUse),
        "var" => Some(TokenKind::KwVar),
        "where" => Some(TokenKind::KwWhere),
        "while" => Some(TokenKind::KwWhile),
        _ => None,
    }
}

/// Dedent a triple-quoted multiline string literal per Dana rules:
/// - Strips a single immediately following `\r\n` or `\n` after `"""`.
/// - If the final line before the closing `"""` is horizontal whitespace only, strips it
///   (preserving the preceding newline if any).
/// - Strips the common minimum indentation of all non-empty lines.
fn dedent_multiline(raw_body: &str) -> String {
    let s = raw_body
        .strip_prefix("\r\n")
        .or_else(|| raw_body.strip_prefix('\n'))
        .unwrap_or(raw_body);

    // Check if the trailing segment after the last '\n' is whitespace-only (the closing `"""` indent).
    let trimmed = if let Some(last_nl) = s.rfind('\n') {
        let after = &s[last_nl + 1..];
        if after.bytes().all(|b| b == b' ' || b == b'\t') {
            &s[..=last_nl]
        } else {
            s
        }
    } else if s.bytes().all(|b| b == b' ' || b == b'\t') {
        ""
    } else {
        s
    };

    let min_indent = trimmed
        .split('\n')
        .filter(|line| !line.trim_end_matches('\r').is_empty())
        .map(|line| {
            line.bytes()
                .take_while(|&b| b == b' ' || b == b'\t')
                .count()
        })
        .min()
        .unwrap_or(0);

    if min_indent == 0 {
        return trimmed.replace("\r\n", "\n");
    }

    let mut out = String::with_capacity(trimmed.len());
    let parts: Vec<&str> = trimmed.split('\n').collect();
    for (idx, part) in parts.iter().enumerate() {
        let clean = part.trim_end_matches('\r');
        if clean.len() >= min_indent
            && clean.as_bytes()[..min_indent]
                .iter()
                .all(|&b| b == b' ' || b == b'\t')
        {
            out.push_str(&clean[min_indent..]);
        } else {
            out.push_str(clean);
        }
        if idx + 1 < parts.len() {
            out.push('\n');
        }
    }
    out
}

impl<'a> Lexer<'a> {
    fn peek(&self, offset: usize) -> u8 {
        self.bytes.get(self.pos + offset).copied().unwrap_or(0)
    }

    fn advance_byte(&mut self) -> u8 {
        let b = self.peek(0);
        if self.pos < self.bytes.len() {
            self.pos += 1;
            if b == b'\n' {
                self.line += 1;
            }
        }
        b
    }

    fn span(&self, start: usize, end: usize) -> Span {
        Span::new(
            self.file,
            u32::try_from(start).unwrap_or(u32::MAX),
            u32::try_from(end).unwrap_or(u32::MAX),
        )
    }

    fn emit(&mut self, kind: TokenKind, start: usize, end: usize, token_line: u32) {
        self.prev_token = Some(kind.clone());
        if !matches!(kind, TokenKind::Newline | TokenKind::Eof) {
            self.prev_token_line = token_line;
        }
        self.tokens.push(Token {
            kind,
            span: self.span(start, end),
        });
    }

    /// Mirrors `grammar/lexer.c:next_line_continues`.
    fn next_line_continues(&self) -> bool {
        let mut p = self.pos;
        while p < self.bytes.len() {
            let b = self.bytes[p];
            if matches!(b, b' ' | b'\t' | b'\r' | b'\n') {
                p += 1;
                continue;
            }
            if b == b'#' {
                while p < self.bytes.len() && self.bytes[p] != b'\n' {
                    p += 1;
                }
                continue;
            }
            break;
        }
        if p >= self.bytes.len() {
            return false;
        }
        let b = self.bytes[p];
        let b2 = self.bytes.get(p + 1).copied().unwrap_or(0);
        if matches!(b, b'.' | b')' | b']' | b'}' | b'+' | b'*' | b'/' | b'%') {
            return true;
        }
        if (b == b'|' && b2 == b'>')
            || (b == b'?' && b2 == b'?')
            || (b == b'=' && b2 == b'=')
            || (b == b'!' && b2 == b'=')
            || b == b'<'
            || b == b'>'
        {
            return true;
        }
        let rest = &self.bytes[p..];
        if rest.starts_with(b"and") && rest.get(3).is_none_or(|&x| !is_ident_cont(x)) {
            return true;
        }
        if rest.starts_with(b"or") && rest.get(2).is_none_or(|&x| !is_ident_cont(x)) {
            return true;
        }
        if rest.starts_with(b"is") && rest.get(2).is_none_or(|&x| !is_ident_cont(x)) {
            return true;
        }
        false
    }

    fn is_4d_2d_2d(&self, p: usize) -> bool {
        if p + 10 > self.bytes.len() {
            return false;
        }
        let s = &self.bytes[p..p + 10];
        s[0].is_ascii_digit()
            && s[1].is_ascii_digit()
            && s[2].is_ascii_digit()
            && s[3].is_ascii_digit()
            && s[4] == b'-'
            && s[5].is_ascii_digit()
            && s[6].is_ascii_digit()
            && s[7] == b'-'
            && s[8].is_ascii_digit()
            && s[9].is_ascii_digit()
    }

    fn lex_escape(&mut self, out: &mut String, esc_start: usize) -> Result<(), Diagnostic> {
        // Leading `\` already consumed.
        if self.pos >= self.bytes.len() {
            return Err(
                Diagnostic::error(DiagCode::LexError, "unterminated string escape").with_primary(
                    self.span(esc_start, self.pos),
                    "expected escape sequence after `\\`",
                ),
            );
        }
        let b = self.advance_byte();
        match b {
            b'"' => out.push('"'),
            b'\\' => out.push('\\'),
            b'n' => out.push('\n'),
            b'r' => out.push('\r'),
            b't' => out.push('\t'),
            b'0' => out.push('\0'),
            b'#' => out.push('#'),
            b'u' if self.peek(0) == b'{' => {
                self.advance_byte(); // '{'
                let hex_start = self.pos;
                while self.pos < self.bytes.len() && self.peek(0) != b'}' {
                    let hb = self.peek(0);
                    if !hb.is_ascii_hexdigit() {
                        return Err(Diagnostic::error(
                            DiagCode::LexError,
                            "invalid hex digit in Unicode escape",
                        )
                        .with_primary(
                            self.span(esc_start, self.pos + 1),
                            "expected hexadecimal digits inside `\\u{...}`",
                        ));
                    }
                    self.advance_byte();
                }
                let hex_end = self.pos;
                if self.peek(0) != b'}' || hex_end == hex_start || hex_end - hex_start > 6 {
                    return Err(Diagnostic::error(
                        DiagCode::LexError,
                        "malformed Unicode escape sequence",
                    )
                    .with_primary(
                        self.span(esc_start, self.pos),
                        "expected `\\u{HEX}` with 1 to 6 hex digits",
                    ));
                }
                self.advance_byte(); // '}'
                let hex_str = &self.src[hex_start..hex_end];
                let code = u32::from_str_radix(hex_str, 16)
                    .ok()
                    .and_then(char::from_u32);
                match code {
                    Some(ch) => out.push(ch),
                    None => {
                        return Err(Diagnostic::error(
                            DiagCode::LexError,
                            format!("invalid Unicode scalar value `\\u{{{hex_str}}}`"),
                        )
                        .with_primary(
                            self.span(esc_start, self.pos),
                            "not a valid Unicode scalar value",
                        ));
                    }
                }
            }
            other => {
                // Keep lexer.c compatibility for any other single-char escape if present,
                // while rejecting raw newline escapes cleanly.
                if other == b'\n' {
                    return Err(Diagnostic::error(
                        DiagCode::LexError,
                        "unterminated string escape before newline",
                    )
                    .with_primary(self.span(esc_start, self.pos), "invalid escape"));
                }
                // Consume full UTF-8 char if multibyte.
                let ch_start = self.pos - 1;
                while self.pos < self.bytes.len() && !self.src.is_char_boundary(self.pos) {
                    self.pos += 1;
                }
                out.push_str(&self.src[ch_start..self.pos]);
            }
        }
        Ok(())
    }

    fn lex_string(
        &mut self,
        multiline: bool,
        resuming: bool,
        tok_start: usize,
        tok_line: u32,
    ) -> Result<(), Diagnostic> {
        let content_start = self.pos;
        let mut decoded = String::new();

        while self.pos < self.bytes.len() {
            let b = self.peek(0);
            if multiline {
                if b == b'"' && self.peek(1) == b'"' && self.peek(2) == b'"' {
                    let content_end = self.pos;
                    self.advance_byte();
                    self.advance_byte();
                    self.advance_byte();
                    let raw = self.src[content_start..content_end].to_string();
                    let value = if resuming {
                        decoded
                    } else {
                        dedent_multiline(&decoded)
                    };
                    let kind = if resuming {
                        TokenKind::TextTail {
                            value,
                            multiline,
                            raw,
                        }
                    } else {
                        TokenKind::Text {
                            value,
                            multiline,
                            raw,
                        }
                    };
                    self.emit(kind, tok_start, self.pos, tok_line);
                    return Ok(());
                }
            } else {
                if b == b'"' {
                    let content_end = self.pos;
                    self.advance_byte();
                    let raw = self.src[content_start..content_end].to_string();
                    let kind = if resuming {
                        TokenKind::TextTail {
                            value: decoded,
                            multiline,
                            raw,
                        }
                    } else {
                        TokenKind::Text {
                            value: decoded,
                            multiline,
                            raw,
                        }
                    };
                    self.emit(kind, tok_start, self.pos, tok_line);
                    return Ok(());
                }
                if b == b'\n' {
                    return Err(Diagnostic::error(
                        DiagCode::LexError,
                        "unterminated string literal",
                    )
                    .with_primary(
                        self.span(tok_start, self.pos),
                        "string literal reaches end of line without closing `\"`",
                    ));
                }
            }

            if b == b'\\' {
                let esc_start = self.pos;
                self.advance_byte();
                self.lex_escape(&mut decoded, esc_start)?;
                continue;
            }

            if b == b'#' && self.peek(1) == b'{' {
                let content_end = self.pos;
                self.advance_byte();
                self.advance_byte();
                if self.interp_stack.len() >= 64 {
                    return Err(Diagnostic::error(
                        DiagCode::LexError,
                        "string interpolation nesting too deep",
                    )
                    .with_primary(
                        self.span(content_end, self.pos),
                        "maximum interpolation nesting depth (64) exceeded",
                    ));
                }
                self.interp_stack.push(InterpFrame {
                    saved_paren_depth: self.paren_depth,
                    multiline,
                });
                self.paren_depth += 1;
                let raw = self.src[content_start..content_end].to_string();
                let kind = if resuming {
                    TokenKind::TextMid {
                        value: decoded,
                        multiline,
                        raw,
                    }
                } else {
                    TokenKind::TextHead {
                        value: decoded,
                        multiline,
                        raw,
                    }
                };
                self.emit(kind, tok_start, self.pos, tok_line);
                return Ok(());
            }

            let ch_start = self.pos;
            self.advance_byte();
            while self.pos < self.bytes.len() && !self.src.is_char_boundary(self.pos) {
                self.pos += 1;
            }
            decoded.push_str(&self.src[ch_start..self.pos]);
        }

        Err(
            Diagnostic::error(DiagCode::LexError, "unterminated string literal").with_primary(
                self.span(tok_start, self.pos),
                "reached end of file before closing quote",
            ),
        )
    }

    fn run(&mut self) -> Result<(), Diagnostic> {
        loop {
            let mut saw_space = false;
            let mut saw_nl = false;
            let mut nl_start = self.pos;
            let mut nl_line = self.line;

            while self.pos < self.bytes.len() {
                let b = self.peek(0);
                if matches!(b, b' ' | b'\t' | b'\r') {
                    saw_space = true;
                    self.advance_byte();
                } else if b == b'#' {
                    let c_start = self.pos;
                    let c_line = self.line;
                    let is_inline = self.prev_token_line == c_line && self.prev_token.is_some();
                    while self.pos < self.bytes.len() && self.peek(0) != b'\n' {
                        self.advance_byte();
                    }
                    let c_end = self.pos;
                    let raw = self.src[c_start..c_end].trim_end_matches('\r');
                    let is_doc = raw.starts_with("##") && !raw.starts_with("###");
                    self.comments.push(Comment {
                        span: self.span(c_start, c_end),
                        text: raw.to_string(),
                        is_doc,
                        line: c_line,
                        is_inline,
                    });
                } else if b == b'\n' {
                    if !saw_nl {
                        nl_start = self.pos;
                        nl_line = self.line;
                    }
                    saw_nl = true;
                    saw_space = true;
                    self.advance_byte();
                } else {
                    break;
                }
            }

            let prev_continues = self
                .prev_token
                .as_ref()
                .is_none_or(TokenKind::continues_after);
            if saw_nl && self.paren_depth == 0 && !prev_continues && !self.next_line_continues() {
                self.emit(TokenKind::Newline, nl_start, nl_start + 1, nl_line);
                continue;
            }

            if self.pos >= self.bytes.len() {
                let need_trailing_nl = self.paren_depth == 0
                    && self
                        .prev_token
                        .as_ref()
                        .is_some_and(|t| !matches!(t, TokenKind::Newline));
                if need_trailing_nl {
                    let end = self.pos;
                    let line = self.line;
                    self.emit(TokenKind::Newline, end, end, line);
                }
                let end = self.pos;
                let line = self.line;
                self.emit(TokenKind::Eof, end, end, line);
                return Ok(());
            }

            let start = self.pos;
            let tok_line = self.line;
            let b = self.peek(0);
            let b2 = self.peek(1);

            // Resume string interpolation on matching `}`.
            if b == b'}'
                && let Some(&top) = self.interp_stack.last()
                && self.paren_depth == top.saved_paren_depth + 1
            {
                self.advance_byte();
                self.interp_stack.pop();
                self.paren_depth = top.saved_paren_depth;
                self.lex_string(top.multiline, true, start, tok_line)?;
                continue;
            }

            // Strings (single-line and multiline `"""`).
            if b == b'"' {
                if b2 == b'"' && self.peek(2) == b'"' {
                    self.advance_byte();
                    self.advance_byte();
                    self.advance_byte();
                    self.lex_string(true, false, start, tok_line)?;
                } else {
                    self.advance_byte();
                    self.lex_string(false, false, start, tok_line)?;
                }
                continue;
            }

            // Numbers, ISO Dates (YYYY-MM-DD), and ISO Timestamps (YYYY-MM-DDT...).
            if b.is_ascii_digit() {
                if self.is_4d_2d_2d(self.pos) {
                    for _ in 0..10 {
                        self.advance_byte();
                    }
                    if self.peek(0) == b'T' {
                        self.advance_byte();
                        while self.pos < self.bytes.len() {
                            let tc = self.peek(0);
                            if tc.is_ascii_digit() || matches!(tc, b':' | b'.' | b'Z' | b'+' | b'-')
                            {
                                self.advance_byte();
                            } else {
                                break;
                            }
                        }
                        let lexeme = self.src[start..self.pos].to_string();
                        self.emit(TokenKind::Timestamp(lexeme), start, self.pos, tok_line);
                    } else {
                        let lexeme = self.src[start..self.pos].to_string();
                        self.emit(TokenKind::Date(lexeme), start, self.pos, tok_line);
                    }
                    continue;
                }

                while self.peek(0).is_ascii_digit() || self.peek(0) == b'_' {
                    self.advance_byte();
                }
                let mut is_dec = false;
                if self.peek(0) == b'.' && self.peek(1).is_ascii_digit() {
                    is_dec = true;
                    self.advance_byte();
                    while self.peek(0).is_ascii_digit() || self.peek(0) == b'_' {
                        self.advance_byte();
                    }
                }
                if matches!(self.peek(0), b'e' | b'E')
                    && (self.peek(1).is_ascii_digit()
                        || (matches!(self.peek(1), b'+' | b'-') && self.peek(2).is_ascii_digit()))
                {
                    is_dec = true;
                    self.advance_byte();
                    if matches!(self.peek(0), b'+' | b'-') {
                        self.advance_byte();
                    }
                    while self.peek(0).is_ascii_digit() {
                        self.advance_byte();
                    }
                }
                let lexeme = self.src[start..self.pos].to_string();
                let kind = if is_dec {
                    TokenKind::Decimal(lexeme)
                } else {
                    TokenKind::Int(lexeme)
                };
                self.emit(kind, start, self.pos, tok_line);
                continue;
            }

            // Contextual atoms (`:month`, `:pearson`, `:active`) vs `:`.
            if b == b':'
                && b2.is_ascii_lowercase()
                && (saw_space
                    || self
                        .prev_token
                        .as_ref()
                        .is_none_or(TokenKind::allows_adjacent_atom))
            {
                self.advance_byte(); // ':'
                let name_start = self.pos;
                while is_ident_cont(self.peek(0)) {
                    self.advance_byte();
                }
                let atom = self.src[name_start..self.pos].to_string();
                self.emit(TokenKind::Atom(atom), start, self.pos, tok_line);
                continue;
            }

            // Identifiers, CapNames, Keywords, and `_`.
            if is_ident_start(b) {
                while is_ident_cont(self.peek(0)) {
                    self.advance_byte();
                }
                let base_end = self.pos;
                if base_end - start == 1 && b == b'_' {
                    self.emit(TokenKind::Underscore, start, self.pos, tok_line);
                    continue;
                }
                let mut has_suffix = false;
                if b.is_ascii_lowercase() {
                    let suf = self.peek(0);
                    if (suf == b'?' && self.peek(1) != b'?')
                        || (suf == b'!' && self.peek(1) != b'=')
                    {
                        self.advance_byte();
                        has_suffix = true;
                    }
                }
                let text = &self.src[start..self.pos];
                if !has_suffix && let Some(kw) = lookup_keyword(text) {
                    self.emit(kw, start, self.pos, tok_line);
                    continue;
                }
                let kind = if b.is_ascii_uppercase() {
                    TokenKind::CapName(text.to_string())
                } else {
                    TokenKind::Name(text.to_string())
                };
                self.emit(kind, start, self.pos, tok_line);
                continue;
            }

            // Two-character operators.
            let two = match (b, b2) {
                (b'|', b'>') => Some(TokenKind::Pipe),
                (b'?', b'?') => Some(TokenKind::QQ),
                (b'.', b'.') => Some(TokenKind::DotDot),
                (b'=', b'=') => Some(TokenKind::Eq),
                (b'!', b'=') => Some(TokenKind::Ne),
                (b'<', b'=') => Some(TokenKind::Le),
                (b'>', b'=') => Some(TokenKind::Ge),
                _ => None,
            };
            if let Some(kind) = two {
                self.advance_byte();
                self.advance_byte();
                self.emit(kind, start, self.pos, tok_line);
                continue;
            }

            // Single-character delimiters & operators.
            self.advance_byte();
            let one = match b {
                b'(' => {
                    self.paren_depth += 1;
                    TokenKind::LParen
                }
                b')' => {
                    self.paren_depth = self.paren_depth.saturating_sub(1);
                    TokenKind::RParen
                }
                b'[' => {
                    self.paren_depth += 1;
                    TokenKind::LBrack
                }
                b']' => {
                    self.paren_depth = self.paren_depth.saturating_sub(1);
                    TokenKind::RBrack
                }
                b'{' => {
                    self.paren_depth += 1;
                    TokenKind::LBrace
                }
                b'}' => {
                    self.paren_depth = self.paren_depth.saturating_sub(1);
                    TokenKind::RBrace
                }
                b',' => TokenKind::Comma,
                b':' => TokenKind::Colon,
                b'.' => TokenKind::Dot,
                b'|' => TokenKind::Bar,
                b'?' => TokenKind::QMark,
                b'=' => TokenKind::Assign,
                b'<' => TokenKind::Lt,
                b'>' => TokenKind::Gt,
                b'+' => TokenKind::Plus,
                b'-' => TokenKind::Minus,
                b'*' => TokenKind::Star,
                b'/' => TokenKind::Slash,
                b'%' => TokenKind::Percent,
                _ => {
                    // Consume full UTF-8 char for span accuracy.
                    while self.pos < self.bytes.len() && !self.src.is_char_boundary(self.pos) {
                        self.pos += 1;
                    }
                    let ch_text = &self.src[start..self.pos];
                    return Err(Diagnostic::error(
                        DiagCode::LexError,
                        format!("unexpected character `{ch_text}`"),
                    )
                    .with_primary(self.span(start, self.pos), "unrecognized token"));
                }
            };
            self.emit(one, start, self.pos, tok_line);
        }
    }
}
