//! Surface token definitions mirroring `grammar/dana.y` terminals 1-to-1,
//! plus side-channel comment metadata for lossless formatting.

use crate::base::Span;

/// A `#` line comment or `##` documentation comment captured during lexing.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Comment {
    pub span: Span,
    /// Full comment text including the leading `#` or `##`, without trailing newline.
    pub text: String,
    pub is_doc: bool,
    /// 1-based line number of the comment.
    pub line: u32,
    /// True if a non-whitespace token appeared earlier on the same line.
    pub is_inline: bool,
}

/// Token kinds mirroring every terminal in `grammar/dana.y`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TokenKind {
    Newline,
    Eof,

    // Identifiers and atoms
    Name(String),
    CapName(String),
    Underscore,
    Atom(String),

    // Literals
    Int(String),
    /// Decimal or scientific-notation float lexeme (exact raw text preserved).
    Decimal(String),
    Date(String),
    Timestamp(String),
    /// Complete string literal (decoded content, raw multiline flag).
    Text {
        value: String,
        multiline: bool,
        raw: String,
    },
    /// Opening text segment before `#{` in an interpolated string.
    TextHead {
        value: String,
        multiline: bool,
        raw: String,
    },
    /// Middle text segment between `}` and `#{`.
    TextMid {
        value: String,
        multiline: bool,
        raw: String,
    },
    /// Closing text segment after `}` in an interpolated string.
    TextTail {
        value: String,
        multiline: bool,
        raw: String,
    },

    // Keywords (exact set from grammar/lexer.c)
    KwModule,
    KwExpose,
    KwUse,
    KwTag,
    KwSchema,
    KwStruct,
    KwEnum,
    KwConst,
    KwFn,
    KwVar,
    KwIf,
    KwElse,
    KwCase,
    KwFor,
    KwIn,
    KwWhile,
    KwBreak,
    KwContinue,
    KwReturn,
    KwTry,
    KwAnd,
    KwOr,
    KwNot,
    KwIs,
    KwTrue,
    KwFalse,
    KwNone,
    KwStop,
    KwPromise,
    KwExamples,
    KwTest,
    KwAssert,
    KwTable,
    KwWhere,
    KwEnd,

    // Delimiters and punctuation
    LParen,
    RParen,
    LBrack,
    RBrack,
    LBrace,
    RBrace,
    Comma,
    Colon,
    Dot,
    DotDot,
    Bar,
    Pipe,
    QMark,
    QQ,
    Assign,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    Plus,
    Minus,
    Star,
    Slash,
    Percent,
}

impl TokenKind {
    /// Human-readable description for syntax error messages.
    #[must_use]
    pub const fn describe(&self) -> &'static str {
        match self {
            Self::Newline => "end of line",
            Self::Eof => "end of file",
            Self::Name(_) => "name",
            Self::CapName(_) => "capitalized name",
            Self::Underscore => "`_`",
            Self::Atom(_) => "atom",
            Self::Int(_) => "integer literal",
            Self::Decimal(_) => "decimal literal",
            Self::Date(_) => "date literal",
            Self::Timestamp(_) => "timestamp literal",
            Self::Text { .. } => "string literal",
            Self::TextHead { .. } => "interpolated string",
            Self::TextMid { .. } => "string interpolation continuation",
            Self::TextTail { .. } => "end of interpolated string",
            Self::KwModule => "`module`",
            Self::KwExpose => "`expose`",
            Self::KwUse => "`use`",
            Self::KwTag => "`tag`",
            Self::KwSchema => "`schema`",
            Self::KwStruct => "`struct`",
            Self::KwEnum => "`enum`",
            Self::KwConst => "`const`",
            Self::KwFn => "`fn`",
            Self::KwVar => "`var`",
            Self::KwIf => "`if`",
            Self::KwElse => "`else`",
            Self::KwCase => "`case`",
            Self::KwFor => "`for`",
            Self::KwIn => "`in`",
            Self::KwWhile => "`while`",
            Self::KwBreak => "`break`",
            Self::KwContinue => "`continue`",
            Self::KwReturn => "`return`",
            Self::KwTry => "`try`",
            Self::KwAnd => "`and`",
            Self::KwOr => "`or`",
            Self::KwNot => "`not`",
            Self::KwIs => "`is`",
            Self::KwTrue => "`true`",
            Self::KwFalse => "`false`",
            Self::KwNone => "`none`",
            Self::KwStop => "`stop`",
            Self::KwPromise => "`promise`",
            Self::KwExamples => "`examples`",
            Self::KwTest => "`test`",
            Self::KwAssert => "`assert`",
            Self::KwTable => "`table`",
            Self::KwWhere => "`where`",
            Self::KwEnd => "`end`",
            Self::LParen => "`(`",
            Self::RParen => "`)`",
            Self::LBrack => "`[`",
            Self::RBrack => "`]`",
            Self::LBrace => "`{`",
            Self::RBrace => "`}`",
            Self::Comma => "`,`",
            Self::Colon => "`:`",
            Self::Dot => "`.`",
            Self::DotDot => "`..`",
            Self::Bar => "`|`",
            Self::Pipe => "`|>`",
            Self::QMark => "`?`",
            Self::QQ => "`??`",
            Self::Assign => "`=`",
            Self::Eq => "`==`",
            Self::Ne => "`!=`",
            Self::Lt => "`<`",
            Self::Le => "`<=`",
            Self::Gt => "`>`",
            Self::Ge => "`>=`",
            Self::Plus => "`+`",
            Self::Minus => "`-`",
            Self::Star => "`*`",
            Self::Slash => "`/`",
            Self::Percent => "`%`",
        }
    }

    /// True if a newline immediately following this token is suppressed (mirrors `lexer.c`).
    #[must_use]
    pub const fn continues_after(&self) -> bool {
        matches!(
            self,
            Self::Newline
                | Self::LParen
                | Self::LBrack
                | Self::LBrace
                | Self::Comma
                | Self::Dot
                | Self::Assign
                | Self::Pipe
                | Self::KwAnd
                | Self::KwOr
                | Self::KwNot
                | Self::KwIs
                | Self::QQ
                | Self::Eq
                | Self::Ne
                | Self::Lt
                | Self::Le
                | Self::Gt
                | Self::Ge
                | Self::Plus
                | Self::Minus
                | Self::Star
                | Self::Slash
                | Self::Percent
        )
    }

    /// True if this token can immediately precede a contextual `:atom` without whitespace.
    #[must_use]
    pub const fn allows_adjacent_atom(&self) -> bool {
        matches!(
            self,
            Self::Newline
                | Self::LParen
                | Self::LBrack
                | Self::LBrace
                | Self::Comma
                | Self::Colon
                | Self::Assign
                | Self::Pipe
                | Self::Bar
        )
    }
}

/// A single lexed token with its byte span.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Token {
    pub kind: TokenKind,
    pub span: Span,
}
