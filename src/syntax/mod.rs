//! Dana surface syntax: UTF-8 lexer, recursive-descent parser (100% parity with
//! `grammar/dana.y`), lossless Surface AST, and canonical 2-space formatter.

pub mod ast;
pub mod fmt;
pub mod lexer;
pub mod parser;
pub mod token;

pub use ast::*;
pub use fmt::format_module;
pub use lexer::{LexOutput, lex, lex_bytes};
pub use parser::{parse_fragment, parse_fragment_bytes, parse_module, parse_module_bytes};
pub use token::{Comment, Token, TokenKind};
