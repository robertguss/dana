//! Recursive-descent parser for Dana Language Reference v0.1 with 100% parity
//! against `grammar/dana.y` (0-conflict Bison IELR(1) grammar).
//!
//! Uses explicit stratified precedence functions and bounded nesting depth (1,024)
//! so adversarial deep inputs return a clean syntax diagnostic rather than overflowing the stack.

use crate::base::{DiagCode, Diagnostic, FileId, Span};
use crate::syntax::ast::*;
use crate::syntax::lexer::{LexOutput, lex, lex_bytes};
use crate::syntax::token::{Token, TokenKind};

const MAX_NESTING_DEPTH: usize = 128;

/// Parse a full Dana module file (`module Name ...`) from UTF-8 source text.
///
/// # Errors
/// Returns a [`Diagnostic`] on lexing or syntax errors.
pub fn parse_module(file: FileId, src: &str) -> Result<Module, Diagnostic> {
    let lexed = lex(file, src)?;
    parse_module_tokens(file, lexed)
}

/// Parse a full Dana module file from raw bytes (validating UTF-8 first).
///
/// # Errors
/// Returns a [`Diagnostic`] on invalid UTF-8, lexing, or syntax errors.
pub fn parse_module_bytes(file: FileId, bytes: &[u8]) -> Result<Module, Diagnostic> {
    let lexed = lex_bytes(file, bytes)?;
    parse_module_tokens(file, lexed)
}

/// Parse a Dana fragment (optional module header + declarations/statements),
/// matching `grammar/dana.y`'s `START_FRAGMENT` rule.
///
/// # Errors
/// Returns a [`Diagnostic`] on lexing or syntax errors.
pub fn parse_fragment(file: FileId, src: &str) -> Result<Fragment, Diagnostic> {
    let lexed = lex(file, src)?;
    parse_fragment_tokens(file, lexed)
}

/// Parse a Dana fragment from raw bytes (validating UTF-8 first).
///
/// # Errors
/// Returns a [`Diagnostic`] on invalid UTF-8, lexing, or syntax errors.
pub fn parse_fragment_bytes(file: FileId, bytes: &[u8]) -> Result<Fragment, Diagnostic> {
    let lexed = lex_bytes(file, bytes)?;
    parse_fragment_tokens(file, lexed)
}

fn parse_module_tokens(file: FileId, lexed: LexOutput) -> Result<Module, Diagnostic> {
    let mut p = Parser::new(file, lexed.tokens);
    p.skip_newlines();
    let header = p.parse_module_header()?;
    let mut items = Vec::new();
    while !p.at_eof() {
        items.push(p.parse_top_item()?);
    }
    let end = items.last().map_or(header.span, TopItem::span);
    let span = header.span.merge(end);
    Ok(Module {
        header,
        items,
        comments: lexed.comments,
        blank_lines: lexed.blank_lines,
        span,
    })
}

fn parse_fragment_tokens(file: FileId, lexed: LexOutput) -> Result<Fragment, Diagnostic> {
    let mut p = Parser::new(file, lexed.tokens);
    p.skip_newlines();
    let start_span = p.current_span();
    let header = if matches!(p.peek_kind(), TokenKind::KwModule) {
        Some(p.parse_module_header()?)
    } else {
        None
    };
    let mut items = Vec::new();
    while !p.at_eof() {
        items.push(p.parse_fragment_item()?);
    }
    let end_span = p.current_span();
    Ok(Fragment {
        header,
        items,
        comments: lexed.comments,
        span: start_span.merge(end_span),
    })
}

struct Parser {
    file: FileId,
    tokens: Vec<Token>,
    pos: usize,
    depth: usize,
}

impl Parser {
    const fn new(file: FileId, tokens: Vec<Token>) -> Self {
        Self {
            file,
            tokens,
            pos: 0,
            depth: 0,
        }
    }

    fn enter_nested(&mut self) -> Result<(), Diagnostic> {
        self.depth += 1;
        if self.depth > MAX_NESTING_DEPTH {
            return Err(Diagnostic::error(
                DiagCode::ParseError,
                format!("maximum syntax nesting depth ({MAX_NESTING_DEPTH}) exceeded"),
            )
            .with_span(self.current_span()));
        }
        Ok(())
    }

    fn leave_nested(&mut self) {
        self.depth = self.depth.saturating_sub(1);
    }

    fn peek(&self) -> &Token {
        self.tokens
            .get(self.pos)
            .or_else(|| self.tokens.last())
            .unwrap_or(&EOF_FALLBACK)
    }

    fn peek_at(&self, offset: usize) -> &Token {
        self.tokens
            .get(self.pos + offset)
            .or_else(|| self.tokens.last())
            .unwrap_or(&EOF_FALLBACK)
    }

    fn peek_kind(&self) -> &TokenKind {
        &self.peek().kind
    }

    fn current_span(&self) -> Span {
        let s = self.peek().span;
        if s.file == FileId(0) && s.start == 0 && s.end == 0 {
            Span::point(self.file, 0)
        } else {
            s
        }
    }

    fn at_eof(&self) -> bool {
        matches!(self.peek_kind(), TokenKind::Eof)
    }

    fn advance(&mut self) -> Token {
        if self.pos < self.tokens.len() {
            let tok = self.tokens[self.pos].clone();
            if !matches!(tok.kind, TokenKind::Eof) {
                self.pos += 1;
            }
            tok
        } else {
            Token {
                kind: TokenKind::Eof,
                span: Span::point(self.file, 0),
            }
        }
    }

    fn skip_newlines(&mut self) {
        while matches!(self.peek_kind(), TokenKind::Newline) {
            self.advance();
        }
    }

    fn expect_nl(&mut self) -> Result<Span, Diagnostic> {
        if matches!(self.peek_kind(), TokenKind::Newline) {
            let sp = self.advance().span;
            self.skip_newlines();
            Ok(sp)
        } else {
            Err(self.unexpected("end of line"))
        }
    }

    fn expect(&mut self, expected: &TokenKind) -> Result<Span, Diagnostic> {
        if self.peek_kind() == expected {
            Ok(self.advance().span)
        } else {
            Err(self.unexpected(expected.describe()))
        }
    }

    fn unexpected(&self, expected: &str) -> Diagnostic {
        let tok = self.peek();
        Diagnostic::error(
            DiagCode::ParseError,
            format!("expected {expected}, found {}", tok.kind.describe()),
        )
        .with_primary(tok.span, format!("unexpected {}", tok.kind.describe()))
    }

    // -----------------------------------------------------------------------
    // Identifiers
    // -----------------------------------------------------------------------

    fn is_ident_kind(k: &TokenKind) -> bool {
        matches!(
            k,
            TokenKind::Name(_) | TokenKind::KwWhere | TokenKind::KwTag
        )
    }

    fn is_member_name_kind(k: &TokenKind) -> bool {
        matches!(
            k,
            TokenKind::Name(_)
                | TokenKind::CapName(_)
                | TokenKind::KwWhere
                | TokenKind::KwTag
                | TokenKind::KwTable
        )
    }

    fn parse_ident(&mut self) -> Result<SpannedName, Diagnostic> {
        let tok = self.peek().clone();
        match tok.kind {
            TokenKind::Name(s) => {
                self.advance();
                Ok(SpannedName::new(s, tok.span))
            }
            TokenKind::KwWhere => {
                self.advance();
                Ok(SpannedName::new("where", tok.span))
            }
            TokenKind::KwTag => {
                self.advance();
                Ok(SpannedName::new("tag", tok.span))
            }
            _ => Err(self.unexpected("identifier")),
        }
    }

    fn parse_cap_name(&mut self) -> Result<SpannedName, Diagnostic> {
        let tok = self.peek().clone();
        match tok.kind {
            TokenKind::CapName(s) => {
                self.advance();
                Ok(SpannedName::new(s, tok.span))
            }
            _ => Err(self.unexpected("capitalized name")),
        }
    }

    fn parse_member_name(&mut self) -> Result<SpannedName, Diagnostic> {
        let tok = self.peek().clone();
        match tok.kind {
            TokenKind::Name(s) | TokenKind::CapName(s) => {
                self.advance();
                Ok(SpannedName::new(s, tok.span))
            }
            TokenKind::KwWhere => {
                self.advance();
                Ok(SpannedName::new("where", tok.span))
            }
            TokenKind::KwTag => {
                self.advance();
                Ok(SpannedName::new("tag", tok.span))
            }
            TokenKind::KwTable => {
                self.advance();
                Ok(SpannedName::new("table", tok.span))
            }
            _ => Err(self.unexpected("member name")),
        }
    }

    // -----------------------------------------------------------------------
    // Module Header
    // -----------------------------------------------------------------------

    fn parse_module_header(&mut self) -> Result<ModuleHeader, Diagnostic> {
        let start = self.expect(&TokenKind::KwModule)?;
        let path = self.parse_module_path()?;
        let mut end = self.expect_nl()?;

        let expose = if matches!(self.peek_kind(), TokenKind::KwExpose) {
            let ex = self.parse_expose()?;
            end = ex.span;
            Some(ex)
        } else {
            None
        };

        let mut uses = Vec::new();
        while matches!(self.peek_kind(), TokenKind::KwUse) {
            let u = self.parse_use()?;
            end = u.span;
            uses.push(u);
        }

        Ok(ModuleHeader {
            path,
            expose,
            uses,
            span: start.merge(end),
        })
    }

    fn parse_module_path(&mut self) -> Result<Vec<SpannedName>, Diagnostic> {
        let mut path = vec![self.parse_cap_name()?];
        while matches!(self.peek_kind(), TokenKind::Dot) {
            self.advance();
            path.push(self.parse_cap_name()?);
        }
        Ok(path)
    }

    fn parse_expose(&mut self) -> Result<ExposeDecl, Diagnostic> {
        let start = self.expect(&TokenKind::KwExpose)?;
        let mut items = vec![self.parse_expose_item()?];
        while matches!(self.peek_kind(), TokenKind::Comma) {
            self.advance();
            items.push(self.parse_expose_item()?);
        }
        let end = self.expect_nl()?;
        Ok(ExposeDecl {
            items,
            span: start.merge(end),
        })
    }

    fn parse_expose_item(&mut self) -> Result<ExposeItem, Diagnostic> {
        if matches!(self.peek_kind(), TokenKind::CapName(_)) {
            let name = self.parse_cap_name()?;
            if matches!(self.peek_kind(), TokenKind::LParen) {
                self.advance();
                self.expect(&TokenKind::DotDot)?;
                self.expect(&TokenKind::RParen)?;
                Ok(ExposeItem::TypeAll(name))
            } else {
                Ok(ExposeItem::Type(name))
            }
        } else {
            Ok(ExposeItem::Value(self.parse_ident()?))
        }
    }

    fn parse_use(&mut self) -> Result<UseDecl, Diagnostic> {
        let start = self.expect(&TokenKind::KwUse)?;
        let path = self.parse_module_path()?;
        let items = if matches!(self.peek_kind(), TokenKind::LBrace) {
            self.advance();
            let mut list = vec![self.parse_use_item()?];
            while matches!(self.peek_kind(), TokenKind::Comma) {
                self.advance();
                list.push(self.parse_use_item()?);
            }
            self.expect(&TokenKind::RBrace)?;
            Some(list)
        } else {
            None
        };
        let end = self.expect_nl()?;
        Ok(UseDecl {
            path,
            items,
            span: start.merge(end),
        })
    }

    fn parse_use_item(&mut self) -> Result<SpannedName, Diagnostic> {
        if matches!(self.peek_kind(), TokenKind::CapName(_)) {
            self.parse_cap_name()
        } else {
            self.parse_ident()
        }
    }

    // -----------------------------------------------------------------------
    // Top-level and Fragment Items
    // -----------------------------------------------------------------------

    fn parse_top_item(&mut self) -> Result<TopItem, Diagnostic> {
        match self.peek_kind() {
            TokenKind::KwTag => Ok(TopItem::Tag(self.parse_tag_decl()?)),
            TokenKind::KwSchema => Ok(TopItem::Schema(self.parse_schema_decl()?)),
            TokenKind::KwStruct => Ok(TopItem::Struct(self.parse_struct_decl()?)),
            TokenKind::KwEnum => Ok(TopItem::Enum(self.parse_enum_decl()?)),
            TokenKind::KwConst => Ok(TopItem::Const(self.parse_const_decl()?)),
            TokenKind::KwFn => Ok(TopItem::Fn(self.parse_fn_decl()?)),
            TokenKind::KwTest => Ok(TopItem::Test(self.parse_test_decl()?)),
            _ => Err(self.unexpected("top-level declaration")),
        }
    }

    fn parse_fragment_item(&mut self) -> Result<FragmentItem, Diagnostic> {
        match self.peek_kind() {
            TokenKind::KwTag if Self::is_ident_kind(&self.peek_at(1).kind) => {
                Ok(FragmentItem::Top(TopItem::Tag(self.parse_tag_decl()?)))
            }
            TokenKind::KwSchema => Ok(FragmentItem::Top(TopItem::Schema(
                self.parse_schema_decl()?,
            ))),
            TokenKind::KwStruct => Ok(FragmentItem::Top(TopItem::Struct(
                self.parse_struct_decl()?,
            ))),
            TokenKind::KwEnum => Ok(FragmentItem::Top(TopItem::Enum(self.parse_enum_decl()?))),
            TokenKind::KwConst => Ok(FragmentItem::Top(TopItem::Const(self.parse_const_decl()?))),
            TokenKind::KwFn if Self::is_ident_kind(&self.peek_at(1).kind) => {
                Ok(FragmentItem::Top(TopItem::Fn(self.parse_fn_decl()?)))
            }
            TokenKind::KwTest => Ok(FragmentItem::Top(TopItem::Test(self.parse_test_decl()?))),
            _ => Ok(FragmentItem::Stmt(self.parse_stmt()?)),
        }
    }

    // -----------------------------------------------------------------------
    // Declarations
    // -----------------------------------------------------------------------

    fn parse_tag_decl(&mut self) -> Result<TagDecl, Diagnostic> {
        let start = self.expect(&TokenKind::KwTag)?;
        let name = self.parse_ident()?;
        let end = self.expect_nl()?;
        Ok(TagDecl {
            name,
            span: start.merge(end),
        })
    }

    fn parse_opt_tags(&mut self) -> Result<Vec<SpannedName>, Diagnostic> {
        if !matches!(self.peek_kind(), TokenKind::LBrack) {
            return Ok(Vec::new());
        }
        self.advance();
        let tags = self.parse_tag_list()?;
        self.expect(&TokenKind::RBrack)?;
        Ok(tags)
    }

    fn parse_tag_list(&mut self) -> Result<Vec<SpannedName>, Diagnostic> {
        let mut tags = Vec::new();
        if !matches!(self.peek_kind(), TokenKind::RBrack) {
            tags.push(self.parse_ident()?);
            while matches!(self.peek_kind(), TokenKind::Comma) {
                self.advance();
                tags.push(self.parse_ident()?);
            }
        }
        Ok(tags)
    }

    fn parse_schema_decl(&mut self) -> Result<SchemaDecl, Diagnostic> {
        let start = self.expect(&TokenKind::KwSchema)?;
        let name = self.parse_cap_name()?;
        let tags = self.parse_opt_tags()?;
        self.expect_nl()?;
        let mut fields = Vec::new();
        while !matches!(self.peek_kind(), TokenKind::KwEnd | TokenKind::Eof) {
            fields.push(self.parse_schema_field()?);
        }
        let end_kw = self.expect(&TokenKind::KwEnd)?;
        self.expect_nl()?;
        Ok(SchemaDecl {
            name,
            tags,
            fields,
            span: start.merge(end_kw),
        })
    }

    fn parse_schema_field(&mut self) -> Result<SchemaField, Diagnostic> {
        let name = self.parse_ident()?;
        self.expect(&TokenKind::Colon)?;
        let ty = self.parse_type_expr()?;
        let tags = self.parse_opt_tags()?;
        let constraint = if matches!(self.peek_kind(), TokenKind::KwWhere) {
            self.advance();
            Some(self.parse_expr()?)
        } else {
            None
        };
        let end = self.expect_nl()?;
        Ok(SchemaField {
            span: name.span.merge(end),
            name,
            ty,
            tags,
            constraint,
        })
    }

    fn parse_struct_decl(&mut self) -> Result<StructDecl, Diagnostic> {
        let start = self.expect(&TokenKind::KwStruct)?;
        let name = self.parse_cap_name()?;
        self.expect_nl()?;
        let mut fields = Vec::new();
        while !matches!(self.peek_kind(), TokenKind::KwEnd | TokenKind::Eof) {
            let fname = self.parse_ident()?;
            self.expect(&TokenKind::Colon)?;
            let ty = self.parse_type_expr()?;
            let tags = self.parse_opt_tags()?;
            let fend = self.expect_nl()?;
            fields.push(StructField {
                span: fname.span.merge(fend),
                name: fname,
                ty,
                tags,
            });
        }
        let end_kw = self.expect(&TokenKind::KwEnd)?;
        self.expect_nl()?;
        Ok(StructDecl {
            name,
            fields,
            span: start.merge(end_kw),
        })
    }

    fn parse_enum_decl(&mut self) -> Result<EnumDecl, Diagnostic> {
        let start = self.expect(&TokenKind::KwEnum)?;
        let name = self.parse_cap_name()?;
        self.expect_nl()?;
        let mut variants = Vec::new();
        while !matches!(self.peek_kind(), TokenKind::KwEnd | TokenKind::Eof) {
            let vname = self.parse_cap_name()?;
            let mut fields = Vec::new();
            if matches!(self.peek_kind(), TokenKind::LParen) {
                self.advance();
                fields.push(self.parse_variant_field()?);
                while matches!(self.peek_kind(), TokenKind::Comma) {
                    self.advance();
                    fields.push(self.parse_variant_field()?);
                }
                self.expect(&TokenKind::RParen)?;
            }
            let vend = self.expect_nl()?;
            variants.push(EnumVariant {
                span: vname.span.merge(vend),
                name: vname,
                fields,
            });
        }
        let end_kw = self.expect(&TokenKind::KwEnd)?;
        self.expect_nl()?;
        Ok(EnumDecl {
            name,
            variants,
            span: start.merge(end_kw),
        })
    }

    fn parse_variant_field(&mut self) -> Result<VariantField, Diagnostic> {
        if Self::is_ident_kind(self.peek_kind()) && matches!(self.peek_at(1).kind, TokenKind::Colon)
        {
            let name = self.parse_ident()?;
            self.advance(); // ':'
            let ty = self.parse_type_expr()?;
            let tags = self.parse_opt_tags()?;
            let span = name.span.merge(ty.span);
            Ok(VariantField::Named {
                name,
                ty,
                tags,
                span,
            })
        } else {
            let ty = self.parse_type_expr()?;
            let span = ty.span;
            Ok(VariantField::Positional { ty, span })
        }
    }

    fn parse_const_decl(&mut self) -> Result<ConstDecl, Diagnostic> {
        let start = self.expect(&TokenKind::KwConst)?;
        let name = self.parse_ident()?;
        let ty = if matches!(self.peek_kind(), TokenKind::Colon) {
            self.advance();
            Some(self.parse_type_expr()?)
        } else {
            None
        };
        self.expect(&TokenKind::Assign)?;
        let value = self.parse_expr()?;
        let end = self.expect_nl()?;
        Ok(ConstDecl {
            name,
            ty,
            value,
            span: start.merge(end),
        })
    }

    fn parse_fn_decl(&mut self) -> Result<FnDecl, Diagnostic> {
        let start = self.expect(&TokenKind::KwFn)?;
        let name = self.parse_ident()?;
        self.expect(&TokenKind::LParen)?;
        let mut params = Vec::new();
        if !matches!(self.peek_kind(), TokenKind::RParen) {
            params.push(self.parse_param()?);
            while matches!(self.peek_kind(), TokenKind::Comma) {
                self.advance();
                params.push(self.parse_param()?);
            }
        }
        self.expect(&TokenKind::RParen)?;
        let ret_ty = if matches!(self.peek_kind(), TokenKind::Colon) {
            let cspan = self.advance().span;
            let ty = self.parse_type_expr()?;
            let tags = self.parse_opt_tags()?;
            let end_sp = tags.last().map_or(ty.span, |t| t.span);
            Some(ReturnType {
                ty,
                tags,
                span: cspan.merge(end_sp),
            })
        } else {
            None
        };
        self.expect_nl()?;
        let mut body = Vec::new();
        while !matches!(self.peek_kind(), TokenKind::KwEnd | TokenKind::Eof) {
            body.push(self.parse_fn_stmt()?);
        }
        let end_kw = self.expect(&TokenKind::KwEnd)?;
        self.expect_nl()?;
        Ok(FnDecl {
            name,
            params,
            ret_ty,
            body,
            span: start.merge(end_kw),
        })
    }

    fn parse_param(&mut self) -> Result<Param, Diagnostic> {
        let name = self.parse_ident()?;
        self.expect(&TokenKind::Colon)?;
        let ty = self.parse_type_expr()?;
        let tags = self.parse_opt_tags()?;
        let end_sp = tags.last().map_or(ty.span, |t| t.span);
        Ok(Param {
            span: name.span.merge(end_sp),
            name,
            ty,
            tags,
        })
    }

    fn parse_fn_stmt(&mut self) -> Result<FnStmt, Diagnostic> {
        match self.peek_kind() {
            TokenKind::KwExamples => {
                let start = self.advance().span;
                self.expect_nl()?;
                let stmts = self.parse_stmts_until(&[TokenKind::KwEnd])?;
                let end_kw = self.expect(&TokenKind::KwEnd)?;
                self.expect_nl()?;
                Ok(FnStmt::Examples {
                    stmts,
                    span: start.merge(end_kw),
                })
            }
            TokenKind::KwPromise => {
                let start = self.advance().span;
                let expr = self.parse_expr()?;
                let end = self.expect_nl()?;
                Ok(FnStmt::Promise {
                    expr,
                    span: start.merge(end),
                })
            }
            _ => Ok(FnStmt::Stmt(self.parse_stmt()?)),
        }
    }

    fn parse_test_decl(&mut self) -> Result<TestDecl, Diagnostic> {
        let start = self.expect(&TokenKind::KwTest)?;
        let tok = self.peek().clone();
        let (name, name_raw) = match tok.kind {
            TokenKind::Text { value, raw, .. } => {
                self.advance();
                (value, raw)
            }
            _ => return Err(self.unexpected("test name string literal")),
        };
        self.expect_nl()?;
        let body = self.parse_stmts_until(&[TokenKind::KwEnd])?;
        let end_kw = self.expect(&TokenKind::KwEnd)?;
        self.expect_nl()?;
        Ok(TestDecl {
            name,
            name_raw,
            body,
            span: start.merge(end_kw),
        })
    }

    // -----------------------------------------------------------------------
    // Types
    // -----------------------------------------------------------------------

    fn parse_type_expr(&mut self) -> Result<TypeExpr, Diagnostic> {
        self.enter_nested()?;
        let res = self.parse_type_expr_inner();
        self.leave_nested();
        res
    }

    fn parse_type_expr_inner(&mut self) -> Result<TypeExpr, Diagnostic> {
        let (kind, mut span) = match self.peek_kind() {
            TokenKind::CapName(_) => {
                let name = self.parse_cap_name()?;
                let mut sp = name.span;
                let args = if matches!(self.peek_kind(), TokenKind::LParen) {
                    self.advance();
                    let mut list = vec![self.parse_type_arg()?];
                    while matches!(self.peek_kind(), TokenKind::Comma) {
                        self.advance();
                        list.push(self.parse_type_arg()?);
                    }
                    let rp = self.expect(&TokenKind::RParen)?;
                    sp = sp.merge(rp);
                    list
                } else {
                    Vec::new()
                };
                (TypeKind::Named { name, args }, sp)
            }
            TokenKind::LParen => {
                let lp = self.advance().span;
                let first = self.parse_type_expr()?;
                self.expect(&TokenKind::Comma)?;
                let mut elems = vec![first, self.parse_type_expr()?];
                while matches!(self.peek_kind(), TokenKind::Comma) {
                    self.advance();
                    elems.push(self.parse_type_expr()?);
                }
                let rp = self.expect(&TokenKind::RParen)?;
                (TypeKind::Tuple(elems), lp.merge(rp))
            }
            _ => return Err(self.unexpected("type expression")),
        };

        let optional = if matches!(self.peek_kind(), TokenKind::QMark) {
            let q = self.advance().span;
            span = span.merge(q);
            true
        } else {
            false
        };

        Ok(TypeExpr {
            kind,
            optional,
            span,
        })
    }

    fn parse_type_arg(&mut self) -> Result<TypeArg, Diagnostic> {
        if let TokenKind::Text { value, raw, .. } = self.peek_kind().clone() {
            let span = self.advance().span;
            return Ok(TypeArg::Text { value, raw, span });
        }
        if Self::is_ident_kind(self.peek_kind()) && matches!(self.peek_at(1).kind, TokenKind::Colon)
        {
            let name = self.parse_ident()?;
            self.advance(); // ':'
            if matches!(self.peek_kind(), TokenKind::LBrack) {
                self.advance();
                let tags = self.parse_tag_list()?;
                let rb = self.expect(&TokenKind::RBrack)?;
                return Ok(TypeArg::NamedTags {
                    span: name.span.merge(rb),
                    name,
                    tags,
                });
            }
            let ty = self.parse_type_expr()?;
            let tags = self.parse_opt_tags()?;
            let end_sp = tags.last().map_or(ty.span, |t| t.span);
            return Ok(TypeArg::NamedType {
                span: name.span.merge(end_sp),
                name,
                ty,
                tags,
            });
        }
        Ok(TypeArg::Type(self.parse_type_expr()?))
    }

    // -----------------------------------------------------------------------
    // Statements
    // -----------------------------------------------------------------------

    fn parse_stmts_until(&mut self, terminators: &[TokenKind]) -> Result<Vec<Stmt>, Diagnostic> {
        let mut stmts = Vec::new();
        while !self.at_eof() && !terminators.contains(self.peek_kind()) {
            stmts.push(self.parse_stmt()?);
        }
        Ok(stmts)
    }

    fn parse_stmt(&mut self) -> Result<Stmt, Diagnostic> {
        self.enter_nested()?;
        let res = self.parse_stmt_inner();
        self.leave_nested();
        res
    }

    fn parse_stmt_inner(&mut self) -> Result<Stmt, Diagnostic> {
        match self.peek_kind() {
            TokenKind::KwVar => {
                let start = self.advance().span;
                let name = self.parse_ident()?;
                let ty = if matches!(self.peek_kind(), TokenKind::Colon) {
                    self.advance();
                    Some(self.parse_type_expr()?)
                } else {
                    None
                };
                self.expect(&TokenKind::Assign)?;
                let value = self.parse_expr()?;
                let end = self.expect_nl()?;
                Ok(Stmt {
                    kind: StmtKind::Var { name, ty, value },
                    span: start.merge(end),
                })
            }
            TokenKind::KwAssert => {
                let start = self.advance().span;
                let expr = self.parse_expr()?;
                let end = self.expect_nl()?;
                Ok(Stmt {
                    kind: StmtKind::Assert(expr),
                    span: start.merge(end),
                })
            }
            TokenKind::KwReturn => {
                let start = self.advance().span;
                if matches!(self.peek_kind(), TokenKind::Newline) {
                    let end = self.expect_nl()?;
                    return Ok(Stmt {
                        kind: StmtKind::Return {
                            value: None,
                            guard: None,
                        },
                        span: start.merge(end),
                    });
                }
                if self.is_if_inline_ahead() {
                    let val = self.parse_if_inline_expr()?;
                    let end = self.expect_nl()?;
                    return Ok(Stmt {
                        kind: StmtKind::Return {
                            value: Some(val),
                            guard: None,
                        },
                        span: start.merge(end),
                    });
                }
                let val = self.parse_pipe_expr()?;
                let guard = if matches!(self.peek_kind(), TokenKind::KwIf) {
                    self.advance();
                    Some(self.parse_expr()?)
                } else {
                    None
                };
                let end = self.expect_nl()?;
                Ok(Stmt {
                    kind: StmtKind::Return {
                        value: Some(val),
                        guard,
                    },
                    span: start.merge(end),
                })
            }
            TokenKind::KwBreak => {
                let start = self.advance().span;
                let guard = self.parse_opt_guard()?;
                let end = self.expect_nl()?;
                Ok(Stmt {
                    kind: StmtKind::Break { guard },
                    span: start.merge(end),
                })
            }
            TokenKind::KwContinue => {
                let start = self.advance().span;
                let guard = self.parse_opt_guard()?;
                let end = self.expect_nl()?;
                Ok(Stmt {
                    kind: StmtKind::Continue { guard },
                    span: start.merge(end),
                })
            }
            TokenKind::KwStop => {
                let start = self.advance().span;
                let expr = if matches!(self.peek_kind(), TokenKind::Newline) {
                    None
                } else {
                    Some(self.parse_expr()?)
                };
                let end = self.expect_nl()?;
                Ok(Stmt {
                    kind: StmtKind::Stop(expr),
                    span: start.merge(end),
                })
            }
            TokenKind::KwFor => {
                let start = self.advance().span;
                let target = self.parse_for_target()?;
                self.expect(&TokenKind::KwIn)?;
                let iter = self.parse_expr()?;
                self.expect_nl()?;
                let body = self.parse_stmts_until(&[TokenKind::KwEnd])?;
                let end_kw = self.expect(&TokenKind::KwEnd)?;
                self.expect_nl()?;
                Ok(Stmt {
                    kind: StmtKind::For { target, iter, body },
                    span: start.merge(end_kw),
                })
            }
            TokenKind::KwWhile => {
                let start = self.advance().span;
                let cond = self.parse_expr()?;
                self.expect_nl()?;
                let body = self.parse_stmts_until(&[TokenKind::KwEnd])?;
                let end_kw = self.expect(&TokenKind::KwEnd)?;
                self.expect_nl()?;
                Ok(Stmt {
                    kind: StmtKind::While { cond, body },
                    span: start.merge(end_kw),
                })
            }
            _ => {
                let expr = self.parse_expr()?;
                if matches!(self.peek_kind(), TokenKind::Assign) {
                    self.advance();
                    let rhs = self.parse_expr()?;
                    let end = self.expect_nl()?;
                    let span = expr.span.merge(end);
                    Ok(Stmt {
                        kind: StmtKind::Assign { lhs: expr, rhs },
                        span,
                    })
                } else {
                    let end = self.expect_nl()?;
                    let span = expr.span.merge(end);
                    Ok(Stmt {
                        kind: StmtKind::Expr(expr),
                        span,
                    })
                }
            }
        }
    }

    fn parse_opt_guard(&mut self) -> Result<Option<Expr>, Diagnostic> {
        if matches!(self.peek_kind(), TokenKind::KwIf) {
            self.advance();
            Ok(Some(self.parse_expr()?))
        } else {
            Ok(None)
        }
    }

    fn parse_for_target(&mut self) -> Result<ForTarget, Diagnostic> {
        match self.peek_kind() {
            TokenKind::Underscore => Ok(ForTarget::Wildcard(self.advance().span)),
            TokenKind::LParen => {
                let lp = self.advance().span;
                let first = self.parse_for_target()?;
                self.expect(&TokenKind::Comma)?;
                let mut list = vec![first, self.parse_for_target()?];
                while matches!(self.peek_kind(), TokenKind::Comma) {
                    self.advance();
                    list.push(self.parse_for_target()?);
                }
                let rp = self.expect(&TokenKind::RParen)?;
                Ok(ForTarget::Tuple(list, lp.merge(rp)))
            }
            _ => Ok(ForTarget::Name(self.parse_ident()?)),
        }
    }

    // -----------------------------------------------------------------------
    // Expressions (Exact Stratified Precedence from grammar/dana.y)
    // -----------------------------------------------------------------------

    /// O(k) depth-0 lookahead distinguishing inline `if cond: a else: b` from block `if cond\n...\nend`.
    fn is_if_inline_ahead(&self) -> bool {
        if !matches!(self.peek_kind(), TokenKind::KwIf) {
            return false;
        }
        let mut idx = self.pos + 1;
        let mut depth: usize = 0;
        while let Some(tok) = self.tokens.get(idx) {
            match tok.kind {
                TokenKind::LParen | TokenKind::LBrack | TokenKind::LBrace => depth += 1,
                TokenKind::RParen | TokenKind::RBrack | TokenKind::RBrace => {
                    if depth == 0 {
                        return false;
                    }
                    depth -= 1;
                }
                TokenKind::Colon if depth == 0 => return true,
                TokenKind::Newline | TokenKind::Eof if depth == 0 => return false,
                _ => {}
            }
            idx += 1;
        }
        false
    }

    fn parse_expr(&mut self) -> Result<Expr, Diagnostic> {
        self.enter_nested()?;
        let res = if self.is_if_inline_ahead() {
            self.parse_if_inline_expr()
        } else {
            self.parse_pipe_expr()
        };
        self.leave_nested();
        res
    }

    fn parse_pipe_expr(&mut self) -> Result<Expr, Diagnostic> {
        self.parse_bp(1)
    }

    fn parse_unary_expr(&mut self) -> Result<Expr, Diagnostic> {
        self.parse_bp(16)
    }

    /// Pratt expression parser matching `grammar/dana.y`'s exact stratified precedence:
    /// 1: `|>` (left) < 3: `or` (left) < 5: `and` (left) < 7: prefix `not`
    /// < 8: `== != < <= > >= is` (non-associative) < 10: `??` (right)
    /// < 12: `+ -` (left) < 14: `* / %` (left) < 16: prefix `-`, `try` < postfix `. () []`.
    fn parse_bp(&mut self, min_bp: u8) -> Result<Expr, Diagnostic> {
        self.enter_nested()?;
        let res = self.parse_bp_inner(min_bp);
        self.leave_nested();
        res
    }

    fn parse_bp_inner(&mut self, min_bp: u8) -> Result<Expr, Diagnostic> {
        // Prefix / primary
        let mut lhs = match self.peek_kind() {
            TokenKind::KwNot if min_bp <= 7 => {
                let start = self.advance().span;
                let expr = self.parse_bp(7)?;
                let span = start.merge(expr.span);
                Expr {
                    kind: ExprKind::Unary {
                        op: UnaryOp::Not,
                        expr: Box::new(expr),
                    },
                    span,
                }
            }
            TokenKind::Minus => {
                let start = self.advance().span;
                let expr = self.parse_bp(16)?;
                let span = start.merge(expr.span);
                Expr {
                    kind: ExprKind::Unary {
                        op: UnaryOp::Neg,
                        expr: Box::new(expr),
                    },
                    span,
                }
            }
            TokenKind::KwTry => {
                let start = self.advance().span;
                let expr = self.parse_bp(16)?;
                let span = start.merge(expr.span);
                Expr {
                    kind: ExprKind::Unary {
                        op: UnaryOp::Try,
                        expr: Box::new(expr),
                    },
                    span,
                }
            }
            _ => self.parse_postfix_expr()?,
        };

        let mut seen_cmp = false;
        loop {
            let (op, lbp, rbp, is_cmp) = match self.peek_kind() {
                TokenKind::Pipe => (BinOp::Pipe, 1, 2, false),
                TokenKind::KwOr => (BinOp::Or, 3, 4, false),
                TokenKind::KwAnd => (BinOp::And, 5, 6, false),
                TokenKind::Eq => (BinOp::Eq, 8, 9, true),
                TokenKind::Ne => (BinOp::Ne, 8, 9, true),
                TokenKind::Lt => (BinOp::Lt, 8, 9, true),
                TokenKind::Le => (BinOp::Le, 8, 9, true),
                TokenKind::Gt => (BinOp::Gt, 8, 9, true),
                TokenKind::Ge => (BinOp::Ge, 8, 9, true),
                TokenKind::KwIs => (BinOp::Is, 8, 9, true),
                TokenKind::QQ => (BinOp::Coalesce, 10, 10, false),
                TokenKind::Plus => (BinOp::Add, 12, 13, false),
                TokenKind::Minus => (BinOp::Sub, 12, 13, false),
                TokenKind::Star => (BinOp::Mul, 14, 15, false),
                TokenKind::Slash => (BinOp::Div, 14, 15, false),
                TokenKind::Percent => (BinOp::Mod, 14, 15, false),
                _ => break,
            };
            if lbp < min_bp {
                break;
            }
            if is_cmp && seen_cmp {
                // Comparisons are strictly non-associative in `grammar/dana.y`.
                break;
            }
            self.advance();
            let rhs = self.parse_bp(rbp)?;
            let span = lhs.span.merge(rhs.span);
            lhs = Expr {
                kind: ExprKind::Binary {
                    op,
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                },
                span,
            };
            if is_cmp {
                seen_cmp = true;
            } else if lbp < 8 {
                seen_cmp = false;
            }
        }
        Ok(lhs)
    }

    fn parse_postfix_expr(&mut self) -> Result<Expr, Diagnostic> {
        let mut expr = self.parse_primary_expr()?;
        loop {
            match self.peek_kind() {
                TokenKind::Dot => {
                    self.advance();
                    let member = self.parse_member_name()?;
                    let span = expr.span.merge(member.span);
                    expr = Expr {
                        kind: ExprKind::Field {
                            receiver: Box::new(expr),
                            member,
                        },
                        span,
                    };
                }
                TokenKind::LParen => {
                    self.advance();
                    let mut args = Vec::new();
                    if !matches!(self.peek_kind(), TokenKind::RParen) {
                        args.push(self.parse_call_arg()?);
                        while matches!(self.peek_kind(), TokenKind::Comma) {
                            self.advance();
                            args.push(self.parse_call_arg()?);
                        }
                    }
                    let rp = self.expect(&TokenKind::RParen)?;
                    let span = expr.span.merge(rp);
                    expr = Expr {
                        kind: ExprKind::Call {
                            callee: Box::new(expr),
                            args,
                        },
                        span,
                    };
                }
                TokenKind::LBrack => {
                    self.advance();
                    let index = self.parse_expr()?;
                    let rb = self.expect(&TokenKind::RBrack)?;
                    let span = expr.span.merge(rb);
                    expr = Expr {
                        kind: ExprKind::Index {
                            target: Box::new(expr),
                            index: Box::new(index),
                        },
                        span,
                    };
                }
                _ => break,
            }
        }
        Ok(expr)
    }

    fn parse_call_arg(&mut self) -> Result<CallArg, Diagnostic> {
        if Self::is_ident_kind(self.peek_kind()) && matches!(self.peek_at(1).kind, TokenKind::Colon)
        {
            let name = self.parse_ident()?;
            self.advance(); // ':'
            let value = self.parse_expr()?;
            let span = name.span.merge(value.span);
            Ok(CallArg::Named { name, value, span })
        } else {
            Ok(CallArg::Positional(self.parse_expr()?))
        }
    }

    fn parse_primary_expr(&mut self) -> Result<Expr, Diagnostic> {
        let tok = self.peek().clone();
        match tok.kind {
            TokenKind::Int(s) => {
                self.advance();
                Ok(Expr {
                    kind: ExprKind::Int(s),
                    span: tok.span,
                })
            }
            TokenKind::Decimal(s) => {
                self.advance();
                Ok(Expr {
                    kind: ExprKind::Decimal(s),
                    span: tok.span,
                })
            }
            TokenKind::Date(s) => {
                self.advance();
                Ok(Expr {
                    kind: ExprKind::Date(s),
                    span: tok.span,
                })
            }
            TokenKind::Timestamp(s) => {
                self.advance();
                Ok(Expr {
                    kind: ExprKind::Timestamp(s),
                    span: tok.span,
                })
            }
            TokenKind::Text {
                value,
                multiline,
                raw,
            } => {
                self.advance();
                Ok(Expr {
                    kind: ExprKind::Text {
                        value,
                        multiline,
                        raw,
                    },
                    span: tok.span,
                })
            }
            TokenKind::TextHead {
                value,
                multiline,
                raw,
            } => {
                let start = self.advance().span;
                let mut parts = vec![InterpPart::Literal { value, raw }];
                parts.push(InterpPart::Expr(self.parse_expr()?));
                let end = loop {
                    let next = self.peek().clone();
                    match next.kind {
                        TokenKind::TextTail { value, raw, .. } => {
                            self.advance();
                            parts.push(InterpPart::Literal { value, raw });
                            break next.span;
                        }
                        TokenKind::TextMid { value, raw, .. } => {
                            self.advance();
                            parts.push(InterpPart::Literal { value, raw });
                            parts.push(InterpPart::Expr(self.parse_expr()?));
                        }
                        _ => return Err(self.unexpected("end of interpolated string")),
                    }
                };
                Ok(Expr {
                    kind: ExprKind::InterpText { parts, multiline },
                    span: start.merge(end),
                })
            }
            TokenKind::Atom(s) => {
                self.advance();
                Ok(Expr {
                    kind: ExprKind::Atom(s),
                    span: tok.span,
                })
            }
            TokenKind::KwTrue => {
                self.advance();
                Ok(Expr {
                    kind: ExprKind::Bool(true),
                    span: tok.span,
                })
            }
            TokenKind::KwFalse => {
                self.advance();
                Ok(Expr {
                    kind: ExprKind::Bool(false),
                    span: tok.span,
                })
            }
            TokenKind::KwNone => {
                self.advance();
                Ok(Expr {
                    kind: ExprKind::None,
                    span: tok.span,
                })
            }
            TokenKind::Name(s) => {
                self.advance();
                Ok(Expr {
                    kind: ExprKind::Ident(s),
                    span: tok.span,
                })
            }
            TokenKind::KwWhere => {
                self.advance();
                Ok(Expr {
                    kind: ExprKind::Ident("where".to_string()),
                    span: tok.span,
                })
            }
            TokenKind::KwTag => {
                self.advance();
                Ok(Expr {
                    kind: ExprKind::Ident("tag".to_string()),
                    span: tok.span,
                })
            }
            TokenKind::CapName(s) => {
                self.advance();
                Ok(Expr {
                    kind: ExprKind::CapName(s),
                    span: tok.span,
                })
            }
            TokenKind::Underscore => {
                self.advance();
                Ok(Expr {
                    kind: ExprKind::Underscore,
                    span: tok.span,
                })
            }
            TokenKind::Dot => {
                let dot_sp = self.advance().span;
                if Self::is_member_name_kind(self.peek_kind()) {
                    let member = self.parse_member_name()?;
                    let span = dot_sp.merge(member.span);
                    Ok(Expr {
                        kind: ExprKind::DotField(member),
                        span,
                    })
                } else {
                    Ok(Expr {
                        kind: ExprKind::DotSelf,
                        span: dot_sp,
                    })
                }
            }
            TokenKind::LParen => {
                let lp = self.advance().span;
                let first = self.parse_expr()?;
                if matches!(self.peek_kind(), TokenKind::Comma) {
                    let mut elems = vec![first];
                    while matches!(self.peek_kind(), TokenKind::Comma) {
                        self.advance();
                        elems.push(self.parse_expr()?);
                    }
                    let rp = self.expect(&TokenKind::RParen)?;
                    Ok(Expr {
                        kind: ExprKind::Tuple(elems),
                        span: lp.merge(rp),
                    })
                } else {
                    let rp = self.expect(&TokenKind::RParen)?;
                    Ok(Expr {
                        kind: ExprKind::Paren(Box::new(first)),
                        span: lp.merge(rp),
                    })
                }
            }
            TokenKind::LBrack => {
                let lb = self.advance().span;
                let mut elems = Vec::new();
                if !matches!(self.peek_kind(), TokenKind::RBrack) {
                    elems.push(self.parse_expr()?);
                    while matches!(self.peek_kind(), TokenKind::Comma) {
                        self.advance();
                        elems.push(self.parse_expr()?);
                    }
                }
                let rb = self.expect(&TokenKind::RBrack)?;
                Ok(Expr {
                    kind: ExprKind::List(elems),
                    span: lb.merge(rb),
                })
            }
            TokenKind::LBrace => {
                let lb = self.advance().span;
                let mut entries = Vec::new();
                if !matches!(self.peek_kind(), TokenKind::RBrace) {
                    let k = self.parse_expr()?;
                    self.expect(&TokenKind::Colon)?;
                    let v = self.parse_expr()?;
                    entries.push((k, v));
                    while matches!(self.peek_kind(), TokenKind::Comma) {
                        self.advance();
                        let k = self.parse_expr()?;
                        self.expect(&TokenKind::Colon)?;
                        let v = self.parse_expr()?;
                        entries.push((k, v));
                    }
                }
                let rb = self.expect(&TokenKind::RBrace)?;
                Ok(Expr {
                    kind: ExprKind::Map(entries),
                    span: lb.merge(rb),
                })
            }
            TokenKind::KwIf => self.parse_if_block_expr(),
            TokenKind::KwCase => self.parse_case_expr(),
            TokenKind::KwTable => self.parse_table_lit(),
            TokenKind::KwFn => self.parse_lambda_expr(),
            _ => Err(self.unexpected("expression")),
        }
    }

    fn parse_if_inline_expr(&mut self) -> Result<Expr, Diagnostic> {
        let start = self.expect(&TokenKind::KwIf)?;
        let cond = self.parse_pipe_expr()?;
        self.expect(&TokenKind::Colon)?;
        let then_expr = self.parse_expr()?;
        self.skip_newlines();

        let mut else_ifs = Vec::new();
        loop {
            self.expect(&TokenKind::KwElse)?;
            if matches!(self.peek_kind(), TokenKind::KwIf) {
                self.advance();
                let c = self.parse_pipe_expr()?;
                self.expect(&TokenKind::Colon)?;
                let t = self.parse_expr()?;
                self.skip_newlines();
                else_ifs.push((c, t));
            } else {
                self.expect(&TokenKind::Colon)?;
                let else_expr = self.parse_expr()?;
                let span = start.merge(else_expr.span);
                return Ok(Expr {
                    kind: ExprKind::IfInline {
                        cond: Box::new(cond),
                        then_expr: Box::new(then_expr),
                        else_ifs,
                        else_expr: Box::new(else_expr),
                    },
                    span,
                });
            }
        }
    }

    fn parse_if_block_expr(&mut self) -> Result<Expr, Diagnostic> {
        let start = self.expect(&TokenKind::KwIf)?;
        let cond = self.parse_expr()?;
        self.expect_nl()?;
        let then_body = self.parse_stmts_until(&[TokenKind::KwElse, TokenKind::KwEnd])?;
        let mut else_ifs = Vec::new();
        let mut else_body = None;

        while matches!(self.peek_kind(), TokenKind::KwElse) {
            let else_kw = self.advance().span;
            if matches!(self.peek_kind(), TokenKind::KwIf) {
                self.advance();
                let c = self.parse_expr()?;
                self.expect_nl()?;
                let body = self.parse_stmts_until(&[TokenKind::KwElse, TokenKind::KwEnd])?;
                else_ifs.push(ElseIfBranch {
                    else_kw,
                    cond: c,
                    body,
                });
            } else {
                self.expect_nl()?;
                let body = self.parse_stmts_until(&[TokenKind::KwEnd])?;
                else_body = Some(ElseBranch { else_kw, body });
                break;
            }
        }

        let end_kw = self.expect(&TokenKind::KwEnd)?;
        Ok(Expr {
            kind: ExprKind::IfBlock {
                cond: Box::new(cond),
                then_body,
                else_ifs,
                else_body,
            },
            span: start.merge(end_kw),
        })
    }

    /// Check whether the current line inside `case ... end` is a `unary_expr COLON ...` arm
    /// (as opposed to an arm-body statement).
    fn is_case_arm_ahead(&self) -> bool {
        if matches!(
            self.peek_kind(),
            TokenKind::KwVar
                | TokenKind::KwAssert
                | TokenKind::KwReturn
                | TokenKind::KwBreak
                | TokenKind::KwContinue
                | TokenKind::KwStop
                | TokenKind::KwFor
                | TokenKind::KwWhile
                | TokenKind::KwIf
        ) {
            return false;
        }
        let mut idx = self.pos;
        let mut depth: usize = 0;
        while let Some(tok) = self.tokens.get(idx) {
            match tok.kind {
                TokenKind::LParen | TokenKind::LBrack | TokenKind::LBrace => depth += 1,
                TokenKind::RParen | TokenKind::RBrack | TokenKind::RBrace => {
                    if depth == 0 {
                        return false;
                    }
                    depth -= 1;
                }
                TokenKind::Colon if depth == 0 => return true,
                TokenKind::Assign | TokenKind::Newline | TokenKind::Eof if depth == 0 => {
                    return false;
                }
                _ => {}
            }
            idx += 1;
        }
        false
    }

    fn parse_case_expr(&mut self) -> Result<Expr, Diagnostic> {
        let start = self.expect(&TokenKind::KwCase)?;
        let scrut = self.parse_expr()?;
        self.expect_nl()?;
        let mut lines = Vec::new();
        while !matches!(self.peek_kind(), TokenKind::KwEnd | TokenKind::Eof) {
            if self.is_case_arm_ahead() {
                let pattern = self.parse_unary_expr()?;
                self.expect(&TokenKind::Colon)?;
                if matches!(self.peek_kind(), TokenKind::Newline) {
                    let nl = self.expect_nl()?;
                    let span = pattern.span.merge(nl);
                    lines.push(CaseLine::ArmHeader { pattern, span });
                } else {
                    let expr = self.parse_expr()?;
                    let nl = self.expect_nl()?;
                    let span = pattern.span.merge(nl);
                    lines.push(CaseLine::ArmInline {
                        pattern,
                        expr,
                        span,
                    });
                }
            } else {
                lines.push(CaseLine::Stmt(self.parse_stmt()?));
            }
        }
        if lines.is_empty() {
            return Err(Diagnostic::error(
                DiagCode::ParseError,
                "`case` expression requires at least one arm",
            )
            .with_span(self.current_span()));
        }
        let end_kw = self.expect(&TokenKind::KwEnd)?;
        Ok(Expr {
            kind: ExprKind::Case {
                scrut: Box::new(scrut),
                lines,
            },
            span: start.merge(end_kw),
        })
    }

    fn parse_lambda_expr(&mut self) -> Result<Expr, Diagnostic> {
        let start = self.expect(&TokenKind::KwFn)?;
        self.expect(&TokenKind::LParen)?;
        let mut params = Vec::new();
        if !matches!(self.peek_kind(), TokenKind::RParen) {
            params.push(self.parse_lambda_param()?);
            while matches!(self.peek_kind(), TokenKind::Comma) {
                self.advance();
                params.push(self.parse_lambda_param()?);
            }
        }
        self.expect(&TokenKind::RParen)?;
        let body = if matches!(self.peek_kind(), TokenKind::Newline) {
            self.expect_nl()?;
            let stmts = self.parse_stmts_until(&[TokenKind::KwEnd])?;
            LambdaBody::Block(stmts)
        } else {
            LambdaBody::Expr(Box::new(self.parse_expr()?))
        };
        let end_kw = self.expect(&TokenKind::KwEnd)?;
        Ok(Expr {
            kind: ExprKind::Lambda { params, body },
            span: start.merge(end_kw),
        })
    }

    fn parse_lambda_param(&mut self) -> Result<LambdaParam, Diagnostic> {
        if matches!(self.peek_kind(), TokenKind::Underscore) {
            Ok(LambdaParam::Wildcard(self.advance().span))
        } else {
            Ok(LambdaParam::Name(self.parse_ident()?))
        }
    }

    fn parse_table_lit(&mut self) -> Result<Expr, Diagnostic> {
        let start = self.expect(&TokenKind::KwTable)?;
        self.expect_nl()?;
        self.expect(&TokenKind::Bar)?;
        let mut headers = vec![self.parse_ident()?];
        while matches!(self.peek_kind(), TokenKind::Bar)
            && Self::is_ident_kind(&self.peek_at(1).kind)
        {
            self.advance(); // '|'
            headers.push(self.parse_ident()?);
        }
        self.expect(&TokenKind::Bar)?;
        self.expect_nl()?;

        let mut rows = Vec::new();
        while matches!(self.peek_kind(), TokenKind::Bar) {
            self.advance(); // leading '|'
            let mut cells = vec![self.parse_expr()?];
            while matches!(self.peek_kind(), TokenKind::Bar)
                && !matches!(self.peek_at(1).kind, TokenKind::Newline | TokenKind::Eof)
            {
                self.advance(); // separator '|'
                cells.push(self.parse_expr()?);
            }
            self.expect(&TokenKind::Bar)?;
            self.expect_nl()?;
            rows.push(cells);
        }

        let end_kw = self.expect(&TokenKind::KwEnd)?;
        Ok(Expr {
            kind: ExprKind::TableLit { headers, rows },
            span: start.merge(end_kw),
        })
    }
}

static EOF_FALLBACK: Token = Token {
    kind: TokenKind::Eof,
    span: Span {
        file: FileId(0),
        start: 0,
        end: 0,
    },
};
