//! Canonical `(dana-core 0.1 ...)` S-expression wire codec (printer & parser)
//! and canonical `(dana-report 0.1 ...)` formatter for Dana Core IR v0.1.
//!
//! Mirrors `formal/DanaCore/Text.lean` byte-for-byte.

use std::fmt;
use std::str::FromStr;

use crate::core::bigint::BigInt;
use crate::core::stack::with_large_stack;
use crate::core::syntax::{
    AggItem, AggKind, AggOp, BugKind, CaseArm, ChartKind, ColSpec, CompilerMetadata, ConstDecl,
    CoreVersion, CtorDecl, DataDecl, DeriveItem, Expr, Float64, FunDecl, FunKind, HostOp, Ident,
    JoinKind, JoinOn, LTy, Literal, MetaEntry, Plan, Policy, PolicyWriteRule, PrimOp, Program,
    RowExpr, RowLit, ScalarTy, SchemaDecl, SortDir, SourceSpan, SuppressMode, TableTy, TagSet, Ty,
    WindowFn, WindowItem,
};
use crate::oracle::world::{ExecReport, ExitStatus};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WireError {
    pub message: String,
}

impl WireError {
    #[must_use]
    pub fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
        }
    }
}

impl fmt::Display for WireError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.message)
    }
}

impl std::error::Error for WireError {}

fn err<T>(msg: impl Into<String>) -> Result<T, WireError> {
    Err(WireError::new(msg))
}

// ---------------------------------------------------------------------------
// Canonical S-Expression AST & Printer
// ---------------------------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SExp {
    Atom(String),
    Str(String),
    List(Vec<SExp>),
}

impl Drop for SExp {
    fn drop(&mut self) {
        if let Self::List(items) = self {
            let mut stack = std::mem::take(items);
            while let Some(mut node) = stack.pop() {
                if let Self::List(children) = &mut node {
                    stack.extend(std::mem::take(children));
                }
            }
        }
    }
}

#[must_use]
pub fn is_control_char(c: char) -> bool {
    let cp = c as u32;
    cp < 0x20 || cp == 0x7F || (0x80..=0x9F).contains(&cp)
}

#[must_use]
pub fn escape_canonical_string(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if is_control_char(c) => {
                use std::fmt::Write as _;
                let _ = write!(out, "\\u{{{:x}}}", c as u32);
            }
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

enum WriteFrame<'a> {
    Node(&'a SExp),
    Space,
    CloseParen,
}

#[must_use]
pub fn print_sexp(sexp: &SExp) -> String {
    let mut out = String::new();
    let mut stack = vec![WriteFrame::Node(sexp)];
    while let Some(frame) = stack.pop() {
        match frame {
            WriteFrame::Space => out.push(' '),
            WriteFrame::CloseParen => out.push(')'),
            WriteFrame::Node(SExp::Atom(s)) => out.push_str(s),
            WriteFrame::Node(SExp::Str(s)) => out.push_str(&escape_canonical_string(s)),
            WriteFrame::Node(SExp::List(items)) => {
                out.push('(');
                stack.push(WriteFrame::CloseParen);
                for (i, item) in items.iter().enumerate().rev() {
                    stack.push(WriteFrame::Node(item));
                    if i > 0 {
                        stack.push(WriteFrame::Space);
                    }
                }
            }
        }
    }
    out
}

// ---------------------------------------------------------------------------
// Strict S-Expression Tokenizer & Parser
// ---------------------------------------------------------------------------

fn is_lower_hex_digit(c: char) -> bool {
    c.is_ascii_digit() || ('a'..='f').contains(&c)
}

fn hex_val(c: char) -> u32 {
    if c.is_ascii_digit() {
        (c as u32) - ('0' as u32)
    } else {
        10 + ((c as u32) - ('a' as u32))
    }
}

fn parse_lower_hex_u32(cs: &[char]) -> Option<u32> {
    if cs.is_empty() || cs.len() > 6 || !cs.iter().copied().all(is_lower_hex_digit) {
        return None;
    }
    let mut acc = 0u32;
    for &c in cs {
        acc = acc * 16 + hex_val(c);
    }
    Some(acc)
}

fn is_atom_char(c: char) -> bool {
    !is_control_char(c) && !matches!(c, ' ' | '(' | ')' | '"' | '\\')
}

fn parse_escaped_string(chars: &[char], mut pos: usize) -> Result<(String, usize), WireError> {
    let mut acc = String::new();
    loop {
        let Some(&c) = chars.get(pos) else {
            return err("unterminated string literal");
        };
        pos += 1;
        match c {
            '"' => return Ok((acc, pos)),
            '\\' => {
                let Some(&esc) = chars.get(pos) else {
                    return err("trailing backslash in string");
                };
                pos += 1;
                match esc {
                    '"' => acc.push('"'),
                    '\\' => acc.push('\\'),
                    'n' => acc.push('\n'),
                    'r' => acc.push('\r'),
                    't' => acc.push('\t'),
                    'u' => {
                        if chars.get(pos) != Some(&'{') {
                            return err("expected '{' after \\u");
                        }
                        pos += 1;
                        let start = pos;
                        while chars.get(pos).is_some_and(|&ch| ch != '}') {
                            pos += 1;
                        }
                        if chars.get(pos) != Some(&'}') {
                            return err("unclosed \\u{...} escape");
                        }
                        let hex_slice = &chars[start..pos];
                        pos += 1; // consume '}'
                        let Some(cp) = parse_lower_hex_u32(hex_slice) else {
                            return err("invalid or non-lowercase \\u{hex} escape in string");
                        };
                        if (0xD800..=0xDFFF).contains(&cp) || cp > 0x10FFFF {
                            return err("surrogate or out-of-range Unicode scalar in \\u{hex}");
                        }
                        let Some(ch) = char::from_u32(cp) else {
                            return err("surrogate or out-of-range Unicode scalar in \\u{hex}");
                        };
                        let hex_str: String = hex_slice.iter().collect();
                        let canon_hex = format!("{cp:x}");
                        if !is_control_char(ch)
                            || matches!(ch, '\n' | '\r' | '\t')
                            || hex_str != canon_hex
                        {
                            return err("non-canonical \\u{hex} escape in string");
                        }
                        acc.push(ch);
                    }
                    other => return err(format!("unknown string escape '\\{other}'")),
                }
            }
            ch => {
                if is_control_char(ch) {
                    return err("raw control character inside string literal");
                }
                acc.push(ch);
            }
        }
    }
}

fn parse_sexp_chars(chars: &[char], mut pos: usize) -> Result<(SExp, usize), WireError> {
    let mut stack: Vec<Vec<SExp>> = Vec::new();
    let mut expect_item = true;
    loop {
        if expect_item {
            let Some(&c) = chars.get(pos) else {
                return err("unexpected end of S-expression");
            };
            match c {
                '(' => {
                    stack.push(Vec::new());
                    pos += 1;
                    expect_item = false;
                }
                '"' => {
                    let (s, next) = parse_escaped_string(chars, pos + 1)?;
                    let node = SExp::Str(s);
                    pos = next;
                    if let Some(cur) = stack.last_mut() {
                        cur.push(node);
                        expect_item = false;
                    } else {
                        return Ok((node, pos));
                    }
                }
                _ => {
                    if !is_atom_char(c) {
                        return err("unexpected delimiter or control character in S-expression");
                    }
                    let mut end = pos + 1;
                    while chars.get(end).copied().is_some_and(is_atom_char) {
                        end += 1;
                    }
                    let atom_str: String = chars[pos..end].iter().collect();
                    let node = SExp::Atom(atom_str);
                    pos = end;
                    if let Some(cur) = stack.last_mut() {
                        cur.push(node);
                        expect_item = false;
                    } else {
                        return Ok((node, pos));
                    }
                }
            }
        } else {
            let Some(&c) = chars.get(pos) else {
                return err("unclosed '(' in S-expression");
            };
            match c {
                ')' => {
                    let Some(items) = stack.pop() else {
                        return err("unexpected delimiter or control character in S-expression");
                    };
                    let completed = SExp::List(items);
                    pos += 1;
                    if let Some(parent) = stack.last_mut() {
                        parent.push(completed);
                    } else {
                        return Ok((completed, pos));
                    }
                }
                ' ' => {
                    if chars.get(pos + 1) == Some(&')') {
                        return err("trailing space before ')' in canonical S-expression");
                    }
                    if chars.get(pos + 1) == Some(&' ') {
                        return err("duplicate space in canonical S-expression");
                    }
                    if stack.last().is_some_and(Vec::is_empty) {
                        return err("leading space after '(' in canonical S-expression");
                    }
                    pos += 1;
                    expect_item = true;
                }
                _ => {
                    if stack.last().is_some_and(|v| !v.is_empty()) {
                        return err("missing single space separator between S-expression items");
                    }
                    expect_item = true;
                }
            }
        }
    }
}

/// Parse a complete canonical single-line S-expression (requiring a single trailing LF).
pub fn parse_canonical_sexp(input: &str) -> Result<SExp, WireError> {
    let Some(body) = input.strip_suffix('\n') else {
        return err("canonical wire format requires single trailing LF");
    };
    if body.contains('\n') || body.contains('\r') {
        return err("internal line breaks forbidden in canonical wire format");
    }
    let body_chars: Vec<char> = body.chars().collect();
    if body_chars.iter().copied().any(is_control_char) {
        return err("raw control characters forbidden in canonical wire format");
    }
    let (sexp, end) = parse_sexp_chars(&body_chars, 0)?;
    if end == body_chars.len() {
        Ok(sexp)
    } else {
        err("trailing characters after top-level S-expression")
    }
}

// ---------------------------------------------------------------------------
// Primitive Encoders & Decoders
// ---------------------------------------------------------------------------

fn atom(s: &str) -> SExp {
    SExp::Atom(s.to_string())
}

fn encode_bool(b: bool) -> SExp {
    atom(if b { "true" } else { "false" })
}

fn decode_bool(s: &SExp) -> Result<bool, WireError> {
    match s {
        SExp::Atom(a) if a == "true" => Ok(true),
        SExp::Atom(a) if a == "false" => Ok(false),
        _ => err("expected bool atom"),
    }
}

fn encode_nat(n: u64) -> SExp {
    SExp::Atom(n.to_string())
}

fn decode_nat(s: &SExp) -> Result<u64, WireError> {
    match s {
        SExp::Atom(a) => {
            if a.is_empty() || !a.bytes().all(|b| b.is_ascii_digit()) {
                return err(format!("expected Nat, got '{a}'"));
            }
            a.parse::<u64>()
                .map_err(|_| WireError::new("non-canonical wire encoding (Nat out of range)"))
        }
        _ => err("expected Nat atom"),
    }
}

fn encode_big_nat(n: &BigInt) -> SExp {
    SExp::Atom(n.to_string())
}

fn decode_big_nat(s: &SExp) -> Result<BigInt, WireError> {
    match s {
        SExp::Atom(a) => {
            if a.is_empty() || !a.bytes().all(|b| b.is_ascii_digit()) {
                return err(format!("expected Nat, got '{a}'"));
            }
            BigInt::from_str(a).map_err(|_| WireError::new(format!("expected Nat, got '{a}'")))
        }
        _ => err("expected Nat atom"),
    }
}

fn encode_int(n: &BigInt) -> SExp {
    SExp::Atom(n.to_string())
}

fn decode_int(s: &SExp) -> Result<BigInt, WireError> {
    match s {
        SExp::Atom(a) => {
            BigInt::from_str(a).map_err(|_| WireError::new(format!("expected Int, got '{a}'")))
        }
        _ => err("expected Int atom"),
    }
}

fn encode_ident(id: &str) -> SExp {
    SExp::Str(id.to_string())
}

fn decode_ident(s: &SExp) -> Result<Ident, WireError> {
    match s {
        SExp::Str(v) | SExp::Atom(v) => Ok(v.clone()),
        SExp::List(_) => err("expected identifier"),
    }
}

fn decode_str_only(s: &SExp) -> Result<String, WireError> {
    match s {
        SExp::Str(v) => Ok(v.clone()),
        _ => err("expected string literal"),
    }
}

fn encode_opt<T>(opt: &Option<T>, enc: impl Fn(&T) -> SExp) -> SExp {
    match opt {
        None => SExp::List(vec![atom("none")]),
        Some(v) => SExp::List(vec![atom("some"), enc(v)]),
    }
}

fn decode_opt<T>(
    s: &SExp,
    dec: impl Fn(&SExp) -> Result<T, WireError>,
) -> Result<Option<T>, WireError> {
    match s {
        SExp::List(xs) => match xs.as_slice() {
            [SExp::Atom(tag)] if tag == "none" => Ok(None),
            [SExp::Atom(tag), x] if tag == "some" => Ok(Some(dec(x)?)),
            _ => err("expected (none) or (some ...)"),
        },
        _ => err("expected (none) or (some ...)"),
    }
}

fn map_decode<T>(
    items: &[SExp],
    dec: impl Fn(&SExp) -> Result<T, WireError>,
) -> Result<Vec<T>, WireError> {
    items.iter().map(dec).collect()
}

fn as_list(s: &SExp) -> Result<&[SExp], WireError> {
    match s {
        SExp::List(xs) => Ok(xs),
        _ => err("expected S-expression list"),
    }
}

// ---------------------------------------------------------------------------
// Sensitivity, Schema, and Type Wire Serialization
// ---------------------------------------------------------------------------

fn encode_tag_set(ts: &TagSet) -> SExp {
    let mut items = Vec::with_capacity(ts.elems().len() + 1);
    items.push(atom("tags"));
    items.extend(ts.elems().iter().map(|t| encode_ident(t)));
    SExp::List(items)
}

fn decode_tag_set(s: &SExp) -> Result<TagSet, WireError> {
    let xs = as_list(s)?;
    let Some((SExp::Atom(head), rest)) = xs.split_first() else {
        return err("expected (tags ...)");
    };
    if head != "tags" {
        return err("expected (tags ...)");
    }
    let names = map_decode(rest, decode_ident)?;
    TagSet::from_canonical_elems(names)
        .ok_or_else(|| WireError::new("non-canonical unsorted or duplicate TagSet on wire"))
}

fn encode_agg_kind(ak: AggKind) -> SExp {
    match ak {
        AggKind::Raw => atom("raw"),
        AggKind::GroupKey => atom("group-key"),
        AggKind::Blending => atom("blending"),
        AggKind::NonBlending => atom("non-blending"),
    }
}

fn decode_agg_kind(s: &SExp) -> Result<AggKind, WireError> {
    match s {
        SExp::Atom(a) => match a.as_str() {
            "raw" => Ok(AggKind::Raw),
            "group-key" => Ok(AggKind::GroupKey),
            "blending" => Ok(AggKind::Blending),
            "non-blending" => Ok(AggKind::NonBlending),
            _ => err("expected agg-kind"),
        },
        _ => err("expected agg-kind"),
    }
}

fn encode_scalar_ty(ty: &ScalarTy) -> SExp {
    let mut opt_depth = 0usize;
    let mut cur = ty;
    while let ScalarTy::Option(inner) = cur {
        opt_depth += 1;
        cur = inner;
    }
    let mut out = match cur {
        ScalarTy::Unit => SExp::List(vec![atom("unit")]),
        ScalarTy::Bool => SExp::List(vec![atom("bool")]),
        ScalarTy::Int => SExp::List(vec![atom("int")]),
        ScalarTy::Decimal => SExp::List(vec![atom("decimal")]),
        ScalarTy::Float => SExp::List(vec![atom("float")]),
        ScalarTy::Text => SExp::List(vec![atom("text")]),
        ScalarTy::Bytes => SExp::List(vec![atom("bytes")]),
        ScalarTy::Date => SExp::List(vec![atom("date")]),
        ScalarTy::Timestamp => SExp::List(vec![atom("timestamp")]),
        ScalarTy::Duration => SExp::List(vec![atom("duration")]),
        ScalarTy::Data(n) => SExp::List(vec![atom("data"), encode_ident(n)]),
        ScalarTy::Option(_) => unreachable!("peeled above"),
    };
    for _ in 0..opt_depth {
        out = SExp::List(vec![atom("option"), out]);
    }
    out
}

fn decode_scalar_ty(s: &SExp) -> Result<ScalarTy, WireError> {
    let mut opt_depth = 0usize;
    let mut cur = s;
    loop {
        let xs = as_list(cur)?;
        if let [SExp::Atom(t), inner] = xs
            && t == "option"
        {
            opt_depth += 1;
            cur = inner;
            continue;
        }
        let mut out = match xs {
            [SExp::Atom(t)] => match t.as_str() {
                "unit" => Ok(ScalarTy::Unit),
                "bool" => Ok(ScalarTy::Bool),
                "int" => Ok(ScalarTy::Int),
                "decimal" => Ok(ScalarTy::Decimal),
                "float" => Ok(ScalarTy::Float),
                "text" => Ok(ScalarTy::Text),
                "bytes" => Ok(ScalarTy::Bytes),
                "date" => Ok(ScalarTy::Date),
                "timestamp" => Ok(ScalarTy::Timestamp),
                "duration" => Ok(ScalarTy::Duration),
                _ => err("invalid scalar-ty"),
            },
            [SExp::Atom(t), n] if t == "data" => Ok(ScalarTy::Data(decode_ident(n)?)),
            _ => err("invalid scalar-ty"),
        }?;
        for _ in 0..opt_depth {
            out = ScalarTy::Option(Box::new(out));
        }
        return Ok(out);
    }
}

fn encode_col_spec(c: &ColSpec) -> SExp {
    SExp::List(vec![
        atom("col"),
        encode_ident(&c.name),
        encode_scalar_ty(&c.ty),
        encode_tag_set(&c.tags),
        encode_bool(c.bucketed),
        encode_agg_kind(c.agg_kind),
    ])
}

fn decode_col_spec(s: &SExp) -> Result<ColSpec, WireError> {
    let xs = as_list(s)?;
    let [SExp::Atom(h), n, t, ts, b, ak] = xs else {
        return err("expected (col ...)");
    };
    if h != "col" {
        return err("expected (col ...)");
    }
    Ok(ColSpec {
        name: decode_ident(n)?,
        ty: decode_scalar_ty(t)?,
        tags: decode_tag_set(ts)?,
        bucketed: decode_bool(b)?,
        agg_kind: decode_agg_kind(ak)?,
    })
}

fn encode_table_ty(tt: &TableTy) -> SExp {
    SExp::List(vec![
        atom("table-ty"),
        SExp::List(tt.cols.iter().map(encode_col_spec).collect()),
        encode_tag_set(&tt.row_tags),
        encode_tag_set(&tt.order_tags),
        encode_opt(&tt.grouped_by, |ks| {
            SExp::List(ks.iter().map(|k| encode_ident(k)).collect())
        }),
        encode_bool(tt.summarized),
        encode_opt(&tt.distinct_by, |db| encode_ident(db)),
    ])
}

fn decode_table_ty(s: &SExp) -> Result<TableTy, WireError> {
    let xs = as_list(s)?;
    let [SExp::Atom(h), cs, rt, ot, gb, sum_b, db] = xs else {
        return err("expected (table-ty ...)");
    };
    if h != "table-ty" {
        return err("expected (table-ty ...)");
    }
    Ok(TableTy {
        cols: map_decode(as_list(cs)?, decode_col_spec)?,
        row_tags: decode_tag_set(rt)?,
        order_tags: decode_tag_set(ot)?,
        grouped_by: decode_opt(gb, |x| map_decode(as_list(x)?, decode_ident))?,
        summarized: decode_bool(sum_b)?,
        distinct_by: decode_opt(db, decode_ident)?,
    })
}

enum EncodeTyBuild<'a> {
    Option,
    Result,
    Tuple(usize),
    List,
    Map,
    Fn { n_params: usize, pc: &'a TagSet },
    LTy(&'a TagSet),
}

enum EncodeTyTask<'a> {
    Ty(&'a Ty),
    LTy(&'a LTy),
    Finish(EncodeTyBuild<'a>),
}

fn encode_ty_iter(init: EncodeTyTask<'_>) -> SExp {
    let mut tasks = vec![init];
    let mut vals: Vec<SExp> = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            EncodeTyTask::LTy(lty) => {
                tasks.push(EncodeTyTask::Finish(EncodeTyBuild::LTy(&lty.tags)));
                tasks.push(EncodeTyTask::Ty(&lty.ty));
            }
            EncodeTyTask::Ty(ty) => match ty {
                Ty::Unit => vals.push(SExp::List(vec![atom("unit")])),
                Ty::Bool => vals.push(SExp::List(vec![atom("bool")])),
                Ty::Int => vals.push(SExp::List(vec![atom("int")])),
                Ty::Decimal => vals.push(SExp::List(vec![atom("decimal")])),
                Ty::Float => vals.push(SExp::List(vec![atom("float")])),
                Ty::Text => vals.push(SExp::List(vec![atom("text")])),
                Ty::Bytes => vals.push(SExp::List(vec![atom("bytes")])),
                Ty::Date => vals.push(SExp::List(vec![atom("date")])),
                Ty::Timestamp => vals.push(SExp::List(vec![atom("timestamp")])),
                Ty::Duration => vals.push(SExp::List(vec![atom("duration")])),
                Ty::Option(t) => {
                    tasks.push(EncodeTyTask::Finish(EncodeTyBuild::Option));
                    tasks.push(EncodeTyTask::Ty(t));
                }
                Ty::Result { ok_ty, err_ty } => {
                    tasks.push(EncodeTyTask::Finish(EncodeTyBuild::Result));
                    tasks.push(EncodeTyTask::Ty(err_ty));
                    tasks.push(EncodeTyTask::Ty(ok_ty));
                }
                Ty::Tuple(es) => {
                    tasks.push(EncodeTyTask::Finish(EncodeTyBuild::Tuple(es.len())));
                    for e in es.iter().rev() {
                        tasks.push(EncodeTyTask::LTy(e));
                    }
                }
                Ty::List(e) => {
                    tasks.push(EncodeTyTask::Finish(EncodeTyBuild::List));
                    tasks.push(EncodeTyTask::LTy(e));
                }
                Ty::Map { key, val } => {
                    tasks.push(EncodeTyTask::Finish(EncodeTyBuild::Map));
                    tasks.push(EncodeTyTask::LTy(val));
                    tasks.push(EncodeTyTask::LTy(key));
                }
                Ty::Data(n) => vals.push(SExp::List(vec![atom("data"), encode_ident(n)])),
                Ty::Table(tt) => vals.push(SExp::List(vec![atom("table"), encode_table_ty(tt)])),
                Ty::DynamicTable(ts) => {
                    vals.push(SExp::List(vec![atom("dynamic-table"), encode_tag_set(ts)]));
                }
                Ty::Chart(ts) => vals.push(SExp::List(vec![atom("chart"), encode_tag_set(ts)])),
                Ty::Report(ts) => {
                    vals.push(SExp::List(vec![atom("report-ty"), encode_tag_set(ts)]));
                }
                Ty::Profile(ts) => {
                    vals.push(SExp::List(vec![atom("profile"), encode_tag_set(ts)]));
                }
                Ty::LinearModel => vals.push(SExp::List(vec![atom("linear-model")])),
                Ty::StatTest => vals.push(SExp::List(vec![atom("stat-test")])),
                Ty::Fn { params, pc, ret } => {
                    tasks.push(EncodeTyTask::Finish(EncodeTyBuild::Fn {
                        n_params: params.len(),
                        pc,
                    }));
                    tasks.push(EncodeTyTask::LTy(ret));
                    for p in params.iter().rev() {
                        tasks.push(EncodeTyTask::LTy(p));
                    }
                }
                Ty::Args => vals.push(SExp::List(vec![atom("args")])),
                Ty::Clock => vals.push(SExp::List(vec![atom("clock")])),
                Ty::Console(allows) => {
                    vals.push(SExp::List(vec![atom("console"), encode_tag_set(allows)]));
                }
                Ty::ReadFiles => vals.push(SExp::List(vec![atom("read-files")])),
                Ty::WriteFiles { root, allows } => vals.push(SExp::List(vec![
                    atom("write-files"),
                    SExp::Str(root.clone()),
                    encode_tag_set(allows),
                ])),
                Ty::ReadDB(db) => vals.push(SExp::List(vec![atom("read-db"), encode_ident(db)])),
                Ty::WriteTable {
                    db,
                    table_name,
                    dest_cols,
                    dest_row_tags,
                    allows,
                } => vals.push(SExp::List(vec![
                    atom("write-table"),
                    encode_ident(db),
                    encode_ident(table_name),
                    SExp::List(dest_cols.iter().map(encode_col_spec).collect()),
                    encode_tag_set(dest_row_tags),
                    encode_tag_set(allows),
                ])),
                Ty::RawReadDB(db) => {
                    vals.push(SExp::List(vec![atom("raw-read-db"), encode_ident(db)]));
                }
                Ty::HttpsAllow { host, allows } => vals.push(SExp::List(vec![
                    atom("https-allow"),
                    SExp::Str(host.clone()),
                    encode_tag_set(allows),
                ])),
                Ty::Secret(name) => {
                    vals.push(SExp::List(vec![atom("secret"), SExp::Str(name.clone())]));
                }
                Ty::Declassify(allows) => {
                    vals.push(SExp::List(vec![atom("declassify"), encode_tag_set(allows)]));
                }
            },
            EncodeTyTask::Finish(build) => match build {
                EncodeTyBuild::Option => {
                    let Some(inner) = vals.pop() else {
                        unreachable!("stack balanced");
                    };
                    vals.push(SExp::List(vec![atom("option"), inner]));
                }
                EncodeTyBuild::Result => {
                    let (Some(err_s), Some(ok_s)) = (vals.pop(), vals.pop()) else {
                        unreachable!("stack balanced");
                    };
                    vals.push(SExp::List(vec![atom("result"), ok_s, err_s]));
                }
                EncodeTyBuild::Tuple(n) => {
                    let elems = vals.split_off(vals.len() - n);
                    vals.push(SExp::List(vec![atom("tuple"), SExp::List(elems)]));
                }
                EncodeTyBuild::List => {
                    let Some(elem) = vals.pop() else {
                        unreachable!("stack balanced");
                    };
                    vals.push(SExp::List(vec![atom("list"), elem]));
                }
                EncodeTyBuild::Map => {
                    let (Some(v), Some(k)) = (vals.pop(), vals.pop()) else {
                        unreachable!("stack balanced");
                    };
                    vals.push(SExp::List(vec![atom("map"), k, v]));
                }
                EncodeTyBuild::Fn { n_params, pc } => {
                    let Some(ret_s) = vals.pop() else {
                        unreachable!("stack balanced");
                    };
                    let ps = vals.split_off(vals.len() - n_params);
                    vals.push(SExp::List(vec![
                        atom("fn-ty"),
                        SExp::List(ps),
                        encode_tag_set(pc),
                        ret_s,
                    ]));
                }
                EncodeTyBuild::LTy(tags) => {
                    let Some(t_s) = vals.pop() else {
                        unreachable!("stack balanced");
                    };
                    vals.push(SExp::List(vec![atom("lty"), t_s, encode_tag_set(tags)]));
                }
            },
        }
    }
    match vals.pop() {
        Some(res) => res,
        None => unreachable!("encode_ty_iter always produces one SExp"),
    }
}

fn encode_ty(ty: &Ty) -> SExp {
    encode_ty_iter(EncodeTyTask::Ty(ty))
}

fn encode_lty(lty: &LTy) -> SExp {
    encode_ty_iter(EncodeTyTask::LTy(lty))
}

enum DecodedTyVal {
    Ty(Ty),
    LTy(LTy),
    Tags(TagSet),
}

enum DecodeTyBuild<'a> {
    Option,
    Result,
    Tuple(usize),
    List,
    Map,
    Fn { n_params: usize },
    LTy(&'a SExp),
}

enum DecodeTyTask<'a> {
    Ty(&'a SExp),
    LTy(&'a SExp),
    TagSet(&'a SExp),
    Finish(DecodeTyBuild<'a>),
}

fn decode_ty_iter(init: DecodeTyTask<'_>) -> Result<DecodedTyVal, WireError> {
    let mut tasks = vec![init];
    let mut vals: Vec<DecodedTyVal> = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            DecodeTyTask::TagSet(s) => {
                vals.push(DecodedTyVal::Tags(decode_tag_set(s)?));
            }
            DecodeTyTask::LTy(s) => {
                let xs = as_list(s)?;
                let [SExp::Atom(h), t, ts] = xs else {
                    return err("expected (lty ...)");
                };
                if h != "lty" {
                    return err("expected (lty ...)");
                }
                tasks.push(DecodeTyTask::Finish(DecodeTyBuild::LTy(ts)));
                tasks.push(DecodeTyTask::Ty(t));
            }
            DecodeTyTask::Ty(s) => {
                let xs = as_list(s)?;
                match xs {
                    [SExp::Atom(t)] => {
                        let ty = match t.as_str() {
                            "unit" => Ty::Unit,
                            "bool" => Ty::Bool,
                            "int" => Ty::Int,
                            "decimal" => Ty::Decimal,
                            "float" => Ty::Float,
                            "text" => Ty::Text,
                            "bytes" => Ty::Bytes,
                            "date" => Ty::Date,
                            "timestamp" => Ty::Timestamp,
                            "duration" => Ty::Duration,
                            "linear-model" => Ty::LinearModel,
                            "stat-test" => Ty::StatTest,
                            "args" => Ty::Args,
                            "clock" => Ty::Clock,
                            "read-files" => Ty::ReadFiles,
                            _ => return err("invalid Ty S-expression"),
                        };
                        vals.push(DecodedTyVal::Ty(ty));
                    }
                    [SExp::Atom(t), x] => match t.as_str() {
                        "option" => {
                            tasks.push(DecodeTyTask::Finish(DecodeTyBuild::Option));
                            tasks.push(DecodeTyTask::Ty(x));
                        }
                        "tuple" => {
                            let elems = as_list(x)?;
                            tasks.push(DecodeTyTask::Finish(DecodeTyBuild::Tuple(elems.len())));
                            for e in elems.iter().rev() {
                                tasks.push(DecodeTyTask::LTy(e));
                            }
                        }
                        "list" => {
                            tasks.push(DecodeTyTask::Finish(DecodeTyBuild::List));
                            tasks.push(DecodeTyTask::LTy(x));
                        }
                        "data" => vals.push(DecodedTyVal::Ty(Ty::Data(decode_ident(x)?))),
                        "table" => vals.push(DecodedTyVal::Ty(Ty::Table(decode_table_ty(x)?))),
                        "dynamic-table" => {
                            vals.push(DecodedTyVal::Ty(Ty::DynamicTable(decode_tag_set(x)?)));
                        }
                        "chart" => vals.push(DecodedTyVal::Ty(Ty::Chart(decode_tag_set(x)?))),
                        "report-ty" => vals.push(DecodedTyVal::Ty(Ty::Report(decode_tag_set(x)?))),
                        "profile" => vals.push(DecodedTyVal::Ty(Ty::Profile(decode_tag_set(x)?))),
                        "console" => vals.push(DecodedTyVal::Ty(Ty::Console(decode_tag_set(x)?))),
                        "read-db" => vals.push(DecodedTyVal::Ty(Ty::ReadDB(decode_ident(x)?))),
                        "raw-read-db" => {
                            vals.push(DecodedTyVal::Ty(Ty::RawReadDB(decode_ident(x)?)));
                        }
                        "secret" => vals.push(DecodedTyVal::Ty(Ty::Secret(decode_str_only(x)?))),
                        "declassify" => {
                            vals.push(DecodedTyVal::Ty(Ty::Declassify(decode_tag_set(x)?)));
                        }
                        _ => return err("invalid Ty S-expression"),
                    },
                    [SExp::Atom(t), a, b] => match t.as_str() {
                        "result" => {
                            tasks.push(DecodeTyTask::Finish(DecodeTyBuild::Result));
                            tasks.push(DecodeTyTask::Ty(b));
                            tasks.push(DecodeTyTask::Ty(a));
                        }
                        "map" => {
                            tasks.push(DecodeTyTask::Finish(DecodeTyBuild::Map));
                            tasks.push(DecodeTyTask::LTy(b));
                            tasks.push(DecodeTyTask::LTy(a));
                        }
                        "write-files" => vals.push(DecodedTyVal::Ty(Ty::WriteFiles {
                            root: decode_str_only(a)?,
                            allows: decode_tag_set(b)?,
                        })),
                        "https-allow" => vals.push(DecodedTyVal::Ty(Ty::HttpsAllow {
                            host: decode_str_only(a)?,
                            allows: decode_tag_set(b)?,
                        })),
                        _ => return err("invalid Ty S-expression"),
                    },
                    [SExp::Atom(t), ps, pc, ret] if t == "fn-ty" => {
                        let p_list = as_list(ps)?;
                        tasks.push(DecodeTyTask::Finish(DecodeTyBuild::Fn {
                            n_params: p_list.len(),
                        }));
                        tasks.push(DecodeTyTask::LTy(ret));
                        tasks.push(DecodeTyTask::TagSet(pc));
                        for p in p_list.iter().rev() {
                            tasks.push(DecodeTyTask::LTy(p));
                        }
                    }
                    [SExp::Atom(t), db, tbl, cs, rt, allows] if t == "write-table" => {
                        vals.push(DecodedTyVal::Ty(Ty::WriteTable {
                            db: decode_ident(db)?,
                            table_name: decode_ident(tbl)?,
                            dest_cols: map_decode(as_list(cs)?, decode_col_spec)?,
                            dest_row_tags: decode_tag_set(rt)?,
                            allows: decode_tag_set(allows)?,
                        }));
                    }
                    _ => return err("invalid Ty S-expression"),
                }
            }
            DecodeTyTask::Finish(build) => match build {
                DecodeTyBuild::Option => {
                    let Some(DecodedTyVal::Ty(inner)) = vals.pop() else {
                        unreachable!("stack balanced");
                    };
                    vals.push(DecodedTyVal::Ty(Ty::Option(Box::new(inner))));
                }
                DecodeTyBuild::Result => {
                    let (Some(DecodedTyVal::Ty(err_ty)), Some(DecodedTyVal::Ty(ok_ty))) =
                        (vals.pop(), vals.pop())
                    else {
                        unreachable!("stack balanced");
                    };
                    vals.push(DecodedTyVal::Ty(Ty::Result {
                        ok_ty: Box::new(ok_ty),
                        err_ty: Box::new(err_ty),
                    }));
                }
                DecodeTyBuild::Tuple(n) => {
                    let raw = vals.split_off(vals.len() - n);
                    let mut elems = Vec::with_capacity(n);
                    for item in raw {
                        if let DecodedTyVal::LTy(l) = item {
                            elems.push(l);
                        }
                    }
                    vals.push(DecodedTyVal::Ty(Ty::Tuple(elems)));
                }
                DecodeTyBuild::List => {
                    let Some(DecodedTyVal::LTy(elem)) = vals.pop() else {
                        unreachable!("stack balanced");
                    };
                    vals.push(DecodedTyVal::Ty(Ty::List(Box::new(elem))));
                }
                DecodeTyBuild::Map => {
                    let (Some(DecodedTyVal::LTy(val)), Some(DecodedTyVal::LTy(key))) =
                        (vals.pop(), vals.pop())
                    else {
                        unreachable!("stack balanced");
                    };
                    vals.push(DecodedTyVal::Ty(Ty::Map {
                        key: Box::new(key),
                        val: Box::new(val),
                    }));
                }
                DecodeTyBuild::Fn { n_params } => {
                    let (Some(DecodedTyVal::LTy(ret)), Some(DecodedTyVal::Tags(pc))) =
                        (vals.pop(), vals.pop())
                    else {
                        unreachable!("stack balanced");
                    };
                    let raw = vals.split_off(vals.len() - n_params);
                    let mut params = Vec::with_capacity(n_params);
                    for item in raw {
                        if let DecodedTyVal::LTy(l) = item {
                            params.push(l);
                        }
                    }
                    vals.push(DecodedTyVal::Ty(Ty::Fn {
                        params,
                        pc,
                        ret: Box::new(ret),
                    }));
                }
                DecodeTyBuild::LTy(ts_sexp) => {
                    let Some(DecodedTyVal::Ty(ty)) = vals.pop() else {
                        unreachable!("stack balanced");
                    };
                    vals.push(DecodedTyVal::LTy(LTy::new(ty, decode_tag_set(ts_sexp)?)));
                }
            },
        }
    }
    match vals.pop() {
        Some(res) => Ok(res),
        None => unreachable!("decode_ty_iter always produces one value"),
    }
}

fn decode_ty(s: &SExp) -> Result<Ty, WireError> {
    match decode_ty_iter(DecodeTyTask::Ty(s))? {
        DecodedTyVal::Ty(ty) => Ok(ty),
        _ => unreachable!("Ty task returns Ty"),
    }
}

fn decode_lty(s: &SExp) -> Result<LTy, WireError> {
    match decode_ty_iter(DecodeTyTask::LTy(s))? {
        DecodedTyVal::LTy(lty) => Ok(lty),
        _ => unreachable!("LTy task returns LTy"),
    }
}

// ---------------------------------------------------------------------------
// Literals, PrimOps, HostOps, RowExpr, Expr, Plan Serialization
// ---------------------------------------------------------------------------

fn encode_literal(lit: &Literal) -> SExp {
    match lit {
        Literal::Unit => SExp::List(vec![atom("lit-unit")]),
        Literal::Bool(b) => SExp::List(vec![atom("lit-bool"), encode_bool(*b)]),
        Literal::Int(n) => SExp::List(vec![atom("lit-int"), encode_int(n)]),
        Literal::Decimal(d) => SExp::List(vec![atom("lit-decimal"), encode_int(d)]),
        Literal::Float(f) => SExp::List(vec![atom("lit-float"), encode_nat(f.bits)]),
        Literal::Text(s) => SExp::List(vec![atom("lit-text"), SExp::Str(s.clone())]),
        Literal::Bytes(bs) => SExp::List(vec![
            atom("lit-bytes"),
            SExp::List(bs.iter().map(|&b| encode_nat(u64::from(b))).collect()),
        ]),
        Literal::Date(d) => SExp::List(vec![atom("lit-date"), encode_int(d)]),
        Literal::Timestamp(ts) => SExp::List(vec![atom("lit-timestamp"), encode_int(ts)]),
        Literal::Duration(dur) => SExp::List(vec![atom("lit-duration"), encode_int(dur)]),
        Literal::NoneLit(inner) => SExp::List(vec![atom("lit-none"), encode_ty(inner)]),
    }
}

fn decode_literal(s: &SExp) -> Result<Literal, WireError> {
    let xs = as_list(s)?;
    match xs {
        [SExp::Atom(t)] if t == "lit-unit" => Ok(Literal::Unit),
        [SExp::Atom(t), x] => match t.as_str() {
            "lit-bool" => Ok(Literal::Bool(decode_bool(x)?)),
            "lit-int" => Ok(Literal::Int(decode_int(x)?)),
            "lit-decimal" => Ok(Literal::Decimal(decode_int(x)?)),
            "lit-float" => Ok(Literal::Float(Float64::from_bits(decode_nat(x)?))),
            "lit-text" => Ok(Literal::Text(decode_str_only(x)?)),
            "lit-bytes" => {
                let ns = map_decode(as_list(x)?, decode_big_nat)?;
                let mut bs = Vec::with_capacity(ns.len());
                for n in ns {
                    if let Some(b) = n.to_u64().and_then(|v| u8::try_from(v).ok()) {
                        bs.push(b);
                    } else {
                        return err("byte value out of 0..255 range");
                    }
                }
                Ok(Literal::Bytes(bs))
            }
            "lit-date" => Ok(Literal::Date(decode_int(x)?)),
            "lit-timestamp" => Ok(Literal::Timestamp(decode_int(x)?)),
            "lit-duration" => Ok(Literal::Duration(decode_int(x)?)),
            "lit-none" => Ok(Literal::NoneLit(decode_ty(x)?)),
            _ => err("invalid Literal S-expression"),
        },
        _ => err("invalid Literal S-expression"),
    }
}

fn encode_chart_kind(k: ChartKind) -> SExp {
    match k {
        ChartKind::Bar => atom("bar"),
        ChartKind::Line => atom("line"),
        ChartKind::Scatter => atom("scatter"),
        ChartKind::Histogram => atom("histogram"),
        ChartKind::Heatmap => atom("heatmap"),
    }
}

fn decode_chart_kind(s: &SExp) -> Result<ChartKind, WireError> {
    match s {
        SExp::Atom(a) => match a.as_str() {
            "bar" => Ok(ChartKind::Bar),
            "line" => Ok(ChartKind::Line),
            "scatter" => Ok(ChartKind::Scatter),
            "histogram" => Ok(ChartKind::Histogram),
            "heatmap" => Ok(ChartKind::Heatmap),
            _ => err("invalid chart kind"),
        },
        _ => err("invalid chart kind"),
    }
}

fn encode_prim_op(op: &PrimOp) -> SExp {
    match op {
        PrimOp::SomeVal(t) => SExp::List(vec![atom("some-val"), encode_ty(t)]),
        PrimOp::IsSome => atom("is-some"),
        PrimOp::IsNone => atom("is-none"),
        PrimOp::UnwrapOr => atom("unwrap-or"),
        PrimOp::UnwrapBang => atom("unwrap-bang"),
        PrimOp::OkVal(t) => SExp::List(vec![atom("ok-val"), encode_ty(t)]),
        PrimOp::ErrVal(t) => SExp::List(vec![atom("err-val"), encode_ty(t)]),
        PrimOp::AddInt => atom("add-int"),
        PrimOp::SubInt => atom("sub-int"),
        PrimOp::MulInt => atom("mul-int"),
        PrimOp::DivInt => atom("div-int"),
        PrimOp::ModInt => atom("mod-int"),
        PrimOp::NegInt => atom("neg-int"),
        PrimOp::AddDec => atom("add-dec"),
        PrimOp::SubDec => atom("sub-dec"),
        PrimOp::MulDec => atom("mul-dec"),
        PrimOp::DivDec => atom("div-dec"),
        PrimOp::NegDec => atom("neg-dec"),
        PrimOp::IntToDec => atom("int-to-dec"),
        PrimOp::BoolToDec => atom("bool-to-dec"),
        PrimOp::Eq => atom("eq"),
        PrimOp::Ne => atom("ne"),
        PrimOp::Lt => atom("lt"),
        PrimOp::Le => atom("le"),
        PrimOp::Gt => atom("gt"),
        PrimOp::Ge => atom("ge"),
        PrimOp::NotBool => atom("not-bool"),
        PrimOp::AndBool => atom("and-bool"),
        PrimOp::OrBool => atom("or-bool"),
        PrimOp::ConcatText => atom("concat-text"),
        PrimOp::TrimText => atom("trim-text"),
        PrimOp::LowerAsciiText => atom("lower-ascii-text"),
        PrimOp::ContainsText => atom("contains-text"),
        PrimOp::EmptyText => atom("empty-text"),
        PrimOp::IntToText => atom("int-to-text"),
        PrimOp::DecToText => atom("dec-to-text"),
        PrimOp::DateTruncMonth => atom("date-trunc-month"),
        PrimOp::AddDuration => atom("add-duration"),
        PrimOp::DiffTimestamp => atom("diff-timestamp"),
        PrimOp::ListLit(el) => SExp::List(vec![atom("list-lit"), encode_lty(el)]),
        PrimOp::ListLen => atom("list-len"),
        PrimOp::ListEmpty => atom("list-empty"),
        PrimOp::ListAppend => atom("list-append"),
        PrimOp::ListConcat => atom("list-concat"),
        PrimOp::MapLit { key_lty, val_lty } => SExp::List(vec![
            atom("map-lit"),
            encode_lty(key_lty),
            encode_lty(val_lty),
        ]),
        PrimOp::MapGet => atom("map-get"),
        PrimOp::TableCount => atom("table-count"),
        PrimOp::TableConcat(s) => SExp::List(vec![atom("table-concat"), encode_table_ty(s)]),
        PrimOp::TableProfile => atom("table-profile"),
        PrimOp::StatsCorr { col_x, col_y } => SExp::List(vec![
            atom("stats-corr"),
            encode_ident(col_x),
            encode_ident(col_y),
        ]),
        PrimOp::StatsLinReg { col_x, col_y } => SExp::List(vec![
            atom("stats-linreg"),
            encode_ident(col_x),
            encode_ident(col_y),
        ]),
        PrimOp::StatsTTest { col_x, col_y } => SExp::List(vec![
            atom("stats-ttest"),
            encode_ident(col_x),
            encode_ident(col_y),
        ]),
        PrimOp::ChartMake { kind, cols, title } => SExp::List(vec![
            atom("chart-make"),
            encode_chart_kind(*kind),
            SExp::List(cols.iter().map(|c| encode_ident(c)).collect()),
            SExp::Str(title.clone()),
        ]),
        PrimOp::ReportNew => atom("report-new"),
        PrimOp::ReportAddSummary => atom("report-add-summary"),
        PrimOp::ReportAddChart => atom("report-add-chart"),
        PrimOp::ReportAddTable => atom("report-add-table"),
    }
}

fn decode_prim_op(s: &SExp) -> Result<PrimOp, WireError> {
    match s {
        SExp::Atom(a) => match a.as_str() {
            "is-some" => Ok(PrimOp::IsSome),
            "is-none" => Ok(PrimOp::IsNone),
            "unwrap-or" => Ok(PrimOp::UnwrapOr),
            "unwrap-bang" => Ok(PrimOp::UnwrapBang),
            "add-int" => Ok(PrimOp::AddInt),
            "sub-int" => Ok(PrimOp::SubInt),
            "mul-int" => Ok(PrimOp::MulInt),
            "div-int" => Ok(PrimOp::DivInt),
            "mod-int" => Ok(PrimOp::ModInt),
            "neg-int" => Ok(PrimOp::NegInt),
            "add-dec" => Ok(PrimOp::AddDec),
            "sub-dec" => Ok(PrimOp::SubDec),
            "mul-dec" => Ok(PrimOp::MulDec),
            "div-dec" => Ok(PrimOp::DivDec),
            "neg-dec" => Ok(PrimOp::NegDec),
            "int-to-dec" => Ok(PrimOp::IntToDec),
            "bool-to-dec" => Ok(PrimOp::BoolToDec),
            "eq" => Ok(PrimOp::Eq),
            "ne" => Ok(PrimOp::Ne),
            "lt" => Ok(PrimOp::Lt),
            "le" => Ok(PrimOp::Le),
            "gt" => Ok(PrimOp::Gt),
            "ge" => Ok(PrimOp::Ge),
            "not-bool" => Ok(PrimOp::NotBool),
            "and-bool" => Ok(PrimOp::AndBool),
            "or-bool" => Ok(PrimOp::OrBool),
            "concat-text" => Ok(PrimOp::ConcatText),
            "trim-text" => Ok(PrimOp::TrimText),
            "lower-ascii-text" => Ok(PrimOp::LowerAsciiText),
            "contains-text" => Ok(PrimOp::ContainsText),
            "empty-text" => Ok(PrimOp::EmptyText),
            "int-to-text" => Ok(PrimOp::IntToText),
            "dec-to-text" => Ok(PrimOp::DecToText),
            "date-trunc-month" => Ok(PrimOp::DateTruncMonth),
            "add-duration" => Ok(PrimOp::AddDuration),
            "diff-timestamp" => Ok(PrimOp::DiffTimestamp),
            "list-len" => Ok(PrimOp::ListLen),
            "list-empty" => Ok(PrimOp::ListEmpty),
            "list-append" => Ok(PrimOp::ListAppend),
            "list-concat" => Ok(PrimOp::ListConcat),
            "map-get" => Ok(PrimOp::MapGet),
            "table-count" => Ok(PrimOp::TableCount),
            "table-profile" => Ok(PrimOp::TableProfile),
            "report-new" => Ok(PrimOp::ReportNew),
            "report-add-summary" => Ok(PrimOp::ReportAddSummary),
            "report-add-chart" => Ok(PrimOp::ReportAddChart),
            "report-add-table" => Ok(PrimOp::ReportAddTable),
            _ => err("invalid PrimOp"),
        },
        SExp::List(xs) => match xs.as_slice() {
            [SExp::Atom(t), x] => match t.as_str() {
                "some-val" => Ok(PrimOp::SomeVal(decode_ty(x)?)),
                "ok-val" => Ok(PrimOp::OkVal(decode_ty(x)?)),
                "err-val" => Ok(PrimOp::ErrVal(decode_ty(x)?)),
                "list-lit" => Ok(PrimOp::ListLit(decode_lty(x)?)),
                "table-concat" => Ok(PrimOp::TableConcat(decode_table_ty(x)?)),
                _ => err("invalid PrimOp"),
            },
            [SExp::Atom(t), a, b] => match t.as_str() {
                "map-lit" => Ok(PrimOp::MapLit {
                    key_lty: decode_lty(a)?,
                    val_lty: decode_lty(b)?,
                }),
                "stats-corr" => Ok(PrimOp::StatsCorr {
                    col_x: decode_ident(a)?,
                    col_y: decode_ident(b)?,
                }),
                "stats-linreg" => Ok(PrimOp::StatsLinReg {
                    col_x: decode_ident(a)?,
                    col_y: decode_ident(b)?,
                }),
                "stats-ttest" => Ok(PrimOp::StatsTTest {
                    col_x: decode_ident(a)?,
                    col_y: decode_ident(b)?,
                }),
                _ => err("invalid PrimOp"),
            },
            [SExp::Atom(t), k, cs, title] if t == "chart-make" => Ok(PrimOp::ChartMake {
                kind: decode_chart_kind(k)?,
                cols: map_decode(as_list(cs)?, decode_ident)?,
                title: decode_str_only(title)?,
            }),
            _ => err("invalid PrimOp"),
        },
        SExp::Str(_) => err("invalid PrimOp"),
    }
}

fn encode_host_op(op: &HostOp) -> SExp {
    match op {
        HostOp::ArgsGet => atom("args-get"),
        HostOp::ClockNow => atom("clock-now"),
        HostOp::ConsolePrint => atom("console-print"),
        HostOp::ConsoleError => atom("console-error"),
        HostOp::ConsolePrintTable => atom("console-print-table"),
        HostOp::ReadCsv(s) => SExp::List(vec![atom("read-csv"), encode_ident(s)]),
        HostOp::WriteFile => atom("write-file"),
        HostOp::WriteReportHtml => atom("write-report-html"),
        HostOp::WriteTable => atom("write-table-op"),
        HostOp::DeclassifyApprove(ts) => {
            SExp::List(vec![atom("declassify-approve"), encode_tag_set(ts)])
        }
        HostOp::RawSqlQuery { db, out_schema } => SExp::List(vec![
            atom("raw-sql-query"),
            encode_ident(db),
            encode_table_ty(out_schema),
        ]),
        HostOp::HttpsGetJson => atom("https-get-json"),
        HostOp::ReadParquet(s) => SExp::List(vec![atom("read-parquet"), encode_table_ty(s)]),
        HostOp::WriteParquet => atom("write-parquet"),
        HostOp::WriteXlsx => atom("write-xlsx"),
        HostOp::FakeConsole(allows) => {
            SExp::List(vec![atom("fake-console"), encode_tag_set(allows)])
        }
        HostOp::FakeFiles(allows) => SExp::List(vec![atom("fake-files"), encode_tag_set(allows)]),
        HostOp::FakeDB(db) => SExp::List(vec![atom("fake-db"), encode_ident(db)]),
        HostOp::FakeHttps { host, allows } => SExp::List(vec![
            atom("fake-https"),
            SExp::Str(host.clone()),
            encode_tag_set(allows),
        ]),
        HostOp::FakeSecret(name) => SExp::List(vec![atom("fake-secret"), SExp::Str(name.clone())]),
    }
}

fn decode_host_op(s: &SExp) -> Result<HostOp, WireError> {
    match s {
        SExp::Atom(a) => match a.as_str() {
            "args-get" => Ok(HostOp::ArgsGet),
            "clock-now" => Ok(HostOp::ClockNow),
            "console-print" => Ok(HostOp::ConsolePrint),
            "console-error" => Ok(HostOp::ConsoleError),
            "console-print-table" => Ok(HostOp::ConsolePrintTable),
            "write-file" => Ok(HostOp::WriteFile),
            "write-report-html" => Ok(HostOp::WriteReportHtml),
            "write-table-op" => Ok(HostOp::WriteTable),
            "https-get-json" => Ok(HostOp::HttpsGetJson),
            "write-parquet" => Ok(HostOp::WriteParquet),
            "write-xlsx" => Ok(HostOp::WriteXlsx),
            _ => err("invalid HostOp"),
        },
        SExp::List(xs) => match xs.as_slice() {
            [SExp::Atom(t), x] => match t.as_str() {
                "read-csv" => Ok(HostOp::ReadCsv(decode_ident(x)?)),
                "declassify-approve" => Ok(HostOp::DeclassifyApprove(decode_tag_set(x)?)),
                "read-parquet" => Ok(HostOp::ReadParquet(decode_table_ty(x)?)),
                "fake-console" => Ok(HostOp::FakeConsole(decode_tag_set(x)?)),
                "fake-files" => Ok(HostOp::FakeFiles(decode_tag_set(x)?)),
                "fake-db" => Ok(HostOp::FakeDB(decode_ident(x)?)),
                "fake-secret" => Ok(HostOp::FakeSecret(decode_str_only(x)?)),
                _ => err("invalid HostOp"),
            },
            [SExp::Atom(t), a, b] => match t.as_str() {
                "raw-sql-query" => Ok(HostOp::RawSqlQuery {
                    db: decode_ident(a)?,
                    out_schema: decode_table_ty(b)?,
                }),
                "fake-https" => Ok(HostOp::FakeHttps {
                    host: decode_str_only(a)?,
                    allows: decode_tag_set(b)?,
                }),
                _ => err("invalid HostOp"),
            },
            _ => err("invalid HostOp"),
        },
        SExp::Str(_) => err("invalid HostOp"),
    }
}

fn encode_bug_kind(k: BugKind) -> SExp {
    match k {
        BugKind::IntOverflow => atom("int-overflow"),
        BugKind::DecimalOverflow => atom("decimal-overflow"),
        BugKind::DivByZero => atom("div-by-zero"),
        BugKind::UnwrapNone => atom("unwrap-none"),
        BugKind::JoinCardinality => atom("join-cardinality"),
        BugKind::PromiseViolation => atom("promise-violation"),
        BugKind::SchemaConstraint => atom("schema-constraint"),
        BugKind::ExportGateDenied => atom("export-gate-denied"),
        BugKind::OutsideBoundary => atom("outside-boundary"),
        BugKind::UserStop => atom("user-stop"),
    }
}

fn decode_bug_kind(s: &SExp) -> Result<BugKind, WireError> {
    match s {
        SExp::Atom(a) => match a.as_str() {
            "int-overflow" => Ok(BugKind::IntOverflow),
            "decimal-overflow" => Ok(BugKind::DecimalOverflow),
            "div-by-zero" => Ok(BugKind::DivByZero),
            "unwrap-none" => Ok(BugKind::UnwrapNone),
            "join-cardinality" => Ok(BugKind::JoinCardinality),
            "promise-violation" => Ok(BugKind::PromiseViolation),
            "schema-constraint" => Ok(BugKind::SchemaConstraint),
            "export-gate-denied" => Ok(BugKind::ExportGateDenied),
            "outside-boundary" => Ok(BugKind::OutsideBoundary),
            "user-stop" => Ok(BugKind::UserStop),
            _ => err("invalid BugKind"),
        },
        _ => err("invalid BugKind"),
    }
}

enum EncodeRowBuild<'a> {
    Prim(&'a PrimOp, usize),
    IfE,
    Coalesce,
    CallPure(&'a Ident, usize),
}

enum EncodeRowTask<'a> {
    Node(&'a RowExpr),
    Finish(EncodeRowBuild<'a>),
}

fn encode_row_expr(re: &RowExpr) -> SExp {
    let mut tasks = vec![EncodeRowTask::Node(re)];
    let mut vals: Vec<SExp> = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            EncodeRowTask::Node(node) => match node {
                RowExpr::Lit(v) => vals.push(SExp::List(vec![atom("re-lit"), encode_literal(v)])),
                RowExpr::Col(n) => vals.push(SExp::List(vec![atom("re-col"), encode_ident(n)])),
                RowExpr::OuterVar(n) => {
                    vals.push(SExp::List(vec![atom("re-outer"), encode_ident(n)]));
                }
                RowExpr::ConstRef(n) => {
                    vals.push(SExp::List(vec![atom("re-const"), encode_ident(n)]));
                }
                RowExpr::Prim { op, args } => {
                    tasks.push(EncodeRowTask::Finish(EncodeRowBuild::Prim(op, args.len())));
                    for a in args.iter().rev() {
                        tasks.push(EncodeRowTask::Node(a));
                    }
                }
                RowExpr::IfE {
                    cond,
                    then_br,
                    else_br,
                } => {
                    tasks.push(EncodeRowTask::Finish(EncodeRowBuild::IfE));
                    tasks.push(EncodeRowTask::Node(else_br));
                    tasks.push(EncodeRowTask::Node(then_br));
                    tasks.push(EncodeRowTask::Node(cond));
                }
                RowExpr::Coalesce {
                    opt_expr,
                    default_expr,
                } => {
                    tasks.push(EncodeRowTask::Finish(EncodeRowBuild::Coalesce));
                    tasks.push(EncodeRowTask::Node(default_expr));
                    tasks.push(EncodeRowTask::Node(opt_expr));
                }
                RowExpr::CallPure { fn_name, args } => {
                    tasks.push(EncodeRowTask::Finish(EncodeRowBuild::CallPure(
                        fn_name,
                        args.len(),
                    )));
                    for a in args.iter().rev() {
                        tasks.push(EncodeRowTask::Node(a));
                    }
                }
            },
            EncodeRowTask::Finish(build) => match build {
                EncodeRowBuild::Prim(op, n) => {
                    let args = vals.split_off(vals.len() - n);
                    vals.push(SExp::List(vec![
                        atom("re-prim"),
                        encode_prim_op(op),
                        SExp::List(args),
                    ]));
                }
                EncodeRowBuild::IfE => {
                    let (Some(el), Some(th), Some(c)) = (vals.pop(), vals.pop(), vals.pop()) else {
                        unreachable!("stack balanced");
                    };
                    vals.push(SExp::List(vec![atom("re-if"), c, th, el]));
                }
                EncodeRowBuild::Coalesce => {
                    let (Some(d), Some(o)) = (vals.pop(), vals.pop()) else {
                        unreachable!("stack balanced");
                    };
                    vals.push(SExp::List(vec![atom("re-coalesce"), o, d]));
                }
                EncodeRowBuild::CallPure(fn_name, n) => {
                    let args = vals.split_off(vals.len() - n);
                    vals.push(SExp::List(vec![
                        atom("re-call"),
                        encode_ident(fn_name),
                        SExp::List(args),
                    ]));
                }
            },
        }
    }
    match vals.pop() {
        Some(res) => res,
        None => unreachable!("encode_row_expr always produces one SExp"),
    }
}

enum DecodeRowBuild {
    Prim(Box<PrimOp>, usize),
    IfE,
    Coalesce,
    CallPure(Ident, usize),
}

enum DecodeRowTask<'a> {
    Node(&'a SExp),
    Finish(DecodeRowBuild),
}

fn decode_row_expr(s: &SExp) -> Result<RowExpr, WireError> {
    let mut tasks = vec![DecodeRowTask::Node(s)];
    let mut vals: Vec<RowExpr> = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            DecodeRowTask::Node(cur) => {
                let xs = as_list(cur)?;
                match xs {
                    [SExp::Atom(t), x] => match t.as_str() {
                        "re-lit" => vals.push(RowExpr::Lit(decode_literal(x)?)),
                        "re-col" => vals.push(RowExpr::Col(decode_ident(x)?)),
                        "re-outer" => vals.push(RowExpr::OuterVar(decode_ident(x)?)),
                        "re-const" => vals.push(RowExpr::ConstRef(decode_ident(x)?)),
                        _ => return err("invalid RowExpr"),
                    },
                    [SExp::Atom(t), a, b] => match t.as_str() {
                        "re-prim" => {
                            let op = decode_prim_op(a)?;
                            let args = as_list(b)?;
                            tasks.push(DecodeRowTask::Finish(DecodeRowBuild::Prim(
                                Box::new(op),
                                args.len(),
                            )));
                            for arg in args.iter().rev() {
                                tasks.push(DecodeRowTask::Node(arg));
                            }
                        }
                        "re-coalesce" => {
                            tasks.push(DecodeRowTask::Finish(DecodeRowBuild::Coalesce));
                            tasks.push(DecodeRowTask::Node(b));
                            tasks.push(DecodeRowTask::Node(a));
                        }
                        "re-call" => {
                            let fn_name = decode_ident(a)?;
                            let args = as_list(b)?;
                            tasks.push(DecodeRowTask::Finish(DecodeRowBuild::CallPure(
                                fn_name,
                                args.len(),
                            )));
                            for arg in args.iter().rev() {
                                tasks.push(DecodeRowTask::Node(arg));
                            }
                        }
                        _ => return err("invalid RowExpr"),
                    },
                    [SExp::Atom(t), c, th, el] if t == "re-if" => {
                        tasks.push(DecodeRowTask::Finish(DecodeRowBuild::IfE));
                        tasks.push(DecodeRowTask::Node(el));
                        tasks.push(DecodeRowTask::Node(th));
                        tasks.push(DecodeRowTask::Node(c));
                    }
                    _ => return err("invalid RowExpr"),
                }
            }
            DecodeRowTask::Finish(build) => match build {
                DecodeRowBuild::Prim(op, n) => {
                    let args = vals.split_off(vals.len() - n);
                    vals.push(RowExpr::Prim { op: *op, args });
                }
                DecodeRowBuild::IfE => {
                    let (Some(el), Some(th), Some(c)) = (vals.pop(), vals.pop(), vals.pop()) else {
                        unreachable!("stack balanced");
                    };
                    vals.push(RowExpr::IfE {
                        cond: Box::new(c),
                        then_br: Box::new(th),
                        else_br: Box::new(el),
                    });
                }
                DecodeRowBuild::Coalesce => {
                    let (Some(d), Some(o)) = (vals.pop(), vals.pop()) else {
                        unreachable!("stack balanced");
                    };
                    vals.push(RowExpr::Coalesce {
                        opt_expr: Box::new(o),
                        default_expr: Box::new(d),
                    });
                }
                DecodeRowBuild::CallPure(fn_name, n) => {
                    let args = vals.split_off(vals.len() - n);
                    vals.push(RowExpr::CallPure { fn_name, args });
                }
            },
        }
    }
    match vals.pop() {
        Some(res) => Ok(res),
        None => unreachable!("decode_row_expr always produces one RowExpr"),
    }
}

fn encode_derive_item(item: &DeriveItem) -> SExp {
    match item {
        DeriveItem::ColExpr { name, expr } => SExp::List(vec![
            atom("col-expr"),
            encode_ident(name),
            encode_row_expr(expr),
        ]),
        DeriveItem::BucketCol {
            name,
            source,
            cuts,
            labels,
        } => SExp::List(vec![
            atom("bucket-col"),
            encode_ident(name),
            encode_ident(source),
            SExp::List(cuts.iter().map(encode_literal).collect()),
            SExp::List(labels.iter().cloned().map(SExp::Str).collect()),
        ]),
    }
}

fn decode_derive_item(s: &SExp) -> Result<DeriveItem, WireError> {
    let xs = as_list(s)?;
    match xs {
        [SExp::Atom(t), n, re] if t == "col-expr" => Ok(DeriveItem::ColExpr {
            name: decode_ident(n)?,
            expr: Box::new(decode_row_expr(re)?),
        }),
        [SExp::Atom(t), n, src, cuts, lbls] if t == "bucket-col" => Ok(DeriveItem::BucketCol {
            name: decode_ident(n)?,
            source: decode_ident(src)?,
            cuts: map_decode(as_list(cuts)?, decode_literal)?,
            labels: map_decode(as_list(lbls)?, decode_str_only)?,
        }),
        _ => err("invalid DeriveItem"),
    }
}

fn encode_sort_dir(d: SortDir) -> SExp {
    match d {
        SortDir::Asc => atom("asc"),
        SortDir::Desc => atom("desc"),
    }
}

fn decode_sort_dir(s: &SExp) -> Result<SortDir, WireError> {
    match s {
        SExp::Atom(a) if a == "asc" => Ok(SortDir::Asc),
        SExp::Atom(a) if a == "desc" => Ok(SortDir::Desc),
        _ => err("invalid SortDir"),
    }
}

fn encode_join_kind(k: JoinKind) -> SExp {
    match k {
        JoinKind::InnerOne => atom("inner-one"),
        JoinKind::InnerManyToOne => atom("inner-many-to-one"),
        JoinKind::InnerMany => atom("inner-many"),
        JoinKind::LeftOne => atom("left-one"),
        JoinKind::LeftManyToOne => atom("left-many-to-one"),
        JoinKind::Semi => atom("semi"),
        JoinKind::Anti => atom("anti"),
    }
}

fn decode_join_kind(s: &SExp) -> Result<JoinKind, WireError> {
    match s {
        SExp::Atom(a) => match a.as_str() {
            "inner-one" => Ok(JoinKind::InnerOne),
            "inner-many-to-one" => Ok(JoinKind::InnerManyToOne),
            "inner-many" => Ok(JoinKind::InnerMany),
            "left-one" => Ok(JoinKind::LeftOne),
            "left-many-to-one" => Ok(JoinKind::LeftManyToOne),
            "semi" => Ok(JoinKind::Semi),
            "anti" => Ok(JoinKind::Anti),
            _ => err("invalid JoinKind"),
        },
        _ => err("invalid JoinKind"),
    }
}

fn encode_join_on(on: &JoinOn) -> SExp {
    match on {
        JoinOn::SameKeys(ks) => SExp::List(vec![
            atom("same-keys"),
            SExp::List(ks.iter().map(|k| encode_ident(k)).collect()),
        ]),
        JoinOn::Pairs(ps) => SExp::List(vec![
            atom("key-pairs"),
            SExp::List(
                ps.iter()
                    .map(|(l, r)| SExp::List(vec![encode_ident(l), encode_ident(r)]))
                    .collect(),
            ),
        ]),
    }
}

fn decode_join_on(s: &SExp) -> Result<JoinOn, WireError> {
    let xs = as_list(s)?;
    match xs {
        [SExp::Atom(t), ks] if t == "same-keys" => {
            Ok(JoinOn::SameKeys(map_decode(as_list(ks)?, decode_ident)?))
        }
        [SExp::Atom(t), ps] if t == "key-pairs" => {
            Ok(JoinOn::Pairs(map_decode(as_list(ps)?, |pair| {
                let [l, r] = as_list(pair)? else {
                    return err("expected key pair");
                };
                Ok((decode_ident(l)?, decode_ident(r)?))
            })?))
        }
        _ => err("invalid JoinOn"),
    }
}

fn encode_agg_op(op: AggOp) -> SExp {
    match op {
        AggOp::Count => atom("count"),
        AggOp::CountDistinct => atom("count-distinct"),
        AggOp::Sum => atom("sum"),
        AggOp::Mean => atom("mean"),
        AggOp::Median => atom("median"),
        AggOp::Stddev => atom("stddev"),
        AggOp::Variance => atom("variance"),
        AggOp::Percentile(p) => SExp::List(vec![atom("percentile"), encode_nat(p.bits)]),
        AggOp::Min => atom("min"),
        AggOp::Max => atom("max"),
        AggOp::First => atom("first"),
        AggOp::Last => atom("last"),
    }
}

fn decode_agg_op(s: &SExp) -> Result<AggOp, WireError> {
    match s {
        SExp::Atom(a) => match a.as_str() {
            "count" => Ok(AggOp::Count),
            "count-distinct" => Ok(AggOp::CountDistinct),
            "sum" => Ok(AggOp::Sum),
            "mean" => Ok(AggOp::Mean),
            "median" => Ok(AggOp::Median),
            "stddev" => Ok(AggOp::Stddev),
            "variance" => Ok(AggOp::Variance),
            "min" => Ok(AggOp::Min),
            "max" => Ok(AggOp::Max),
            "first" => Ok(AggOp::First),
            "last" => Ok(AggOp::Last),
            _ => err("invalid AggOp"),
        },
        SExp::List(xs) => match xs.as_slice() {
            [SExp::Atom(t), b] if t == "percentile" => {
                Ok(AggOp::Percentile(Float64::from_bits(decode_nat(b)?)))
            }
            _ => err("invalid AggOp"),
        },
        SExp::Str(_) => err("invalid AggOp"),
    }
}

fn encode_agg_item(a: &AggItem) -> SExp {
    SExp::List(vec![
        atom("agg"),
        encode_ident(&a.name),
        encode_agg_op(a.op),
        encode_opt(&a.arg, encode_row_expr),
    ])
}

fn decode_agg_item(s: &SExp) -> Result<AggItem, WireError> {
    let [SExp::Atom(t), n, op, arg] = as_list(s)? else {
        return err("invalid AggItem");
    };
    if t != "agg" {
        return err("invalid AggItem");
    }
    Ok(AggItem {
        name: decode_ident(n)?,
        op: decode_agg_op(op)?,
        arg: decode_opt(arg, decode_row_expr)?,
    })
}

fn encode_suppress_mode(m: SuppressMode) -> SExp {
    match m {
        SuppressMode::Drop => atom("drop"),
        SuppressMode::MaskComplementary => atom("mask-complementary"),
    }
}

fn decode_suppress_mode(s: &SExp) -> Result<SuppressMode, WireError> {
    match s {
        SExp::Atom(a) if a == "drop" => Ok(SuppressMode::Drop),
        SExp::Atom(a) if a == "mask-complementary" => Ok(SuppressMode::MaskComplementary),
        _ => err("invalid SuppressMode"),
    }
}

fn encode_window_fn(w: &WindowFn) -> SExp {
    match w {
        WindowFn::Lag { col, offset } => {
            SExp::List(vec![atom("lag"), encode_ident(col), encode_big_nat(offset)])
        }
        WindowFn::Lead { col, offset } => SExp::List(vec![
            atom("lead"),
            encode_ident(col),
            encode_big_nat(offset),
        ]),
        WindowFn::RowNumber => atom("row-number"),
        WindowFn::Rank { col } => SExp::List(vec![atom("rank"), encode_ident(col)]),
        WindowFn::RunningSum { col } => SExp::List(vec![atom("running-sum"), encode_ident(col)]),
        WindowFn::RollingMean { col, window_size } => SExp::List(vec![
            atom("rolling-mean"),
            encode_ident(col),
            encode_big_nat(window_size),
        ]),
    }
}

fn decode_window_fn(s: &SExp) -> Result<WindowFn, WireError> {
    match s {
        SExp::Atom(a) if a == "row-number" => Ok(WindowFn::RowNumber),
        SExp::List(xs) => match xs.as_slice() {
            [SExp::Atom(t), c, k] if t == "lag" => Ok(WindowFn::Lag {
                col: decode_ident(c)?,
                offset: decode_big_nat(k)?,
            }),
            [SExp::Atom(t), c, k] if t == "lead" => Ok(WindowFn::Lead {
                col: decode_ident(c)?,
                offset: decode_big_nat(k)?,
            }),
            [SExp::Atom(t), c] if t == "rank" => Ok(WindowFn::Rank {
                col: decode_ident(c)?,
            }),
            [SExp::Atom(t), c] if t == "running-sum" => Ok(WindowFn::RunningSum {
                col: decode_ident(c)?,
            }),
            [SExp::Atom(t), c, w] if t == "rolling-mean" => Ok(WindowFn::RollingMean {
                col: decode_ident(c)?,
                window_size: decode_big_nat(w)?,
            }),
            _ => err("invalid WindowFn"),
        },
        _ => err("invalid WindowFn"),
    }
}

fn encode_window_item(w: &WindowItem) -> SExp {
    SExp::List(vec![
        atom("win-item"),
        encode_ident(&w.name),
        encode_window_fn(&w.win_fn),
        SExp::List(w.over.iter().map(|c| encode_ident(c)).collect()),
        SExp::List(
            w.order
                .iter()
                .map(|(c, d)| SExp::List(vec![encode_ident(c), encode_sort_dir(*d)]))
                .collect(),
        ),
    ])
}

fn decode_window_item(s: &SExp) -> Result<WindowItem, WireError> {
    let [SExp::Atom(t), n, win_fn, ov, ord] = as_list(s)? else {
        return err("invalid WindowItem");
    };
    if t != "win-item" {
        return err("invalid WindowItem");
    }
    Ok(WindowItem {
        name: decode_ident(n)?,
        win_fn: decode_window_fn(win_fn)?,
        over: map_decode(as_list(ov)?, decode_ident)?,
        order: map_decode(as_list(ord)?, |pair| {
            let [c, d] = as_list(pair)? else {
                return err("expected (col dir)");
            };
            Ok((decode_ident(c)?, decode_sort_dir(d)?))
        })?,
    })
}

enum EncodeIrBuild<'a> {
    Let(&'a Ident, &'a LTy),
    If,
    Case(&'a [CaseArm]),
    Lam(&'a [(Ident, LTy)], &'a TagSet, &'a LTy),
    App(usize),
    Call(&'a Ident, usize),
    Join(&'a Ident, &'a [(Ident, LTy)]),
    Jump(&'a Ident, usize),
    Tuple(usize),
    Proj(&'a BigInt),
    Ctor(&'a Ident, &'a Ident, usize),
    Prim(&'a PrimOp, usize),
    Rel,
    Host(&'a HostOp, usize),
    StopSome(BugKind),
    Fail,
    SourceExpr,
    SourceDB(&'a Ident, &'a TableTy),
    PlanJoin(JoinKind, &'a JoinOn, &'a Option<(String, String)>),
    PlanUnion,
    PlanPseudonymize(&'a Ident),
    PlanUnary(&'a Plan),
}

enum EncodeIrTask<'a> {
    Expr(&'a Expr),
    Plan(&'a Plan),
    Finish(EncodeIrBuild<'a>),
}

fn encode_expr(expr: &Expr) -> SExp {
    let mut tasks = vec![EncodeIrTask::Expr(expr)];
    let mut vals: Vec<SExp> = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            EncodeIrTask::Expr(cur) => match cur {
                Expr::Lit(v) => vals.push(SExp::List(vec![atom("lit"), encode_literal(v)])),
                Expr::Var(n) => vals.push(SExp::List(vec![atom("var"), encode_ident(n)])),
                Expr::ConstRef(n) => {
                    vals.push(SExp::List(vec![atom("const-ref"), encode_ident(n)]));
                }
                Expr::TableLit { schema, rows } => vals.push(SExp::List(vec![
                    atom("table-lit"),
                    encode_table_ty(schema),
                    SExp::List(
                        rows.iter()
                            .map(|r| SExp::List(r.cells.iter().map(encode_literal).collect()))
                            .collect(),
                    ),
                ])),
                Expr::LetE {
                    name,
                    lty,
                    bound,
                    body,
                } => {
                    tasks.push(EncodeIrTask::Finish(EncodeIrBuild::Let(name, lty)));
                    tasks.push(EncodeIrTask::Expr(body));
                    tasks.push(EncodeIrTask::Expr(bound));
                }
                Expr::IfE {
                    cond,
                    then_br,
                    else_br,
                } => {
                    tasks.push(EncodeIrTask::Finish(EncodeIrBuild::If));
                    tasks.push(EncodeIrTask::Expr(else_br));
                    tasks.push(EncodeIrTask::Expr(then_br));
                    tasks.push(EncodeIrTask::Expr(cond));
                }
                Expr::CaseE { scrut, arms } => {
                    tasks.push(EncodeIrTask::Finish(EncodeIrBuild::Case(arms)));
                    for arm in arms.iter().rev() {
                        tasks.push(EncodeIrTask::Expr(&arm.body));
                    }
                    tasks.push(EncodeIrTask::Expr(scrut));
                }
                Expr::Lam {
                    params,
                    pc,
                    ret,
                    body,
                } => {
                    tasks.push(EncodeIrTask::Finish(EncodeIrBuild::Lam(params, pc, ret)));
                    tasks.push(EncodeIrTask::Expr(body));
                }
                Expr::App { fn_expr, args } => {
                    tasks.push(EncodeIrTask::Finish(EncodeIrBuild::App(args.len())));
                    for a in args.iter().rev() {
                        tasks.push(EncodeIrTask::Expr(a));
                    }
                    tasks.push(EncodeIrTask::Expr(fn_expr));
                }
                Expr::Call { fn_name, args } => {
                    tasks.push(EncodeIrTask::Finish(EncodeIrBuild::Call(
                        fn_name,
                        args.len(),
                    )));
                    for a in args.iter().rev() {
                        tasks.push(EncodeIrTask::Expr(a));
                    }
                }
                Expr::Join {
                    label,
                    params,
                    rhs,
                    body,
                } => {
                    tasks.push(EncodeIrTask::Finish(EncodeIrBuild::Join(label, params)));
                    tasks.push(EncodeIrTask::Expr(body));
                    tasks.push(EncodeIrTask::Expr(rhs));
                }
                Expr::Jump { label, args } => {
                    tasks.push(EncodeIrTask::Finish(EncodeIrBuild::Jump(label, args.len())));
                    for a in args.iter().rev() {
                        tasks.push(EncodeIrTask::Expr(a));
                    }
                }
                Expr::Tuple(es) => {
                    tasks.push(EncodeIrTask::Finish(EncodeIrBuild::Tuple(es.len())));
                    for e in es.iter().rev() {
                        tasks.push(EncodeIrTask::Expr(e));
                    }
                }
                Expr::Proj { tup, idx } => {
                    tasks.push(EncodeIrTask::Finish(EncodeIrBuild::Proj(idx)));
                    tasks.push(EncodeIrTask::Expr(tup));
                }
                Expr::Ctor {
                    type_name,
                    ctor_name,
                    args,
                } => {
                    tasks.push(EncodeIrTask::Finish(EncodeIrBuild::Ctor(
                        type_name,
                        ctor_name,
                        args.len(),
                    )));
                    for a in args.iter().rev() {
                        tasks.push(EncodeIrTask::Expr(a));
                    }
                }
                Expr::Prim { op, args } => {
                    tasks.push(EncodeIrTask::Finish(EncodeIrBuild::Prim(op, args.len())));
                    for a in args.iter().rev() {
                        tasks.push(EncodeIrTask::Expr(a));
                    }
                }
                Expr::Rel(plan) => {
                    tasks.push(EncodeIrTask::Finish(EncodeIrBuild::Rel));
                    tasks.push(EncodeIrTask::Plan(plan));
                }
                Expr::Host { op, args } => {
                    tasks.push(EncodeIrTask::Finish(EncodeIrBuild::Host(op, args.len())));
                    for a in args.iter().rev() {
                        tasks.push(EncodeIrTask::Expr(a));
                    }
                }
                Expr::Stop { kind, detail } => match detail {
                    None => vals.push(SExp::List(vec![
                        atom("stop"),
                        encode_bug_kind(*kind),
                        SExp::List(vec![atom("none")]),
                    ])),
                    Some(d) => {
                        tasks.push(EncodeIrTask::Finish(EncodeIrBuild::StopSome(*kind)));
                        tasks.push(EncodeIrTask::Expr(d));
                    }
                },
                Expr::Fail(m) => {
                    tasks.push(EncodeIrTask::Finish(EncodeIrBuild::Fail));
                    tasks.push(EncodeIrTask::Expr(m));
                }
            },
            EncodeIrTask::Plan(plan) => match plan {
                Plan::SourceExpr(e) => {
                    tasks.push(EncodeIrTask::Finish(EncodeIrBuild::SourceExpr));
                    tasks.push(EncodeIrTask::Expr(e));
                }
                Plan::SourceDB {
                    cap,
                    table_name,
                    schema,
                } => {
                    tasks.push(EncodeIrTask::Finish(EncodeIrBuild::SourceDB(
                        table_name, schema,
                    )));
                    tasks.push(EncodeIrTask::Expr(cap));
                }
                Plan::Join {
                    kind,
                    left,
                    right,
                    on,
                    suffixes,
                } => {
                    tasks.push(EncodeIrTask::Finish(EncodeIrBuild::PlanJoin(
                        *kind, on, suffixes,
                    )));
                    tasks.push(EncodeIrTask::Plan(right));
                    tasks.push(EncodeIrTask::Plan(left));
                }
                Plan::Union { left, right } => {
                    tasks.push(EncodeIrTask::Finish(EncodeIrBuild::PlanUnion));
                    tasks.push(EncodeIrTask::Plan(right));
                    tasks.push(EncodeIrTask::Plan(left));
                }
                Plan::Pseudonymize { input, col, secret } => {
                    tasks.push(EncodeIrTask::Finish(EncodeIrBuild::PlanPseudonymize(col)));
                    tasks.push(EncodeIrTask::Expr(secret));
                    tasks.push(EncodeIrTask::Plan(input));
                }
                Plan::Select { input, .. }
                | Plan::Drop { input, .. }
                | Plan::Rename { input, .. }
                | Plan::Derive { input, .. }
                | Plan::Filter { input, .. }
                | Plan::Distinct { input, .. }
                | Plan::Sort { input, .. }
                | Plan::Limit { input, .. }
                | Plan::GroupBy { input, .. }
                | Plan::Summarize { input, .. }
                | Plan::SuppressSmallGroups { input, .. }
                | Plan::Window { input, .. }
                | Plan::FillGaps { input, .. }
                | Plan::PivotWider { input, .. }
                | Plan::Crosstab { input, .. }
                | Plan::Redact { input, .. } => {
                    tasks.push(EncodeIrTask::Finish(EncodeIrBuild::PlanUnary(plan)));
                    tasks.push(EncodeIrTask::Plan(input));
                }
            },
            EncodeIrTask::Finish(build) => match build {
                EncodeIrBuild::Let(name, lty) => {
                    let (Some(body_s), Some(bound_s)) = (vals.pop(), vals.pop()) else {
                        unreachable!("stack balanced");
                    };
                    vals.push(SExp::List(vec![
                        atom("let"),
                        encode_ident(name),
                        encode_lty(lty),
                        bound_s,
                        body_s,
                    ]));
                }
                EncodeIrBuild::If => {
                    let (Some(else_s), Some(then_s), Some(cond_s)) =
                        (vals.pop(), vals.pop(), vals.pop())
                    else {
                        unreachable!("stack balanced");
                    };
                    vals.push(SExp::List(vec![atom("if"), cond_s, then_s, else_s]));
                }
                EncodeIrBuild::Case(arms) => {
                    let body_sexps = vals.split_off(vals.len() - arms.len());
                    let Some(scrut_s) = vals.pop() else {
                        unreachable!("stack balanced");
                    };
                    let arm_sexps = arms
                        .iter()
                        .zip(body_sexps)
                        .map(|(arm, body_s)| {
                            SExp::List(vec![
                                atom("arm"),
                                encode_ident(&arm.ctor),
                                SExp::List(arm.binders.iter().map(|b| encode_ident(b)).collect()),
                                body_s,
                            ])
                        })
                        .collect();
                    vals.push(SExp::List(vec![
                        atom("case"),
                        scrut_s,
                        SExp::List(arm_sexps),
                    ]));
                }
                EncodeIrBuild::Lam(params, pc, ret) => {
                    let Some(body_s) = vals.pop() else {
                        unreachable!("stack balanced");
                    };
                    vals.push(SExp::List(vec![
                        atom("lam"),
                        SExp::List(
                            params
                                .iter()
                                .map(|(n, l)| SExp::List(vec![encode_ident(n), encode_lty(l)]))
                                .collect(),
                        ),
                        encode_tag_set(pc),
                        encode_lty(ret),
                        body_s,
                    ]));
                }
                EncodeIrBuild::App(n) => {
                    let arg_sexps = vals.split_off(vals.len() - n);
                    let Some(fn_s) = vals.pop() else {
                        unreachable!("stack balanced");
                    };
                    vals.push(SExp::List(vec![atom("app"), fn_s, SExp::List(arg_sexps)]));
                }
                EncodeIrBuild::Call(fn_name, n) => {
                    let arg_sexps = vals.split_off(vals.len() - n);
                    vals.push(SExp::List(vec![
                        atom("call"),
                        encode_ident(fn_name),
                        SExp::List(arg_sexps),
                    ]));
                }
                EncodeIrBuild::Join(label, params) => {
                    let (Some(body_s), Some(rhs_s)) = (vals.pop(), vals.pop()) else {
                        unreachable!("stack balanced");
                    };
                    vals.push(SExp::List(vec![
                        atom("join-pt"),
                        encode_ident(label),
                        SExp::List(
                            params
                                .iter()
                                .map(|(n, l)| SExp::List(vec![encode_ident(n), encode_lty(l)]))
                                .collect(),
                        ),
                        rhs_s,
                        body_s,
                    ]));
                }
                EncodeIrBuild::Jump(label, n) => {
                    let arg_sexps = vals.split_off(vals.len() - n);
                    vals.push(SExp::List(vec![
                        atom("jump"),
                        encode_ident(label),
                        SExp::List(arg_sexps),
                    ]));
                }
                EncodeIrBuild::Tuple(n) => {
                    let elem_sexps = vals.split_off(vals.len() - n);
                    vals.push(SExp::List(vec![atom("tuple-val"), SExp::List(elem_sexps)]));
                }
                EncodeIrBuild::Proj(idx) => {
                    let Some(tup_s) = vals.pop() else {
                        unreachable!("stack balanced");
                    };
                    vals.push(SExp::List(vec![atom("proj"), tup_s, encode_big_nat(idx)]));
                }
                EncodeIrBuild::Ctor(type_name, ctor_name, n) => {
                    let arg_sexps = vals.split_off(vals.len() - n);
                    vals.push(SExp::List(vec![
                        atom("ctor"),
                        encode_ident(type_name),
                        encode_ident(ctor_name),
                        SExp::List(arg_sexps),
                    ]));
                }
                EncodeIrBuild::Prim(op, n) => {
                    let arg_sexps = vals.split_off(vals.len() - n);
                    vals.push(SExp::List(vec![
                        atom("prim"),
                        encode_prim_op(op),
                        SExp::List(arg_sexps),
                    ]));
                }
                EncodeIrBuild::Rel => {
                    let Some(plan_s) = vals.pop() else {
                        unreachable!("stack balanced");
                    };
                    vals.push(SExp::List(vec![atom("rel"), plan_s]));
                }
                EncodeIrBuild::Host(op, n) => {
                    let arg_sexps = vals.split_off(vals.len() - n);
                    vals.push(SExp::List(vec![
                        atom("host"),
                        encode_host_op(op),
                        SExp::List(arg_sexps),
                    ]));
                }
                EncodeIrBuild::StopSome(kind) => {
                    let Some(d_s) = vals.pop() else {
                        unreachable!("stack balanced");
                    };
                    vals.push(SExp::List(vec![
                        atom("stop"),
                        encode_bug_kind(kind),
                        SExp::List(vec![atom("some"), d_s]),
                    ]));
                }
                EncodeIrBuild::Fail => {
                    let Some(m_s) = vals.pop() else {
                        unreachable!("stack balanced");
                    };
                    vals.push(SExp::List(vec![atom("fail"), m_s]));
                }
                EncodeIrBuild::SourceExpr => {
                    let Some(e_s) = vals.pop() else {
                        unreachable!("stack balanced");
                    };
                    vals.push(SExp::List(vec![atom("source-expr"), e_s]));
                }
                EncodeIrBuild::SourceDB(table_name, schema) => {
                    let Some(cap_s) = vals.pop() else {
                        unreachable!("stack balanced");
                    };
                    vals.push(SExp::List(vec![
                        atom("source-db"),
                        cap_s,
                        encode_ident(table_name),
                        encode_table_ty(schema),
                    ]));
                }
                EncodeIrBuild::PlanJoin(kind, on, suffixes) => {
                    let (Some(r_s), Some(l_s)) = (vals.pop(), vals.pop()) else {
                        unreachable!("stack balanced");
                    };
                    vals.push(SExp::List(vec![
                        atom("join"),
                        encode_join_kind(kind),
                        l_s,
                        r_s,
                        encode_join_on(on),
                        encode_opt(suffixes, |(sl, sr)| {
                            SExp::List(vec![SExp::Str(sl.clone()), SExp::Str(sr.clone())])
                        }),
                    ]));
                }
                EncodeIrBuild::PlanUnion => {
                    let (Some(r_s), Some(l_s)) = (vals.pop(), vals.pop()) else {
                        unreachable!("stack balanced");
                    };
                    vals.push(SExp::List(vec![atom("union"), l_s, r_s]));
                }
                EncodeIrBuild::PlanPseudonymize(col) => {
                    let (Some(sec_s), Some(in_s)) = (vals.pop(), vals.pop()) else {
                        unreachable!("stack balanced");
                    };
                    vals.push(SExp::List(vec![
                        atom("pseudonymize"),
                        in_s,
                        encode_ident(col),
                        sec_s,
                    ]));
                }
                EncodeIrBuild::PlanUnary(stage) => {
                    let Some(in_s) = vals.pop() else {
                        unreachable!("stack balanced");
                    };
                    vals.push(encode_plan_unary_step(stage, in_s));
                }
            },
        }
    }
    match vals.pop() {
        Some(res) => res,
        None => unreachable!("encode_expr always produces one SExp"),
    }
}

fn encode_plan_unary_step(stage: &Plan, in_sexp: SExp) -> SExp {
    match stage {
        Plan::Select { cols, .. } => SExp::List(vec![
            atom("select"),
            in_sexp,
            SExp::List(cols.iter().map(|c| encode_ident(c)).collect()),
        ]),
        Plan::Drop { cols, .. } => SExp::List(vec![
            atom("drop"),
            in_sexp,
            SExp::List(cols.iter().map(|c| encode_ident(c)).collect()),
        ]),
        Plan::Rename { pairs, .. } => SExp::List(vec![
            atom("rename"),
            in_sexp,
            SExp::List(
                pairs
                    .iter()
                    .map(|(nw, ol)| SExp::List(vec![encode_ident(nw), encode_ident(ol)]))
                    .collect(),
            ),
        ]),
        Plan::Derive { items, .. } => SExp::List(vec![
            atom("derive"),
            in_sexp,
            SExp::List(items.iter().map(encode_derive_item).collect()),
        ]),
        Plan::Filter { pred, .. } => {
            SExp::List(vec![atom("filter"), in_sexp, encode_row_expr(pred)])
        }
        Plan::Distinct { cols, .. } => SExp::List(vec![
            atom("distinct"),
            in_sexp,
            SExp::List(cols.iter().map(|c| encode_ident(c)).collect()),
        ]),
        Plan::Sort { keys, .. } => SExp::List(vec![
            atom("sort"),
            in_sexp,
            SExp::List(
                keys.iter()
                    .map(|(c, d)| SExp::List(vec![encode_ident(c), encode_sort_dir(*d)]))
                    .collect(),
            ),
        ]),
        Plan::Limit { n, .. } => SExp::List(vec![atom("limit"), in_sexp, encode_big_nat(n)]),
        Plan::GroupBy { keys, .. } => SExp::List(vec![
            atom("group-by"),
            in_sexp,
            SExp::List(keys.iter().map(|c| encode_ident(c)).collect()),
        ]),
        Plan::Summarize {
            aggs, distinct_key, ..
        } => SExp::List(vec![
            atom("summarize"),
            in_sexp,
            SExp::List(aggs.iter().map(encode_agg_item).collect()),
            encode_opt(distinct_key, |dk| encode_ident(dk)),
        ]),
        Plan::SuppressSmallGroups {
            min_k,
            distinct_by,
            mode,
            ..
        } => SExp::List(vec![
            atom("suppress-small-groups"),
            in_sexp,
            encode_big_nat(min_k),
            encode_opt(distinct_by, |db| encode_ident(db)),
            encode_suppress_mode(*mode),
        ]),
        Plan::Window { items, .. } => SExp::List(vec![
            atom("window"),
            in_sexp,
            SExp::List(items.iter().map(encode_window_item).collect()),
        ]),
        Plan::FillGaps {
            col,
            step_micros,
            over,
            fill,
            ..
        } => SExp::List(vec![
            atom("fill-gaps"),
            in_sexp,
            encode_ident(col),
            encode_int(step_micros),
            SExp::List(over.iter().map(|c| encode_ident(c)).collect()),
            SExp::List(
                fill.iter()
                    .map(|(cn, lit)| SExp::List(vec![encode_ident(cn), encode_literal(lit)]))
                    .collect(),
            ),
        ]),
        Plan::PivotWider {
            names_from,
            values_from,
            static_cols,
            fill,
            ..
        } => SExp::List(vec![
            atom("pivot-wider"),
            in_sexp,
            encode_ident(names_from),
            encode_ident(values_from),
            SExp::List(static_cols.iter().map(|c| encode_ident(c)).collect()),
            encode_literal(fill),
        ]),
        Plan::Crosstab {
            rows_col,
            cols_col,
            values_col,
            fill,
            ..
        } => SExp::List(vec![
            atom("crosstab"),
            in_sexp,
            encode_ident(rows_col),
            encode_ident(cols_col),
            encode_ident(values_col),
            encode_literal(fill),
        ]),
        Plan::Redact {
            col, replacement, ..
        } => SExp::List(vec![
            atom("redact"),
            in_sexp,
            encode_ident(col),
            SExp::Str(replacement.clone()),
        ]),
        _ => unreachable!("non-unary plans handled by encode_expr"),
    }
}

enum DecodedIr {
    Expr(Expr),
    Plan(Plan),
    CaseArm(CaseArm),
}

impl DecodedIr {
    fn into_expr(self) -> Expr {
        match self {
            Self::Expr(e) => e,
            _ => unreachable!("expected DecodedIr::Expr"),
        }
    }

    fn into_plan(self) -> Plan {
        match self {
            Self::Plan(p) => p,
            _ => unreachable!("expected DecodedIr::Plan"),
        }
    }

    fn into_case_arm(self) -> CaseArm {
        match self {
            Self::CaseArm(a) => a,
            _ => unreachable!("expected DecodedIr::CaseArm"),
        }
    }
}

enum DecodeIrBuild<'a> {
    Let {
        name: Ident,
        lty: Box<LTy>,
    },
    If,
    Case(usize),
    CaseArm {
        ctor: Ident,
        binders: Vec<Ident>,
    },
    Lam {
        params: Vec<(Ident, LTy)>,
        pc: TagSet,
        ret: Box<LTy>,
    },
    App(usize),
    Call(Ident, usize),
    Join {
        label: Ident,
        params: Vec<(Ident, LTy)>,
    },
    Jump(Ident, usize),
    Tuple(usize),
    Proj(&'a SExp),
    Ctor(Ident, Ident, usize),
    Prim(Box<PrimOp>, usize),
    Rel,
    Host(Box<HostOp>, usize),
    StopSome(BugKind),
    Fail,
    SourceExpr,
    SourceDB(&'a SExp, &'a SExp),
    PlanJoin {
        kind: JoinKind,
        on: &'a SExp,
        suffixes: &'a SExp,
    },
    PlanUnion,
    PlanPseudonymize(Ident),
    PlanUnary(&'a [SExp]),
}

enum DecodeIrTask<'a> {
    Expr(&'a SExp),
    Plan(&'a SExp),
    CaseAfterScrut(&'a SExp),
    CaseArm(&'a SExp),
    AppAfterFn(&'a SExp),
    PseudoAfterInput(&'a SExp, &'a SExp),
    Finish(DecodeIrBuild<'a>),
}

fn decode_expr(s: &SExp) -> Result<Expr, WireError> {
    let mut tasks = vec![DecodeIrTask::Expr(s)];
    let mut vals: Vec<DecodedIr> = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            DecodeIrTask::Expr(cur) => {
                let xs = as_list(cur)?;
                match xs {
                    [SExp::Atom(t), x] => match t.as_str() {
                        "lit" => vals.push(DecodedIr::Expr(Expr::Lit(decode_literal(x)?))),
                        "var" => vals.push(DecodedIr::Expr(Expr::Var(decode_ident(x)?))),
                        "const-ref" => {
                            vals.push(DecodedIr::Expr(Expr::ConstRef(decode_ident(x)?)));
                        }
                        "tuple-val" => {
                            let es = as_list(x)?;
                            tasks.push(DecodeIrTask::Finish(DecodeIrBuild::Tuple(es.len())));
                            for e in es.iter().rev() {
                                tasks.push(DecodeIrTask::Expr(e));
                            }
                        }
                        "rel" => {
                            tasks.push(DecodeIrTask::Finish(DecodeIrBuild::Rel));
                            tasks.push(DecodeIrTask::Plan(x));
                        }
                        "fail" => {
                            tasks.push(DecodeIrTask::Finish(DecodeIrBuild::Fail));
                            tasks.push(DecodeIrTask::Expr(x));
                        }
                        _ => return err("invalid Expr S-expression"),
                    },
                    [SExp::Atom(t), a, b] => match t.as_str() {
                        "case" => {
                            tasks.push(DecodeIrTask::CaseAfterScrut(b));
                            tasks.push(DecodeIrTask::Expr(a));
                        }
                        "app" => {
                            tasks.push(DecodeIrTask::AppAfterFn(b));
                            tasks.push(DecodeIrTask::Expr(a));
                        }
                        "call" => {
                            let fn_name = decode_ident(a)?;
                            let arg_list = as_list(b)?;
                            tasks.push(DecodeIrTask::Finish(DecodeIrBuild::Call(
                                fn_name,
                                arg_list.len(),
                            )));
                            for arg in arg_list.iter().rev() {
                                tasks.push(DecodeIrTask::Expr(arg));
                            }
                        }
                        "jump" => {
                            let label = decode_ident(a)?;
                            let arg_list = as_list(b)?;
                            tasks.push(DecodeIrTask::Finish(DecodeIrBuild::Jump(
                                label,
                                arg_list.len(),
                            )));
                            for arg in arg_list.iter().rev() {
                                tasks.push(DecodeIrTask::Expr(arg));
                            }
                        }
                        "proj" => {
                            tasks.push(DecodeIrTask::Finish(DecodeIrBuild::Proj(b)));
                            tasks.push(DecodeIrTask::Expr(a));
                        }
                        "table-lit" => {
                            let schema = decode_table_ty(a)?;
                            let rows = map_decode(as_list(b)?, |row_s| {
                                Ok(RowLit {
                                    cells: map_decode(as_list(row_s)?, decode_literal)?,
                                })
                            })?;
                            vals.push(DecodedIr::Expr(Expr::TableLit { schema, rows }));
                        }
                        "prim" => {
                            let op = decode_prim_op(a)?;
                            let arg_list = as_list(b)?;
                            tasks.push(DecodeIrTask::Finish(DecodeIrBuild::Prim(
                                Box::new(op),
                                arg_list.len(),
                            )));
                            for arg in arg_list.iter().rev() {
                                tasks.push(DecodeIrTask::Expr(arg));
                            }
                        }
                        "host" => {
                            let op = decode_host_op(a)?;
                            let arg_list = as_list(b)?;
                            tasks.push(DecodeIrTask::Finish(DecodeIrBuild::Host(
                                Box::new(op),
                                arg_list.len(),
                            )));
                            for arg in arg_list.iter().rev() {
                                tasks.push(DecodeIrTask::Expr(arg));
                            }
                        }
                        "stop" => {
                            let kind = decode_bug_kind(a)?;
                            match b {
                                SExp::List(opt_xs) => match opt_xs.as_slice() {
                                    [SExp::Atom(tag)] if tag == "none" => {
                                        vals.push(DecodedIr::Expr(Expr::Stop {
                                            kind,
                                            detail: None,
                                        }));
                                    }
                                    [SExp::Atom(tag), d] if tag == "some" => {
                                        tasks.push(DecodeIrTask::Finish(DecodeIrBuild::StopSome(
                                            kind,
                                        )));
                                        tasks.push(DecodeIrTask::Expr(d));
                                    }
                                    _ => return err("expected (none) or (some ...)"),
                                },
                                _ => return err("expected (none) or (some ...)"),
                            }
                        }
                        _ => return err("invalid Expr S-expression"),
                    },
                    [SExp::Atom(t), a, b, c] => match t.as_str() {
                        "if" => {
                            tasks.push(DecodeIrTask::Finish(DecodeIrBuild::If));
                            tasks.push(DecodeIrTask::Expr(c));
                            tasks.push(DecodeIrTask::Expr(b));
                            tasks.push(DecodeIrTask::Expr(a));
                        }
                        "ctor" => {
                            let type_name = decode_ident(a)?;
                            let ctor_name = decode_ident(b)?;
                            let arg_list = as_list(c)?;
                            tasks.push(DecodeIrTask::Finish(DecodeIrBuild::Ctor(
                                type_name,
                                ctor_name,
                                arg_list.len(),
                            )));
                            for arg in arg_list.iter().rev() {
                                tasks.push(DecodeIrTask::Expr(arg));
                            }
                        }
                        _ => return err("invalid Expr S-expression"),
                    },
                    [SExp::Atom(t), a, b, c, d] => match t.as_str() {
                        "let" => {
                            let name = decode_ident(a)?;
                            let lty = decode_lty(b)?;
                            tasks.push(DecodeIrTask::Finish(DecodeIrBuild::Let {
                                name,
                                lty: Box::new(lty),
                            }));
                            tasks.push(DecodeIrTask::Expr(d));
                            tasks.push(DecodeIrTask::Expr(c));
                        }
                        "lam" => {
                            let params = map_decode(as_list(a)?, |pair| {
                                let [n, l] = as_list(pair)? else {
                                    return err("expected param pair");
                                };
                                Ok((decode_ident(n)?, decode_lty(l)?))
                            })?;
                            let pc = decode_tag_set(b)?;
                            let ret = decode_lty(c)?;
                            tasks.push(DecodeIrTask::Finish(DecodeIrBuild::Lam {
                                params,
                                pc,
                                ret: Box::new(ret),
                            }));
                            tasks.push(DecodeIrTask::Expr(d));
                        }
                        "join-pt" => {
                            let label = decode_ident(a)?;
                            let params = map_decode(as_list(b)?, |pair| {
                                let [n, l] = as_list(pair)? else {
                                    return err("expected join param");
                                };
                                Ok((decode_ident(n)?, decode_lty(l)?))
                            })?;
                            tasks.push(DecodeIrTask::Finish(DecodeIrBuild::Join { label, params }));
                            tasks.push(DecodeIrTask::Expr(d));
                            tasks.push(DecodeIrTask::Expr(c));
                        }
                        _ => return err("invalid Expr S-expression"),
                    },
                    _ => return err("invalid Expr S-expression"),
                }
            }
            DecodeIrTask::CaseAfterScrut(arms_s) => {
                let arm_list = as_list(arms_s)?;
                tasks.push(DecodeIrTask::Finish(DecodeIrBuild::Case(arm_list.len())));
                for arm_s in arm_list.iter().rev() {
                    tasks.push(DecodeIrTask::CaseArm(arm_s));
                }
            }
            DecodeIrTask::CaseArm(arm_s) => {
                let [SExp::Atom(t), cn, bs, body] = as_list(arm_s)? else {
                    return err("invalid CaseArm");
                };
                if t != "arm" {
                    return err("invalid CaseArm");
                }
                let ctor = decode_ident(cn)?;
                let binders = map_decode(as_list(bs)?, decode_ident)?;
                tasks.push(DecodeIrTask::Finish(DecodeIrBuild::CaseArm {
                    ctor,
                    binders,
                }));
                tasks.push(DecodeIrTask::Expr(body));
            }
            DecodeIrTask::AppAfterFn(args_s) => {
                let arg_list = as_list(args_s)?;
                tasks.push(DecodeIrTask::Finish(DecodeIrBuild::App(arg_list.len())));
                for arg in arg_list.iter().rev() {
                    tasks.push(DecodeIrTask::Expr(arg));
                }
            }
            DecodeIrTask::Plan(cur) => {
                let xs = as_list(cur)?;
                match xs {
                    [SExp::Atom(t), e] if t == "source-expr" => {
                        tasks.push(DecodeIrTask::Finish(DecodeIrBuild::SourceExpr));
                        tasks.push(DecodeIrTask::Expr(e));
                    }
                    [SExp::Atom(t), a, b] if t == "union" => {
                        tasks.push(DecodeIrTask::Finish(DecodeIrBuild::PlanUnion));
                        tasks.push(DecodeIrTask::Plan(b));
                        tasks.push(DecodeIrTask::Plan(a));
                    }
                    [SExp::Atom(t), a, b, c] if t == "source-db" => {
                        tasks.push(DecodeIrTask::Finish(DecodeIrBuild::SourceDB(b, c)));
                        tasks.push(DecodeIrTask::Expr(a));
                    }
                    [SExp::Atom(t), a, b, c] if t == "pseudonymize" => {
                        tasks.push(DecodeIrTask::PseudoAfterInput(b, c));
                        tasks.push(DecodeIrTask::Plan(a));
                    }
                    [SExp::Atom(t), a, b, c, d, e] if t == "join" => {
                        let kind = decode_join_kind(a)?;
                        tasks.push(DecodeIrTask::Finish(DecodeIrBuild::PlanJoin {
                            kind,
                            on: d,
                            suffixes: e,
                        }));
                        tasks.push(DecodeIrTask::Plan(c));
                        tasks.push(DecodeIrTask::Plan(b));
                    }
                    [SExp::Atom(t), a, _]
                        if matches!(
                            t.as_str(),
                            "select"
                                | "drop"
                                | "rename"
                                | "derive"
                                | "filter"
                                | "distinct"
                                | "sort"
                                | "limit"
                                | "group-by"
                                | "window"
                        ) =>
                    {
                        tasks.push(DecodeIrTask::Finish(DecodeIrBuild::PlanUnary(xs)));
                        tasks.push(DecodeIrTask::Plan(a));
                    }
                    [SExp::Atom(t), a, _, _] if matches!(t.as_str(), "summarize" | "redact") => {
                        tasks.push(DecodeIrTask::Finish(DecodeIrBuild::PlanUnary(xs)));
                        tasks.push(DecodeIrTask::Plan(a));
                    }
                    [SExp::Atom(t), a, _, _, _] if t == "suppress-small-groups" => {
                        tasks.push(DecodeIrTask::Finish(DecodeIrBuild::PlanUnary(xs)));
                        tasks.push(DecodeIrTask::Plan(a));
                    }
                    [SExp::Atom(t), a, _, _, _, _]
                        if matches!(t.as_str(), "fill-gaps" | "pivot-wider" | "crosstab") =>
                    {
                        tasks.push(DecodeIrTask::Finish(DecodeIrBuild::PlanUnary(xs)));
                        tasks.push(DecodeIrTask::Plan(a));
                    }
                    _ => return err("invalid Plan S-expression"),
                }
            }
            DecodeIrTask::PseudoAfterInput(col_s, sec_s) => {
                let col = decode_ident(col_s)?;
                tasks.push(DecodeIrTask::Finish(DecodeIrBuild::PlanPseudonymize(col)));
                tasks.push(DecodeIrTask::Expr(sec_s));
            }
            DecodeIrTask::Finish(build) => match build {
                DecodeIrBuild::Let { name, lty } => {
                    let (Some(body), Some(bound)) = (vals.pop(), vals.pop()) else {
                        unreachable!("stack balanced");
                    };
                    vals.push(DecodedIr::Expr(Expr::LetE {
                        name,
                        lty: *lty,
                        bound: Box::new(bound.into_expr()),
                        body: Box::new(body.into_expr()),
                    }));
                }
                DecodeIrBuild::If => {
                    let (Some(else_br), Some(then_br), Some(cond)) =
                        (vals.pop(), vals.pop(), vals.pop())
                    else {
                        unreachable!("stack balanced");
                    };
                    vals.push(DecodedIr::Expr(Expr::IfE {
                        cond: Box::new(cond.into_expr()),
                        then_br: Box::new(then_br.into_expr()),
                        else_br: Box::new(else_br.into_expr()),
                    }));
                }
                DecodeIrBuild::CaseArm { ctor, binders } => {
                    let Some(body) = vals.pop() else {
                        unreachable!("stack balanced");
                    };
                    vals.push(DecodedIr::CaseArm(CaseArm {
                        ctor,
                        binders,
                        body: body.into_expr(),
                    }));
                }
                DecodeIrBuild::Case(n) => {
                    let arms = vals
                        .split_off(vals.len() - n)
                        .into_iter()
                        .map(DecodedIr::into_case_arm)
                        .collect();
                    let Some(scrut) = vals.pop() else {
                        unreachable!("stack balanced");
                    };
                    vals.push(DecodedIr::Expr(Expr::CaseE {
                        scrut: Box::new(scrut.into_expr()),
                        arms,
                    }));
                }
                DecodeIrBuild::Lam { params, pc, ret } => {
                    let Some(body) = vals.pop() else {
                        unreachable!("stack balanced");
                    };
                    vals.push(DecodedIr::Expr(Expr::Lam {
                        params,
                        pc,
                        ret: *ret,
                        body: std::sync::Arc::new(body.into_expr()),
                    }));
                }
                DecodeIrBuild::App(n) => {
                    let args = vals
                        .split_off(vals.len() - n)
                        .into_iter()
                        .map(DecodedIr::into_expr)
                        .collect();
                    let Some(fn_expr) = vals.pop() else {
                        unreachable!("stack balanced");
                    };
                    vals.push(DecodedIr::Expr(Expr::App {
                        fn_expr: Box::new(fn_expr.into_expr()),
                        args,
                    }));
                }
                DecodeIrBuild::Call(fn_name, n) => {
                    let args = vals
                        .split_off(vals.len() - n)
                        .into_iter()
                        .map(DecodedIr::into_expr)
                        .collect();
                    vals.push(DecodedIr::Expr(Expr::Call { fn_name, args }));
                }
                DecodeIrBuild::Join { label, params } => {
                    let (Some(body), Some(rhs)) = (vals.pop(), vals.pop()) else {
                        unreachable!("stack balanced");
                    };
                    vals.push(DecodedIr::Expr(Expr::Join {
                        label,
                        params,
                        rhs: Box::new(rhs.into_expr()),
                        body: Box::new(body.into_expr()),
                    }));
                }
                DecodeIrBuild::Jump(label, n) => {
                    let args = vals
                        .split_off(vals.len() - n)
                        .into_iter()
                        .map(DecodedIr::into_expr)
                        .collect();
                    vals.push(DecodedIr::Expr(Expr::Jump { label, args }));
                }
                DecodeIrBuild::Tuple(n) => {
                    let es = vals
                        .split_off(vals.len() - n)
                        .into_iter()
                        .map(DecodedIr::into_expr)
                        .collect();
                    vals.push(DecodedIr::Expr(Expr::Tuple(es)));
                }
                DecodeIrBuild::Proj(idx_s) => {
                    let Some(tup) = vals.pop() else {
                        unreachable!("stack balanced");
                    };
                    let idx = decode_big_nat(idx_s)?;
                    vals.push(DecodedIr::Expr(Expr::Proj {
                        tup: Box::new(tup.into_expr()),
                        idx,
                    }));
                }
                DecodeIrBuild::Ctor(type_name, ctor_name, n) => {
                    let args = vals
                        .split_off(vals.len() - n)
                        .into_iter()
                        .map(DecodedIr::into_expr)
                        .collect();
                    vals.push(DecodedIr::Expr(Expr::Ctor {
                        type_name,
                        ctor_name,
                        args,
                    }));
                }
                DecodeIrBuild::Prim(op, n) => {
                    let args = vals
                        .split_off(vals.len() - n)
                        .into_iter()
                        .map(DecodedIr::into_expr)
                        .collect();
                    vals.push(DecodedIr::Expr(Expr::Prim { op: *op, args }));
                }
                DecodeIrBuild::Rel => {
                    let Some(plan) = vals.pop() else {
                        unreachable!("stack balanced");
                    };
                    vals.push(DecodedIr::Expr(Expr::Rel(Box::new(plan.into_plan()))));
                }
                DecodeIrBuild::Host(op, n) => {
                    let args = vals
                        .split_off(vals.len() - n)
                        .into_iter()
                        .map(DecodedIr::into_expr)
                        .collect();
                    vals.push(DecodedIr::Expr(Expr::Host { op: *op, args }));
                }
                DecodeIrBuild::StopSome(kind) => {
                    let Some(detail) = vals.pop() else {
                        unreachable!("stack balanced");
                    };
                    vals.push(DecodedIr::Expr(Expr::Stop {
                        kind,
                        detail: Some(Box::new(detail.into_expr())),
                    }));
                }
                DecodeIrBuild::Fail => {
                    let Some(msg) = vals.pop() else {
                        unreachable!("stack balanced");
                    };
                    vals.push(DecodedIr::Expr(Expr::Fail(Box::new(msg.into_expr()))));
                }
                DecodeIrBuild::SourceExpr => {
                    let Some(e) = vals.pop() else {
                        unreachable!("stack balanced");
                    };
                    vals.push(DecodedIr::Plan(Plan::SourceExpr(Box::new(e.into_expr()))));
                }
                DecodeIrBuild::SourceDB(table_s, schema_s) => {
                    let Some(cap) = vals.pop() else {
                        unreachable!("stack balanced");
                    };
                    vals.push(DecodedIr::Plan(Plan::SourceDB {
                        cap: Box::new(cap.into_expr()),
                        table_name: decode_ident(table_s)?,
                        schema: decode_table_ty(schema_s)?,
                    }));
                }
                DecodeIrBuild::PlanJoin { kind, on, suffixes } => {
                    let (Some(right), Some(left)) = (vals.pop(), vals.pop()) else {
                        unreachable!("stack balanced");
                    };
                    vals.push(DecodedIr::Plan(Plan::Join {
                        kind,
                        left: Box::new(left.into_plan()),
                        right: Box::new(right.into_plan()),
                        on: decode_join_on(on)?,
                        suffixes: decode_opt(suffixes, |pair| {
                            let [sl, sr] = as_list(pair)? else {
                                return err("expected suffix pair");
                            };
                            Ok((decode_str_only(sl)?, decode_str_only(sr)?))
                        })?,
                    }));
                }
                DecodeIrBuild::PlanUnion => {
                    let (Some(right), Some(left)) = (vals.pop(), vals.pop()) else {
                        unreachable!("stack balanced");
                    };
                    vals.push(DecodedIr::Plan(Plan::Union {
                        left: Box::new(left.into_plan()),
                        right: Box::new(right.into_plan()),
                    }));
                }
                DecodeIrBuild::PlanPseudonymize(col) => {
                    let (Some(secret), Some(input)) = (vals.pop(), vals.pop()) else {
                        unreachable!("stack balanced");
                    };
                    vals.push(DecodedIr::Plan(Plan::Pseudonymize {
                        input: Box::new(input.into_plan()),
                        col,
                        secret: Box::new(secret.into_expr()),
                    }));
                }
                DecodeIrBuild::PlanUnary(xs) => {
                    let Some(input) = vals.pop() else {
                        unreachable!("stack balanced");
                    };
                    vals.push(DecodedIr::Plan(decode_plan_unary_step(
                        xs,
                        input.into_plan(),
                    )?));
                }
            },
        }
    }
    match vals.pop() {
        Some(res) => Ok(res.into_expr()),
        None => unreachable!("decode_expr always produces one Expr"),
    }
}

fn decode_plan_unary_step(xs: &[SExp], input: Plan) -> Result<Plan, WireError> {
    match xs {
        [SExp::Atom(t), _, b] => match t.as_str() {
            "select" => Ok(Plan::Select {
                input: Box::new(input),
                cols: map_decode(as_list(b)?, decode_ident)?,
            }),
            "drop" => Ok(Plan::Drop {
                input: Box::new(input),
                cols: map_decode(as_list(b)?, decode_ident)?,
            }),
            "rename" => Ok(Plan::Rename {
                input: Box::new(input),
                pairs: map_decode(as_list(b)?, |pair| {
                    let [nw, ol] = as_list(pair)? else {
                        return err("expected rename pair");
                    };
                    Ok((decode_ident(nw)?, decode_ident(ol)?))
                })?,
            }),
            "derive" => Ok(Plan::Derive {
                input: Box::new(input),
                items: map_decode(as_list(b)?, decode_derive_item)?,
            }),
            "filter" => Ok(Plan::Filter {
                input: Box::new(input),
                pred: decode_row_expr(b)?,
            }),
            "distinct" => Ok(Plan::Distinct {
                input: Box::new(input),
                cols: map_decode(as_list(b)?, decode_ident)?,
            }),
            "sort" => Ok(Plan::Sort {
                input: Box::new(input),
                keys: map_decode(as_list(b)?, |pair| {
                    let [c, d] = as_list(pair)? else {
                        return err("expected sort key");
                    };
                    Ok((decode_ident(c)?, decode_sort_dir(d)?))
                })?,
            }),
            "limit" => Ok(Plan::Limit {
                input: Box::new(input),
                n: decode_big_nat(b)?,
            }),
            "group-by" => Ok(Plan::GroupBy {
                input: Box::new(input),
                keys: map_decode(as_list(b)?, decode_ident)?,
            }),
            "window" => Ok(Plan::Window {
                input: Box::new(input),
                items: map_decode(as_list(b)?, decode_window_item)?,
            }),
            _ => err("invalid Plan S-expression"),
        },
        [SExp::Atom(t), _, b, c] => match t.as_str() {
            "summarize" => Ok(Plan::Summarize {
                input: Box::new(input),
                aggs: map_decode(as_list(b)?, decode_agg_item)?,
                distinct_key: decode_opt(c, decode_ident)?,
            }),
            "redact" => Ok(Plan::Redact {
                input: Box::new(input),
                col: decode_ident(b)?,
                replacement: decode_str_only(c)?,
            }),
            _ => err("invalid Plan S-expression"),
        },
        [SExp::Atom(t), _, k, db, m] if t == "suppress-small-groups" => {
            Ok(Plan::SuppressSmallGroups {
                input: Box::new(input),
                min_k: decode_big_nat(k)?,
                distinct_by: decode_opt(db, decode_ident)?,
                mode: decode_suppress_mode(m)?,
            })
        }
        [SExp::Atom(t), _, b, c, d, e] => match t.as_str() {
            "fill-gaps" => Ok(Plan::FillGaps {
                input: Box::new(input),
                col: decode_ident(b)?,
                step_micros: decode_int(c)?,
                over: map_decode(as_list(d)?, decode_ident)?,
                fill: map_decode(as_list(e)?, |pair| {
                    let [cn, lit] = as_list(pair)? else {
                        return err("expected fill pair");
                    };
                    Ok((decode_ident(cn)?, decode_literal(lit)?))
                })?,
            }),
            "pivot-wider" => Ok(Plan::PivotWider {
                input: Box::new(input),
                names_from: decode_ident(b)?,
                values_from: decode_ident(c)?,
                static_cols: map_decode(as_list(d)?, decode_ident)?,
                fill: decode_literal(e)?,
            }),
            "crosstab" => Ok(Plan::Crosstab {
                input: Box::new(input),
                rows_col: decode_ident(b)?,
                cols_col: decode_ident(c)?,
                values_col: decode_ident(d)?,
                fill: decode_literal(e)?,
            }),
            _ => err("invalid Plan S-expression"),
        },
        _ => err("invalid Plan S-expression"),
    }
}

// ---------------------------------------------------------------------------
// Policy, Top-Level Declarations, Metadata Validation & `Program` Wire Codec
// ---------------------------------------------------------------------------

fn encode_policy(p: &Policy) -> SExp {
    SExp::List(vec![
        atom("policy"),
        encode_big_nat(&p.min_group_size),
        encode_bool(p.forbid_manual_declassify),
        encode_bool(p.forbid_repl_sensitive),
        encode_tag_set(&p.allow_console),
        SExp::List(
            p.allow_export
                .iter()
                .map(|(r, ts)| SExp::List(vec![SExp::Str(r.clone()), encode_tag_set(ts)]))
                .collect(),
        ),
        SExp::List(
            p.allow_https
                .iter()
                .map(|(h, ts)| SExp::List(vec![SExp::Str(h.clone()), encode_tag_set(ts)]))
                .collect(),
        ),
        SExp::List(
            p.allow_write
                .iter()
                .map(|w| {
                    SExp::List(vec![
                        encode_ident(&w.db),
                        encode_ident(&w.table),
                        encode_tag_set(&w.tags),
                    ])
                })
                .collect(),
        ),
    ])
}

fn decode_policy(s: &SExp) -> Result<Policy, WireError> {
    let [SExp::Atom(t), mg, fmd, frs, ac, ae, ah, aw] = as_list(s)? else {
        return err("expected (policy ...)");
    };
    if t != "policy" {
        return err("expected (policy ...)");
    }
    Ok(Policy {
        min_group_size: decode_big_nat(mg)?,
        forbid_manual_declassify: decode_bool(fmd)?,
        forbid_repl_sensitive: decode_bool(frs)?,
        allow_console: decode_tag_set(ac)?,
        allow_export: map_decode(as_list(ae)?, |rule| {
            let [r, ts] = as_list(rule)? else {
                return err("invalid allow-export rule");
            };
            Ok((decode_str_only(r)?, decode_tag_set(ts)?))
        })?,
        allow_https: map_decode(as_list(ah)?, |rule| {
            let [h, ts] = as_list(rule)? else {
                return err("invalid allow-https rule");
            };
            Ok((decode_str_only(h)?, decode_tag_set(ts)?))
        })?,
        allow_write: map_decode(as_list(aw)?, |rule| {
            let [db, tbl, ts] = as_list(rule)? else {
                return err("invalid allow-write rule");
            };
            Ok(PolicyWriteRule {
                db: decode_ident(db)?,
                table: decode_ident(tbl)?,
                tags: decode_tag_set(ts)?,
            })
        })?,
    })
}

fn encode_data_decl(d: &DataDecl) -> SExp {
    SExp::List(vec![
        atom("data-decl"),
        encode_ident(&d.name),
        SExp::List(
            d.ctors
                .iter()
                .map(|c| {
                    SExp::List(vec![
                        atom("ctor-decl"),
                        encode_ident(&c.name),
                        SExp::List(c.fields.iter().map(encode_lty).collect()),
                    ])
                })
                .collect(),
        ),
    ])
}

fn decode_data_decl(s: &SExp) -> Result<DataDecl, WireError> {
    let [SExp::Atom(t), n, cs] = as_list(s)? else {
        return err("expected data-decl");
    };
    if t != "data-decl" {
        return err("expected data-decl");
    }
    let ctors = map_decode(as_list(cs)?, |c| {
        let [SExp::Atom(ct), cn, fs] = as_list(c)? else {
            return err("expected ctor-decl");
        };
        if ct != "ctor-decl" {
            return err("expected ctor-decl");
        }
        Ok(CtorDecl {
            name: decode_ident(cn)?,
            fields: map_decode(as_list(fs)?, decode_lty)?,
        })
    })?;
    Ok(DataDecl {
        name: decode_ident(n)?,
        ctors,
    })
}

fn encode_schema_decl(s: &SchemaDecl) -> SExp {
    SExp::List(vec![
        atom("schema-decl"),
        encode_ident(&s.name),
        encode_table_ty(&s.schema),
    ])
}

fn decode_schema_decl(s: &SExp) -> Result<SchemaDecl, WireError> {
    let [SExp::Atom(t), n, tt] = as_list(s)? else {
        return err("expected schema-decl");
    };
    if t != "schema-decl" {
        return err("expected schema-decl");
    }
    Ok(SchemaDecl {
        name: decode_ident(n)?,
        schema: decode_table_ty(tt)?,
    })
}

fn encode_const_decl(c: &ConstDecl) -> SExp {
    SExp::List(vec![
        atom("const-decl"),
        encode_ident(&c.name),
        encode_lty(&c.lty),
        encode_literal(&c.value),
    ])
}

fn decode_const_decl(s: &SExp) -> Result<ConstDecl, WireError> {
    let [SExp::Atom(t), n, l, v] = as_list(s)? else {
        return err("expected const-decl");
    };
    if t != "const-decl" {
        return err("expected const-decl");
    }
    Ok(ConstDecl {
        name: decode_ident(n)?,
        lty: decode_lty(l)?,
        value: decode_literal(v)?,
    })
}

fn encode_fun_kind(k: FunKind) -> SExp {
    match k {
        FunKind::Function => atom("fn"),
        FunKind::Test => atom("test"),
        FunKind::ExampleDecl => atom("example"),
        FunKind::Promise => atom("promise"),
    }
}

fn decode_fun_kind(s: &SExp) -> Result<FunKind, WireError> {
    match s {
        SExp::Atom(a) => match a.as_str() {
            "fn" => Ok(FunKind::Function),
            "test" => Ok(FunKind::Test),
            "example" => Ok(FunKind::ExampleDecl),
            "promise" => Ok(FunKind::Promise),
            _ => err("invalid FunKind"),
        },
        _ => err("invalid FunKind"),
    }
}

fn encode_fun_decl(f: &FunDecl) -> SExp {
    SExp::List(vec![
        atom("fun-decl"),
        encode_ident(&f.name),
        encode_fun_kind(f.kind),
        encode_bool(f.is_pure),
        SExp::List(
            f.params
                .iter()
                .map(|(n, l)| SExp::List(vec![encode_ident(n), encode_lty(l)]))
                .collect(),
        ),
        encode_tag_set(&f.pc),
        encode_lty(&f.ret),
        encode_expr(&f.body),
    ])
}

fn decode_fun_decl(s: &SExp) -> Result<FunDecl, WireError> {
    let [SExp::Atom(t), n, k, p_b, ps, pc, ret, body] = as_list(s)? else {
        return err("expected fun-decl");
    };
    if t != "fun-decl" {
        return err("expected fun-decl");
    }
    Ok(FunDecl {
        name: decode_ident(n)?,
        kind: decode_fun_kind(k)?,
        is_pure: decode_bool(p_b)?,
        params: map_decode(as_list(ps)?, |pair| {
            let [pn, pl] = as_list(pair)? else {
                return err("expected param");
            };
            Ok((decode_ident(pn)?, decode_lty(pl)?))
        })?,
        pc: decode_tag_set(pc)?,
        ret: decode_lty(ret)?,
        body: decode_expr(body)?,
    })
}

fn valid_source_span_shape(sp: &SourceSpan) -> bool {
    let one = BigInt::one();
    !sp.file.is_empty()
        && sp.start_line >= one
        && sp.start_col >= one
        && sp.start_line <= sp.end_line
        && if sp.start_line == sp.end_line {
            sp.start_col <= sp.end_col
        } else {
            sp.end_col >= one
        }
}

fn encode_source_span(sp: &SourceSpan) -> SExp {
    SExp::List(vec![
        atom("span"),
        SExp::Str(sp.file.clone()),
        encode_big_nat(&sp.start_line),
        encode_big_nat(&sp.start_col),
        encode_big_nat(&sp.end_line),
        encode_big_nat(&sp.end_col),
    ])
}

fn decode_source_span(s: &SExp) -> Result<SourceSpan, WireError> {
    let [SExp::Atom(t), file, sl, sc, el, ec] = as_list(s)? else {
        return err("expected (span ...)");
    };
    if t != "span" {
        return err("expected (span ...)");
    }
    let sp = SourceSpan {
        file: decode_str_only(file)?,
        start_line: decode_big_nat(sl)?,
        start_col: decode_big_nat(sc)?,
        end_line: decode_big_nat(el)?,
        end_col: decode_big_nat(ec)?,
    };
    if valid_source_span_shape(&sp) {
        Ok(sp)
    } else {
        err("invalid SourceSpan shape in CompilerMetadata")
    }
}

fn encode_metadata(m: &CompilerMetadata) -> SExp {
    let mut items = Vec::with_capacity(m.entries.len() + 1);
    items.push(atom("meta"));
    items.extend(m.entries.iter().map(|e| {
        SExp::List(vec![
            atom("meta-entry"),
            encode_ident(&e.node_id),
            encode_opt(&e.orig_name, |s| SExp::Str(s.clone())),
            encode_opt(&e.span, encode_source_span),
        ])
    }));
    SExp::List(items)
}

fn decode_metadata(s: &SExp) -> Result<CompilerMetadata, WireError> {
    let xs = as_list(s)?;
    let Some((SExp::Atom(h), rest)) = xs.split_first() else {
        return err("expected (meta ...) in CompilerMetadata");
    };
    if h != "meta" {
        return err("expected (meta ...) in CompilerMetadata");
    }
    let entries = map_decode(rest, |item| {
        let [SExp::Atom(t), nid, onm, sp] = as_list(item)? else {
            return err("invalid meta-entry shape in CompilerMetadata");
        };
        if t != "meta-entry" {
            return err("invalid meta-entry shape in CompilerMetadata");
        }
        let node_id = decode_ident(nid)?;
        if node_id.is_empty() {
            return err("empty nodeId in CompilerMetadata");
        }
        let orig_name = decode_opt(onm, decode_str_only)?;
        let span = decode_opt(sp, decode_source_span)?;
        Ok(MetaEntry {
            node_id,
            orig_name,
            span,
        })
    })?;
    Ok(CompilerMetadata { entries })
}

/// Print a `Program` in canonical `(dana-core 0.1 ...)` S-expression wire format
/// terminated by a single LF (`\n`).
#[must_use]
pub fn print_program(prog: &Program) -> String {
    with_large_stack(|| print_program_inner(prog))
}

fn print_program_inner(prog: &Program) -> String {
    let mut custom_tags = vec![atom("custom-tags")];
    custom_tags.extend(prog.tags.iter().map(|t| encode_ident(t)));

    let mut datas = vec![atom("datas")];
    datas.extend(prog.datas.iter().map(encode_data_decl));

    let mut schemas = vec![atom("schemas")];
    schemas.extend(prog.schemas.iter().map(encode_schema_decl));

    let mut consts = vec![atom("consts")];
    consts.extend(prog.consts.iter().map(encode_const_decl));

    let mut funs = vec![atom("funs")];
    funs.extend(prog.funs.iter().map(encode_fun_decl));

    let sexp = SExp::List(vec![
        atom("dana-core"),
        SExp::Atom(format!("{}.{}", prog.version.major, prog.version.minor)),
        SExp::List(custom_tags),
        encode_opt(&prog.policy, encode_policy),
        SExp::List(datas),
        SExp::List(schemas),
        SExp::List(consts),
        SExp::List(funs),
        encode_opt(&prog.entry, |e| encode_ident(e)),
        encode_metadata(&prog.metadata),
    ]);
    let mut out = print_sexp(&sexp);
    out.push('\n');
    out
}

/// Parse a canonical `(dana-core 0.1 ...)` wire document into a `Program`.
/// Enforces version 0.1, strict escaping, metadata shape, and exact byte-for-byte
/// canonicality (`print_program(&prog) == wire`).
pub fn parse_program(wire: &str) -> Result<Program, WireError> {
    with_large_stack(|| parse_program_inner(wire))
}

fn parse_program_inner(wire: &str) -> Result<Program, WireError> {
    let sexp = parse_canonical_sexp(wire)?;
    let xs =
        as_list(&sexp).map_err(|_| WireError::new("expected top-level (dana-core 0.1 ...)"))?;
    match xs {
        [
            SExp::Atom(head),
            SExp::Atom(ver),
            SExp::List(tag_list),
            pol_sexp,
            SExp::List(data_list),
            SExp::List(schema_list),
            SExp::List(const_list),
            SExp::List(fun_list),
            entry_sexp,
            meta_sexp,
        ] if head == "dana-core" => {
            if ver != "0.1" {
                return err(format!(
                    "unsupported dana-core wire version '{ver}' (expected 0.1)"
                ));
            }
            let Some((SExp::Atom(th), tag_items)) = tag_list.split_first() else {
                return err("malformed (dana-core 0.1 ...) payload structure");
            };
            let Some((SExp::Atom(dh), data_items)) = data_list.split_first() else {
                return err("malformed (dana-core 0.1 ...) payload structure");
            };
            let Some((SExp::Atom(sh), schema_items)) = schema_list.split_first() else {
                return err("malformed (dana-core 0.1 ...) payload structure");
            };
            let Some((SExp::Atom(ch), const_items)) = const_list.split_first() else {
                return err("malformed (dana-core 0.1 ...) payload structure");
            };
            let Some((SExp::Atom(fh), fun_items)) = fun_list.split_first() else {
                return err("malformed (dana-core 0.1 ...) payload structure");
            };
            if th != "custom-tags"
                || dh != "datas"
                || sh != "schemas"
                || ch != "consts"
                || fh != "funs"
            {
                return err("malformed (dana-core 0.1 ...) payload structure");
            }
            let prog = Program {
                version: CoreVersion { major: 0, minor: 1 },
                tags: map_decode(tag_items, decode_ident)?,
                policy: decode_opt(pol_sexp, decode_policy)?,
                datas: map_decode(data_items, decode_data_decl)?,
                schemas: map_decode(schema_items, decode_schema_decl)?,
                consts: map_decode(const_items, decode_const_decl)?,
                funs: map_decode(fun_items, decode_fun_decl)?,
                entry: decode_opt(entry_sexp, decode_ident)?,
                metadata: decode_metadata(meta_sexp)?,
            };
            if print_program(&prog) != wire {
                return err("non-canonical wire encoding (must match printProgram byte-for-byte)");
            }
            Ok(prog)
        }
        [SExp::Atom(head), SExp::Atom(ver), ..] if head == "dana-core" => {
            if ver != "0.1" {
                err(format!(
                    "unsupported dana-core wire version '{ver}' (expected 0.1)"
                ))
            } else {
                err("malformed (dana-core 0.1 ...) payload structure")
            }
        }
        _ => err("expected top-level (dana-core 0.1 ...)"),
    }
}

// ---------------------------------------------------------------------------
// Canonical Observable `Report` Wire Printer
// ---------------------------------------------------------------------------

fn encode_exit_status(st: ExitStatus) -> SExp {
    match st {
        ExitStatus::Ok => atom("ok"),
        ExitStatus::Stopped => atom("stopped"),
        ExitStatus::Failed => atom("failed"),
    }
}

/// Emit canonical `(dana-report 0.1 ...)\n` matching `formal/DanaCore/Text.lean:printReport`.
#[must_use]
pub fn print_report(rep: &ExecReport) -> String {
    let mut stdout_list = vec![atom("stdout")];
    stdout_list.extend(rep.stdout.iter().cloned().map(SExp::Str));

    let mut stderr_list = vec![atom("stderr")];
    stderr_list.extend(rep.stderr.iter().cloned().map(SExp::Str));

    let mut written_files_list = vec![atom("written-files")];
    written_files_list.extend(
        rep.written_files
            .iter()
            .map(|(p, c)| SExp::List(vec![SExp::Str(p.clone()), SExp::Str(c.clone())])),
    );

    let mut written_tables_list = vec![atom("written-tables")];
    written_tables_list.extend(rep.written_tables.iter().map(|(db, tbl, cols, rows)| {
        SExp::List(vec![
            encode_ident(db),
            encode_ident(tbl),
            SExp::List(cols.iter().map(|c| encode_ident(c)).collect()),
            SExp::List(
                rows.iter()
                    .map(|r| SExp::List(r.iter().cloned().map(SExp::Str).collect()))
                    .collect(),
            ),
        ])
    }));

    let mut fake_consoles_list = vec![atom("fake-consoles")];
    fake_consoles_list.extend(rep.fake_consoles.iter().map(|fc| {
        let mut fc_out = vec![atom("stdout")];
        fc_out.extend(fc.stdout.iter().cloned().map(SExp::Str));
        let mut fc_err = vec![atom("stderr")];
        fc_err.extend(fc.stderr.iter().cloned().map(SExp::Str));
        SExp::List(vec![SExp::List(fc_out), SExp::List(fc_err)])
    }));

    let mut fake_files_list = vec![atom("fake-files")];
    fake_files_list.extend(rep.fake_files.iter().map(|ff| {
        SExp::List(
            ff.files
                .iter()
                .map(|(p, c)| SExp::List(vec![SExp::Str(p.clone()), SExp::Str(c.clone())]))
                .collect(),
        )
    }));

    let sexp = SExp::List(vec![
        atom("dana-report"),
        atom("0.1"),
        SExp::List(vec![atom("status"), encode_exit_status(rep.status)]),
        SExp::List(vec![
            atom("diagnostic"),
            encode_opt(&rep.diagnostic, |s| SExp::Str(s.clone())),
        ]),
        SExp::List(stdout_list),
        SExp::List(stderr_list),
        SExp::List(written_files_list),
        SExp::List(written_tables_list),
        SExp::List(fake_consoles_list),
        SExp::List(fake_files_list),
    ]);
    let mut out = print_sexp(&sexp);
    out.push('\n');
    out
}
