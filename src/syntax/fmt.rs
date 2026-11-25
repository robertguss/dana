//! Canonical 2-space idempotent formatter for Dana (`dana format`).
//!
//! Preserves all `#` line comments and `##` doc comments, aligns Markdown `table ... end`
//! columns cleanly, and guarantees `format_module(parse_module(format_module(m))) == format_module(m)`.

use std::fmt::Write as _;

use crate::base::Span;
use crate::syntax::ast::*;
use crate::syntax::token::Comment;

const LINE_WIDTH: usize = 96;

/// Format a parsed [`Module`] into canonical 2-space Dana source text.
#[must_use]
pub fn format_module(module: &Module) -> String {
    let mut f = Formatter::new(&module.comments, &module.blank_lines);
    f.emit_comments_before(module.header.span.start, 0, false);
    f.format_header(&module.header);
    for item in &module.items {
        f.ensure_blank_line();
        f.emit_comments_before(item.span().start, 0, true);
        f.format_top_item(item);
    }
    f.emit_remaining_comments(0);
    if !f.out.ends_with('\n') {
        f.out.push('\n');
    }
    f.out
}

struct Formatter<'a> {
    comments: &'a [Comment],
    blank_lines: &'a [u32],
    c_idx: usize,
    out: String,
}

impl<'a> Formatter<'a> {
    const fn new(comments: &'a [Comment], blank_lines: &'a [u32]) -> Self {
        Self {
            comments,
            blank_lines,
            c_idx: 0,
            out: String::new(),
        }
    }

    fn has_blank_line_between(&self, start: u32, end: u32) -> bool {
        if start >= end {
            return false;
        }
        let idx = self.blank_lines.partition_point(|&off| off < start);
        self.blank_lines.get(idx).is_some_and(|&off| off < end)
    }

    fn next_comment_or(&self, limit: u32) -> u32 {
        self.comments
            .get(self.c_idx)
            .filter(|c| c.span.start < limit)
            .map_or(limit, |c| c.span.start)
    }

    fn indent(&mut self, level: usize) {
        for _ in 0..(level * 2) {
            self.out.push(' ');
        }
    }

    fn ensure_blank_line(&mut self) {
        if self.out.is_empty() {
            return;
        }
        if !self.out.ends_with('\n') {
            self.out.push('\n');
        }
        if !self.out.ends_with("\n\n") {
            self.out.push('\n');
        }
    }

    fn emit_comments_before(&mut self, byte_offset: u32, level: usize, separate_groups: bool) {
        let mut prev_line: Option<u32> = None;
        while let Some(c) = self.comments.get(self.c_idx) {
            if c.span.start >= byte_offset {
                break;
            }
            if separate_groups
                && let Some(pl) = prev_line
                && c.line > pl + 1
            {
                self.ensure_blank_line();
            }
            self.indent(level);
            self.out.push_str(&c.text);
            self.out.push('\n');
            prev_line = Some(c.line);
            self.c_idx += 1;
        }
    }

    fn emit_inline_comment_after(&mut self, span: Span) {
        // Declaration/field spans include their terminating newline, so any inline comment on
        // the same line strictly lies within `[span.start, span.end]`.
        if let Some(c) = self.comments.get(self.c_idx)
            && c.is_inline
            && c.span.start >= span.start
            && c.span.end <= span.end
        {
            self.out.push_str("  ");
            self.out.push_str(&c.text);
            self.c_idx += 1;
        }
    }

    fn emit_remaining_comments(&mut self, level: usize) {
        while let Some(c) = self.comments.get(self.c_idx) {
            self.indent(level);
            self.out.push_str(&c.text);
            self.out.push('\n');
            self.c_idx += 1;
        }
    }

    fn format_header(&mut self, h: &ModuleHeader) {
        self.out.push_str("module ");
        self.write_module_path(&h.path);
        self.out.push('\n');
        if let Some(ex) = &h.expose {
            self.emit_comments_before(ex.span.start, 0, false);
            self.out.push_str("expose ");
            for (i, item) in ex.items.iter().enumerate() {
                if i > 0 {
                    self.out.push_str(", ");
                }
                match item {
                    ExposeItem::Value(n) | ExposeItem::Type(n) => self.out.push_str(&n.name),
                    ExposeItem::TypeAll(n) => {
                        let _ = write!(self.out, "{}(..)", n.name);
                    }
                }
            }
            self.out.push('\n');
        }
        for u in &h.uses {
            self.emit_comments_before(u.span.start, 0, false);
            self.out.push_str("use ");
            self.write_module_path(&u.path);
            if let Some(items) = &u.items {
                self.out.push_str(" {");
                for (i, it) in items.iter().enumerate() {
                    if i > 0 {
                        self.out.push_str(", ");
                    }
                    self.out.push_str(&it.name);
                }
                self.out.push('}');
            }
            self.out.push('\n');
        }
    }

    fn write_module_path(&mut self, path: &[SpannedName]) {
        for (i, seg) in path.iter().enumerate() {
            if i > 0 {
                self.out.push('.');
            }
            self.out.push_str(&seg.name);
        }
    }

    fn format_top_item(&mut self, item: &TopItem) {
        match item {
            TopItem::Tag(t) => {
                let _ = writeln!(self.out, "tag {}", t.name.name);
            }
            TopItem::Schema(s) => self.format_schema(s),
            TopItem::Struct(s) => self.format_struct(s),
            TopItem::Enum(e) => self.format_enum(e),
            TopItem::Const(c) => {
                self.out.push_str("const ");
                self.out.push_str(&c.name.name);
                if let Some(ty) = &c.ty {
                    self.out.push_str(": ");
                    self.out.push_str(&render_type(ty));
                }
                self.out.push_str(" = ");
                let rendered = self.render_expr(&c.value, 0);
                self.out.push_str(&rendered);
                self.out.push('\n');
            }
            TopItem::Fn(f) => self.format_fn(f),
            TopItem::Test(t) => self.format_test(t),
        }
    }

    fn format_schema(&mut self, s: &SchemaDecl) {
        self.out.push_str("schema ");
        self.out.push_str(&s.name.name);
        if !s.tags.is_empty() {
            self.out.push(' ');
            self.out.push_str(&render_tags(&s.tags));
        }
        self.out.push('\n');
        for field in &s.fields {
            self.emit_comments_before(field.span.start, 1, false);
            self.indent(1);
            let _ = write!(self.out, "{}: {}", field.name.name, render_type(&field.ty));
            if !field.tags.is_empty() {
                self.out.push(' ');
                self.out.push_str(&render_tags(&field.tags));
            }
            if let Some(w) = &field.constraint {
                self.out.push_str(" where ");
                let rendered = self.render_expr(w, 1);
                self.out.push_str(&rendered);
            }
            self.emit_inline_comment_after(field.span);
            self.out.push('\n');
        }
        self.emit_comments_before(s.span.end, 1, false);
        self.out.push_str("end\n");
    }

    fn format_struct(&mut self, s: &StructDecl) {
        let _ = writeln!(self.out, "struct {}", s.name.name);
        for field in &s.fields {
            self.emit_comments_before(field.span.start, 1, false);
            self.indent(1);
            let _ = write!(
                self.out,
                "{}: {}",
                field.name.name,
                render_type_indented(&field.ty, 1)
            );
            if !field.tags.is_empty() {
                self.out.push(' ');
                self.out.push_str(&render_tags(&field.tags));
            }
            self.emit_inline_comment_after(field.span);
            self.out.push('\n');
        }
        self.emit_comments_before(s.span.end, 1, false);
        self.out.push_str("end\n");
    }

    fn format_enum(&mut self, e: &EnumDecl) {
        let _ = writeln!(self.out, "enum {}", e.name.name);
        for v in &e.variants {
            self.emit_comments_before(v.span.start, 1, false);
            self.indent(1);
            self.out.push_str(&v.name.name);
            if !v.fields.is_empty() {
                self.out.push('(');
                for (i, vf) in v.fields.iter().enumerate() {
                    if i > 0 {
                        self.out.push_str(", ");
                    }
                    match vf {
                        VariantField::Positional { ty, .. } => self.out.push_str(&render_type(ty)),
                        VariantField::Named { name, ty, tags, .. } => {
                            let _ = write!(self.out, "{}: {}", name.name, render_type(ty));
                            if !tags.is_empty() {
                                self.out.push(' ');
                                self.out.push_str(&render_tags(tags));
                            }
                        }
                    }
                }
                self.out.push(')');
            }
            self.emit_inline_comment_after(v.span);
            self.out.push('\n');
        }
        self.emit_comments_before(e.span.end, 1, false);
        self.out.push_str("end\n");
    }

    fn format_fn(&mut self, f: &FnDecl) {
        let single_params: Vec<String> = f.params.iter().map(render_param).collect();
        let ret_inline = f.ret_ty.as_ref().map(|r| {
            let mut s = format!(" : {}", render_type(&r.ty));
            if !r.tags.is_empty() {
                s.push(' ');
                s.push_str(&render_tags(&r.tags));
            }
            s
        });
        let single_line = format!(
            "fn {}({}){}",
            f.name.name,
            single_params.join(", "),
            ret_inline.as_deref().unwrap_or("")
        );

        if single_line.len() <= LINE_WIDTH && !single_line.contains('\n') {
            self.out.push_str(&single_line);
            self.out.push('\n');
        } else {
            let _ = write!(self.out, "fn {}", f.name.name);
            if f.params.is_empty() {
                self.out.push_str("()");
            } else if single_params.join(", ").len() + f.name.name.len() + 6 <= LINE_WIDTH {
                let _ = write!(self.out, "({})", single_params.join(", "));
            } else {
                self.out.push_str("(\n");
                for (i, p) in single_params.iter().enumerate() {
                    self.indent(1);
                    self.out.push_str(p);
                    if i + 1 < single_params.len() {
                        self.out.push(',');
                    }
                    self.out.push('\n');
                }
                self.out.push(')');
            }
            if let Some(r) = &f.ret_ty {
                self.out.push_str(" : ");
                self.out.push_str(&render_type_indented(&r.ty, 0));
                if !r.tags.is_empty() {
                    self.out.push(' ');
                    self.out.push_str(&render_tags(&r.tags));
                }
            }
            self.out.push('\n');
        }

        let mut prev_was_examples_or_promise = false;
        let mut prev_end: Option<u32> = None;
        for (idx, fs) in f.body.iter().enumerate() {
            let is_spec = matches!(fs, FnStmt::Examples { .. } | FnStmt::Promise { .. });
            let fs_start = fs.span().start;
            let force_blank = idx > 0
                && (matches!(fs, FnStmt::Examples { .. })
                    || (prev_was_examples_or_promise && !is_spec));
            let source_blank = prev_end
                .is_some_and(|pe| self.has_blank_line_between(pe, self.next_comment_or(fs_start)));
            if force_blank || source_blank {
                self.ensure_blank_line();
            }
            self.emit_comments_before(fs_start, 1, idx > 0);
            match fs {
                FnStmt::Examples { stmts, span } => {
                    self.indent(1);
                    self.out.push_str("examples\n");
                    self.format_stmts(stmts, 2, span.end);
                    self.indent(1);
                    self.out.push_str("end\n");
                    prev_was_examples_or_promise = true;
                }
                FnStmt::Promise { expr, .. } => {
                    self.indent(1);
                    let rendered = self.render_expr(expr, 1);
                    let _ = writeln!(self.out, "promise {rendered}");
                    prev_was_examples_or_promise = true;
                }
                FnStmt::Stmt(st) => {
                    self.format_stmt(st, 1);
                    prev_was_examples_or_promise = false;
                }
            }
            prev_end = Some(fs.span().end);
        }
        self.emit_comments_before(f.span.end, 1, false);
        self.out.push_str("end\n");
    }

    fn format_test(&mut self, t: &TestDecl) {
        let _ = writeln!(self.out, "test \"{}\"", t.name_raw);
        self.format_stmts(&t.body, 1, t.span.end);
        self.out.push_str("end\n");
    }

    fn format_stmts(&mut self, stmts: &[Stmt], level: usize, block_end: u32) {
        let mut prev_end: Option<u32> = None;
        for (idx, st) in stmts.iter().enumerate() {
            if let Some(pe) = prev_end
                && self.has_blank_line_between(pe, self.next_comment_or(st.span.start))
            {
                self.ensure_blank_line();
            }
            self.emit_comments_before(st.span.start, level, idx > 0);
            self.format_stmt(st, level);
            prev_end = Some(st.span.end);
        }
        self.emit_comments_before(block_end, level, false);
    }

    fn format_stmt(&mut self, st: &Stmt, level: usize) {
        match &st.kind {
            StmtKind::Var { name, ty, value } => {
                self.indent(level);
                self.out.push_str("var ");
                self.out.push_str(&name.name);
                if let Some(t) = ty {
                    let _ = write!(self.out, ": {}", render_type(t));
                }
                self.out.push_str(" = ");
                let rendered = self.render_expr(value, level);
                self.out.push_str(&rendered);
                self.emit_inline_comment_after(st.span);
                self.out.push('\n');
            }
            StmtKind::Assert(e) => {
                self.indent(level);
                let rendered = self.render_expr(e, level);
                let _ = write!(self.out, "assert {rendered}");
                self.emit_inline_comment_after(st.span);
                self.out.push('\n');
            }
            StmtKind::Return { value, guard } => {
                self.indent(level);
                self.out.push_str("return");
                if let Some(v) = value {
                    let rendered = self.render_expr(v, level);
                    let _ = write!(self.out, " {rendered}");
                }
                if let Some(g) = guard {
                    let rendered = self.render_expr(g, level);
                    let _ = write!(self.out, " if {rendered}");
                }
                self.emit_inline_comment_after(st.span);
                self.out.push('\n');
            }
            StmtKind::Break { guard } => {
                self.indent(level);
                self.out.push_str("break");
                if let Some(g) = guard {
                    let rendered = self.render_expr(g, level);
                    let _ = write!(self.out, " if {rendered}");
                }
                self.emit_inline_comment_after(st.span);
                self.out.push('\n');
            }
            StmtKind::Continue { guard } => {
                self.indent(level);
                self.out.push_str("continue");
                if let Some(g) = guard {
                    let rendered = self.render_expr(g, level);
                    let _ = write!(self.out, " if {rendered}");
                }
                self.emit_inline_comment_after(st.span);
                self.out.push('\n');
            }
            StmtKind::Stop(e) => {
                self.indent(level);
                self.out.push_str("stop");
                if let Some(ex) = e {
                    let rendered = self.render_expr(ex, level);
                    let _ = write!(self.out, " {rendered}");
                }
                self.emit_inline_comment_after(st.span);
                self.out.push('\n');
            }
            StmtKind::For { target, iter, body } => {
                self.indent(level);
                let it_str = self.render_expr(iter, level);
                let _ = writeln!(self.out, "for {} in {it_str}", render_for_target(target));
                self.format_stmts(body, level + 1, st.span.end);
                self.indent(level);
                self.out.push_str("end\n");
            }
            StmtKind::While { cond, body } => {
                self.indent(level);
                let c_str = self.render_expr(cond, level);
                let _ = writeln!(self.out, "while {c_str}");
                self.format_stmts(body, level + 1, st.span.end);
                self.indent(level);
                self.out.push_str("end\n");
            }
            StmtKind::Assign { lhs, rhs } => {
                self.indent(level);
                let l = self.render_expr(lhs, level);
                let r = self.render_expr(rhs, level);
                let _ = write!(self.out, "{l} = {r}");
                self.emit_inline_comment_after(st.span);
                self.out.push('\n');
            }
            StmtKind::Expr(e) => {
                self.indent(level);
                let r = self.render_expr(e, level);
                self.out.push_str(&r);
                self.emit_inline_comment_after(st.span);
                self.out.push('\n');
            }
        }
    }

    fn render_expr(&mut self, expr: &Expr, level: usize) -> String {
        match &expr.kind {
            ExprKind::Int(s)
            | ExprKind::Decimal(s)
            | ExprKind::Date(s)
            | ExprKind::Timestamp(s)
            | ExprKind::Ident(s)
            | ExprKind::CapName(s) => s.clone(),
            ExprKind::Atom(s) => format!(":{s}"),
            ExprKind::Bool(b) => if *b { "true" } else { "false" }.to_string(),
            ExprKind::None => "none".to_string(),
            ExprKind::Underscore => "_".to_string(),
            ExprKind::DotSelf => ".".to_string(),
            ExprKind::DotField(m) => format!(".{}", m.name),
            ExprKind::Text { multiline, raw, .. } => {
                if *multiline {
                    format!("\"\"\"{raw}\"\"\"")
                } else {
                    format!("\"{raw}\"")
                }
            }
            ExprKind::InterpText { parts, multiline } => {
                let delim = if *multiline { "\"\"\"" } else { "\"" };
                let mut s = String::from(delim);
                for part in parts {
                    match part {
                        InterpPart::Literal { raw, .. } => s.push_str(raw),
                        InterpPart::Expr(ex) => {
                            let inner = self.render_expr(ex, level);
                            let _ = write!(s, "#{{{inner}}}");
                        }
                    }
                }
                s.push_str(delim);
                s
            }
            ExprKind::Paren(inner) => format!("({})", self.render_expr(inner, level)),
            ExprKind::Tuple(elems) => {
                let items: Vec<String> = elems.iter().map(|e| self.render_expr(e, level)).collect();
                format!("({})", items.join(", "))
            }
            ExprKind::List(elems) => {
                let items: Vec<String> = elems.iter().map(|e| self.render_expr(e, level)).collect();
                format!("[{}]", items.join(", "))
            }
            ExprKind::Map(entries) => {
                if entries.is_empty() {
                    return "{}".to_string();
                }
                let items: Vec<String> = entries
                    .iter()
                    .map(|(k, v)| {
                        format!(
                            "{}: {}",
                            self.render_expr(k, level),
                            self.render_expr(v, level)
                        )
                    })
                    .collect();
                let single = format!("{{{}}}", items.join(", "));
                if single.len() <= LINE_WIDTH && !single.contains('\n') {
                    single
                } else {
                    let pad = " ".repeat((level + 1) * 2);
                    let close_pad = " ".repeat(level * 2);
                    let mut out = String::from("{\n");
                    for (i, it) in items.iter().enumerate() {
                        out.push_str(&pad);
                        out.push_str(it);
                        if i + 1 < items.len() {
                            out.push(',');
                        }
                        out.push('\n');
                    }
                    out.push_str(&close_pad);
                    out.push('}');
                    out
                }
            }
            ExprKind::Unary { op, expr: inner } => {
                let s = self.render_expr(inner, level);
                match op {
                    UnaryOp::Neg => format!("-{s}"),
                    UnaryOp::Not => format!("not {s}"),
                    UnaryOp::Try => format!("try {s}"),
                }
            }
            ExprKind::Binary {
                op: BinOp::Pipe,
                lhs,
                rhs,
            } => {
                // Collect full left-associative pipe chain for clean vertical alignment.
                let mut stages = Vec::new();
                collect_pipe_chain(lhs, &mut stages);
                stages.push(rhs);
                let first = self.render_expr(stages[0], level);
                let pipe_pad = " ".repeat((level + 1) * 2);
                if stages.len() == 2
                    && !self.has_comment_between(stages[0].span.end, stages[1].span.start)
                {
                    let saved_c_idx = self.c_idx;
                    let second = self.render_expr(stages[1], level + 1);
                    let single = format!("{first} |> {second}");
                    if single.len() <= LINE_WIDTH && !single.contains('\n') {
                        return single;
                    }
                    self.c_idx = saved_c_idx;
                }
                let mut out = first;
                for stage in &stages[1..] {
                    self.append_comments_inline(&mut out, stage.span.start, level + 1);
                    let rendered = self.render_expr(stage, level + 1);
                    let _ = write!(out, "\n{pipe_pad}|> {rendered}");
                }
                out
            }
            ExprKind::Binary { op, lhs, rhs } => {
                // Flatten arbitrarily long left-associative binary chains iteratively so
                // 200,000+ term expressions never overflow the call stack.
                let mut chain: Vec<(BinOp, &Expr)> = Vec::new();
                chain.push((*op, rhs.as_ref()));
                let mut cur = lhs.as_ref();
                while let ExprKind::Binary {
                    op: lop,
                    lhs: llhs,
                    rhs: lrhs,
                } = &cur.kind
                {
                    if *lop == BinOp::Pipe {
                        break;
                    }
                    chain.push((*lop, lrhs.as_ref()));
                    cur = llhs.as_ref();
                }
                let mut out = self.render_expr(cur, level);
                while let Some((bop, r)) = chain.pop() {
                    let rs = self.render_expr(r, level);
                    out.push(' ');
                    out.push_str(bop.as_str());
                    out.push(' ');
                    out.push_str(&rs);
                }
                out
            }
            ExprKind::Field { .. } | ExprKind::Call { .. } | ExprKind::Index { .. } => {
                // Iteratively flatten arbitrarily long postfix chains (`xs.append(1).append(1)...`,
                // `f()()()...`, `m[1][1]...`, `a.b.c...`) so 200,000+ links format in O(1) stack.
                enum PostfixFmt<'b> {
                    Field(&'b str),
                    Call(&'b [CallArg], u32),
                    Index(&'b Expr),
                }
                let mut steps: Vec<PostfixFmt<'_>> = Vec::new();
                let mut cur = expr;
                loop {
                    match &cur.kind {
                        ExprKind::Field { receiver, member } => {
                            steps.push(PostfixFmt::Field(member.name.as_str()));
                            cur = receiver.as_ref();
                        }
                        ExprKind::Call { callee, args } => {
                            steps.push(PostfixFmt::Call(args.as_slice(), callee.span.end));
                            cur = callee.as_ref();
                        }
                        ExprKind::Index { target, index } => {
                            steps.push(PostfixFmt::Index(index.as_ref()));
                            cur = target.as_ref();
                        }
                        _ => break,
                    }
                }
                let mut out = self.render_expr(cur, level);
                while let Some(step) = steps.pop() {
                    match step {
                        PostfixFmt::Field(m) => {
                            out.push('.');
                            out.push_str(m);
                        }
                        PostfixFmt::Call(args, callee_end) => {
                            if args.is_empty() {
                                out.push_str("()");
                                continue;
                            }
                            let has_internal_comment = args
                                .iter()
                                .any(|a| self.has_comment_between(callee_end, a.span().start));
                            let mut fitted_inline = false;
                            if !has_internal_comment {
                                let saved_c_idx = self.c_idx;
                                let rendered_inline: Vec<String> = args
                                    .iter()
                                    .map(|a| self.render_call_arg(a, level + 1))
                                    .collect();
                                let inline_args = rendered_inline.join(", ");
                                let last_line_len =
                                    out.rsplit('\n').next().map_or(out.len(), str::len);
                                if last_line_len + inline_args.len() + 2 <= LINE_WIDTH
                                    && !inline_args.contains('\n')
                                {
                                    out.push('(');
                                    out.push_str(&inline_args);
                                    out.push(')');
                                    fitted_inline = true;
                                } else {
                                    self.c_idx = saved_c_idx;
                                }
                            }
                            if !fitted_inline {
                                let pad = " ".repeat((level + 1) * 2);
                                let close_pad = " ".repeat(level * 2);
                                out.push_str("(\n");
                                for (i, arg) in args.iter().enumerate() {
                                    self.append_comments_inline(
                                        &mut out,
                                        arg.span().start,
                                        level + 1,
                                    );
                                    let rendered = self.render_call_arg(arg, level + 1);
                                    out.push_str(&pad);
                                    out.push_str(&rendered);
                                    if i + 1 < args.len() {
                                        out.push(',');
                                    }
                                    out.push('\n');
                                }
                                out.push_str(&close_pad);
                                out.push(')');
                            }
                        }
                        PostfixFmt::Index(idx) => {
                            let rendered = self.render_expr(idx, level);
                            let _ = write!(out, "[{rendered}]");
                        }
                    }
                }
                out
            }
            ExprKind::IfInline {
                cond,
                then_expr,
                else_ifs,
                else_expr,
            } => {
                let c = self.render_expr(cond, level);
                let t = self.render_expr(then_expr, level);
                let saved_c_idx = self.c_idx;
                let mut single = format!("if {c}: {t}");
                for (ec, et) in else_ifs {
                    let _ = write!(
                        single,
                        " else if {}: {}",
                        self.render_expr(ec, level),
                        self.render_expr(et, level)
                    );
                }
                let e = self.render_expr(else_expr, level);
                let _ = write!(single, " else: {e}");
                if single.len() <= LINE_WIDTH && !single.contains('\n') {
                    single
                } else {
                    self.c_idx = saved_c_idx;
                    let pad = " ".repeat((level + 1) * 2);
                    let mut out = format!("if {c}: {t}");
                    for (ec, et) in else_ifs {
                        let _ = write!(
                            out,
                            "\n{pad}else if {}: {}",
                            self.render_expr(ec, level + 1),
                            self.render_expr(et, level + 1)
                        );
                    }
                    let e_multi = self.render_expr(else_expr, level + 1);
                    let _ = write!(out, "\n{pad}else: {e_multi}");
                    out
                }
            }
            ExprKind::IfBlock {
                cond,
                then_body,
                else_ifs,
                else_body,
            } => {
                let pad = " ".repeat(level * 2);
                let mut sub = Formatter {
                    comments: self.comments,
                    blank_lines: self.blank_lines,
                    c_idx: self.c_idx,
                    out: String::new(),
                };
                let c_str = sub.render_expr(cond, level);
                let _ = writeln!(sub.out, "if {c_str}");
                let then_end = else_ifs
                    .first()
                    .map(|b| b.else_kw.start)
                    .or_else(|| else_body.as_ref().map(|b| b.else_kw.start))
                    .unwrap_or(expr.span.end);
                sub.format_stmts(then_body, level + 1, then_end);
                for (i, branch) in else_ifs.iter().enumerate() {
                    let _ = write!(sub.out, "{pad}else if ");
                    let ecs = sub.render_expr(&branch.cond, level);
                    let _ = writeln!(sub.out, "{ecs}");
                    let next_end = else_ifs
                        .get(i + 1)
                        .map(|nb| nb.else_kw.start)
                        .or_else(|| else_body.as_ref().map(|b| b.else_kw.start))
                        .unwrap_or(expr.span.end);
                    sub.format_stmts(&branch.body, level + 1, next_end);
                }
                if let Some(eb) = else_body {
                    let _ = writeln!(sub.out, "{pad}else");
                    sub.format_stmts(&eb.body, level + 1, expr.span.end);
                }
                let _ = write!(sub.out, "{pad}end");
                self.c_idx = sub.c_idx;
                sub.out
            }
            ExprKind::Case { scrut, lines } => {
                let pad = " ".repeat(level * 2);
                let mut sub = Formatter {
                    comments: self.comments,
                    blank_lines: self.blank_lines,
                    c_idx: self.c_idx,
                    out: String::new(),
                };
                let sc = sub.render_expr(scrut, level);
                let _ = writeln!(sub.out, "case {sc}");
                for line in lines {
                    match line {
                        CaseLine::ArmHeader { pattern, span } => {
                            sub.emit_comments_before(span.start, level + 1, false);
                            sub.indent(level + 1);
                            let pat = sub.render_expr(pattern, level + 1);
                            let _ = writeln!(sub.out, "{pat}:");
                        }
                        CaseLine::ArmInline {
                            pattern,
                            expr: arm_expr,
                            span,
                        } => {
                            sub.emit_comments_before(span.start, level + 1, false);
                            sub.indent(level + 1);
                            let pat = sub.render_expr(pattern, level + 1);
                            let val = sub.render_expr(arm_expr, level + 1);
                            let _ = writeln!(sub.out, "{pat}: {val}");
                        }
                        CaseLine::Stmt(st) => {
                            sub.emit_comments_before(st.span.start, level + 2, false);
                            sub.format_stmt(st, level + 2);
                        }
                    }
                }
                sub.emit_comments_before(expr.span.end, level + 1, false);
                let _ = write!(sub.out, "{pad}end");
                self.c_idx = sub.c_idx;
                sub.out
            }
            ExprKind::Lambda { params, body } => {
                let plist: Vec<&str> = params
                    .iter()
                    .map(|p| match p {
                        LambdaParam::Name(n) => n.name.as_str(),
                        LambdaParam::Wildcard(_) => "_",
                    })
                    .collect();
                match body {
                    LambdaBody::Expr(ex) => {
                        let rendered = self.render_expr(ex, level);
                        format!("fn ({}) {rendered} end", plist.join(", "))
                    }
                    LambdaBody::Block(stmts) => {
                        let pad = " ".repeat(level * 2);
                        let mut sub = Formatter {
                            comments: self.comments,
                            blank_lines: self.blank_lines,
                            c_idx: self.c_idx,
                            out: String::new(),
                        };
                        let _ = writeln!(sub.out, "fn ({})", plist.join(", "));
                        sub.format_stmts(stmts, level + 1, expr.span.end);
                        let _ = write!(sub.out, "{pad}end");
                        self.c_idx = sub.c_idx;
                        sub.out
                    }
                }
            }
            ExprKind::TableLit { headers, rows } => {
                let row_pad = " ".repeat((level + 1) * 2);
                let close_pad = " ".repeat(level * 2);
                let mut rendered_rows: Vec<Vec<String>> = Vec::with_capacity(rows.len());
                let mut widths: Vec<usize> = headers.iter().map(|h| h.name.len()).collect();
                for row in rows {
                    let mut r_cells = Vec::with_capacity(row.len());
                    for (ci, cell) in row.iter().enumerate() {
                        let s = self.render_expr(cell, level + 1);
                        if ci < widths.len() {
                            widths[ci] = widths[ci].max(s.len());
                        } else {
                            widths.push(s.len());
                        }
                        r_cells.push(s);
                    }
                    rendered_rows.push(r_cells);
                }
                let mut out = String::from("table\n");
                out.push_str(&row_pad);
                out.push('|');
                for (ci, h) in headers.iter().enumerate() {
                    let w = widths[ci];
                    let _ = write!(out, " {:<w$} |", h.name);
                }
                out.push('\n');
                for r_cells in &rendered_rows {
                    out.push_str(&row_pad);
                    out.push('|');
                    for (ci, cell) in r_cells.iter().enumerate() {
                        let w = widths.get(ci).copied().unwrap_or(cell.len());
                        let _ = write!(out, " {cell:<w$} |");
                    }
                    out.push('\n');
                }
                out.push_str(&close_pad);
                out.push_str("end");
                out
            }
        }
    }

    fn render_call_arg(&mut self, arg: &CallArg, level: usize) -> String {
        match arg {
            CallArg::Positional(e) => self.render_expr(e, level),
            CallArg::Named { name, value, .. } => {
                format!("{}: {}", name.name, self.render_expr(value, level))
            }
        }
    }

    fn has_comment_between(&self, start: u32, end: u32) -> bool {
        self.comments
            .get(self.c_idx)
            .is_some_and(|c| c.span.start >= start && c.span.start < end)
    }

    fn append_comments_inline(&mut self, out: &mut String, before_offset: u32, level: usize) {
        let pad = " ".repeat(level * 2);
        while let Some(c) = self.comments.get(self.c_idx) {
            if c.span.start >= before_offset {
                break;
            }
            if !out.ends_with('\n') {
                out.push('\n');
            }
            out.push_str(&pad);
            out.push_str(&c.text);
            out.push('\n');
            self.c_idx += 1;
        }
    }
}

fn collect_pipe_chain<'a>(expr: &'a Expr, out: &mut Vec<&'a Expr>) {
    let mut stack = Vec::new();
    let mut cur = expr;
    while let ExprKind::Binary {
        op: BinOp::Pipe,
        lhs,
        rhs,
    } = &cur.kind
    {
        stack.push(rhs.as_ref());
        cur = lhs.as_ref();
    }
    out.push(cur);
    while let Some(s) = stack.pop() {
        out.push(s);
    }
}

fn render_tags(tags: &[SpannedName]) -> String {
    let names: Vec<&str> = tags.iter().map(|t| t.name.as_str()).collect();
    format!("[{}]", names.join(", "))
}

fn render_param(p: &Param) -> String {
    let mut s = format!("{}: {}", p.name.name, render_type(&p.ty));
    if !p.tags.is_empty() {
        s.push(' ');
        s.push_str(&render_tags(&p.tags));
    }
    s
}

fn render_type(ty: &TypeExpr) -> String {
    let mut s = match &ty.kind {
        TypeKind::Named { name, args } => {
            if args.is_empty() {
                name.name.clone()
            } else {
                let parts: Vec<String> = args.iter().map(render_type_arg).collect();
                format!("{}({})", name.name, parts.join(", "))
            }
        }
        TypeKind::Tuple(elems) => {
            let parts: Vec<String> = elems.iter().map(render_type).collect();
            format!("({})", parts.join(", "))
        }
    };
    if ty.optional {
        s.push('?');
    }
    s
}

fn render_type_indented(ty: &TypeExpr, level: usize) -> String {
    let single = render_type(ty);
    if single.len() <= LINE_WIDTH {
        return single;
    }
    if let TypeKind::Named { name, args } = &ty.kind
        && args.len() >= 3
    {
        let pad = " ".repeat((level + 1) * 2);
        let close_pad = " ".repeat(level * 2);
        let mut out = format!("{}(\n", name.name);
        for (i, a) in args.iter().enumerate() {
            out.push_str(&pad);
            out.push_str(&render_type_arg(a));
            if i + 1 < args.len() {
                out.push(',');
            }
            out.push('\n');
        }
        out.push_str(&close_pad);
        out.push(')');
        if ty.optional {
            out.push('?');
        }
        return out;
    }
    single
}

fn render_type_arg(arg: &TypeArg) -> String {
    match arg {
        TypeArg::Type(t) => render_type(t),
        TypeArg::Text { raw, .. } => format!("\"{raw}\""),
        TypeArg::NamedType { name, ty, tags, .. } => {
            let mut s = format!("{}: {}", name.name, render_type(ty));
            if !tags.is_empty() {
                s.push(' ');
                s.push_str(&render_tags(tags));
            }
            s
        }
        TypeArg::NamedTags { name, tags, .. } => {
            format!("{}: {}", name.name, render_tags(tags))
        }
    }
}

fn render_for_target(t: &ForTarget) -> String {
    match t {
        ForTarget::Name(n) => n.name.clone(),
        ForTarget::Wildcard(_) => "_".to_string(),
        ForTarget::Tuple(ts, _) => {
            let parts: Vec<String> = ts.iter().map(render_for_target).collect();
            format!("({})", parts.join(", "))
        }
    }
}
