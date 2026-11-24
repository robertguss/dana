//! Lossless Surface AST for Dana Language Reference v0.1.
//!
//! Every node carries a [`Span`] and preserves enough syntactic detail for canonical
//! 2-space formatting (`dana format`) as well as exact type/privacy checking and Core IR lowering.
//! Recursive nodes (`Expr`, `Stmt`, `TypeExpr`) implement iterative `Drop` to avoid
//! drop-time stack overflow on deep inputs.

use crate::base::Span;
use crate::syntax::token::Comment;

/// A spanned identifier string.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SpannedName {
    pub name: String,
    pub span: Span,
}

impl SpannedName {
    #[must_use]
    pub fn new(name: impl Into<String>, span: Span) -> Self {
        Self {
            name: name.into(),
            span,
        }
    }
}

/// Complete parsed `.dana` module file.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Module {
    pub header: ModuleHeader,
    pub items: Vec<TopItem>,
    pub comments: Vec<Comment>,
    pub span: Span,
}

/// Parsed Dana code fragment (used for Reference doc tests and `--fragment` parity checks).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Fragment {
    pub header: Option<ModuleHeader>,
    pub items: Vec<FragmentItem>,
    pub comments: Vec<Comment>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ModuleHeader {
    pub path: Vec<SpannedName>,
    pub expose: Option<ExposeDecl>,
    pub uses: Vec<UseDecl>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExposeDecl {
    pub items: Vec<ExposeItem>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExposeItem {
    Value(SpannedName),
    Type(SpannedName),
    TypeAll(SpannedName),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct UseDecl {
    pub path: Vec<SpannedName>,
    pub items: Option<Vec<SpannedName>>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TopItem {
    Tag(TagDecl),
    Schema(SchemaDecl),
    Struct(StructDecl),
    Enum(EnumDecl),
    Const(ConstDecl),
    Fn(FnDecl),
    Test(TestDecl),
}

impl TopItem {
    #[must_use]
    pub const fn span(&self) -> Span {
        match self {
            Self::Tag(d) => d.span,
            Self::Schema(d) => d.span,
            Self::Struct(d) => d.span,
            Self::Enum(d) => d.span,
            Self::Const(d) => d.span,
            Self::Fn(d) => d.span,
            Self::Test(d) => d.span,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FragmentItem {
    Top(TopItem),
    Stmt(Stmt),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TagDecl {
    pub name: SpannedName,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SchemaDecl {
    pub name: SpannedName,
    pub tags: Vec<SpannedName>,
    pub fields: Vec<SchemaField>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SchemaField {
    pub name: SpannedName,
    pub ty: TypeExpr,
    pub tags: Vec<SpannedName>,
    pub constraint: Option<Expr>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StructDecl {
    pub name: SpannedName,
    pub fields: Vec<StructField>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StructField {
    pub name: SpannedName,
    pub ty: TypeExpr,
    pub tags: Vec<SpannedName>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EnumDecl {
    pub name: SpannedName,
    pub variants: Vec<EnumVariant>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EnumVariant {
    pub name: SpannedName,
    pub fields: Vec<VariantField>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VariantField {
    Named {
        name: SpannedName,
        ty: TypeExpr,
        tags: Vec<SpannedName>,
        span: Span,
    },
    Positional {
        ty: TypeExpr,
        span: Span,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConstDecl {
    pub name: SpannedName,
    pub ty: Option<TypeExpr>,
    pub value: Expr,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FnDecl {
    pub name: SpannedName,
    pub params: Vec<Param>,
    pub ret_ty: Option<ReturnType>,
    pub body: Vec<FnStmt>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Param {
    pub name: SpannedName,
    pub ty: TypeExpr,
    pub tags: Vec<SpannedName>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReturnType {
    pub ty: TypeExpr,
    pub tags: Vec<SpannedName>,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FnStmt {
    Examples { stmts: Vec<Stmt>, span: Span },
    Promise { expr: Expr, span: Span },
    Stmt(Stmt),
}

impl FnStmt {
    #[must_use]
    pub const fn span(&self) -> Span {
        match self {
            Self::Examples { span, .. } | Self::Promise { span, .. } => *span,
            Self::Stmt(s) => s.span,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TestDecl {
    pub name: String,
    pub name_raw: String,
    pub body: Vec<Stmt>,
    pub span: Span,
}

// ---------------------------------------------------------------------------
// Type Expressions
// ---------------------------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TypeExpr {
    pub kind: TypeKind,
    pub optional: bool,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TypeKind {
    Named {
        name: SpannedName,
        args: Vec<TypeArg>,
    },
    Tuple(Vec<TypeExpr>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TypeArg {
    Type(TypeExpr),
    Text {
        value: String,
        raw: String,
        span: Span,
    },
    NamedType {
        name: SpannedName,
        ty: TypeExpr,
        tags: Vec<SpannedName>,
        span: Span,
    },
    NamedTags {
        name: SpannedName,
        tags: Vec<SpannedName>,
        span: Span,
    },
}

// ---------------------------------------------------------------------------
// Statements
// ---------------------------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Stmt {
    pub kind: StmtKind,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StmtKind {
    Var {
        name: SpannedName,
        ty: Option<TypeExpr>,
        value: Expr,
    },
    Assert(Expr),
    Return {
        value: Option<Expr>,
        guard: Option<Expr>,
    },
    Break {
        guard: Option<Expr>,
    },
    Continue {
        guard: Option<Expr>,
    },
    Stop(Option<Expr>),
    For {
        target: ForTarget,
        iter: Expr,
        body: Vec<Stmt>,
    },
    While {
        cond: Expr,
        body: Vec<Stmt>,
    },
    Assign {
        lhs: Expr,
        rhs: Expr,
    },
    Expr(Expr),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ForTarget {
    Name(SpannedName),
    Wildcard(Span),
    Tuple(Vec<ForTarget>, Span),
}

// ---------------------------------------------------------------------------
// Expressions
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum BinOp {
    Pipe,
    Or,
    And,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    Is,
    Coalesce,
    Add,
    Sub,
    Mul,
    Div,
    Mod,
}

impl BinOp {
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Pipe => "|>",
            Self::Or => "or",
            Self::And => "and",
            Self::Eq => "==",
            Self::Ne => "!=",
            Self::Lt => "<",
            Self::Le => "<=",
            Self::Gt => ">",
            Self::Ge => ">=",
            Self::Is => "is",
            Self::Coalesce => "??",
            Self::Add => "+",
            Self::Sub => "-",
            Self::Mul => "*",
            Self::Div => "/",
            Self::Mod => "%",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum UnaryOp {
    Not,
    Neg,
    Try,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExprKind {
    Int(String),
    Decimal(String),
    Date(String),
    Timestamp(String),
    Text {
        value: String,
        multiline: bool,
        raw: String,
    },
    InterpText {
        parts: Vec<InterpPart>,
        multiline: bool,
    },
    Atom(String),
    Bool(bool),
    None,
    Ident(String),
    CapName(String),
    Underscore,
    /// Leading `.col` or `.empty?` column / row-self field reference.
    DotField(SpannedName),
    /// Standalone `.` referring to the column value in `where` / `promise`.
    DotSelf,
    Paren(Box<Expr>),
    Tuple(Vec<Expr>),
    List(Vec<Expr>),
    Map(Vec<(Expr, Expr)>),
    Unary {
        op: UnaryOp,
        expr: Box<Expr>,
    },
    Binary {
        op: BinOp,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },
    Field {
        receiver: Box<Expr>,
        member: SpannedName,
    },
    Call {
        callee: Box<Expr>,
        args: Vec<CallArg>,
    },
    Index {
        target: Box<Expr>,
        index: Box<Expr>,
    },
    IfInline {
        cond: Box<Expr>,
        then_expr: Box<Expr>,
        else_ifs: Vec<(Expr, Expr)>,
        else_expr: Box<Expr>,
    },
    IfBlock {
        cond: Box<Expr>,
        then_body: Vec<Stmt>,
        else_ifs: Vec<(Expr, Vec<Stmt>)>,
        else_body: Option<Vec<Stmt>>,
    },
    Case {
        scrut: Box<Expr>,
        lines: Vec<CaseLine>,
    },
    Lambda {
        params: Vec<LambdaParam>,
        body: LambdaBody,
    },
    TableLit {
        headers: Vec<SpannedName>,
        rows: Vec<Vec<Expr>>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InterpPart {
    Literal { value: String, raw: String },
    Expr(Expr),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CallArg {
    Positional(Expr),
    Named {
        name: SpannedName,
        value: Expr,
        span: Span,
    },
}

impl CallArg {
    #[must_use]
    pub const fn span(&self) -> Span {
        match self {
            Self::Positional(e) => e.span,
            Self::Named { span, .. } => *span,
        }
    }
}

/// Exact flat `case_line` representation mirroring `grammar/dana.y:572-576`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CaseLine {
    /// `pattern:` followed by newline (starts a multi-statement arm).
    ArmHeader { pattern: Expr, span: Span },
    /// `pattern: expr` single-line arm.
    ArmInline {
        pattern: Expr,
        expr: Expr,
        span: Span,
    },
    /// Statement belonging to the preceding `ArmHeader`.
    Stmt(Stmt),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LambdaParam {
    Name(SpannedName),
    Wildcard(Span),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LambdaBody {
    Expr(Box<Expr>),
    Block(Vec<Stmt>),
}

// ---------------------------------------------------------------------------
// Iterative Drop for Recursive AST Nodes (Prevents Drop-Time Stack Overflow)
// ---------------------------------------------------------------------------

enum AstDropNode {
    Expr(Expr),
    Stmt(Stmt),
    Type(TypeExpr),
}

fn dummy_expr() -> Expr {
    Expr {
        kind: ExprKind::None,
        span: Span::default(),
    }
}

fn push_expr_children(e: &mut Expr, stack: &mut Vec<AstDropNode>) {
    match &mut e.kind {
        ExprKind::Paren(inner) | ExprKind::Unary { expr: inner, .. } => {
            stack.push(AstDropNode::Expr(std::mem::replace(
                inner.as_mut(),
                dummy_expr(),
            )));
        }
        ExprKind::Binary { lhs, rhs, .. } => {
            stack.push(AstDropNode::Expr(std::mem::replace(
                lhs.as_mut(),
                dummy_expr(),
            )));
            stack.push(AstDropNode::Expr(std::mem::replace(
                rhs.as_mut(),
                dummy_expr(),
            )));
        }
        ExprKind::Field { receiver, .. } => {
            stack.push(AstDropNode::Expr(std::mem::replace(
                receiver.as_mut(),
                dummy_expr(),
            )));
        }
        ExprKind::Index { target, index } => {
            stack.push(AstDropNode::Expr(std::mem::replace(
                target.as_mut(),
                dummy_expr(),
            )));
            stack.push(AstDropNode::Expr(std::mem::replace(
                index.as_mut(),
                dummy_expr(),
            )));
        }
        ExprKind::Tuple(xs) | ExprKind::List(xs) => {
            for x in std::mem::take(xs) {
                stack.push(AstDropNode::Expr(x));
            }
        }
        ExprKind::Map(pairs) => {
            for (k, v) in std::mem::take(pairs) {
                stack.push(AstDropNode::Expr(k));
                stack.push(AstDropNode::Expr(v));
            }
        }
        ExprKind::InterpText { parts, .. } => {
            for p in std::mem::take(parts) {
                if let InterpPart::Expr(ex) = p {
                    stack.push(AstDropNode::Expr(ex));
                }
            }
        }
        ExprKind::Call { callee, args } => {
            stack.push(AstDropNode::Expr(std::mem::replace(
                callee.as_mut(),
                dummy_expr(),
            )));
            for a in std::mem::take(args) {
                match a {
                    CallArg::Positional(ex) | CallArg::Named { value: ex, .. } => {
                        stack.push(AstDropNode::Expr(ex));
                    }
                }
            }
        }
        ExprKind::IfInline {
            cond,
            then_expr,
            else_ifs,
            else_expr,
        } => {
            stack.push(AstDropNode::Expr(std::mem::replace(
                cond.as_mut(),
                dummy_expr(),
            )));
            stack.push(AstDropNode::Expr(std::mem::replace(
                then_expr.as_mut(),
                dummy_expr(),
            )));
            for (c, t) in std::mem::take(else_ifs) {
                stack.push(AstDropNode::Expr(c));
                stack.push(AstDropNode::Expr(t));
            }
            stack.push(AstDropNode::Expr(std::mem::replace(
                else_expr.as_mut(),
                dummy_expr(),
            )));
        }
        ExprKind::IfBlock {
            cond,
            then_body,
            else_ifs,
            else_body,
        } => {
            stack.push(AstDropNode::Expr(std::mem::replace(
                cond.as_mut(),
                dummy_expr(),
            )));
            for s in std::mem::take(then_body) {
                stack.push(AstDropNode::Stmt(s));
            }
            for (c, body) in std::mem::take(else_ifs) {
                stack.push(AstDropNode::Expr(c));
                for s in body {
                    stack.push(AstDropNode::Stmt(s));
                }
            }
            if let Some(body) = else_body.take() {
                for s in body {
                    stack.push(AstDropNode::Stmt(s));
                }
            }
        }
        ExprKind::Case { scrut, lines } => {
            stack.push(AstDropNode::Expr(std::mem::replace(
                scrut.as_mut(),
                dummy_expr(),
            )));
            for line in std::mem::take(lines) {
                match line {
                    CaseLine::ArmHeader { pattern, .. } => stack.push(AstDropNode::Expr(pattern)),
                    CaseLine::ArmInline { pattern, expr, .. } => {
                        stack.push(AstDropNode::Expr(pattern));
                        stack.push(AstDropNode::Expr(expr));
                    }
                    CaseLine::Stmt(s) => stack.push(AstDropNode::Stmt(s)),
                }
            }
        }
        ExprKind::Lambda { body, .. } => match body {
            LambdaBody::Expr(ex) => {
                stack.push(AstDropNode::Expr(std::mem::replace(
                    ex.as_mut(),
                    dummy_expr(),
                )));
            }
            LambdaBody::Block(stmts) => {
                for s in std::mem::take(stmts) {
                    stack.push(AstDropNode::Stmt(s));
                }
            }
        },
        ExprKind::TableLit { rows, .. } => {
            for row in std::mem::take(rows) {
                for cell in row {
                    stack.push(AstDropNode::Expr(cell));
                }
            }
        }
        ExprKind::Int(_)
        | ExprKind::Decimal(_)
        | ExprKind::Date(_)
        | ExprKind::Timestamp(_)
        | ExprKind::Text { .. }
        | ExprKind::Atom(_)
        | ExprKind::Bool(_)
        | ExprKind::None
        | ExprKind::Ident(_)
        | ExprKind::CapName(_)
        | ExprKind::Underscore
        | ExprKind::DotField(_)
        | ExprKind::DotSelf => {}
    }
}

fn push_stmt_children(s: &mut Stmt, stack: &mut Vec<AstDropNode>) {
    match &mut s.kind {
        StmtKind::Var { ty, value, .. } => {
            if let Some(t) = ty.take() {
                stack.push(AstDropNode::Type(t));
            }
            stack.push(AstDropNode::Expr(std::mem::replace(value, dummy_expr())));
        }
        StmtKind::Assert(e) | StmtKind::Expr(e) => {
            stack.push(AstDropNode::Expr(std::mem::replace(e, dummy_expr())));
        }
        StmtKind::Return { value, guard } => {
            if let Some(v) = value.take() {
                stack.push(AstDropNode::Expr(v));
            }
            if let Some(g) = guard.take() {
                stack.push(AstDropNode::Expr(g));
            }
        }
        StmtKind::Break { guard } | StmtKind::Continue { guard } => {
            if let Some(g) = guard.take() {
                stack.push(AstDropNode::Expr(g));
            }
        }
        StmtKind::Stop(opt) => {
            if let Some(e) = opt.take() {
                stack.push(AstDropNode::Expr(e));
            }
        }
        StmtKind::For { iter, body, .. } => {
            stack.push(AstDropNode::Expr(std::mem::replace(iter, dummy_expr())));
            for st in std::mem::take(body) {
                stack.push(AstDropNode::Stmt(st));
            }
        }
        StmtKind::While { cond, body } => {
            stack.push(AstDropNode::Expr(std::mem::replace(cond, dummy_expr())));
            for st in std::mem::take(body) {
                stack.push(AstDropNode::Stmt(st));
            }
        }
        StmtKind::Assign { lhs, rhs } => {
            stack.push(AstDropNode::Expr(std::mem::replace(lhs, dummy_expr())));
            stack.push(AstDropNode::Expr(std::mem::replace(rhs, dummy_expr())));
        }
    }
}

fn push_type_children(t: &mut TypeExpr, stack: &mut Vec<AstDropNode>) {
    match &mut t.kind {
        TypeKind::Named { args, .. } => {
            for a in std::mem::take(args) {
                match a {
                    TypeArg::Type(ty) | TypeArg::NamedType { ty, .. } => {
                        stack.push(AstDropNode::Type(ty));
                    }
                    TypeArg::Text { .. } | TypeArg::NamedTags { .. } => {}
                }
            }
        }
        TypeKind::Tuple(ts) => {
            for ty in std::mem::take(ts) {
                stack.push(AstDropNode::Type(ty));
            }
        }
    }
}

fn drain_ast_drop(mut stack: Vec<AstDropNode>) {
    while let Some(mut node) = stack.pop() {
        match &mut node {
            AstDropNode::Expr(e) => push_expr_children(e, &mut stack),
            AstDropNode::Stmt(s) => push_stmt_children(s, &mut stack),
            AstDropNode::Type(t) => push_type_children(t, &mut stack),
        }
    }
}

impl Drop for Expr {
    fn drop(&mut self) {
        let mut stack = Vec::new();
        push_expr_children(self, &mut stack);
        drain_ast_drop(stack);
    }
}

impl Drop for Stmt {
    fn drop(&mut self) {
        let mut stack = Vec::new();
        push_stmt_children(self, &mut stack);
        drain_ast_drop(stack);
    }
}

impl Drop for TypeExpr {
    fn drop(&mut self) {
        let mut stack = Vec::new();
        push_type_children(self, &mut stack);
        drain_ast_drop(stack);
    }
}
