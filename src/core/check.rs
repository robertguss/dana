//! Decidable static schema, type, sensitivity-taint, declassification, capability,
//! policy, and spec-code verifier for Dana Core IR v0.1.
//!
//! Mirrors `formal/DanaCore/Check.lean` 1-to-1.

use std::fmt;
use std::sync::Arc;

use crate::core::bigint::BigInt;
use crate::core::stack::with_large_stack;
use crate::core::syntax::{
    AggItem, AggKind, BUILT_IN_TAGS, CaseArm, ColSpec, ConstDecl, DeriveItem, Expr, FunDecl,
    HostOp, Ident, JoinKind, JoinOn, LTy, Literal, Plan, Policy, PrimOp, Program, RowExpr, RowLit,
    ScalarTy, TableTy, TagSet, Ty, WindowFn, WindowItem,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CheckError {
    pub message: String,
}

impl CheckError {
    #[must_use]
    pub fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
        }
    }
}

impl fmt::Display for CheckError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.message)
    }
}

impl std::error::Error for CheckError {}

fn err<T>(msg: impl Into<String>) -> Result<T, CheckError> {
    Err(CheckError::new(msg))
}

// ---------------------------------------------------------------------------
// Basic Uniqueness & Validity Helpers
// ---------------------------------------------------------------------------

#[must_use]
pub fn distinct_idents(idents: &[Ident]) -> bool {
    for (i, x) in idents.iter().enumerate() {
        if idents[i + 1..].contains(x) {
            return false;
        }
    }
    true
}

#[must_use]
pub fn valid_tag(prog: &Program, t: &str) -> bool {
    BUILT_IN_TAGS.contains(&t) || prog.tags.iter().any(|ct| ct == t)
}

#[must_use]
pub fn valid_tag_set(prog: &Program, ts: &TagSet) -> bool {
    ts.elems().iter().all(|t| valid_tag(prog, t))
}

#[must_use]
pub fn valid_scalar_ty(prog: &Program, ty: &ScalarTy) -> bool {
    let mut cur = ty;
    loop {
        match cur {
            ScalarTy::Unit
            | ScalarTy::Bool
            | ScalarTy::Int
            | ScalarTy::Decimal
            | ScalarTy::Float
            | ScalarTy::Text
            | ScalarTy::Bytes
            | ScalarTy::Date
            | ScalarTy::Timestamp
            | ScalarTy::Duration => return true,
            ScalarTy::Data(name) => return prog.find_data(name).is_some(),
            ScalarTy::Option(inner) => {
                if inner.is_option() {
                    return false;
                }
                cur = inner;
            }
        }
    }
}

#[must_use]
pub fn valid_col_spec(prog: &Program, c: &ColSpec) -> bool {
    valid_scalar_ty(prog, &c.ty)
        && valid_tag_set(prog, &c.tags)
        && (!c.bucketed || c.ty == ScalarTy::Text)
}

#[must_use]
pub fn valid_table_ty(prog: &Program, tt: &TableTy) -> bool {
    let gks: &[Ident] = tt.grouped_by.as_deref().unwrap_or(&[]);
    let col_names = tt.col_names();
    distinct_idents(&col_names)
        && tt.cols.iter().all(|c| {
            valid_col_spec(prog, c) && ((c.agg_kind == AggKind::GroupKey) == gks.contains(&c.name))
        })
        && valid_tag_set(prog, &tt.row_tags)
        && valid_tag_set(prog, &tt.order_tags)
        && match &tt.grouped_by {
            None => true,
            Some(ks) => distinct_idents(ks) && ks.iter().all(|k| tt.find_col(k).is_some()),
        }
}

#[must_use]
pub fn valid_ty(prog: &Program, ty: &Ty) -> bool {
    let mut stack: Vec<&Ty> = vec![ty];
    while let Some(cur) = stack.pop() {
        match cur {
            Ty::Unit
            | Ty::Bool
            | Ty::Int
            | Ty::Decimal
            | Ty::Float
            | Ty::Text
            | Ty::Bytes
            | Ty::Date
            | Ty::Timestamp
            | Ty::Duration
            | Ty::LinearModel
            | Ty::StatTest
            | Ty::Args
            | Ty::Clock
            | Ty::ReadFiles
            | Ty::ReadDB(_)
            | Ty::RawReadDB(_)
            | Ty::Secret(_) => {}
            Ty::Option(inner) => {
                if inner.is_option() {
                    return false;
                }
                stack.push(inner);
            }
            Ty::Result { ok_ty, err_ty } => {
                stack.push(ok_ty);
                stack.push(err_ty);
            }
            Ty::Tuple(elems) => {
                for e in elems {
                    if !valid_tag_set(prog, &e.tags) {
                        return false;
                    }
                    stack.push(&e.ty);
                }
            }
            Ty::List(elem) => {
                if !valid_tag_set(prog, &elem.tags) {
                    return false;
                }
                stack.push(&elem.ty);
            }
            Ty::Map { key, val } => {
                if !valid_tag_set(prog, &key.tags) || !valid_tag_set(prog, &val.tags) {
                    return false;
                }
                stack.push(&key.ty);
                stack.push(&val.ty);
            }
            Ty::Data(name) => {
                if prog.find_data(name).is_none() {
                    return false;
                }
            }
            Ty::Table(tt) => {
                if !valid_table_ty(prog, tt) {
                    return false;
                }
            }
            Ty::DynamicTable(ts)
            | Ty::Chart(ts)
            | Ty::Report(ts)
            | Ty::Profile(ts)
            | Ty::Console(ts)
            | Ty::Declassify(ts) => {
                if !valid_tag_set(prog, ts) {
                    return false;
                }
            }
            Ty::WriteFiles { allows, .. } | Ty::HttpsAllow { allows, .. } => {
                if !valid_tag_set(prog, allows) {
                    return false;
                }
            }
            Ty::WriteTable {
                dest_cols,
                dest_row_tags,
                allows,
                ..
            } => {
                let names: Vec<Ident> = dest_cols.iter().map(|c| c.name.clone()).collect();
                if !distinct_idents(&names)
                    || !dest_cols.iter().all(|c| valid_col_spec(prog, c))
                    || !valid_tag_set(prog, dest_row_tags)
                    || !valid_tag_set(prog, allows)
                {
                    return false;
                }
            }
            Ty::Fn { params, pc, ret } => {
                if !valid_tag_set(prog, pc) || !valid_tag_set(prog, &ret.tags) {
                    return false;
                }
                for p in params {
                    if !valid_tag_set(prog, &p.tags) {
                        return false;
                    }
                    stack.push(&p.ty);
                }
                stack.push(&ret.ty);
            }
        }
    }
    true
}

#[must_use]
pub fn valid_lty(prog: &Program, lty: &LTy) -> bool {
    valid_ty(prog, &lty.ty) && valid_tag_set(prog, &lty.tags)
}

#[must_use]
pub fn is_equatable_ty(ty: &Ty) -> bool {
    let mut stack: Vec<&Ty> = vec![ty];
    while let Some(cur) = stack.pop() {
        match cur {
            Ty::Unit
            | Ty::Bool
            | Ty::Int
            | Ty::Decimal
            | Ty::Float
            | Ty::Text
            | Ty::Bytes
            | Ty::Date
            | Ty::Timestamp
            | Ty::Duration
            | Ty::Data(_)
            | Ty::LinearModel
            | Ty::StatTest
            | Ty::Table(_) => {}
            Ty::Option(inner) => stack.push(inner),
            Ty::Result { ok_ty, err_ty } => {
                stack.push(ok_ty);
                stack.push(err_ty);
            }
            Ty::Tuple(elems) => {
                for e in elems {
                    stack.push(&e.ty);
                }
            }
            Ty::List(elem) => stack.push(&elem.ty),
            Ty::Map { key, val } => {
                stack.push(&key.ty);
                stack.push(&val.ty);
            }
            Ty::DynamicTable(_)
            | Ty::Chart(_)
            | Ty::Report(_)
            | Ty::Profile(_)
            | Ty::Fn { .. }
            | Ty::Args
            | Ty::Clock
            | Ty::Console(_)
            | Ty::ReadFiles
            | Ty::WriteFiles { .. }
            | Ty::ReadDB(_)
            | Ty::WriteTable { .. }
            | Ty::RawReadDB(_)
            | Ty::HttpsAllow { .. }
            | Ty::Secret(_)
            | Ty::Declassify(_) => return false,
        }
    }
    true
}

#[must_use]
pub fn is_ordered_scalar_ty(ty: &Ty) -> bool {
    matches!(
        ty,
        Ty::Bool
            | Ty::Int
            | Ty::Decimal
            | Ty::Float
            | Ty::Text
            | Ty::Date
            | Ty::Timestamp
            | Ty::Duration
    )
}

#[must_use]
pub fn numeric_core_of_scalar(s: &ScalarTy) -> Option<ScalarTy> {
    match s {
        ScalarTy::Int => Some(ScalarTy::Int),
        ScalarTy::Decimal => Some(ScalarTy::Decimal),
        ScalarTy::Float => Some(ScalarTy::Float),
        ScalarTy::Option(inner) => match inner.as_ref() {
            ScalarTy::Int => Some(ScalarTy::Int),
            ScalarTy::Decimal => Some(ScalarTy::Decimal),
            ScalarTy::Float => Some(ScalarTy::Float),
            _ => None,
        },
        _ => None,
    }
}

#[must_use]
pub fn base_of_scalar(s: &ScalarTy) -> &ScalarTy {
    match s {
        ScalarTy::Option(inner) => inner,
        other => other,
    }
}

#[must_use]
pub fn ensure_option_scalar(s: &ScalarTy) -> ScalarTy {
    match s {
        ScalarTy::Option(inner) => ScalarTy::Option(inner.clone()),
        other => ScalarTy::Option(Box::new(other.clone())),
    }
}

// ---------------------------------------------------------------------------
// Environments & Subtyping
// ---------------------------------------------------------------------------

pub type TyEnv = Vec<(Ident, LTy)>;

#[must_use]
pub fn lookup_ty_env<'a>(env: &'a [(Ident, LTy)], name: &str) -> Option<&'a LTy> {
    env.iter().find(|(k, _)| k == name).map(|(_, v)| v)
}

#[must_use]
pub fn extend_ty_env(env: &[(Ident, LTy)], bindings: &[(Ident, LTy)]) -> TyEnv {
    let mut out = Vec::with_capacity(bindings.len() + env.len());
    out.extend_from_slice(bindings);
    out.extend_from_slice(env);
    out
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct JoinSig {
    pub params: Vec<(Ident, LTy)>,
    pub join_pc: TagSet,
    pub ret_lty: LTy,
}

pub type JoinEnv = Vec<(Ident, JoinSig)>;

#[derive(Clone, Debug)]
struct TyEnvNode {
    name: Ident,
    lty: LTy,
    tail: Option<Arc<TyEnvNode>>,
}

/// Persistent `Arc`-backed type environment with O(1) extension/clone and iterative `Drop`.
#[derive(Clone, Debug, Default)]
pub(crate) struct ArcTyEnv(Option<Arc<TyEnvNode>>);

impl ArcTyEnv {
    #[must_use]
    pub(crate) const fn empty() -> Self {
        Self(None)
    }

    #[must_use]
    pub(crate) fn from_slice(env: &[(Ident, LTy)]) -> Self {
        let mut cur = Self::empty();
        for (name, lty) in env.iter().rev() {
            cur = Self::cons(name.clone(), lty.clone(), cur);
        }
        cur
    }

    #[must_use]
    pub(crate) fn cons(name: Ident, lty: LTy, mut tail: Self) -> Self {
        Self(Some(Arc::new(TyEnvNode {
            name,
            lty,
            tail: tail.0.take(),
        })))
    }

    #[must_use]
    pub(crate) fn extend_slice(&self, bindings: &[(Ident, LTy)]) -> Self {
        let mut cur = self.clone();
        for (name, lty) in bindings.iter().rev() {
            cur = Self::cons(name.clone(), lty.clone(), cur);
        }
        cur
    }

    #[must_use]
    pub(crate) fn lookup(&self, name: &str) -> Option<&LTy> {
        let mut cur = self.0.as_deref();
        while let Some(node) = cur {
            if node.name == name {
                return Some(&node.lty);
            }
            cur = node.tail.as_deref();
        }
        None
    }
}

impl Drop for ArcTyEnv {
    fn drop(&mut self) {
        let mut cur = self.0.take();
        while let Some(arc) = cur {
            match Arc::try_unwrap(arc) {
                Ok(mut node) => cur = node.tail.take(),
                Err(_) => break,
            }
        }
    }
}

#[derive(Clone, Debug)]
struct JoinEnvNode {
    label: Ident,
    sig: JoinSig,
    tail: Option<Arc<JoinEnvNode>>,
}

#[derive(Clone, Debug, Default)]
struct ArcJoinEnv(Option<Arc<JoinEnvNode>>);

impl ArcJoinEnv {
    const fn empty() -> Self {
        Self(None)
    }

    fn from_slice(jenv: &[(Ident, JoinSig)]) -> Self {
        let mut cur = Self::empty();
        for (label, sig) in jenv.iter().rev() {
            cur = Self::cons(label.clone(), sig.clone(), cur);
        }
        cur
    }

    fn cons(label: Ident, sig: JoinSig, mut tail: Self) -> Self {
        Self(Some(Arc::new(JoinEnvNode {
            label,
            sig,
            tail: tail.0.take(),
        })))
    }

    fn lookup(&self, label: &str) -> Option<&JoinSig> {
        let mut cur = self.0.as_deref();
        while let Some(node) = cur {
            if node.label == label {
                return Some(&node.sig);
            }
            cur = node.tail.as_deref();
        }
        None
    }
}

impl Drop for ArcJoinEnv {
    fn drop(&mut self) {
        let mut cur = self.0.take();
        while let Some(arc) = cur {
            match Arc::try_unwrap(arc) {
                Ok(mut node) => cur = node.tail.take(),
                Err(_) => break,
            }
        }
    }
}

#[must_use]
pub fn lty_subtype(sub: &LTy, sup: &LTy) -> bool {
    sub.ty == sup.ty && sub.tags.is_subset(&sup.tags)
}

// ---------------------------------------------------------------------------
// Tail-Jump Restriction Checker (Iterative, O(1) Stack Depth)
// ---------------------------------------------------------------------------

enum JumpWork<'a> {
    Expr(Vec<Ident>, &'a Expr),
    Plan(&'a Plan),
}

fn run_no_free_jumps(mut stack: Vec<JumpWork<'_>>) -> bool {
    while let Some(item) = stack.pop() {
        match item {
            JumpWork::Expr(bound_labels, expr) => match expr {
                Expr::Lit(_) | Expr::Var(_) | Expr::ConstRef(_) | Expr::TableLit { .. } => {}
                Expr::LetE { bound, body, .. } => {
                    stack.push(JumpWork::Expr(bound_labels, body));
                    stack.push(JumpWork::Expr(Vec::new(), bound));
                }
                Expr::IfE {
                    cond,
                    then_br,
                    else_br,
                } => {
                    stack.push(JumpWork::Expr(bound_labels.clone(), else_br));
                    stack.push(JumpWork::Expr(bound_labels, then_br));
                    stack.push(JumpWork::Expr(Vec::new(), cond));
                }
                Expr::CaseE { scrut, arms } => {
                    for a in arms {
                        stack.push(JumpWork::Expr(bound_labels.clone(), &a.body));
                    }
                    stack.push(JumpWork::Expr(Vec::new(), scrut));
                }
                Expr::Lam { body, .. } => {
                    stack.push(JumpWork::Expr(Vec::new(), body));
                }
                Expr::Proj { tup: body, .. } | Expr::Fail(body) => {
                    stack.push(JumpWork::Expr(Vec::new(), body));
                }
                Expr::App { fn_expr, args } => {
                    for a in args {
                        stack.push(JumpWork::Expr(Vec::new(), a));
                    }
                    stack.push(JumpWork::Expr(Vec::new(), fn_expr));
                }
                Expr::Call { args, .. }
                | Expr::Tuple(args)
                | Expr::Ctor { args, .. }
                | Expr::Prim { args, .. }
                | Expr::Host { args, .. } => {
                    for a in args {
                        stack.push(JumpWork::Expr(Vec::new(), a));
                    }
                }
                Expr::Join {
                    label, rhs, body, ..
                } => {
                    let mut next = Vec::with_capacity(bound_labels.len() + 1);
                    next.push(label.clone());
                    next.extend(bound_labels);
                    stack.push(JumpWork::Expr(next.clone(), body));
                    stack.push(JumpWork::Expr(next, rhs));
                }
                Expr::Jump { label, args } => {
                    if !bound_labels.contains(label) {
                        return false;
                    }
                    for a in args {
                        stack.push(JumpWork::Expr(Vec::new(), a));
                    }
                }
                Expr::Rel(plan) => {
                    stack.push(JumpWork::Plan(plan));
                }
                Expr::Stop { detail, .. } => {
                    if let Some(d) = detail {
                        stack.push(JumpWork::Expr(Vec::new(), d));
                    }
                }
            },
            JumpWork::Plan(plan) => match plan {
                Plan::SourceExpr(e) | Plan::SourceDB { cap: e, .. } => {
                    stack.push(JumpWork::Expr(Vec::new(), e));
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
                    stack.push(JumpWork::Plan(input));
                }
                Plan::Join { left, right, .. } | Plan::Union { left, right } => {
                    stack.push(JumpWork::Plan(right));
                    stack.push(JumpWork::Plan(left));
                }
                Plan::Pseudonymize { input, secret, .. } => {
                    stack.push(JumpWork::Expr(Vec::new(), secret));
                    stack.push(JumpWork::Plan(input));
                }
            },
        }
    }
    true
}

#[must_use]
pub fn no_free_jumps(bound_labels: &[Ident], expr: &Expr) -> bool {
    run_no_free_jumps(vec![JumpWork::Expr(bound_labels.to_vec(), expr)])
}

fn no_free_jumps_list(exprs: &[Expr]) -> bool {
    let stack = exprs
        .iter()
        .map(|e| JumpWork::Expr(Vec::new(), e))
        .collect();
    run_no_free_jumps(stack)
}

fn no_free_jumps_plan(plan: &Plan) -> bool {
    run_no_free_jumps(vec![JumpWork::Plan(plan)])
}

// ---------------------------------------------------------------------------
// Literal & Primitive Type Checking
// ---------------------------------------------------------------------------

pub fn check_literal(prog: &Program, pc: &TagSet, lit: &Literal) -> Result<LTy, CheckError> {
    match lit {
        Literal::Unit => Ok(LTy::new(Ty::Unit, pc.clone())),
        Literal::Bool(_) => Ok(LTy::new(Ty::Bool, pc.clone())),
        Literal::Int(n) => {
            if n.in_int64_range() {
                Ok(LTy::new(Ty::Int, pc.clone()))
            } else {
                err("integer literal out of 64-bit signed range")
            }
        }
        Literal::Decimal(d) => {
            if d.in_decimal_range() {
                Ok(LTy::new(Ty::Decimal, pc.clone()))
            } else {
                err("decimal literal out of 128-bit range")
            }
        }
        Literal::Float(_) => Ok(LTy::new(Ty::Float, pc.clone())),
        Literal::Text(_) => Ok(LTy::new(Ty::Text, pc.clone())),
        Literal::Bytes(_) => Ok(LTy::new(Ty::Bytes, pc.clone())),
        Literal::Date(_) => Ok(LTy::new(Ty::Date, pc.clone())),
        Literal::Timestamp(_) => Ok(LTy::new(Ty::Timestamp, pc.clone())),
        Literal::Duration(_) => Ok(LTy::new(Ty::Duration, pc.clone())),
        Literal::NoneLit(inner) => {
            if !inner.is_option() && valid_ty(prog, inner) {
                Ok(LTy::new(Ty::Option(Box::new(inner.clone())), pc.clone()))
            } else {
                err("invalid Option inner type in none literal")
            }
        }
    }
}

fn check_row_lit(prog: &Program, cols: &[ColSpec], row: &RowLit) -> bool {
    if cols.len() != row.cells.len() {
        return false;
    }
    cols.iter().zip(&row.cells).all(|(c, l)| {
        check_literal(prog, &TagSet::empty(), l).is_ok_and(|lty| lty.ty == c.ty.to_ty())
    })
}

pub fn check_prim_op(
    prog: &Program,
    pc: &TagSet,
    op: &PrimOp,
    args: &[LTy],
) -> Result<LTy, CheckError> {
    match (op, args) {
        (PrimOp::SomeVal(inner), [a]) => {
            if !inner.is_option() && valid_ty(prog, inner) && a.ty == *inner {
                Ok(LTy::new(
                    Ty::Option(Box::new(inner.clone())),
                    a.tags.union(pc),
                ))
            } else {
                err("someVal type mismatch")
            }
        }
        (
            PrimOp::IsSome | PrimOp::IsNone,
            [
                LTy {
                    ty: Ty::Option(_),
                    tags,
                },
            ],
        ) => Ok(LTy::new(Ty::Bool, tags.union(pc))),
        (
            PrimOp::UnwrapOr,
            [
                LTy {
                    ty: Ty::Option(inner),
                    tags: ts1,
                },
                LTy { ty: ty2, tags: ts2 },
            ],
        ) => {
            if inner.as_ref() == ty2 {
                Ok(LTy::new(ty2.clone(), ts1.union(ts2).union(pc)))
            } else {
                err("unwrapOr branch type mismatch")
            }
        }
        (
            PrimOp::UnwrapBang,
            [
                LTy {
                    ty: Ty::Option(inner),
                    tags: ts,
                },
            ],
        ) => Ok(LTy::new(inner.as_ref().clone(), ts.union(pc))),
        (PrimOp::OkVal(err_ty), [a]) => {
            if valid_ty(prog, err_ty) {
                Ok(LTy::new(
                    Ty::Result {
                        ok_ty: Box::new(a.ty.clone()),
                        err_ty: Box::new(err_ty.clone()),
                    },
                    a.tags.union(pc),
                ))
            } else {
                err("invalid errTy in okVal")
            }
        }
        (PrimOp::ErrVal(ok_ty), [a]) => {
            if valid_ty(prog, ok_ty) {
                Ok(LTy::new(
                    Ty::Result {
                        ok_ty: Box::new(ok_ty.clone()),
                        err_ty: Box::new(a.ty.clone()),
                    },
                    a.tags.union(pc),
                ))
            } else {
                err("invalid okTy in errVal")
            }
        }
        (
            PrimOp::AddInt | PrimOp::SubInt | PrimOp::MulInt | PrimOp::DivInt | PrimOp::ModInt,
            [
                LTy {
                    ty: Ty::Int,
                    tags: t1,
                },
                LTy {
                    ty: Ty::Int,
                    tags: t2,
                },
            ],
        ) => Ok(LTy::new(Ty::Int, t1.union(t2).union(pc))),
        (
            PrimOp::NegInt,
            [
                LTy {
                    ty: Ty::Int,
                    tags: t1,
                },
            ],
        ) => Ok(LTy::new(Ty::Int, t1.union(pc))),
        (
            PrimOp::AddDec | PrimOp::SubDec | PrimOp::MulDec | PrimOp::DivDec,
            [
                LTy {
                    ty: Ty::Decimal,
                    tags: t1,
                },
                LTy {
                    ty: Ty::Decimal,
                    tags: t2,
                },
            ],
        ) => Ok(LTy::new(Ty::Decimal, t1.union(t2).union(pc))),
        (
            PrimOp::NegDec,
            [
                LTy {
                    ty: Ty::Decimal,
                    tags: t1,
                },
            ],
        ) => Ok(LTy::new(Ty::Decimal, t1.union(pc))),
        (
            PrimOp::IntToDec,
            [
                LTy {
                    ty: Ty::Int,
                    tags: t1,
                },
            ],
        )
        | (
            PrimOp::BoolToDec,
            [
                LTy {
                    ty: Ty::Bool,
                    tags: t1,
                },
            ],
        ) => Ok(LTy::new(Ty::Decimal, t1.union(pc))),
        (PrimOp::Eq | PrimOp::Ne, [a1, a2]) => {
            if a1.ty == a2.ty && is_equatable_ty(&a1.ty) {
                Ok(LTy::new(
                    Ty::Bool,
                    a1.effective_tags().union(&a2.effective_tags()).union(pc),
                ))
            } else {
                err("eq/ne requires matching equatable types")
            }
        }
        (PrimOp::Lt | PrimOp::Le | PrimOp::Gt | PrimOp::Ge, [a1, a2]) => {
            if a1.ty == a2.ty && is_ordered_scalar_ty(&a1.ty) {
                Ok(LTy::new(
                    Ty::Bool,
                    a1.effective_tags().union(&a2.effective_tags()).union(pc),
                ))
            } else {
                err("comparison requires matching ordered scalar types")
            }
        }
        (
            PrimOp::NotBool,
            [
                LTy {
                    ty: Ty::Bool,
                    tags: t1,
                },
            ],
        ) => Ok(LTy::new(Ty::Bool, t1.union(pc))),
        (
            PrimOp::AndBool | PrimOp::OrBool,
            [
                LTy {
                    ty: Ty::Bool,
                    tags: t1,
                },
                LTy {
                    ty: Ty::Bool,
                    tags: t2,
                },
            ],
        ) => Ok(LTy::new(Ty::Bool, t1.union(t2).union(pc))),
        (
            PrimOp::ConcatText,
            [
                LTy {
                    ty: Ty::Text,
                    tags: t1,
                },
                LTy {
                    ty: Ty::Text,
                    tags: t2,
                },
            ],
        ) => Ok(LTy::new(Ty::Text, t1.union(t2).union(pc))),
        (
            PrimOp::ContainsText,
            [
                LTy {
                    ty: Ty::Text,
                    tags: t1,
                },
                LTy {
                    ty: Ty::Text,
                    tags: t2,
                },
            ],
        ) => Ok(LTy::new(Ty::Bool, t1.union(t2).union(pc))),
        (
            PrimOp::TrimText | PrimOp::LowerAsciiText,
            [
                LTy {
                    ty: Ty::Text,
                    tags: t1,
                },
            ],
        ) => Ok(LTy::new(Ty::Text, t1.union(pc))),
        (
            PrimOp::EmptyText,
            [
                LTy {
                    ty: Ty::Text,
                    tags: t1,
                },
            ],
        ) => Ok(LTy::new(Ty::Bool, t1.union(pc))),
        (
            PrimOp::IntToText,
            [
                LTy {
                    ty: Ty::Int,
                    tags: t1,
                },
            ],
        )
        | (
            PrimOp::DecToText,
            [
                LTy {
                    ty: Ty::Decimal,
                    tags: t1,
                },
            ],
        ) => Ok(LTy::new(Ty::Text, t1.union(pc))),
        (
            PrimOp::DateTruncMonth,
            [
                LTy {
                    ty: Ty::Date,
                    tags: t1,
                },
            ],
        ) => Ok(LTy::new(Ty::Date, t1.union(pc))),
        (
            PrimOp::AddDuration,
            [
                LTy {
                    ty: Ty::Timestamp,
                    tags: t1,
                },
                LTy {
                    ty: Ty::Duration,
                    tags: t2,
                },
            ],
        ) => Ok(LTy::new(Ty::Timestamp, t1.union(t2).union(pc))),
        (
            PrimOp::DiffTimestamp,
            [
                LTy {
                    ty: Ty::Timestamp,
                    tags: t1,
                },
                LTy {
                    ty: Ty::Timestamp,
                    tags: t2,
                },
            ],
        ) => Ok(LTy::new(Ty::Duration, t1.union(t2).union(pc))),
        (PrimOp::ListLit(elem_lty), elems) => {
            if valid_lty(prog, elem_lty) && elems.iter().all(|a| lty_subtype(a, elem_lty)) {
                Ok(LTy::new(Ty::List(Box::new(elem_lty.clone())), pc.clone()))
            } else {
                err("listLit element type/tag mismatch")
            }
        }
        (
            PrimOp::ListLen,
            [
                LTy {
                    ty: Ty::List(_),
                    tags,
                },
            ],
        ) => Ok(LTy::new(Ty::Int, tags.union(pc))),
        (
            PrimOp::ListEmpty,
            [
                LTy {
                    ty: Ty::List(_),
                    tags,
                },
            ],
        ) => Ok(LTy::new(Ty::Bool, tags.union(pc))),
        (
            PrimOp::ListAppend,
            [
                LTy {
                    ty: Ty::List(elem_lty),
                    tags: ts_l,
                },
                item,
            ],
        ) => {
            if lty_subtype(item, elem_lty) {
                Ok(LTy::new(Ty::List(elem_lty.clone()), ts_l.union(pc)))
            } else {
                err("listAppend element mismatch")
            }
        }
        (
            PrimOp::ListConcat,
            [
                LTy {
                    ty: Ty::List(inner_lty),
                    tags: outer_ts,
                },
            ],
        ) => {
            if let Ty::List(elem_lty) = &inner_lty.ty {
                let inner_ts = &inner_lty.tags;
                Ok(LTy::new(
                    Ty::List(Box::new(elem_lty.add_tags(inner_ts))),
                    outer_ts.union(inner_ts).union(pc),
                ))
            } else {
                err("ill-typed primitive operation")
            }
        }
        (PrimOp::MapLit { key_lty, val_lty }, kv_args) => {
            let pairs_ok =
                kv_args.len().is_multiple_of(2)
                    && kv_args.as_chunks::<2>().0.iter().all(|pair| {
                        lty_subtype(&pair[0], key_lty) && lty_subtype(&pair[1], val_lty)
                    });
            if valid_lty(prog, key_lty)
                && valid_lty(prog, val_lty)
                && is_equatable_ty(&key_lty.ty)
                && pairs_ok
            {
                Ok(LTy::new(
                    Ty::Map {
                        key: Box::new(key_lty.clone()),
                        val: Box::new(val_lty.clone()),
                    },
                    pc.clone(),
                ))
            } else {
                err("mapLit key/value type mismatch")
            }
        }
        (
            PrimOp::MapGet,
            [
                LTy {
                    ty:
                        Ty::Map {
                            key: k_lty,
                            val: v_lty,
                        },
                    tags: map_ts,
                },
                LTy {
                    ty: q_ty,
                    tags: q_ts,
                },
            ],
        ) => {
            if *q_ty == k_lty.ty && is_equatable_ty(q_ty) && !v_lty.ty.is_option() {
                let res_tags = map_ts
                    .union(&k_lty.effective_tags())
                    .union(&v_lty.tags)
                    .union(q_ts)
                    .union(pc);
                Ok(LTy::new(Ty::Option(Box::new(v_lty.ty.clone())), res_tags))
            } else {
                err("mapGet key type mismatch")
            }
        }
        (
            PrimOp::TableCount,
            [
                LTy {
                    ty: Ty::Table(tt),
                    tags: t_ts,
                },
            ],
        ) => Ok(LTy::new(Ty::Int, tt.row_tags.union(t_ts).union(pc))),
        (
            PrimOp::TableConcat(schema),
            [
                LTy {
                    ty: Ty::List(elem_lty),
                    tags: list_ts,
                },
            ],
        ) => {
            if let Ty::Table(tt) = &elem_lty.ty {
                if schema == tt && valid_table_ty(prog, schema) {
                    let extra = elem_lty.tags.union(list_ts).union(pc);
                    let out_tt = TableTy {
                        cols: tt
                            .cols
                            .iter()
                            .map(|c| ColSpec {
                                agg_kind: AggKind::Raw,
                                ..c.clone()
                            })
                            .collect(),
                        row_tags: tt.row_tags.union(&extra),
                        order_tags: tt.order_tags.union(&extra),
                        grouped_by: None,
                        summarized: false,
                        distinct_by: None,
                    };
                    Ok(LTy::new(Ty::Table(out_tt), pc.clone()))
                } else {
                    err("tableConcat schema annotation mismatch")
                }
            } else {
                err("ill-typed primitive operation")
            }
        }
        (
            PrimOp::TableProfile,
            [
                LTy {
                    ty: Ty::Table(tt),
                    tags: t_ts,
                },
            ],
        ) => Ok(LTy::new(
            Ty::Profile(tt.total_tags().union(t_ts).union(pc)),
            pc.clone(),
        )),
        (
            PrimOp::StatsCorr { col_x, col_y },
            [
                LTy {
                    ty: Ty::Table(tt),
                    tags: t_ts,
                },
            ],
        ) => match (tt.find_col(col_x), tt.find_col(col_y)) {
            (Some(cx), Some(cy)) => {
                if numeric_core_of_scalar(&cx.ty).is_some()
                    && numeric_core_of_scalar(&cy.ty).is_some()
                {
                    let s_tags = tt
                        .row_tags
                        .union(t_ts)
                        .union(&cx.tags)
                        .union(&cy.tags)
                        .union(pc);
                    Ok(LTy::new(Ty::Option(Box::new(Ty::Float)), s_tags))
                } else {
                    err("statsCorr requires numeric columns")
                }
            }
            _ => err("statsCorr missing column"),
        },
        (
            PrimOp::StatsLinReg { col_x, col_y },
            [
                LTy {
                    ty: Ty::Table(tt),
                    tags: t_ts,
                },
            ],
        ) => match (tt.find_col(col_x), tt.find_col(col_y)) {
            (Some(cx), Some(cy)) => {
                if numeric_core_of_scalar(&cx.ty).is_some()
                    && numeric_core_of_scalar(&cy.ty).is_some()
                {
                    let s_tags = tt
                        .row_tags
                        .union(t_ts)
                        .union(&cx.tags)
                        .union(&cy.tags)
                        .union(pc);
                    Ok(LTy::new(Ty::LinearModel, s_tags))
                } else {
                    err("statsLinReg requires numeric columns")
                }
            }
            _ => err("statsLinReg missing column"),
        },
        (
            PrimOp::StatsTTest { col_x, col_y },
            [
                LTy {
                    ty: Ty::Table(tt),
                    tags: t_ts,
                },
            ],
        ) => match (tt.find_col(col_x), tt.find_col(col_y)) {
            (Some(cx), Some(cy)) => {
                if numeric_core_of_scalar(&cx.ty).is_some()
                    && numeric_core_of_scalar(&cy.ty).is_some()
                {
                    let s_tags = tt
                        .row_tags
                        .union(t_ts)
                        .union(&cx.tags)
                        .union(&cy.tags)
                        .union(pc);
                    Ok(LTy::new(Ty::StatTest, s_tags))
                } else {
                    err("statsTTest requires numeric columns")
                }
            }
            _ => err("statsTTest missing column"),
        },
        (
            PrimOp::ChartMake { cols, .. },
            [
                LTy {
                    ty: Ty::Table(tt),
                    tags: t_ts,
                },
            ],
        ) => {
            if !cols.is_empty() && cols.iter().all(|cn| tt.find_col(cn).is_some()) {
                let col_tags = TagSet::union_list(
                    cols.iter()
                        .filter_map(|cn| tt.find_col(cn).map(|c| &c.tags)),
                );
                let c_tags = tt
                    .row_tags
                    .union(&tt.order_tags)
                    .union(t_ts)
                    .union(&col_tags)
                    .union(pc);
                Ok(LTy::new(Ty::Chart(c_tags), pc.clone()))
            } else {
                err("chartMake references unknown or empty columns")
            }
        }
        (
            PrimOp::ReportNew,
            [
                LTy {
                    ty: Ty::Text,
                    tags: t_ts,
                },
            ],
        ) => Ok(LTy::new(Ty::Report(t_ts.union(pc)), pc.clone())),
        (
            PrimOp::ReportAddSummary,
            [
                LTy {
                    ty: Ty::Report(r_ts),
                    tags: ro_ts,
                },
                LTy {
                    ty: Ty::Text,
                    tags: s_ts,
                },
            ],
        ) => Ok(LTy::new(
            Ty::Report(r_ts.union(ro_ts).union(s_ts).union(pc)),
            pc.clone(),
        )),
        (
            PrimOp::ReportAddChart,
            [
                LTy {
                    ty: Ty::Report(r_ts),
                    tags: ro_ts,
                },
                LTy {
                    ty: Ty::Chart(c_ts),
                    tags: co_ts,
                },
            ],
        ) => Ok(LTy::new(
            Ty::Report(r_ts.union(ro_ts).union(c_ts).union(co_ts).union(pc)),
            pc.clone(),
        )),
        (
            PrimOp::ReportAddTable,
            [
                LTy {
                    ty: Ty::Report(r_ts),
                    tags: ro_ts,
                },
                LTy {
                    ty: Ty::Table(tt),
                    tags: to_ts,
                },
            ],
        ) => Ok(LTy::new(
            Ty::Report(
                r_ts.union(ro_ts)
                    .union(&tt.total_tags())
                    .union(to_ts)
                    .union(pc),
            ),
            pc.clone(),
        )),
        _ => err("ill-typed primitive operation"),
    }
}

// ---------------------------------------------------------------------------
// RowExpr Static Checker
// ---------------------------------------------------------------------------

pub fn check_row_expr(
    prog: &Program,
    env: &[(Ident, LTy)],
    cols: &[ColSpec],
    re: &RowExpr,
) -> Result<(ScalarTy, TagSet), CheckError> {
    let arc_env = ArcTyEnv::from_slice(env);
    check_row_expr_arc(prog, &arc_env, cols, re)
}

enum RowCheckTask<'a> {
    Eval(&'a RowExpr),
    FinishPrim(&'a PrimOp, usize),
    FinishIf,
    FinishCoalesce,
    FinishCallPure(&'a Ident, usize),
}

fn check_row_expr_arc(
    prog: &Program,
    env: &ArcTyEnv,
    cols: &[ColSpec],
    re: &RowExpr,
) -> Result<(ScalarTy, TagSet), CheckError> {
    let mut tasks = vec![RowCheckTask::Eval(re)];
    let mut vals: Vec<(ScalarTy, TagSet)> = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            RowCheckTask::Eval(cur) => match cur {
                RowExpr::Lit(v) => {
                    let lty = check_literal(prog, &TagSet::empty(), v)?;
                    match lty.ty.to_scalar_ty() {
                        Some(s_ty) => {
                            if valid_scalar_ty(prog, &s_ty) {
                                vals.push((s_ty, TagSet::empty()));
                            } else {
                                return err("invalid scalar literal type in RowExpr");
                            }
                        }
                        None => return err("non-scalar literal in RowExpr"),
                    }
                }
                RowExpr::Col(name) => match cols.iter().find(|c| c.name == *name) {
                    Some(c) => vals.push((c.ty.clone(), c.tags.clone())),
                    None => return err(format!("missing column '{name}' in RowExpr")),
                },
                RowExpr::OuterVar(name) => match env.lookup(name) {
                    Some(lty) => match lty.ty.to_scalar_ty() {
                        Some(s_ty) => {
                            if valid_scalar_ty(prog, &s_ty) {
                                vals.push((s_ty, lty.effective_tags()));
                            } else {
                                return err(format!(
                                    "outer variable '{name}' in RowExpr has invalid scalar type"
                                ));
                            }
                        }
                        None => {
                            return err(format!(
                                "outer variable '{name}' in RowExpr is not a scalar type"
                            ));
                        }
                    },
                    None => return err(format!("unbound outer variable '{name}' in RowExpr")),
                },
                RowExpr::ConstRef(name) => match prog.find_const(name) {
                    Some(c_decl) => match c_decl.lty.ty.to_scalar_ty() {
                        Some(s_ty) => {
                            if valid_scalar_ty(prog, &s_ty) {
                                vals.push((s_ty, c_decl.lty.effective_tags()));
                            } else {
                                return err(format!("constant '{name}' has invalid scalar type"));
                            }
                        }
                        None => return err(format!("constant '{name}' is not scalar")),
                    },
                    None => return err(format!("unknown constant '{name}'")),
                },
                RowExpr::Prim { op, args } => {
                    tasks.push(RowCheckTask::FinishPrim(op, args.len()));
                    for a in args.iter().rev() {
                        tasks.push(RowCheckTask::Eval(a));
                    }
                }
                RowExpr::IfE {
                    cond,
                    then_br,
                    else_br,
                } => {
                    tasks.push(RowCheckTask::FinishIf);
                    tasks.push(RowCheckTask::Eval(else_br));
                    tasks.push(RowCheckTask::Eval(then_br));
                    tasks.push(RowCheckTask::Eval(cond));
                }
                RowExpr::Coalesce {
                    opt_expr,
                    default_expr,
                } => {
                    tasks.push(RowCheckTask::FinishCoalesce);
                    tasks.push(RowCheckTask::Eval(default_expr));
                    tasks.push(RowCheckTask::Eval(opt_expr));
                }
                RowExpr::CallPure { fn_name, args } => {
                    tasks.push(RowCheckTask::FinishCallPure(fn_name, args.len()));
                    for a in args.iter().rev() {
                        tasks.push(RowCheckTask::Eval(a));
                    }
                }
            },
            RowCheckTask::FinishPrim(op, n) => {
                let arg_pairs = vals.split_off(vals.len() - n);
                let arg_ltys: Vec<LTy> = arg_pairs
                    .into_iter()
                    .map(|(s_ty, ts)| LTy::new(s_ty.to_ty(), ts))
                    .collect();
                let res_lty = check_prim_op(prog, &TagSet::empty(), op, &arg_ltys)?;
                match res_lty.ty.to_scalar_ty() {
                    Some(s_ty) => {
                        if valid_scalar_ty(prog, &s_ty) {
                            vals.push((s_ty, res_lty.effective_tags()));
                        } else {
                            return err(
                                "PrimOp in RowExpr produced nested Option or invalid scalar type",
                            );
                        }
                    }
                    None => return err("PrimOp in RowExpr did not produce a scalar column type"),
                }
            }
            RowCheckTask::FinishIf => {
                let (Some((e_ty, e_tags)), Some((t_ty, t_tags)), Some((c_ty, c_tags))) =
                    (vals.pop(), vals.pop(), vals.pop())
                else {
                    unreachable!("stack balanced");
                };
                if c_ty == ScalarTy::Bool && t_ty == e_ty {
                    vals.push((t_ty, c_tags.union(&t_tags).union(&e_tags)));
                } else {
                    return err("RowExpr ifE requires Bool condition and matching branch types");
                }
            }
            RowCheckTask::FinishCoalesce => {
                let (Some((d_ty, d_tags)), Some((o_ty, o_tags))) = (vals.pop(), vals.pop()) else {
                    unreachable!("stack balanced");
                };
                match &o_ty {
                    ScalarTy::Option(inner) => {
                        if **inner == d_ty {
                            vals.push((d_ty, o_tags.union(&d_tags)));
                        } else {
                            return err("RowExpr coalesce type mismatch");
                        }
                    }
                    _ => return err("RowExpr coalesce requires Option left operand"),
                }
            }
            RowCheckTask::FinishCallPure(fn_name, n) => {
                let arg_pairs = vals.split_off(vals.len() - n);
                match prog.find_fun(fn_name) {
                    Some(f_decl) => {
                        if !f_decl.is_pure || f_decl.kind.is_spec() {
                            return err(format!(
                                "function '{fn_name}' called in RowExpr must be a pure non-spec function"
                            ));
                        }
                        if f_decl.params.len() != arg_pairs.len() {
                            return err(format!("arity mismatch in RowExpr call to '{fn_name}'"));
                        }
                        let args_ok =
                            arg_pairs
                                .iter()
                                .zip(&f_decl.params)
                                .all(|((s_ty, _), (_, p_lty))| {
                                    s_ty.to_ty() == p_lty.ty && p_lty.tags.is_empty()
                                });
                        if !f_decl.pc.is_empty() || !args_ok {
                            return err(format!(
                                "pure function '{fn_name}' in RowExpr must have public signature"
                            ));
                        }
                        match f_decl.ret.ty.to_scalar_ty() {
                            Some(ret_sty) => {
                                if valid_scalar_ty(prog, &ret_sty) {
                                    let arg_union =
                                        TagSet::union_list(arg_pairs.iter().map(|(_, ts)| ts));
                                    vals.push((
                                        ret_sty,
                                        f_decl.ret.effective_tags().union(&arg_union),
                                    ));
                                } else {
                                    return err(format!(
                                        "pure function '{fn_name}' returns invalid scalar type"
                                    ));
                                }
                            }
                            None => {
                                return err(format!(
                                    "pure function '{fn_name}' does not return a scalar type"
                                ));
                            }
                        }
                    }
                    None => return err(format!("unknown function '{fn_name}' in RowExpr")),
                }
            }
        }
    }
    match vals.pop() {
        Some(res) => Ok(res),
        None => unreachable!("check_row_expr_arc always produces one result"),
    }
}

// ---------------------------------------------------------------------------
// Host Capability Operations & `dana.policy` Enforcement
// ---------------------------------------------------------------------------

#[must_use]
pub fn quarantine_bad_row_table_ty(s: &TableTy) -> TableTy {
    let val_tags = s.all_col_tags();
    let line_tags = s.row_tags.union(&val_tags);
    TableTy {
        cols: vec![
            ColSpec {
                name: "line".to_string(),
                ty: ScalarTy::Int,
                tags: TagSet::empty(),
                bucketed: false,
                agg_kind: AggKind::Raw,
            },
            ColSpec {
                name: "column".to_string(),
                ty: ScalarTy::Text,
                tags: TagSet::empty(),
                bucketed: false,
                agg_kind: AggKind::Raw,
            },
            ColSpec {
                name: "error_kind".to_string(),
                ty: ScalarTy::Text,
                tags: TagSet::empty(),
                bucketed: false,
                agg_kind: AggKind::Raw,
            },
            ColSpec {
                name: "raw_value".to_string(),
                ty: ScalarTy::Text,
                tags: val_tags,
                bucketed: false,
                agg_kind: AggKind::Raw,
            },
            ColSpec {
                name: "raw_line".to_string(),
                ty: ScalarTy::Text,
                tags: line_tags,
                bucketed: false,
                agg_kind: AggKind::Raw,
            },
        ],
        row_tags: s.row_tags.clone(),
        order_tags: s.order_tags.clone(),
        grouped_by: None,
        summarized: false,
        distinct_by: None,
    }
}

#[must_use]
pub fn is_safe_relative_path(path: &str) -> bool {
    !path.is_empty()
        && !path.starts_with('/')
        && !path.contains('\\')
        && !path.split('/').any(|seg| seg == "..")
}

#[must_use]
pub fn join_confined_path(root: &str, rel_path: &str) -> String {
    if root.is_empty() {
        rel_path.to_string()
    } else if root.ends_with('/') {
        format!("{root}{rel_path}")
    } else {
        format!("{root}/{rel_path}")
    }
}

#[must_use]
pub fn path_matches_export_prefix(policy_root: &str, req_root: &str) -> bool {
    is_safe_relative_path(req_root)
        && (req_root == policy_root
            || (policy_root.ends_with('/') && req_root.starts_with(policy_root))
            || (!policy_root.ends_with('/') && req_root.starts_with(&format!("{policy_root}/"))))
}

fn policy_allows_export(p: &Policy, root: &str, allows: &TagSet) -> bool {
    allows.is_empty()
        || (is_safe_relative_path(root)
            && p.allow_export.iter().any(|(r, pol_tags)| {
                path_matches_export_prefix(r, root) && allows.is_subset(pol_tags)
            }))
}

fn policy_allows_https(p: &Policy, host: &str, allows: &TagSet) -> bool {
    allows.is_empty()
        || p.allow_https
            .iter()
            .any(|(h, pol_tags)| h == host && allows.is_subset(pol_tags))
}

fn policy_allows_write(p: &Policy, db: &str, tbl: &str, allows: &TagSet) -> bool {
    allows.is_empty()
        || p.allow_write
            .iter()
            .any(|r| r.db == db && r.table == tbl && allows.is_subset(&r.tags))
}

pub fn check_cap_against_policy(pol: Option<&Policy>, ty: &Ty) -> Result<(), CheckError> {
    let Some(p) = pol else {
        return Ok(());
    };
    match ty {
        Ty::Declassify(_) => {
            if p.forbid_manual_declassify {
                err("dana.policy forbids manual Declassify capabilities")
            } else {
                Ok(())
            }
        }
        Ty::Console(allows) => {
            if allows.is_empty() || allows.is_subset(&p.allow_console) {
                Ok(())
            } else {
                err("Console capability exceeds dana.policy allowConsole")
            }
        }
        Ty::WriteFiles { root, allows } => {
            if policy_allows_export(p, root, allows) {
                Ok(())
            } else {
                err(format!(
                    "WriteFiles(\"{root}\") capability exceeds dana.policy"
                ))
            }
        }
        Ty::HttpsAllow { host, allows } => {
            if policy_allows_https(p, host, allows) {
                Ok(())
            } else {
                err(format!(
                    "HttpsAllow(\"{host}\") capability exceeds dana.policy"
                ))
            }
        }
        Ty::WriteTable {
            db,
            table_name,
            allows,
            ..
        } => {
            if policy_allows_write(p, db, table_name, allows) {
                Ok(())
            } else {
                err(format!(
                    "WriteTable({db}.{table_name}) capability exceeds dana.policy"
                ))
            }
        }
        _ => Ok(()),
    }
}

fn check_write_table_cols(
    src_cols: &[ColSpec],
    dest_cols: &[ColSpec],
    eff_row_tags: &TagSet,
    dest_row_tags: &TagSet,
) -> bool {
    if !dest_cols
        .iter()
        .all(|dc| eff_row_tags.is_subset(&dest_row_tags.union(&dc.tags)))
    {
        return false;
    }
    if src_cols.len() != dest_cols.len() {
        return false;
    }
    src_cols
        .iter()
        .zip(dest_cols)
        .all(|(sc, dc)| sc.name == dc.name && sc.ty == dc.ty && sc.tags.is_subset(&dc.tags))
}

pub fn check_host_op(
    prog: &Program,
    pc: &TagSet,
    in_spec: bool,
    op: &HostOp,
    args: &[LTy],
) -> Result<LTy, CheckError> {
    match (op, args) {
        (
            HostOp::ArgsGet,
            [
                LTy {
                    ty: Ty::Args,
                    tags: cap_ts,
                },
            ],
        ) => Ok(LTy::new(
            Ty::List(Box::new(LTy::public(Ty::Text))),
            cap_ts.union(pc),
        )),
        (
            HostOp::ClockNow,
            [
                LTy {
                    ty: Ty::Clock,
                    tags: cap_ts,
                },
            ],
        ) => Ok(LTy::new(Ty::Timestamp, cap_ts.union(pc))),
        (
            HostOp::ConsolePrint | HostOp::ConsoleError,
            [
                LTy {
                    ty: Ty::Console(allows),
                    tags: cap_ts,
                },
                LTy {
                    ty: Ty::Text,
                    tags: m_ts,
                },
            ],
        ) => {
            check_cap_against_policy(prog.policy.as_ref(), &Ty::Console(allows.clone()))?;
            let eff = pc.union(cap_ts).union(m_ts);
            if eff.is_subset(allows) {
                Ok(LTy::new(Ty::Unit, pc.clone()))
            } else {
                err("Console sink unauthorized for value or pc sensitivity tags")
            }
        }
        (
            HostOp::ConsolePrintTable,
            [
                LTy {
                    ty: Ty::Console(allows),
                    tags: cap_ts,
                },
                LTy {
                    ty: Ty::Table(tt),
                    tags: t_ts,
                },
            ],
        ) => {
            check_cap_against_policy(prog.policy.as_ref(), &Ty::Console(allows.clone()))?;
            let eff = pc.union(cap_ts).union(t_ts).union(&tt.total_tags());
            if eff.is_subset(allows) {
                Ok(LTy::new(Ty::Unit, pc.clone()))
            } else {
                err("Console.printTable unauthorized for table sensitivity tags")
            }
        }
        (
            HostOp::ReadCsv(schema_name),
            [
                LTy {
                    ty: Ty::ReadFiles,
                    tags: cap_ts,
                },
                LTy {
                    ty: Ty::Text,
                    tags: path_ts,
                },
            ],
        ) => match prog.find_schema(schema_name) {
            Some(s_decl) => {
                let ctx_ts = pc.union(cap_ts).union(path_ts);
                let good_tt = TableTy {
                    row_tags: s_decl.schema.row_tags.union(&ctx_ts),
                    order_tags: s_decl.schema.order_tags.union(&ctx_ts),
                    ..s_decl.schema.clone()
                };
                let base_bad = quarantine_bad_row_table_ty(&s_decl.schema);
                let bad_tt = TableTy {
                    row_tags: base_bad.row_tags.union(&ctx_ts),
                    order_tags: base_bad.order_tags.union(&ctx_ts),
                    ..base_bad
                };
                let tup_ty = Ty::Tuple(vec![
                    LTy::public(Ty::Table(good_tt)),
                    LTy::public(Ty::Table(bad_tt)),
                ]);
                Ok(LTy::new(
                    Ty::Result {
                        ok_ty: Box::new(tup_ty),
                        err_ty: Box::new(Ty::Text),
                    },
                    ctx_ts,
                ))
            }
            None => err(format!("unknown schema '{schema_name}' in readCsv")),
        },
        (
            HostOp::WriteFile,
            [
                LTy {
                    ty: Ty::WriteFiles { root, allows },
                    tags: cap_ts,
                },
                LTy {
                    ty: Ty::Text,
                    tags: p_ts,
                },
                LTy {
                    ty: Ty::Text,
                    tags: c_ts,
                },
            ],
        ) => {
            check_cap_against_policy(
                prog.policy.as_ref(),
                &Ty::WriteFiles {
                    root: root.clone(),
                    allows: allows.clone(),
                },
            )?;
            let eff = pc.union(cap_ts).union(p_ts).union(c_ts);
            if eff.is_subset(allows) {
                Ok(LTy::new(
                    Ty::Result {
                        ok_ty: Box::new(Ty::Unit),
                        err_ty: Box::new(Ty::Text),
                    },
                    eff,
                ))
            } else {
                err(format!(
                    "WriteFiles(\"{root}\") unauthorized for sensitivity tags"
                ))
            }
        }
        (
            HostOp::WriteReportHtml,
            [
                LTy {
                    ty: Ty::WriteFiles { root, allows },
                    tags: cap_ts,
                },
                LTy {
                    ty: Ty::Text,
                    tags: p_ts,
                },
                LTy {
                    ty: Ty::Report(r_ts),
                    tags: ro_ts,
                },
            ],
        ) => {
            check_cap_against_policy(
                prog.policy.as_ref(),
                &Ty::WriteFiles {
                    root: root.clone(),
                    allows: allows.clone(),
                },
            )?;
            let eff = pc.union(cap_ts).union(p_ts).union(r_ts).union(ro_ts);
            if eff.is_subset(allows) {
                Ok(LTy::new(
                    Ty::Result {
                        ok_ty: Box::new(Ty::Unit),
                        err_ty: Box::new(Ty::Text),
                    },
                    eff,
                ))
            } else {
                err(format!(
                    "WriteFiles(\"{root}\") unauthorized for Report sensitivity tags"
                ))
            }
        }
        (
            HostOp::WriteTable,
            [
                LTy {
                    ty:
                        cap_ty @ Ty::WriteTable {
                            db,
                            table_name: tbl,
                            dest_cols,
                            dest_row_tags,
                            allows,
                        },
                    tags: cap_ts,
                },
                LTy {
                    ty: Ty::Table(src_tt),
                    tags: src_ts,
                },
            ],
        ) => {
            check_cap_against_policy(prog.policy.as_ref(), cap_ty)?;
            let eff_row = pc
                .union(cap_ts)
                .union(src_ts)
                .union(&src_tt.row_tags.union(&src_tt.order_tags));
            let eff_all = eff_row.union(&src_tt.all_col_tags());
            if !eff_all.is_subset(allows) {
                err(format!(
                    "WriteTable({db}.{tbl}) allows set does not cover source sensitivity tags"
                ))
            } else if !check_write_table_cols(&src_tt.cols, dest_cols, &eff_row, dest_row_tags) {
                err(format!(
                    "WriteTable({db}.{tbl}) column-by-column schema or tag mismatch"
                ))
            } else {
                Ok(LTy::new(
                    Ty::Result {
                        ok_ty: Box::new(Ty::Int),
                        err_ty: Box::new(Ty::Text),
                    },
                    eff_row,
                ))
            }
        }
        (
            HostOp::DeclassifyApprove(clear_tags),
            [
                LTy {
                    ty: Ty::Declassify(allows),
                    tags: cap_ts,
                },
                val_lty,
                LTy {
                    ty: Ty::Text,
                    tags: reason_ts,
                },
            ],
        ) => {
            check_cap_against_policy(prog.policy.as_ref(), &Ty::Declassify(allows.clone()))?;
            if !valid_tag_set(prog, clear_tags) {
                err("invalid tag in declassifyApprove")
            } else if !clear_tags.is_subset(allows) {
                err("declassifyApprove clearTags exceeds Declassify capability allows")
            } else if !reason_ts.is_empty() {
                err("declassifyApprove audit reason must be public")
            } else {
                let base_tags = val_lty.tags.union(cap_ts).union(pc);
                match val_lty.ty {
                    Ty::Table(_) => {
                        err("declassifyApprove operates on scalar/composite values, not raw Tables")
                    }
                    _ => Ok(LTy::new(
                        val_lty.ty.clone(),
                        base_tags.diff(clear_tags).union(pc),
                    )),
                }
            }
        }
        (
            HostOp::RawSqlQuery {
                db: req_db,
                out_schema,
            },
            [
                LTy {
                    ty: Ty::RawReadDB(cap_db),
                    tags: cap_ts,
                },
                LTy {
                    ty: Ty::Text,
                    tags: sql_ts,
                },
            ],
        ) => {
            if req_db == cap_db && valid_table_ty(prog, out_schema) && sql_ts.is_empty() {
                let ctx_ts = cap_ts.union(pc);
                let out_tt = TableTy {
                    row_tags: out_schema.row_tags.union(&ctx_ts),
                    order_tags: out_schema.order_tags.union(&ctx_ts),
                    ..out_schema.clone()
                };
                Ok(LTy::new(
                    Ty::Result {
                        ok_ty: Box::new(Ty::Table(out_tt)),
                        err_ty: Box::new(Ty::Text),
                    },
                    ctx_ts,
                ))
            } else {
                err("rawSqlQuery DB mismatch, invalid schema, or non-public SQL string")
            }
        }
        (
            HostOp::HttpsGetJson,
            [
                LTy {
                    ty: Ty::HttpsAllow { host, allows },
                    tags: cap_ts,
                },
                LTy {
                    ty: Ty::Text,
                    tags: url_ts,
                },
            ],
        ) => {
            check_cap_against_policy(
                prog.policy.as_ref(),
                &Ty::HttpsAllow {
                    host: host.clone(),
                    allows: allows.clone(),
                },
            )?;
            let eff = pc.union(cap_ts).union(url_ts);
            if eff.is_subset(allows) {
                Ok(LTy::new(
                    Ty::Result {
                        ok_ty: Box::new(Ty::Text),
                        err_ty: Box::new(Ty::Text),
                    },
                    eff,
                ))
            } else {
                err(format!(
                    "HttpsAllow(\"{host}\") unauthorized for URL/pc sensitivity tags"
                ))
            }
        }
        (
            HostOp::ReadParquet(out_schema),
            [
                LTy {
                    ty: Ty::ReadFiles,
                    tags: cap_ts,
                },
                LTy {
                    ty: Ty::Text,
                    tags: path_ts,
                },
            ],
        ) => {
            if valid_table_ty(prog, out_schema) {
                let ctx_ts = pc.union(cap_ts).union(path_ts);
                let out_tt = TableTy {
                    row_tags: out_schema.row_tags.union(&ctx_ts),
                    order_tags: out_schema.order_tags.union(&ctx_ts),
                    ..out_schema.clone()
                };
                Ok(LTy::new(
                    Ty::Result {
                        ok_ty: Box::new(Ty::Table(out_tt)),
                        err_ty: Box::new(Ty::Text),
                    },
                    ctx_ts,
                ))
            } else {
                err("invalid schema in readParquet")
            }
        }
        (
            HostOp::WriteParquet | HostOp::WriteXlsx,
            [
                LTy {
                    ty: Ty::WriteFiles { root, allows },
                    tags: cap_ts,
                },
                LTy {
                    ty: Ty::Text,
                    tags: p_ts,
                },
                LTy {
                    ty: Ty::Table(src_tt),
                    tags: src_ts,
                },
            ],
        ) => {
            check_cap_against_policy(
                prog.policy.as_ref(),
                &Ty::WriteFiles {
                    root: root.clone(),
                    allows: allows.clone(),
                },
            )?;
            let eff = pc
                .union(cap_ts)
                .union(p_ts)
                .union(src_ts)
                .union(&src_tt.total_tags());
            if eff.is_subset(allows) {
                Ok(LTy::new(
                    Ty::Result {
                        ok_ty: Box::new(Ty::Unit),
                        err_ty: Box::new(Ty::Text),
                    },
                    eff,
                ))
            } else {
                err(format!(
                    "WriteFiles(\"{root}\") unauthorized for Parquet/XLSX table tags"
                ))
            }
        }
        (HostOp::FakeConsole(allows), []) => {
            if in_spec && valid_tag_set(prog, allows) {
                Ok(LTy::new(Ty::Console(allows.clone()), pc.clone()))
            } else {
                err("fakeConsole is only permitted in spec functions (test/example/promise)")
            }
        }
        (HostOp::FakeFiles(allows), []) => {
            if in_spec && valid_tag_set(prog, allows) {
                Ok(LTy::new(
                    Ty::WriteFiles {
                        root: "mem://".to_string(),
                        allows: allows.clone(),
                    },
                    pc.clone(),
                ))
            } else {
                err("fakeFiles is only permitted in spec functions")
            }
        }
        (HostOp::FakeDB(db), []) => {
            if in_spec {
                Ok(LTy::new(Ty::ReadDB(db.clone()), pc.clone()))
            } else {
                err("fakeDB is only permitted in spec functions")
            }
        }
        (HostOp::FakeHttps { host, allows }, []) => {
            if in_spec && valid_tag_set(prog, allows) {
                Ok(LTy::new(
                    Ty::HttpsAllow {
                        host: host.clone(),
                        allows: allows.clone(),
                    },
                    pc.clone(),
                ))
            } else {
                err("fakeHttps is only permitted in spec functions")
            }
        }
        (
            HostOp::FakeSecret(name),
            [
                LTy {
                    ty: Ty::Text,
                    tags: val_ts,
                },
            ],
        ) => {
            if in_spec && val_ts.is_empty() {
                Ok(LTy::new(
                    Ty::Secret(name.clone()),
                    pc.union(&TagSet::singleton("secret")),
                ))
            } else {
                err("fakeSecret is only permitted in spec functions with public fixture text")
            }
        }
        _ => err("ill-typed HostOp"),
    }
}

// ---------------------------------------------------------------------------
// Relational Plan Helper Functions
// ---------------------------------------------------------------------------

pub fn resolve_join_pairs(
    l_tt: &TableTy,
    r_tt: &TableTy,
    on: &JoinOn,
) -> Result<Vec<(ColSpec, ColSpec)>, CheckError> {
    let raw_pairs: Vec<(&str, &str)> = match on {
        JoinOn::SameKeys(ks) => ks.iter().map(|k| (k.as_str(), k.as_str())).collect(),
        JoinOn::Pairs(ps) => ps.iter().map(|(l, r)| (l.as_str(), r.as_str())).collect(),
    };
    if raw_pairs.is_empty() {
        return err("join requires at least one key pair");
    }
    let mut out = Vec::with_capacity(raw_pairs.len());
    for (lk, rk) in raw_pairs {
        match (l_tt.find_col(lk), r_tt.find_col(rk)) {
            (Some(lc), Some(rc)) => {
                if lc.ty == rc.ty && is_equatable_ty(&lc.ty.to_ty()) {
                    out.push((lc.clone(), rc.clone()));
                } else {
                    return err(format!("join key type mismatch between '{lk}' and '{rk}'"));
                }
            }
            _ => return err(format!("missing join key '{lk}' or '{rk}'")),
        }
    }
    Ok(out)
}

pub fn build_joined_cols(
    kind: JoinKind,
    l_cols: &[ColSpec],
    r_cols: &[ColSpec],
    on: &JoinOn,
    suffixes: &Option<(String, String)>,
) -> Result<Vec<ColSpec>, CheckError> {
    match kind {
        JoinKind::Semi | JoinKind::Anti => Ok(l_cols
            .iter()
            .map(|c| ColSpec {
                agg_kind: AggKind::Raw,
                ..c.clone()
            })
            .collect()),
        _ => {
            let same_key_names: &[Ident] = match on {
                JoinOn::SameKeys(ks) => ks,
                JoinOn::Pairs(_) => &[],
            };
            let r_filtered: Vec<&ColSpec> = r_cols
                .iter()
                .filter(|rc| !same_key_names.contains(&rc.name))
                .collect();
            let is_left_outer = matches!(kind, JoinKind::LeftOne | JoinKind::LeftManyToOne);
            let l_updated: Vec<ColSpec> = l_cols
                .iter()
                .map(|lc| {
                    if same_key_names.contains(&lc.name) {
                        match r_cols.iter().find(|rc| rc.name == lc.name) {
                            Some(rc) => ColSpec {
                                tags: lc.tags.union(&rc.tags),
                                bucketed: false,
                                agg_kind: AggKind::Raw,
                                ..lc.clone()
                            },
                            None => ColSpec {
                                agg_kind: AggKind::Raw,
                                ..lc.clone()
                            },
                        }
                    } else {
                        ColSpec {
                            agg_kind: AggKind::Raw,
                            ..lc.clone()
                        }
                    }
                })
                .collect();
            let r_prepared: Vec<ColSpec> = r_filtered
                .into_iter()
                .map(|rc| ColSpec {
                    ty: if is_left_outer {
                        ensure_option_scalar(&rc.ty)
                    } else {
                        rc.ty.clone()
                    },
                    bucketed: if is_left_outer { false } else { rc.bucketed },
                    agg_kind: AggKind::Raw,
                    ..rc.clone()
                })
                .collect();
            let l_names: Vec<Ident> = l_updated.iter().map(|c| c.name.clone()).collect();
            let r_names: Vec<Ident> = r_prepared.iter().map(|c| c.name.clone()).collect();
            let has_collision = l_names.iter().any(|n| r_names.contains(n));
            if !has_collision {
                let mut combined = l_updated;
                combined.extend(r_prepared);
                return Ok(combined);
            }
            match suffixes {
                None => err("overlapping non-key join columns require explicit suffixes"),
                Some((s_l, s_r)) => {
                    if s_l == s_r || (s_l.is_empty() && s_r.is_empty()) {
                        return err("join suffixes must be distinct");
                    }
                    let l_renamed: Vec<ColSpec> = l_updated
                        .into_iter()
                        .map(|c| {
                            if r_names.contains(&c.name) {
                                ColSpec {
                                    name: format!("{}{s_l}", c.name),
                                    ..c
                                }
                            } else {
                                c
                            }
                        })
                        .collect();
                    let r_renamed: Vec<ColSpec> = r_prepared
                        .into_iter()
                        .map(|c| {
                            if l_names.contains(&c.name) {
                                ColSpec {
                                    name: format!("{}{s_r}", c.name),
                                    ..c
                                }
                            } else {
                                c
                            }
                        })
                        .collect();
                    let mut combined = l_renamed;
                    combined.extend(r_renamed);
                    let names: Vec<Ident> = combined.iter().map(|c| c.name.clone()).collect();
                    if distinct_idents(&names) {
                        Ok(combined)
                    } else {
                        err("join suffixes still produced duplicate column names")
                    }
                }
            }
        }
    }
}

fn check_bucket_cuts(
    prog: &Program,
    src_ty: &ScalarTy,
    cuts: &[Literal],
    labels: &[String],
) -> bool {
    !cuts.is_empty()
        && labels.len() == cuts.len() + 1
        && is_ordered_scalar_ty(&src_ty.to_ty())
        && cuts.iter().all(|lit| {
            check_literal(prog, &TagSet::empty(), lit).is_ok_and(|lty| lty.ty == src_ty.to_ty())
        })
}

pub fn check_agg_item(
    prog: &Program,
    env: &[(Ident, LTy)],
    in_tt: &TableTy,
    item: &AggItem,
) -> Result<ColSpec, CheckError> {
    let arc_env = ArcTyEnv::from_slice(env);
    check_agg_item_arc(prog, &arc_env, in_tt, item)
}

fn check_agg_item_arc(
    prog: &Program,
    env: &ArcTyEnv,
    in_tt: &TableTy,
    item: &AggItem,
) -> Result<ColSpec, CheckError> {
    let kind = if item.op.is_blending() {
        AggKind::Blending
    } else {
        AggKind::NonBlending
    };
    let ord_tags = if item.op.is_order_sensitive() {
        in_tt.order_tags.clone()
    } else {
        TagSet::empty()
    };
    let base_ctx = in_tt.row_tags.union(&ord_tags);
    match (&item.op, &item.arg) {
        (crate::core::syntax::AggOp::Count, None) => Ok(ColSpec {
            name: item.name.clone(),
            ty: ScalarTy::Int,
            tags: base_ctx,
            bucketed: false,
            agg_kind: kind,
        }),
        (crate::core::syntax::AggOp::CountDistinct, Some(re)) => {
            let (s_ty, r_tags) = check_row_expr_arc(prog, env, &in_tt.cols, re)?;
            if is_equatable_ty(&s_ty.to_ty()) {
                Ok(ColSpec {
                    name: item.name.clone(),
                    ty: ScalarTy::Int,
                    tags: r_tags.union(&base_ctx),
                    bucketed: false,
                    agg_kind: kind,
                })
            } else {
                err("countDistinct requires equatable argument")
            }
        }
        (crate::core::syntax::AggOp::Sum, Some(re)) => {
            let (s_ty, r_tags) = check_row_expr_arc(prog, env, &in_tt.cols, re)?;
            match numeric_core_of_scalar(&s_ty) {
                Some(num_ty) => Ok(ColSpec {
                    name: item.name.clone(),
                    ty: num_ty,
                    tags: r_tags.union(&base_ctx),
                    bucketed: false,
                    agg_kind: kind,
                }),
                None => err("sum requires numeric argument"),
            }
        }
        (crate::core::syntax::AggOp::Mean | crate::core::syntax::AggOp::Median, Some(re)) => {
            let (s_ty, r_tags) = check_row_expr_arc(prog, env, &in_tt.cols, re)?;
            match numeric_core_of_scalar(&s_ty) {
                Some(ScalarTy::Int) => Ok(ColSpec {
                    name: item.name.clone(),
                    ty: ScalarTy::Option(Box::new(ScalarTy::Float)),
                    tags: r_tags.union(&base_ctx),
                    bucketed: false,
                    agg_kind: kind,
                }),
                Some(num_ty) => Ok(ColSpec {
                    name: item.name.clone(),
                    ty: ScalarTy::Option(Box::new(num_ty)),
                    tags: r_tags.union(&base_ctx),
                    bucketed: false,
                    agg_kind: kind,
                }),
                None => err("mean/median requires numeric argument"),
            }
        }
        (crate::core::syntax::AggOp::Stddev | crate::core::syntax::AggOp::Variance, Some(re)) => {
            let (s_ty, r_tags) = check_row_expr_arc(prog, env, &in_tt.cols, re)?;
            if numeric_core_of_scalar(&s_ty).is_some() {
                Ok(ColSpec {
                    name: item.name.clone(),
                    ty: ScalarTy::Option(Box::new(ScalarTy::Float)),
                    tags: r_tags.union(&base_ctx),
                    bucketed: false,
                    agg_kind: kind,
                })
            } else {
                err("stddev/variance requires numeric argument")
            }
        }
        (crate::core::syntax::AggOp::Percentile(p), Some(re)) => {
            let (s_ty, r_tags) = check_row_expr_arc(prog, env, &in_tt.cols, re)?;
            let pf = p.to_f64();
            if pf.is_nan() || !(0.0..=1.0).contains(&pf) {
                err("percentile parameter p must be finite in [0.0, 1.0]")
            } else if numeric_core_of_scalar(&s_ty).is_some() {
                Ok(ColSpec {
                    name: item.name.clone(),
                    ty: ScalarTy::Option(Box::new(ScalarTy::Float)),
                    tags: r_tags.union(&base_ctx),
                    bucketed: false,
                    agg_kind: kind,
                })
            } else {
                err("percentile requires numeric argument")
            }
        }
        (crate::core::syntax::AggOp::Min | crate::core::syntax::AggOp::Max, Some(re)) => {
            let (s_ty, r_tags) = check_row_expr_arc(prog, env, &in_tt.cols, re)?;
            let b_ty = base_of_scalar(&s_ty).clone();
            if is_ordered_scalar_ty(&b_ty.to_ty()) {
                Ok(ColSpec {
                    name: item.name.clone(),
                    ty: ScalarTy::Option(Box::new(b_ty)),
                    tags: r_tags.union(&base_ctx),
                    bucketed: false,
                    agg_kind: kind,
                })
            } else {
                err("min/max requires ordered scalar argument")
            }
        }
        (crate::core::syntax::AggOp::First | crate::core::syntax::AggOp::Last, Some(re)) => {
            let (s_ty, r_tags) = check_row_expr_arc(prog, env, &in_tt.cols, re)?;
            Ok(ColSpec {
                name: item.name.clone(),
                ty: ensure_option_scalar(&s_ty),
                tags: r_tags.union(&base_ctx),
                bucketed: false,
                agg_kind: kind,
            })
        }
        _ => err(format!(
            "invalid argument arity for aggregate '{}'",
            item.name
        )),
    }
}

pub fn apply_derive_item(
    prog: &Program,
    env: &[(Ident, LTy)],
    cols: &[ColSpec],
    item: &DeriveItem,
) -> Result<Vec<ColSpec>, CheckError> {
    let arc_env = ArcTyEnv::from_slice(env);
    apply_derive_item_arc(prog, &arc_env, cols, item)
}

pub(crate) fn apply_derive_item_arc(
    prog: &Program,
    env: &ArcTyEnv,
    cols: &[ColSpec],
    item: &DeriveItem,
) -> Result<Vec<ColSpec>, CheckError> {
    match item {
        DeriveItem::ColExpr { name, expr } => {
            let (s_ty, r_tags) = check_row_expr_arc(prog, env, cols, expr)?;
            let new_col = ColSpec {
                name: name.clone(),
                ty: s_ty,
                tags: r_tags,
                bucketed: false,
                agg_kind: AggKind::Raw,
            };
            if cols.iter().any(|c| c.name == *name) {
                Ok(cols
                    .iter()
                    .map(|c| {
                        if c.name == *name {
                            new_col.clone()
                        } else {
                            c.clone()
                        }
                    })
                    .collect())
            } else {
                let mut out = cols.to_vec();
                out.push(new_col);
                Ok(out)
            }
        }
        DeriveItem::BucketCol {
            name,
            source,
            cuts,
            labels,
        } => match cols.iter().find(|c| c.name == *source) {
            Some(src_col) => {
                if check_bucket_cuts(prog, &src_col.ty, cuts, labels) {
                    let new_col = ColSpec {
                        name: name.clone(),
                        ty: ScalarTy::Text,
                        tags: src_col.tags.clone(),
                        bucketed: true,
                        agg_kind: AggKind::Raw,
                    };
                    if cols.iter().any(|c| c.name == *name) {
                        Ok(cols
                            .iter()
                            .map(|c| {
                                if c.name == *name {
                                    new_col.clone()
                                } else {
                                    c.clone()
                                }
                            })
                            .collect())
                    } else {
                        let mut out = cols.to_vec();
                        out.push(new_col);
                        Ok(out)
                    }
                } else {
                    err(format!("invalid cuts/labels in bucketCol '{name}'"))
                }
            }
            None => err(format!("unknown source column '{source}' in bucketCol")),
        },
    }
}

pub fn apply_window_item(
    cols: &[ColSpec],
    order_tags: &TagSet,
    item: &WindowItem,
) -> Result<Vec<ColSpec>, CheckError> {
    let over_ok = item.over.iter().all(|k| cols.iter().any(|c| c.name == *k));
    let order_ok = item.order.iter().all(|(k, _)| {
        cols.iter()
            .find(|c| c.name == *k)
            .is_some_and(|c| is_ordered_scalar_ty(&base_of_scalar(&c.ty).to_ty()))
    });
    if !over_ok || !order_ok {
        return err(format!(
            "window item '{}' references invalid partition/order columns",
            item.name
        ));
    }
    let over_tags = TagSet::union_list(
        item.over
            .iter()
            .filter_map(|k| cols.iter().find(|c| c.name == *k).map(|c| &c.tags)),
    );
    let ord_key_tags = TagSet::union_list(
        item.order
            .iter()
            .filter_map(|(k, _)| cols.iter().find(|c| c.name == *k).map(|c| &c.tags)),
    );
    let ctx_tags = over_tags.union(&ord_key_tags).union(order_tags);
    let fn_spec: Option<(ScalarTy, TagSet)> = match &item.win_fn {
        WindowFn::RowNumber => Some((ScalarTy::Int, ctx_tags)),
        WindowFn::Rank { col } => cols.iter().find(|c| c.name == *col).and_then(|c| {
            if is_ordered_scalar_ty(&base_of_scalar(&c.ty).to_ty()) {
                Some((ScalarTy::Int, c.tags.union(&ctx_tags)))
            } else {
                None
            }
        }),
        WindowFn::Lag { col, .. } | WindowFn::Lead { col, .. } => cols
            .iter()
            .find(|c| c.name == *col)
            .map(|c| (ensure_option_scalar(&c.ty), c.tags.union(&ctx_tags))),
        WindowFn::RunningSum { col } => cols.iter().find(|c| c.name == *col).and_then(|c| {
            numeric_core_of_scalar(&c.ty).map(|n_ty| (n_ty, c.tags.union(&ctx_tags)))
        }),
        WindowFn::RollingMean { col, window_size } => {
            if window_size.is_zero() {
                None
            } else {
                cols.iter().find(|c| c.name == *col).and_then(|c| {
                    numeric_core_of_scalar(&c.ty).map(|_| {
                        (
                            ScalarTy::Option(Box::new(ScalarTy::Float)),
                            c.tags.union(&ctx_tags),
                        )
                    })
                })
            }
        }
    };
    match fn_spec {
        None => err(format!("ill-typed window function in '{}'", item.name)),
        Some((w_ty, w_tags)) => {
            let new_col = ColSpec {
                name: item.name.clone(),
                ty: w_ty,
                tags: w_tags,
                bucketed: false,
                agg_kind: AggKind::Raw,
            };
            if cols.iter().any(|c| c.name == item.name) {
                Ok(cols
                    .iter()
                    .map(|c| {
                        if c.name == item.name {
                            new_col.clone()
                        } else {
                            c.clone()
                        }
                    })
                    .collect())
            } else {
                let mut out = cols.to_vec();
                out.push(new_col);
                Ok(out)
            }
        }
    }
}

fn apply_derive_items_arc(
    prog: &Program,
    env: &ArcTyEnv,
    init_cols: Vec<ColSpec>,
    items: &[DeriveItem],
) -> Result<Vec<ColSpec>, CheckError> {
    let mut cols = init_cols;
    for item in items {
        cols = apply_derive_item_arc(prog, env, &cols, item)?;
    }
    Ok(cols)
}

fn apply_window_items(
    order_tags: &TagSet,
    init_cols: Vec<ColSpec>,
    items: &[WindowItem],
) -> Result<Vec<ColSpec>, CheckError> {
    let mut cols = init_cols;
    for item in items {
        cols = apply_window_item(&cols, order_tags, item)?;
    }
    Ok(cols)
}

fn check_agg_item_list_arc(
    prog: &Program,
    env: &ArcTyEnv,
    in_tt: &TableTy,
    aggs: &[AggItem],
) -> Result<Vec<ColSpec>, CheckError> {
    aggs.iter()
        .map(|a| check_agg_item_arc(prog, env, in_tt, a))
        .collect()
}

#[must_use]
pub fn merge_union_cols(l_cols: &[ColSpec], r_cols: &[ColSpec]) -> Option<Vec<ColSpec>> {
    if l_cols.len() != r_cols.len() {
        return None;
    }
    let mut out = Vec::with_capacity(l_cols.len());
    for (lc, rc) in l_cols.iter().zip(r_cols) {
        if lc.name == rc.name && lc.ty == rc.ty {
            out.push(ColSpec {
                name: lc.name.clone(),
                ty: lc.ty.clone(),
                tags: lc.tags.union(&rc.tags),
                bucketed: lc.bucketed && rc.bucketed,
                agg_kind: AggKind::Raw,
            });
        } else {
            return None;
        }
    }
    Some(out)
}

// ---------------------------------------------------------------------------
// Case Arm Exhaustiveness & Heuristic Join Inference
// ---------------------------------------------------------------------------

fn expected_case_specs(
    prog: &Program,
    scrut_ty: &Ty,
    scrut_tags: &TagSet,
) -> Result<Vec<(Ident, Vec<LTy>)>, CheckError> {
    match scrut_ty {
        Ty::Bool => Ok(vec![
            ("true".to_string(), vec![]),
            ("false".to_string(), vec![]),
        ]),
        Ty::Option(inner) => Ok(vec![
            ("None".to_string(), vec![]),
            (
                "Some".to_string(),
                vec![LTy::new(inner.as_ref().clone(), scrut_tags.clone())],
            ),
        ]),
        Ty::Result { ok_ty, err_ty } => Ok(vec![
            (
                "Ok".to_string(),
                vec![LTy::new(ok_ty.as_ref().clone(), scrut_tags.clone())],
            ),
            (
                "Error".to_string(),
                vec![LTy::new(err_ty.as_ref().clone(), scrut_tags.clone())],
            ),
        ]),
        Ty::Data(d_name) => match prog.find_data(d_name) {
            Some(d_decl) => Ok(d_decl
                .ctors
                .iter()
                .map(|c| {
                    (
                        c.name.clone(),
                        c.fields.iter().map(|f| f.add_tags(scrut_tags)).collect(),
                    )
                })
                .collect()),
            None => err(format!("unknown data type '{d_name}' in Case")),
        },
        _ => err("Case scrutinee must be Bool, Option, Result, or Data"),
    }
}

#[must_use]
pub fn infer_jump_pc(
    prog: &Program,
    target: &str,
    env: &[(Ident, LTy)],
    cur_pc: &TagSet,
    expr: &Expr,
) -> TagSet {
    let arc_env = ArcTyEnv::from_slice(env);
    infer_jump_pc_arc(prog, target, &arc_env, cur_pc, expr)
}

enum JumpPcTask<'a> {
    Eval {
        target: &'a str,
        env: ArcTyEnv,
        cur_pc: TagSet,
        expr: &'a Expr,
    },
    JoinAfterSub {
        outer_target: &'a str,
        env: ArcTyEnv,
        cur_pc: TagSet,
        params: &'a [(Ident, LTy)],
        rhs: &'a Expr,
        body: &'a Expr,
    },
}

pub(crate) fn infer_jump_pc_arc(
    prog: &Program,
    target: &str,
    env: &ArcTyEnv,
    cur_pc: &TagSet,
    expr: &Expr,
) -> TagSet {
    let mut acc_stack = vec![TagSet::empty()];
    let mut tasks = vec![JumpPcTask::Eval {
        target,
        env: env.clone(),
        cur_pc: cur_pc.clone(),
        expr,
    }];
    while let Some(task) = tasks.pop() {
        match task {
            JumpPcTask::Eval {
                target,
                env,
                cur_pc,
                expr,
            } => match expr {
                Expr::Lit(_)
                | Expr::Var(_)
                | Expr::ConstRef(_)
                | Expr::TableLit { .. }
                | Expr::Lam { .. }
                | Expr::App { .. }
                | Expr::Call { .. }
                | Expr::Tuple(_)
                | Expr::Proj { .. }
                | Expr::Ctor { .. }
                | Expr::Prim { .. }
                | Expr::Rel(_)
                | Expr::Host { .. }
                | Expr::Stop { .. }
                | Expr::Fail(_) => {}
                Expr::LetE {
                    name,
                    lty,
                    bound,
                    body,
                } => {
                    let body_env = ArcTyEnv::cons(name.clone(), lty.clone(), env.clone());
                    tasks.push(JumpPcTask::Eval {
                        target,
                        env: body_env,
                        cur_pc: cur_pc.clone(),
                        expr: body,
                    });
                    tasks.push(JumpPcTask::Eval {
                        target,
                        env,
                        cur_pc,
                        expr: bound,
                    });
                }
                Expr::IfE {
                    cond,
                    then_br,
                    else_br,
                } => {
                    let cond_guess = expr_quick_tags_arc(prog, &env, cond);
                    let br_pc = cur_pc.union(&cond_guess);
                    tasks.push(JumpPcTask::Eval {
                        target,
                        env: env.clone(),
                        cur_pc: br_pc.clone(),
                        expr: else_br,
                    });
                    tasks.push(JumpPcTask::Eval {
                        target,
                        env,
                        cur_pc: br_pc,
                        expr: then_br,
                    });
                }
                Expr::CaseE { scrut, arms } => {
                    let scrut_guess = expr_quick_tags_arc(prog, &env, scrut);
                    let arm_pc = cur_pc.union(&scrut_guess);
                    for a in arms.iter().rev() {
                        tasks.push(JumpPcTask::Eval {
                            target,
                            env: env.clone(),
                            cur_pc: arm_pc.clone(),
                            expr: &a.body,
                        });
                    }
                }
                Expr::Join {
                    label,
                    params,
                    rhs,
                    body,
                } => {
                    if label != target {
                        tasks.push(JumpPcTask::JoinAfterSub {
                            outer_target: target,
                            env: env.clone(),
                            cur_pc: cur_pc.clone(),
                            params,
                            rhs,
                            body,
                        });
                        tasks.push(JumpPcTask::Eval {
                            target: label,
                            env,
                            cur_pc,
                            expr: body,
                        });
                        acc_stack.push(TagSet::empty());
                    }
                }
                Expr::Jump { label, .. } => {
                    if label == target
                        && let Some(acc) = acc_stack.last_mut()
                    {
                        *acc = acc.union(&cur_pc);
                    }
                }
            },
            JumpPcTask::JoinAfterSub {
                outer_target,
                env,
                cur_pc,
                params,
                rhs,
                body,
            } => {
                let Some(sub_pc) = acc_stack.pop() else {
                    unreachable!("acc_stack balanced");
                };
                let rhs_env = env.extend_slice(params);
                let rhs_pc = cur_pc.union(&sub_pc);
                tasks.push(JumpPcTask::Eval {
                    target: outer_target,
                    env: rhs_env,
                    cur_pc: rhs_pc,
                    expr: rhs,
                });
                tasks.push(JumpPcTask::Eval {
                    target: outer_target,
                    env,
                    cur_pc,
                    expr: body,
                });
            }
        }
    }
    acc_stack.pop().unwrap_or_default()
}

fn expr_quick_tags_arc(prog: &Program, env: &ArcTyEnv, expr: &Expr) -> TagSet {
    expr_quick_tags_worklist(prog, vec![(env.clone(), expr)])
}

fn expr_quick_tags_list_arc(prog: &Program, env: &ArcTyEnv, exprs: &[Expr]) -> TagSet {
    let stack = exprs.iter().map(|e| (env.clone(), e)).collect();
    expr_quick_tags_worklist(prog, stack)
}

fn expr_quick_tags_worklist(prog: &Program, mut stack: Vec<(ArcTyEnv, &Expr)>) -> TagSet {
    let mut acc = TagSet::empty();
    while let Some((env, expr)) = stack.pop() {
        match expr {
            Expr::Lit(_)
            | Expr::TableLit { .. }
            | Expr::Lam { .. }
            | Expr::Rel(_)
            | Expr::Stop { .. }
            | Expr::Fail(_) => {}
            Expr::Var(x) => {
                if let Some(lty) = env.lookup(x) {
                    acc = acc.union(&lty.effective_tags());
                }
            }
            Expr::ConstRef(c) => {
                if let Some(d) = prog.find_const(c) {
                    acc = acc.union(&d.lty.effective_tags());
                }
            }
            Expr::LetE {
                name,
                lty,
                bound,
                body,
            } => {
                let body_env = ArcTyEnv::cons(name.clone(), lty.clone(), env.clone());
                stack.push((body_env, body));
                stack.push((env, bound));
            }
            Expr::IfE {
                cond,
                then_br,
                else_br,
            } => {
                stack.push((env.clone(), else_br));
                stack.push((env.clone(), then_br));
                stack.push((env, cond));
            }
            Expr::CaseE { scrut, .. } => {
                stack.push((env, scrut));
            }
            Expr::App { fn_expr, args } => {
                for a in args {
                    stack.push((env.clone(), a));
                }
                stack.push((env, fn_expr));
            }
            Expr::Call { fn_name, args } => {
                if let Some(d) = prog.find_fun(fn_name) {
                    acc = acc.union(&d.ret.effective_tags());
                }
                for a in args {
                    stack.push((env.clone(), a));
                }
            }
            Expr::Join { rhs, body, .. } => {
                stack.push((env.clone(), body));
                stack.push((env, rhs));
            }
            Expr::Jump { args, .. }
            | Expr::Tuple(args)
            | Expr::Ctor { args, .. }
            | Expr::Prim { args, .. }
            | Expr::Host { args, .. } => {
                for a in args {
                    stack.push((env.clone(), a));
                }
            }
            Expr::Proj { tup, .. } => {
                stack.push((env, tup));
            }
        }
    }
    acc
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PlanTy {
    Table(TableTy),
    Dynamic(TagSet),
}

impl PlanTy {
    #[must_use]
    pub fn to_lty(&self, pc: &TagSet) -> LTy {
        match self {
            Self::Table(tt) => {
                let tt_out = TableTy {
                    row_tags: tt.row_tags.union(pc),
                    order_tags: tt.order_tags.union(pc),
                    ..tt.clone()
                };
                LTy::new(Ty::Table(tt_out), pc.clone())
            }
            Self::Dynamic(ts) => LTy::new(Ty::DynamicTable(ts.union(pc)), pc.clone()),
        }
    }
}

enum InferBuild<'a> {
    If(TagSet),
    CaseArms(usize, TagSet),
    App(TagSet),
    Tuple(usize, TagSet),
    Proj(&'a BigInt, TagSet),
    Prim(&'a PrimOp, usize, TagSet),
    Host(&'a HostOp, usize, TagSet),
    PlanSourceExpr(TagSet),
    PlanSourceDB(&'a TableTy, TagSet),
    PlanJoin {
        kind: JoinKind,
        on: &'a JoinOn,
        suffixes: &'a Option<(String, String)>,
        cur_pc: TagSet,
    },
    PlanUnion(TagSet),
    PlanUnary(&'a Plan, ArcTyEnv, TagSet),
}

enum InferTask<'a> {
    Expr {
        env: ArcTyEnv,
        jenv: ArcJoinEnv,
        cur_pc: TagSet,
        skip_labels: Arc<Vec<Ident>>,
        expr: &'a Expr,
    },
    Plan {
        env: ArcTyEnv,
        cur_pc: TagSet,
        skip_labels: Arc<Vec<Ident>>,
        plan: &'a Plan,
    },
    JoinAfterRhs {
        env: ArcTyEnv,
        jenv: ArcJoinEnv,
        cur_pc: TagSet,
        skip_labels: Arc<Vec<Ident>>,
        body: &'a Expr,
    },
    Finish(InferBuild<'a>),
}

fn infer_branch_lty_arc(
    prog: &Program,
    env: &ArcTyEnv,
    jenv: &ArcJoinEnv,
    cur_pc: &TagSet,
    skip_labels: Arc<Vec<Ident>>,
    expr: &Expr,
) -> Option<LTy> {
    let mut tasks = vec![InferTask::Expr {
        env: env.clone(),
        jenv: jenv.clone(),
        cur_pc: cur_pc.clone(),
        skip_labels,
        expr,
    }];
    let mut vals: Vec<Option<LTy>> = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            InferTask::Expr {
                env,
                jenv,
                cur_pc,
                skip_labels,
                expr,
            } => match expr {
                Expr::Lit(v) => vals.push(check_literal(prog, &cur_pc, v).ok()),
                Expr::Var(x) => vals.push(env.lookup(x).map(|l| l.add_tags(&cur_pc))),
                Expr::ConstRef(c) => {
                    vals.push(prog.find_const(c).map(|d| d.lty.add_tags(&cur_pc)));
                }
                Expr::LetE {
                    name, lty, body, ..
                } => {
                    let next_env = ArcTyEnv::cons(name.clone(), lty.add_tags(&cur_pc), env);
                    tasks.push(InferTask::Expr {
                        env: next_env,
                        jenv,
                        cur_pc,
                        skip_labels,
                        expr: body,
                    });
                }
                Expr::IfE {
                    cond,
                    then_br,
                    else_br,
                } => {
                    let br_pc = cur_pc.union(&expr_quick_tags_arc(prog, &env, cond));
                    tasks.push(InferTask::Finish(InferBuild::If(br_pc.clone())));
                    tasks.push(InferTask::Expr {
                        env: env.clone(),
                        jenv: jenv.clone(),
                        cur_pc: br_pc.clone(),
                        skip_labels: Arc::clone(&skip_labels),
                        expr: else_br,
                    });
                    tasks.push(InferTask::Expr {
                        env,
                        jenv,
                        cur_pc: br_pc,
                        skip_labels,
                        expr: then_br,
                    });
                }
                Expr::CaseE { scrut, arms } => {
                    let arm_pc = cur_pc.union(&expr_quick_tags_arc(prog, &env, scrut));
                    tasks.push(InferTask::Finish(InferBuild::CaseArms(
                        arms.len(),
                        arm_pc.clone(),
                    )));
                    for arm in arms.iter().rev() {
                        tasks.push(InferTask::Expr {
                            env: env.clone(),
                            jenv: jenv.clone(),
                            cur_pc: arm_pc.clone(),
                            skip_labels: Arc::clone(&skip_labels),
                            expr: &arm.body,
                        });
                    }
                }
                Expr::Lam {
                    params, pc, ret, ..
                } => vals.push(Some(LTy::new(
                    Ty::Fn {
                        params: params.iter().map(|(_, l)| l.clone()).collect(),
                        pc: pc.clone(),
                        ret: Box::new(ret.clone()),
                    },
                    cur_pc,
                ))),
                Expr::Call { fn_name, .. } => {
                    vals.push(prog.find_fun(fn_name).map(|d| d.ret.add_tags(&cur_pc)));
                }
                Expr::App { fn_expr, .. } => {
                    tasks.push(InferTask::Finish(InferBuild::App(cur_pc.clone())));
                    tasks.push(InferTask::Expr {
                        env,
                        jenv,
                        cur_pc,
                        skip_labels,
                        expr: fn_expr,
                    });
                }
                Expr::Join {
                    label,
                    params,
                    rhs,
                    body,
                } => {
                    let sub_env = env.extend_slice(params);
                    let mut next_skip_vec = Vec::with_capacity(skip_labels.len() + 1);
                    next_skip_vec.push(label.clone());
                    next_skip_vec.extend(skip_labels.iter().cloned());
                    let next_skip = Arc::new(next_skip_vec);
                    tasks.push(InferTask::JoinAfterRhs {
                        env,
                        jenv: jenv.clone(),
                        cur_pc: cur_pc.clone(),
                        skip_labels: Arc::clone(&next_skip),
                        body,
                    });
                    tasks.push(InferTask::Expr {
                        env: sub_env,
                        jenv,
                        cur_pc,
                        skip_labels: next_skip,
                        expr: rhs,
                    });
                }
                Expr::Jump { label, .. } => {
                    if skip_labels.contains(label) {
                        vals.push(None);
                    } else {
                        vals.push(jenv.lookup(label).map(|sig| sig.ret_lty.clone()));
                    }
                }
                Expr::Tuple(es) => {
                    tasks.push(InferTask::Finish(InferBuild::Tuple(
                        es.len(),
                        cur_pc.clone(),
                    )));
                    for e in es.iter().rev() {
                        tasks.push(InferTask::Expr {
                            env: env.clone(),
                            jenv: jenv.clone(),
                            cur_pc: cur_pc.clone(),
                            skip_labels: Arc::clone(&skip_labels),
                            expr: e,
                        });
                    }
                }
                Expr::Proj { tup, idx } => {
                    tasks.push(InferTask::Finish(InferBuild::Proj(idx, cur_pc.clone())));
                    tasks.push(InferTask::Expr {
                        env,
                        jenv,
                        cur_pc,
                        skip_labels,
                        expr: tup,
                    });
                }
                Expr::Ctor {
                    type_name, args, ..
                } => vals.push(Some(LTy::new(
                    Ty::Data(type_name.clone()),
                    expr_quick_tags_list_arc(prog, &env, args).union(&cur_pc),
                ))),
                Expr::TableLit { schema, .. } => {
                    vals.push(Some(LTy::new(Ty::Table(schema.clone()), cur_pc)));
                }
                Expr::Prim { op, args } => {
                    tasks.push(InferTask::Finish(InferBuild::Prim(
                        op,
                        args.len(),
                        cur_pc.clone(),
                    )));
                    for e in args.iter().rev() {
                        tasks.push(InferTask::Expr {
                            env: env.clone(),
                            jenv: jenv.clone(),
                            cur_pc: cur_pc.clone(),
                            skip_labels: Arc::clone(&skip_labels),
                            expr: e,
                        });
                    }
                }
                Expr::Rel(plan) => {
                    tasks.push(InferTask::Plan {
                        env,
                        cur_pc,
                        skip_labels,
                        plan,
                    });
                }
                Expr::Host { op, args } => {
                    tasks.push(InferTask::Finish(InferBuild::Host(
                        op,
                        args.len(),
                        cur_pc.clone(),
                    )));
                    for e in args.iter().rev() {
                        tasks.push(InferTask::Expr {
                            env: env.clone(),
                            jenv: jenv.clone(),
                            cur_pc: cur_pc.clone(),
                            skip_labels: Arc::clone(&skip_labels),
                            expr: e,
                        });
                    }
                }
                Expr::Stop { .. } | Expr::Fail(_) => vals.push(Some(LTy::new(Ty::Unit, cur_pc))),
            },
            InferTask::JoinAfterRhs {
                env,
                jenv,
                cur_pc,
                skip_labels,
                body,
            } => {
                let Some(rhs_opt) = vals.pop() else {
                    unreachable!("stack balanced");
                };
                if rhs_opt.is_some() {
                    vals.push(rhs_opt);
                } else {
                    tasks.push(InferTask::Expr {
                        env,
                        jenv,
                        cur_pc,
                        skip_labels,
                        expr: body,
                    });
                }
            }
            InferTask::Plan {
                env,
                cur_pc,
                skip_labels,
                plan,
            } => match plan {
                Plan::SourceExpr(e) => {
                    tasks.push(InferTask::Finish(InferBuild::PlanSourceExpr(
                        cur_pc.clone(),
                    )));
                    tasks.push(InferTask::Expr {
                        env,
                        jenv: ArcJoinEnv::empty(),
                        cur_pc,
                        skip_labels,
                        expr: e,
                    });
                }
                Plan::SourceDB { cap, schema, .. } => {
                    tasks.push(InferTask::Finish(InferBuild::PlanSourceDB(
                        schema,
                        cur_pc.clone(),
                    )));
                    tasks.push(InferTask::Expr {
                        env,
                        jenv: ArcJoinEnv::empty(),
                        cur_pc,
                        skip_labels,
                        expr: cap,
                    });
                }
                Plan::Join {
                    kind,
                    left,
                    right,
                    on,
                    suffixes,
                } => {
                    tasks.push(InferTask::Finish(InferBuild::PlanJoin {
                        kind: *kind,
                        on,
                        suffixes,
                        cur_pc: cur_pc.clone(),
                    }));
                    tasks.push(InferTask::Plan {
                        env: env.clone(),
                        cur_pc: cur_pc.clone(),
                        skip_labels: Arc::clone(&skip_labels),
                        plan: right,
                    });
                    tasks.push(InferTask::Plan {
                        env,
                        cur_pc,
                        skip_labels,
                        plan: left,
                    });
                }
                Plan::Union { left, right } => {
                    tasks.push(InferTask::Finish(InferBuild::PlanUnion(cur_pc.clone())));
                    tasks.push(InferTask::Plan {
                        env: env.clone(),
                        cur_pc: cur_pc.clone(),
                        skip_labels: Arc::clone(&skip_labels),
                        plan: right,
                    });
                    tasks.push(InferTask::Plan {
                        env,
                        cur_pc,
                        skip_labels,
                        plan: left,
                    });
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
                | Plan::Redact { input, .. }
                | Plan::Pseudonymize { input, .. } => {
                    tasks.push(InferTask::Finish(InferBuild::PlanUnary(
                        plan,
                        env.clone(),
                        cur_pc.clone(),
                    )));
                    tasks.push(InferTask::Plan {
                        env,
                        cur_pc,
                        skip_labels,
                        plan: input,
                    });
                }
            },
            InferTask::Finish(build) => match build {
                InferBuild::If(br_pc) => {
                    let (Some(e_opt), Some(t_opt)) = (vals.pop(), vals.pop()) else {
                        unreachable!("stack balanced");
                    };
                    let res = match (t_opt, e_opt) {
                        (Some(l1), Some(l2)) => {
                            Some(LTy::new(l1.ty, l1.tags.union(&l2.tags).union(&br_pc)))
                        }
                        (Some(l1), None) => Some(l1.add_tags(&br_pc)),
                        (None, Some(l2)) => Some(l2.add_tags(&br_pc)),
                        (None, None) => None,
                    };
                    vals.push(res);
                }
                InferBuild::CaseArms(n, arm_pc) => {
                    let arm_opts = vals.split_off(vals.len() - n);
                    let mut acc: Option<LTy> = None;
                    for cur in arm_opts.into_iter().rev() {
                        acc = match (cur, acc) {
                            (Some(l1), Some(l2)) => {
                                Some(LTy::new(l1.ty, l1.tags.union(&l2.tags).union(&arm_pc)))
                            }
                            (Some(l1), None) => Some(l1.add_tags(&arm_pc)),
                            (None, Some(l2)) => Some(l2.add_tags(&arm_pc)),
                            (None, None) => None,
                        };
                    }
                    vals.push(acc);
                }
                InferBuild::App(cur_pc) => {
                    let Some(fn_opt) = vals.pop() else {
                        unreachable!("stack balanced");
                    };
                    let res = match fn_opt {
                        Some(LTy {
                            ty: Ty::Fn { ref ret, .. },
                            tags: f_ts,
                        }) => Some(ret.add_tags(&cur_pc.union(&f_ts))),
                        _ => None,
                    };
                    vals.push(res);
                }
                InferBuild::Tuple(n, cur_pc) => {
                    let opts = vals.split_off(vals.len() - n);
                    let res = opts
                        .into_iter()
                        .collect::<Option<Vec<LTy>>>()
                        .map(|ls| LTy::new(Ty::Tuple(ls), cur_pc));
                    vals.push(res);
                }
                InferBuild::Proj(idx, cur_pc) => {
                    let Some(tup_opt) = vals.pop() else {
                        unreachable!("stack balanced");
                    };
                    let res = match tup_opt {
                        Some(LTy {
                            ty: Ty::Tuple(ref ls),
                            tags: t_ts,
                        }) => idx
                            .to_usize()
                            .and_then(|i| ls.get(i))
                            .map(|e| e.add_tags(&t_ts.union(&cur_pc))),
                        _ => None,
                    };
                    vals.push(res);
                }
                InferBuild::Prim(op, n, cur_pc) => {
                    let opts = vals.split_off(vals.len() - n);
                    let res = opts
                        .into_iter()
                        .collect::<Option<Vec<LTy>>>()
                        .and_then(|ltys| check_prim_op(prog, &cur_pc, op, &ltys).ok());
                    vals.push(res);
                }
                InferBuild::Host(op, n, cur_pc) => {
                    let opts = vals.split_off(vals.len() - n);
                    let res = opts
                        .into_iter()
                        .collect::<Option<Vec<LTy>>>()
                        .and_then(|ltys| check_host_op(prog, &cur_pc, true, op, &ltys).ok());
                    vals.push(res);
                }
                InferBuild::PlanSourceExpr(cur_pc) => {
                    let Some(e_opt) = vals.pop() else {
                        unreachable!("stack balanced");
                    };
                    let res = e_opt.and_then(|lty| {
                        let extra = lty.tags.union(&cur_pc);
                        let tt = lty.ty.into_table()?;
                        Some(
                            PlanTy::Table(TableTy {
                                row_tags: tt.row_tags.union(&extra),
                                order_tags: tt.order_tags.union(&extra),
                                ..tt
                            })
                            .to_lty(&cur_pc),
                        )
                    });
                    vals.push(res);
                }
                InferBuild::PlanSourceDB(schema, cur_pc) => {
                    let Some(cap_opt) = vals.pop() else {
                        unreachable!("stack balanced");
                    };
                    let extra = match cap_opt {
                        Some(l) => l.tags.union(&cur_pc),
                        None => cur_pc.clone(),
                    };
                    vals.push(Some(
                        PlanTy::Table(TableTy {
                            row_tags: schema.row_tags.union(&extra),
                            order_tags: schema.order_tags.union(&extra),
                            ..schema.clone()
                        })
                        .to_lty(&cur_pc),
                    ));
                }
                InferBuild::PlanJoin {
                    kind,
                    on,
                    suffixes,
                    cur_pc,
                } => {
                    let (Some(r_opt), Some(l_opt)) = (vals.pop(), vals.pop()) else {
                        unreachable!("stack balanced");
                    };
                    let res = (|| {
                        let l_tt = l_opt?.ty.into_table()?;
                        let r_tt = r_opt?.ty.into_table()?;
                        let key_pairs = resolve_join_pairs(&l_tt, &r_tt, on).ok()?;
                        let joined_cols =
                            build_joined_cols(kind, &l_tt.cols, &r_tt.cols, on, suffixes).ok()?;
                        let on_tags = TagSet::union_owned(
                            key_pairs.iter().map(|(lc, rc)| lc.tags.union(&rc.tags)),
                        );
                        let new_order_tags = match kind {
                            JoinKind::Semi | JoinKind::Anti => l_tt.order_tags,
                            _ => l_tt.order_tags.union(&r_tt.order_tags),
                        };
                        Some(
                            PlanTy::Table(TableTy {
                                cols: joined_cols,
                                row_tags: l_tt.row_tags.union(&r_tt.row_tags).union(&on_tags),
                                order_tags: new_order_tags,
                                ..TableTy::default()
                            })
                            .to_lty(&cur_pc),
                        )
                    })();
                    vals.push(res);
                }
                InferBuild::PlanUnion(cur_pc) => {
                    let (Some(r_opt), Some(l_opt)) = (vals.pop(), vals.pop()) else {
                        unreachable!("stack balanced");
                    };
                    let res = (|| {
                        let l_tt = l_opt?.ty.into_table()?;
                        let r_tt = r_opt?.ty.into_table()?;
                        let out_cols = merge_union_cols(&l_tt.cols, &r_tt.cols)?;
                        Some(
                            PlanTy::Table(TableTy {
                                cols: out_cols,
                                row_tags: l_tt.row_tags.union(&r_tt.row_tags),
                                order_tags: l_tt.order_tags.union(&r_tt.order_tags),
                                ..TableTy::default()
                            })
                            .to_lty(&cur_pc),
                        )
                    })();
                    vals.push(res);
                }
                InferBuild::PlanUnary(plan, env, cur_pc) => {
                    let Some(in_opt) = vals.pop() else {
                        unreachable!("stack balanced");
                    };
                    let res = in_opt
                        .and_then(|l| l.ty.into_table())
                        .and_then(|tt| infer_quick_plan_unary_step(prog, &env, &cur_pc, plan, tt));
                    vals.push(res);
                }
            },
        }
    }
    vals.pop().flatten()
}

fn infer_quick_plan_unary_step(
    prog: &Program,
    env: &ArcTyEnv,
    cur_pc: &TagSet,
    plan: &Plan,
    tt: TableTy,
) -> Option<LTy> {
    match plan {
        Plan::Select { cols, .. } => {
            let out_cols = cols
                .iter()
                .filter_map(|n| {
                    tt.find_col(n).map(|c| ColSpec {
                        agg_kind: AggKind::Raw,
                        ..c.clone()
                    })
                })
                .collect();
            Some(
                PlanTy::Table(TableTy {
                    cols: out_cols,
                    row_tags: tt.row_tags,
                    order_tags: tt.order_tags,
                    ..TableTy::default()
                })
                .to_lty(cur_pc),
            )
        }
        Plan::Drop { cols, .. } => {
            let out_cols = tt
                .cols
                .into_iter()
                .filter(|c| !cols.contains(&c.name))
                .map(|c| ColSpec {
                    agg_kind: AggKind::Raw,
                    ..c
                })
                .collect();
            Some(
                PlanTy::Table(TableTy {
                    cols: out_cols,
                    row_tags: tt.row_tags,
                    order_tags: tt.order_tags,
                    ..TableTy::default()
                })
                .to_lty(cur_pc),
            )
        }
        Plan::Rename { pairs, .. } => {
            let out_cols = tt
                .cols
                .into_iter()
                .map(|c| match pairs.iter().find(|(_, old_n)| *old_n == c.name) {
                    Some((new_n, _)) => ColSpec {
                        name: new_n.clone(),
                        agg_kind: AggKind::Raw,
                        ..c
                    },
                    None => ColSpec {
                        agg_kind: AggKind::Raw,
                        ..c
                    },
                })
                .collect();
            Some(
                PlanTy::Table(TableTy {
                    cols: out_cols,
                    row_tags: tt.row_tags,
                    order_tags: tt.order_tags,
                    ..TableTy::default()
                })
                .to_lty(cur_pc),
            )
        }
        Plan::Derive { items, .. } => {
            let raw_cols: Vec<ColSpec> = tt
                .cols
                .into_iter()
                .map(|c| ColSpec {
                    agg_kind: AggKind::Raw,
                    ..c
                })
                .collect();
            let out_cols = apply_derive_items_arc(prog, env, raw_cols, items).ok()?;
            Some(
                PlanTy::Table(TableTy {
                    cols: out_cols,
                    row_tags: tt.row_tags,
                    order_tags: tt.order_tags,
                    ..TableTy::default()
                })
                .to_lty(cur_pc),
            )
        }
        Plan::Filter { pred, .. } => {
            let p_tags = check_row_expr_arc(prog, env, &tt.cols, pred)
                .map(|(_, ts)| ts)
                .unwrap_or_default();
            Some(
                PlanTy::Table(TableTy {
                    cols: tt
                        .cols
                        .into_iter()
                        .map(|c| ColSpec {
                            agg_kind: AggKind::Raw,
                            ..c
                        })
                        .collect(),
                    row_tags: tt.row_tags.union(&p_tags),
                    order_tags: tt.order_tags,
                    ..TableTy::default()
                })
                .to_lty(cur_pc),
            )
        }
        Plan::Distinct { cols, .. } => {
            let key_names: Vec<Ident> = if cols.is_empty() {
                tt.col_names()
            } else {
                cols.clone()
            };
            let key_tags = TagSet::union_list(
                key_names
                    .iter()
                    .filter_map(|k| tt.find_col(k).map(|c| &c.tags)),
            );
            let ord_dep = if key_names.len() == tt.cols.len() {
                TagSet::empty()
            } else {
                tt.order_tags.clone()
            };
            Some(
                PlanTy::Table(TableTy {
                    cols: tt
                        .cols
                        .into_iter()
                        .map(|c| ColSpec {
                            agg_kind: AggKind::Raw,
                            ..c
                        })
                        .collect(),
                    row_tags: tt.row_tags.union(&key_tags).union(&ord_dep),
                    order_tags: tt.order_tags,
                    ..TableTy::default()
                })
                .to_lty(cur_pc),
            )
        }
        Plan::Sort { keys, .. } => {
            let sort_key_tags = TagSet::union_list(
                keys.iter()
                    .filter_map(|(k, _)| tt.find_col(k).map(|c| &c.tags)),
            );
            Some(
                PlanTy::Table(TableTy {
                    cols: tt
                        .cols
                        .into_iter()
                        .map(|c| ColSpec {
                            agg_kind: AggKind::Raw,
                            ..c
                        })
                        .collect(),
                    row_tags: tt.row_tags,
                    order_tags: tt.order_tags.union(&sort_key_tags),
                    ..TableTy::default()
                })
                .to_lty(cur_pc),
            )
        }
        Plan::Limit { .. } => {
            let row_tags = tt.row_tags.union(&tt.order_tags);
            Some(
                PlanTy::Table(TableTy {
                    cols: tt
                        .cols
                        .into_iter()
                        .map(|c| ColSpec {
                            agg_kind: AggKind::Raw,
                            ..c
                        })
                        .collect(),
                    row_tags,
                    order_tags: tt.order_tags,
                    ..TableTy::default()
                })
                .to_lty(cur_pc),
            )
        }
        Plan::GroupBy { keys, .. } => {
            let key_tags =
                TagSet::union_list(keys.iter().filter_map(|k| tt.find_col(k).map(|c| &c.tags)));
            let out_cols = tt
                .cols
                .into_iter()
                .map(|c| {
                    let agg_kind = if keys.contains(&c.name) {
                        AggKind::GroupKey
                    } else {
                        AggKind::Raw
                    };
                    ColSpec { agg_kind, ..c }
                })
                .collect();
            Some(
                PlanTy::Table(TableTy {
                    cols: out_cols,
                    row_tags: tt.row_tags.union(&key_tags),
                    order_tags: tt.order_tags,
                    grouped_by: Some(keys.clone()),
                    summarized: false,
                    distinct_by: None,
                })
                .to_lty(cur_pc),
            )
        }
        Plan::Summarize {
            aggs, distinct_key, ..
        } => {
            let group_keys = tt.grouped_by.clone().unwrap_or_default();
            let dk_tags = distinct_key
                .as_deref()
                .and_then(|dk| tt.find_col(dk).map(|c| c.tags.clone()))
                .unwrap_or_default();
            let key_cols: Vec<ColSpec> = tt
                .cols
                .iter()
                .filter(|c| group_keys.contains(&c.name))
                .map(|c| ColSpec {
                    agg_kind: AggKind::GroupKey,
                    ..c.clone()
                })
                .collect();
            let agg_cols = check_agg_item_list_arc(prog, env, &tt, aggs).ok()?;
            let mut cols = key_cols;
            cols.extend(agg_cols);
            Some(
                PlanTy::Table(TableTy {
                    cols,
                    row_tags: tt.row_tags.union(&dk_tags),
                    order_tags: TagSet::empty(),
                    grouped_by: Some(group_keys),
                    summarized: true,
                    distinct_by: distinct_key.clone(),
                })
                .to_lty(cur_pc),
            )
        }
        Plan::SuppressSmallGroups { .. } => {
            let raw_key_tags = TagSet::union_list(
                tt.cols
                    .iter()
                    .filter(|c| c.agg_kind == AggKind::GroupKey && !c.bucketed)
                    .map(|c| &c.tags),
            );
            let out_cols = tt
                .cols
                .into_iter()
                .map(|c| match c.agg_kind {
                    AggKind::GroupKey => {
                        if c.bucketed {
                            ColSpec {
                                tags: cur_pc.clone(),
                                agg_kind: AggKind::Raw,
                                ..c
                            }
                        } else {
                            ColSpec {
                                agg_kind: AggKind::Raw,
                                ..c
                            }
                        }
                    }
                    AggKind::Blending => ColSpec {
                        tags: cur_pc.clone(),
                        agg_kind: AggKind::Raw,
                        ..c
                    },
                    AggKind::NonBlending | AggKind::Raw => ColSpec {
                        agg_kind: AggKind::Raw,
                        ..c
                    },
                })
                .collect();
            Some(
                PlanTy::Table(TableTy {
                    cols: out_cols,
                    row_tags: raw_key_tags.union(cur_pc),
                    order_tags: tt.order_tags,
                    ..TableTy::default()
                })
                .to_lty(cur_pc),
            )
        }
        Plan::Window { items, .. } => {
            let raw_cols: Vec<ColSpec> = tt
                .cols
                .into_iter()
                .map(|c| ColSpec {
                    agg_kind: AggKind::Raw,
                    ..c
                })
                .collect();
            let out_cols = apply_window_items(&tt.order_tags, raw_cols, items).ok()?;
            Some(
                PlanTy::Table(TableTy {
                    cols: out_cols,
                    row_tags: tt.row_tags,
                    order_tags: tt.order_tags,
                    ..TableTy::default()
                })
                .to_lty(cur_pc),
            )
        }
        Plan::FillGaps { col, over, .. } => {
            let t_col = tt.find_col(col)?;
            let over_tags =
                TagSet::union_list(over.iter().filter_map(|k| tt.find_col(k).map(|c| &c.tags)));
            let new_row_tags = tt.row_tags.union(&t_col.tags).union(&over_tags);
            let out_cols = tt
                .cols
                .iter()
                .map(|c| {
                    if c.name == *col || over.contains(&c.name) {
                        ColSpec {
                            agg_kind: AggKind::Raw,
                            bucketed: false,
                            ..c.clone()
                        }
                    } else {
                        ColSpec {
                            tags: c.tags.union(&new_row_tags).union(&tt.order_tags),
                            agg_kind: AggKind::Raw,
                            bucketed: false,
                            ..c.clone()
                        }
                    }
                })
                .collect();
            Some(
                PlanTy::Table(TableTy {
                    cols: out_cols,
                    row_tags: new_row_tags,
                    order_tags: TagSet::empty(),
                    ..TableTy::default()
                })
                .to_lty(cur_pc),
            )
        }
        Plan::PivotWider {
            names_from,
            values_from,
            static_cols,
            ..
        } => {
            let n_col = tt.find_col(names_from)?;
            let v_col = tt.find_col(values_from)?;
            let id_cols: Vec<ColSpec> = tt
                .cols
                .iter()
                .filter(|c| c.name != *names_from && c.name != *values_from)
                .map(|c| ColSpec {
                    agg_kind: AggKind::Raw,
                    ..c.clone()
                })
                .collect();
            let id_tags = TagSet::union_list(id_cols.iter().map(|c| &c.tags));
            let new_row_tags = tt.row_tags.union(&n_col.tags).union(&id_tags);
            let cell_tags = n_col
                .tags
                .union(&v_col.tags)
                .union(&new_row_tags)
                .union(&tt.order_tags);
            let mut cols = id_cols;
            cols.extend(static_cols.iter().map(|sc| ColSpec {
                name: sc.clone(),
                ty: v_col.ty.clone(),
                tags: cell_tags.clone(),
                bucketed: false,
                agg_kind: AggKind::Raw,
            }));
            Some(
                PlanTy::Table(TableTy {
                    cols,
                    row_tags: new_row_tags,
                    order_tags: TagSet::empty(),
                    ..TableTy::default()
                })
                .to_lty(cur_pc),
            )
        }
        Plan::Crosstab {
            rows_col,
            cols_col,
            values_col,
            ..
        } => {
            let r_col = tt.find_col(rows_col)?;
            let c_col = tt.find_col(cols_col)?;
            let v_col = tt.find_col(values_col)?;
            let dt_tags = tt
                .row_tags
                .union(&tt.order_tags)
                .union(&r_col.tags)
                .union(&c_col.tags)
                .union(&v_col.tags)
                .union(cur_pc);
            Some(PlanTy::Dynamic(dt_tags).to_lty(cur_pc))
        }
        Plan::Redact { col, .. } => {
            let out_cols = tt
                .cols
                .into_iter()
                .map(|c| {
                    if c.name == *col {
                        ColSpec {
                            ty: ScalarTy::Text,
                            tags: cur_pc.clone(),
                            bucketed: false,
                            agg_kind: AggKind::Raw,
                            ..c
                        }
                    } else {
                        ColSpec {
                            agg_kind: AggKind::Raw,
                            ..c
                        }
                    }
                })
                .collect();
            Some(
                PlanTy::Table(TableTy {
                    cols: out_cols,
                    row_tags: tt.row_tags,
                    order_tags: tt.order_tags,
                    ..TableTy::default()
                })
                .to_lty(cur_pc),
            )
        }
        Plan::Pseudonymize { col, .. } => {
            let out_cols = tt
                .cols
                .into_iter()
                .map(|c| {
                    if c.name == *col {
                        ColSpec {
                            ty: ScalarTy::Text,
                            tags: c.tags.remove("pii").union(cur_pc),
                            bucketed: false,
                            agg_kind: AggKind::Raw,
                            ..c
                        }
                    } else {
                        ColSpec {
                            agg_kind: AggKind::Raw,
                            ..c
                        }
                    }
                })
                .collect();
            Some(
                PlanTy::Table(TableTy {
                    cols: out_cols,
                    row_tags: tt.row_tags,
                    order_tags: tt.order_tags,
                    ..TableTy::default()
                })
                .to_lty(cur_pc),
            )
        }
        _ => unreachable!("non-unary plans handled by infer_branch_lty_arc"),
    }
}

fn infer_join_ret_lty_arc(
    prog: &Program,
    env: &ArcTyEnv,
    jenv: &ArcJoinEnv,
    cur_pc: &TagSet,
    skip_label: &Ident,
    rhs: &Expr,
    body: &Expr,
) -> Option<LTy> {
    let skip = Arc::new(vec![skip_label.clone()]);
    infer_branch_lty_arc(prog, env, jenv, cur_pc, Arc::clone(&skip), rhs)
        .or_else(|| infer_branch_lty_arc(prog, env, jenv, cur_pc, skip, body))
}

// ---------------------------------------------------------------------------
// Mutual Static Checker for `Expr` and `Plan` (100% Iterative Heap Stack)
// ---------------------------------------------------------------------------

enum CheckedIr {
    LTy(LTy),
    PlanTy(PlanTy),
}

impl CheckedIr {
    fn into_lty(self) -> LTy {
        match self {
            Self::LTy(l) => l,
            Self::PlanTy(_) => unreachable!("expected CheckedIr::LTy"),
        }
    }

    fn into_plan_ty(self) -> PlanTy {
        match self {
            Self::PlanTy(p) => p,
            Self::LTy(_) => unreachable!("expected CheckedIr::PlanTy"),
        }
    }
}

enum CheckTask<'a> {
    Expr {
        env: ArcTyEnv,
        jenv: ArcJoinEnv,
        pc: TagSet,
        expr: &'a Expr,
        verified_nfj: bool,
    },
    Plan {
        env: ArcTyEnv,
        pc: TagSet,
        plan: &'a Plan,
        verified_nfj: bool,
    },
    LetAfterBound {
        name: &'a Ident,
        decl_lty: &'a LTy,
        env: ArcTyEnv,
        jenv: ArcJoinEnv,
        pc: TagSet,
        body: &'a Expr,
        verified_nfj: bool,
    },
    IfAfterCond {
        env: ArcTyEnv,
        jenv: ArcJoinEnv,
        pc: TagSet,
        then_br: &'a Expr,
        else_br: &'a Expr,
        verified_nfj: bool,
    },
    FinishIf {
        br_pc: TagSet,
    },
    CaseAfterScrut {
        env: ArcTyEnv,
        jenv: ArcJoinEnv,
        pc: TagSet,
        arms: &'a [CaseArm],
        verified_nfj: bool,
    },
    CaseArmStep {
        env: ArcTyEnv,
        jenv: ArcJoinEnv,
        arm_pc: TagSet,
        specs: Arc<Vec<(Ident, Vec<LTy>)>>,
        arm: &'a CaseArm,
        verified_nfj: bool,
    },
    FinishCase {
        n_arms: usize,
        arm_pc: TagSet,
    },
    FinishLam {
        params: &'a [(Ident, LTy)],
        fn_pc: &'a TagSet,
        ret_lty: &'a LTy,
        outer_pc: TagSet,
    },
    FinishApp {
        n_args: usize,
        pc: TagSet,
    },
    FinishCall {
        fn_name: &'a Ident,
        n_args: usize,
        pc: TagSet,
    },
    JoinAfterPass1 {
        label: &'a Ident,
        params: &'a [(Ident, LTy)],
        env: ArcTyEnv,
        jenv: ArcJoinEnv,
        pc: TagSet,
        join_pc: TagSet,
        ret_lty: LTy,
        rhs: &'a Expr,
        body: &'a Expr,
        verified_nfj: bool,
    },
    JoinAfterPass2 {
        label: &'a Ident,
        final_ret: LTy,
    },
    FinishJump {
        label: &'a Ident,
        n_args: usize,
        jenv: ArcJoinEnv,
        pc: TagSet,
    },
    FinishTuple {
        n_elems: usize,
        pc: TagSet,
    },
    FinishProj {
        idx: &'a BigInt,
        pc: TagSet,
    },
    FinishCtor {
        type_name: &'a Ident,
        ctor_name: &'a Ident,
        n_args: usize,
        pc: TagSet,
    },
    FinishPrim {
        op: &'a PrimOp,
        n_args: usize,
        pc: TagSet,
    },
    FinishRel {
        pc: TagSet,
    },
    FinishHost {
        op: &'a HostOp,
        n_args: usize,
        pc: TagSet,
    },
    FinishStopDetail {
        pc: TagSet,
    },
    FinishFail {
        pc: TagSet,
    },
    FinishSourceExpr {
        pc: TagSet,
    },
    FinishSourceDB {
        schema: &'a TableTy,
        pc: TagSet,
    },
    FinishPlanJoin {
        kind: JoinKind,
        on: &'a JoinOn,
        suffixes: &'a Option<(String, String)>,
    },
    FinishPlanUnion,
    FinishPlanPseudo {
        col: &'a Ident,
        pc: TagSet,
    },
    FinishPlanUnary {
        stage: &'a Plan,
        env: ArcTyEnv,
        pc: TagSet,
    },
}

fn check_ir_iter(
    prog: &Program,
    in_spec: bool,
    init: CheckTask<'_>,
) -> Result<CheckedIr, CheckError> {
    let mut tasks = vec![init];
    let mut vals: Vec<CheckedIr> = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            CheckTask::Expr {
                env,
                jenv,
                pc,
                expr,
                verified_nfj,
            } => match expr {
                Expr::Lit(v) => vals.push(CheckedIr::LTy(check_literal(prog, &pc, v)?)),
                Expr::Var(name) => match env.lookup(name) {
                    Some(lty) => vals.push(CheckedIr::LTy(lty.add_tags(&pc))),
                    None => return err(format!("unbound variable '{name}'")),
                },
                Expr::ConstRef(name) => match prog.find_const(name) {
                    Some(c_decl) => vals.push(CheckedIr::LTy(c_decl.lty.add_tags(&pc))),
                    None => return err(format!("unknown constant '{name}'")),
                },
                Expr::LetE {
                    name,
                    lty: decl_lty,
                    bound,
                    body,
                } => {
                    if !valid_lty(prog, decl_lty) {
                        return err(format!("invalid type annotation on let '{name}'"));
                    }
                    if !verified_nfj && !no_free_jumps(&[], bound) {
                        return err(format!(
                            "non-tail jump inside bound expression of let '{name}'"
                        ));
                    }
                    tasks.push(CheckTask::LetAfterBound {
                        name,
                        decl_lty,
                        env: env.clone(),
                        jenv,
                        pc: pc.clone(),
                        body,
                        verified_nfj,
                    });
                    tasks.push(CheckTask::Expr {
                        env,
                        jenv: ArcJoinEnv::empty(),
                        pc,
                        expr: bound,
                        verified_nfj: true,
                    });
                }
                Expr::IfE {
                    cond,
                    then_br,
                    else_br,
                } => {
                    if !verified_nfj && !no_free_jumps(&[], cond) {
                        return err("non-tail jump inside if condition");
                    }
                    tasks.push(CheckTask::IfAfterCond {
                        env: env.clone(),
                        jenv,
                        pc: pc.clone(),
                        then_br,
                        else_br,
                        verified_nfj,
                    });
                    tasks.push(CheckTask::Expr {
                        env,
                        jenv: ArcJoinEnv::empty(),
                        pc,
                        expr: cond,
                        verified_nfj: true,
                    });
                }
                Expr::CaseE { scrut, arms } => {
                    if !verified_nfj && !no_free_jumps(&[], scrut) {
                        return err("non-tail jump inside case scrutinee");
                    }
                    tasks.push(CheckTask::CaseAfterScrut {
                        env: env.clone(),
                        jenv,
                        pc: pc.clone(),
                        arms,
                        verified_nfj,
                    });
                    tasks.push(CheckTask::Expr {
                        env,
                        jenv: ArcJoinEnv::empty(),
                        pc,
                        expr: scrut,
                        verified_nfj: true,
                    });
                }
                Expr::Lam {
                    params,
                    pc: fn_pc,
                    ret: ret_lty,
                    body,
                } => {
                    let p_names: Vec<Ident> = params.iter().map(|(n, _)| n.clone()).collect();
                    if !distinct_idents(&p_names)
                        || !params.iter().all(|(_, l)| valid_lty(prog, l))
                        || !valid_tag_set(prog, fn_pc)
                        || !valid_lty(prog, ret_lty)
                    {
                        return err("invalid lambda parameter or return types");
                    }
                    if !verified_nfj && !no_free_jumps(&[], body) {
                        return err("lambda cannot jump to enclosing outer join point");
                    }
                    if !fn_pc.is_subset(&ret_lty.effective_tags()) {
                        return err("lambda caller pc bound must be reflected in return type tags");
                    }
                    let body_env = env.extend_slice(params);
                    tasks.push(CheckTask::FinishLam {
                        params,
                        fn_pc,
                        ret_lty,
                        outer_pc: pc,
                    });
                    tasks.push(CheckTask::Expr {
                        env: body_env,
                        jenv: ArcJoinEnv::empty(),
                        pc: fn_pc.clone(),
                        expr: body,
                        verified_nfj: true,
                    });
                }
                Expr::App { fn_expr, args } => {
                    if !verified_nfj && (!no_free_jumps(&[], fn_expr) || !no_free_jumps_list(args))
                    {
                        return err("non-tail jump in function application");
                    }
                    tasks.push(CheckTask::FinishApp {
                        n_args: args.len(),
                        pc: pc.clone(),
                    });
                    for arg in args.iter().rev() {
                        tasks.push(CheckTask::Expr {
                            env: env.clone(),
                            jenv: ArcJoinEnv::empty(),
                            pc: pc.clone(),
                            expr: arg,
                            verified_nfj: true,
                        });
                    }
                    tasks.push(CheckTask::Expr {
                        env,
                        jenv: ArcJoinEnv::empty(),
                        pc,
                        expr: fn_expr,
                        verified_nfj: true,
                    });
                }
                Expr::Call { fn_name, args } => {
                    if !verified_nfj && !no_free_jumps_list(args) {
                        return err("non-tail jump in call arguments");
                    }
                    tasks.push(CheckTask::FinishCall {
                        fn_name,
                        n_args: args.len(),
                        pc: pc.clone(),
                    });
                    for arg in args.iter().rev() {
                        tasks.push(CheckTask::Expr {
                            env: env.clone(),
                            jenv: ArcJoinEnv::empty(),
                            pc: pc.clone(),
                            expr: arg,
                            verified_nfj: true,
                        });
                    }
                }
                Expr::Join {
                    label,
                    params,
                    rhs,
                    body,
                } => {
                    let p_names: Vec<Ident> = params.iter().map(|(n, _)| n.clone()).collect();
                    if !distinct_idents(&p_names) || !params.iter().all(|(_, l)| valid_lty(prog, l))
                    {
                        return err(format!("invalid parameters on join point '{label}'"));
                    }
                    let guess1 = pc.union(&infer_jump_pc_arc(prog, label, &env, &pc, body));
                    let rhs_env = env.extend_slice(params);
                    let join_pc =
                        guess1.union(&infer_jump_pc_arc(prog, label, &rhs_env, &guess1, rhs));
                    let Some(cand_ret_lty) =
                        infer_join_ret_lty_arc(prog, &rhs_env, &jenv, &join_pc, label, rhs, body)
                    else {
                        return err(format!(
                            "could not determine return type of join point '{label}'"
                        ));
                    };
                    let ret_lty = cand_ret_lty.add_tags(&join_pc);
                    if !valid_lty(prog, &ret_lty) {
                        return err(format!("invalid inferred return type for join '{label}'"));
                    }
                    let sig = JoinSig {
                        params: params.clone(),
                        join_pc: join_pc.clone(),
                        ret_lty: ret_lty.clone(),
                    };
                    let jenv_next = ArcJoinEnv::cons(label.clone(), sig, jenv.clone());
                    tasks.push(CheckTask::JoinAfterPass1 {
                        label,
                        params,
                        env: env.clone(),
                        jenv,
                        pc: pc.clone(),
                        join_pc: join_pc.clone(),
                        ret_lty,
                        rhs,
                        body,
                        verified_nfj,
                    });
                    tasks.push(CheckTask::Expr {
                        env,
                        jenv: jenv_next.clone(),
                        pc,
                        expr: body,
                        verified_nfj,
                    });
                    tasks.push(CheckTask::Expr {
                        env: rhs_env,
                        jenv: jenv_next,
                        pc: join_pc,
                        expr: rhs,
                        verified_nfj,
                    });
                }
                Expr::Jump { label, args } => {
                    if !verified_nfj && !no_free_jumps_list(args) {
                        return err("non-tail jump inside jump arguments");
                    }
                    tasks.push(CheckTask::FinishJump {
                        label,
                        n_args: args.len(),
                        jenv,
                        pc: pc.clone(),
                    });
                    for arg in args.iter().rev() {
                        tasks.push(CheckTask::Expr {
                            env: env.clone(),
                            jenv: ArcJoinEnv::empty(),
                            pc: pc.clone(),
                            expr: arg,
                            verified_nfj: true,
                        });
                    }
                }
                Expr::Tuple(elems) => {
                    if !verified_nfj && !no_free_jumps_list(elems) {
                        return err("non-tail jump inside tuple");
                    }
                    tasks.push(CheckTask::FinishTuple {
                        n_elems: elems.len(),
                        pc: pc.clone(),
                    });
                    for elem in elems.iter().rev() {
                        tasks.push(CheckTask::Expr {
                            env: env.clone(),
                            jenv: ArcJoinEnv::empty(),
                            pc: pc.clone(),
                            expr: elem,
                            verified_nfj: true,
                        });
                    }
                }
                Expr::Proj { tup, idx } => {
                    if !verified_nfj && !no_free_jumps(&[], tup) {
                        return err("non-tail jump inside tuple projection");
                    }
                    tasks.push(CheckTask::FinishProj {
                        idx,
                        pc: pc.clone(),
                    });
                    tasks.push(CheckTask::Expr {
                        env,
                        jenv: ArcJoinEnv::empty(),
                        pc,
                        expr: tup,
                        verified_nfj: true,
                    });
                }
                Expr::Ctor {
                    type_name,
                    ctor_name,
                    args,
                } => {
                    if !verified_nfj && !no_free_jumps_list(args) {
                        return err("non-tail jump inside constructor arguments");
                    }
                    tasks.push(CheckTask::FinishCtor {
                        type_name,
                        ctor_name,
                        n_args: args.len(),
                        pc: pc.clone(),
                    });
                    for arg in args.iter().rev() {
                        tasks.push(CheckTask::Expr {
                            env: env.clone(),
                            jenv: ArcJoinEnv::empty(),
                            pc: pc.clone(),
                            expr: arg,
                            verified_nfj: true,
                        });
                    }
                }
                Expr::TableLit { schema, rows } => {
                    if !valid_table_ty(prog, schema)
                        || schema.summarized
                        || schema.grouped_by.is_some()
                        || schema.distinct_by.is_some()
                    {
                        return err("invalid TableTy in tableLit");
                    }
                    if !schema
                        .cols
                        .iter()
                        .all(|c| !c.bucketed && c.agg_kind == AggKind::Raw)
                    {
                        return err(
                            "tableLit columns must have bucketed = false and aggKind = raw",
                        );
                    }
                    if !rows.iter().all(|r| check_row_lit(prog, &schema.cols, r)) {
                        return err("tableLit row cells do not match declared TableTy");
                    }
                    let out_schema = TableTy {
                        row_tags: schema.row_tags.union(&pc),
                        order_tags: schema.order_tags.union(&pc),
                        ..schema.clone()
                    };
                    vals.push(CheckedIr::LTy(LTy::new(Ty::Table(out_schema), pc)));
                }
                Expr::Prim { op, args } => {
                    if !verified_nfj && !no_free_jumps_list(args) {
                        return err("non-tail jump inside primitive arguments");
                    }
                    tasks.push(CheckTask::FinishPrim {
                        op,
                        n_args: args.len(),
                        pc: pc.clone(),
                    });
                    for arg in args.iter().rev() {
                        tasks.push(CheckTask::Expr {
                            env: env.clone(),
                            jenv: ArcJoinEnv::empty(),
                            pc: pc.clone(),
                            expr: arg,
                            verified_nfj: true,
                        });
                    }
                }
                Expr::Rel(plan) => {
                    if !verified_nfj && !no_free_jumps_plan(plan) {
                        return err("non-tail jump inside relational plan");
                    }
                    tasks.push(CheckTask::FinishRel { pc: pc.clone() });
                    tasks.push(CheckTask::Plan {
                        env,
                        pc,
                        plan,
                        verified_nfj: true,
                    });
                }
                Expr::Host { op, args } => {
                    if !verified_nfj && !no_free_jumps_list(args) {
                        return err("non-tail jump inside host arguments");
                    }
                    tasks.push(CheckTask::FinishHost {
                        op,
                        n_args: args.len(),
                        pc: pc.clone(),
                    });
                    for arg in args.iter().rev() {
                        tasks.push(CheckTask::Expr {
                            env: env.clone(),
                            jenv: ArcJoinEnv::empty(),
                            pc: pc.clone(),
                            expr: arg,
                            verified_nfj: true,
                        });
                    }
                }
                Expr::Stop { detail, .. } => match detail {
                    None => vals.push(CheckedIr::LTy(LTy::new(Ty::Unit, pc))),
                    Some(d) => {
                        if !verified_nfj && !no_free_jumps(&[], d) {
                            return err("non-tail jump inside stop detail");
                        }
                        tasks.push(CheckTask::FinishStopDetail { pc: pc.clone() });
                        tasks.push(CheckTask::Expr {
                            env,
                            jenv: ArcJoinEnv::empty(),
                            pc,
                            expr: d,
                            verified_nfj: true,
                        });
                    }
                },
                Expr::Fail(msg) => {
                    if !in_spec {
                        return err(
                            "Fail is only permitted inside spec functions (test/example/promise)",
                        );
                    }
                    if !verified_nfj && !no_free_jumps(&[], msg) {
                        return err("non-tail jump inside fail message");
                    }
                    tasks.push(CheckTask::FinishFail { pc: pc.clone() });
                    tasks.push(CheckTask::Expr {
                        env,
                        jenv: ArcJoinEnv::empty(),
                        pc,
                        expr: msg,
                        verified_nfj: true,
                    });
                }
            },
            CheckTask::Plan {
                env,
                pc,
                plan,
                verified_nfj,
            } => match plan {
                Plan::SourceExpr(e) => {
                    tasks.push(CheckTask::FinishSourceExpr { pc: pc.clone() });
                    tasks.push(CheckTask::Expr {
                        env,
                        jenv: ArcJoinEnv::empty(),
                        pc,
                        expr: e,
                        verified_nfj,
                    });
                }
                Plan::SourceDB { cap, schema, .. } => {
                    tasks.push(CheckTask::FinishSourceDB {
                        schema,
                        pc: pc.clone(),
                    });
                    tasks.push(CheckTask::Expr {
                        env,
                        jenv: ArcJoinEnv::empty(),
                        pc,
                        expr: cap,
                        verified_nfj,
                    });
                }
                Plan::Join {
                    kind,
                    left,
                    right,
                    on,
                    suffixes,
                } => {
                    tasks.push(CheckTask::FinishPlanJoin {
                        kind: *kind,
                        on,
                        suffixes,
                    });
                    tasks.push(CheckTask::Plan {
                        env: env.clone(),
                        pc: pc.clone(),
                        plan: right,
                        verified_nfj,
                    });
                    tasks.push(CheckTask::Plan {
                        env,
                        pc,
                        plan: left,
                        verified_nfj,
                    });
                }
                Plan::Union { left, right } => {
                    tasks.push(CheckTask::FinishPlanUnion);
                    tasks.push(CheckTask::Plan {
                        env: env.clone(),
                        pc: pc.clone(),
                        plan: right,
                        verified_nfj,
                    });
                    tasks.push(CheckTask::Plan {
                        env,
                        pc,
                        plan: left,
                        verified_nfj,
                    });
                }
                Plan::Pseudonymize { input, col, secret } => {
                    tasks.push(CheckTask::FinishPlanPseudo {
                        col,
                        pc: pc.clone(),
                    });
                    tasks.push(CheckTask::Expr {
                        env: env.clone(),
                        jenv: ArcJoinEnv::empty(),
                        pc: pc.clone(),
                        expr: secret,
                        verified_nfj,
                    });
                    tasks.push(CheckTask::Plan {
                        env,
                        pc,
                        plan: input,
                        verified_nfj,
                    });
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
                    tasks.push(CheckTask::FinishPlanUnary {
                        stage: plan,
                        env: env.clone(),
                        pc: pc.clone(),
                    });
                    tasks.push(CheckTask::Plan {
                        env,
                        pc,
                        plan: input,
                        verified_nfj,
                    });
                }
            },
            CheckTask::LetAfterBound {
                name,
                decl_lty,
                env,
                jenv,
                pc,
                body,
                verified_nfj,
            } => {
                let Some(b_lty) = vals.pop().map(CheckedIr::into_lty) else {
                    unreachable!("stack balanced");
                };
                if !lty_subtype(&b_lty, decl_lty) {
                    return err(format!("let '{name}' bound type mismatch"));
                }
                let next_env = ArcTyEnv::cons(name.clone(), decl_lty.add_tags(&pc), env);
                tasks.push(CheckTask::Expr {
                    env: next_env,
                    jenv,
                    pc,
                    expr: body,
                    verified_nfj,
                });
            }
            CheckTask::IfAfterCond {
                env,
                jenv,
                pc,
                then_br,
                else_br,
                verified_nfj,
            } => {
                let Some(cond_lty) = vals.pop().map(CheckedIr::into_lty) else {
                    unreachable!("stack balanced");
                };
                if cond_lty.ty != Ty::Bool {
                    return err("if condition must have type Bool");
                }
                let br_pc = pc.union(&cond_lty.tags);
                tasks.push(CheckTask::FinishIf {
                    br_pc: br_pc.clone(),
                });
                tasks.push(CheckTask::Expr {
                    env: env.clone(),
                    jenv: jenv.clone(),
                    pc: br_pc.clone(),
                    expr: else_br,
                    verified_nfj,
                });
                tasks.push(CheckTask::Expr {
                    env,
                    jenv,
                    pc: br_pc,
                    expr: then_br,
                    verified_nfj,
                });
            }
            CheckTask::FinishIf { br_pc } => {
                let (Some(e_lty), Some(t_lty)) = (
                    vals.pop().map(CheckedIr::into_lty),
                    vals.pop().map(CheckedIr::into_lty),
                ) else {
                    unreachable!("stack balanced");
                };
                if t_lty.ty == e_lty.ty {
                    vals.push(CheckedIr::LTy(LTy::new(
                        t_lty.ty,
                        t_lty.tags.union(&e_lty.tags).union(&br_pc),
                    )));
                } else {
                    return err("if branches have mismatched structural types");
                }
            }
            CheckTask::CaseAfterScrut {
                env,
                jenv,
                pc,
                arms,
                verified_nfj,
            } => {
                let Some(scrut_lty) = vals.pop().map(CheckedIr::into_lty) else {
                    unreachable!("stack balanced");
                };
                let scrut_tags = scrut_lty.effective_tags();
                let arm_pc = pc.union(&scrut_tags);
                let specs = Arc::new(expected_case_specs(prog, &scrut_lty.ty, &scrut_tags)?);
                let arm_ctors: Vec<Ident> = arms.iter().map(|a| a.ctor.clone()).collect();
                if !distinct_idents(&arm_ctors) || arms.len() != specs.len() {
                    return err("case arms must be exhaustive and duplicate-free");
                }
                tasks.push(CheckTask::FinishCase {
                    n_arms: arms.len(),
                    arm_pc: arm_pc.clone(),
                });
                for arm in arms.iter().rev() {
                    tasks.push(CheckTask::CaseArmStep {
                        env: env.clone(),
                        jenv: jenv.clone(),
                        arm_pc: arm_pc.clone(),
                        specs: Arc::clone(&specs),
                        arm,
                        verified_nfj,
                    });
                }
            }
            CheckTask::CaseArmStep {
                env,
                jenv,
                arm_pc,
                specs,
                arm,
                verified_nfj,
            } => {
                let Some((_, field_ltys)) = specs.iter().find(|(sn, _)| *sn == arm.ctor) else {
                    return err(format!("unexpected constructor '{}' in Case", arm.ctor));
                };
                if !distinct_idents(&arm.binders) || arm.binders.len() != field_ltys.len() {
                    return err(format!(
                        "case arm '{}' binder count or duplicate mismatch",
                        arm.ctor
                    ));
                }
                let arm_bindings: Vec<(Ident, LTy)> = arm
                    .binders
                    .iter()
                    .cloned()
                    .zip(field_ltys.iter().map(|f| f.add_tags(&arm_pc)))
                    .collect();
                let arm_env = env.extend_slice(&arm_bindings);
                tasks.push(CheckTask::Expr {
                    env: arm_env,
                    jenv,
                    pc: arm_pc,
                    expr: &arm.body,
                    verified_nfj,
                });
            }
            CheckTask::FinishCase { n_arms, arm_pc } => {
                let arm_ltys: Vec<LTy> = vals
                    .split_off(vals.len() - n_arms)
                    .into_iter()
                    .map(CheckedIr::into_lty)
                    .collect();
                let Some((first_lty, rest_ltys)) = arm_ltys.split_first() else {
                    return err("empty case arms");
                };
                if rest_ltys.iter().all(|l| l.ty == first_lty.ty) {
                    let union_arm_tags = TagSet::union_list(arm_ltys.iter().map(|l| &l.tags));
                    vals.push(CheckedIr::LTy(LTy::new(
                        first_lty.ty.clone(),
                        union_arm_tags.union(&arm_pc),
                    )));
                } else {
                    return err("case arms have mismatched return types");
                }
            }
            CheckTask::FinishLam {
                params,
                fn_pc,
                ret_lty,
                outer_pc,
            } => {
                let Some(body_lty) = vals.pop().map(CheckedIr::into_lty) else {
                    unreachable!("stack balanced");
                };
                if lty_subtype(&body_lty, ret_lty) {
                    vals.push(CheckedIr::LTy(LTy::new(
                        Ty::Fn {
                            params: params.iter().map(|(_, l)| l.clone()).collect(),
                            pc: fn_pc.clone(),
                            ret: Box::new(ret_lty.clone()),
                        },
                        outer_pc,
                    )));
                } else {
                    return err("lambda body type/tags do not match declared return LTy");
                }
            }
            CheckTask::FinishApp { n_args, pc } => {
                let arg_ltys: Vec<LTy> = vals
                    .split_off(vals.len() - n_args)
                    .into_iter()
                    .map(CheckedIr::into_lty)
                    .collect();
                let Some(fn_lty) = vals.pop().map(CheckedIr::into_lty) else {
                    unreachable!("stack balanced");
                };
                match &fn_lty.ty {
                    Ty::Fn {
                        params: param_ltys,
                        pc: fn_pc,
                        ret: ret_lty,
                    } => {
                        let call_pc = pc.union(&fn_lty.tags);
                        if !call_pc.is_subset(fn_pc) {
                            return err("caller pc / closure taint exceeds function pc bound");
                        } else if arg_ltys.len() != param_ltys.len() {
                            return err("closure call arity mismatch");
                        } else if !arg_ltys
                            .iter()
                            .zip(param_ltys)
                            .all(|(a, p)| lty_subtype(a, p))
                        {
                            return err("closure call argument type/tag mismatch");
                        }
                        vals.push(CheckedIr::LTy(ret_lty.add_tags(&call_pc)));
                    }
                    _ => return err("application target is not a function"),
                }
            }
            CheckTask::FinishCall {
                fn_name,
                n_args,
                pc,
            } => {
                let arg_ltys: Vec<LTy> = vals
                    .split_off(vals.len() - n_args)
                    .into_iter()
                    .map(CheckedIr::into_lty)
                    .collect();
                match prog.find_fun(fn_name) {
                    Some(f_decl) => {
                        if f_decl.kind.is_spec() && !in_spec {
                            return err(format!(
                                "ordinary function cannot call spec function '{fn_name}'"
                            ));
                        } else if !pc.is_subset(&f_decl.pc) {
                            return err(format!("caller pc exceeds function '{fn_name}' pc bound"));
                        } else if arg_ltys.len() != f_decl.params.len() {
                            return err(format!("call to '{fn_name}' arity mismatch"));
                        } else if !arg_ltys
                            .iter()
                            .zip(&f_decl.params)
                            .all(|(a, (_, p))| lty_subtype(a, p))
                        {
                            return err(format!("call to '{fn_name}' argument type/tag mismatch"));
                        }
                        vals.push(CheckedIr::LTy(f_decl.ret.add_tags(&pc)));
                    }
                    None => return err(format!("unknown function '{fn_name}'")),
                }
            }
            CheckTask::JoinAfterPass1 {
                label,
                params,
                env,
                jenv,
                pc,
                join_pc,
                ret_lty,
                rhs,
                body,
                verified_nfj,
            } => {
                let (Some(body_lty), Some(rhs_lty)) = (
                    vals.pop().map(CheckedIr::into_lty),
                    vals.pop().map(CheckedIr::into_lty),
                ) else {
                    unreachable!("stack balanced");
                };
                if rhs_lty.ty != ret_lty.ty || body_lty.ty != ret_lty.ty {
                    return err(format!("join point '{label}' body and rhs types differ"));
                }
                let final_tags = ret_lty
                    .tags
                    .union(&rhs_lty.tags)
                    .union(&body_lty.tags.union(&pc));
                if final_tags.is_subset(&ret_lty.tags) {
                    vals.push(CheckedIr::LTy(ret_lty));
                } else {
                    let final_ret = LTy::new(ret_lty.ty, final_tags);
                    let sig2 = JoinSig {
                        params: params.to_vec(),
                        join_pc: join_pc.clone(),
                        ret_lty: final_ret.clone(),
                    };
                    let jenv2 = ArcJoinEnv::cons(label.clone(), sig2, jenv);
                    let rhs_env = env.extend_slice(params);
                    tasks.push(CheckTask::JoinAfterPass2 { label, final_ret });
                    tasks.push(CheckTask::Expr {
                        env,
                        jenv: jenv2.clone(),
                        pc,
                        expr: body,
                        verified_nfj,
                    });
                    tasks.push(CheckTask::Expr {
                        env: rhs_env,
                        jenv: jenv2,
                        pc: join_pc,
                        expr: rhs,
                        verified_nfj,
                    });
                }
            }
            CheckTask::JoinAfterPass2 { label, final_ret } => {
                let (Some(body_lty2), Some(rhs_lty2)) = (
                    vals.pop().map(CheckedIr::into_lty),
                    vals.pop().map(CheckedIr::into_lty),
                ) else {
                    unreachable!("stack balanced");
                };
                if lty_subtype(&rhs_lty2, &final_ret) && lty_subtype(&body_lty2, &final_ret) {
                    vals.push(CheckedIr::LTy(final_ret));
                } else {
                    return err(format!("join point '{label}' return label mismatch"));
                }
            }
            CheckTask::FinishJump {
                label,
                n_args,
                jenv,
                pc,
            } => {
                let arg_ltys: Vec<LTy> = vals
                    .split_off(vals.len() - n_args)
                    .into_iter()
                    .map(CheckedIr::into_lty)
                    .collect();
                match jenv.lookup(label) {
                    Some(sig) => {
                        if !pc.is_subset(&sig.join_pc) {
                            return err(format!("jump to '{label}' from pc exceeding joinPc"));
                        } else if !pc.is_subset(&sig.ret_lty.effective_tags()) {
                            return err(format!(
                                "jump to '{label}' pc not reflected in join return tags"
                            ));
                        } else if arg_ltys.len() != sig.params.len() {
                            return err(format!("jump to '{label}' arity mismatch"));
                        } else if !arg_ltys.iter().zip(&sig.params).all(|(a, (_, p))| {
                            lty_subtype(&a.add_tags(&pc), p) && pc.is_subset(&p.tags)
                        }) {
                            return err(format!(
                                "jump to '{label}' argument type or pc-taint mismatch"
                            ));
                        }
                        vals.push(CheckedIr::LTy(sig.ret_lty.clone()));
                    }
                    None => return err(format!("jump to unbound or non-tail label '{label}'")),
                }
            }
            CheckTask::FinishTuple { n_elems, pc } => {
                let elem_ltys: Vec<LTy> = vals
                    .split_off(vals.len() - n_elems)
                    .into_iter()
                    .map(CheckedIr::into_lty)
                    .collect();
                vals.push(CheckedIr::LTy(LTy::new(Ty::Tuple(elem_ltys), pc)));
            }
            CheckTask::FinishProj { idx, pc } => {
                let Some(tup_lty) = vals.pop().map(CheckedIr::into_lty) else {
                    unreachable!("stack balanced");
                };
                match &tup_lty.ty {
                    Ty::Tuple(elem_ltys) => match idx.to_usize().and_then(|i| elem_ltys.get(i)) {
                        Some(e_lty) => {
                            vals.push(CheckedIr::LTy(e_lty.add_tags(&tup_lty.tags.union(&pc))));
                        }
                        None => return err(format!("tuple projection index {idx} out of bounds")),
                    },
                    _ => return err("projection requires Tuple operand"),
                }
            }
            CheckTask::FinishCtor {
                type_name,
                ctor_name,
                n_args,
                pc,
            } => {
                let arg_ltys: Vec<LTy> = vals
                    .split_off(vals.len() - n_args)
                    .into_iter()
                    .map(CheckedIr::into_lty)
                    .collect();
                let Some(d_decl) = prog.find_data(type_name) else {
                    return err(format!("unknown data type '{type_name}'"));
                };
                let Some(c_decl) = d_decl.ctors.iter().find(|c| c.name == *ctor_name) else {
                    return err(format!(
                        "unknown constructor '{ctor_name}' for '{type_name}'"
                    ));
                };
                if arg_ltys.len() != c_decl.fields.len() {
                    return err(format!("constructor '{ctor_name}' arity mismatch"));
                }
                if !arg_ltys
                    .iter()
                    .zip(&c_decl.fields)
                    .all(|(a, f)| a.ty == f.ty)
                {
                    return err(format!("constructor '{ctor_name}' field type mismatch"));
                }
                let extra_arg_tags = TagSet::union_owned(arg_ltys.iter().map(LTy::effective_tags));
                vals.push(CheckedIr::LTy(LTy::new(
                    Ty::Data(type_name.clone()),
                    extra_arg_tags.union(&pc),
                )));
            }
            CheckTask::FinishPrim { op, n_args, pc } => {
                let arg_ltys: Vec<LTy> = vals
                    .split_off(vals.len() - n_args)
                    .into_iter()
                    .map(CheckedIr::into_lty)
                    .collect();
                vals.push(CheckedIr::LTy(check_prim_op(prog, &pc, op, &arg_ltys)?));
            }
            CheckTask::FinishRel { pc } => {
                let Some(p_ty) = vals.pop().map(CheckedIr::into_plan_ty) else {
                    unreachable!("stack balanced");
                };
                vals.push(CheckedIr::LTy(p_ty.to_lty(&pc)));
            }
            CheckTask::FinishHost { op, n_args, pc } => {
                let arg_ltys: Vec<LTy> = vals
                    .split_off(vals.len() - n_args)
                    .into_iter()
                    .map(CheckedIr::into_lty)
                    .collect();
                vals.push(CheckedIr::LTy(check_host_op(
                    prog, &pc, in_spec, op, &arg_ltys,
                )?));
            }
            CheckTask::FinishStopDetail { pc } => {
                let Some(d_lty) = vals.pop().map(CheckedIr::into_lty) else {
                    unreachable!("stack balanced");
                };
                if is_equatable_ty(&d_lty.ty) {
                    vals.push(CheckedIr::LTy(LTy::new(Ty::Unit, pc)));
                } else {
                    return err("stop detail must be a printable/redacted value type");
                }
            }
            CheckTask::FinishFail { pc } => {
                let Some(m_lty) = vals.pop().map(CheckedIr::into_lty) else {
                    unreachable!("stack balanced");
                };
                if m_lty.ty == Ty::Text && m_lty.tags.is_subset(&pc) {
                    vals.push(CheckedIr::LTy(LTy::new(Ty::Unit, pc)));
                } else {
                    return err("Fail message must be Text with tags bounded by pc");
                }
            }
            CheckTask::FinishSourceExpr { pc } => {
                let Some(lty) = vals.pop().map(CheckedIr::into_lty) else {
                    unreachable!("stack balanced");
                };
                let extra = lty.tags.union(&pc);
                match lty.ty.into_table() {
                    Some(tt) => vals.push(CheckedIr::PlanTy(PlanTy::Table(TableTy {
                        row_tags: tt.row_tags.union(&extra),
                        order_tags: tt.order_tags.union(&extra),
                        ..tt
                    }))),
                    None => return err("SourceExpr requires Table expression"),
                }
            }
            CheckTask::FinishSourceDB { schema, pc } => {
                let Some(cap_lty) = vals.pop().map(CheckedIr::into_lty) else {
                    unreachable!("stack balanced");
                };
                match cap_lty.ty {
                    Ty::ReadDB(_) => {
                        if valid_table_ty(prog, schema)
                            && !schema.summarized
                            && schema.grouped_by.is_none()
                            && schema.distinct_by.is_none()
                            && schema
                                .cols
                                .iter()
                                .all(|c| !c.bucketed && c.agg_kind == AggKind::Raw)
                        {
                            let extra = cap_lty.tags.union(&pc);
                            vals.push(CheckedIr::PlanTy(PlanTy::Table(TableTy {
                                row_tags: schema.row_tags.union(&extra),
                                order_tags: schema.order_tags.union(&extra),
                                ..schema.clone()
                            })));
                        } else {
                            return err("invalid initial schema in SourceDB");
                        }
                    }
                    _ => return err("SourceDB requires ReadDB capability"),
                }
            }
            CheckTask::FinishPlanJoin { kind, on, suffixes } => {
                let (Some(r_plan), Some(l_plan)) = (
                    vals.pop().map(CheckedIr::into_plan_ty),
                    vals.pop().map(CheckedIr::into_plan_ty),
                ) else {
                    unreachable!("stack balanced");
                };
                match (l_plan, r_plan) {
                    (PlanTy::Table(l_tt), PlanTy::Table(r_tt)) => {
                        let key_pairs = resolve_join_pairs(&l_tt, &r_tt, on)?;
                        let on_tags = TagSet::union_owned(
                            key_pairs.iter().map(|(lc, rc)| lc.tags.union(&rc.tags)),
                        );
                        let joined_cols =
                            build_joined_cols(kind, &l_tt.cols, &r_tt.cols, on, suffixes)?;
                        let new_row_tags = l_tt.row_tags.union(&r_tt.row_tags).union(&on_tags);
                        let new_order_tags = match kind {
                            JoinKind::Semi | JoinKind::Anti => l_tt.order_tags,
                            _ => l_tt.order_tags.union(&r_tt.order_tags),
                        };
                        vals.push(CheckedIr::PlanTy(PlanTy::Table(TableTy {
                            cols: joined_cols,
                            row_tags: new_row_tags,
                            order_tags: new_order_tags,
                            grouped_by: None,
                            summarized: false,
                            distinct_by: None,
                        })));
                    }
                    _ => return err("Join inputs must be statically typed Tables"),
                }
            }
            CheckTask::FinishPlanUnion => {
                let (Some(r_plan), Some(l_plan)) = (
                    vals.pop().map(CheckedIr::into_plan_ty),
                    vals.pop().map(CheckedIr::into_plan_ty),
                ) else {
                    unreachable!("stack balanced");
                };
                match (l_plan, r_plan) {
                    (PlanTy::Table(l_tt), PlanTy::Table(r_tt)) => {
                        match merge_union_cols(&l_tt.cols, &r_tt.cols) {
                            Some(out_cols) => {
                                vals.push(CheckedIr::PlanTy(PlanTy::Table(TableTy {
                                    cols: out_cols,
                                    row_tags: l_tt.row_tags.union(&r_tt.row_tags),
                                    order_tags: l_tt.order_tags.union(&r_tt.order_tags),
                                    grouped_by: None,
                                    summarized: false,
                                    distinct_by: None,
                                })))
                            }
                            None => return err("Union requires matching column names and types"),
                        }
                    }
                    _ => return err("Union inputs must be statically typed Tables"),
                }
            }
            CheckTask::FinishPlanPseudo { col, pc } => {
                let (Some(sec_lty), Some(in_plan)) = (
                    vals.pop().map(CheckedIr::into_lty),
                    vals.pop().map(CheckedIr::into_plan_ty),
                ) else {
                    unreachable!("stack balanced");
                };
                match (in_plan, sec_lty.ty) {
                    (PlanTy::Table(tt), Ty::Secret(_)) => {
                        let Some(target_col) = tt.find_col(col) else {
                            return err(format!("unknown column '{col}' in Pseudonymize"));
                        };
                        if is_equatable_ty(&target_col.ty.to_ty())
                            && sec_lty
                                .tags
                                .is_subset(&TagSet::singleton("secret").union(&pc))
                        {
                            let cleared_tags = target_col.tags.remove("pii").union(&pc);
                            let out_cols = tt
                                .cols
                                .into_iter()
                                .map(|c| {
                                    if c.name == *col {
                                        ColSpec {
                                            ty: ScalarTy::Text,
                                            tags: cleared_tags.clone(),
                                            bucketed: false,
                                            agg_kind: AggKind::Raw,
                                            ..c
                                        }
                                    } else {
                                        ColSpec {
                                            agg_kind: AggKind::Raw,
                                            ..c
                                        }
                                    }
                                })
                                .collect();
                            vals.push(CheckedIr::PlanTy(PlanTy::Table(TableTy {
                                cols: out_cols,
                                row_tags: tt.row_tags,
                                order_tags: tt.order_tags,
                                grouped_by: None,
                                summarized: false,
                                distinct_by: None,
                            })));
                        } else {
                            return err(format!("Pseudonymize column '{col}' must be equatable"));
                        }
                    }
                    (PlanTy::Dynamic(_), _) => return err("cannot Pseudonymize on DynamicTable"),
                    _ => {
                        return err(
                            "Pseudonymize requires a Secret capability key (hardcoded strings forbidden)",
                        );
                    }
                }
            }
            CheckTask::FinishPlanUnary { stage, env, pc } => {
                let Some(in_plan) = vals.pop().map(CheckedIr::into_plan_ty) else {
                    unreachable!("stack balanced");
                };
                vals.push(CheckedIr::PlanTy(check_plan_unary_step(
                    prog, &env, &pc, stage, in_plan,
                )?));
            }
        }
    }
    match vals.pop() {
        Some(res) => Ok(res),
        None => unreachable!("check_ir_iter always produces one result"),
    }
}

pub fn check_expr(
    prog: &Program,
    env: &[(Ident, LTy)],
    jenv: &[(Ident, JoinSig)],
    pc: &TagSet,
    in_spec: bool,
    expr: &Expr,
) -> Result<LTy, CheckError> {
    let arc_env = ArcTyEnv::from_slice(env);
    let arc_jenv = ArcJoinEnv::from_slice(jenv);
    check_ir_iter(
        prog,
        in_spec,
        CheckTask::Expr {
            env: arc_env,
            jenv: arc_jenv,
            pc: pc.clone(),
            expr,
            verified_nfj: false,
        },
    )
    .map(CheckedIr::into_lty)
}

pub(crate) fn check_expr_arc(
    prog: &Program,
    env: &ArcTyEnv,
    pc: &TagSet,
    in_spec: bool,
    expr: &Expr,
    verified_nfj: bool,
) -> Result<LTy, CheckError> {
    check_ir_iter(
        prog,
        in_spec,
        CheckTask::Expr {
            env: env.clone(),
            jenv: ArcJoinEnv::empty(),
            pc: pc.clone(),
            expr,
            verified_nfj,
        },
    )
    .map(CheckedIr::into_lty)
}

pub fn check_plan(
    prog: &Program,
    env: &[(Ident, LTy)],
    pc: &TagSet,
    in_spec: bool,
    plan: &Plan,
) -> Result<PlanTy, CheckError> {
    let arc_env = ArcTyEnv::from_slice(env);
    check_plan_arc(prog, &arc_env, pc, in_spec, plan, false)
}

pub(crate) fn check_plan_arc(
    prog: &Program,
    env: &ArcTyEnv,
    pc: &TagSet,
    in_spec: bool,
    plan: &Plan,
    verified_nfj: bool,
) -> Result<PlanTy, CheckError> {
    check_ir_iter(
        prog,
        in_spec,
        CheckTask::Plan {
            env: env.clone(),
            pc: pc.clone(),
            plan,
            verified_nfj,
        },
    )
    .map(CheckedIr::into_plan_ty)
}

fn check_plan_unary_step(
    prog: &Program,
    env: &ArcTyEnv,
    pc: &TagSet,
    stage: &Plan,
    in_plan: PlanTy,
) -> Result<PlanTy, CheckError> {
    match stage {
        Plan::Select { cols, .. } => match in_plan {
            PlanTy::Table(tt) => {
                if cols.is_empty() || !distinct_idents(cols) {
                    return err("Select requires non-empty distinct column list");
                }
                if !cols.iter().all(|n| tt.find_col(n).is_some()) {
                    return err("Select references missing column");
                }
                let out_cols = cols
                    .iter()
                    .filter_map(|n| {
                        tt.find_col(n).map(|c| ColSpec {
                            agg_kind: AggKind::Raw,
                            ..c.clone()
                        })
                    })
                    .collect();
                Ok(PlanTy::Table(TableTy {
                    cols: out_cols,
                    row_tags: tt.row_tags,
                    order_tags: tt.order_tags,
                    grouped_by: None,
                    summarized: false,
                    distinct_by: None,
                }))
            }
            PlanTy::Dynamic(_) => err("cannot Select on DynamicTable"),
        },
        Plan::Drop { cols, .. } => match in_plan {
            PlanTy::Table(tt) => {
                if !distinct_idents(cols) || !cols.iter().all(|n| tt.find_col(n).is_some()) {
                    return err("Drop references unknown or duplicate columns");
                }
                let out_cols: Vec<ColSpec> = tt
                    .cols
                    .into_iter()
                    .filter(|c| !cols.contains(&c.name))
                    .map(|c| ColSpec {
                        agg_kind: AggKind::Raw,
                        ..c
                    })
                    .collect();
                if out_cols.is_empty() {
                    err("Drop cannot remove every column of a Table")
                } else {
                    Ok(PlanTy::Table(TableTy {
                        cols: out_cols,
                        row_tags: tt.row_tags,
                        order_tags: tt.order_tags,
                        grouped_by: None,
                        summarized: false,
                        distinct_by: None,
                    }))
                }
            }
            PlanTy::Dynamic(_) => err("cannot Drop on DynamicTable"),
        },
        Plan::Rename { pairs, .. } => match in_plan {
            PlanTy::Table(tt) => {
                let new_names: Vec<Ident> = pairs.iter().map(|(nw, _)| nw.clone()).collect();
                let old_names: Vec<Ident> = pairs.iter().map(|(_, ol)| ol.clone()).collect();
                if !distinct_idents(&new_names)
                    || !distinct_idents(&old_names)
                    || !old_names.iter().all(|old_n| tt.find_col(old_n).is_some())
                {
                    return err("Rename has duplicate or missing columns");
                }
                let out_cols: Vec<ColSpec> = tt
                    .cols
                    .into_iter()
                    .map(|c| match pairs.iter().find(|(_, old_n)| *old_n == c.name) {
                        Some((new_n, _)) => ColSpec {
                            name: new_n.clone(),
                            agg_kind: AggKind::Raw,
                            ..c
                        },
                        None => ColSpec {
                            agg_kind: AggKind::Raw,
                            ..c
                        },
                    })
                    .collect();
                let names: Vec<Ident> = out_cols.iter().map(|c| c.name.clone()).collect();
                if distinct_idents(&names) {
                    Ok(PlanTy::Table(TableTy {
                        cols: out_cols,
                        row_tags: tt.row_tags,
                        order_tags: tt.order_tags,
                        grouped_by: None,
                        summarized: false,
                        distinct_by: None,
                    }))
                } else {
                    err("Rename produced colliding column names")
                }
            }
            PlanTy::Dynamic(_) => err("cannot Rename on DynamicTable"),
        },
        Plan::Derive { items, .. } => match in_plan {
            PlanTy::Table(tt) => {
                let raw_cols: Vec<ColSpec> = tt
                    .cols
                    .into_iter()
                    .map(|c| ColSpec {
                        agg_kind: AggKind::Raw,
                        ..c
                    })
                    .collect();
                let out_cols = apply_derive_items_arc(prog, env, raw_cols, items)?;
                let names: Vec<Ident> = out_cols.iter().map(|c| c.name.clone()).collect();
                if distinct_idents(&names) {
                    Ok(PlanTy::Table(TableTy {
                        cols: out_cols,
                        row_tags: tt.row_tags,
                        order_tags: tt.order_tags,
                        grouped_by: None,
                        summarized: false,
                        distinct_by: None,
                    }))
                } else {
                    err("Derive produced duplicate column names")
                }
            }
            PlanTy::Dynamic(_) => err("cannot Derive on DynamicTable"),
        },
        Plan::Filter { pred, .. } => match in_plan {
            PlanTy::Table(tt) => {
                let (p_ty, p_tags) = check_row_expr_arc(prog, env, &tt.cols, pred)?;
                if p_ty == ScalarTy::Bool {
                    Ok(PlanTy::Table(TableTy {
                        cols: tt
                            .cols
                            .into_iter()
                            .map(|c| ColSpec {
                                agg_kind: AggKind::Raw,
                                ..c
                            })
                            .collect(),
                        row_tags: tt.row_tags.union(&p_tags),
                        order_tags: tt.order_tags,
                        grouped_by: None,
                        summarized: false,
                        distinct_by: None,
                    }))
                } else {
                    err("Filter predicate must return Bool")
                }
            }
            PlanTy::Dynamic(_) => err("cannot Filter on DynamicTable"),
        },
        Plan::Distinct { cols, .. } => match in_plan {
            PlanTy::Table(tt) => {
                let key_names: Vec<Ident> = if cols.is_empty() {
                    tt.col_names()
                } else {
                    cols.clone()
                };
                let keys_ok = distinct_idents(&key_names)
                    && key_names.iter().all(|k| {
                        tt.find_col(k)
                            .is_some_and(|c| is_equatable_ty(&c.ty.to_ty()))
                    });
                if !keys_ok {
                    return err("Distinct references missing or non-equatable columns");
                }
                let key_tags = TagSet::union_list(
                    key_names
                        .iter()
                        .filter_map(|k| tt.find_col(k).map(|c| &c.tags)),
                );
                let ord_dep = if key_names.len() == tt.cols.len() {
                    TagSet::empty()
                } else {
                    tt.order_tags.clone()
                };
                Ok(PlanTy::Table(TableTy {
                    cols: tt
                        .cols
                        .into_iter()
                        .map(|c| ColSpec {
                            agg_kind: AggKind::Raw,
                            ..c
                        })
                        .collect(),
                    row_tags: tt.row_tags.union(&key_tags).union(&ord_dep),
                    order_tags: tt.order_tags,
                    grouped_by: None,
                    summarized: false,
                    distinct_by: None,
                }))
            }
            PlanTy::Dynamic(_) => err("cannot Distinct on DynamicTable"),
        },
        Plan::Sort { keys, .. } => match in_plan {
            PlanTy::Table(tt) => {
                let key_names: Vec<Ident> = keys.iter().map(|(k, _)| k.clone()).collect();
                let keys_ok = !keys.is_empty()
                    && distinct_idents(&key_names)
                    && key_names.iter().all(|k| {
                        tt.find_col(k)
                            .is_some_and(|c| is_ordered_scalar_ty(&base_of_scalar(&c.ty).to_ty()))
                    });
                if !keys_ok {
                    return err("Sort requires non-empty distinct ordered columns");
                }
                let sort_key_tags = TagSet::union_list(
                    key_names
                        .iter()
                        .filter_map(|k| tt.find_col(k).map(|c| &c.tags)),
                );
                Ok(PlanTy::Table(TableTy {
                    cols: tt
                        .cols
                        .into_iter()
                        .map(|c| ColSpec {
                            agg_kind: AggKind::Raw,
                            ..c
                        })
                        .collect(),
                    row_tags: tt.row_tags,
                    order_tags: tt.order_tags.union(&sort_key_tags),
                    grouped_by: None,
                    summarized: false,
                    distinct_by: None,
                }))
            }
            PlanTy::Dynamic(_) => err("cannot Sort on DynamicTable"),
        },
        Plan::Limit { .. } => match in_plan {
            PlanTy::Table(tt) => {
                let row_tags = tt.row_tags.union(&tt.order_tags);
                Ok(PlanTy::Table(TableTy {
                    cols: tt
                        .cols
                        .into_iter()
                        .map(|c| ColSpec {
                            agg_kind: AggKind::Raw,
                            ..c
                        })
                        .collect(),
                    row_tags,
                    order_tags: tt.order_tags,
                    grouped_by: None,
                    summarized: false,
                    distinct_by: None,
                }))
            }
            PlanTy::Dynamic(_) => err("cannot Limit on DynamicTable"),
        },
        Plan::GroupBy { keys, .. } => match in_plan {
            PlanTy::Table(tt) => {
                let keys_ok = distinct_idents(keys)
                    && keys.iter().all(|k| {
                        tt.find_col(k).is_some_and(|c| {
                            is_ordered_scalar_ty(&base_of_scalar(&c.ty).to_ty())
                                || is_equatable_ty(&c.ty.to_ty())
                        })
                    });
                if !keys_ok {
                    return err(
                        "GroupBy references duplicate, missing, or non-equatable key columns",
                    );
                }
                let key_tags =
                    TagSet::union_list(keys.iter().filter_map(|k| tt.find_col(k).map(|c| &c.tags)));
                let out_cols = tt
                    .cols
                    .into_iter()
                    .map(|c| {
                        let agg_kind = if keys.contains(&c.name) {
                            AggKind::GroupKey
                        } else {
                            AggKind::Raw
                        };
                        ColSpec { agg_kind, ..c }
                    })
                    .collect();
                Ok(PlanTy::Table(TableTy {
                    cols: out_cols,
                    row_tags: tt.row_tags.union(&key_tags),
                    order_tags: tt.order_tags,
                    grouped_by: Some(keys.clone()),
                    summarized: false,
                    distinct_by: None,
                }))
            }
            PlanTy::Dynamic(_) => err("cannot GroupBy on DynamicTable"),
        },
        Plan::Summarize {
            aggs, distinct_key, ..
        } => match in_plan {
            PlanTy::Table(tt) => {
                let group_keys = tt.grouped_by.clone().unwrap_or_default();
                if aggs.is_empty() {
                    return err("Summarize requires at least one aggregate");
                }
                let dk_tags = match distinct_key {
                    None => TagSet::empty(),
                    Some(dk) => match tt.find_col(dk) {
                        Some(c) => {
                            if is_equatable_ty(&c.ty.to_ty()) {
                                c.tags.clone()
                            } else {
                                return err(format!("distinctKey '{dk}' must be equatable"));
                            }
                        }
                        None => return err(format!("unknown distinctKey '{dk}' in Summarize")),
                    },
                };
                let key_cols: Vec<ColSpec> = tt
                    .cols
                    .iter()
                    .filter(|c| group_keys.contains(&c.name))
                    .map(|c| ColSpec {
                        agg_kind: AggKind::GroupKey,
                        ..c.clone()
                    })
                    .collect();
                let agg_cols = check_agg_item_list_arc(prog, env, &tt, aggs)?;
                let mut out_cols = key_cols;
                out_cols.extend(agg_cols);
                let names: Vec<Ident> = out_cols.iter().map(|c| c.name.clone()).collect();
                if !distinct_idents(&names) {
                    return err("Summarize output column names must be strictly unique");
                }
                Ok(PlanTy::Table(TableTy {
                    cols: out_cols,
                    row_tags: tt.row_tags.union(&dk_tags),
                    order_tags: TagSet::empty(),
                    grouped_by: Some(group_keys),
                    summarized: true,
                    distinct_by: distinct_key.clone(),
                }))
            }
            PlanTy::Dynamic(_) => err("cannot Summarize on DynamicTable"),
        },
        Plan::SuppressSmallGroups {
            min_k,
            distinct_by,
            mode,
            ..
        } => match in_plan {
            PlanTy::Table(tt) => {
                let floor = prog.min_group_floor();
                if !tt.summarized {
                    return err(
                        "SuppressSmallGroups requires immediately summarized input table (summarized = true)",
                    );
                }
                if *min_k < floor {
                    return err(format!(
                        "SuppressSmallGroups min_k ({min_k}) is below required minimum floor ({floor})"
                    ));
                }
                if distinct_by.is_some() && *distinct_by != tt.distinct_by {
                    return err(
                        "SuppressSmallGroups distinct_by must match Summarize distinct_key",
                    );
                }
                let raw_key_tags = TagSet::union_list(
                    tt.cols
                        .iter()
                        .filter(|c| c.agg_kind == AggKind::GroupKey && !c.bucketed)
                        .map(|c| &c.tags),
                );
                let new_row_tags = raw_key_tags.union(pc);
                let out_cols = tt
                    .cols
                    .into_iter()
                    .map(|c| {
                        let orig_kind = c.agg_kind;
                        let base = match orig_kind {
                            AggKind::GroupKey => {
                                if c.bucketed {
                                    ColSpec {
                                        tags: pc.clone(),
                                        agg_kind: AggKind::Raw,
                                        ..c
                                    }
                                } else {
                                    ColSpec {
                                        agg_kind: AggKind::Raw,
                                        ..c
                                    }
                                }
                            }
                            AggKind::Blending => ColSpec {
                                tags: pc.clone(),
                                agg_kind: AggKind::Raw,
                                ..c
                            },
                            AggKind::NonBlending | AggKind::Raw => ColSpec {
                                agg_kind: AggKind::Raw,
                                ..c
                            },
                        };
                        match (mode, orig_kind) {
                            (
                                crate::core::syntax::SuppressMode::MaskComplementary,
                                AggKind::Blending | AggKind::NonBlending,
                            ) => ColSpec {
                                ty: ensure_option_scalar(&base.ty),
                                bucketed: false,
                                ..base
                            },
                            _ => base,
                        }
                    })
                    .collect();
                Ok(PlanTy::Table(TableTy {
                    cols: out_cols,
                    row_tags: new_row_tags,
                    order_tags: tt.order_tags,
                    grouped_by: None,
                    summarized: false,
                    distinct_by: None,
                }))
            }
            PlanTy::Dynamic(_) => err("cannot SuppressSmallGroups on DynamicTable"),
        },
        Plan::Window { items, .. } => match in_plan {
            PlanTy::Table(tt) => {
                if items.is_empty() {
                    return err("Window requires at least one WindowItem");
                }
                let raw_cols: Vec<ColSpec> = tt
                    .cols
                    .into_iter()
                    .map(|c| ColSpec {
                        agg_kind: AggKind::Raw,
                        ..c
                    })
                    .collect();
                let out_cols = apply_window_items(&tt.order_tags, raw_cols, items)?;
                let names: Vec<Ident> = out_cols.iter().map(|c| c.name.clone()).collect();
                if distinct_idents(&names) {
                    Ok(PlanTy::Table(TableTy {
                        cols: out_cols,
                        row_tags: tt.row_tags,
                        order_tags: tt.order_tags,
                        grouped_by: None,
                        summarized: false,
                        distinct_by: None,
                    }))
                } else {
                    err("Window produced duplicate column names")
                }
            }
            PlanTy::Dynamic(_) => err("cannot Window on DynamicTable"),
        },
        Plan::FillGaps {
            col,
            step_micros,
            over,
            fill,
            ..
        } => match in_plan {
            PlanTy::Table(tt) => {
                if !step_micros.is_positive() || !distinct_idents(over) {
                    return err("FillGaps requires positive step and distinct partition keys");
                }
                let Some(t_col) = tt.find_col(col) else {
                    return err(format!("missing time column '{col}' in FillGaps"));
                };
                if !matches!(
                    t_col.ty,
                    ScalarTy::Date | ScalarTy::Timestamp | ScalarTy::Int
                ) {
                    return err("FillGaps column must be Date, Timestamp, or Int");
                }
                if !over.iter().all(|k| k != col && tt.find_col(k).is_some()) {
                    return err("FillGaps partition keys must exist and exclude the time column");
                }
                let fill_ok = tt
                    .cols
                    .iter()
                    .filter(|c| c.name != *col && !over.contains(&c.name))
                    .all(|c| match fill.iter().find(|(fn_, _)| *fn_ == c.name) {
                        Some((_, lit)) => check_literal(prog, &TagSet::empty(), lit)
                            .is_ok_and(|lty| lty.ty == c.ty.to_ty()),
                        None => c.ty == ensure_option_scalar(&c.ty),
                    });
                if !fill_ok {
                    return err(
                        "FillGaps requires type-matching fill literals for non-nullable non-key columns",
                    );
                }
                let over_tags =
                    TagSet::union_list(over.iter().filter_map(|k| tt.find_col(k).map(|c| &c.tags)));
                let new_row_tags = tt.row_tags.union(&t_col.tags).union(&over_tags);
                let out_cols = tt
                    .cols
                    .iter()
                    .map(|c| {
                        if c.name == *col || over.contains(&c.name) {
                            ColSpec {
                                agg_kind: AggKind::Raw,
                                bucketed: false,
                                ..c.clone()
                            }
                        } else {
                            ColSpec {
                                tags: c.tags.union(&new_row_tags).union(&tt.order_tags),
                                agg_kind: AggKind::Raw,
                                bucketed: false,
                                ..c.clone()
                            }
                        }
                    })
                    .collect();
                Ok(PlanTy::Table(TableTy {
                    cols: out_cols,
                    row_tags: new_row_tags,
                    order_tags: TagSet::empty(),
                    grouped_by: None,
                    summarized: false,
                    distinct_by: None,
                }))
            }
            PlanTy::Dynamic(_) => err("cannot FillGaps on DynamicTable"),
        },
        Plan::PivotWider {
            names_from,
            values_from,
            static_cols,
            fill,
            ..
        } => match in_plan {
            PlanTy::Table(tt) => {
                if static_cols.is_empty()
                    || !distinct_idents(static_cols)
                    || names_from == values_from
                {
                    return err(
                        "PivotWider requires distinct non-empty staticCols and distinct namesFrom/valuesFrom",
                    );
                }
                let (Some(n_col), Some(v_col)) =
                    (tt.find_col(names_from), tt.find_col(values_from))
                else {
                    return err("PivotWider missing namesFrom or valuesFrom column");
                };
                if n_col.ty != ScalarTy::Text {
                    return err("PivotWider namesFrom column must have type Text");
                }
                let fill_lty = check_literal(prog, &TagSet::empty(), fill)?;
                if fill_lty.ty != v_col.ty.to_ty() {
                    return err("PivotWider fill literal must match valuesFrom type");
                }
                let id_cols: Vec<ColSpec> = tt
                    .cols
                    .iter()
                    .filter(|c| c.name != *names_from && c.name != *values_from)
                    .map(|c| ColSpec {
                        agg_kind: AggKind::Raw,
                        ..c.clone()
                    })
                    .collect();
                let id_tags = TagSet::union_list(id_cols.iter().map(|c| &c.tags));
                let new_row_tags = tt.row_tags.union(&n_col.tags).union(&id_tags);
                let cell_tags = n_col
                    .tags
                    .union(&v_col.tags)
                    .union(&new_row_tags)
                    .union(&tt.order_tags);
                let mut out_cols = id_cols;
                out_cols.extend(static_cols.iter().map(|sc| ColSpec {
                    name: sc.clone(),
                    ty: v_col.ty.clone(),
                    tags: cell_tags.clone(),
                    bucketed: false,
                    agg_kind: AggKind::Raw,
                }));
                let names: Vec<Ident> = out_cols.iter().map(|c| c.name.clone()).collect();
                if distinct_idents(&names) {
                    Ok(PlanTy::Table(TableTy {
                        cols: out_cols,
                        row_tags: new_row_tags,
                        order_tags: TagSet::empty(),
                        grouped_by: None,
                        summarized: false,
                        distinct_by: None,
                    }))
                } else {
                    err("PivotWider staticCols collide with remaining id columns")
                }
            }
            PlanTy::Dynamic(_) => err("cannot PivotWider on DynamicTable"),
        },
        Plan::Crosstab {
            rows_col,
            cols_col,
            values_col,
            fill,
            ..
        } => match in_plan {
            PlanTy::Table(tt) => {
                let (Some(r_col), Some(c_col), Some(v_col)) = (
                    tt.find_col(rows_col),
                    tt.find_col(cols_col),
                    tt.find_col(values_col),
                ) else {
                    return err("Crosstab missing column");
                };
                let fill_lty = check_literal(prog, &TagSet::empty(), fill)?;
                if is_equatable_ty(&r_col.ty.to_ty())
                    && is_equatable_ty(&c_col.ty.to_ty())
                    && fill_lty.ty == v_col.ty.to_ty()
                {
                    let dt_tags = tt
                        .row_tags
                        .union(&tt.order_tags)
                        .union(&r_col.tags)
                        .union(&c_col.tags)
                        .union(&v_col.tags)
                        .union(pc);
                    Ok(PlanTy::Dynamic(dt_tags))
                } else {
                    err("Crosstab column or fill type mismatch")
                }
            }
            PlanTy::Dynamic(_) => err("cannot Crosstab on DynamicTable"),
        },
        Plan::Redact { col, .. } => match in_plan {
            PlanTy::Table(tt) => {
                let Some(target_col) = tt.find_col(col) else {
                    return err(format!("unknown column '{col}' in Redact"));
                };
                if target_col.ty == ScalarTy::Text
                    || target_col.ty == ScalarTy::Option(Box::new(ScalarTy::Text))
                {
                    let out_cols = tt
                        .cols
                        .into_iter()
                        .map(|c| {
                            if c.name == *col {
                                ColSpec {
                                    ty: ScalarTy::Text,
                                    tags: pc.clone(),
                                    bucketed: false,
                                    agg_kind: AggKind::Raw,
                                    ..c
                                }
                            } else {
                                ColSpec {
                                    agg_kind: AggKind::Raw,
                                    ..c
                                }
                            }
                        })
                        .collect();
                    Ok(PlanTy::Table(TableTy {
                        cols: out_cols,
                        row_tags: tt.row_tags,
                        order_tags: tt.order_tags,
                        grouped_by: None,
                        summarized: false,
                        distinct_by: None,
                    }))
                } else {
                    err(format!("Redact column '{col}' must be Text or Text?"))
                }
            }
            PlanTy::Dynamic(_) => err("cannot Redact on DynamicTable"),
        },
        _ => unreachable!("non-unary plans handled by check_ir_iter"),
    }
}

// ---------------------------------------------------------------------------
// Whole-Program & Policy Verification (`check_program`)
// ---------------------------------------------------------------------------

fn check_data_decls(prog: &Program) -> Result<(), CheckError> {
    let names: Vec<Ident> = prog.datas.iter().map(|d| d.name.clone()).collect();
    if !distinct_idents(&names) {
        return err("duplicate data type names");
    }
    let ok = prog.datas.iter().all(|d| {
        let ctor_names: Vec<Ident> = d.ctors.iter().map(|c| c.name.clone()).collect();
        !d.ctors.is_empty()
            && distinct_idents(&ctor_names)
            && d.ctors.iter().all(|c| {
                c.fields
                    .iter()
                    .all(|f| valid_lty(prog, f) && is_equatable_ty(&f.ty))
            })
    });
    if ok {
        Ok(())
    } else {
        err("invalid DataDecl constructors or non-data fields")
    }
}

fn check_schema_decls(prog: &Program) -> Result<(), CheckError> {
    let names: Vec<Ident> = prog.schemas.iter().map(|s| s.name.clone()).collect();
    if !distinct_idents(&names) {
        return err("duplicate schema names");
    }
    let ok = prog.schemas.iter().all(|s| {
        valid_table_ty(prog, &s.schema)
            && !s.schema.summarized
            && s.schema.grouped_by.is_none()
            && s.schema.distinct_by.is_none()
            && s.schema
                .cols
                .iter()
                .all(|c| !c.bucketed && c.agg_kind == AggKind::Raw)
    });
    if ok {
        Ok(())
    } else {
        err("invalid SchemaDecl")
    }
}

fn check_const_decls(prog: &Program) -> Result<(), CheckError> {
    let names: Vec<Ident> = prog.consts.iter().map(|c| c.name.clone()).collect();
    if !distinct_idents(&names) {
        return err("duplicate constant names");
    }
    for ConstDecl { name, lty, value } in &prog.consts {
        if !valid_lty(prog, lty) {
            return err(format!("invalid type on constant '{name}'"));
        }
        let v_lty = check_literal(prog, &TagSet::empty(), value)?;
        if !lty_subtype(&v_lty, lty) {
            return err(format!(
                "constant '{name}' value does not match declared LTy"
            ));
        }
    }
    Ok(())
}

enum PureWork<'a> {
    Expr(&'a Expr),
    Plan(&'a Plan),
}

fn run_is_pure(mut stack: Vec<PureWork<'_>>) -> bool {
    while let Some(item) = stack.pop() {
        match item {
            PureWork::Expr(expr) => match expr {
                Expr::Lit(_) | Expr::Var(_) | Expr::ConstRef(_) | Expr::TableLit { .. } => {}
                Expr::LetE { bound, body, .. } => {
                    stack.push(PureWork::Expr(body));
                    stack.push(PureWork::Expr(bound));
                }
                Expr::IfE {
                    cond,
                    then_br,
                    else_br,
                } => {
                    stack.push(PureWork::Expr(else_br));
                    stack.push(PureWork::Expr(then_br));
                    stack.push(PureWork::Expr(cond));
                }
                Expr::CaseE { scrut, arms } => {
                    for a in arms {
                        stack.push(PureWork::Expr(&a.body));
                    }
                    stack.push(PureWork::Expr(scrut));
                }
                Expr::Lam { body, .. } => {
                    stack.push(PureWork::Expr(body));
                }
                Expr::Proj { tup: body, .. } => {
                    stack.push(PureWork::Expr(body));
                }
                Expr::App { fn_expr, args } => {
                    for a in args {
                        stack.push(PureWork::Expr(a));
                    }
                    stack.push(PureWork::Expr(fn_expr));
                }
                Expr::Call { args, .. }
                | Expr::Jump { args, .. }
                | Expr::Tuple(args)
                | Expr::Ctor { args, .. }
                | Expr::Prim { args, .. } => {
                    for a in args {
                        stack.push(PureWork::Expr(a));
                    }
                }
                Expr::Join { rhs, body, .. } => {
                    stack.push(PureWork::Expr(body));
                    stack.push(PureWork::Expr(rhs));
                }
                Expr::Rel(plan) => stack.push(PureWork::Plan(plan)),
                Expr::Host { .. } | Expr::Fail(_) => return false,
                Expr::Stop { detail, .. } => {
                    if let Some(d) = detail {
                        stack.push(PureWork::Expr(d));
                    }
                }
            },
            PureWork::Plan(plan) => match plan {
                Plan::SourceExpr(e) => stack.push(PureWork::Expr(e)),
                Plan::SourceDB { .. } | Plan::Pseudonymize { .. } => return false,
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
                | Plan::Redact { input, .. } => stack.push(PureWork::Plan(input)),
                Plan::Join { left, right, .. } | Plan::Union { left, right } => {
                    stack.push(PureWork::Plan(right));
                    stack.push(PureWork::Plan(left));
                }
            },
        }
    }
    true
}

#[must_use]
pub fn expr_is_pure(expr: &Expr) -> bool {
    run_is_pure(vec![PureWork::Expr(expr)])
}

#[must_use]
pub fn plan_is_pure(plan: &Plan) -> bool {
    run_is_pure(vec![PureWork::Plan(plan)])
}

#[must_use]
pub fn is_capability_ty(ty: &Ty) -> bool {
    matches!(
        ty,
        Ty::Args
            | Ty::Clock
            | Ty::Console(_)
            | Ty::ReadFiles
            | Ty::WriteFiles { .. }
            | Ty::ReadDB(_)
            | Ty::WriteTable { .. }
            | Ty::RawReadDB(_)
            | Ty::HttpsAllow { .. }
            | Ty::Secret(_)
            | Ty::Declassify(_)
    )
}

fn check_fun_decl(prog: &Program, f: &FunDecl) -> Result<(), CheckError> {
    let p_names: Vec<Ident> = f.params.iter().map(|(n, _)| n.clone()).collect();
    if !distinct_idents(&p_names) {
        return err(format!(
            "duplicate parameter names in function '{}'",
            f.name
        ));
    }
    if !f.params.iter().all(|(_, l)| valid_lty(prog, l))
        || !valid_tag_set(prog, &f.pc)
        || !valid_lty(prog, &f.ret)
    {
        return err(format!(
            "invalid types or undeclared sensitivity tags in function '{}'",
            f.name
        ));
    }
    if !f.pc.is_subset(&f.ret.effective_tags()) {
        return err(format!(
            "function '{}' caller pc bound must be reflected in return LTy",
            f.name
        ));
    }
    if !no_free_jumps(&[], &f.body) {
        return err(format!(
            "function '{}' contains jump to unbound label",
            f.name
        ));
    }
    if f.is_pure
        && (f.params.iter().any(|(_, l)| is_capability_ty(&l.ty)) || !expr_is_pure(&f.body))
    {
        return err(format!(
            "function '{}' marked pure contains host effects or capabilities",
            f.name
        ));
    }
    for (_, p_lty) in &f.params {
        check_cap_against_policy(prog.policy.as_ref(), &p_lty.ty)?;
    }
    let body_env: TyEnv = f.params.iter().rev().cloned().collect();
    let arc_env = ArcTyEnv::from_slice(&body_env);
    let body_lty = check_expr_arc(prog, &arc_env, &f.pc, f.kind.is_spec(), &f.body, true)?;
    if lty_subtype(&body_lty, &f.ret) {
        Ok(())
    } else {
        err(format!("function '{}' body return LTy mismatch", f.name))
    }
}

fn check_policy_wf(prog: &Program) -> Result<(), CheckError> {
    let Some(p) = &prog.policy else {
        return Ok(());
    };
    if p.min_group_size >= BigInt::one()
        && valid_tag_set(prog, &p.allow_console)
        && p.allow_export.iter().all(|(_, ts)| valid_tag_set(prog, ts))
        && p.allow_https.iter().all(|(_, ts)| valid_tag_set(prog, ts))
        && p.allow_write.iter().all(|r| valid_tag_set(prog, &r.tags))
    {
        Ok(())
    } else {
        err("invalid tags or min_group_size in Policy")
    }
}

/// Complete decidable static checker for Dana Core IR v0.1 programs.
/// Note: `prog.metadata` is intentionally never inspected.
pub fn check_program(prog: &Program) -> Result<(), CheckError> {
    with_large_stack(|| check_program_inner(prog))
}

fn check_program_inner(prog: &Program) -> Result<(), CheckError> {
    if prog.version.major != 0 || prog.version.minor != 1 {
        return err(format!(
            "unsupported Dana Core version {}.{}",
            prog.version.major, prog.version.minor
        ));
    }
    if !distinct_idents(&prog.tags)
        || prog
            .tags
            .iter()
            .any(|t| BUILT_IN_TAGS.contains(&t.as_str()))
    {
        return err("duplicate or built-in-shadowing custom tag declarations");
    }
    check_policy_wf(prog)?;
    check_data_decls(prog)?;
    check_schema_decls(prog)?;
    check_const_decls(prog)?;
    let fun_names: Vec<Ident> = prog.funs.iter().map(|f| f.name.clone()).collect();
    if !distinct_idents(&fun_names) {
        return err("duplicate function names");
    }
    for f in &prog.funs {
        check_fun_decl(prog, f)?;
    }
    if let Some(main_name) = &prog.entry {
        let Some(main_fn) = prog.find_fun(main_name) else {
            return err(format!("declared entry '{main_name}' not found"));
        };
        if main_fn.kind.is_spec() {
            return err("program entry cannot be a spec function");
        }
        if !main_fn.pc.is_empty() {
            return err("program entry must have public caller pc = []");
        }
        let params_ok = main_fn.params.iter().all(|(_, l)| {
            is_capability_ty(&l.ty)
                && match &l.ty {
                    Ty::Secret(_) => l.tags.is_subset(&TagSet::singleton("secret")),
                    _ => l.tags.is_empty(),
                }
        });
        if !params_ok {
            return err("program entry parameters must be top-level capabilities");
        }
    }
    Ok(())
}

#[must_use]
pub fn is_well_typed_program(prog: &Program) -> bool {
    check_program(prog).is_ok()
}
