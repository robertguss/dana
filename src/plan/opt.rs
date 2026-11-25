//! Stop-, tag-, and cardinality-preserving relational query optimizer for
//! Core IR v0.1 (`core::Plan`) and Phase 2 `ExecPlan`.

use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use crate::core::syntax::{
    CaseArm, DeriveItem, Expr, FunDecl, Ident, JoinKind, JoinOn, Literal, Plan, PrimOp, Program,
    RowExpr,
};
use crate::runtime::ir::{
    ExecCaseArm, ExecDeriveItem, ExecExpr, ExecFun, ExecPlan, ExecPrimOp, ExecProgram, ExecPromise,
    ExecRowExpr,
};

/// Counters describing algebraic rewrites applied during optimization.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct OptStats {
    pub filters_fused: usize,
    pub predicates_pushed: usize,
    pub dead_ops_eliminated: usize,
    pub derive_items_pruned: usize,
    pub limits_folded: usize,
}

// ===========================================================================
// Core IR v0.1 Optimizer (`core::Plan` / `core::Program`)
// ===========================================================================

/// Optimize every relational plan nested inside a Core IR v0.1 [`Program`].
#[must_use]
pub fn optimize_program(prog: &Program) -> (Program, OptStats) {
    let mut stats = OptStats::default();
    let funs = prog
        .funs
        .iter()
        .map(|f| FunDecl {
            body: optimize_core_expr(&f.body, prog, &mut stats),
            ..f.clone()
        })
        .collect();
    (
        Program {
            funs,
            ..prog.clone()
        },
        stats,
    )
}

/// Optimize a single Core IR v0.1 [`Plan`] tree.
#[must_use]
pub fn optimize_plan(plan: &Plan, prog: &Program) -> (Plan, OptStats) {
    let mut stats = OptStats::default();
    let p = optimize_core_plan_inner(plan, prog, &mut stats);
    (p, stats)
}

fn optimize_core_expr(expr: &Expr, prog: &Program, stats: &mut OptStats) -> Expr {
    match expr {
        Expr::Lit(_) | Expr::Var(_) | Expr::ConstRef(_) | Expr::TableLit { .. } => expr.clone(),
        Expr::LetE {
            name,
            lty,
            bound,
            body,
        } => Expr::LetE {
            name: name.clone(),
            lty: lty.clone(),
            bound: Box::new(optimize_core_expr(bound, prog, stats)),
            body: Box::new(optimize_core_expr(body, prog, stats)),
        },
        Expr::IfE {
            cond,
            then_br,
            else_br,
        } => Expr::IfE {
            cond: Box::new(optimize_core_expr(cond, prog, stats)),
            then_br: Box::new(optimize_core_expr(then_br, prog, stats)),
            else_br: Box::new(optimize_core_expr(else_br, prog, stats)),
        },
        Expr::CaseE { scrut, arms } => Expr::CaseE {
            scrut: Box::new(optimize_core_expr(scrut, prog, stats)),
            arms: arms
                .iter()
                .map(|a| CaseArm {
                    ctor: a.ctor.clone(),
                    binders: a.binders.clone(),
                    body: optimize_core_expr(&a.body, prog, stats),
                })
                .collect(),
        },
        Expr::Lam {
            params,
            pc,
            ret,
            body,
        } => Expr::Lam {
            params: params.clone(),
            pc: pc.clone(),
            ret: ret.clone(),
            body: Arc::new(optimize_core_expr(body, prog, stats)),
        },
        Expr::App { fn_expr, args } => Expr::App {
            fn_expr: Box::new(optimize_core_expr(fn_expr, prog, stats)),
            args: args
                .iter()
                .map(|a| optimize_core_expr(a, prog, stats))
                .collect(),
        },
        Expr::Call { fn_name, args } => Expr::Call {
            fn_name: fn_name.clone(),
            args: args
                .iter()
                .map(|a| optimize_core_expr(a, prog, stats))
                .collect(),
        },
        Expr::Join {
            label,
            params,
            rhs,
            body,
        } => Expr::Join {
            label: label.clone(),
            params: params.clone(),
            rhs: Box::new(optimize_core_expr(rhs, prog, stats)),
            body: Box::new(optimize_core_expr(body, prog, stats)),
        },
        Expr::Jump { label, args } => Expr::Jump {
            label: label.clone(),
            args: args
                .iter()
                .map(|a| optimize_core_expr(a, prog, stats))
                .collect(),
        },
        Expr::Tuple(xs) => Expr::Tuple(
            xs.iter()
                .map(|x| optimize_core_expr(x, prog, stats))
                .collect(),
        ),
        Expr::Proj { tup, idx } => Expr::Proj {
            tup: Box::new(optimize_core_expr(tup, prog, stats)),
            idx: idx.clone(),
        },
        Expr::Ctor {
            type_name,
            ctor_name,
            args,
        } => Expr::Ctor {
            type_name: type_name.clone(),
            ctor_name: ctor_name.clone(),
            args: args
                .iter()
                .map(|a| optimize_core_expr(a, prog, stats))
                .collect(),
        },
        Expr::Prim { op, args } => Expr::Prim {
            op: op.clone(),
            args: args
                .iter()
                .map(|a| optimize_core_expr(a, prog, stats))
                .collect(),
        },
        Expr::Rel(plan) => Expr::Rel(Box::new(optimize_core_plan_inner(plan, prog, stats))),
        Expr::Host { op, args } => Expr::Host {
            op: op.clone(),
            args: args
                .iter()
                .map(|a| optimize_core_expr(a, prog, stats))
                .collect(),
        },
        Expr::Stop { kind, detail } => Expr::Stop {
            kind: *kind,
            detail: detail
                .as_deref()
                .map(|d| Box::new(optimize_core_expr(d, prog, stats))),
        },
        Expr::Fail(e) => Expr::Fail(Box::new(optimize_core_expr(e, prog, stats))),
    }
}

/// Conservative stop analysis on a Core IR `RowExpr`.
#[must_use]
pub fn may_stop_core_row_expr(re: &RowExpr) -> bool {
    match re {
        RowExpr::Lit(_) | RowExpr::Col(_) | RowExpr::OuterVar(_) | RowExpr::ConstRef(_) => false,
        RowExpr::CallPure { .. } => true,
        RowExpr::IfE {
            cond,
            then_br,
            else_br,
        } => {
            may_stop_core_row_expr(cond)
                || may_stop_core_row_expr(then_br)
                || may_stop_core_row_expr(else_br)
        }
        RowExpr::Coalesce {
            opt_expr,
            default_expr,
        } => may_stop_core_row_expr(opt_expr) || may_stop_core_row_expr(default_expr),
        RowExpr::Prim { op, args } => {
            prim_op_may_stop(op) || args.iter().any(may_stop_core_row_expr)
        }
    }
}

const fn prim_op_may_stop(op: &PrimOp) -> bool {
    matches!(
        op,
        PrimOp::UnwrapBang
            | PrimOp::AddInt
            | PrimOp::SubInt
            | PrimOp::MulInt
            | PrimOp::DivInt
            | PrimOp::ModInt
            | PrimOp::NegInt
            | PrimOp::AddDec
            | PrimOp::SubDec
            | PrimOp::MulDec
            | PrimOp::DivDec
            | PrimOp::NegDec
            | PrimOp::IntToDec
            | PrimOp::ListLen
            | PrimOp::TableCount
            | PrimOp::StatsLinReg { .. }
            | PrimOp::StatsTTest { .. }
    )
}

fn may_stop_core_derive_item(item: &DeriveItem) -> bool {
    match item {
        DeriveItem::ColExpr { expr, .. } => may_stop_core_row_expr(expr),
        DeriveItem::BucketCol { .. } => false,
    }
}

fn core_row_expr_cols(re: &RowExpr, out: &mut HashSet<Ident>) {
    match re {
        RowExpr::Col(c) => {
            out.insert(c.clone());
        }
        RowExpr::Lit(_) | RowExpr::OuterVar(_) | RowExpr::ConstRef(_) => {}
        RowExpr::Prim { args, .. } | RowExpr::CallPure { args, .. } => {
            for a in args {
                core_row_expr_cols(a, out);
            }
        }
        RowExpr::IfE {
            cond,
            then_br,
            else_br,
        } => {
            core_row_expr_cols(cond, out);
            core_row_expr_cols(then_br, out);
            core_row_expr_cols(else_br, out);
        }
        RowExpr::Coalesce {
            opt_expr,
            default_expr,
        } => {
            core_row_expr_cols(opt_expr, out);
            core_row_expr_cols(default_expr, out);
        }
    }
}

fn subst_core_row_expr_cols(re: &RowExpr, map: &HashMap<String, String>) -> RowExpr {
    match re {
        RowExpr::Col(c) => RowExpr::Col(map.get(c).cloned().unwrap_or_else(|| c.clone())),
        RowExpr::Lit(l) => RowExpr::Lit(l.clone()),
        RowExpr::OuterVar(v) => RowExpr::OuterVar(v.clone()),
        RowExpr::ConstRef(c) => RowExpr::ConstRef(c.clone()),
        RowExpr::Prim { op, args } => RowExpr::Prim {
            op: op.clone(),
            args: args
                .iter()
                .map(|a| subst_core_row_expr_cols(a, map))
                .collect(),
        },
        RowExpr::IfE {
            cond,
            then_br,
            else_br,
        } => RowExpr::IfE {
            cond: Box::new(subst_core_row_expr_cols(cond, map)),
            then_br: Box::new(subst_core_row_expr_cols(then_br, map)),
            else_br: Box::new(subst_core_row_expr_cols(else_br, map)),
        },
        RowExpr::Coalesce {
            opt_expr,
            default_expr,
        } => RowExpr::Coalesce {
            opt_expr: Box::new(subst_core_row_expr_cols(opt_expr, map)),
            default_expr: Box::new(subst_core_row_expr_cols(default_expr, map)),
        },
        RowExpr::CallPure { fn_name, args } => RowExpr::CallPure {
            fn_name: fn_name.clone(),
            args: args
                .iter()
                .map(|a| subst_core_row_expr_cols(a, map))
                .collect(),
        },
    }
}

fn known_core_plan_cols(plan: &Plan) -> Option<Vec<Ident>> {
    match plan {
        Plan::SourceExpr(e) => match e.as_ref() {
            Expr::TableLit { schema, .. } => {
                Some(schema.cols.iter().map(|c| c.name.clone()).collect())
            }
            _ => None,
        },
        Plan::SourceDB { schema, .. } => Some(schema.cols.iter().map(|c| c.name.clone()).collect()),
        Plan::Select { cols, .. } => Some(cols.clone()),
        Plan::Drop { input, cols } => {
            let mut in_c = known_core_plan_cols(input)?;
            in_c.retain(|c| !cols.contains(c));
            Some(in_c)
        }
        Plan::Rename { input, pairs } => {
            let in_c = known_core_plan_cols(input)?;
            Some(
                in_c.into_iter()
                    .map(|c| {
                        pairs
                            .iter()
                            .find(|(_, old_n)| *old_n == c)
                            .map_or(c, |(new_n, _)| new_n.clone())
                    })
                    .collect(),
            )
        }
        Plan::Derive { input, items } => {
            let mut cols = known_core_plan_cols(input)?;
            for it in items {
                let name = match it {
                    DeriveItem::ColExpr { name, .. } | DeriveItem::BucketCol { name, .. } => name,
                };
                if !cols.contains(name) {
                    cols.push(name.clone());
                }
            }
            Some(cols)
        }
        Plan::Filter { input, .. }
        | Plan::Distinct { input, .. }
        | Plan::Sort { input, .. }
        | Plan::Limit { input, .. }
        | Plan::GroupBy { input, .. }
        | Plan::SuppressSmallGroups { input, .. }
        | Plan::FillGaps { input, .. }
        | Plan::Redact { input, .. }
        | Plan::Pseudonymize { input, .. } => known_core_plan_cols(input),
        Plan::Union { left, .. } => known_core_plan_cols(left),
        Plan::Window { input, items } => {
            let mut cols = known_core_plan_cols(input)?;
            for it in items {
                if !cols.contains(&it.name) {
                    cols.push(it.name.clone());
                }
            }
            Some(cols)
        }
        Plan::Join {
            kind,
            left,
            right,
            on,
            suffixes,
        } => {
            let l_cols = known_core_plan_cols(left)?;
            if matches!(kind, JoinKind::Semi | JoinKind::Anti) {
                return Some(l_cols);
            }
            let r_cols = known_core_plan_cols(right)?;
            let same_keys: &[Ident] = match on {
                JoinOn::SameKeys(ks) => ks,
                JoinOn::Pairs(_) => &[],
            };
            let r_kept: Vec<Ident> = r_cols
                .into_iter()
                .filter(|rc| !same_keys.contains(rc))
                .collect();
            let has_collision = l_cols.iter().any(|lc| r_kept.contains(lc));
            if !has_collision {
                let mut out = l_cols;
                out.extend(r_kept);
                Some(out)
            } else if let Some((sl, sr)) = suffixes {
                let mut out: Vec<Ident> = l_cols
                    .iter()
                    .map(|c| {
                        if r_kept.contains(c) {
                            format!("{c}{sl}")
                        } else {
                            c.clone()
                        }
                    })
                    .collect();
                for c in &r_kept {
                    if l_cols.contains(c) {
                        out.push(format!("{c}{sr}"));
                    } else {
                        out.push(c.clone());
                    }
                }
                Some(out)
            } else {
                None
            }
        }
        Plan::Summarize { .. } | Plan::PivotWider { .. } | Plan::Crosstab { .. } => None,
    }
}

fn optimize_core_plan_inner(plan: &Plan, prog: &Program, stats: &mut OptStats) -> Plan {
    let rewritten = rewrite_core_plan(plan, prog, stats);
    prune_core_plan_derives(&rewritten, None, stats)
}

fn rewrite_core_plan(plan: &Plan, prog: &Program, stats: &mut OptStats) -> Plan {
    match plan {
        Plan::SourceExpr(e) => Plan::SourceExpr(Box::new(optimize_core_expr(e, prog, stats))),
        Plan::SourceDB {
            cap,
            table_name,
            schema,
        } => Plan::SourceDB {
            cap: Box::new(optimize_core_expr(cap, prog, stats)),
            table_name: table_name.clone(),
            schema: schema.clone(),
        },
        Plan::Select { input, cols } => {
            let opt_in = rewrite_core_plan(input, prog, stats);
            if let Plan::Select {
                input: inner,
                cols: inner_cols,
            } = &opt_in
                && cols.iter().all(|c| inner_cols.contains(c))
            {
                stats.dead_ops_eliminated += 1;
                return Plan::Select {
                    input: Box::new((**inner).clone()),
                    cols: cols.clone(),
                };
            }
            Plan::Select {
                input: Box::new(opt_in),
                cols: cols.clone(),
            }
        }
        Plan::Drop { input, cols } => {
            let opt_in = rewrite_core_plan(input, prog, stats);
            if cols.is_empty() {
                stats.dead_ops_eliminated += 1;
                return opt_in;
            }
            Plan::Drop {
                input: Box::new(opt_in),
                cols: cols.clone(),
            }
        }
        Plan::Rename { input, pairs } => {
            let opt_in = rewrite_core_plan(input, prog, stats);
            if pairs.is_empty() {
                stats.dead_ops_eliminated += 1;
                return opt_in;
            }
            Plan::Rename {
                input: Box::new(opt_in),
                pairs: pairs.clone(),
            }
        }
        Plan::Derive { input, items } => {
            let opt_in = rewrite_core_plan(input, prog, stats);
            if items.is_empty() {
                stats.dead_ops_eliminated += 1;
                return opt_in;
            }
            Plan::Derive {
                input: Box::new(opt_in),
                items: items.clone(),
            }
        }
        Plan::Filter { input, pred } => {
            let opt_in = rewrite_core_plan(input, prog, stats);
            push_or_fuse_core_filter(&opt_in, pred.clone(), stats)
        }
        Plan::Distinct { input, cols } => Plan::Distinct {
            input: Box::new(rewrite_core_plan(input, prog, stats)),
            cols: cols.clone(),
        },
        Plan::Sort { input, keys } => {
            let opt_in = rewrite_core_plan(input, prog, stats);
            if keys.is_empty() {
                stats.dead_ops_eliminated += 1;
                return opt_in;
            }
            Plan::Sort {
                input: Box::new(opt_in),
                keys: keys.clone(),
            }
        }
        Plan::Limit { input, n } => {
            let opt_in = rewrite_core_plan(input, prog, stats);
            if let Plan::Limit {
                input: inner,
                n: n_inner,
            } = &opt_in
            {
                stats.limits_folded += 1;
                let folded = if n <= n_inner {
                    n.clone()
                } else {
                    n_inner.clone()
                };
                return Plan::Limit {
                    input: Box::new((**inner).clone()),
                    n: folded,
                };
            }
            Plan::Limit {
                input: Box::new(opt_in),
                n: n.clone(),
            }
        }
        Plan::Join {
            kind,
            left,
            right,
            on,
            suffixes,
        } => Plan::Join {
            kind: *kind,
            left: Box::new(rewrite_core_plan(left, prog, stats)),
            right: Box::new(rewrite_core_plan(right, prog, stats)),
            on: on.clone(),
            suffixes: suffixes.clone(),
        },
        Plan::Union { left, right } => Plan::Union {
            left: Box::new(rewrite_core_plan(left, prog, stats)),
            right: Box::new(rewrite_core_plan(right, prog, stats)),
        },
        Plan::GroupBy { input, keys } => Plan::GroupBy {
            input: Box::new(rewrite_core_plan(input, prog, stats)),
            keys: keys.clone(),
        },
        Plan::Summarize {
            input,
            aggs,
            distinct_key,
        } => Plan::Summarize {
            input: Box::new(rewrite_core_plan(input, prog, stats)),
            aggs: aggs.clone(),
            distinct_key: distinct_key.clone(),
        },
        Plan::SuppressSmallGroups {
            input,
            min_k,
            distinct_by,
            mode,
        } => Plan::SuppressSmallGroups {
            input: Box::new(rewrite_core_plan(input, prog, stats)),
            min_k: min_k.clone(),
            distinct_by: distinct_by.clone(),
            mode: *mode,
        },
        Plan::Window { input, items } => {
            let opt_in = rewrite_core_plan(input, prog, stats);
            if items.is_empty() {
                stats.dead_ops_eliminated += 1;
                return opt_in;
            }
            Plan::Window {
                input: Box::new(opt_in),
                items: items.clone(),
            }
        }
        Plan::FillGaps {
            input,
            col,
            step_micros,
            over,
            fill,
        } => Plan::FillGaps {
            input: Box::new(rewrite_core_plan(input, prog, stats)),
            col: col.clone(),
            step_micros: step_micros.clone(),
            over: over.clone(),
            fill: fill.clone(),
        },
        Plan::PivotWider {
            input,
            names_from,
            values_from,
            static_cols,
            fill,
        } => Plan::PivotWider {
            input: Box::new(rewrite_core_plan(input, prog, stats)),
            names_from: names_from.clone(),
            values_from: values_from.clone(),
            static_cols: static_cols.clone(),
            fill: fill.clone(),
        },
        Plan::Crosstab {
            input,
            rows_col,
            cols_col,
            values_col,
            fill,
        } => Plan::Crosstab {
            input: Box::new(rewrite_core_plan(input, prog, stats)),
            rows_col: rows_col.clone(),
            cols_col: cols_col.clone(),
            values_col: values_col.clone(),
            fill: fill.clone(),
        },
        Plan::Redact {
            input,
            col,
            replacement,
        } => Plan::Redact {
            input: Box::new(rewrite_core_plan(input, prog, stats)),
            col: col.clone(),
            replacement: replacement.clone(),
        },
        Plan::Pseudonymize { input, col, secret } => Plan::Pseudonymize {
            input: Box::new(rewrite_core_plan(input, prog, stats)),
            col: col.clone(),
            secret: Box::new(optimize_core_expr(secret, prog, stats)),
        },
    }
}

fn push_or_fuse_core_filter(input: &Plan, pred: RowExpr, stats: &mut OptStats) -> Plan {
    if matches!(pred, RowExpr::Lit(Literal::Bool(true)))
        && !matches!(input, Plan::GroupBy { .. } | Plan::Summarize { .. })
    {
        stats.dead_ops_eliminated += 1;
        return input.clone();
    }

    let pred_total = !may_stop_core_row_expr(&pred);
    let mut pred_cols = HashSet::new();
    core_row_expr_cols(&pred, &mut pred_cols);

    match input {
        // Filter fusion: `Filter(Filter(inner, e1), e2)` -> `Filter(inner, if e1 then e2 else false)`.
        Plan::Filter {
            input: inner,
            pred: p1,
        } => {
            stats.filters_fused += 1;
            let fused = RowExpr::IfE {
                cond: Box::new(p1.clone()),
                then_br: Box::new(pred),
                else_br: Box::new(RowExpr::Lit(Literal::Bool(false))),
            };
            push_or_fuse_core_filter(inner, fused, stats)
        }
        Plan::Select { input: inner, cols }
            if !matches!(
                inner.as_ref(),
                Plan::GroupBy { .. } | Plan::Summarize { .. }
            ) =>
        {
            stats.predicates_pushed += 1;
            let pushed = push_or_fuse_core_filter(inner, pred, stats);
            Plan::Select {
                input: Box::new(pushed),
                cols: cols.clone(),
            }
        }
        Plan::Drop { input: inner, cols }
            if !matches!(
                inner.as_ref(),
                Plan::GroupBy { .. } | Plan::Summarize { .. }
            ) =>
        {
            stats.predicates_pushed += 1;
            let pushed = push_or_fuse_core_filter(inner, pred, stats);
            Plan::Drop {
                input: Box::new(pushed),
                cols: cols.clone(),
            }
        }
        // Core IR `Rename` pairs are `(new_name, old_name)`.
        Plan::Rename {
            input: inner,
            pairs,
        } if !matches!(
            inner.as_ref(),
            Plan::GroupBy { .. } | Plan::Summarize { .. }
        ) =>
        {
            let mut rev_map: HashMap<String, String> = HashMap::with_capacity(pairs.len());
            let mut all_distinct_new = true;
            for (new_n, old_n) in pairs {
                if rev_map.insert(new_n.clone(), old_n.clone()).is_some() {
                    all_distinct_new = false;
                }
            }
            if all_distinct_new {
                stats.predicates_pushed += 1;
                let rewritten_pred = subst_core_row_expr_cols(&pred, &rev_map);
                let pushed = push_or_fuse_core_filter(inner, rewritten_pred, stats);
                Plan::Rename {
                    input: Box::new(pushed),
                    pairs: pairs.clone(),
                }
            } else {
                Plan::Filter {
                    input: Box::new(input.clone()),
                    pred,
                }
            }
        }
        Plan::Derive {
            input: inner,
            items,
        } if !matches!(
            inner.as_ref(),
            Plan::GroupBy { .. } | Plan::Summarize { .. }
        ) && items.iter().all(|it| {
            let target = match it {
                DeriveItem::ColExpr { name, .. } | DeriveItem::BucketCol { name, .. } => name,
            };
            !pred_cols.contains(target) && !may_stop_core_derive_item(it)
        }) =>
        {
            stats.predicates_pushed += 1;
            let pushed = push_or_fuse_core_filter(inner, pred, stats);
            Plan::Derive {
                input: Box::new(pushed),
                items: items.clone(),
            }
        }
        Plan::Sort { input: inner, keys }
            if pred_total
                && !matches!(
                    inner.as_ref(),
                    Plan::GroupBy { .. } | Plan::Summarize { .. }
                ) =>
        {
            stats.predicates_pushed += 1;
            let pushed = push_or_fuse_core_filter(inner, pred, stats);
            Plan::Sort {
                input: Box::new(pushed),
                keys: keys.clone(),
            }
        }
        Plan::Redact {
            input: inner,
            col,
            replacement,
        } if !pred_cols.contains(col)
            && !matches!(
                inner.as_ref(),
                Plan::GroupBy { .. } | Plan::Summarize { .. }
            ) =>
        {
            stats.predicates_pushed += 1;
            let pushed = push_or_fuse_core_filter(inner, pred, stats);
            Plan::Redact {
                input: Box::new(pushed),
                col: col.clone(),
                replacement: replacement.clone(),
            }
        }
        Plan::Union { left, right }
            if pred_total
                && !matches!(left.as_ref(), Plan::GroupBy { .. } | Plan::Summarize { .. })
                && !matches!(
                    right.as_ref(),
                    Plan::GroupBy { .. } | Plan::Summarize { .. }
                ) =>
        {
            stats.predicates_pushed += 1;
            let p_left = push_or_fuse_core_filter(left, pred.clone(), stats);
            let p_right = push_or_fuse_core_filter(right, pred, stats);
            Plan::Union {
                left: Box::new(p_left),
                right: Box::new(p_right),
            }
        }
        Plan::Join {
            kind,
            left,
            right,
            on,
            suffixes,
        } if pred_total && !pred_cols.is_empty() => {
            let can_push_left = matches!(
                kind,
                JoinKind::InnerMany
                    | JoinKind::InnerManyToOne
                    | JoinKind::LeftManyToOne
                    | JoinKind::Semi
                    | JoinKind::Anti
            );
            let can_push_right = matches!(kind, JoinKind::InnerMany);
            if let (Some(l_cols), Some(r_cols)) =
                (known_core_plan_cols(left), known_core_plan_cols(right))
            {
                let same_keys: &[Ident] = match on {
                    JoinOn::SameKeys(ks) => ks,
                    JoinOn::Pairs(_) => &[],
                };
                let r_kept: Vec<&Ident> =
                    r_cols.iter().filter(|rc| !same_keys.contains(rc)).collect();
                let has_collision = l_cols.iter().any(|lc| r_kept.contains(&lc));
                if !has_collision {
                    let l_set: HashSet<&str> = l_cols.iter().map(String::as_str).collect();
                    let r_only_set: HashSet<&str> = r_kept.iter().map(|s| s.as_str()).collect();
                    if can_push_left
                        && pred_cols.iter().all(|c| l_set.contains(c.as_str()))
                        && !matches!(left.as_ref(), Plan::GroupBy { .. } | Plan::Summarize { .. })
                    {
                        stats.predicates_pushed += 1;
                        let pushed_l = push_or_fuse_core_filter(left, pred, stats);
                        return Plan::Join {
                            kind: *kind,
                            left: Box::new(pushed_l),
                            right: Box::new((**right).clone()),
                            on: on.clone(),
                            suffixes: suffixes.clone(),
                        };
                    }
                    if can_push_right
                        && pred_cols.iter().all(|c| r_only_set.contains(c.as_str()))
                        && !matches!(
                            right.as_ref(),
                            Plan::GroupBy { .. } | Plan::Summarize { .. }
                        )
                    {
                        stats.predicates_pushed += 1;
                        let pushed_r = push_or_fuse_core_filter(right, pred, stats);
                        return Plan::Join {
                            kind: *kind,
                            left: Box::new((**left).clone()),
                            right: Box::new(pushed_r),
                            on: on.clone(),
                            suffixes: suffixes.clone(),
                        };
                    }
                }
            }
            Plan::Filter {
                input: Box::new(input.clone()),
                pred,
            }
        }
        other => Plan::Filter {
            input: Box::new(other.clone()),
            pred,
        },
    }
}

fn prune_core_plan_derives(
    plan: &Plan,
    needed: Option<&HashSet<Ident>>,
    stats: &mut OptStats,
) -> Plan {
    match plan {
        Plan::Select { input, cols } => {
            let req: HashSet<Ident> = cols.iter().cloned().collect();
            Plan::Select {
                input: Box::new(prune_core_plan_derives(input, Some(&req), stats)),
                cols: cols.clone(),
            }
        }
        Plan::Drop { input, cols } => {
            let opt_in = match needed {
                Some(req) => {
                    let mut child_req = req.clone();
                    for c in cols {
                        child_req.remove(c);
                    }
                    prune_core_plan_derives(input, Some(&child_req), stats)
                }
                None => prune_core_plan_derives(input, None, stats),
            };
            Plan::Drop {
                input: Box::new(opt_in),
                cols: cols.clone(),
            }
        }
        Plan::Rename { input, pairs } => {
            let opt_in = match needed {
                Some(req) => {
                    let child_req: HashSet<Ident> = req
                        .iter()
                        .map(|c| {
                            pairs
                                .iter()
                                .find(|(new_n, _)| new_n == c)
                                .map_or_else(|| c.clone(), |(_, old_n)| old_n.clone())
                        })
                        .collect();
                    prune_core_plan_derives(input, Some(&child_req), stats)
                }
                None => prune_core_plan_derives(input, None, stats),
            };
            Plan::Rename {
                input: Box::new(opt_in),
                pairs: pairs.clone(),
            }
        }
        Plan::Filter { input, pred } => {
            let opt_in = match needed {
                Some(req) => {
                    let mut child_req = req.clone();
                    core_row_expr_cols(pred, &mut child_req);
                    prune_core_plan_derives(input, Some(&child_req), stats)
                }
                None => prune_core_plan_derives(input, None, stats),
            };
            Plan::Filter {
                input: Box::new(opt_in),
                pred: pred.clone(),
            }
        }
        Plan::Sort { input, keys } => {
            let opt_in = match needed {
                Some(req) => {
                    let mut child_req = req.clone();
                    for (k, _) in keys {
                        child_req.insert(k.clone());
                    }
                    prune_core_plan_derives(input, Some(&child_req), stats)
                }
                None => prune_core_plan_derives(input, None, stats),
            };
            Plan::Sort {
                input: Box::new(opt_in),
                keys: keys.clone(),
            }
        }
        Plan::Limit { input, n } => Plan::Limit {
            input: Box::new(prune_core_plan_derives(input, needed, stats)),
            n: n.clone(),
        },
        Plan::Derive { input, items } => {
            let Some(req) = needed else {
                return Plan::Derive {
                    input: Box::new(prune_core_plan_derives(input, None, stats)),
                    items: items.clone(),
                };
            };
            let mut live = req.clone();
            let mut keep_flags = vec![false; items.len()];
            for (idx, it) in items.iter().enumerate().rev() {
                let target = match it {
                    DeriveItem::ColExpr { name, .. } | DeriveItem::BucketCol { name, .. } => name,
                };
                if live.contains(target) || may_stop_core_derive_item(it) {
                    keep_flags[idx] = true;
                    live.remove(target);
                    match it {
                        DeriveItem::ColExpr { expr, .. } => core_row_expr_cols(expr, &mut live),
                        DeriveItem::BucketCol { source, .. } => {
                            live.insert(source.clone());
                        }
                    }
                } else {
                    stats.derive_items_pruned += 1;
                }
            }
            let kept: Vec<DeriveItem> = items
                .iter()
                .zip(keep_flags)
                .filter(|(_, keep)| *keep)
                .map(|(it, _)| it.clone())
                .collect();
            let opt_in = prune_core_plan_derives(input, Some(&live), stats);
            if kept.is_empty() {
                stats.dead_ops_eliminated += 1;
                opt_in
            } else {
                Plan::Derive {
                    input: Box::new(opt_in),
                    items: kept,
                }
            }
        }
        Plan::Union { left, right } => Plan::Union {
            left: Box::new(prune_core_plan_derives(left, needed, stats)),
            right: Box::new(prune_core_plan_derives(right, needed, stats)),
        },
        Plan::Join {
            kind,
            left,
            right,
            on,
            suffixes,
        } => Plan::Join {
            kind: *kind,
            left: Box::new(prune_core_plan_derives(left, None, stats)),
            right: Box::new(prune_core_plan_derives(right, None, stats)),
            on: on.clone(),
            suffixes: suffixes.clone(),
        },
        Plan::Distinct { input, cols } => Plan::Distinct {
            input: Box::new(prune_core_plan_derives(input, None, stats)),
            cols: cols.clone(),
        },
        Plan::GroupBy { input, keys } => Plan::GroupBy {
            input: Box::new(prune_core_plan_derives(input, None, stats)),
            keys: keys.clone(),
        },
        Plan::Summarize {
            input,
            aggs,
            distinct_key,
        } => {
            let mut req = HashSet::new();
            for a in aggs {
                if let Some(re) = &a.arg {
                    core_row_expr_cols(re, &mut req);
                }
            }
            if let Some(dk) = distinct_key {
                req.insert(dk.clone());
            }
            let opt_in = match input.as_ref() {
                Plan::GroupBy {
                    input: gb_in,
                    keys: gb_keys,
                } => {
                    for k in gb_keys {
                        req.insert(k.clone());
                    }
                    Plan::GroupBy {
                        input: Box::new(prune_core_plan_derives(gb_in, Some(&req), stats)),
                        keys: gb_keys.clone(),
                    }
                }
                other => prune_core_plan_derives(other, Some(&req), stats),
            };
            Plan::Summarize {
                input: Box::new(opt_in),
                aggs: aggs.clone(),
                distinct_key: distinct_key.clone(),
            }
        }
        Plan::SuppressSmallGroups {
            input,
            min_k,
            distinct_by,
            mode,
        } => Plan::SuppressSmallGroups {
            input: Box::new(prune_core_plan_derives(input, None, stats)),
            min_k: min_k.clone(),
            distinct_by: distinct_by.clone(),
            mode: *mode,
        },
        Plan::Window { input, items } => Plan::Window {
            input: Box::new(prune_core_plan_derives(input, None, stats)),
            items: items.clone(),
        },
        Plan::FillGaps {
            input,
            col,
            step_micros,
            over,
            fill,
        } => Plan::FillGaps {
            input: Box::new(prune_core_plan_derives(input, None, stats)),
            col: col.clone(),
            step_micros: step_micros.clone(),
            over: over.clone(),
            fill: fill.clone(),
        },
        Plan::PivotWider {
            input,
            names_from,
            values_from,
            static_cols,
            fill,
        } => Plan::PivotWider {
            input: Box::new(prune_core_plan_derives(input, None, stats)),
            names_from: names_from.clone(),
            values_from: values_from.clone(),
            static_cols: static_cols.clone(),
            fill: fill.clone(),
        },
        Plan::Crosstab {
            input,
            rows_col,
            cols_col,
            values_col,
            fill,
        } => Plan::Crosstab {
            input: Box::new(prune_core_plan_derives(input, None, stats)),
            rows_col: rows_col.clone(),
            cols_col: cols_col.clone(),
            values_col: values_col.clone(),
            fill: fill.clone(),
        },
        Plan::Redact {
            input,
            col,
            replacement,
        } => Plan::Redact {
            input: Box::new(prune_core_plan_derives(input, None, stats)),
            col: col.clone(),
            replacement: replacement.clone(),
        },
        Plan::Pseudonymize { input, col, secret } => Plan::Pseudonymize {
            input: Box::new(prune_core_plan_derives(input, None, stats)),
            col: col.clone(),
            secret: Box::new((**secret).clone()),
        },
        other @ (Plan::SourceExpr(_) | Plan::SourceDB { .. }) => other.clone(),
    }
}

// ===========================================================================
// Phase 2 Execution IR Optimizer (`ExecPlan` / `ExecProgram`)
// ===========================================================================

/// Optimize every relational [`ExecPlan`] nested inside an [`ExecProgram`].
#[must_use]
pub fn optimize_exec_program(prog: &ExecProgram) -> (ExecProgram, OptStats) {
    let mut stats = OptStats::default();
    let funs = prog
        .funs
        .iter()
        .map(|f| ExecFun {
            body: optimize_exec_expr(&f.body, prog, &mut stats),
            ..f.clone()
        })
        .collect();
    (
        ExecProgram {
            funs,
            ..prog.clone()
        },
        stats,
    )
}

/// Optimize a single [`ExecPlan`] tree.
#[must_use]
pub fn optimize_exec_plan(plan: &ExecPlan, prog: &ExecProgram) -> (ExecPlan, OptStats) {
    let mut stats = OptStats::default();
    let p = optimize_exec_plan_inner(plan, prog, &mut stats);
    (p, stats)
}

fn optimize_exec_expr(expr: &ExecExpr, prog: &ExecProgram, stats: &mut OptStats) -> ExecExpr {
    match expr {
        ExecExpr::Lit(_) | ExecExpr::Var(_) | ExecExpr::ConstRef(_) | ExecExpr::TableLit { .. } => {
            expr.clone()
        }
        ExecExpr::LetE {
            name,
            lty,
            bound,
            body,
        } => ExecExpr::LetE {
            name: name.clone(),
            lty: lty.clone(),
            bound: Box::new(optimize_exec_expr(bound, prog, stats)),
            body: Box::new(optimize_exec_expr(body, prog, stats)),
        },
        ExecExpr::IfE {
            cond,
            then_br,
            else_br,
        } => ExecExpr::IfE {
            cond: Box::new(optimize_exec_expr(cond, prog, stats)),
            then_br: Box::new(optimize_exec_expr(then_br, prog, stats)),
            else_br: Box::new(optimize_exec_expr(else_br, prog, stats)),
        },
        ExecExpr::CaseE { scrut, arms } => ExecExpr::CaseE {
            scrut: Box::new(optimize_exec_expr(scrut, prog, stats)),
            arms: arms
                .iter()
                .map(|a| ExecCaseArm {
                    pattern: a.pattern.clone(),
                    body: optimize_exec_expr(&a.body, prog, stats),
                })
                .collect(),
        },
        ExecExpr::Lam {
            params,
            pc,
            ret,
            body,
        } => ExecExpr::Lam {
            params: params.clone(),
            pc: pc.clone(),
            ret: ret.clone(),
            body: Arc::new(optimize_exec_expr(body, prog, stats)),
        },
        ExecExpr::App { fn_expr, args } => ExecExpr::App {
            fn_expr: Box::new(optimize_exec_expr(fn_expr, prog, stats)),
            args: args
                .iter()
                .map(|a| optimize_exec_expr(a, prog, stats))
                .collect(),
        },
        ExecExpr::Call { fn_name, args } => ExecExpr::Call {
            fn_name: fn_name.clone(),
            args: args
                .iter()
                .map(|a| optimize_exec_expr(a, prog, stats))
                .collect(),
        },
        ExecExpr::Join {
            label,
            params,
            rhs,
            body,
        } => ExecExpr::Join {
            label: label.clone(),
            params: params.clone(),
            rhs: Box::new(optimize_exec_expr(rhs, prog, stats)),
            body: Box::new(optimize_exec_expr(body, prog, stats)),
        },
        ExecExpr::Jump { label, args } => ExecExpr::Jump {
            label: label.clone(),
            args: args
                .iter()
                .map(|a| optimize_exec_expr(a, prog, stats))
                .collect(),
        },
        ExecExpr::ForLoop {
            item_var,
            iter_expr,
            state_vars,
            body,
            after,
        } => ExecExpr::ForLoop {
            item_var: item_var.clone(),
            iter_expr: Box::new(optimize_exec_expr(iter_expr, prog, stats)),
            state_vars: state_vars.clone(),
            body: Box::new(optimize_exec_expr(body, prog, stats)),
            after: Box::new(optimize_exec_expr(after, prog, stats)),
        },
        ExecExpr::WhileLoop {
            cond,
            state_vars,
            body,
            after,
        } => ExecExpr::WhileLoop {
            cond: Box::new(optimize_exec_expr(cond, prog, stats)),
            state_vars: state_vars.clone(),
            body: Box::new(optimize_exec_expr(body, prog, stats)),
            after: Box::new(optimize_exec_expr(after, prog, stats)),
        },
        ExecExpr::Tuple(xs) => ExecExpr::Tuple(
            xs.iter()
                .map(|x| optimize_exec_expr(x, prog, stats))
                .collect(),
        ),
        ExecExpr::Proj { tup, idx } => ExecExpr::Proj {
            tup: Box::new(optimize_exec_expr(tup, prog, stats)),
            idx: idx.clone(),
        },
        ExecExpr::Ctor {
            type_name,
            ctor_name,
            args,
        } => ExecExpr::Ctor {
            type_name: type_name.clone(),
            ctor_name: ctor_name.clone(),
            args: args
                .iter()
                .map(|a| optimize_exec_expr(a, prog, stats))
                .collect(),
        },
        ExecExpr::Prim { op, args } => ExecExpr::Prim {
            op: op.clone(),
            args: args
                .iter()
                .map(|a| optimize_exec_expr(a, prog, stats))
                .collect(),
        },
        ExecExpr::Rel(plan) => ExecExpr::Rel(Box::new(optimize_exec_plan_inner(plan, prog, stats))),
        ExecExpr::Host { op, args } => ExecExpr::Host {
            op: op.clone(),
            args: args
                .iter()
                .map(|a| optimize_exec_expr(a, prog, stats))
                .collect(),
        },
        ExecExpr::Assert { cond, message } => ExecExpr::Assert {
            cond: Box::new(optimize_exec_expr(cond, prog, stats)),
            message: message.clone(),
        },
        ExecExpr::CheckPromise { ret_var, promise } => ExecExpr::CheckPromise {
            ret_var: ret_var.clone(),
            promise: match promise {
                ExecPromise::UniqueCols(c) => ExecPromise::UniqueCols(c.clone()),
                ExecPromise::AllRows(re) => ExecPromise::AllRows(re.clone()),
                ExecPromise::BoolExpr(e) => {
                    ExecPromise::BoolExpr(Box::new(optimize_exec_expr(e, prog, stats)))
                }
            },
        },
        ExecExpr::Stop {
            kind,
            detail,
            detail_tags,
        } => ExecExpr::Stop {
            kind: *kind,
            detail: detail
                .as_deref()
                .map(|d| Box::new(optimize_exec_expr(d, prog, stats))),
            detail_tags: detail_tags.clone(),
        },
        ExecExpr::Fail(e) => ExecExpr::Fail(Box::new(optimize_exec_expr(e, prog, stats))),
    }
}

#[must_use]
pub fn may_stop_exec_row_expr(re: &ExecRowExpr) -> bool {
    match re {
        ExecRowExpr::Lit(_)
        | ExecRowExpr::Col(_)
        | ExecRowExpr::OuterVar(_)
        | ExecRowExpr::ConstRef(_) => false,
        ExecRowExpr::CallPure { .. } => true,
        ExecRowExpr::IfE {
            cond,
            then_br,
            else_br,
        } => {
            may_stop_exec_row_expr(cond)
                || may_stop_exec_row_expr(then_br)
                || may_stop_exec_row_expr(else_br)
        }
        ExecRowExpr::Coalesce {
            opt_expr,
            default_expr,
        } => may_stop_exec_row_expr(opt_expr) || may_stop_exec_row_expr(default_expr),
        ExecRowExpr::Prim { op, args } => {
            exec_prim_op_may_stop(op) || args.iter().any(may_stop_exec_row_expr)
        }
    }
}

const fn exec_prim_op_may_stop(op: &ExecPrimOp) -> bool {
    match op {
        ExecPrimOp::Core(cop) => prim_op_may_stop(cop),
        ExecPrimOp::DivFloat
        | ExecPrimOp::AbsInt
        | ExecPrimOp::InTz
        | ExecPrimOp::DateInTz
        | ExecPrimOp::ListFirstBang
        | ExecPrimOp::TableFirstBang
        | ExecPrimOp::OptSubInt
        | ExecPrimOp::OptSubDec
        | ExecPrimOp::TableColSum(_)
        | ExecPrimOp::DateTruncUnit(_)
        | ExecPrimOp::DateTruncDuration
        | ExecPrimOp::ClampInt
        | ExecPrimOp::ClampFloat
        | ExecPrimOp::ClampDecimal
        | ExecPrimOp::RoundToFloat => true,
        _ => false,
    }
}

fn may_stop_exec_derive_item(item: &ExecDeriveItem) -> bool {
    match item {
        ExecDeriveItem::ColExpr { expr, .. } => may_stop_exec_row_expr(expr),
        ExecDeriveItem::BucketCol { .. } => false,
    }
}

fn exec_row_expr_cols(re: &ExecRowExpr, out: &mut HashSet<Ident>) {
    match re {
        ExecRowExpr::Col(c) => {
            out.insert(c.clone());
        }
        ExecRowExpr::Lit(_) | ExecRowExpr::OuterVar(_) | ExecRowExpr::ConstRef(_) => {}
        ExecRowExpr::Prim { args, .. } | ExecRowExpr::CallPure { args, .. } => {
            for a in args {
                exec_row_expr_cols(a, out);
            }
        }
        ExecRowExpr::IfE {
            cond,
            then_br,
            else_br,
        } => {
            exec_row_expr_cols(cond, out);
            exec_row_expr_cols(then_br, out);
            exec_row_expr_cols(else_br, out);
        }
        ExecRowExpr::Coalesce {
            opt_expr,
            default_expr,
        } => {
            exec_row_expr_cols(opt_expr, out);
            exec_row_expr_cols(default_expr, out);
        }
    }
}

fn subst_exec_row_expr_cols(re: &ExecRowExpr, map: &HashMap<String, String>) -> ExecRowExpr {
    match re {
        ExecRowExpr::Col(c) => ExecRowExpr::Col(map.get(c).cloned().unwrap_or_else(|| c.clone())),
        ExecRowExpr::Lit(l) => ExecRowExpr::Lit(l.clone()),
        ExecRowExpr::OuterVar(v) => ExecRowExpr::OuterVar(v.clone()),
        ExecRowExpr::ConstRef(c) => ExecRowExpr::ConstRef(c.clone()),
        ExecRowExpr::Prim { op, args } => ExecRowExpr::Prim {
            op: op.clone(),
            args: args
                .iter()
                .map(|a| subst_exec_row_expr_cols(a, map))
                .collect(),
        },
        ExecRowExpr::IfE {
            cond,
            then_br,
            else_br,
        } => ExecRowExpr::IfE {
            cond: Box::new(subst_exec_row_expr_cols(cond, map)),
            then_br: Box::new(subst_exec_row_expr_cols(then_br, map)),
            else_br: Box::new(subst_exec_row_expr_cols(else_br, map)),
        },
        ExecRowExpr::Coalesce {
            opt_expr,
            default_expr,
        } => ExecRowExpr::Coalesce {
            opt_expr: Box::new(subst_exec_row_expr_cols(opt_expr, map)),
            default_expr: Box::new(subst_exec_row_expr_cols(default_expr, map)),
        },
        ExecRowExpr::CallPure { fn_name, args } => ExecRowExpr::CallPure {
            fn_name: fn_name.clone(),
            args: args
                .iter()
                .map(|a| subst_exec_row_expr_cols(a, map))
                .collect(),
        },
    }
}

fn optimize_exec_plan_inner(plan: &ExecPlan, prog: &ExecProgram, stats: &mut OptStats) -> ExecPlan {
    let rewritten = rewrite_exec_plan(plan, prog, stats);
    prune_exec_plan_derives(&rewritten, None, stats)
}

fn rewrite_exec_plan(plan: &ExecPlan, prog: &ExecProgram, stats: &mut OptStats) -> ExecPlan {
    match plan {
        ExecPlan::SourceExpr(e) => {
            ExecPlan::SourceExpr(Box::new(optimize_exec_expr(e, prog, stats)))
        }
        ExecPlan::SourceDB {
            cap,
            table_name,
            schema,
        } => ExecPlan::SourceDB {
            cap: Box::new(optimize_exec_expr(cap, prog, stats)),
            table_name: table_name.clone(),
            schema: schema.clone(),
        },
        ExecPlan::Select { input, cols } => {
            let opt_in = rewrite_exec_plan(input, prog, stats);
            if let ExecPlan::Select {
                input: inner,
                cols: inner_cols,
            } = &opt_in
                && cols.iter().all(|c| inner_cols.contains(c))
            {
                stats.dead_ops_eliminated += 1;
                return ExecPlan::Select {
                    input: Box::new((**inner).clone()),
                    cols: cols.clone(),
                };
            }
            ExecPlan::Select {
                input: Box::new(opt_in),
                cols: cols.clone(),
            }
        }
        ExecPlan::Drop { input, cols } => {
            let opt_in = rewrite_exec_plan(input, prog, stats);
            if cols.is_empty() {
                stats.dead_ops_eliminated += 1;
                return opt_in;
            }
            ExecPlan::Drop {
                input: Box::new(opt_in),
                cols: cols.clone(),
            }
        }
        ExecPlan::Rename { input, pairs } => {
            let opt_in = rewrite_exec_plan(input, prog, stats);
            if pairs.is_empty() {
                stats.dead_ops_eliminated += 1;
                return opt_in;
            }
            ExecPlan::Rename {
                input: Box::new(opt_in),
                pairs: pairs.clone(),
            }
        }
        ExecPlan::Derive { input, items } => {
            let opt_in = rewrite_exec_plan(input, prog, stats);
            if items.is_empty() {
                stats.dead_ops_eliminated += 1;
                return opt_in;
            }
            ExecPlan::Derive {
                input: Box::new(opt_in),
                items: items.clone(),
            }
        }
        ExecPlan::Filter { input, pred } => {
            let opt_in = rewrite_exec_plan(input, prog, stats);
            push_or_fuse_exec_filter(&opt_in, pred.clone(), stats)
        }
        ExecPlan::Distinct { input, cols } => ExecPlan::Distinct {
            input: Box::new(rewrite_exec_plan(input, prog, stats)),
            cols: cols.clone(),
        },
        ExecPlan::Sort { input, keys } => {
            let opt_in = rewrite_exec_plan(input, prog, stats);
            if keys.is_empty() {
                stats.dead_ops_eliminated += 1;
                return opt_in;
            }
            ExecPlan::Sort {
                input: Box::new(opt_in),
                keys: keys.clone(),
            }
        }
        ExecPlan::Limit { input, n } => {
            let opt_in = rewrite_exec_plan(input, prog, stats);
            if let ExecPlan::Limit {
                input: inner,
                n: n_inner,
            } = &opt_in
            {
                stats.limits_folded += 1;
                let folded = if n <= n_inner {
                    n.clone()
                } else {
                    n_inner.clone()
                };
                return ExecPlan::Limit {
                    input: Box::new((**inner).clone()),
                    n: folded,
                };
            }
            ExecPlan::Limit {
                input: Box::new(opt_in),
                n: n.clone(),
            }
        }
        ExecPlan::Join {
            kind,
            left,
            right,
            on,
            suffixes,
        } => ExecPlan::Join {
            kind: *kind,
            left: Box::new(rewrite_exec_plan(left, prog, stats)),
            right: Box::new(rewrite_exec_plan(right, prog, stats)),
            on: on.clone(),
            suffixes: suffixes.clone(),
        },
        ExecPlan::Union { left, right } => ExecPlan::Union {
            left: Box::new(rewrite_exec_plan(left, prog, stats)),
            right: Box::new(rewrite_exec_plan(right, prog, stats)),
        },
        ExecPlan::GroupBy { input, keys } => ExecPlan::GroupBy {
            input: Box::new(rewrite_exec_plan(input, prog, stats)),
            keys: keys.clone(),
        },
        ExecPlan::Summarize {
            input,
            aggs,
            distinct_key,
        } => ExecPlan::Summarize {
            input: Box::new(rewrite_exec_plan(input, prog, stats)),
            aggs: aggs.clone(),
            distinct_key: distinct_key.clone(),
        },
        ExecPlan::SuppressSmallGroups {
            input,
            min_k,
            distinct_by,
            mode,
        } => ExecPlan::SuppressSmallGroups {
            input: Box::new(rewrite_exec_plan(input, prog, stats)),
            min_k: min_k.clone(),
            distinct_by: distinct_by.clone(),
            mode: *mode,
        },
        ExecPlan::Shuffle { input, seed } => ExecPlan::Shuffle {
            input: Box::new(rewrite_exec_plan(input, prog, stats)),
            seed: Box::new(optimize_exec_expr(seed, prog, stats)),
        },
        ExecPlan::SuppressSmallCells {
            input,
            by_cols,
            min_k,
            distinct_by,
        } => ExecPlan::SuppressSmallCells {
            input: Box::new(rewrite_exec_plan(input, prog, stats)),
            by_cols: by_cols.clone(),
            min_k: min_k.clone(),
            distinct_by: distinct_by.clone(),
        },
        ExecPlan::Window { input, items } => {
            let opt_in = rewrite_exec_plan(input, prog, stats);
            if items.is_empty() {
                stats.dead_ops_eliminated += 1;
                return opt_in;
            }
            ExecPlan::Window {
                input: Box::new(opt_in),
                items: items.clone(),
            }
        }
        ExecPlan::FillGaps {
            input,
            col,
            step_micros,
            over,
            fill,
        } => ExecPlan::FillGaps {
            input: Box::new(rewrite_exec_plan(input, prog, stats)),
            col: col.clone(),
            step_micros: step_micros.clone(),
            over: over.clone(),
            fill: fill.clone(),
        },
        ExecPlan::PivotWider {
            input,
            names_from,
            values_from,
            static_cols,
            fill,
        } => ExecPlan::PivotWider {
            input: Box::new(rewrite_exec_plan(input, prog, stats)),
            names_from: names_from.clone(),
            values_from: values_from.clone(),
            static_cols: static_cols.clone(),
            fill: fill.clone(),
        },
        ExecPlan::PivotLonger {
            input,
            cols,
            names_to,
            values_to,
            value_ty,
            value_tags,
        } => ExecPlan::PivotLonger {
            input: Box::new(rewrite_exec_plan(input, prog, stats)),
            cols: cols.clone(),
            names_to: names_to.clone(),
            values_to: values_to.clone(),
            value_ty: value_ty.clone(),
            value_tags: value_tags.clone(),
        },
        ExecPlan::Crosstab {
            input,
            rows_col,
            cols_col,
            values_col,
            fill,
        } => ExecPlan::Crosstab {
            input: Box::new(rewrite_exec_plan(input, prog, stats)),
            rows_col: rows_col.clone(),
            cols_col: cols_col.clone(),
            values_col: values_col.clone(),
            fill: fill.clone(),
        },
        ExecPlan::Redact {
            input,
            col,
            replacement,
        } => ExecPlan::Redact {
            input: Box::new(rewrite_exec_plan(input, prog, stats)),
            col: col.clone(),
            replacement: replacement.clone(),
        },
        ExecPlan::Pseudonymize { input, col, secret } => ExecPlan::Pseudonymize {
            input: Box::new(rewrite_exec_plan(input, prog, stats)),
            col: col.clone(),
            secret: Box::new(optimize_exec_expr(secret, prog, stats)),
        },
    }
}

fn push_or_fuse_exec_filter(input: &ExecPlan, pred: ExecRowExpr, stats: &mut OptStats) -> ExecPlan {
    if matches!(pred, ExecRowExpr::Lit(Literal::Bool(true)))
        && !matches!(input, ExecPlan::GroupBy { .. } | ExecPlan::Summarize { .. })
    {
        stats.dead_ops_eliminated += 1;
        return input.clone();
    }

    let pred_total = !may_stop_exec_row_expr(&pred);
    let mut pred_cols = HashSet::new();
    exec_row_expr_cols(&pred, &mut pred_cols);

    match input {
        ExecPlan::Filter {
            input: inner,
            pred: p1,
        } => {
            stats.filters_fused += 1;
            let fused = ExecRowExpr::IfE {
                cond: Box::new(p1.clone()),
                then_br: Box::new(pred),
                else_br: Box::new(ExecRowExpr::Lit(Literal::Bool(false))),
            };
            push_or_fuse_exec_filter(inner, fused, stats)
        }
        ExecPlan::Select { input: inner, cols }
            if !matches!(
                inner.as_ref(),
                ExecPlan::GroupBy { .. } | ExecPlan::Summarize { .. }
            ) =>
        {
            stats.predicates_pushed += 1;
            let pushed = push_or_fuse_exec_filter(inner, pred, stats);
            ExecPlan::Select {
                input: Box::new(pushed),
                cols: cols.clone(),
            }
        }
        ExecPlan::Drop { input: inner, cols }
            if !matches!(
                inner.as_ref(),
                ExecPlan::GroupBy { .. } | ExecPlan::Summarize { .. }
            ) =>
        {
            stats.predicates_pushed += 1;
            let pushed = push_or_fuse_exec_filter(inner, pred, stats);
            ExecPlan::Drop {
                input: Box::new(pushed),
                cols: cols.clone(),
            }
        }
        // `ExecPlan::Rename` stores `(old_name, new_name)`.
        ExecPlan::Rename {
            input: inner,
            pairs,
        } if !matches!(
            inner.as_ref(),
            ExecPlan::GroupBy { .. } | ExecPlan::Summarize { .. }
        ) =>
        {
            let mut rev_map: HashMap<String, String> = HashMap::with_capacity(pairs.len());
            let mut all_distinct_new = true;
            for (old_n, new_n) in pairs {
                if rev_map.insert(new_n.clone(), old_n.clone()).is_some() {
                    all_distinct_new = false;
                }
            }
            if all_distinct_new {
                stats.predicates_pushed += 1;
                let rewritten_pred = subst_exec_row_expr_cols(&pred, &rev_map);
                let pushed = push_or_fuse_exec_filter(inner, rewritten_pred, stats);
                ExecPlan::Rename {
                    input: Box::new(pushed),
                    pairs: pairs.clone(),
                }
            } else {
                ExecPlan::Filter {
                    input: Box::new(input.clone()),
                    pred,
                }
            }
        }
        ExecPlan::Derive {
            input: inner,
            items,
        } if !matches!(
            inner.as_ref(),
            ExecPlan::GroupBy { .. } | ExecPlan::Summarize { .. }
        ) && items.iter().all(|it| {
            let target = match it {
                ExecDeriveItem::ColExpr { name, .. } | ExecDeriveItem::BucketCol { name, .. } => {
                    name
                }
            };
            !pred_cols.contains(target) && !may_stop_exec_derive_item(it)
        }) =>
        {
            stats.predicates_pushed += 1;
            let pushed = push_or_fuse_exec_filter(inner, pred, stats);
            ExecPlan::Derive {
                input: Box::new(pushed),
                items: items.clone(),
            }
        }
        ExecPlan::Sort { input: inner, keys }
            if pred_total
                && !matches!(
                    inner.as_ref(),
                    ExecPlan::GroupBy { .. } | ExecPlan::Summarize { .. }
                ) =>
        {
            stats.predicates_pushed += 1;
            let pushed = push_or_fuse_exec_filter(inner, pred, stats);
            ExecPlan::Sort {
                input: Box::new(pushed),
                keys: keys.clone(),
            }
        }
        ExecPlan::Redact {
            input: inner,
            col,
            replacement,
        } if !pred_cols.contains(col)
            && !matches!(
                inner.as_ref(),
                ExecPlan::GroupBy { .. } | ExecPlan::Summarize { .. }
            ) =>
        {
            stats.predicates_pushed += 1;
            let pushed = push_or_fuse_exec_filter(inner, pred, stats);
            ExecPlan::Redact {
                input: Box::new(pushed),
                col: col.clone(),
                replacement: replacement.clone(),
            }
        }
        ExecPlan::Union { left, right }
            if pred_total
                && !matches!(
                    left.as_ref(),
                    ExecPlan::GroupBy { .. } | ExecPlan::Summarize { .. }
                )
                && !matches!(
                    right.as_ref(),
                    ExecPlan::GroupBy { .. } | ExecPlan::Summarize { .. }
                ) =>
        {
            stats.predicates_pushed += 1;
            let p_left = push_or_fuse_exec_filter(left, pred.clone(), stats);
            let p_right = push_or_fuse_exec_filter(right, pred, stats);
            ExecPlan::Union {
                left: Box::new(p_left),
                right: Box::new(p_right),
            }
        }
        other => ExecPlan::Filter {
            input: Box::new(other.clone()),
            pred,
        },
    }
}

fn prune_exec_plan_derives(
    plan: &ExecPlan,
    needed: Option<&HashSet<Ident>>,
    stats: &mut OptStats,
) -> ExecPlan {
    match plan {
        ExecPlan::Select { input, cols } => {
            let req: HashSet<Ident> = cols.iter().cloned().collect();
            ExecPlan::Select {
                input: Box::new(prune_exec_plan_derives(input, Some(&req), stats)),
                cols: cols.clone(),
            }
        }
        ExecPlan::Drop { input, cols } => {
            let opt_in = match needed {
                Some(req) => {
                    let mut child_req = req.clone();
                    for c in cols {
                        child_req.remove(c);
                    }
                    prune_exec_plan_derives(input, Some(&child_req), stats)
                }
                None => prune_exec_plan_derives(input, None, stats),
            };
            ExecPlan::Drop {
                input: Box::new(opt_in),
                cols: cols.clone(),
            }
        }
        ExecPlan::Rename { input, pairs } => {
            let opt_in = match needed {
                Some(req) => {
                    let child_req: HashSet<Ident> = req
                        .iter()
                        .map(|c| {
                            pairs
                                .iter()
                                .find(|(_, new_n)| new_n == c)
                                .map_or_else(|| c.clone(), |(old_n, _)| old_n.clone())
                        })
                        .collect();
                    prune_exec_plan_derives(input, Some(&child_req), stats)
                }
                None => prune_exec_plan_derives(input, None, stats),
            };
            ExecPlan::Rename {
                input: Box::new(opt_in),
                pairs: pairs.clone(),
            }
        }
        ExecPlan::Filter { input, pred } => {
            let opt_in = match needed {
                Some(req) => {
                    let mut child_req = req.clone();
                    exec_row_expr_cols(pred, &mut child_req);
                    prune_exec_plan_derives(input, Some(&child_req), stats)
                }
                None => prune_exec_plan_derives(input, None, stats),
            };
            ExecPlan::Filter {
                input: Box::new(opt_in),
                pred: pred.clone(),
            }
        }
        ExecPlan::Sort { input, keys } => {
            let opt_in = match needed {
                Some(req) => {
                    let mut child_req = req.clone();
                    for (k, _) in keys {
                        child_req.insert(k.clone());
                    }
                    prune_exec_plan_derives(input, Some(&child_req), stats)
                }
                None => prune_exec_plan_derives(input, None, stats),
            };
            ExecPlan::Sort {
                input: Box::new(opt_in),
                keys: keys.clone(),
            }
        }
        ExecPlan::Limit { input, n } => ExecPlan::Limit {
            input: Box::new(prune_exec_plan_derives(input, needed, stats)),
            n: n.clone(),
        },
        ExecPlan::Derive { input, items } => {
            let Some(req) = needed else {
                return ExecPlan::Derive {
                    input: Box::new(prune_exec_plan_derives(input, None, stats)),
                    items: items.clone(),
                };
            };
            let mut live = req.clone();
            let mut keep_flags = vec![false; items.len()];
            for (idx, it) in items.iter().enumerate().rev() {
                let target = match it {
                    ExecDeriveItem::ColExpr { name, .. }
                    | ExecDeriveItem::BucketCol { name, .. } => name,
                };
                if live.contains(target) || may_stop_exec_derive_item(it) {
                    keep_flags[idx] = true;
                    live.remove(target);
                    match it {
                        ExecDeriveItem::ColExpr { expr, .. } => exec_row_expr_cols(expr, &mut live),
                        ExecDeriveItem::BucketCol { source, .. } => {
                            live.insert(source.clone());
                        }
                    }
                } else {
                    stats.derive_items_pruned += 1;
                }
            }
            let kept: Vec<ExecDeriveItem> = items
                .iter()
                .zip(keep_flags)
                .filter(|(_, keep)| *keep)
                .map(|(it, _)| it.clone())
                .collect();
            let opt_in = prune_exec_plan_derives(input, Some(&live), stats);
            if kept.is_empty() {
                stats.dead_ops_eliminated += 1;
                opt_in
            } else {
                ExecPlan::Derive {
                    input: Box::new(opt_in),
                    items: kept,
                }
            }
        }
        ExecPlan::Summarize {
            input,
            aggs,
            distinct_key,
        } => {
            let mut req = HashSet::new();
            for a in aggs {
                if let Some(re) = &a.arg {
                    exec_row_expr_cols(re, &mut req);
                }
            }
            if let Some(dk) = distinct_key {
                req.insert(dk.clone());
            }
            let opt_in = match input.as_ref() {
                ExecPlan::GroupBy {
                    input: gb_in,
                    keys: gb_keys,
                } => {
                    for k in gb_keys {
                        req.insert(k.clone());
                    }
                    ExecPlan::GroupBy {
                        input: Box::new(prune_exec_plan_derives(gb_in, Some(&req), stats)),
                        keys: gb_keys.clone(),
                    }
                }
                other => prune_exec_plan_derives(other, Some(&req), stats),
            };
            ExecPlan::Summarize {
                input: Box::new(opt_in),
                aggs: aggs.clone(),
                distinct_key: distinct_key.clone(),
            }
        }
        ExecPlan::Union { left, right } => ExecPlan::Union {
            left: Box::new(prune_exec_plan_derives(left, needed, stats)),
            right: Box::new(prune_exec_plan_derives(right, needed, stats)),
        },
        ExecPlan::Join {
            kind,
            left,
            right,
            on,
            suffixes,
        } => ExecPlan::Join {
            kind: *kind,
            left: Box::new(prune_exec_plan_derives(left, None, stats)),
            right: Box::new(prune_exec_plan_derives(right, None, stats)),
            on: on.clone(),
            suffixes: suffixes.clone(),
        },
        ExecPlan::Distinct { input, cols } => ExecPlan::Distinct {
            input: Box::new(prune_exec_plan_derives(input, None, stats)),
            cols: cols.clone(),
        },
        ExecPlan::GroupBy { input, keys } => ExecPlan::GroupBy {
            input: Box::new(prune_exec_plan_derives(input, None, stats)),
            keys: keys.clone(),
        },
        ExecPlan::SuppressSmallGroups {
            input,
            min_k,
            distinct_by,
            mode,
        } => ExecPlan::SuppressSmallGroups {
            input: Box::new(prune_exec_plan_derives(input, None, stats)),
            min_k: min_k.clone(),
            distinct_by: distinct_by.clone(),
            mode: *mode,
        },
        ExecPlan::Shuffle { input, seed } => ExecPlan::Shuffle {
            input: Box::new(prune_exec_plan_derives(input, needed, stats)),
            seed: Box::new((**seed).clone()),
        },
        ExecPlan::SuppressSmallCells {
            input,
            by_cols,
            min_k,
            distinct_by,
        } => ExecPlan::SuppressSmallCells {
            input: Box::new(prune_exec_plan_derives(input, None, stats)),
            by_cols: by_cols.clone(),
            min_k: min_k.clone(),
            distinct_by: distinct_by.clone(),
        },
        ExecPlan::Window { input, items } => ExecPlan::Window {
            input: Box::new(prune_exec_plan_derives(input, None, stats)),
            items: items.clone(),
        },
        ExecPlan::FillGaps {
            input,
            col,
            step_micros,
            over,
            fill,
        } => ExecPlan::FillGaps {
            input: Box::new(prune_exec_plan_derives(input, None, stats)),
            col: col.clone(),
            step_micros: step_micros.clone(),
            over: over.clone(),
            fill: fill.clone(),
        },
        ExecPlan::PivotWider {
            input,
            names_from,
            values_from,
            static_cols,
            fill,
        } => ExecPlan::PivotWider {
            input: Box::new(prune_exec_plan_derives(input, None, stats)),
            names_from: names_from.clone(),
            values_from: values_from.clone(),
            static_cols: static_cols.clone(),
            fill: fill.clone(),
        },
        ExecPlan::PivotLonger {
            input,
            cols,
            names_to,
            values_to,
            value_ty,
            value_tags,
        } => ExecPlan::PivotLonger {
            input: Box::new(prune_exec_plan_derives(input, None, stats)),
            cols: cols.clone(),
            names_to: names_to.clone(),
            values_to: values_to.clone(),
            value_ty: value_ty.clone(),
            value_tags: value_tags.clone(),
        },
        ExecPlan::Crosstab {
            input,
            rows_col,
            cols_col,
            values_col,
            fill,
        } => ExecPlan::Crosstab {
            input: Box::new(prune_exec_plan_derives(input, None, stats)),
            rows_col: rows_col.clone(),
            cols_col: cols_col.clone(),
            values_col: values_col.clone(),
            fill: fill.clone(),
        },
        ExecPlan::Redact {
            input,
            col,
            replacement,
        } => ExecPlan::Redact {
            input: Box::new(prune_exec_plan_derives(input, None, stats)),
            col: col.clone(),
            replacement: replacement.clone(),
        },
        ExecPlan::Pseudonymize { input, col, secret } => ExecPlan::Pseudonymize {
            input: Box::new(prune_exec_plan_derives(input, None, stats)),
            col: col.clone(),
            secret: Box::new((**secret).clone()),
        },
        other @ (ExecPlan::SourceExpr(_) | ExecPlan::SourceDB { .. }) => other.clone(),
    }
}
