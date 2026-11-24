//! Human-readable tree formatting for logical and optimized Dana relational plans.

use std::fmt::Write;

use crate::core::syntax::{DeriveItem, JoinOn, Plan};
use crate::runtime::ir::{ExecDeriveItem, ExecPlan};

/// Render a Core IR [`Plan`] as an indented execution tree.
#[must_use]
pub fn explain_plan(plan: &Plan) -> String {
    let mut out = String::new();
    fmt_core_plan(plan, 0, &mut out);
    out
}

/// Render a Phase 2 [`ExecPlan`] as an indented execution tree.
#[must_use]
pub fn explain_exec_plan(plan: &ExecPlan) -> String {
    let mut out = String::new();
    fmt_exec_plan(plan, 0, &mut out);
    out
}

fn indent(depth: usize, out: &mut String) {
    for _ in 0..depth {
        out.push_str("  ");
    }
}

fn fmt_join_on(on: &JoinOn) -> String {
    match on {
        JoinOn::SameKeys(ks) => ks.join(", "),
        JoinOn::Pairs(ps) => ps
            .iter()
            .map(|(l, r)| format!("{l}={r}"))
            .collect::<Vec<_>>()
            .join(", "),
    }
}

fn fmt_core_plan(plan: &Plan, depth: usize, out: &mut String) {
    indent(depth, out);
    match plan {
        Plan::SourceExpr(_) => {
            let _ = writeln!(out, "SourceExpr");
        }
        Plan::SourceDB { table_name, .. } => {
            let _ = writeln!(out, "SourceDB({table_name})");
        }
        Plan::Select { input, cols } => {
            let _ = writeln!(out, "Select([{}])", cols.join(", "));
            fmt_core_plan(input, depth + 1, out);
        }
        Plan::Drop { input, cols } => {
            let _ = writeln!(out, "Drop([{}])", cols.join(", "));
            fmt_core_plan(input, depth + 1, out);
        }
        Plan::Rename { input, pairs } => {
            let ps: Vec<String> = pairs.iter().map(|(n, o)| format!("{n}<-{o}")).collect();
            let _ = writeln!(out, "Rename([{}])", ps.join(", "));
            fmt_core_plan(input, depth + 1, out);
        }
        Plan::Derive { input, items } => {
            let names: Vec<&str> = items
                .iter()
                .map(|it| match it {
                    DeriveItem::ColExpr { name, .. } | DeriveItem::BucketCol { name, .. } => {
                        name.as_str()
                    }
                })
                .collect();
            let _ = writeln!(out, "Derive([{}])", names.join(", "));
            fmt_core_plan(input, depth + 1, out);
        }
        Plan::Filter { input, .. } => {
            let _ = writeln!(out, "Filter");
            fmt_core_plan(input, depth + 1, out);
        }
        Plan::Distinct { input, cols } => {
            let _ = writeln!(out, "Distinct([{}])", cols.join(", "));
            fmt_core_plan(input, depth + 1, out);
        }
        Plan::Sort { input, keys } => {
            let ks: Vec<String> = keys.iter().map(|(k, d)| format!("{k}:{d:?}")).collect();
            let _ = writeln!(out, "Sort([{}])", ks.join(", "));
            fmt_core_plan(input, depth + 1, out);
        }
        Plan::Limit { input, n } => {
            let _ = writeln!(out, "Limit({n})");
            fmt_core_plan(input, depth + 1, out);
        }
        Plan::Join {
            kind,
            left,
            right,
            on,
            ..
        } => {
            let _ = writeln!(out, "HashJoin({kind:?}, on=[{}])", fmt_join_on(on));
            fmt_core_plan(left, depth + 1, out);
            fmt_core_plan(right, depth + 1, out);
        }
        Plan::Union { left, right } => {
            let _ = writeln!(out, "Union");
            fmt_core_plan(left, depth + 1, out);
            fmt_core_plan(right, depth + 1, out);
        }
        Plan::GroupBy { input, keys } => {
            let _ = writeln!(out, "GroupBy([{}])", keys.join(", "));
            fmt_core_plan(input, depth + 1, out);
        }
        Plan::Summarize { input, aggs, .. } => {
            let names: Vec<String> = aggs
                .iter()
                .map(|a| format!("{}:{:?}", a.name, a.op))
                .collect();
            let _ = writeln!(out, "HashAggregate([{}])", names.join(", "));
            fmt_core_plan(input, depth + 1, out);
        }
        Plan::SuppressSmallGroups {
            input, min_k, mode, ..
        } => {
            let _ = writeln!(out, "SuppressSmallGroups(min={min_k}, mode={mode:?})");
            fmt_core_plan(input, depth + 1, out);
        }
        Plan::Window { input, items } => {
            let names: Vec<&str> = items.iter().map(|i| i.name.as_str()).collect();
            let _ = writeln!(out, "Window([{}])", names.join(", "));
            fmt_core_plan(input, depth + 1, out);
        }
        Plan::FillGaps { input, col, .. } => {
            let _ = writeln!(out, "FillGaps({col})");
            fmt_core_plan(input, depth + 1, out);
        }
        Plan::PivotWider {
            input,
            names_from,
            values_from,
            ..
        } => {
            let _ = writeln!(out, "PivotWider({names_from} -> {values_from})");
            fmt_core_plan(input, depth + 1, out);
        }
        Plan::Crosstab {
            input,
            rows_col,
            cols_col,
            values_col,
            ..
        } => {
            let _ = writeln!(out, "Crosstab({rows_col} x {cols_col} = {values_col})");
            fmt_core_plan(input, depth + 1, out);
        }
        Plan::Redact { input, col, .. } => {
            let _ = writeln!(out, "Redact({col})");
            fmt_core_plan(input, depth + 1, out);
        }
        Plan::Pseudonymize { input, col, .. } => {
            let _ = writeln!(out, "Pseudonymize({col})");
            fmt_core_plan(input, depth + 1, out);
        }
    }
}

fn fmt_exec_plan(plan: &ExecPlan, depth: usize, out: &mut String) {
    indent(depth, out);
    match plan {
        ExecPlan::SourceExpr(_) => {
            let _ = writeln!(out, "SourceExpr");
        }
        ExecPlan::SourceDB { table_name, .. } => {
            let _ = writeln!(out, "SourceDB({table_name})");
        }
        ExecPlan::Select { input, cols } => {
            let _ = writeln!(out, "Select([{}])", cols.join(", "));
            fmt_exec_plan(input, depth + 1, out);
        }
        ExecPlan::Drop { input, cols } => {
            let _ = writeln!(out, "Drop([{}])", cols.join(", "));
            fmt_exec_plan(input, depth + 1, out);
        }
        ExecPlan::Rename { input, pairs } => {
            let ps: Vec<String> = pairs.iter().map(|(o, n)| format!("{n}<-{o}")).collect();
            let _ = writeln!(out, "Rename([{}])", ps.join(", "));
            fmt_exec_plan(input, depth + 1, out);
        }
        ExecPlan::Derive { input, items } => {
            let names: Vec<&str> = items
                .iter()
                .map(|it| match it {
                    ExecDeriveItem::ColExpr { name, .. }
                    | ExecDeriveItem::BucketCol { name, .. } => name.as_str(),
                })
                .collect();
            let _ = writeln!(out, "Derive([{}])", names.join(", "));
            fmt_exec_plan(input, depth + 1, out);
        }
        ExecPlan::Filter { input, .. } => {
            let _ = writeln!(out, "Filter");
            fmt_exec_plan(input, depth + 1, out);
        }
        ExecPlan::Distinct { input, cols } => {
            let _ = writeln!(out, "Distinct([{}])", cols.join(", "));
            fmt_exec_plan(input, depth + 1, out);
        }
        ExecPlan::Sort { input, keys } => {
            let ks: Vec<String> = keys.iter().map(|(k, d)| format!("{k}:{d:?}")).collect();
            let _ = writeln!(out, "Sort([{}])", ks.join(", "));
            fmt_exec_plan(input, depth + 1, out);
        }
        ExecPlan::Limit { input, n } => {
            let _ = writeln!(out, "Limit({n})");
            fmt_exec_plan(input, depth + 1, out);
        }
        ExecPlan::Join {
            kind,
            left,
            right,
            on,
            ..
        } => {
            let _ = writeln!(out, "HashJoin({kind:?}, on=[{}])", fmt_join_on(on));
            fmt_exec_plan(left, depth + 1, out);
            fmt_exec_plan(right, depth + 1, out);
        }
        ExecPlan::Union { left, right } => {
            let _ = writeln!(out, "Union");
            fmt_exec_plan(left, depth + 1, out);
            fmt_exec_plan(right, depth + 1, out);
        }
        ExecPlan::GroupBy { input, keys } => {
            let _ = writeln!(out, "GroupBy([{}])", keys.join(", "));
            fmt_exec_plan(input, depth + 1, out);
        }
        ExecPlan::Summarize { input, aggs, .. } => {
            let names: Vec<String> = aggs
                .iter()
                .map(|a| format!("{}:{:?}", a.name, a.op))
                .collect();
            let _ = writeln!(out, "HashAggregate([{}])", names.join(", "));
            fmt_exec_plan(input, depth + 1, out);
        }
        ExecPlan::SuppressSmallGroups {
            input, min_k, mode, ..
        } => {
            let _ = writeln!(out, "SuppressSmallGroups(min={min_k}, mode={mode:?})");
            fmt_exec_plan(input, depth + 1, out);
        }
        ExecPlan::Window { input, items } => {
            let names: Vec<&str> = items.iter().map(|i| i.name.as_str()).collect();
            let _ = writeln!(out, "Window([{}])", names.join(", "));
            fmt_exec_plan(input, depth + 1, out);
        }
        ExecPlan::FillGaps { input, col, .. } => {
            let _ = writeln!(out, "FillGaps({col})");
            fmt_exec_plan(input, depth + 1, out);
        }
        ExecPlan::PivotWider {
            input,
            names_from,
            values_from,
            ..
        } => {
            let _ = writeln!(out, "PivotWider({names_from} -> {values_from})");
            fmt_exec_plan(input, depth + 1, out);
        }
        ExecPlan::Crosstab {
            input,
            rows_col,
            cols_col,
            values_col,
            ..
        } => {
            let _ = writeln!(out, "Crosstab({rows_col} x {cols_col} = {values_col})");
            fmt_exec_plan(input, depth + 1, out);
        }
        ExecPlan::Redact { input, col, .. } => {
            let _ = writeln!(out, "Redact({col})");
            fmt_exec_plan(input, depth + 1, out);
        }
        ExecPlan::Pseudonymize { input, col, .. } => {
            let _ = writeln!(out, "Pseudonymize({col})");
            fmt_exec_plan(input, depth + 1, out);
        }
    }
}
