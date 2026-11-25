//! Human-readable tree formatting, SQL pushdown visualization, and sensitivity-tag
//! provenance tracing for logical and optimized Dana relational plans.

use std::collections::HashMap;
use std::fmt::Write;

use crate::core::check::{
    apply_window_item, build_joined_cols, ensure_option_scalar, merge_union_cols,
    resolve_join_pairs,
};
use crate::core::syntax::{
    AggItem, AggKind, ColSpec, DeriveItem, Expr, Ident, JoinKind, JoinOn, Plan, Program, RowExpr,
    ScalarTy, SuppressMode, TableTy, TagSet, Ty,
};
use crate::db::SqlDialect;
use crate::db::schema_lock::SchemaLockFile;
use crate::plan::opt::{optimize_exec_plan, optimize_plan};
use crate::plan::pushdown::{
    SplitPlan, SqlPushdownQuery, collect_core_plan_pushdowns, collect_exec_plan_pushdowns,
    split_core_plan_pushdown, split_exec_plan_pushdown,
};
use crate::runtime::ir::{
    ExecAggItem, ExecDeriveItem, ExecExpr, ExecPlan, ExecProgram, ExecRowExpr,
};

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

/// Render a full explain report for a Core IR [`Plan`] including:
/// - `[LOGICAL PLAN]`
/// - `[OPTIMIZED PLAN]`
/// - `[SQL PUSHDOWN -> sqlite|postgres]` with parameterized SQL + parameter slot table
/// - `[PUSHDOWN BOUNDARY: ...]` and `[LOCAL VM SUFFIX]`
/// - `[SENSITIVITY PROVENANCE]` tracing where tags enter, propagate, clear, or remain.
#[must_use]
pub fn explain_core_plan_with_pushdown(
    plan: &Plan,
    prog: &Program,
    db_name: &str,
    dialect: SqlDialect,
    lock: Option<&SchemaLockFile>,
) -> String {
    let (opt, stats) = optimize_plan(plan, prog);
    let split = split_core_plan_pushdown(&opt, prog, db_name, dialect, lock);

    let mut out = String::new();
    let _ = writeln!(out, "[LOGICAL PLAN]");
    fmt_core_plan(plan, 1, &mut out);
    let _ = writeln!(
        out,
        "[OPTIMIZED PLAN] (fused={}, pushed={}, pruned={}, dead={}, limits={})",
        stats.filters_fused,
        stats.predicates_pushed,
        stats.derive_items_pruned,
        stats.dead_ops_eliminated,
        stats.limits_folded
    );
    fmt_core_plan(&opt, 1, &mut out);

    match &split {
        SplitPlan::FullyPushed(q) => {
            fmt_pushdown_query(q, None, &mut out);
            let _ = writeln!(out, "[LOCAL VM SUFFIX]");
            let _ = writeln!(out, "  (none — fully pushed to {})", q.dialect);
        }
        SplitPlan::Hybrid {
            pushdown,
            placeholder_var,
            local_suffix,
        } => {
            let collected = collect_core_plan_pushdowns(&opt, prog, dialect, lock);
            if collected.branches.len() > 1 {
                for br in &collected.branches {
                    fmt_pushdown_query(&br.pushdown, Some(&br.placeholder_var), &mut out);
                }
                if let Some(reason) = &pushdown.boundary_reason {
                    let _ = writeln!(out, "[PUSHDOWN BOUNDARY: {reason}]");
                }
                let _ = writeln!(out, "[LOCAL VM SUFFIX]");
                fmt_core_plan(&collected.local_plan, 1, &mut out);
            } else {
                fmt_pushdown_query(pushdown, Some(placeholder_var), &mut out);
                if let Some(reason) = &pushdown.boundary_reason {
                    let _ = writeln!(out, "[PUSHDOWN BOUNDARY: {reason}]");
                }
                let _ = writeln!(out, "[LOCAL VM SUFFIX]");
                fmt_core_plan(local_suffix, 1, &mut out);
            }
        }
        SplitPlan::LocalOnly { plan: _, reason } => {
            let collected = collect_core_plan_pushdowns(&opt, prog, dialect, lock);
            if collected.branches.is_empty() {
                let _ = writeln!(out, "[PUSHDOWN BOUNDARY: {reason}]");
                let _ = writeln!(out, "[LOCAL VM SUFFIX]");
                fmt_core_plan(&opt, 1, &mut out);
            } else {
                for br in &collected.branches {
                    fmt_pushdown_query(&br.pushdown, Some(&br.placeholder_var), &mut out);
                }
                let _ = writeln!(out, "[PUSHDOWN BOUNDARY: {reason}]");
                let _ = writeln!(out, "[LOCAL VM SUFFIX]");
                fmt_core_plan(&collected.local_plan, 1, &mut out);
            }
        }
    }

    let _ = writeln!(out, "[SENSITIVITY PROVENANCE]");
    let prov = explain_sensitivity_provenance(&opt, prog);
    out.push_str(&prov);
    out
}

/// Render a full explain report for a Phase 2 [`ExecPlan`] including:
/// - `[LOGICAL PLAN]`
/// - `[OPTIMIZED PLAN]`
/// - `[SQL PUSHDOWN -> sqlite|postgres]` with parameterized SQL + parameter slot table
/// - `[PUSHDOWN BOUNDARY: ...]` and `[LOCAL VM SUFFIX]`
/// - `[SENSITIVITY PROVENANCE]` tracing where tags enter, propagate, clear, or remain.
#[must_use]
pub fn explain_exec_plan_with_pushdown(
    plan: &ExecPlan,
    prog: &ExecProgram,
    db_name: &str,
    dialect: SqlDialect,
    lock: Option<&SchemaLockFile>,
) -> String {
    let (opt, stats) = optimize_exec_plan(plan, prog);
    let split = split_exec_plan_pushdown(&opt, prog, db_name, dialect, lock);

    let mut out = String::new();
    let _ = writeln!(out, "[LOGICAL PLAN]");
    fmt_exec_plan(plan, 1, &mut out);
    let _ = writeln!(
        out,
        "[OPTIMIZED PLAN] (fused={}, pushed={}, pruned={}, dead={}, limits={})",
        stats.filters_fused,
        stats.predicates_pushed,
        stats.derive_items_pruned,
        stats.dead_ops_eliminated,
        stats.limits_folded
    );
    fmt_exec_plan(&opt, 1, &mut out);

    match &split {
        SplitPlan::FullyPushed(q) => {
            fmt_pushdown_query(q, None, &mut out);
            let _ = writeln!(out, "[LOCAL VM SUFFIX]");
            let _ = writeln!(out, "  (none — fully pushed to {})", q.dialect);
        }
        SplitPlan::Hybrid {
            pushdown,
            placeholder_var,
            local_suffix,
        } => {
            let collected = collect_exec_plan_pushdowns(&opt, prog, dialect, lock);
            if collected.branches.len() > 1 {
                for br in &collected.branches {
                    fmt_pushdown_query(&br.pushdown, Some(&br.placeholder_var), &mut out);
                }
                if let Some(reason) = &pushdown.boundary_reason {
                    let _ = writeln!(out, "[PUSHDOWN BOUNDARY: {reason}]");
                }
                let _ = writeln!(out, "[LOCAL VM SUFFIX]");
                fmt_exec_plan(&collected.local_plan, 1, &mut out);
            } else {
                fmt_pushdown_query(pushdown, Some(placeholder_var), &mut out);
                if let Some(reason) = &pushdown.boundary_reason {
                    let _ = writeln!(out, "[PUSHDOWN BOUNDARY: {reason}]");
                }
                let _ = writeln!(out, "[LOCAL VM SUFFIX]");
                fmt_exec_plan(local_suffix, 1, &mut out);
            }
        }
        SplitPlan::LocalOnly { plan: _, reason } => {
            let collected = collect_exec_plan_pushdowns(&opt, prog, dialect, lock);
            if collected.branches.is_empty() {
                let _ = writeln!(out, "[PUSHDOWN BOUNDARY: {reason}]");
                let _ = writeln!(out, "[LOCAL VM SUFFIX]");
                fmt_exec_plan(&opt, 1, &mut out);
            } else {
                for br in &collected.branches {
                    fmt_pushdown_query(&br.pushdown, Some(&br.placeholder_var), &mut out);
                }
                let _ = writeln!(out, "[PUSHDOWN BOUNDARY: {reason}]");
                let _ = writeln!(out, "[LOCAL VM SUFFIX]");
                fmt_exec_plan(&collected.local_plan, 1, &mut out);
            }
        }
    }

    let _ = writeln!(out, "[SENSITIVITY PROVENANCE]");
    let prov = explain_exec_sensitivity_provenance(&opt, prog);
    out.push_str(&prov);
    out
}

/// Trace where sensitivity tags enter, propagate, clear, or remain across a Core IR [`Plan`].
#[must_use]
pub fn explain_sensitivity_provenance(plan: &Plan, prog: &Program) -> String {
    let mut var_tags: HashMap<Ident, TagSet> = HashMap::new();
    let mut table_vars: HashMap<Ident, TableTy> = HashMap::new();
    for f in &prog.funs {
        for (name, lty) in &f.params {
            if let Ty::Table(tt) = &lty.ty {
                table_vars.insert(name.clone(), tt.clone());
            } else {
                var_tags.insert(name.clone(), lty.effective_tags());
            }
        }
    }
    let mut lines = Vec::new();
    let out_tt = trace_core_provenance(plan, prog, &var_tags, &table_vars, &mut lines);
    fmt_provenance_summary(&lines, out_tt.as_ref())
}

/// Trace where sensitivity tags enter, propagate, clear, or remain across a Phase 2 [`ExecPlan`].
#[must_use]
pub fn explain_exec_sensitivity_provenance(plan: &ExecPlan, prog: &ExecProgram) -> String {
    let mut var_tags: HashMap<Ident, TagSet> = HashMap::new();
    let mut table_vars: HashMap<Ident, TableTy> = HashMap::new();
    for f in &prog.funs {
        for (name, lty) in &f.params {
            if let Ty::Table(tt) = &lty.ty {
                table_vars.insert(name.clone(), tt.clone());
            } else {
                var_tags.insert(name.clone(), lty.effective_tags());
            }
        }
    }
    let mut lines = Vec::new();
    let out_tt = trace_exec_provenance(plan, prog, &var_tags, &table_vars, &mut lines);
    fmt_provenance_summary(&lines, out_tt.as_ref())
}

fn fmt_pushdown_query(q: &SqlPushdownQuery, bind_var: Option<&str>, out: &mut String) {
    match bind_var {
        Some(v) => {
            let _ = writeln!(
                out,
                "[SQL PUSHDOWN -> {}] (db={}, bind={}, ops=[{}])",
                q.dialect,
                q.db_name,
                v,
                q.pushed_ops.join(" -> ")
            );
        }
        None => {
            let _ = writeln!(
                out,
                "[SQL PUSHDOWN -> {}] (db={}, ops=[{}])",
                q.dialect,
                q.db_name,
                q.pushed_ops.join(" -> ")
            );
        }
    }
    let _ = writeln!(out, "  {}", q.sql);
    if q.param_slots.is_empty() {
        let _ = writeln!(out, "[PARAMETERS] (none)");
    } else {
        let _ = writeln!(out, "[PARAMETERS]");
        for (i, slot) in q.param_slots.iter().enumerate() {
            let ph = match q.dialect {
                SqlDialect::Sqlite => format!("?{}", i + 1),
                SqlDialect::Postgres => format!("${}", i + 1),
            };
            let _ = writeln!(out, "  {ph} = {}", slot.describe());
        }
    }
}

fn fmt_tags(ts: &TagSet) -> String {
    if ts.is_empty() {
        "[]".to_string()
    } else {
        format!("[{}]", ts.elems().join(", "))
    }
}

fn fmt_tagged_cols(cols: &[ColSpec]) -> String {
    let tagged: Vec<String> = cols
        .iter()
        .filter(|c| !c.tags.is_empty())
        .map(|c| format!("{}:{}", c.name, fmt_tags(&c.tags)))
        .collect();
    if tagged.is_empty() {
        "[]".to_string()
    } else {
        format!("[{}]", tagged.join(", "))
    }
}

fn fmt_provenance_summary(lines: &[String], out_tt: Option<&TableTy>) -> String {
    let mut out = String::new();
    for line in lines {
        let _ = writeln!(out, "  {line}");
    }
    match out_tt {
        Some(tt) => {
            let remaining = tt.total_tags();
            if remaining.is_empty() {
                let _ = writeln!(out, "  OUTPUT: PUBLIC (no sensitivity tags remaining)");
            } else {
                let _ = writeln!(
                    out,
                    "  OUTPUT: SENSITIVE {} (row_tags={}, order_tags={}, tagged_cols={})",
                    fmt_tags(&remaining),
                    fmt_tags(&tt.row_tags),
                    fmt_tags(&tt.order_tags),
                    fmt_tagged_cols(&tt.cols)
                );
            }
        }
        None => {
            let _ = writeln!(out, "  OUTPUT: (dynamic or unresolved table schema)");
        }
    }
    out
}

// ===========================================================================
// Core IR Sensitivity Provenance Tracer
// ===========================================================================

fn core_row_expr_tags(
    re: &RowExpr,
    cols: &[ColSpec],
    prog: &Program,
    var_tags: &HashMap<Ident, TagSet>,
) -> TagSet {
    match re {
        RowExpr::Lit(_) => TagSet::empty(),
        RowExpr::Col(c) => cols
            .iter()
            .find(|cs| cs.name == *c)
            .map(|cs| cs.tags.clone())
            .unwrap_or_default(),
        RowExpr::OuterVar(v) => var_tags.get(v).cloned().unwrap_or_default(),
        RowExpr::ConstRef(c) => prog
            .find_const(c)
            .map(|d| d.lty.effective_tags())
            .unwrap_or_default(),
        RowExpr::Prim { args, .. } | RowExpr::CallPure { args, .. } => {
            let mut acc = TagSet::empty();
            for a in args {
                acc = acc.union(&core_row_expr_tags(a, cols, prog, var_tags));
            }
            acc
        }
        RowExpr::IfE {
            cond,
            then_br,
            else_br,
        } => core_row_expr_tags(cond, cols, prog, var_tags)
            .union(&core_row_expr_tags(then_br, cols, prog, var_tags))
            .union(&core_row_expr_tags(else_br, cols, prog, var_tags)),
        RowExpr::Coalesce {
            opt_expr,
            default_expr,
        } => core_row_expr_tags(opt_expr, cols, prog, var_tags).union(&core_row_expr_tags(
            default_expr,
            cols,
            prog,
            var_tags,
        )),
    }
}

fn trace_core_provenance(
    plan: &Plan,
    prog: &Program,
    var_tags: &HashMap<Ident, TagSet>,
    table_vars: &HashMap<Ident, TableTy>,
    lines: &mut Vec<String>,
) -> Option<TableTy> {
    match plan {
        Plan::SourceDB {
            table_name, schema, ..
        } => {
            let total = schema.total_tags();
            lines.push(format!(
                "ENTER SourceDB({table_name}): tags={}, cols={}, row_tags={}",
                fmt_tags(&total),
                fmt_tagged_cols(&schema.cols),
                fmt_tags(&schema.row_tags)
            ));
            Some(schema.clone())
        }
        Plan::SourceExpr(e) => match e.as_ref() {
            Expr::TableLit { schema, .. } => {
                lines.push(format!(
                    "ENTER TableLit: tags={}, cols={}",
                    fmt_tags(&schema.total_tags()),
                    fmt_tagged_cols(&schema.cols)
                ));
                Some(schema.clone())
            }
            Expr::Var(v) => {
                let tt = table_vars.get(v).cloned();
                if let Some(ref schema) = tt {
                    lines.push(format!(
                        "ENTER SourceVar({v}): tags={}, cols={}",
                        fmt_tags(&schema.total_tags()),
                        fmt_tagged_cols(&schema.cols)
                    ));
                }
                tt
            }
            _ => None,
        },
        Plan::Select { input, cols } => {
            let tt = trace_core_provenance(input, prog, var_tags, table_vars, lines)?;
            let dropped: Vec<String> = tt
                .cols
                .iter()
                .filter(|c| !cols.contains(&c.name) && !c.tags.is_empty())
                .map(|c| format!("{}:{}", c.name, fmt_tags(&c.tags)))
                .collect();
            if !dropped.is_empty() {
                lines.push(format!(
                    "DROP_COL Select([{}]): removed tagged cols [{}]",
                    cols.join(", "),
                    dropped.join(", ")
                ));
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
            Some(TableTy {
                cols: out_cols,
                row_tags: tt.row_tags,
                order_tags: tt.order_tags,
                ..TableTy::default()
            })
        }
        Plan::Drop { input, cols } => {
            let tt = trace_core_provenance(input, prog, var_tags, table_vars, lines)?;
            let dropped: Vec<String> = tt
                .cols
                .iter()
                .filter(|c| cols.contains(&c.name) && !c.tags.is_empty())
                .map(|c| format!("{}:{}", c.name, fmt_tags(&c.tags)))
                .collect();
            if !dropped.is_empty() {
                lines.push(format!(
                    "DROP_COL Drop([{}]): removed tagged cols [{}]",
                    cols.join(", "),
                    dropped.join(", ")
                ));
            }
            let out_cols = tt
                .cols
                .into_iter()
                .filter(|c| !cols.contains(&c.name))
                .map(|c| ColSpec {
                    agg_kind: AggKind::Raw,
                    ..c
                })
                .collect();
            Some(TableTy {
                cols: out_cols,
                row_tags: tt.row_tags,
                order_tags: tt.order_tags,
                ..TableTy::default()
            })
        }
        Plan::Rename { input, pairs } => {
            let tt = trace_core_provenance(input, prog, var_tags, table_vars, lines)?;
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
            Some(TableTy {
                cols: out_cols,
                row_tags: tt.row_tags,
                order_tags: tt.order_tags,
                ..TableTy::default()
            })
        }
        Plan::Filter { input, pred } => {
            let tt = trace_core_provenance(input, prog, var_tags, table_vars, lines)?;
            let p_tags = core_row_expr_tags(pred, &tt.cols, prog, var_tags);
            let next_row = tt.row_tags.union(&p_tags);
            if !p_tags.is_empty() {
                lines.push(format!(
                    "PROPAGATE Filter: predicate tags {} -> row_tags={}",
                    fmt_tags(&p_tags),
                    fmt_tags(&next_row)
                ));
            }
            Some(TableTy {
                cols: tt
                    .cols
                    .into_iter()
                    .map(|c| ColSpec {
                        agg_kind: AggKind::Raw,
                        ..c
                    })
                    .collect(),
                row_tags: next_row,
                order_tags: tt.order_tags,
                ..TableTy::default()
            })
        }
        Plan::Derive { input, items } => {
            let tt = trace_core_provenance(input, prog, var_tags, table_vars, lines)?;
            let mut cols: Vec<ColSpec> = tt
                .cols
                .into_iter()
                .map(|c| ColSpec {
                    agg_kind: AggKind::Raw,
                    ..c
                })
                .collect();
            for item in items {
                match item {
                    DeriveItem::ColExpr { name, expr } => {
                        let tags = core_row_expr_tags(expr, &cols, prog, var_tags);
                        if !tags.is_empty() {
                            lines.push(format!(
                                "PROPAGATE Derive({name}): inherited tags {}",
                                fmt_tags(&tags)
                            ));
                        }
                        let new_col = ColSpec {
                            name: name.clone(),
                            ty: ScalarTy::Text,
                            tags,
                            bucketed: false,
                            agg_kind: AggKind::Raw,
                        };
                        if let Some(slot) = cols.iter_mut().find(|c| c.name == *name) {
                            *slot = new_col;
                        } else {
                            cols.push(new_col);
                        }
                    }
                    DeriveItem::BucketCol { name, source, .. } => {
                        let src_tags = cols
                            .iter()
                            .find(|c| c.name == *source)
                            .map(|c| c.tags.clone())
                            .unwrap_or_default();
                        lines.push(format!(
                            "BUCKET Derive({name} <- {source}): tags={}, bucketed=true (eligible for clearance under suppress_small_groups)",
                            fmt_tags(&src_tags)
                        ));
                        let new_col = ColSpec {
                            name: name.clone(),
                            ty: ScalarTy::Text,
                            tags: src_tags,
                            bucketed: true,
                            agg_kind: AggKind::Raw,
                        };
                        if let Some(slot) = cols.iter_mut().find(|c| c.name == *name) {
                            *slot = new_col;
                        } else {
                            cols.push(new_col);
                        }
                    }
                }
            }
            Some(TableTy {
                cols,
                row_tags: tt.row_tags,
                order_tags: tt.order_tags,
                ..TableTy::default()
            })
        }
        Plan::Sort { input, keys } => {
            let tt = trace_core_provenance(input, prog, var_tags, table_vars, lines)?;
            let key_tags = TagSet::union_list(
                keys.iter()
                    .filter_map(|(k, _)| tt.find_col(k).map(|c| &c.tags)),
            );
            let next_order = tt.order_tags.union(&key_tags);
            if !key_tags.is_empty() {
                lines.push(format!(
                    "PROPAGATE Sort: key tags {} -> order_tags={}",
                    fmt_tags(&key_tags),
                    fmt_tags(&next_order)
                ));
            }
            Some(TableTy {
                cols: tt
                    .cols
                    .into_iter()
                    .map(|c| ColSpec {
                        agg_kind: AggKind::Raw,
                        ..c
                    })
                    .collect(),
                row_tags: tt.row_tags,
                order_tags: next_order,
                ..TableTy::default()
            })
        }
        Plan::Limit { input, .. } => {
            let tt = trace_core_provenance(input, prog, var_tags, table_vars, lines)?;
            let next_row = tt.row_tags.union(&tt.order_tags);
            if !tt.order_tags.is_empty() {
                lines.push(format!(
                    "PROPAGATE Limit: order_tags {} -> row_tags={}",
                    fmt_tags(&tt.order_tags),
                    fmt_tags(&next_row)
                ));
            }
            Some(TableTy {
                cols: tt
                    .cols
                    .into_iter()
                    .map(|c| ColSpec {
                        agg_kind: AggKind::Raw,
                        ..c
                    })
                    .collect(),
                row_tags: next_row,
                order_tags: tt.order_tags,
                ..TableTy::default()
            })
        }
        Plan::Distinct { input, cols } => {
            let tt = trace_core_provenance(input, prog, var_tags, table_vars, lines)?;
            let key_names = if cols.is_empty() {
                tt.col_names()
            } else {
                cols.clone()
            };
            let key_tags = TagSet::union_list(
                key_names
                    .iter()
                    .filter_map(|k| tt.find_col(k).map(|c| &c.tags)),
            );
            let next_row = tt.row_tags.union(&key_tags);
            if !key_tags.is_empty() {
                lines.push(format!(
                    "PROPAGATE Distinct: key tags {} -> row_tags={}",
                    fmt_tags(&key_tags),
                    fmt_tags(&next_row)
                ));
            }
            Some(TableTy {
                cols: tt
                    .cols
                    .into_iter()
                    .map(|c| ColSpec {
                        agg_kind: AggKind::Raw,
                        ..c
                    })
                    .collect(),
                row_tags: next_row,
                order_tags: tt.order_tags,
                ..TableTy::default()
            })
        }
        Plan::GroupBy { input, keys } => {
            let tt = trace_core_provenance(input, prog, var_tags, table_vars, lines)?;
            let key_tags =
                TagSet::union_list(keys.iter().filter_map(|k| tt.find_col(k).map(|c| &c.tags)));
            let next_row = tt.row_tags.union(&key_tags);
            if !key_tags.is_empty() {
                lines.push(format!(
                    "PROPAGATE GroupBy([{}]): key tags {} -> row_tags={}",
                    keys.join(", "),
                    fmt_tags(&key_tags),
                    fmt_tags(&next_row)
                ));
            }
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
            Some(TableTy {
                cols: out_cols,
                row_tags: next_row,
                order_tags: tt.order_tags,
                grouped_by: Some(keys.clone()),
                summarized: false,
                distinct_by: None,
            })
        }
        Plan::Summarize {
            input,
            aggs,
            distinct_key,
        } => {
            let tt = trace_core_provenance(input, prog, var_tags, table_vars, lines)?;
            let group_keys = tt.grouped_by.clone().unwrap_or_default();
            let dk_tags = distinct_key
                .as_deref()
                .and_then(|dk| tt.find_col(dk).map(|c| c.tags.clone()))
                .unwrap_or_default();
            let next_row = tt.row_tags.union(&dk_tags);
            let mut out_cols: Vec<ColSpec> = tt
                .cols
                .iter()
                .filter(|c| group_keys.contains(&c.name))
                .map(|c| ColSpec {
                    agg_kind: AggKind::GroupKey,
                    ..c.clone()
                })
                .collect();
            let mut agg_notes = Vec::new();
            for AggItem { name, op, arg } in aggs {
                let kind = if op.is_blending() {
                    AggKind::Blending
                } else {
                    AggKind::NonBlending
                };
                let arg_tags = arg
                    .as_ref()
                    .map(|re| core_row_expr_tags(re, &tt.cols, prog, var_tags))
                    .unwrap_or_default();
                let ord_tags = if op.is_order_sensitive() {
                    tt.order_tags.clone()
                } else {
                    TagSet::empty()
                };
                let col_tags = arg_tags.union(&tt.row_tags).union(&ord_tags);
                if !col_tags.is_empty() {
                    agg_notes.push(format!("{name}({op:?},{kind:?})={}", fmt_tags(&col_tags)));
                }
                out_cols.push(ColSpec {
                    name: name.clone(),
                    ty: ScalarTy::Int,
                    tags: col_tags,
                    bucketed: false,
                    agg_kind: kind,
                });
            }
            if !agg_notes.is_empty() || !next_row.is_empty() {
                lines.push(format!(
                    "PROPAGATE Summarize: row_tags={}, aggs=[{}]",
                    fmt_tags(&next_row),
                    agg_notes.join(", ")
                ));
            }
            Some(TableTy {
                cols: out_cols,
                row_tags: next_row,
                order_tags: TagSet::empty(),
                grouped_by: Some(group_keys),
                summarized: true,
                distinct_by: distinct_key.clone(),
            })
        }
        Plan::SuppressSmallGroups {
            input, min_k, mode, ..
        } => {
            let tt = trace_core_provenance(input, prog, var_tags, table_vars, lines)?;
            let before_tags = tt.total_tags();
            let out_tt = apply_suppress_schema(&tt, *mode);
            let cleared = before_tags.diff(&out_tt.total_tags());
            lines.push(format!(
                "CLEAR SuppressSmallGroups(min={min_k}, mode={mode:?}): cleared {} (remaining={})",
                fmt_tags(&cleared),
                fmt_tags(&out_tt.total_tags())
            ));
            Some(out_tt)
        }
        Plan::Redact { input, col, .. } => {
            let tt = trace_core_provenance(input, prog, var_tags, table_vars, lines)?;
            let cleared = tt.find_col(col).map(|c| c.tags.clone()).unwrap_or_default();
            lines.push(format!(
                "CLEAR Redact({col}): cleared {} from column `{col}`",
                fmt_tags(&cleared)
            ));
            let out_cols = tt
                .cols
                .into_iter()
                .map(|c| {
                    if c.name == *col {
                        ColSpec {
                            ty: ScalarTy::Text,
                            tags: TagSet::empty(),
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
            Some(TableTy {
                cols: out_cols,
                row_tags: tt.row_tags,
                order_tags: tt.order_tags,
                ..TableTy::default()
            })
        }
        Plan::Pseudonymize { input, col, .. } => {
            let tt = trace_core_provenance(input, prog, var_tags, table_vars, lines)?;
            let had_pii = tt.find_col(col).is_some_and(|c| c.tags.contains("pii"));
            if had_pii {
                lines.push(format!(
                    "CLEAR Pseudonymize({col}): cleared [pii] from column `{col}`"
                ));
            }
            let out_cols = tt
                .cols
                .into_iter()
                .map(|c| {
                    if c.name == *col {
                        ColSpec {
                            ty: ScalarTy::Text,
                            tags: c.tags.remove("pii"),
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
            Some(TableTy {
                cols: out_cols,
                row_tags: tt.row_tags,
                order_tags: tt.order_tags,
                ..TableTy::default()
            })
        }
        Plan::Join {
            kind,
            left,
            right,
            on,
            suffixes,
        } => {
            let l_tt = trace_core_provenance(left, prog, var_tags, table_vars, lines)?;
            let r_tt = trace_core_provenance(right, prog, var_tags, table_vars, lines)?;
            let key_pairs = resolve_join_pairs(&l_tt, &r_tt, on).ok()?;
            let joined_cols =
                build_joined_cols(*kind, &l_tt.cols, &r_tt.cols, on, suffixes).ok()?;
            let on_tags =
                TagSet::union_owned(key_pairs.iter().map(|(lc, rc)| lc.tags.union(&rc.tags)));
            let next_row = l_tt.row_tags.union(&r_tt.row_tags).union(&on_tags);
            if !on_tags.is_empty() || !next_row.is_empty() {
                lines.push(format!(
                    "PROPAGATE Join({kind:?}, on=[{}]): key tags {} -> row_tags={}",
                    fmt_join_on(on),
                    fmt_tags(&on_tags),
                    fmt_tags(&next_row)
                ));
            }
            let new_order = match kind {
                JoinKind::Semi | JoinKind::Anti => l_tt.order_tags,
                _ => l_tt.order_tags.union(&r_tt.order_tags),
            };
            Some(TableTy {
                cols: joined_cols,
                row_tags: next_row,
                order_tags: new_order,
                ..TableTy::default()
            })
        }
        Plan::Union { left, right } => {
            let l_tt = trace_core_provenance(left, prog, var_tags, table_vars, lines)?;
            let r_tt = trace_core_provenance(right, prog, var_tags, table_vars, lines)?;
            let out_cols = merge_union_cols(&l_tt.cols, &r_tt.cols)?;
            let next_row = l_tt.row_tags.union(&r_tt.row_tags);
            let next_order = l_tt.order_tags.union(&r_tt.order_tags);
            lines.push(format!(
                "PROPAGATE Union: row_tags={}, cols={}",
                fmt_tags(&next_row),
                fmt_tagged_cols(&out_cols)
            ));
            Some(TableTy {
                cols: out_cols,
                row_tags: next_row,
                order_tags: next_order,
                ..TableTy::default()
            })
        }
        Plan::Window { input, items } => {
            let tt = trace_core_provenance(input, prog, var_tags, table_vars, lines)?;
            let mut cols: Vec<ColSpec> = tt
                .cols
                .into_iter()
                .map(|c| ColSpec {
                    agg_kind: AggKind::Raw,
                    ..c
                })
                .collect();
            for item in items {
                if let Ok(next_cols) = apply_window_item(&cols, &tt.order_tags, item) {
                    if let Some(added) = next_cols.iter().find(|c| c.name == item.name)
                        && !added.tags.is_empty()
                    {
                        lines.push(format!(
                            "PROPAGATE Window({}): tags={}",
                            item.name,
                            fmt_tags(&added.tags)
                        ));
                    }
                    cols = next_cols;
                }
            }
            Some(TableTy {
                cols,
                row_tags: tt.row_tags,
                order_tags: tt.order_tags,
                ..TableTy::default()
            })
        }
        Plan::FillGaps { input, .. }
        | Plan::PivotWider { input, .. }
        | Plan::Crosstab { input, .. } => {
            trace_core_provenance(input, prog, var_tags, table_vars, lines)
        }
    }
}

// ===========================================================================
// Phase 2 ExecPlan Sensitivity Provenance Tracer
// ===========================================================================

fn exec_row_expr_tags(
    re: &ExecRowExpr,
    cols: &[ColSpec],
    prog: &ExecProgram,
    var_tags: &HashMap<Ident, TagSet>,
) -> TagSet {
    match re {
        ExecRowExpr::Lit(_) => TagSet::empty(),
        ExecRowExpr::Col(c) => cols
            .iter()
            .find(|cs| cs.name == *c)
            .map(|cs| cs.tags.clone())
            .unwrap_or_default(),
        ExecRowExpr::OuterVar(v) => var_tags.get(v).cloned().unwrap_or_default(),
        ExecRowExpr::ConstRef(c) => prog
            .find_const(c)
            .map(|d| d.lty.effective_tags())
            .unwrap_or_default(),
        ExecRowExpr::Prim { args, .. } | ExecRowExpr::CallPure { args, .. } => {
            let mut acc = TagSet::empty();
            for a in args {
                acc = acc.union(&exec_row_expr_tags(a, cols, prog, var_tags));
            }
            acc
        }
        ExecRowExpr::IfE {
            cond,
            then_br,
            else_br,
        } => exec_row_expr_tags(cond, cols, prog, var_tags)
            .union(&exec_row_expr_tags(then_br, cols, prog, var_tags))
            .union(&exec_row_expr_tags(else_br, cols, prog, var_tags)),
        ExecRowExpr::Coalesce {
            opt_expr,
            default_expr,
        } => exec_row_expr_tags(opt_expr, cols, prog, var_tags).union(&exec_row_expr_tags(
            default_expr,
            cols,
            prog,
            var_tags,
        )),
    }
}

fn trace_exec_provenance(
    plan: &ExecPlan,
    prog: &ExecProgram,
    var_tags: &HashMap<Ident, TagSet>,
    table_vars: &HashMap<Ident, TableTy>,
    lines: &mut Vec<String>,
) -> Option<TableTy> {
    match plan {
        ExecPlan::SourceDB {
            table_name, schema, ..
        } => {
            let total = schema.total_tags();
            lines.push(format!(
                "ENTER SourceDB({table_name}): tags={}, cols={}, row_tags={}",
                fmt_tags(&total),
                fmt_tagged_cols(&schema.cols),
                fmt_tags(&schema.row_tags)
            ));
            Some(schema.clone())
        }
        ExecPlan::SourceExpr(e) => match e.as_ref() {
            ExecExpr::TableLit { schema, .. } => {
                lines.push(format!(
                    "ENTER TableLit: tags={}, cols={}",
                    fmt_tags(&schema.total_tags()),
                    fmt_tagged_cols(&schema.cols)
                ));
                Some(schema.clone())
            }
            ExecExpr::Var(v) => {
                let tt = table_vars.get(v).cloned();
                if let Some(ref schema) = tt {
                    lines.push(format!(
                        "ENTER SourceVar({v}): tags={}, cols={}",
                        fmt_tags(&schema.total_tags()),
                        fmt_tagged_cols(&schema.cols)
                    ));
                }
                tt
            }
            _ => None,
        },
        ExecPlan::Select { input, cols } => {
            let tt = trace_exec_provenance(input, prog, var_tags, table_vars, lines)?;
            let dropped: Vec<String> = tt
                .cols
                .iter()
                .filter(|c| !cols.contains(&c.name) && !c.tags.is_empty())
                .map(|c| format!("{}:{}", c.name, fmt_tags(&c.tags)))
                .collect();
            if !dropped.is_empty() {
                lines.push(format!(
                    "DROP_COL Select([{}]): removed tagged cols [{}]",
                    cols.join(", "),
                    dropped.join(", ")
                ));
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
            Some(TableTy {
                cols: out_cols,
                row_tags: tt.row_tags,
                order_tags: tt.order_tags,
                ..TableTy::default()
            })
        }
        ExecPlan::Drop { input, cols } => {
            let tt = trace_exec_provenance(input, prog, var_tags, table_vars, lines)?;
            let dropped: Vec<String> = tt
                .cols
                .iter()
                .filter(|c| cols.contains(&c.name) && !c.tags.is_empty())
                .map(|c| format!("{}:{}", c.name, fmt_tags(&c.tags)))
                .collect();
            if !dropped.is_empty() {
                lines.push(format!(
                    "DROP_COL Drop([{}]): removed tagged cols [{}]",
                    cols.join(", "),
                    dropped.join(", ")
                ));
            }
            let out_cols = tt
                .cols
                .into_iter()
                .filter(|c| !cols.contains(&c.name))
                .map(|c| ColSpec {
                    agg_kind: AggKind::Raw,
                    ..c
                })
                .collect();
            Some(TableTy {
                cols: out_cols,
                row_tags: tt.row_tags,
                order_tags: tt.order_tags,
                ..TableTy::default()
            })
        }
        ExecPlan::Rename { input, pairs } => {
            let tt = trace_exec_provenance(input, prog, var_tags, table_vars, lines)?;
            let out_cols = tt
                .cols
                .into_iter()
                .map(|c| match pairs.iter().find(|(old_n, _)| *old_n == c.name) {
                    Some((_, new_n)) => ColSpec {
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
            Some(TableTy {
                cols: out_cols,
                row_tags: tt.row_tags,
                order_tags: tt.order_tags,
                ..TableTy::default()
            })
        }
        ExecPlan::Filter { input, pred } => {
            let tt = trace_exec_provenance(input, prog, var_tags, table_vars, lines)?;
            let p_tags = exec_row_expr_tags(pred, &tt.cols, prog, var_tags);
            let next_row = tt.row_tags.union(&p_tags);
            if !p_tags.is_empty() {
                lines.push(format!(
                    "PROPAGATE Filter: predicate tags {} -> row_tags={}",
                    fmt_tags(&p_tags),
                    fmt_tags(&next_row)
                ));
            }
            Some(TableTy {
                cols: tt
                    .cols
                    .into_iter()
                    .map(|c| ColSpec {
                        agg_kind: AggKind::Raw,
                        ..c
                    })
                    .collect(),
                row_tags: next_row,
                order_tags: tt.order_tags,
                ..TableTy::default()
            })
        }
        ExecPlan::Derive { input, items } => {
            let tt = trace_exec_provenance(input, prog, var_tags, table_vars, lines)?;
            let mut cols: Vec<ColSpec> = tt
                .cols
                .into_iter()
                .map(|c| ColSpec {
                    agg_kind: AggKind::Raw,
                    ..c
                })
                .collect();
            for item in items {
                match item {
                    ExecDeriveItem::ColExpr { name, expr } => {
                        let tags = exec_row_expr_tags(expr, &cols, prog, var_tags);
                        if !tags.is_empty() {
                            lines.push(format!(
                                "PROPAGATE Derive({name}): inherited tags {}",
                                fmt_tags(&tags)
                            ));
                        }
                        let new_col = ColSpec {
                            name: name.clone(),
                            ty: ScalarTy::Text,
                            tags,
                            bucketed: false,
                            agg_kind: AggKind::Raw,
                        };
                        if let Some(slot) = cols.iter_mut().find(|c| c.name == *name) {
                            *slot = new_col;
                        } else {
                            cols.push(new_col);
                        }
                    }
                    ExecDeriveItem::BucketCol { name, source, .. } => {
                        let src_tags = cols
                            .iter()
                            .find(|c| c.name == *source)
                            .map(|c| c.tags.clone())
                            .unwrap_or_default();
                        lines.push(format!(
                            "BUCKET Derive({name} <- {source}): tags={}, bucketed=true (eligible for clearance under suppress_small_groups)",
                            fmt_tags(&src_tags)
                        ));
                        let new_col = ColSpec {
                            name: name.clone(),
                            ty: ScalarTy::Text,
                            tags: src_tags,
                            bucketed: true,
                            agg_kind: AggKind::Raw,
                        };
                        if let Some(slot) = cols.iter_mut().find(|c| c.name == *name) {
                            *slot = new_col;
                        } else {
                            cols.push(new_col);
                        }
                    }
                }
            }
            Some(TableTy {
                cols,
                row_tags: tt.row_tags,
                order_tags: tt.order_tags,
                ..TableTy::default()
            })
        }
        ExecPlan::Sort { input, keys } => {
            let tt = trace_exec_provenance(input, prog, var_tags, table_vars, lines)?;
            let key_tags = TagSet::union_list(
                keys.iter()
                    .filter_map(|(k, _)| tt.find_col(k).map(|c| &c.tags)),
            );
            let next_order = tt.order_tags.union(&key_tags);
            if !key_tags.is_empty() {
                lines.push(format!(
                    "PROPAGATE Sort: key tags {} -> order_tags={}",
                    fmt_tags(&key_tags),
                    fmt_tags(&next_order)
                ));
            }
            Some(TableTy {
                cols: tt
                    .cols
                    .into_iter()
                    .map(|c| ColSpec {
                        agg_kind: AggKind::Raw,
                        ..c
                    })
                    .collect(),
                row_tags: tt.row_tags,
                order_tags: next_order,
                ..TableTy::default()
            })
        }
        ExecPlan::Limit { input, .. } => {
            let tt = trace_exec_provenance(input, prog, var_tags, table_vars, lines)?;
            let next_row = tt.row_tags.union(&tt.order_tags);
            if !tt.order_tags.is_empty() {
                lines.push(format!(
                    "PROPAGATE Limit: order_tags {} -> row_tags={}",
                    fmt_tags(&tt.order_tags),
                    fmt_tags(&next_row)
                ));
            }
            Some(TableTy {
                cols: tt
                    .cols
                    .into_iter()
                    .map(|c| ColSpec {
                        agg_kind: AggKind::Raw,
                        ..c
                    })
                    .collect(),
                row_tags: next_row,
                order_tags: tt.order_tags,
                ..TableTy::default()
            })
        }
        ExecPlan::Distinct { input, cols } => {
            let tt = trace_exec_provenance(input, prog, var_tags, table_vars, lines)?;
            let key_names = if cols.is_empty() {
                tt.col_names()
            } else {
                cols.clone()
            };
            let key_tags = TagSet::union_list(
                key_names
                    .iter()
                    .filter_map(|k| tt.find_col(k).map(|c| &c.tags)),
            );
            let next_row = tt.row_tags.union(&key_tags);
            if !key_tags.is_empty() {
                lines.push(format!(
                    "PROPAGATE Distinct: key tags {} -> row_tags={}",
                    fmt_tags(&key_tags),
                    fmt_tags(&next_row)
                ));
            }
            Some(TableTy {
                cols: tt
                    .cols
                    .into_iter()
                    .map(|c| ColSpec {
                        agg_kind: AggKind::Raw,
                        ..c
                    })
                    .collect(),
                row_tags: next_row,
                order_tags: tt.order_tags,
                ..TableTy::default()
            })
        }
        ExecPlan::GroupBy { input, keys } => {
            let tt = trace_exec_provenance(input, prog, var_tags, table_vars, lines)?;
            let key_tags =
                TagSet::union_list(keys.iter().filter_map(|k| tt.find_col(k).map(|c| &c.tags)));
            let next_row = tt.row_tags.union(&key_tags);
            if !key_tags.is_empty() {
                lines.push(format!(
                    "PROPAGATE GroupBy([{}]): key tags {} -> row_tags={}",
                    keys.join(", "),
                    fmt_tags(&key_tags),
                    fmt_tags(&next_row)
                ));
            }
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
            Some(TableTy {
                cols: out_cols,
                row_tags: next_row,
                order_tags: tt.order_tags,
                grouped_by: Some(keys.clone()),
                summarized: false,
                distinct_by: None,
            })
        }
        ExecPlan::Summarize {
            input,
            aggs,
            distinct_key,
        } => {
            let tt = trace_exec_provenance(input, prog, var_tags, table_vars, lines)?;
            let group_keys = tt.grouped_by.clone().unwrap_or_default();
            let dk_tags = distinct_key
                .as_deref()
                .and_then(|dk| tt.find_col(dk).map(|c| c.tags.clone()))
                .unwrap_or_default();
            let next_row = tt.row_tags.union(&dk_tags);
            let mut out_cols: Vec<ColSpec> = tt
                .cols
                .iter()
                .filter(|c| group_keys.contains(&c.name))
                .map(|c| ColSpec {
                    agg_kind: AggKind::GroupKey,
                    ..c.clone()
                })
                .collect();
            let mut agg_notes = Vec::new();
            for ExecAggItem { name, op, arg } in aggs {
                let kind = if op.is_blending() {
                    AggKind::Blending
                } else {
                    AggKind::NonBlending
                };
                let arg_tags = arg
                    .as_ref()
                    .map(|re| exec_row_expr_tags(re, &tt.cols, prog, var_tags))
                    .unwrap_or_default();
                let ord_tags = if op.is_order_sensitive() {
                    tt.order_tags.clone()
                } else {
                    TagSet::empty()
                };
                let col_tags = arg_tags.union(&tt.row_tags).union(&ord_tags);
                if !col_tags.is_empty() {
                    agg_notes.push(format!("{name}({op:?},{kind:?})={}", fmt_tags(&col_tags)));
                }
                out_cols.push(ColSpec {
                    name: name.clone(),
                    ty: ScalarTy::Int,
                    tags: col_tags,
                    bucketed: false,
                    agg_kind: kind,
                });
            }
            if !agg_notes.is_empty() || !next_row.is_empty() {
                lines.push(format!(
                    "PROPAGATE Summarize: row_tags={}, aggs=[{}]",
                    fmt_tags(&next_row),
                    agg_notes.join(", ")
                ));
            }
            Some(TableTy {
                cols: out_cols,
                row_tags: next_row,
                order_tags: TagSet::empty(),
                grouped_by: Some(group_keys),
                summarized: true,
                distinct_by: distinct_key.clone(),
            })
        }
        ExecPlan::SuppressSmallGroups {
            input, min_k, mode, ..
        } => {
            let tt = trace_exec_provenance(input, prog, var_tags, table_vars, lines)?;
            let before_tags = tt.total_tags();
            let out_tt = apply_suppress_schema(&tt, *mode);
            let cleared = before_tags.diff(&out_tt.total_tags());
            lines.push(format!(
                "CLEAR SuppressSmallGroups(min={min_k}, mode={mode:?}): cleared {} (remaining={})",
                fmt_tags(&cleared),
                fmt_tags(&out_tt.total_tags())
            ));
            Some(out_tt)
        }
        ExecPlan::Redact { input, col, .. } => {
            let tt = trace_exec_provenance(input, prog, var_tags, table_vars, lines)?;
            let cleared = tt.find_col(col).map(|c| c.tags.clone()).unwrap_or_default();
            lines.push(format!(
                "CLEAR Redact({col}): cleared {} from column `{col}`",
                fmt_tags(&cleared)
            ));
            let out_cols = tt
                .cols
                .into_iter()
                .map(|c| {
                    if c.name == *col {
                        ColSpec {
                            ty: ScalarTy::Text,
                            tags: TagSet::empty(),
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
            Some(TableTy {
                cols: out_cols,
                row_tags: tt.row_tags,
                order_tags: tt.order_tags,
                ..TableTy::default()
            })
        }
        ExecPlan::Pseudonymize { input, col, .. } => {
            let tt = trace_exec_provenance(input, prog, var_tags, table_vars, lines)?;
            let had_pii = tt.find_col(col).is_some_and(|c| c.tags.contains("pii"));
            if had_pii {
                lines.push(format!(
                    "CLEAR Pseudonymize({col}): cleared [pii] from column `{col}`"
                ));
            }
            let out_cols = tt
                .cols
                .into_iter()
                .map(|c| {
                    if c.name == *col {
                        ColSpec {
                            ty: ScalarTy::Text,
                            tags: c.tags.remove("pii"),
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
            Some(TableTy {
                cols: out_cols,
                row_tags: tt.row_tags,
                order_tags: tt.order_tags,
                ..TableTy::default()
            })
        }
        ExecPlan::Join {
            kind,
            left,
            right,
            on,
            suffixes,
        } => {
            let l_tt = trace_exec_provenance(left, prog, var_tags, table_vars, lines)?;
            let r_tt = trace_exec_provenance(right, prog, var_tags, table_vars, lines)?;
            let key_pairs = resolve_join_pairs(&l_tt, &r_tt, on).ok()?;
            let joined_cols =
                build_joined_cols(*kind, &l_tt.cols, &r_tt.cols, on, suffixes).ok()?;
            let on_tags =
                TagSet::union_owned(key_pairs.iter().map(|(lc, rc)| lc.tags.union(&rc.tags)));
            let next_row = l_tt.row_tags.union(&r_tt.row_tags).union(&on_tags);
            if !on_tags.is_empty() || !next_row.is_empty() {
                lines.push(format!(
                    "PROPAGATE Join({kind:?}, on=[{}]): key tags {} -> row_tags={}",
                    fmt_join_on(on),
                    fmt_tags(&on_tags),
                    fmt_tags(&next_row)
                ));
            }
            let new_order = match kind {
                JoinKind::Semi | JoinKind::Anti => l_tt.order_tags,
                _ => l_tt.order_tags.union(&r_tt.order_tags),
            };
            Some(TableTy {
                cols: joined_cols,
                row_tags: next_row,
                order_tags: new_order,
                ..TableTy::default()
            })
        }
        ExecPlan::Union { left, right } => {
            let l_tt = trace_exec_provenance(left, prog, var_tags, table_vars, lines)?;
            let r_tt = trace_exec_provenance(right, prog, var_tags, table_vars, lines)?;
            let out_cols = merge_union_cols(&l_tt.cols, &r_tt.cols)?;
            let next_row = l_tt.row_tags.union(&r_tt.row_tags);
            let next_order = l_tt.order_tags.union(&r_tt.order_tags);
            lines.push(format!(
                "PROPAGATE Union: row_tags={}, cols={}",
                fmt_tags(&next_row),
                fmt_tagged_cols(&out_cols)
            ));
            Some(TableTy {
                cols: out_cols,
                row_tags: next_row,
                order_tags: next_order,
                ..TableTy::default()
            })
        }
        ExecPlan::Window { input, items } => {
            let tt = trace_exec_provenance(input, prog, var_tags, table_vars, lines)?;
            let mut cols: Vec<ColSpec> = tt
                .cols
                .into_iter()
                .map(|c| ColSpec {
                    agg_kind: AggKind::Raw,
                    ..c
                })
                .collect();
            for item in items {
                if let Ok(next_cols) = apply_window_item(&cols, &tt.order_tags, item) {
                    if let Some(added) = next_cols.iter().find(|c| c.name == item.name)
                        && !added.tags.is_empty()
                    {
                        lines.push(format!(
                            "PROPAGATE Window({}): tags={}",
                            item.name,
                            fmt_tags(&added.tags)
                        ));
                    }
                    cols = next_cols;
                }
            }
            Some(TableTy {
                cols,
                row_tags: tt.row_tags,
                order_tags: tt.order_tags,
                ..TableTy::default()
            })
        }
        ExecPlan::PivotLonger {
            input,
            cols,
            names_to,
            values_to,
            value_ty,
            value_tags,
        } => {
            let tt = trace_exec_provenance(input, prog, var_tags, table_vars, lines)?;
            let mut val_tags = value_tags.clone();
            let mut out_cols: Vec<ColSpec> = Vec::new();
            for c in &tt.cols {
                if cols.contains(&c.name) {
                    val_tags = val_tags.union(&c.tags);
                } else {
                    out_cols.push(ColSpec {
                        agg_kind: AggKind::Raw,
                        ..c.clone()
                    });
                }
            }
            if !val_tags.is_empty() {
                lines.push(format!(
                    "PROPAGATE PivotLonger({values_to}): tags={}",
                    fmt_tags(&val_tags)
                ));
            }
            out_cols.push(ColSpec {
                name: names_to.clone(),
                ty: ScalarTy::Text,
                tags: TagSet::empty(),
                bucketed: false,
                agg_kind: AggKind::Raw,
            });
            out_cols.push(ColSpec {
                name: values_to.clone(),
                ty: value_ty.clone(),
                tags: val_tags,
                bucketed: false,
                agg_kind: AggKind::Raw,
            });
            Some(TableTy {
                cols: out_cols,
                row_tags: tt.row_tags,
                order_tags: tt.order_tags,
                ..TableTy::default()
            })
        }
        ExecPlan::FillGaps { input, .. }
        | ExecPlan::PivotWider { input, .. }
        | ExecPlan::Crosstab { input, .. } => {
            trace_exec_provenance(input, prog, var_tags, table_vars, lines)
        }
    }
}

fn apply_suppress_schema(tt: &TableTy, mode: SuppressMode) -> TableTy {
    let raw_key_tags = TagSet::union_list(
        tt.cols
            .iter()
            .filter(|c| c.agg_kind == AggKind::GroupKey && !c.bucketed)
            .map(|c| &c.tags),
    );
    let out_cols = tt
        .cols
        .iter()
        .map(|c| {
            let orig_kind = c.agg_kind;
            let base = match orig_kind {
                AggKind::GroupKey => {
                    if c.bucketed {
                        ColSpec {
                            tags: TagSet::empty(),
                            agg_kind: AggKind::Raw,
                            ..c.clone()
                        }
                    } else {
                        ColSpec {
                            agg_kind: AggKind::Raw,
                            ..c.clone()
                        }
                    }
                }
                AggKind::Blending => ColSpec {
                    tags: TagSet::empty(),
                    agg_kind: AggKind::Raw,
                    ..c.clone()
                },
                AggKind::NonBlending | AggKind::Raw => ColSpec {
                    agg_kind: AggKind::Raw,
                    ..c.clone()
                },
            };
            match (mode, orig_kind) {
                (SuppressMode::MaskComplementary, AggKind::Blending | AggKind::NonBlending) => {
                    ColSpec {
                        ty: ensure_option_scalar(&base.ty),
                        bucketed: false,
                        ..base
                    }
                }
                _ => base,
            }
        })
        .collect();
    TableTy {
        cols: out_cols,
        row_tags: raw_key_tags,
        order_tags: tt.order_tags.clone(),
        grouped_by: None,
        summarized: false,
        distinct_by: None,
    }
}

// ===========================================================================
// Plan Tree Formatters
// ===========================================================================

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
        ExecPlan::PivotLonger {
            input,
            cols,
            names_to,
            values_to,
            ..
        } => {
            let _ = writeln!(
                out,
                "PivotLonger([{}] -> {names_to}, {values_to})",
                cols.join(", ")
            );
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
