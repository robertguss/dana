//! Parameterized SQL pushdown splitter for Dana Core IR (`core::Plan`) and
//! Phase 2 execution IR (`runtime::ir::ExecPlan`).
//!
//! Splits relational plans rooted at `SourceDB` into:
//! - [`SplitPlan::FullyPushed`]: the entire plan compiles to a single 100% parameterized
//!   SQL query (`?` for SQLite, `$1..$n` for PostgreSQL).
//! - [`SplitPlan::Hybrid`]: a maximal same-DB prefix compiles to parameterized SQL whose
//!   result is bound to `placeholder_var` as input to `local_suffix` on the vectorized VM.
//! - [`SplitPlan::LocalOnly`]: no same-DB pushdown prefix applies; includes an explicit
//!   `reason` describing the pushdown barrier.
//!
//! Also provides [`collect_core_plan_pushdowns`] and [`collect_exec_plan_pushdowns`] to
//! split independent DB branches inside cross-source, cross-DB, or unchecked-cardinality joins.
//!
//! **Strict Soundness Guarantees (`Oracle == VM == SQLite == Postgres`):**
//! 1. **100% Parameterized SQL:** All identifiers are strictly double-quoted (`"` escaped as `""`).
//!    Every literal value, outer lexical variable, and constant reference is emitted strictly as a
//!    positional bind slot ([`SqlParamSlot`]); values are NEVER interpolated into SQL text.
//! 2. **Dialect-Exact Semantics:** No trapping arithmetic, no `UnwrapBang`, no `CallPure`, no
//!    `Float` comparisons/ordering (`NaN`/`-0.0`), no `Decimal`/`Timestamp` ordering on SQLite,
//!    no `MIN`/`MAX` on `Bool` on Postgres, null-safe `Option` equality (`IS` / `IS NOT DISTINCT FROM`),
//!    exact `OptNone < OptSome` sort order (`ASC NULLS FIRST` / `DESC NULLS LAST`), exact ASCII
//!    whitespace `TRIM(x, " \t\n\r")`, and wildcard-free substring `INSTR`/`STRPOS`.
//! 3. **Order & Cardinality Preservation:** `Sort` pushes only when sort keys are provably tie-free
//!    (covering a unique key or all output columns). `Join` and `Distinct` push only in order-insensitive
//!    contexts (`order_insensitive = true`) and checked joins (`InnerOne`, `InnerManyToOne`, `LeftOne`,
//!    `LeftManyToOne`) push ONLY when the checked side's join keys are proven unique via `SchemaLockFile`
//!    primary keys or upstream `GroupBy` keys. `Summarize` never pushes directly beneath
//!    `SuppressSmallGroups` (which requires local `GroupMeta`).

use std::collections::{HashMap, HashSet};
use std::fmt::Write as _;

use crate::core::bigint::BigInt;
use crate::core::check::{base_of_scalar, build_joined_cols, merge_union_cols, resolve_join_pairs};
use crate::core::syntax::{
    AggItem, AggKind, AggOp, ColSpec, DeriveItem, Expr, Float64, HostOp, Ident, JoinKind, JoinOn,
    Literal, Plan, PrimOp, Program, RowExpr, ScalarTy, SortDir, Suffixes, TableTy, TagSet, Ty,
};
use crate::db::schema_lock::SchemaLockFile;
use crate::db::{
    SqlDialect, SqlParam, format_decimal_canonical, quote_sql_ident, quote_sql_table_ref,
};
use crate::formats::time::{format_iso_date, format_iso_timestamp};
use crate::oracle::value::Val;
use crate::runtime::ir::{
    DedupeKeep, ExecAggItem, ExecAggOp, ExecDeriveItem, ExecExpr, ExecHostOp, ExecPlan, ExecPrimOp,
    ExecProgram, ExecRowExpr,
};

// ===========================================================================
// Public API Types
// ===========================================================================

/// A single parameterized bind slot in a [`SqlPushdownQuery`].
///
/// Separates static plan inspection (`dana explain`, which does not need runtime values)
/// from runtime parameter resolution via [`SqlPushdownQuery::resolve_params`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SqlParamSlot {
    /// Constant scalar literal already converted to a typed [`SqlParam`].
    Literal(SqlParam),
    /// Outer lexical variable captured from an enclosing Dana scope (`OuterVar`).
    OuterVar(Ident),
    /// Top-level Dana `const` reference (`ConstRef`).
    ConstRef(Ident),
}

impl SqlParamSlot {
    /// Format a human-readable, privacy-safe summary of this parameter slot for `explain`.
    #[must_use]
    pub fn describe(&self) -> String {
        match self {
            Self::Literal(p) => describe_sql_param(p),
            Self::OuterVar(name) => format!("OuterVar({name})"),
            Self::ConstRef(name) => format!("ConstRef({name})"),
        }
    }
}

/// Format a [`SqlParam`] concisely for diagnostic/explain parameter tables.
#[must_use]
pub fn describe_sql_param(p: &SqlParam) -> String {
    match p {
        SqlParam::Null => "Null".to_string(),
        SqlParam::Bool(b) => format!("Bool({b})"),
        SqlParam::Int(i) => format!("Int({i})"),
        SqlParam::Decimal(d) => format!("Decimal({})", format_decimal_canonical(d)),
        SqlParam::Float(f) => format!("Float({})", f.to_f64()),
        SqlParam::Text(s) => format!("Text({s:?})"),
        SqlParam::Bytes(bs) => format!("Bytes(len={})", bs.len()),
        SqlParam::Date(days) => format!("Date({})", format_iso_date(*days)),
        SqlParam::Timestamp(us) => format!("Timestamp({})", format_iso_timestamp(*us)),
        SqlParam::Duration(us) => format!("Duration({us}us)"),
    }
}

/// A compiled, 100% parameterized SQL query representing a pushable same-DB subtree.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SqlPushdownQuery {
    pub db_name: Ident,
    pub dialect: SqlDialect,
    pub sql: String,
    pub param_slots: Vec<SqlParamSlot>,
    pub out_schema: TableTy,
    pub pushed_ops: Vec<String>,
    pub boundary_reason: Option<String>,
}

impl SqlPushdownQuery {
    /// Resolve every [`SqlParamSlot`] into a concrete [`SqlParam`] ready for
    /// [`crate::db::DbConnection::query_batches`] / [`crate::db::DbConnection::query_rows`].
    ///
    /// # Errors
    /// Returns a descriptive error string if an `OuterVar` or `ConstRef` is missing or
    /// cannot be converted to a scalar [`SqlParam`].
    pub fn resolve_params(
        &self,
        lookup_var: impl Fn(&str) -> Option<Val>,
        lookup_const: impl Fn(&str) -> Option<Val>,
    ) -> Result<Vec<SqlParam>, String> {
        let mut out = Vec::with_capacity(self.param_slots.len());
        for (idx, slot) in self.param_slots.iter().enumerate() {
            match slot {
                SqlParamSlot::Literal(p) => out.push(p.clone()),
                SqlParamSlot::OuterVar(name) => {
                    let val = lookup_var(name).ok_or_else(|| {
                        format!("missing runtime value for outer variable `{name}` at param #{idx}")
                    })?;
                    let param = SqlParam::from_val(&val).map_err(|e| {
                        format!("failed to bind outer variable `{name}` at param #{idx}: {e}")
                    })?;
                    out.push(param);
                }
                SqlParamSlot::ConstRef(name) => {
                    let val = lookup_const(name)
                        .ok_or_else(|| format!("missing constant `{name}` at param #{idx}"))?;
                    let param = SqlParam::from_val(&val).map_err(|e| {
                        format!("failed to bind constant `{name}` at param #{idx}: {e}")
                    })?;
                    out.push(param);
                }
            }
        }
        Ok(out)
    }
}

/// Result of splitting a relational plan into a parameterized SQL pushdown query and
/// an optional local vectorized VM suffix.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SplitPlan<P> {
    /// Entire plan compiles to a single parameterized SQL query.
    FullyPushed(SqlPushdownQuery),
    /// A maximal DB subtree compiles to `pushdown`; bind its result to `placeholder_var`
    /// and evaluate `local_suffix` on the local columnar VM.
    Hybrid {
        pushdown: SqlPushdownQuery,
        placeholder_var: Ident,
        local_suffix: P,
    },
    /// Plan cannot be pushed to `db_name`; run `plan` locally on the VM.
    LocalOnly { plan: P, reason: String },
}

/// One independently pushable DB subtree extracted from a multi-branch plan tree.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CollectedBranchPushdown {
    pub placeholder_var: Ident,
    pub pushdown: SqlPushdownQuery,
}

/// Result of collecting all independent DB pushdowns across a plan tree
/// (such as cross-DB joins, DB-vs-local joins, or unchecked cardinality joins).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CollectedPlanPushdowns<P> {
    pub branches: Vec<CollectedBranchPushdown>,
    pub local_plan: P,
    pub boundary_reasons: Vec<String>,
}

// ===========================================================================
// Public Entry Points
// ===========================================================================

/// Split a Core IR v0.1 [`Plan`] into a parameterized SQL pushdown query for `db_name`
/// and an optional local vectorized VM suffix.
#[must_use]
pub fn split_core_plan_pushdown(
    plan: &Plan,
    prog: &Program,
    db_name: &str,
    dialect: SqlDialect,
    lock: Option<&SchemaLockFile>,
) -> SplitPlan<Plan> {
    let ctx = CoreSplitCtx::new(prog, Some(db_name), dialect, lock);
    let order_insensitive = false;
    match split_core_node(plan, &ctx, order_insensitive, false) {
        NodeSplit::Pushed(node) => SplitPlan::FullyPushed(node.into_query(dialect, None)),
        NodeSplit::Hybrid {
            pushed,
            placeholder_var,
            local_plan,
            reason,
        } => {
            if core_plan_has_source_db(&local_plan, &ctx, Some(db_name)) {
                SplitPlan::LocalOnly {
                    plan: plan.clone(),
                    reason,
                }
            } else {
                SplitPlan::Hybrid {
                    pushdown: pushed.into_query(dialect, Some(reason)),
                    placeholder_var,
                    local_suffix: local_plan,
                }
            }
        }
        NodeSplit::LocalOnly { reason } => SplitPlan::LocalOnly {
            plan: plan.clone(),
            reason,
        },
    }
}

/// Split a Phase 2 [`ExecPlan`] into a parameterized SQL pushdown query for `db_name`
/// and an optional local vectorized VM suffix.
#[must_use]
pub fn split_exec_plan_pushdown(
    plan: &ExecPlan,
    prog: &ExecProgram,
    db_name: &str,
    dialect: SqlDialect,
    lock: Option<&SchemaLockFile>,
) -> SplitPlan<ExecPlan> {
    split_exec_plan_pushdown_with_table_refs(plan, prog, db_name, dialect, lock, None)
}

/// Hidden metadata column alias carrying per-group raw row counts from SQL `Summarize`
/// into a downstream local `SuppressSmallGroups` stage.
pub const HIDDEN_GROUP_ROW_COUNT_COL: &str = "__dana_gm_rows";

/// Hidden metadata column alias carrying per-group `COUNT(DISTINCT key)` counts from
/// SQL `Summarize` into a downstream local `SuppressSmallGroups(distinct_by: ...)` stage.
pub const HIDDEN_GROUP_DISTINCT_COUNT_COL: &str = "__dana_gm_dist";

const fn join_right_is_order_insensitive(kind: JoinKind, outer_order_insensitive: bool) -> bool {
    outer_order_insensitive
        || matches!(
            kind,
            JoinKind::InnerOne
                | JoinKind::LeftOne
                | JoinKind::InnerManyToOne
                | JoinKind::LeftManyToOne
                | JoinKind::Semi
                | JoinKind::Anti
        )
}

#[derive(Clone, Copy)]
enum SuppressPushCtx<'a> {
    None,
    Direct(Option<&'a str>),
    Indirect,
}

impl SuppressPushCtx<'_> {
    const fn indirect_if_active(self) -> Self {
        match self {
            Self::None => Self::None,
            Self::Direct(_) | Self::Indirect => Self::Indirect,
        }
    }
}

/// Variant of [`split_exec_plan_pushdown`] accepting resolved SQL table references
/// (used by the SQLite driver for `--attach` namespaces and unattached `schema.table` fallbacks).
#[must_use]
pub fn split_exec_plan_pushdown_with_table_refs(
    plan: &ExecPlan,
    prog: &ExecProgram,
    db_name: &str,
    dialect: SqlDialect,
    lock: Option<&SchemaLockFile>,
    table_refs: Option<&HashMap<String, String>>,
) -> SplitPlan<ExecPlan> {
    split_exec_plan_pushdown_with_options(plan, prog, db_name, dialect, lock, table_refs, false)
}

/// Variant of [`split_exec_plan_pushdown_with_table_refs`] also threading caller
/// `order_insensitive` (e.g. when splitting the right side of a local unique/semi/anti join).
#[must_use]
pub fn split_exec_plan_pushdown_with_options(
    plan: &ExecPlan,
    prog: &ExecProgram,
    db_name: &str,
    dialect: SqlDialect,
    lock: Option<&SchemaLockFile>,
    table_refs: Option<&HashMap<String, String>>,
    order_insensitive: bool,
) -> SplitPlan<ExecPlan> {
    let ctx = ExecSplitCtx::new(prog, Some(db_name), dialect, lock);
    match split_exec_node(plan, &ctx, order_insensitive, SuppressPushCtx::None, false) {
        NodeSplit::Pushed(node) => {
            SplitPlan::FullyPushed(node.into_query_with_table_refs(dialect, None, table_refs))
        }
        NodeSplit::Hybrid {
            pushed,
            placeholder_var,
            local_plan,
            reason,
        } => {
            if exec_plan_has_source_db(&local_plan, &ctx, Some(db_name)) {
                SplitPlan::LocalOnly {
                    plan: plan.clone(),
                    reason,
                }
            } else {
                SplitPlan::Hybrid {
                    pushdown: pushed.into_query_with_table_refs(dialect, Some(reason), table_refs),
                    placeholder_var,
                    local_suffix: local_plan,
                }
            }
        }
        NodeSplit::LocalOnly { reason } => SplitPlan::LocalOnly {
            plan: plan.clone(),
            reason,
        },
    }
}

/// Collect all independent DB pushdown subtrees inside a Core IR [`Plan`] tree
/// (including separate branches of a cross-DB, DB-vs-local, or unchecked-cardinality join).
#[must_use]
pub fn collect_core_plan_pushdowns(
    plan: &Plan,
    prog: &Program,
    dialect: SqlDialect,
    lock: Option<&SchemaLockFile>,
) -> CollectedPlanPushdowns<Plan> {
    let ctx = CoreSplitCtx::new(prog, None, dialect, lock);
    let mut branches = Vec::new();
    let mut reasons = Vec::new();
    let mut next_id = 0usize;
    let local_plan = collect_core_rec(
        plan,
        &ctx,
        false,
        false,
        &mut next_id,
        &mut branches,
        &mut reasons,
    );
    CollectedPlanPushdowns {
        branches,
        local_plan,
        boundary_reasons: reasons,
    }
}

/// Collect all independent DB pushdown subtrees inside a Phase 2 [`ExecPlan`] tree
/// (including separate branches of a cross-DB, DB-vs-local, or unchecked-cardinality join).
#[must_use]
pub fn collect_exec_plan_pushdowns(
    plan: &ExecPlan,
    prog: &ExecProgram,
    dialect: SqlDialect,
    lock: Option<&SchemaLockFile>,
) -> CollectedPlanPushdowns<ExecPlan> {
    let ctx = ExecSplitCtx::new(prog, None, dialect, lock);
    let mut branches = Vec::new();
    let mut reasons = Vec::new();
    let mut next_id = 0usize;
    let local_plan = collect_exec_rec(
        plan,
        &ctx,
        false,
        SuppressPushCtx::None,
        false,
        &mut next_id,
        &mut branches,
        &mut reasons,
    );
    CollectedPlanPushdowns {
        branches,
        local_plan,
        boundary_reasons: reasons,
    }
}

/// Substitute `ExecPlan::SourceExpr(ExecExpr::Var(name))` leaves with bound [`ExecPlan`]
/// subtrees (for example, binding function table parameters to `SourceDB` arguments from
/// `main` when inspecting cross-function pushdown in `dana explain`).
#[must_use]
pub fn bind_exec_plan_sources(plan: &ExecPlan, bindings: &HashMap<Ident, ExecPlan>) -> ExecPlan {
    match plan {
        ExecPlan::SourceExpr(e) => {
            if let ExecExpr::Var(name) = e.as_ref()
                && let Some(bound) = bindings.get(name)
            {
                return bound.clone();
            }
            plan.clone()
        }
        ExecPlan::SourceDB { .. } => plan.clone(),
        ExecPlan::Select { input, cols } => ExecPlan::Select {
            input: Box::new(bind_exec_plan_sources(input, bindings)),
            cols: cols.clone(),
        },
        ExecPlan::Drop { input, cols } => ExecPlan::Drop {
            input: Box::new(bind_exec_plan_sources(input, bindings)),
            cols: cols.clone(),
        },
        ExecPlan::Rename { input, pairs } => ExecPlan::Rename {
            input: Box::new(bind_exec_plan_sources(input, bindings)),
            pairs: pairs.clone(),
        },
        ExecPlan::Derive { input, items } => ExecPlan::Derive {
            input: Box::new(bind_exec_plan_sources(input, bindings)),
            items: items.clone(),
        },
        ExecPlan::Filter { input, pred } => ExecPlan::Filter {
            input: Box::new(bind_exec_plan_sources(input, bindings)),
            pred: pred.clone(),
        },
        ExecPlan::Distinct { input, cols } => ExecPlan::Distinct {
            input: Box::new(bind_exec_plan_sources(input, bindings)),
            cols: cols.clone(),
        },
        ExecPlan::DedupeBy {
            input,
            keys,
            order_by,
            keep,
        } => ExecPlan::DedupeBy {
            input: Box::new(bind_exec_plan_sources(input, bindings)),
            keys: keys.clone(),
            order_by: order_by.clone(),
            keep: *keep,
        },
        ExecPlan::Sort { input, keys } => ExecPlan::Sort {
            input: Box::new(bind_exec_plan_sources(input, bindings)),
            keys: keys.clone(),
        },
        ExecPlan::Limit { input, n } => ExecPlan::Limit {
            input: Box::new(bind_exec_plan_sources(input, bindings)),
            n: n.clone(),
        },
        ExecPlan::Join {
            kind,
            left,
            right,
            on,
            suffixes,
        } => ExecPlan::Join {
            kind: *kind,
            left: Box::new(bind_exec_plan_sources(left, bindings)),
            right: Box::new(bind_exec_plan_sources(right, bindings)),
            on: on.clone(),
            suffixes: suffixes.clone(),
        },
        ExecPlan::Union { left, right } => ExecPlan::Union {
            left: Box::new(bind_exec_plan_sources(left, bindings)),
            right: Box::new(bind_exec_plan_sources(right, bindings)),
        },
        ExecPlan::GroupBy { input, keys } => ExecPlan::GroupBy {
            input: Box::new(bind_exec_plan_sources(input, bindings)),
            keys: keys.clone(),
        },
        ExecPlan::Summarize {
            input,
            aggs,
            distinct_key,
        } => ExecPlan::Summarize {
            input: Box::new(bind_exec_plan_sources(input, bindings)),
            aggs: aggs.clone(),
            distinct_key: distinct_key.clone(),
        },
        ExecPlan::SuppressSmallGroups {
            input,
            min_k,
            distinct_by,
            mode,
        } => ExecPlan::SuppressSmallGroups {
            input: Box::new(bind_exec_plan_sources(input, bindings)),
            min_k: min_k.clone(),
            distinct_by: distinct_by.clone(),
            mode: *mode,
        },
        ExecPlan::Shuffle { input, seed } => ExecPlan::Shuffle {
            input: Box::new(bind_exec_plan_sources(input, bindings)),
            seed: seed.clone(),
        },
        ExecPlan::SuppressSmallCells {
            input,
            by_cols,
            min_k,
            distinct_by,
        } => ExecPlan::SuppressSmallCells {
            input: Box::new(bind_exec_plan_sources(input, bindings)),
            by_cols: by_cols.clone(),
            min_k: min_k.clone(),
            distinct_by: distinct_by.clone(),
        },
        ExecPlan::Window { input, items } => ExecPlan::Window {
            input: Box::new(bind_exec_plan_sources(input, bindings)),
            items: items.clone(),
        },
        ExecPlan::FillGaps {
            input,
            col,
            step_micros,
            over,
            fill,
        } => ExecPlan::FillGaps {
            input: Box::new(bind_exec_plan_sources(input, bindings)),
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
            input: Box::new(bind_exec_plan_sources(input, bindings)),
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
            input: Box::new(bind_exec_plan_sources(input, bindings)),
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
            input: Box::new(bind_exec_plan_sources(input, bindings)),
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
            input: Box::new(bind_exec_plan_sources(input, bindings)),
            col: col.clone(),
            replacement: replacement.clone(),
        },
        ExecPlan::Pseudonymize { input, col, secret } => ExecPlan::Pseudonymize {
            input: Box::new(bind_exec_plan_sources(input, bindings)),
            col: col.clone(),
            secret: secret.clone(),
        },
    }
}

// ===========================================================================
// Internal Structured SQL AST (Guarantees Exact Left-to-Right Parameter Order)
// ===========================================================================

#[derive(Clone, Debug)]
enum SqlExpr {
    Col {
        table_alias: Option<String>,
        name: String,
    },
    Param {
        slot: SqlParamSlot,
        pg_cast: Option<&'static str>,
    },
    Unary {
        op: &'static str,
        arg: Box<SqlExpr>,
    },
    Binary {
        op: &'static str,
        left: Box<SqlExpr>,
        right: Box<SqlExpr>,
    },
    NullSafeEq {
        negated: bool,
        left: Box<SqlExpr>,
        right: Box<SqlExpr>,
    },
    IsNull {
        negated: bool,
        arg: Box<SqlExpr>,
    },
    CollateC(Box<SqlExpr>),
    Func {
        name: &'static str,
        args: Vec<SqlExpr>,
    },
    Cast {
        expr: Box<SqlExpr>,
        ty: &'static str,
    },
    Case {
        whens: Vec<(SqlExpr, SqlExpr)>,
        else_br: Box<SqlExpr>,
    },
    Coalesce(Box<SqlExpr>, Box<SqlExpr>),
    Exists {
        negated: bool,
        subquery: Box<SqlQuery>,
    },
    CountStar,
    Agg {
        func: &'static str,
        distinct: bool,
        arg: Box<SqlExpr>,
    },
    BoolLit(bool),
    IntLit(i64),
    Substring {
        str_expr: Box<SqlExpr>,
        start: Box<SqlExpr>,
        len: Box<SqlExpr>,
    },
    InList {
        expr: Box<SqlExpr>,
        items: Vec<SqlExpr>,
    },
    TrimAscii(Box<SqlExpr>),
    TryParseIsoDate {
        inner: Box<SqlExpr>,
        already_trimmed: bool,
    },
    ExtractYear(Box<SqlExpr>),
    AtTimeZone {
        expr: Box<SqlExpr>,
        tz: Box<SqlExpr>,
    },
    RowNumber {
        partition_by: Vec<SqlExpr>,
        order_by: Vec<SqlOrderItem>,
    },
}

#[derive(Clone, Debug)]
struct SqlSelectItem {
    expr: SqlExpr,
    alias: String,
}

#[derive(Clone, Copy, Debug)]
enum SqlJoinKind {
    Inner,
    Left,
}

#[derive(Clone, Debug)]
enum SqlFrom {
    Table {
        name: String,
    },
    CteRef {
        cte_name: String,
        alias: String,
    },
    Subquery {
        query: Box<SqlQuery>,
        alias: String,
    },
    Join {
        left: Box<SqlFrom>,
        kind: SqlJoinKind,
        right: Box<SqlFrom>,
        on: SqlExpr,
    },
}

#[derive(Clone, Debug)]
struct SqlOrderItem {
    expr: SqlExpr,
    dir: SortDir,
}

#[derive(Clone, Debug)]
enum SqlQuery {
    Select {
        distinct: bool,
        distinct_on: Vec<SqlExpr>,
        items: Vec<SqlSelectItem>,
        from: Box<SqlFrom>,
        where_clause: Option<SqlExpr>,
        group_by: Vec<SqlExpr>,
        order_by: Vec<SqlOrderItem>,
        limit: Option<SqlParamSlot>,
    },
    UnionAll {
        left: Box<SqlQuery>,
        right: Box<SqlQuery>,
        col_names: Vec<String>,
    },
}

fn sql_from_subquery_depth(from: &SqlFrom) -> usize {
    match from {
        SqlFrom::Table { .. } | SqlFrom::CteRef { .. } => 0,
        SqlFrom::Subquery { query, .. } => 1 + sql_query_subquery_depth(query),
        SqlFrom::Join { left, right, .. } => {
            sql_from_subquery_depth(left).max(sql_from_subquery_depth(right))
        }
    }
}

fn sql_query_subquery_depth(query: &SqlQuery) -> usize {
    match query {
        SqlQuery::Select { from, .. } => sql_from_subquery_depth(from),
        SqlQuery::UnionAll { left, right, .. } => {
            1 + sql_query_subquery_depth(left).max(sql_query_subquery_depth(right))
        }
    }
}

fn select_defines_hoisted_iso(query: &SqlQuery) -> bool {
    matches!(
        query,
        SqlQuery::Select { items, .. }
            if items
                .iter()
                .any(|item| item.alias.starts_with("_dana_iso_")
                    && matches!(item.expr, SqlExpr::TrimAscii(_)))
    )
}

fn sql_from_has_hoisted_iso(from: &SqlFrom) -> bool {
    match from {
        SqlFrom::Table { .. } | SqlFrom::CteRef { .. } => false,
        SqlFrom::Subquery { query, .. } => sql_query_has_hoisted_iso(query),
        SqlFrom::Join { left, right, .. } => {
            sql_from_has_hoisted_iso(left) || sql_from_has_hoisted_iso(right)
        }
    }
}

fn sql_query_has_hoisted_iso(query: &SqlQuery) -> bool {
    if select_defines_hoisted_iso(query) {
        return true;
    }
    match query {
        SqlQuery::Select { from, .. } => sql_from_has_hoisted_iso(from),
        SqlQuery::UnionAll { left, right, .. } => {
            sql_query_has_hoisted_iso(left) || sql_query_has_hoisted_iso(right)
        }
    }
}

fn lift_from(from: &SqlFrom, ctes: &mut Vec<(String, SqlQuery)>) -> SqlFrom {
    match from {
        SqlFrom::Table { .. } | SqlFrom::CteRef { .. } => from.clone(),
        SqlFrom::Subquery { query, alias } => {
            let flat_inner = lift_query(query, ctes);
            let cte_name = format!("_cte_{}", ctes.len());
            ctes.push((cte_name.clone(), flat_inner));
            SqlFrom::CteRef {
                cte_name,
                alias: alias.clone(),
            }
        }
        SqlFrom::Join {
            left,
            kind,
            right,
            on,
        } => SqlFrom::Join {
            left: Box::new(lift_from(left, ctes)),
            kind: *kind,
            right: Box::new(lift_from(right, ctes)),
            on: on.clone(),
        },
    }
}

fn lift_query(query: &SqlQuery, ctes: &mut Vec<(String, SqlQuery)>) -> SqlQuery {
    match query {
        SqlQuery::Select {
            distinct,
            distinct_on,
            items,
            from,
            where_clause,
            group_by,
            order_by,
            limit,
        } => SqlQuery::Select {
            distinct: *distinct,
            distinct_on: distinct_on.clone(),
            items: items.clone(),
            from: Box::new(lift_from(from, ctes)),
            where_clause: where_clause.clone(),
            group_by: group_by.clone(),
            order_by: order_by.clone(),
            limit: limit.clone(),
        },
        SqlQuery::UnionAll {
            left,
            right,
            col_names,
        } => SqlQuery::UnionAll {
            left: Box::new(lift_query(left, ctes)),
            right: Box::new(lift_query(right, ctes)),
            col_names: col_names.clone(),
        },
    }
}

fn lift_subqueries_to_ctes(query: &SqlQuery) -> (Vec<(String, SqlQuery)>, SqlQuery) {
    let mut ctes = Vec::new();
    let root = lift_query(query, &mut ctes);
    (ctes, root)
}

struct SqlRenderState<'a> {
    dialect: SqlDialect,
    sql: String,
    params: Vec<SqlParamSlot>,
    table_refs: Option<&'a HashMap<String, String>>,
}

impl<'a> SqlRenderState<'a> {
    fn with_table_refs(
        dialect: SqlDialect,
        table_refs: Option<&'a HashMap<String, String>>,
    ) -> Self {
        Self {
            dialect,
            sql: String::new(),
            params: Vec::new(),
            table_refs,
        }
    }

    fn emit_param(&mut self, slot: &SqlParamSlot, pg_cast: Option<&'static str>) {
        self.params.push(slot.clone());
        match self.dialect {
            SqlDialect::Sqlite => self.sql.push('?'),
            SqlDialect::Postgres => {
                let idx = self.params.len();
                if let Some(ty) = pg_cast {
                    let _ = write!(self.sql, "CAST(${idx} AS {ty})");
                } else {
                    let _ = write!(self.sql, "${idx}");
                }
            }
        }
    }

    fn render_root_query(&mut self, query: &SqlQuery) {
        let should_lift = sql_query_subquery_depth(query) >= 4
            || (self.dialect == SqlDialect::Postgres && sql_query_has_hoisted_iso(query));
        if should_lift {
            let (ctes, root) = lift_subqueries_to_ctes(query);
            self.sql.push_str("WITH ");
            for (idx, (cte_name, cte_query)) in ctes.iter().enumerate() {
                if idx > 0 {
                    self.sql.push_str(", ");
                }
                self.sql.push_str(&quote_sql_ident(cte_name));
                if self.dialect == SqlDialect::Postgres && select_defines_hoisted_iso(cte_query) {
                    self.sql.push_str(" AS MATERIALIZED (");
                } else {
                    self.sql.push_str(" AS (");
                }
                self.render_query(cte_query);
                self.sql.push(')');
            }
            self.sql.push(' ');
            self.render_query(&root);
        } else {
            self.render_query(query);
        }
    }

    fn render_query(&mut self, query: &SqlQuery) {
        match query {
            SqlQuery::Select {
                distinct,
                distinct_on,
                items,
                from,
                where_clause,
                group_by,
                order_by,
                limit,
            } => {
                self.sql.push_str("SELECT ");
                if !distinct_on.is_empty() {
                    self.sql.push_str("DISTINCT ON (");
                    for (i, e) in distinct_on.iter().enumerate() {
                        if i > 0 {
                            self.sql.push_str(", ");
                        }
                        self.render_expr(e);
                    }
                    self.sql.push_str(") ");
                } else if *distinct {
                    self.sql.push_str("DISTINCT ");
                }
                for (i, item) in items.iter().enumerate() {
                    if i > 0 {
                        self.sql.push_str(", ");
                    }
                    self.render_expr(&item.expr);
                    self.sql.push_str(" AS ");
                    self.sql.push_str(&quote_sql_ident(&item.alias));
                }
                self.sql.push_str(" FROM ");
                self.render_from(from);
                if let Some(w) = where_clause {
                    self.sql.push_str(" WHERE ");
                    self.render_expr(w);
                }
                if !group_by.is_empty() {
                    self.sql.push_str(" GROUP BY ");
                    for (i, g) in group_by.iter().enumerate() {
                        if i > 0 {
                            self.sql.push_str(", ");
                        }
                        self.render_expr(g);
                    }
                }
                if !order_by.is_empty() {
                    self.sql.push_str(" ORDER BY ");
                    for (i, o) in order_by.iter().enumerate() {
                        if i > 0 {
                            self.sql.push_str(", ");
                        }
                        self.render_expr(&o.expr);
                        match o.dir {
                            SortDir::Asc => self.sql.push_str(" ASC NULLS FIRST"),
                            SortDir::Desc => self.sql.push_str(" DESC NULLS LAST"),
                        }
                    }
                }
                if let Some(lim) = limit {
                    self.sql.push_str(" LIMIT ");
                    self.emit_param(lim, Some("BIGINT"));
                }
            }
            SqlQuery::UnionAll {
                left,
                right,
                col_names,
            } => {
                self.sql.push_str("SELECT ");
                for (i, c) in col_names.iter().enumerate() {
                    if i > 0 {
                        self.sql.push_str(", ");
                    }
                    let q = quote_sql_ident(c);
                    let _ = write!(self.sql, "\"_u1\".{q} AS {q}");
                }
                self.sql.push_str(" FROM (");
                self.render_query(left);
                self.sql.push_str(") AS \"_u1\" UNION ALL SELECT ");
                for (i, c) in col_names.iter().enumerate() {
                    if i > 0 {
                        self.sql.push_str(", ");
                    }
                    let q = quote_sql_ident(c);
                    let _ = write!(self.sql, "\"_u2\".{q} AS {q}");
                }
                self.sql.push_str(" FROM (");
                self.render_query(right);
                self.sql.push_str(") AS \"_u2\"");
            }
        }
    }

    fn render_from(&mut self, from: &SqlFrom) {
        match from {
            SqlFrom::Table { name } => {
                if let Some(resolved) = self.table_refs.and_then(|m| m.get(name)) {
                    self.sql.push_str(resolved);
                } else {
                    self.sql.push_str(&quote_sql_table_ref(name));
                }
            }
            SqlFrom::CteRef { cte_name, alias } => {
                self.sql.push_str(&quote_sql_ident(cte_name));
                self.sql.push_str(" AS ");
                self.sql.push_str(&quote_sql_ident(alias));
            }
            SqlFrom::Subquery { query, alias } => {
                self.sql.push('(');
                self.render_query(query);
                self.sql.push_str(") AS ");
                self.sql.push_str(&quote_sql_ident(alias));
            }
            SqlFrom::Join {
                left,
                kind,
                right,
                on,
            } => {
                self.render_from(left);
                match kind {
                    SqlJoinKind::Inner => self.sql.push_str(" INNER JOIN "),
                    SqlJoinKind::Left => self.sql.push_str(" LEFT JOIN "),
                }
                self.render_from(right);
                self.sql.push_str(" ON ");
                self.render_expr(on);
            }
        }
    }

    fn render_expr(&mut self, expr: &SqlExpr) {
        match expr {
            SqlExpr::Col { table_alias, name } => {
                if let Some(a) = table_alias {
                    self.sql.push_str(&quote_sql_ident(a));
                    self.sql.push('.');
                }
                self.sql.push_str(&quote_sql_ident(name));
            }
            SqlExpr::Param { slot, pg_cast } => self.emit_param(slot, *pg_cast),
            SqlExpr::Unary { op, arg } => {
                self.sql.push('(');
                self.sql.push_str(op);
                self.sql.push(' ');
                self.render_expr(arg);
                self.sql.push(')');
            }
            SqlExpr::Binary { op, left, right } => {
                self.sql.push('(');
                self.render_expr(left);
                self.sql.push(' ');
                self.sql.push_str(op);
                self.sql.push(' ');
                self.render_expr(right);
                self.sql.push(')');
            }
            SqlExpr::NullSafeEq {
                negated,
                left,
                right,
            } => {
                self.sql.push('(');
                self.render_expr(left);
                match (self.dialect, *negated) {
                    (SqlDialect::Sqlite, false) => self.sql.push_str(" IS "),
                    (SqlDialect::Sqlite, true) => self.sql.push_str(" IS NOT "),
                    (SqlDialect::Postgres, false) => self.sql.push_str(" IS NOT DISTINCT FROM "),
                    (SqlDialect::Postgres, true) => self.sql.push_str(" IS DISTINCT FROM "),
                }
                self.render_expr(right);
                self.sql.push(')');
            }
            SqlExpr::IsNull { negated, arg } => {
                self.sql.push('(');
                self.render_expr(arg);
                if *negated {
                    self.sql.push_str(" IS NOT NULL)");
                } else {
                    self.sql.push_str(" IS NULL)");
                }
            }
            SqlExpr::CollateC(inner) => {
                self.render_expr(inner);
                if self.dialect == SqlDialect::Postgres {
                    self.sql.push_str(" COLLATE \"C\"");
                }
            }
            SqlExpr::Func { name, args } => {
                self.sql.push_str(name);
                self.sql.push('(');
                for (i, a) in args.iter().enumerate() {
                    if i > 0 {
                        self.sql.push_str(", ");
                    }
                    self.render_expr(a);
                }
                self.sql.push(')');
            }
            SqlExpr::Cast { expr, ty } => {
                self.sql.push_str("CAST(");
                self.render_expr(expr);
                self.sql.push_str(" AS ");
                self.sql.push_str(ty);
                self.sql.push(')');
            }
            SqlExpr::Case { whens, else_br } => {
                self.sql.push_str("(CASE");
                for (cond, then_e) in whens {
                    self.sql.push_str(" WHEN ");
                    self.render_expr(cond);
                    self.sql.push_str(" THEN ");
                    self.render_expr(then_e);
                }
                self.sql.push_str(" ELSE ");
                self.render_expr(else_br);
                self.sql.push_str(" END)");
            }
            SqlExpr::Coalesce(opt_e, def_e) => {
                self.sql.push_str("COALESCE(");
                self.render_expr(opt_e);
                self.sql.push_str(", ");
                self.render_expr(def_e);
                self.sql.push(')');
            }
            SqlExpr::Exists { negated, subquery } => {
                if *negated {
                    self.sql.push_str("NOT EXISTS (");
                } else {
                    self.sql.push_str("EXISTS (");
                }
                self.render_query(subquery);
                self.sql.push(')');
            }
            SqlExpr::CountStar => self.sql.push_str("COUNT(*)"),
            SqlExpr::Agg {
                func,
                distinct,
                arg,
            } => {
                self.sql.push_str(func);
                self.sql.push('(');
                if *distinct {
                    self.sql.push_str("DISTINCT ");
                }
                self.render_expr(arg);
                self.sql.push(')');
            }
            SqlExpr::BoolLit(b) => match (self.dialect, *b) {
                (SqlDialect::Sqlite, true) => self.sql.push('1'),
                (SqlDialect::Sqlite, false) => self.sql.push('0'),
                (SqlDialect::Postgres, true) => self.sql.push_str("TRUE"),
                (SqlDialect::Postgres, false) => self.sql.push_str("FALSE"),
            },
            SqlExpr::IntLit(n) => {
                let _ = write!(self.sql, "{n}");
            }
            SqlExpr::Substring {
                str_expr,
                start,
                len,
            } => match self.dialect {
                SqlDialect::Sqlite => {
                    self.sql.push_str("SUBSTR(");
                    self.render_expr(str_expr);
                    self.sql.push_str(", ");
                    self.render_expr(start);
                    self.sql.push_str(", ");
                    self.render_expr(len);
                    self.sql.push(')');
                }
                SqlDialect::Postgres => {
                    self.sql.push_str("SUBSTRING(");
                    self.render_expr(str_expr);
                    self.sql.push_str(" FROM ");
                    self.render_expr(start);
                    self.sql.push_str(" FOR ");
                    self.render_expr(len);
                    self.sql.push(')');
                }
            },
            SqlExpr::InList { expr, items } => {
                self.sql.push('(');
                self.render_expr(expr);
                self.sql.push_str(" IN (");
                for (i, item) in items.iter().enumerate() {
                    if i > 0 {
                        self.sql.push_str(", ");
                    }
                    self.render_expr(item);
                }
                self.sql.push_str("))");
            }
            SqlExpr::TrimAscii(inner) => {
                self.render_trimmed_ascii(inner);
            }
            SqlExpr::TryParseIsoDate {
                inner,
                already_trimmed,
            } => {
                self.render_try_parse_iso_date(inner, *already_trimmed);
            }
            SqlExpr::ExtractYear(inner) => {
                self.sql.push_str("CAST(EXTRACT(YEAR FROM ");
                self.render_expr(inner);
                self.sql.push_str(") AS BIGINT)");
            }
            SqlExpr::AtTimeZone { expr, tz } => {
                self.sql.push('(');
                self.render_expr(expr);
                self.sql.push_str(" AT TIME ZONE ");
                self.render_expr(tz);
                self.sql.push(')');
            }
            SqlExpr::RowNumber {
                partition_by,
                order_by,
            } => {
                self.sql.push_str("ROW_NUMBER() OVER (");
                if !partition_by.is_empty() {
                    self.sql.push_str("PARTITION BY ");
                    for (i, e) in partition_by.iter().enumerate() {
                        if i > 0 {
                            self.sql.push_str(", ");
                        }
                        self.render_expr(e);
                    }
                    if !order_by.is_empty() {
                        self.sql.push(' ');
                    }
                }
                if !order_by.is_empty() {
                    self.sql.push_str("ORDER BY ");
                    for (i, o) in order_by.iter().enumerate() {
                        if i > 0 {
                            self.sql.push_str(", ");
                        }
                        self.render_expr(&o.expr);
                        match o.dir {
                            SortDir::Asc => self.sql.push_str(" ASC NULLS FIRST"),
                            SortDir::Desc => self.sql.push_str(" DESC NULLS LAST"),
                        }
                    }
                }
                self.sql.push(')');
            }
        }
    }

    fn render_trimmed_ascii(&mut self, inner: &SqlExpr) {
        match self.dialect {
            SqlDialect::Sqlite => {
                self.sql.push_str("TRIM(");
                self.render_expr(inner);
                self.sql.push_str(", char(32, 9, 10, 13))");
            }
            SqlDialect::Postgres => {
                self.sql.push_str("BTRIM(");
                self.render_expr(inner);
                self.sql
                    .push_str(", CHR(32) || CHR(9) || CHR(10) || CHR(13))");
            }
        }
    }

    fn render_iso_source(&mut self, inner: &SqlExpr, already_trimmed: bool) {
        if already_trimmed {
            self.render_expr(inner);
        } else {
            self.render_trimmed_ascii(inner);
        }
    }

    fn render_substr_slice(
        &mut self,
        inner: &SqlExpr,
        already_trimmed: bool,
        start: usize,
        len: usize,
    ) {
        match self.dialect {
            SqlDialect::Sqlite => {
                self.sql.push_str("SUBSTR(");
                self.render_iso_source(inner, already_trimmed);
                let _ = write!(self.sql, ", {start}, {len})");
            }
            SqlDialect::Postgres => {
                self.sql.push_str("SUBSTRING(");
                self.render_iso_source(inner, already_trimmed);
                let _ = write!(self.sql, " FROM {start} FOR {len})");
            }
        }
    }

    fn render_try_parse_iso_date(&mut self, inner: &SqlExpr, already_trimmed: bool) {
        self.sql.push_str("(CASE WHEN (");
        self.render_iso_source(inner, already_trimmed);
        match self.dialect {
            SqlDialect::Sqlite => {
                self.sql.push_str(
                    " GLOB '[0-9][0-9][0-9][0-9]-[0-9][0-9]-[0-9][0-9]') THEN (CASE WHEN ((",
                );
            }
            SqlDialect::Postgres => {
                self.sql
                    .push_str(" ~ '^[0-9]{4}-[0-9]{2}-[0-9]{2}$') THEN (CASE WHEN ((");
            }
        }
        self.render_substr_slice(inner, already_trimmed, 1, 4);
        self.sql.push_str(" <> '0000') AND (");
        // Months with 31 days
        self.sql.push('(');
        self.render_substr_slice(inner, already_trimmed, 6, 2);
        self.sql
            .push_str(" IN ('01','03','05','07','08','10','12') AND ");
        self.render_substr_slice(inner, already_trimmed, 9, 2);
        self.sql.push_str(" >= '01' AND ");
        self.render_substr_slice(inner, already_trimmed, 9, 2);
        self.sql.push_str(" <= '31')");
        // Months with 30 days
        self.sql.push_str(" OR (");
        self.render_substr_slice(inner, already_trimmed, 6, 2);
        self.sql.push_str(" IN ('04','06','09','11') AND ");
        self.render_substr_slice(inner, already_trimmed, 9, 2);
        self.sql.push_str(" >= '01' AND ");
        self.render_substr_slice(inner, already_trimmed, 9, 2);
        self.sql.push_str(" <= '30')");
        // February with proleptic Gregorian leap-year check
        self.sql.push_str(" OR (");
        self.render_substr_slice(inner, already_trimmed, 6, 2);
        self.sql.push_str(" = '02' AND ");
        self.render_substr_slice(inner, already_trimmed, 9, 2);
        self.sql.push_str(" >= '01' AND ");
        self.render_substr_slice(inner, already_trimmed, 9, 2);
        self.sql.push_str(" <= (CASE WHEN ((CAST(");
        self.render_substr_slice(inner, already_trimmed, 1, 4);
        self.sql.push_str(" AS INTEGER) % 4 = 0 AND CAST(");
        self.render_substr_slice(inner, already_trimmed, 1, 4);
        self.sql.push_str(" AS INTEGER) % 100 <> 0) OR (CAST(");
        self.render_substr_slice(inner, already_trimmed, 1, 4);
        self.sql
            .push_str(" AS INTEGER) % 400 = 0)) THEN '29' ELSE '28' END))");
        match self.dialect {
            SqlDialect::Sqlite => {
                self.sql.push_str(")) THEN ");
                self.render_iso_source(inner, already_trimmed);
                self.sql.push_str(" ELSE NULL END) ELSE NULL END)");
            }
            SqlDialect::Postgres => {
                self.sql.push_str(")) THEN CAST(");
                self.render_iso_source(inner, already_trimmed);
                self.sql.push_str(
                    " AS DATE) ELSE CAST(NULL AS DATE) END) ELSE CAST(NULL AS DATE) END)",
                );
            }
        }
    }
}

// ===========================================================================
// Dialect Type & Literal Soundness Rules
// ===========================================================================

/// Return the PostgreSQL SQL type name for `CAST($k AS <ty>)`.
const fn pg_sql_type_name(ty: &ScalarTy) -> Option<&'static str> {
    match base_scalar_const(ty) {
        ScalarTy::Bool => Some("BOOLEAN"),
        ScalarTy::Int => Some("BIGINT"),
        ScalarTy::Decimal => Some("NUMERIC"),
        ScalarTy::Float => Some("DOUBLE PRECISION"),
        ScalarTy::Text => Some("TEXT"),
        ScalarTy::Bytes => Some("BYTEA"),
        ScalarTy::Date => Some("DATE"),
        ScalarTy::Timestamp => Some("TIMESTAMPTZ"),
        ScalarTy::Duration => Some("INTERVAL"),
        ScalarTy::Unit | ScalarTy::Data(_) | ScalarTy::Option(_) => None,
    }
}

const fn base_scalar_const(ty: &ScalarTy) -> &ScalarTy {
    match ty {
        ScalarTy::Option(inner) => inner,
        other => other,
    }
}

/// Returns `true` if a column of type `ty` can be stored and retrieved losslessly via SQL.
fn is_sql_column_supported(ty: &ScalarTy) -> bool {
    !matches!(base_of_scalar(ty), ScalarTy::Unit | ScalarTy::Data(_))
}

/// Returns `true` if `Eq` / `Ne` / `GROUP BY` / `JOIN` / `DISTINCT` on `ty` is 100% dialect-exact.
fn is_dialect_exact_eq(dialect: SqlDialect, ty: &ScalarTy) -> bool {
    matches!(
        (dialect, base_of_scalar(ty)),
        (
            _,
            ScalarTy::Bool
                | ScalarTy::Int
                | ScalarTy::Text
                | ScalarTy::Date
                | ScalarTy::Duration
                | ScalarTy::Bytes,
        ) | (
            SqlDialect::Postgres,
            ScalarTy::Decimal | ScalarTy::Timestamp
        )
    )
}

/// Returns `true` if `<` / `<=` / `>` / `>=` / `ORDER BY` / `MIN` / `MAX` on `ty` is 100% dialect-exact.
fn is_dialect_exact_ord(dialect: SqlDialect, ty: &ScalarTy) -> bool {
    matches!(
        (dialect, base_of_scalar(ty)),
        (
            _,
            ScalarTy::Bool | ScalarTy::Int | ScalarTy::Text | ScalarTy::Date | ScalarTy::Duration,
        ) | (
            SqlDialect::Postgres,
            ScalarTy::Decimal | ScalarTy::Timestamp
        )
    )
}

fn non_exact_type_reason(dialect: SqlDialect, ty: &ScalarTy, op_name: &str) -> String {
    match (dialect, base_of_scalar(ty)) {
        (_, ScalarTy::Float) => {
            format!("IEEE-754 total-order Float semantics in {op_name} require local VM")
        }
        (SqlDialect::Sqlite, ScalarTy::Decimal) => {
            format!("SQLite TEXT-encoded Decimal {op_name} requires local VM")
        }
        (SqlDialect::Sqlite, ScalarTy::Timestamp) => {
            format!("SQLite ISO-text Timestamp {op_name} requires local VM")
        }
        (_, other) => format!("unsupported scalar type `{other:?}` in {op_name} requires local VM"),
    }
}

/// Days range corresponding to 4-digit non-negative ISO years `0000-01-01` .. `9999-12-31`.
const ISO_4DIGIT_MIN_DAYS: i64 = -719_528;
const ISO_4DIGIT_MAX_DAYS: i64 = 2_932_896;

fn literal_to_sql_param(
    lit: &Literal,
    dialect: SqlDialect,
) -> Result<(SqlParam, ScalarTy, Option<&'static str>), String> {
    match lit {
        Literal::Bool(b) => Ok((SqlParam::Bool(*b), ScalarTy::Bool, Some("BOOLEAN"))),
        Literal::Int(n) => {
            let v = n
                .to_i64()
                .ok_or_else(|| "Int literal outside i64 range requires local VM".to_string())?;
            Ok((SqlParam::Int(v), ScalarTy::Int, Some("BIGINT")))
        }
        Literal::Decimal(d) => {
            if !d.in_decimal_range() {
                return Err("Decimal literal outside 128-bit range requires local VM".to_string());
            }
            Ok((
                SqlParam::Decimal(d.clone()),
                ScalarTy::Decimal,
                Some("NUMERIC"),
            ))
        }
        Literal::Float(f) => {
            if f.is_nan() || !f.to_f64().is_finite() {
                return Err("non-finite Float literal requires local VM".to_string());
            }
            Ok((
                SqlParam::Float(*f),
                ScalarTy::Float,
                Some("DOUBLE PRECISION"),
            ))
        }
        Literal::Text(s) => Ok((SqlParam::Text(s.clone()), ScalarTy::Text, Some("TEXT"))),
        Literal::Bytes(bs) => Ok((SqlParam::Bytes(bs.clone()), ScalarTy::Bytes, Some("BYTEA"))),
        Literal::Date(d) => {
            let days = d
                .to_i64()
                .ok_or_else(|| "Date literal outside i64 range requires local VM".to_string())?;
            if dialect == SqlDialect::Sqlite
                && !(ISO_4DIGIT_MIN_DAYS..=ISO_4DIGIT_MAX_DAYS).contains(&days)
            {
                return Err(
                    "SQLite ISO Date outside 4-digit year range requires local VM".to_string(),
                );
            }
            Ok((SqlParam::Date(days), ScalarTy::Date, Some("DATE")))
        }
        Literal::Timestamp(ts) => {
            let us = ts.to_i64().ok_or_else(|| {
                "Timestamp literal outside i64 range requires local VM".to_string()
            })?;
            Ok((
                SqlParam::Timestamp(us),
                ScalarTy::Timestamp,
                Some("TIMESTAMPTZ"),
            ))
        }
        Literal::Duration(dur) => {
            let us = dur.to_i64().ok_or_else(|| {
                "Duration literal outside i64 range requires local VM".to_string()
            })?;
            Ok((SqlParam::Duration(us), ScalarTy::Duration, Some("INTERVAL")))
        }
        Literal::NoneLit(inner_ty) => {
            let Some(sty) = inner_ty.to_scalar_ty() else {
                return Err("non-scalar none literal requires local VM".to_string());
            };
            if !is_sql_column_supported(&sty) {
                return Err(format!(
                    "unsupported none literal type `{sty:?}` requires local VM"
                ));
            }
            let cast = pg_sql_type_name(&sty);
            Ok((SqlParam::Null, ScalarTy::Option(Box::new(sty)), cast))
        }
        Literal::Unit => Err("Unit literal cannot be pushed into SQL".to_string()),
    }
}

// ===========================================================================
// Pushed Subtree State & Shared SQL Algebraic Builders
// ===========================================================================

#[derive(Clone, Debug)]
struct PushedNode {
    db_name: Ident,
    query: SqlQuery,
    schema: TableTy,
    unique_keys: Vec<Vec<Ident>>,
    pushed_ops: Vec<String>,
    deterministic_order: bool,
    needs_wrap_for_filter: bool,
    needs_wrap_for_proj: bool,
    next_alias_id: usize,
}

type TranslatedAggSpec = (Ident, ExecAggOp, Option<(SqlExpr, ScalarTy, TagSet)>);

impl PushedNode {
    fn fresh_alias(&mut self, prefix: &str) -> String {
        self.next_alias_id += 1;
        format!("_{prefix}{}", self.next_alias_id)
    }

    fn into_query(self, dialect: SqlDialect, boundary_reason: Option<String>) -> SqlPushdownQuery {
        self.into_query_with_table_refs(dialect, boundary_reason, None)
    }

    fn into_query_with_table_refs(
        self,
        dialect: SqlDialect,
        boundary_reason: Option<String>,
        table_refs: Option<&HashMap<String, String>>,
    ) -> SqlPushdownQuery {
        let mut renderer = SqlRenderState::with_table_refs(dialect, table_refs);
        renderer.render_root_query(&self.query);
        SqlPushdownQuery {
            db_name: self.db_name,
            dialect,
            sql: renderer.sql,
            param_slots: renderer.params,
            out_schema: self.schema,
            pushed_ops: self.pushed_ops,
            boundary_reason,
        }
    }

    fn keys_proven_unique(&self, candidate: &[Ident]) -> bool {
        self.unique_keys
            .iter()
            .any(|uk| uk.iter().all(|k| candidate.contains(k)))
    }

    fn wrap_as_subquery(mut self) -> Self {
        let alias = self.fresh_alias("q");
        let items: Vec<SqlSelectItem> = self
            .schema
            .cols
            .iter()
            .map(|c| SqlSelectItem {
                expr: SqlExpr::Col {
                    table_alias: None,
                    name: c.name.clone(),
                },
                alias: c.name.clone(),
            })
            .collect();
        let inner = Box::new(self.query);
        self.query = SqlQuery::Select {
            distinct: false,
            distinct_on: Vec::new(),
            items,
            from: Box::new(SqlFrom::Subquery {
                query: inner,
                alias,
            }),
            where_clause: None,
            group_by: Vec::new(),
            order_by: Vec::new(),
            limit: None,
        };
        self.needs_wrap_for_filter = false;
        self.needs_wrap_for_proj = false;
        self
    }

    fn from_source_db(
        db_name: &str,
        table_name: &str,
        schema: &TableTy,
        lock: Option<&SchemaLockFile>,
        dialect: SqlDialect,
    ) -> Result<Self, String> {
        if schema.cols.is_empty() {
            return Err("empty table schema cannot be pushed to SQL".to_string());
        }
        for c in &schema.cols {
            if !is_sql_column_supported(&c.ty) {
                return Err(format!(
                    "column `{}` has non-SQL scalar type `{:?}`",
                    c.name, c.ty
                ));
            }
        }
        let mut has_pg_text_cast = false;
        let items: Vec<SqlSelectItem> = schema
            .cols
            .iter()
            .map(|c| {
                let base_col = SqlExpr::Col {
                    table_alias: None,
                    name: c.name.clone(),
                };
                // Normalize Postgres text-mapped columns (`ENUM`, `UUID`, `JSONB`, `VARCHAR`,
                // `TEXT`) to `TEXT` at the scan boundary so pushed filters, collations, and
                // string functions never fail on custom type OIDs.
                let expr = if dialect == SqlDialect::Postgres
                    && matches!(base_of_scalar(&c.ty), ScalarTy::Text)
                {
                    has_pg_text_cast = true;
                    SqlExpr::Cast {
                        expr: Box::new(base_col),
                        ty: "TEXT",
                    }
                } else {
                    base_col
                };
                SqlSelectItem {
                    expr,
                    alias: c.name.clone(),
                }
            })
            .collect();
        let mut unique_keys = Vec::new();
        if let Some(pk_cols) = lock
            .and_then(|l| l.find_db(db_name))
            .and_then(|d| d.resolve_table(table_name).ok())
            .map(|t| {
                t.cols
                    .iter()
                    .filter(|c| c.pk)
                    .map(|c| c.name.clone())
                    .collect::<Vec<_>>()
            })
            && !pk_cols.is_empty()
            && pk_cols.iter().all(|pk| schema.find_col(pk).is_some())
        {
            unique_keys.push(pk_cols);
        }
        Ok(Self {
            db_name: db_name.to_string(),
            query: SqlQuery::Select {
                distinct: false,
                distinct_on: Vec::new(),
                items,
                from: Box::new(SqlFrom::Table {
                    name: table_name.to_string(),
                }),
                where_clause: None,
                group_by: Vec::new(),
                order_by: Vec::new(),
                limit: None,
            },
            schema: schema.clone(),
            unique_keys,
            pushed_ops: vec![format!("SourceDB({table_name})")],
            deterministic_order: true,
            needs_wrap_for_filter: has_pg_text_cast,
            needs_wrap_for_proj: false,
            next_alias_id: 0,
        })
    }

    fn apply_select(mut self, cols: &[Ident]) -> Result<Self, String> {
        if cols.is_empty() {
            return Err("empty Select cannot be pushed to SQL".to_string());
        }
        let mut out_cols = Vec::with_capacity(cols.len());
        for name in cols {
            let Some(c) = self.schema.find_col(name) else {
                return Err(format!("Select references missing column `{name}`"));
            };
            out_cols.push(ColSpec {
                agg_kind: AggKind::Raw,
                ..c.clone()
            });
        }
        if self.needs_wrap_for_proj {
            self = self.wrap_as_subquery();
        }
        if let SqlQuery::Select { items, .. } = &mut self.query {
            let item_map: HashMap<String, SqlExpr> = items
                .iter()
                .map(|it| (it.alias.clone(), it.expr.clone()))
                .collect();
            let mut next_items = Vec::with_capacity(cols.len());
            for name in cols {
                let expr = item_map.get(name).cloned().unwrap_or_else(|| SqlExpr::Col {
                    table_alias: None,
                    name: name.clone(),
                });
                next_items.push(SqlSelectItem {
                    expr,
                    alias: name.clone(),
                });
            }
            *items = next_items;
        }
        self.unique_keys
            .retain(|uk| uk.iter().all(|k| cols.contains(k)));
        self.schema = TableTy {
            cols: out_cols,
            row_tags: self.schema.row_tags,
            order_tags: self.schema.order_tags,
            grouped_by: None,
            summarized: false,
            distinct_by: None,
        };
        self.pushed_ops
            .push(format!("Select([{}])", cols.join(", ")));
        Ok(self)
    }

    fn apply_drop(self, cols: &[Ident]) -> Result<Self, String> {
        let kept: Vec<Ident> = self
            .schema
            .cols
            .iter()
            .filter(|c| !cols.contains(&c.name))
            .map(|c| c.name.clone())
            .collect();
        if kept.is_empty() {
            return Err("Drop removed every column".to_string());
        }
        let mut node = self.apply_select(&kept)?;
        if let Some(last) = node.pushed_ops.last_mut() {
            *last = format!("Drop([{}])", cols.join(", "));
        }
        Ok(node)
    }

    /// Apply column renames given canonical `(old_name, new_name)` pairs.
    fn apply_rename(mut self, old_to_new: &[(Ident, Ident)]) -> Result<Self, String> {
        if old_to_new.is_empty() {
            return Ok(self);
        }
        let rename_map: HashMap<&str, &str> = old_to_new
            .iter()
            .map(|(old_n, new_n)| (old_n.as_str(), new_n.as_str()))
            .collect();
        for (old_n, _) in old_to_new {
            if self.schema.find_col(old_n).is_none() {
                return Err(format!("Rename references missing column `{old_n}`"));
            }
        }
        if self.needs_wrap_for_proj {
            self = self.wrap_as_subquery();
        }
        let out_cols: Vec<ColSpec> = self
            .schema
            .cols
            .iter()
            .map(|c| {
                let new_name = rename_map
                    .get(c.name.as_str())
                    .map_or_else(|| c.name.clone(), |s| (*s).to_string());
                ColSpec {
                    name: new_name,
                    agg_kind: AggKind::Raw,
                    ..c.clone()
                }
            })
            .collect();
        if let SqlQuery::Select { items, .. } = &mut self.query {
            for item in items.iter_mut() {
                if let Some(&new_n) = rename_map.get(item.alias.as_str()) {
                    item.alias = new_n.to_string();
                }
            }
        }
        for uk in &mut self.unique_keys {
            for k in uk.iter_mut() {
                if let Some(&new_n) = rename_map.get(k.as_str()) {
                    *k = new_n.to_string();
                }
            }
        }
        self.schema = TableTy {
            cols: out_cols,
            row_tags: self.schema.row_tags,
            order_tags: self.schema.order_tags,
            grouped_by: None,
            summarized: false,
            distinct_by: None,
        };
        // Subsequent filters reference the renamed column names, so wrap before filtering.
        self.needs_wrap_for_filter = true;
        let desc: Vec<String> = old_to_new
            .iter()
            .map(|(o, n)| format!("{n}<-{o}"))
            .collect();
        self.pushed_ops
            .push(format!("Rename([{}])", desc.join(", ")));
        Ok(self)
    }

    /// Hoist any `TryParseIsoDate` trim subexpressions across `exprs` into shared inner subquery
    /// columns so the 15 validation checks never duplicate inner SQL parameters and independent
    /// derive columns share a single materialized CTE.
    fn hoist_try_parse_iso_dates_batch(mut self, mut exprs: Vec<SqlExpr>) -> (Self, Vec<SqlExpr>) {
        loop {
            let mut hoisted = Vec::new();
            let mut next_id = self.next_alias_id;
            for expr in &mut exprs {
                let taken = std::mem::replace(expr, SqlExpr::BoolLit(false));
                *expr =
                    rewrite_leaf_try_parse_dates(taken, &self.schema, &mut next_id, &mut hoisted);
            }
            self.next_alias_id = next_id;
            if hoisted.is_empty() {
                return (self, exprs);
            }
            let must_wrap = self.needs_wrap_for_proj
                || self.needs_wrap_for_filter
                || matches!(
                    &self.query,
                    SqlQuery::Select {
                        distinct,
                        distinct_on,
                        where_clause,
                        group_by,
                        limit,
                        ..
                    } if *distinct
                        || !distinct_on.is_empty()
                        || where_clause.is_some()
                        || !group_by.is_empty()
                        || limit.is_some()
                );
            if must_wrap {
                self = self.wrap_as_subquery();
            }
            if let SqlQuery::Select { items, .. } = &mut self.query {
                for (alias, trim_expr) in hoisted {
                    items.push(SqlSelectItem {
                        expr: trim_expr,
                        alias,
                    });
                }
            }
            self = self.wrap_as_subquery();
        }
    }

    fn hoist_try_parse_iso_dates(self, expr: SqlExpr) -> (Self, SqlExpr) {
        let (wrapped, exprs) = self.hoist_try_parse_iso_dates_batch(vec![expr]);
        let out = exprs.into_iter().next().unwrap_or(SqlExpr::BoolLit(false));
        (wrapped, out)
    }

    fn apply_filter(mut self, pred_expr: SqlExpr, pred_tags: &TagSet) -> Self {
        let pred_expr = simplify_coalesce_pred(pred_expr);
        let (wrapped, pred_expr) = self.hoist_try_parse_iso_dates(pred_expr);
        self = wrapped;
        if self.needs_wrap_for_filter {
            self = self.wrap_as_subquery();
        }
        if let SqlQuery::Select { where_clause, .. } = &mut self.query {
            *where_clause = Some(match where_clause.take() {
                None => pred_expr,
                Some(prev) => SqlExpr::Binary {
                    op: "AND",
                    left: Box::new(prev),
                    right: Box::new(pred_expr),
                },
            });
        }
        self.schema = TableTy {
            cols: self
                .schema
                .cols
                .into_iter()
                .map(|c| ColSpec {
                    agg_kind: AggKind::Raw,
                    ..c
                })
                .collect(),
            row_tags: self.schema.row_tags.union(pred_tags),
            order_tags: self.schema.order_tags,
            grouped_by: None,
            summarized: false,
            distinct_by: None,
        };
        self.pushed_ops.push("Filter".to_string());
        self
    }

    fn apply_derive_wave(mut self, wave: Vec<(Ident, SqlExpr, ColSpec)>) -> Self {
        if wave.is_empty() {
            return self;
        }
        let mut meta = Vec::with_capacity(wave.len());
        let mut exprs = Vec::with_capacity(wave.len());
        for (name, expr, spec) in wave {
            meta.push((name, spec));
            exprs.push(expr);
        }
        let (wrapped, exprs) = self.hoist_try_parse_iso_dates_batch(exprs);
        self = wrapped;
        // Wrap first so derived expressions always see clean upstream column names,
        // and subsequent derives/filters can safely reference newly derived or overwritten columns.
        if self.needs_wrap_for_proj || self.needs_wrap_for_filter {
            self = self.wrap_as_subquery();
        }
        for c in &mut self.schema.cols {
            c.agg_kind = AggKind::Raw;
        }
        for ((name, spec), expr) in meta.into_iter().zip(exprs) {
            let existing_pos = self.schema.cols.iter().position(|c| c.name == name);
            if let SqlQuery::Select { items, .. } = &mut self.query {
                match existing_pos {
                    Some(idx) => {
                        items[idx] = SqlSelectItem {
                            expr,
                            alias: name.clone(),
                        };
                    }
                    None => {
                        items.push(SqlSelectItem {
                            expr,
                            alias: name.clone(),
                        });
                    }
                }
            }
            match existing_pos {
                Some(idx) => {
                    self.schema.cols[idx] = spec;
                    self.unique_keys.retain(|uk| !uk.iter().any(|k| k == &name));
                }
                None => self.schema.cols.push(spec),
            }
        }
        self.schema.grouped_by = None;
        self.schema.summarized = false;
        self.schema.distinct_by = None;
        self.needs_wrap_for_filter = true;
        self.needs_wrap_for_proj = true;
        self
    }

    fn apply_redact(mut self, col: &str, replacement: &str) -> Result<Self, String> {
        let Some(pos) = self.schema.cols.iter().position(|c| c.name == col) else {
            return Err(format!("Redact references missing column `{col}`"));
        };
        if self.needs_wrap_for_proj {
            self = self.wrap_as_subquery();
        }
        let red_expr = SqlExpr::Param {
            slot: SqlParamSlot::Literal(SqlParam::Text(replacement.to_string())),
            pg_cast: Some("TEXT"),
        };
        if let SqlQuery::Select { items, .. } = &mut self.query {
            items[pos] = SqlSelectItem {
                expr: red_expr,
                alias: col.to_string(),
            };
        }
        for c in &mut self.schema.cols {
            c.agg_kind = AggKind::Raw;
        }
        self.schema.cols[pos] = ColSpec {
            name: col.to_string(),
            ty: ScalarTy::Text,
            tags: TagSet::empty(),
            bucketed: false,
            agg_kind: AggKind::Raw,
        };
        self.schema.grouped_by = None;
        self.schema.summarized = false;
        self.schema.distinct_by = None;
        self.unique_keys.retain(|uk| !uk.iter().any(|k| k == col));
        self.needs_wrap_for_filter = true;
        self.needs_wrap_for_proj = true;
        self.pushed_ops.push(format!("Redact({col})"));
        Ok(self)
    }

    fn apply_sort(
        mut self,
        keys: &[(Ident, SortDir)],
        dialect: SqlDialect,
    ) -> Result<Self, String> {
        if keys.is_empty() {
            return Ok(self);
        }
        let key_names: Vec<Ident> = keys.iter().map(|(k, _)| k.clone()).collect();
        for k in &key_names {
            let Some(spec) = self.schema.find_col(k) else {
                return Err(format!("Sort references missing column `{k}`"));
            };
            if !is_dialect_exact_ord(dialect, &spec.ty) {
                return Err(non_exact_type_reason(dialect, &spec.ty, "Sort"));
            }
        }
        let covers_all = self.schema.cols.iter().all(|c| key_names.contains(&c.name));
        let is_tie_free = covers_all || self.keys_proven_unique(&key_names);
        if !is_tie_free {
            return Err(
                "stable sort on non-unique keys requires local VM to preserve tie order"
                    .to_string(),
            );
        }
        if self.needs_wrap_for_proj || self.needs_wrap_for_filter {
            self = self.wrap_as_subquery();
        }
        let mut order_items = Vec::with_capacity(keys.len());
        let mut sort_tags = TagSet::empty();
        for (k, dir) in keys {
            let Some(spec) = self.schema.find_col(k) else {
                return Err(format!("Sort references missing column `{k}`"));
            };
            sort_tags = sort_tags.union(&spec.tags);
            let mut col_expr = SqlExpr::Col {
                table_alias: None,
                name: k.clone(),
            };
            if dialect == SqlDialect::Postgres && matches!(base_of_scalar(&spec.ty), ScalarTy::Text)
            {
                col_expr = SqlExpr::CollateC(Box::new(col_expr));
            }
            order_items.push(SqlOrderItem {
                expr: col_expr,
                dir: *dir,
            });
        }
        if let SqlQuery::Select { order_by, .. } = &mut self.query {
            *order_by = order_items;
        }
        for c in &mut self.schema.cols {
            c.agg_kind = AggKind::Raw;
        }
        self.schema.order_tags = self.schema.order_tags.union(&sort_tags);
        self.schema.grouped_by = None;
        self.schema.summarized = false;
        self.schema.distinct_by = None;
        self.deterministic_order = true;
        self.needs_wrap_for_filter = true;
        self.needs_wrap_for_proj = true;
        let desc: Vec<String> = keys.iter().map(|(k, d)| format!("{k}:{d:?}")).collect();
        self.pushed_ops.push(format!("Sort([{}])", desc.join(", ")));
        Ok(self)
    }

    fn apply_limit(mut self, n: &BigInt) -> Result<Self, String> {
        if !self.deterministic_order {
            return Err("limit over non-deterministic SQL row order requires local VM".to_string());
        }
        let limit_i64 = if n.is_negative() {
            0i64
        } else {
            n.to_i64()
                .ok_or_else(|| "Limit value exceeds i64::MAX and requires local VM".to_string())?
        };
        let already_limited = matches!(
            self.query,
            SqlQuery::Select { limit: Some(_), .. } | SqlQuery::UnionAll { .. }
        );
        if already_limited {
            self = self.wrap_as_subquery();
        }
        if let SqlQuery::Select { limit, .. } = &mut self.query {
            *limit = Some(SqlParamSlot::Literal(SqlParam::Int(limit_i64)));
        }
        for c in &mut self.schema.cols {
            c.agg_kind = AggKind::Raw;
        }
        self.schema.row_tags = self.schema.row_tags.union(&self.schema.order_tags);
        self.schema.grouped_by = None;
        self.schema.summarized = false;
        self.schema.distinct_by = None;
        self.needs_wrap_for_filter = true;
        self.needs_wrap_for_proj = true;
        self.pushed_ops.push(format!("Limit({limit_i64})"));
        Ok(self)
    }

    fn apply_distinct(
        mut self,
        cols: &[Ident],
        dialect: SqlDialect,
        order_insensitive: bool,
    ) -> Result<Self, String> {
        let covers_all = cols.is_empty() || self.schema.cols.iter().all(|c| cols.contains(&c.name));
        if !covers_all {
            return Err("distinct on a column subset requires local VM".to_string());
        }
        if !order_insensitive {
            return Err(
                "order-preserving distinct requires local VM (SQL DISTINCT may reorder rows)"
                    .to_string(),
            );
        }
        for c in &self.schema.cols {
            if !is_dialect_exact_eq(dialect, &c.ty) {
                return Err(non_exact_type_reason(dialect, &c.ty, "Distinct"));
            }
        }
        if self.needs_wrap_for_proj || self.needs_wrap_for_filter {
            self = self.wrap_as_subquery();
        }
        if let SqlQuery::Select { distinct, .. } = &mut self.query {
            *distinct = true;
        }
        let all_names = self.schema.col_names();
        let key_tags = self.schema.all_col_tags();
        self.unique_keys.push(all_names);
        for c in &mut self.schema.cols {
            c.agg_kind = AggKind::Raw;
        }
        self.schema.row_tags = self.schema.row_tags.union(&key_tags);
        self.schema.grouped_by = None;
        self.schema.summarized = false;
        self.schema.distinct_by = None;
        self.deterministic_order = false;
        self.needs_wrap_for_filter = true;
        self.needs_wrap_for_proj = true;
        self.pushed_ops
            .push(format!("Distinct([{}])", cols.join(", ")));
        Ok(self)
    }

    fn apply_dedupe_by(
        mut self,
        keys: &[Ident],
        order_by: &[(Ident, SortDir)],
        keep: DedupeKeep,
        dialect: SqlDialect,
        order_insensitive: bool,
    ) -> Result<Self, String> {
        if !order_insensitive {
            return Err("order-preserving dedupe_by requires local VM".to_string());
        }
        if keys.is_empty() {
            return Err("dedupe_by requires at least one key column".to_string());
        }
        for k in keys {
            let Some(spec) = self.schema.find_col(k) else {
                return Err(format!("dedupe_by references missing key column `{k}`"));
            };
            if !is_dialect_exact_eq(dialect, &spec.ty) {
                return Err(non_exact_type_reason(dialect, &spec.ty, "DedupeBy key"));
            }
        }
        for (c, _) in order_by {
            let Some(spec) = self.schema.find_col(c) else {
                return Err(format!("dedupe_by references missing order column `{c}`"));
            };
            if !is_dialect_exact_ord(dialect, &spec.ty) {
                return Err(non_exact_type_reason(
                    dialect,
                    &spec.ty,
                    "DedupeBy order_by",
                ));
            }
        }
        let mut combined_cols: Vec<Ident> = keys.to_vec();
        for (c, _) in order_by {
            if !combined_cols.contains(c) {
                combined_cols.push(c.clone());
            }
        }
        let covers_all = self
            .schema
            .cols
            .iter()
            .all(|c| combined_cols.contains(&c.name));
        if !(covers_all || self.keys_proven_unique(&combined_cols)) {
            return Err(
                "dedupe_by with non-unique tie-breaker requires local VM to preserve input tie order"
                    .to_string(),
            );
        }

        let effective_order: Vec<(Ident, SortDir)> = order_by
            .iter()
            .map(|(c, d)| {
                let eff_dir = match (keep, d) {
                    (DedupeKeep::First, d) => *d,
                    (DedupeKeep::Last, SortDir::Asc) => SortDir::Desc,
                    (DedupeKeep::Last, SortDir::Desc) => SortDir::Asc,
                };
                (c.clone(), eff_dir)
            })
            .collect();

        let make_col_expr = |col_name: &str, spec: &ColSpec| -> SqlExpr {
            let base = SqlExpr::Col {
                table_alias: None,
                name: col_name.to_string(),
            };
            if dialect == SqlDialect::Postgres && matches!(base_of_scalar(&spec.ty), ScalarTy::Text)
            {
                SqlExpr::CollateC(Box::new(base))
            } else {
                base
            }
        };

        let key_exprs: Vec<SqlExpr> = keys
            .iter()
            .filter_map(|k| self.schema.find_col(k).map(|s| make_col_expr(k, s)))
            .collect();
        let ord_items: Vec<SqlOrderItem> = effective_order
            .iter()
            .filter_map(|(k, d)| {
                self.schema.find_col(k).map(|s| SqlOrderItem {
                    expr: make_col_expr(k, s),
                    dir: *d,
                })
            })
            .collect();

        let key_tags = TagSet::union_list(
            keys.iter()
                .filter_map(|k| self.schema.find_col(k).map(|c| &c.tags)),
        );
        let ord_tags = TagSet::union_list(
            order_by
                .iter()
                .filter_map(|(k, _)| self.schema.find_col(k).map(|c| &c.tags)),
        );

        match dialect {
            SqlDialect::Postgres => {
                let must_wrap = self.needs_wrap_for_proj
                    || self.needs_wrap_for_filter
                    || matches!(
                        &self.query,
                        SqlQuery::UnionAll { .. }
                            | SqlQuery::Select { distinct: true, .. }
                            | SqlQuery::Select { limit: Some(_), .. }
                    )
                    || matches!(
                        &self.query,
                        SqlQuery::Select {
                            group_by,
                            order_by,
                            distinct_on,
                            ..
                        } if !group_by.is_empty() || !order_by.is_empty() || !distinct_on.is_empty()
                    );
                if must_wrap {
                    self = self.wrap_as_subquery();
                }
                let mut pg_order = Vec::with_capacity(key_exprs.len() + ord_items.len());
                for ke in &key_exprs {
                    pg_order.push(SqlOrderItem {
                        expr: ke.clone(),
                        dir: SortDir::Asc,
                    });
                }
                pg_order.extend(ord_items);
                if let SqlQuery::Select {
                    distinct_on,
                    order_by: q_order,
                    ..
                } = &mut self.query
                {
                    *distinct_on = key_exprs;
                    *q_order = pg_order;
                }
            }
            SqlDialect::Sqlite => {
                let mut rn_alias = self.fresh_alias("rn");
                while self.schema.find_col(&rn_alias).is_some() {
                    rn_alias = self.fresh_alias("rn");
                }
                let inner_alias = self.fresh_alias("q");
                let win_alias = self.fresh_alias("dedupe");
                let mut win_items: Vec<SqlSelectItem> = self
                    .schema
                    .cols
                    .iter()
                    .map(|c| SqlSelectItem {
                        expr: SqlExpr::Col {
                            table_alias: None,
                            name: c.name.clone(),
                        },
                        alias: c.name.clone(),
                    })
                    .collect();
                win_items.push(SqlSelectItem {
                    expr: SqlExpr::RowNumber {
                        partition_by: key_exprs,
                        order_by: ord_items,
                    },
                    alias: rn_alias.clone(),
                });
                let win_query = SqlQuery::Select {
                    distinct: false,
                    distinct_on: Vec::new(),
                    items: win_items,
                    from: Box::new(SqlFrom::Subquery {
                        query: Box::new(self.query),
                        alias: inner_alias,
                    }),
                    where_clause: None,
                    group_by: Vec::new(),
                    order_by: Vec::new(),
                    limit: None,
                };
                let outer_items: Vec<SqlSelectItem> = self
                    .schema
                    .cols
                    .iter()
                    .map(|c| SqlSelectItem {
                        expr: SqlExpr::Col {
                            table_alias: None,
                            name: c.name.clone(),
                        },
                        alias: c.name.clone(),
                    })
                    .collect();
                self.query = SqlQuery::Select {
                    distinct: false,
                    distinct_on: Vec::new(),
                    items: outer_items,
                    from: Box::new(SqlFrom::Subquery {
                        query: Box::new(win_query),
                        alias: win_alias,
                    }),
                    where_clause: Some(SqlExpr::Binary {
                        op: "=",
                        left: Box::new(SqlExpr::Col {
                            table_alias: None,
                            name: rn_alias,
                        }),
                        right: Box::new(SqlExpr::IntLit(1)),
                    }),
                    group_by: Vec::new(),
                    order_by: Vec::new(),
                    limit: None,
                };
            }
        }

        self.unique_keys.push(keys.to_vec());
        for c in &mut self.schema.cols {
            c.agg_kind = AggKind::Raw;
        }
        self.schema.row_tags = self
            .schema
            .row_tags
            .union(&key_tags)
            .union(&ord_tags)
            .union(&self.schema.order_tags);
        self.schema.grouped_by = None;
        self.schema.summarized = false;
        self.schema.distinct_by = None;
        self.deterministic_order = false;
        self.needs_wrap_for_filter = true;
        self.needs_wrap_for_proj = true;
        let ord_desc: Vec<String> = order_by.iter().map(|(c, d)| format!("{c}:{d:?}")).collect();
        self.pushed_ops.push(format!(
            "DedupeBy(keys=[{}], order=[{}], keep={keep:?})",
            keys.join(", "),
            ord_desc.join(", ")
        ));
        Ok(self)
    }

    fn apply_union(left: Self, right: Self) -> Result<Self, String> {
        if left.db_name != right.db_name {
            return Err(format!(
                "cross-database union ({} vs {}) requires local VM",
                left.db_name, right.db_name
            ));
        }
        let Some(merged_cols) = merge_union_cols(&left.schema.cols, &right.schema.cols) else {
            return Err("Union column schemas do not align".to_string());
        };
        let col_names: Vec<String> = merged_cols.iter().map(|c| c.name.clone()).collect();
        let mut ops = left.pushed_ops;
        ops.extend(right.pushed_ops);
        ops.push("Union".to_string());
        let next_alias = left.next_alias_id.max(right.next_alias_id);
        Ok(Self {
            db_name: left.db_name,
            query: SqlQuery::UnionAll {
                left: Box::new(left.query),
                right: Box::new(right.query),
                col_names,
            },
            schema: TableTy {
                cols: merged_cols,
                row_tags: left.schema.row_tags.union(&right.schema.row_tags),
                order_tags: left.schema.order_tags.union(&right.schema.order_tags),
                grouped_by: None,
                summarized: false,
                distinct_by: None,
            },
            unique_keys: Vec::new(),
            pushed_ops: ops,
            deterministic_order: false,
            needs_wrap_for_filter: true,
            needs_wrap_for_proj: true,
            next_alias_id: next_alias,
        })
    }

    fn apply_join(
        kind: JoinKind,
        left: Self,
        right: Self,
        on: &JoinOn,
        suffixes: &Suffixes,
        dialect: SqlDialect,
        order_insensitive: bool,
    ) -> Result<Self, String> {
        if left.db_name != right.db_name {
            return Err(format!(
                "cross-database join ({} vs {}) requires local VM",
                left.db_name, right.db_name
            ));
        }
        let key_pairs = resolve_join_pairs(&left.schema, &right.schema, on)
            .map_err(|e| format!("invalid join keys: {e}"))?;
        if key_pairs.is_empty() {
            return Err("join without key pairs requires local VM".to_string());
        }
        let l_keys: Vec<Ident> = key_pairs.iter().map(|(lc, _)| lc.name.clone()).collect();
        let r_keys: Vec<Ident> = key_pairs.iter().map(|(_, rc)| rc.name.clone()).collect();

        // Enforce explicit cardinality checks FIRST so the barrier reason is always exact.
        let need_left_unique = matches!(kind, JoinKind::InnerOne | JoinKind::LeftOne);
        let need_right_unique = matches!(
            kind,
            JoinKind::InnerOne
                | JoinKind::LeftOne
                | JoinKind::InnerManyToOne
                | JoinKind::LeftManyToOne
        );
        if (need_left_unique && !left.keys_proven_unique(&l_keys))
            || (need_right_unique && !right.keys_proven_unique(&r_keys))
        {
            return Err("explicit join cardinality check requires local VM".to_string());
        }

        for (lc, rc) in &key_pairs {
            if !is_dialect_exact_eq(dialect, &lc.ty) {
                return Err(non_exact_type_reason(dialect, &lc.ty, "Join"));
            }
            if !is_dialect_exact_eq(dialect, &rc.ty) {
                return Err(non_exact_type_reason(dialect, &rc.ty, "Join"));
            }
        }

        if !order_insensitive {
            return Err(
                "join without outer canonical ordering requires local VM to preserve row order"
                    .to_string(),
            );
        }

        let joined_cols =
            build_joined_cols(kind, &left.schema.cols, &right.schema.cols, on, suffixes)
                .map_err(|e| format!("invalid joined schema: {e}"))?;
        let on_tags = TagSet::union_owned(key_pairs.iter().map(|(lc, rc)| lc.tags.union(&rc.tags)));
        let new_order_tags = match kind {
            JoinKind::Semi | JoinKind::Anti => left.schema.order_tags.clone(),
            _ => left.schema.order_tags.union(&right.schema.order_tags),
        };
        let next_alias_base = left.next_alias_id.max(right.next_alias_id);
        let l_alias = format!("_jl{}", next_alias_base + 1);
        let r_alias = format!("_jr{}", next_alias_base + 2);

        let mut cond_parts = Vec::with_capacity(key_pairs.len());
        for (lc, rc) in &key_pairs {
            let l_col = SqlExpr::Col {
                table_alias: Some(l_alias.clone()),
                name: lc.name.clone(),
            };
            let r_col = SqlExpr::Col {
                table_alias: Some(r_alias.clone()),
                name: rc.name.clone(),
            };
            let eq_expr = if lc.ty.is_option() || rc.ty.is_option() {
                SqlExpr::NullSafeEq {
                    negated: false,
                    left: Box::new(l_col),
                    right: Box::new(r_col),
                }
            } else {
                SqlExpr::Binary {
                    op: "=",
                    left: Box::new(l_col),
                    right: Box::new(r_col),
                }
            };
            cond_parts.push(eq_expr);
        }
        let join_cond = cond_parts
            .into_iter()
            .reduce(|acc, e| SqlExpr::Binary {
                op: "AND",
                left: Box::new(acc),
                right: Box::new(e),
            })
            .ok_or_else(|| "empty join condition".to_string())?;

        let mut ops = left.pushed_ops;
        ops.extend(right.pushed_ops);
        ops.push(format!("Join({kind:?})"));

        let out_schema = TableTy {
            cols: joined_cols.clone(),
            row_tags: left
                .schema
                .row_tags
                .union(&right.schema.row_tags)
                .union(&on_tags),
            order_tags: new_order_tags,
            grouped_by: None,
            summarized: false,
            distinct_by: None,
        };

        let (query, out_unique_keys) = match kind {
            JoinKind::Semi | JoinKind::Anti => {
                let items: Vec<SqlSelectItem> = left
                    .schema
                    .cols
                    .iter()
                    .map(|c| SqlSelectItem {
                        expr: SqlExpr::Col {
                            table_alias: Some(l_alias.clone()),
                            name: c.name.clone(),
                        },
                        alias: c.name.clone(),
                    })
                    .collect();
                let exists_sub = SqlQuery::Select {
                    distinct: false,
                    distinct_on: Vec::new(),
                    items: vec![SqlSelectItem {
                        expr: SqlExpr::Param {
                            slot: SqlParamSlot::Literal(SqlParam::Int(1)),
                            pg_cast: None,
                        },
                        alias: "_exists".to_string(),
                    }],
                    from: Box::new(SqlFrom::Subquery {
                        query: Box::new(right.query),
                        alias: r_alias,
                    }),
                    where_clause: Some(join_cond),
                    group_by: Vec::new(),
                    order_by: Vec::new(),
                    limit: None,
                };
                let q = SqlQuery::Select {
                    distinct: false,
                    distinct_on: Vec::new(),
                    items,
                    from: Box::new(SqlFrom::Subquery {
                        query: Box::new(left.query),
                        alias: l_alias,
                    }),
                    where_clause: Some(SqlExpr::Exists {
                        negated: matches!(kind, JoinKind::Anti),
                        subquery: Box::new(exists_sub),
                    }),
                    group_by: Vec::new(),
                    order_by: Vec::new(),
                    limit: None,
                };
                (q, left.unique_keys)
            }
            _ => {
                let same_key_names: &[Ident] = match on {
                    JoinOn::SameKeys(ks) => ks,
                    JoinOn::Pairs(_) => &[],
                };
                let r_kept: Vec<&ColSpec> = right
                    .schema
                    .cols
                    .iter()
                    .filter(|rc| !same_key_names.contains(&rc.name))
                    .collect();
                let l_len = left.schema.cols.len();
                let mut items = Vec::with_capacity(joined_cols.len());
                let mut left_rename_map: HashMap<Ident, Ident> = HashMap::new();
                for (i, lc) in left.schema.cols.iter().enumerate() {
                    let out_name = joined_cols[i].name.clone();
                    left_rename_map.insert(lc.name.clone(), out_name.clone());
                    items.push(SqlSelectItem {
                        expr: SqlExpr::Col {
                            table_alias: Some(l_alias.clone()),
                            name: lc.name.clone(),
                        },
                        alias: out_name,
                    });
                }
                for (j, rc) in r_kept.iter().enumerate() {
                    let out_name = joined_cols[l_len + j].name.clone();
                    items.push(SqlSelectItem {
                        expr: SqlExpr::Col {
                            table_alias: Some(r_alias.clone()),
                            name: rc.name.clone(),
                        },
                        alias: out_name,
                    });
                }
                let sql_kind = match kind {
                    JoinKind::LeftOne | JoinKind::LeftManyToOne => SqlJoinKind::Left,
                    _ => SqlJoinKind::Inner,
                };
                let q = SqlQuery::Select {
                    distinct: false,
                    distinct_on: Vec::new(),
                    items,
                    from: Box::new(SqlFrom::Join {
                        left: Box::new(SqlFrom::Subquery {
                            query: Box::new(left.query),
                            alias: l_alias,
                        }),
                        kind: sql_kind,
                        right: Box::new(SqlFrom::Subquery {
                            query: Box::new(right.query),
                            alias: r_alias,
                        }),
                        on: join_cond,
                    }),
                    where_clause: None,
                    group_by: Vec::new(),
                    order_by: Vec::new(),
                    limit: None,
                };
                let preserved_uqs = if need_right_unique {
                    left.unique_keys
                        .into_iter()
                        .map(|uk| {
                            uk.into_iter()
                                .map(|k| left_rename_map.get(&k).cloned().unwrap_or(k))
                                .collect()
                        })
                        .collect()
                } else {
                    Vec::new()
                };
                (q, preserved_uqs)
            }
        };

        Ok(Self {
            db_name: left.db_name,
            query,
            schema: out_schema,
            unique_keys: out_unique_keys,
            pushed_ops: ops,
            deterministic_order: false,
            needs_wrap_for_filter: true,
            needs_wrap_for_proj: true,
            next_alias_id: next_alias_base + 2,
        })
    }

    fn apply_summarize(
        mut self,
        group_keys_raw: &[Ident],
        agg_items: &[TranslatedAggSpec],
        distinct_key: Option<&str>,
        dialect: SqlDialect,
        sort_groups_core: bool,
        emit_group_meta: Option<Option<&str>>,
    ) -> Result<Self, String> {
        if agg_items.is_empty() {
            return Err("empty Summarize cannot be pushed".to_string());
        }
        // Core IR orders output group keys in input schema column order.
        let ordered_group_cols: Vec<ColSpec> = self
            .schema
            .cols
            .iter()
            .filter(|c| group_keys_raw.contains(&c.name))
            .map(|c| ColSpec {
                agg_kind: AggKind::GroupKey,
                ..c.clone()
            })
            .collect();
        if ordered_group_cols.len() != group_keys_raw.len() {
            return Err("GroupBy references missing or duplicate key column".to_string());
        }
        for gc in &ordered_group_cols {
            if !is_dialect_exact_eq(dialect, &gc.ty)
                || (sort_groups_core && !is_dialect_exact_ord(dialect, &gc.ty))
            {
                return Err(non_exact_type_reason(dialect, &gc.ty, "GroupBy"));
            }
        }
        let dk_tags = match distinct_key {
            None => TagSet::empty(),
            Some(dk) => self
                .schema
                .find_col(dk)
                .map(|c| c.tags.clone())
                .unwrap_or_default(),
        };
        let key_tags = TagSet::union_list(ordered_group_cols.iter().map(|c| &c.tags));
        let row_tags = self.schema.row_tags.union(&key_tags).union(&dk_tags);

        if let Some(Some(dk)) = emit_group_meta {
            let Some(dk_col) = self.schema.find_col(dk) else {
                return Err(format!(
                    "suppress_small_groups distinct_by references missing column `{dk}`"
                ));
            };
            if !is_dialect_exact_eq(dialect, &dk_col.ty) {
                return Err(non_exact_type_reason(
                    dialect,
                    &dk_col.ty,
                    "SuppressSmallGroups distinct_by",
                ));
            }
        }

        if self.needs_wrap_for_proj || self.needs_wrap_for_filter {
            self = self.wrap_as_subquery();
        }

        let extra_meta_cols = match emit_group_meta {
            None => 0,
            Some(None) => 1,
            Some(Some(_)) => 2,
        };
        let mut select_items =
            Vec::with_capacity(ordered_group_cols.len() + agg_items.len() + extra_meta_cols);
        let mut group_by_exprs = Vec::with_capacity(ordered_group_cols.len());
        let mut order_by_items = Vec::with_capacity(ordered_group_cols.len());
        let mut out_cols = ordered_group_cols.clone();

        for gc in &ordered_group_cols {
            let col_e = SqlExpr::Col {
                table_alias: None,
                name: gc.name.clone(),
            };
            select_items.push(SqlSelectItem {
                expr: col_e.clone(),
                alias: gc.name.clone(),
            });
            group_by_exprs.push(col_e.clone());
            if sort_groups_core {
                let ord_e = if dialect == SqlDialect::Postgres
                    && matches!(base_of_scalar(&gc.ty), ScalarTy::Text)
                {
                    SqlExpr::CollateC(Box::new(col_e))
                } else {
                    col_e
                };
                order_by_items.push(SqlOrderItem {
                    expr: ord_e,
                    dir: SortDir::Asc,
                });
            }
        }

        for (name, op, arg_opt) in agg_items {
            let kind = if op.is_blending() {
                AggKind::Blending
            } else {
                AggKind::NonBlending
            };
            let (sql_e, out_ty, arg_tags) = match (op, arg_opt) {
                (ExecAggOp::Core(AggOp::Count), None) => {
                    (SqlExpr::CountStar, ScalarTy::Int, TagSet::empty())
                }
                (ExecAggOp::CountIf, Some((cond_e, ScalarTy::Bool, cond_tags))) => {
                    let case_e = SqlExpr::Case {
                        whens: vec![(cond_e.clone(), SqlExpr::IntLit(1))],
                        else_br: Box::new(SqlExpr::IntLit(0)),
                    };
                    let sum_e = SqlExpr::Agg {
                        func: "SUM",
                        distinct: false,
                        arg: Box::new(case_e),
                    };
                    (
                        SqlExpr::Coalesce(Box::new(sum_e), Box::new(SqlExpr::IntLit(0))),
                        ScalarTy::Int,
                        cond_tags.clone(),
                    )
                }
                (ExecAggOp::Core(AggOp::CountDistinct), Some((arg_e, arg_ty, arg_ts))) => {
                    if !is_dialect_exact_eq(dialect, arg_ty) {
                        return Err(non_exact_type_reason(dialect, arg_ty, "CountDistinct"));
                    }
                    (
                        SqlExpr::Agg {
                            func: "COUNT",
                            distinct: true,
                            arg: Box::new(arg_e.clone()),
                        },
                        ScalarTy::Int,
                        arg_ts.clone(),
                    )
                }
                (
                    ExecAggOp::Core(cop @ (AggOp::Min | AggOp::Max)),
                    Some((arg_e, arg_ty, arg_ts)),
                ) => {
                    let b_ty = base_of_scalar(arg_ty);
                    if !is_dialect_exact_ord(dialect, b_ty) {
                        return Err(non_exact_type_reason(dialect, b_ty, "Min/Max"));
                    }
                    // PostgreSQL does not implement MIN(boolean) / MAX(boolean).
                    if dialect == SqlDialect::Postgres && matches!(b_ty, ScalarTy::Bool) {
                        return Err("PostgreSQL lacks native MIN/MAX on Bool; requires local VM"
                            .to_string());
                    }
                    let inner_e =
                        if dialect == SqlDialect::Postgres && matches!(b_ty, ScalarTy::Text) {
                            SqlExpr::CollateC(Box::new(arg_e.clone()))
                        } else {
                            arg_e.clone()
                        };
                    let func = if matches!(cop, AggOp::Min) {
                        "MIN"
                    } else {
                        "MAX"
                    };
                    (
                        SqlExpr::Agg {
                            func,
                            distinct: false,
                            arg: Box::new(inner_e),
                        },
                        ScalarTy::Option(Box::new(b_ty.clone())),
                        arg_ts.clone(),
                    )
                }
                (other_op, _) => {
                    return Err(format!(
                        "aggregate `{}` requires local VM",
                        other_op.display_name()
                    ));
                }
            };
            select_items.push(SqlSelectItem {
                expr: sql_e,
                alias: name.clone(),
            });
            out_cols.push(ColSpec {
                name: name.clone(),
                ty: out_ty,
                tags: arg_tags.union(&row_tags),
                bucketed: false,
                agg_kind: kind,
            });
        }

        if let Some(dk_opt) = emit_group_meta {
            if out_cols.iter().any(|c| c.name.starts_with("__dana_gm_")) {
                return Err(
                    "reserved group-meta column name conflict requires local VM".to_string()
                );
            }
            select_items.push(SqlSelectItem {
                expr: SqlExpr::CountStar,
                alias: HIDDEN_GROUP_ROW_COUNT_COL.to_string(),
            });
            out_cols.push(ColSpec {
                name: HIDDEN_GROUP_ROW_COUNT_COL.to_string(),
                ty: ScalarTy::Int,
                tags: TagSet::empty(),
                bucketed: false,
                agg_kind: AggKind::Raw,
            });
            if let Some(dk) = dk_opt {
                let dk_tags = self
                    .schema
                    .find_col(dk)
                    .map(|c| c.tags.clone())
                    .unwrap_or_default();
                select_items.push(SqlSelectItem {
                    expr: SqlExpr::Agg {
                        func: "COUNT",
                        distinct: true,
                        arg: Box::new(SqlExpr::Col {
                            table_alias: None,
                            name: dk.to_string(),
                        }),
                    },
                    alias: HIDDEN_GROUP_DISTINCT_COUNT_COL.to_string(),
                });
                out_cols.push(ColSpec {
                    name: HIDDEN_GROUP_DISTINCT_COUNT_COL.to_string(),
                    ty: ScalarTy::Int,
                    tags: dk_tags,
                    bucketed: false,
                    agg_kind: AggKind::Raw,
                });
            }
        }

        if let SqlQuery::Select {
            items,
            group_by,
            order_by,
            ..
        } = &mut self.query
        {
            *items = select_items;
            *group_by = group_by_exprs;
            *order_by = order_by_items;
        }

        let ordered_key_names: Vec<Ident> =
            ordered_group_cols.iter().map(|c| c.name.clone()).collect();
        self.unique_keys = vec![ordered_key_names.clone()];
        self.schema = TableTy {
            cols: out_cols,
            row_tags,
            order_tags: TagSet::empty(),
            grouped_by: Some(ordered_key_names.clone()),
            summarized: true,
            distinct_by: distinct_key.map(str::to_string),
        };
        self.deterministic_order = sort_groups_core || ordered_key_names.is_empty();
        self.needs_wrap_for_filter = true;
        self.needs_wrap_for_proj = true;
        if !ordered_key_names.is_empty() {
            self.pushed_ops
                .push(format!("GroupBy([{}])", ordered_key_names.join(", ")));
        }
        let agg_desc: Vec<String> = agg_items
            .iter()
            .map(|(n, op, _)| format!("{n}:{}", op.display_name()))
            .collect();
        self.pushed_ops
            .push(format!("Summarize([{}])", agg_desc.join(", ")));
        Ok(self)
    }
}

fn expr_has_untrimmed_try_parse_date(expr: &SqlExpr) -> bool {
    match expr {
        SqlExpr::TryParseIsoDate {
            already_trimmed: false,
            ..
        } => true,
        SqlExpr::TryParseIsoDate {
            inner,
            already_trimmed: true,
        }
        | SqlExpr::Unary { arg: inner, .. }
        | SqlExpr::IsNull { arg: inner, .. }
        | SqlExpr::CollateC(inner)
        | SqlExpr::Cast { expr: inner, .. }
        | SqlExpr::Agg { arg: inner, .. }
        | SqlExpr::TrimAscii(inner)
        | SqlExpr::ExtractYear(inner) => expr_has_untrimmed_try_parse_date(inner),
        SqlExpr::Binary { left, right, .. }
        | SqlExpr::NullSafeEq { left, right, .. }
        | SqlExpr::Coalesce(left, right)
        | SqlExpr::AtTimeZone {
            expr: left,
            tz: right,
        } => expr_has_untrimmed_try_parse_date(left) || expr_has_untrimmed_try_parse_date(right),
        SqlExpr::Func { args, .. } => args.iter().any(expr_has_untrimmed_try_parse_date),
        SqlExpr::Case { whens, else_br } => {
            whens.iter().any(|(c, t)| {
                expr_has_untrimmed_try_parse_date(c) || expr_has_untrimmed_try_parse_date(t)
            }) || expr_has_untrimmed_try_parse_date(else_br)
        }
        SqlExpr::Substring {
            str_expr,
            start,
            len,
        } => {
            expr_has_untrimmed_try_parse_date(str_expr)
                || expr_has_untrimmed_try_parse_date(start)
                || expr_has_untrimmed_try_parse_date(len)
        }
        SqlExpr::InList { expr, items } => {
            expr_has_untrimmed_try_parse_date(expr)
                || items.iter().any(expr_has_untrimmed_try_parse_date)
        }
        SqlExpr::RowNumber {
            partition_by,
            order_by,
        } => {
            partition_by.iter().any(expr_has_untrimmed_try_parse_date)
                || order_by
                    .iter()
                    .any(|o| expr_has_untrimmed_try_parse_date(&o.expr))
        }
        SqlExpr::Col { .. }
        | SqlExpr::Param { .. }
        | SqlExpr::Exists { .. }
        | SqlExpr::CountStar
        | SqlExpr::BoolLit(_)
        | SqlExpr::IntLit(_) => false,
    }
}

fn collect_sql_from_col_refs(from: &SqlFrom, out: &mut HashSet<String>) {
    match from {
        SqlFrom::Table { .. } | SqlFrom::CteRef { .. } => {}
        SqlFrom::Subquery { query, .. } => collect_sql_query_col_refs(query, out),
        SqlFrom::Join {
            left, right, on, ..
        } => {
            collect_sql_from_col_refs(left, out);
            collect_sql_from_col_refs(right, out);
            collect_sql_expr_col_refs(on, out);
        }
    }
}

fn collect_sql_query_col_refs(query: &SqlQuery, out: &mut HashSet<String>) {
    match query {
        SqlQuery::Select {
            distinct_on,
            items,
            from,
            where_clause,
            group_by,
            order_by,
            ..
        } => {
            for e in distinct_on {
                collect_sql_expr_col_refs(e, out);
            }
            for item in items {
                collect_sql_expr_col_refs(&item.expr, out);
            }
            collect_sql_from_col_refs(from, out);
            if let Some(w) = where_clause {
                collect_sql_expr_col_refs(w, out);
            }
            for g in group_by {
                collect_sql_expr_col_refs(g, out);
            }
            for o in order_by {
                collect_sql_expr_col_refs(&o.expr, out);
            }
        }
        SqlQuery::UnionAll { left, right, .. } => {
            collect_sql_query_col_refs(left, out);
            collect_sql_query_col_refs(right, out);
        }
    }
}

fn collect_sql_expr_col_refs(expr: &SqlExpr, out: &mut HashSet<String>) {
    match expr {
        SqlExpr::Col { name, .. } => {
            out.insert(name.clone());
        }
        SqlExpr::Param { .. } | SqlExpr::CountStar | SqlExpr::BoolLit(_) | SqlExpr::IntLit(_) => {}
        SqlExpr::Unary { arg: inner, .. }
        | SqlExpr::IsNull { arg: inner, .. }
        | SqlExpr::CollateC(inner)
        | SqlExpr::Cast { expr: inner, .. }
        | SqlExpr::Agg { arg: inner, .. }
        | SqlExpr::TrimAscii(inner)
        | SqlExpr::ExtractYear(inner)
        | SqlExpr::TryParseIsoDate { inner, .. } => collect_sql_expr_col_refs(inner, out),
        SqlExpr::Binary { left, right, .. }
        | SqlExpr::NullSafeEq { left, right, .. }
        | SqlExpr::Coalesce(left, right)
        | SqlExpr::AtTimeZone {
            expr: left,
            tz: right,
        } => {
            collect_sql_expr_col_refs(left, out);
            collect_sql_expr_col_refs(right, out);
        }
        SqlExpr::Func { args, .. } => {
            for a in args {
                collect_sql_expr_col_refs(a, out);
            }
        }
        SqlExpr::Case { whens, else_br } => {
            for (c, t) in whens {
                collect_sql_expr_col_refs(c, out);
                collect_sql_expr_col_refs(t, out);
            }
            collect_sql_expr_col_refs(else_br, out);
        }
        SqlExpr::Exists { subquery, .. } => collect_sql_query_col_refs(subquery, out),
        SqlExpr::Substring {
            str_expr,
            start,
            len,
        } => {
            collect_sql_expr_col_refs(str_expr, out);
            collect_sql_expr_col_refs(start, out);
            collect_sql_expr_col_refs(len, out);
        }
        SqlExpr::InList { expr, items } => {
            collect_sql_expr_col_refs(expr, out);
            for item in items {
                collect_sql_expr_col_refs(item, out);
            }
        }
        SqlExpr::RowNumber {
            partition_by,
            order_by,
        } => {
            for p in partition_by {
                collect_sql_expr_col_refs(p, out);
            }
            for o in order_by {
                collect_sql_expr_col_refs(&o.expr, out);
            }
        }
    }
}

fn sql_expr_col_refs(expr: &SqlExpr) -> HashSet<String> {
    let mut out = HashSet::new();
    collect_sql_expr_col_refs(expr, &mut out);
    out
}

struct DeriveWaveState {
    working_schema: TableTy,
    wave: Vec<(Ident, SqlExpr, ColSpec)>,
    written: HashSet<String>,
    read: HashSet<String>,
}

impl DeriveWaveState {
    fn new(schema: TableTy, capacity: usize) -> Self {
        Self {
            working_schema: schema,
            wave: Vec::with_capacity(capacity),
            written: HashSet::new(),
            read: HashSet::new(),
        }
    }

    fn push_item(
        &mut self,
        mut cur: PushedNode,
        name: &str,
        sql_e: SqlExpr,
        spec: ColSpec,
    ) -> PushedNode {
        let deps = sql_expr_col_refs(&sql_e);
        let conflicts = deps.iter().any(|d| self.written.contains(d))
            || self.written.contains(name)
            || self.read.contains(name);
        if conflicts && !self.wave.is_empty() {
            let taken = std::mem::take(&mut self.wave);
            cur = cur.apply_derive_wave(taken);
            self.written.clear();
            self.read.clear();
        }
        if self.wave.is_empty() {
            for c in &mut self.working_schema.cols {
                c.agg_kind = AggKind::Raw;
            }
        }
        match self.working_schema.cols.iter().position(|c| c.name == name) {
            Some(idx) => self.working_schema.cols[idx] = spec.clone(),
            None => self.working_schema.cols.push(spec.clone()),
        }
        self.working_schema.grouped_by = None;
        self.working_schema.summarized = false;
        self.working_schema.distinct_by = None;
        self.written.insert(name.to_string());
        self.read.extend(deps);
        self.wave.push((name.to_string(), sql_e, spec));
        cur
    }

    fn finish(mut self, mut cur: PushedNode) -> PushedNode {
        if !self.wave.is_empty() {
            let taken = std::mem::take(&mut self.wave);
            cur = cur.apply_derive_wave(taken);
        }
        cur
    }
}

fn exact_non_null_lit(expr: &SqlExpr) -> Option<SqlParam> {
    match expr {
        SqlExpr::BoolLit(b) => Some(SqlParam::Bool(*b)),
        SqlExpr::IntLit(n) => Some(SqlParam::Int(*n)),
        SqlExpr::Param {
            slot:
                SqlParamSlot::Literal(
                    p @ (SqlParam::Text(_)
                    | SqlParam::Int(_)
                    | SqlParam::Bool(_)
                    | SqlParam::Date(_)),
                ),
            ..
        } => Some(p.clone()),
        _ => None,
    }
}

const fn same_exact_lit_kind(a: &SqlParam, b: &SqlParam) -> bool {
    matches!(
        (a, b),
        (SqlParam::Text(_), SqlParam::Text(_))
            | (SqlParam::Int(_), SqlParam::Int(_))
            | (SqlParam::Bool(_), SqlParam::Bool(_))
            | (SqlParam::Date(_), SqlParam::Date(_))
    )
}

const fn is_sql_col(expr: &SqlExpr) -> bool {
    matches!(expr, SqlExpr::Col { .. })
}

fn combine_null_guard_pred(col: SqlExpr, null_matches: bool, pred: SqlExpr) -> SqlExpr {
    if null_matches {
        SqlExpr::Binary {
            op: "OR",
            left: Box::new(SqlExpr::IsNull {
                negated: false,
                arg: Box::new(col),
            }),
            right: Box::new(pred),
        }
    } else {
        SqlExpr::Binary {
            op: "AND",
            left: Box::new(SqlExpr::IsNull {
                negated: true,
                arg: Box::new(col),
            }),
            right: Box::new(pred),
        }
    }
}

fn try_rewrite_coalesce_eq(op: &'static str, left: &SqlExpr, right: &SqlExpr) -> Option<SqlExpr> {
    if op != "=" && op != "<>" {
        return None;
    }
    let (col, def_lit, target_lit, cmp) = match (left, right) {
        (SqlExpr::Coalesce(c, d), rhs) if is_sql_col(c) => {
            let d_lit = exact_non_null_lit(d)?;
            let t_lit = exact_non_null_lit(rhs)?;
            if !same_exact_lit_kind(&d_lit, &t_lit) {
                return None;
            }
            (
                c.as_ref().clone(),
                d_lit,
                t_lit,
                SqlExpr::Binary {
                    op,
                    left: Box::new(c.as_ref().clone()),
                    right: Box::new(rhs.clone()),
                },
            )
        }
        (lhs, SqlExpr::Coalesce(c, d)) if is_sql_col(c) => {
            let d_lit = exact_non_null_lit(d)?;
            let t_lit = exact_non_null_lit(lhs)?;
            if !same_exact_lit_kind(&d_lit, &t_lit) {
                return None;
            }
            (
                c.as_ref().clone(),
                d_lit,
                t_lit,
                SqlExpr::Binary {
                    op,
                    left: Box::new(lhs.clone()),
                    right: Box::new(c.as_ref().clone()),
                },
            )
        }
        _ => return None,
    };
    let null_matches = if op == "=" {
        def_lit == target_lit
    } else {
        def_lit != target_lit
    };
    Some(combine_null_guard_pred(col, null_matches, cmp))
}

/// Rewrite `COALESCE(col, d) = t`, `COALESCE(col, d) <> t`, and `COALESCE(col, d) IN (...)`
/// (with exact non-null literals) into MCV-histogram-friendly exact 3-valued logic on `col`
/// (`(col IS NULL) OR ...` / `(col IS NOT NULL) AND ...`).
fn simplify_coalesce_pred(expr: SqlExpr) -> SqlExpr {
    match expr {
        SqlExpr::Unary { op, arg } => SqlExpr::Unary {
            op,
            arg: Box::new(simplify_coalesce_pred(*arg)),
        },
        SqlExpr::Binary { op, left, right } => {
            let left = simplify_coalesce_pred(*left);
            let right = simplify_coalesce_pred(*right);
            if let Some(rewritten) = try_rewrite_coalesce_eq(op, &left, &right) {
                return rewritten;
            }
            SqlExpr::Binary {
                op,
                left: Box::new(left),
                right: Box::new(right),
            }
        }
        SqlExpr::NullSafeEq {
            negated,
            left,
            right,
        } => SqlExpr::NullSafeEq {
            negated,
            left: Box::new(simplify_coalesce_pred(*left)),
            right: Box::new(simplify_coalesce_pred(*right)),
        },
        SqlExpr::IsNull { negated, arg } => SqlExpr::IsNull {
            negated,
            arg: Box::new(simplify_coalesce_pred(*arg)),
        },
        SqlExpr::CollateC(inner) => SqlExpr::CollateC(Box::new(simplify_coalesce_pred(*inner))),
        SqlExpr::Func { name, args } => SqlExpr::Func {
            name,
            args: args.into_iter().map(simplify_coalesce_pred).collect(),
        },
        SqlExpr::Cast { expr, ty } => SqlExpr::Cast {
            expr: Box::new(simplify_coalesce_pred(*expr)),
            ty,
        },
        SqlExpr::Case { whens, else_br } => SqlExpr::Case {
            whens: whens
                .into_iter()
                .map(|(c, t)| (simplify_coalesce_pred(c), simplify_coalesce_pred(t)))
                .collect(),
            else_br: Box::new(simplify_coalesce_pred(*else_br)),
        },
        SqlExpr::Coalesce(left, right) => SqlExpr::Coalesce(
            Box::new(simplify_coalesce_pred(*left)),
            Box::new(simplify_coalesce_pred(*right)),
        ),
        SqlExpr::Substring {
            str_expr,
            start,
            len,
        } => SqlExpr::Substring {
            str_expr: Box::new(simplify_coalesce_pred(*str_expr)),
            start: Box::new(simplify_coalesce_pred(*start)),
            len: Box::new(simplify_coalesce_pred(*len)),
        },
        SqlExpr::InList { expr, items } => {
            let expr = simplify_coalesce_pred(*expr);
            let items: Vec<SqlExpr> = items.into_iter().map(simplify_coalesce_pred).collect();
            if !items.is_empty()
                && let SqlExpr::Coalesce(c, d) = &expr
                && is_sql_col(c)
                && let Some(def_lit) = exact_non_null_lit(d)
            {
                let item_lits: Option<Vec<SqlParam>> = items
                    .iter()
                    .map(|it| {
                        let p = exact_non_null_lit(it)?;
                        same_exact_lit_kind(&def_lit, &p).then_some(p)
                    })
                    .collect();
                if let Some(lits) = item_lits {
                    let null_matches = lits.iter().any(|p| p == &def_lit);
                    let col = c.as_ref().clone();
                    let in_expr = SqlExpr::InList {
                        expr: Box::new(col.clone()),
                        items,
                    };
                    return combine_null_guard_pred(col, null_matches, in_expr);
                }
            }
            SqlExpr::InList {
                expr: Box::new(expr),
                items,
            }
        }
        SqlExpr::TrimAscii(inner) => SqlExpr::TrimAscii(Box::new(simplify_coalesce_pred(*inner))),
        SqlExpr::TryParseIsoDate {
            inner,
            already_trimmed,
        } => SqlExpr::TryParseIsoDate {
            inner: Box::new(simplify_coalesce_pred(*inner)),
            already_trimmed,
        },
        SqlExpr::ExtractYear(inner) => {
            SqlExpr::ExtractYear(Box::new(simplify_coalesce_pred(*inner)))
        }
        SqlExpr::AtTimeZone { expr, tz } => SqlExpr::AtTimeZone {
            expr: Box::new(simplify_coalesce_pred(*expr)),
            tz: Box::new(simplify_coalesce_pred(*tz)),
        },
        other @ (SqlExpr::Col { .. }
        | SqlExpr::Param { .. }
        | SqlExpr::Exists { .. }
        | SqlExpr::CountStar
        | SqlExpr::Agg { .. }
        | SqlExpr::BoolLit(_)
        | SqlExpr::IntLit(_)
        | SqlExpr::RowNumber { .. }) => other,
    }
}

fn rewrite_leaf_try_parse_dates(
    expr: SqlExpr,
    schema: &TableTy,
    next_alias_id: &mut usize,
    hoisted: &mut Vec<(String, SqlExpr)>,
) -> SqlExpr {
    match expr {
        SqlExpr::TryParseIsoDate {
            inner,
            already_trimmed: false,
        } => {
            if expr_has_untrimmed_try_parse_date(&inner) {
                SqlExpr::TryParseIsoDate {
                    inner: Box::new(rewrite_leaf_try_parse_dates(
                        *inner,
                        schema,
                        next_alias_id,
                        hoisted,
                    )),
                    already_trimmed: false,
                }
            } else {
                let candidate = loop {
                    *next_alias_id += 1;
                    let alias = format!("_dana_iso_{}", *next_alias_id);
                    if schema.find_col(&alias).is_none()
                        && !hoisted.iter().any(|(n, _)| n == &alias)
                    {
                        break alias;
                    }
                };
                hoisted.push((candidate.clone(), SqlExpr::TrimAscii(inner)));
                SqlExpr::TryParseIsoDate {
                    inner: Box::new(SqlExpr::Col {
                        table_alias: None,
                        name: candidate,
                    }),
                    already_trimmed: true,
                }
            }
        }
        SqlExpr::TryParseIsoDate {
            inner,
            already_trimmed: true,
        } => SqlExpr::TryParseIsoDate {
            inner: Box::new(rewrite_leaf_try_parse_dates(
                *inner,
                schema,
                next_alias_id,
                hoisted,
            )),
            already_trimmed: true,
        },
        SqlExpr::Unary { op, arg } => SqlExpr::Unary {
            op,
            arg: Box::new(rewrite_leaf_try_parse_dates(
                *arg,
                schema,
                next_alias_id,
                hoisted,
            )),
        },
        SqlExpr::Binary { op, left, right } => SqlExpr::Binary {
            op,
            left: Box::new(rewrite_leaf_try_parse_dates(
                *left,
                schema,
                next_alias_id,
                hoisted,
            )),
            right: Box::new(rewrite_leaf_try_parse_dates(
                *right,
                schema,
                next_alias_id,
                hoisted,
            )),
        },
        SqlExpr::NullSafeEq {
            negated,
            left,
            right,
        } => SqlExpr::NullSafeEq {
            negated,
            left: Box::new(rewrite_leaf_try_parse_dates(
                *left,
                schema,
                next_alias_id,
                hoisted,
            )),
            right: Box::new(rewrite_leaf_try_parse_dates(
                *right,
                schema,
                next_alias_id,
                hoisted,
            )),
        },
        SqlExpr::IsNull { negated, arg } => SqlExpr::IsNull {
            negated,
            arg: Box::new(rewrite_leaf_try_parse_dates(
                *arg,
                schema,
                next_alias_id,
                hoisted,
            )),
        },
        SqlExpr::CollateC(inner) => SqlExpr::CollateC(Box::new(rewrite_leaf_try_parse_dates(
            *inner,
            schema,
            next_alias_id,
            hoisted,
        ))),
        SqlExpr::Func { name, args } => SqlExpr::Func {
            name,
            args: args
                .into_iter()
                .map(|a| rewrite_leaf_try_parse_dates(a, schema, next_alias_id, hoisted))
                .collect(),
        },
        SqlExpr::Cast { expr, ty } => SqlExpr::Cast {
            expr: Box::new(rewrite_leaf_try_parse_dates(
                *expr,
                schema,
                next_alias_id,
                hoisted,
            )),
            ty,
        },
        SqlExpr::Case { whens, else_br } => SqlExpr::Case {
            whens: whens
                .into_iter()
                .map(|(c, t)| {
                    (
                        rewrite_leaf_try_parse_dates(c, schema, next_alias_id, hoisted),
                        rewrite_leaf_try_parse_dates(t, schema, next_alias_id, hoisted),
                    )
                })
                .collect(),
            else_br: Box::new(rewrite_leaf_try_parse_dates(
                *else_br,
                schema,
                next_alias_id,
                hoisted,
            )),
        },
        SqlExpr::Coalesce(left, right) => SqlExpr::Coalesce(
            Box::new(rewrite_leaf_try_parse_dates(
                *left,
                schema,
                next_alias_id,
                hoisted,
            )),
            Box::new(rewrite_leaf_try_parse_dates(
                *right,
                schema,
                next_alias_id,
                hoisted,
            )),
        ),
        SqlExpr::Agg {
            func,
            distinct,
            arg,
        } => SqlExpr::Agg {
            func,
            distinct,
            arg: Box::new(rewrite_leaf_try_parse_dates(
                *arg,
                schema,
                next_alias_id,
                hoisted,
            )),
        },
        SqlExpr::Substring {
            str_expr,
            start,
            len,
        } => SqlExpr::Substring {
            str_expr: Box::new(rewrite_leaf_try_parse_dates(
                *str_expr,
                schema,
                next_alias_id,
                hoisted,
            )),
            start: Box::new(rewrite_leaf_try_parse_dates(
                *start,
                schema,
                next_alias_id,
                hoisted,
            )),
            len: Box::new(rewrite_leaf_try_parse_dates(
                *len,
                schema,
                next_alias_id,
                hoisted,
            )),
        },
        SqlExpr::InList { expr, items } => SqlExpr::InList {
            expr: Box::new(rewrite_leaf_try_parse_dates(
                *expr,
                schema,
                next_alias_id,
                hoisted,
            )),
            items: items
                .into_iter()
                .map(|item| rewrite_leaf_try_parse_dates(item, schema, next_alias_id, hoisted))
                .collect(),
        },
        SqlExpr::TrimAscii(inner) => SqlExpr::TrimAscii(Box::new(rewrite_leaf_try_parse_dates(
            *inner,
            schema,
            next_alias_id,
            hoisted,
        ))),
        SqlExpr::ExtractYear(inner) => SqlExpr::ExtractYear(Box::new(
            rewrite_leaf_try_parse_dates(*inner, schema, next_alias_id, hoisted),
        )),
        SqlExpr::AtTimeZone { expr, tz } => SqlExpr::AtTimeZone {
            expr: Box::new(rewrite_leaf_try_parse_dates(
                *expr,
                schema,
                next_alias_id,
                hoisted,
            )),
            tz: Box::new(rewrite_leaf_try_parse_dates(
                *tz,
                schema,
                next_alias_id,
                hoisted,
            )),
        },
        SqlExpr::RowNumber {
            partition_by,
            order_by,
        } => SqlExpr::RowNumber {
            partition_by: partition_by
                .into_iter()
                .map(|p| rewrite_leaf_try_parse_dates(p, schema, next_alias_id, hoisted))
                .collect(),
            order_by: order_by
                .into_iter()
                .map(|o| SqlOrderItem {
                    expr: rewrite_leaf_try_parse_dates(o.expr, schema, next_alias_id, hoisted),
                    dir: o.dir,
                })
                .collect(),
        },
        other @ (SqlExpr::Col { .. }
        | SqlExpr::Param { .. }
        | SqlExpr::Exists { .. }
        | SqlExpr::CountStar
        | SqlExpr::BoolLit(_)
        | SqlExpr::IntLit(_)) => other,
    }
}

// ===========================================================================
// BucketCol Shared SQL Translation
// ===========================================================================

fn translate_bucket_col(
    schema: &TableTy,
    name: &str,
    source: &str,
    cuts: &[Literal],
    labels: &[String],
    dialect: SqlDialect,
) -> Result<(SqlExpr, ColSpec), String> {
    let Some(src_col) = schema.find_col(source) else {
        return Err(format!("BucketCol references missing source `{source}`"));
    };
    if cuts.is_empty() || labels.len() != cuts.len() + 1 {
        return Err("invalid BucketCol cuts/labels".to_string());
    }
    if src_col.ty.is_option() || !is_dialect_exact_ord(dialect, &src_col.ty) {
        return Err(non_exact_type_reason(dialect, &src_col.ty, "BucketCol"));
    }
    let mut whens = Vec::with_capacity(cuts.len());
    for (cut_lit, lbl) in cuts.iter().zip(labels) {
        let (param, lit_ty, pg_cast) = literal_to_sql_param(cut_lit, dialect)?;
        if lit_ty != src_col.ty {
            return Err("BucketCol cut literal type mismatch".to_string());
        }
        let mut lhs = SqlExpr::Col {
            table_alias: None,
            name: source.to_string(),
        };
        if dialect == SqlDialect::Postgres && matches!(src_col.ty, ScalarTy::Text) {
            lhs = SqlExpr::CollateC(Box::new(lhs));
        }
        let rhs = SqlExpr::Param {
            slot: SqlParamSlot::Literal(param),
            pg_cast,
        };
        let cond = SqlExpr::Binary {
            op: "<",
            left: Box::new(lhs),
            right: Box::new(rhs),
        };
        let then_e = SqlExpr::Param {
            slot: SqlParamSlot::Literal(SqlParam::Text(lbl.clone())),
            pg_cast: Some("TEXT"),
        };
        whens.push((cond, then_e));
    }
    let last_lbl = labels
        .last()
        .ok_or_else(|| "BucketCol missing fallback label".to_string())?;
    let else_br = Box::new(SqlExpr::Param {
        slot: SqlParamSlot::Literal(SqlParam::Text(last_lbl.clone())),
        pg_cast: Some("TEXT"),
    });
    let spec = ColSpec {
        name: name.to_string(),
        ty: ScalarTy::Text,
        tags: src_col.tags.clone(),
        bucketed: true,
        agg_kind: AggKind::Raw,
    };
    Ok((SqlExpr::Case { whens, else_br }, spec))
}

fn translate_coarsen_col(
    schema: &TableTy,
    name: &str,
    source: &str,
    allow: &[String],
    other: &str,
    dialect: SqlDialect,
) -> Result<(SqlExpr, ColSpec), String> {
    let Some(src_col) = schema.find_col(source) else {
        return Err(format!("CoarsenCol references missing source `{source}`"));
    };
    if allow.is_empty() {
        return Err("invalid CoarsenCol empty allow list".to_string());
    }
    let is_text = matches!(&src_col.ty, ScalarTy::Text)
        || matches!(&src_col.ty, ScalarTy::Option(inner) if matches!(inner.as_ref(), ScalarTy::Text));
    if !is_text {
        return Err(non_exact_type_reason(dialect, &src_col.ty, "CoarsenCol"));
    }
    let mut whens = Vec::with_capacity(allow.len());
    for allowed in allow {
        let mut lhs = SqlExpr::Col {
            table_alias: None,
            name: source.to_string(),
        };
        if dialect == SqlDialect::Postgres {
            lhs = SqlExpr::CollateC(Box::new(lhs));
        }
        let rhs = SqlExpr::Param {
            slot: SqlParamSlot::Literal(SqlParam::Text(allowed.clone())),
            pg_cast: Some("TEXT"),
        };
        let cond = SqlExpr::Binary {
            op: "=",
            left: Box::new(lhs),
            right: Box::new(rhs),
        };
        let then_e = SqlExpr::Param {
            slot: SqlParamSlot::Literal(SqlParam::Text(allowed.clone())),
            pg_cast: Some("TEXT"),
        };
        whens.push((cond, then_e));
    }
    let else_br = Box::new(SqlExpr::Param {
        slot: SqlParamSlot::Literal(SqlParam::Text(other.to_string())),
        pg_cast: Some("TEXT"),
    });
    let spec = ColSpec {
        name: name.to_string(),
        ty: ScalarTy::Text,
        tags: src_col.tags.clone(),
        bucketed: true,
        agg_kind: AggKind::Raw,
    };
    Ok((SqlExpr::Case { whens, else_br }, spec))
}

// ===========================================================================
// Shared Core PrimOp SQL Translation
// ===========================================================================

fn translate_core_prim_sql(
    op: &PrimOp,
    args: Vec<(SqlExpr, ScalarTy, TagSet)>,
    dialect: SqlDialect,
) -> Result<(SqlExpr, ScalarTy, TagSet), String> {
    let union_tags = TagSet::union_list(args.iter().map(|(_, _, ts)| ts));
    match (op, args.as_slice()) {
        (PrimOp::SomeVal(inner_ty), [(e, ty, _)]) => {
            let Some(sty) = inner_ty.to_scalar_ty() else {
                return Err("SomeVal non-scalar type requires local VM".to_string());
            };
            if sty != *ty || sty.is_option() {
                return Err("SomeVal type mismatch requires local VM".to_string());
            }
            Ok((e.clone(), ScalarTy::Option(Box::new(sty)), union_tags))
        }
        (PrimOp::IsSome, [(e, ty, _)]) if ty.is_option() => Ok((
            SqlExpr::IsNull {
                negated: true,
                arg: Box::new(e.clone()),
            },
            ScalarTy::Bool,
            union_tags,
        )),
        (PrimOp::IsNone, [(e, ty, _)]) if ty.is_option() => Ok((
            SqlExpr::IsNull {
                negated: false,
                arg: Box::new(e.clone()),
            },
            ScalarTy::Bool,
            union_tags,
        )),
        (PrimOp::UnwrapOr, [(opt_e, opt_ty, _), (def_e, def_ty, _)]) => {
            if let ScalarTy::Option(inner) = opt_ty
                && **inner == *def_ty
            {
                Ok((
                    SqlExpr::Coalesce(Box::new(opt_e.clone()), Box::new(def_e.clone())),
                    def_ty.clone(),
                    union_tags,
                ))
            } else {
                Err("UnwrapOr type mismatch requires local VM".to_string())
            }
        }
        (PrimOp::NotBool, [(e, ScalarTy::Bool, _)]) => Ok((
            SqlExpr::Unary {
                op: "NOT",
                arg: Box::new(e.clone()),
            },
            ScalarTy::Bool,
            union_tags,
        )),
        (PrimOp::AndBool, [(a, ScalarTy::Bool, _), (b, ScalarTy::Bool, _)]) => Ok((
            SqlExpr::Binary {
                op: "AND",
                left: Box::new(a.clone()),
                right: Box::new(b.clone()),
            },
            ScalarTy::Bool,
            union_tags,
        )),
        (PrimOp::OrBool, [(a, ScalarTy::Bool, _), (b, ScalarTy::Bool, _)]) => Ok((
            SqlExpr::Binary {
                op: "OR",
                left: Box::new(a.clone()),
                right: Box::new(b.clone()),
            },
            ScalarTy::Bool,
            union_tags,
        )),
        (PrimOp::Eq | PrimOp::Ne, [(a, t1, _), (b, t2, _)]) => {
            if t1 != t2 {
                return Err("Eq/Ne operand type mismatch".to_string());
            }
            if !is_dialect_exact_eq(dialect, t1) {
                return Err(non_exact_type_reason(dialect, t1, "Eq/Ne"));
            }
            let negated = matches!(op, PrimOp::Ne);
            let sql_e = if t1.is_option() {
                SqlExpr::NullSafeEq {
                    negated,
                    left: Box::new(a.clone()),
                    right: Box::new(b.clone()),
                }
            } else {
                SqlExpr::Binary {
                    op: if negated { "<>" } else { "=" },
                    left: Box::new(a.clone()),
                    right: Box::new(b.clone()),
                }
            };
            Ok((sql_e, ScalarTy::Bool, union_tags))
        }
        (PrimOp::Lt | PrimOp::Le | PrimOp::Gt | PrimOp::Ge, [(a, t1, _), (b, t2, _)]) => {
            if t1 != t2 || t1.is_option() {
                return Err("ordered comparison requires matching non-Option types".to_string());
            }
            if !is_dialect_exact_ord(dialect, t1) {
                return Err(non_exact_type_reason(dialect, t1, "comparison"));
            }
            let lhs = if dialect == SqlDialect::Postgres && matches!(t1, ScalarTy::Text) {
                SqlExpr::CollateC(Box::new(a.clone()))
            } else {
                a.clone()
            };
            let op_str = match op {
                PrimOp::Lt => "<",
                PrimOp::Le => "<=",
                PrimOp::Gt => ">",
                PrimOp::Ge => ">=",
                _ => unreachable!("matched above"),
            };
            Ok((
                SqlExpr::Binary {
                    op: op_str,
                    left: Box::new(lhs),
                    right: Box::new(b.clone()),
                },
                ScalarTy::Bool,
                union_tags,
            ))
        }
        (PrimOp::ConcatText, [(a, ScalarTy::Text, _), (b, ScalarTy::Text, _)]) => Ok((
            SqlExpr::Binary {
                op: "||",
                left: Box::new(a.clone()),
                right: Box::new(b.clone()),
            },
            ScalarTy::Text,
            union_tags,
        )),
        (PrimOp::LowerAsciiText, [(a, ScalarTy::Text, _)]) => Ok((
            SqlExpr::Func {
                name: "LOWER",
                args: vec![a.clone()],
            },
            ScalarTy::Text,
            union_tags,
        )),
        (PrimOp::TrimText, [(a, ScalarTy::Text, _)]) => {
            let ws_param = SqlExpr::Param {
                slot: SqlParamSlot::Literal(SqlParam::Text(" \t\n\r".to_string())),
                pg_cast: Some("TEXT"),
            };
            let func = match dialect {
                SqlDialect::Sqlite => "TRIM",
                SqlDialect::Postgres => "BTRIM",
            };
            Ok((
                SqlExpr::Func {
                    name: func,
                    args: vec![a.clone(), ws_param],
                },
                ScalarTy::Text,
                union_tags,
            ))
        }
        (PrimOp::ContainsText, [(hay, ScalarTy::Text, _), (needle, ScalarTy::Text, _)]) => {
            let func = match dialect {
                SqlDialect::Sqlite => "INSTR",
                SqlDialect::Postgres => "STRPOS",
            };
            let pos_call = SqlExpr::Func {
                name: func,
                args: vec![hay.clone(), needle.clone()],
            };
            let zero = SqlExpr::Param {
                slot: SqlParamSlot::Literal(SqlParam::Int(0)),
                pg_cast: Some("INTEGER"),
            };
            Ok((
                SqlExpr::Binary {
                    op: ">",
                    left: Box::new(pos_call),
                    right: Box::new(zero),
                },
                ScalarTy::Bool,
                union_tags,
            ))
        }
        (PrimOp::EmptyText, [(a, ScalarTy::Text, _)]) => {
            let empty = SqlExpr::Param {
                slot: SqlParamSlot::Literal(SqlParam::Text(String::new())),
                pg_cast: Some("TEXT"),
            };
            Ok((
                SqlExpr::Binary {
                    op: "=",
                    left: Box::new(a.clone()),
                    right: Box::new(empty),
                },
                ScalarTy::Bool,
                union_tags,
            ))
        }
        (PrimOp::IntToText, [(a, ScalarTy::Int, _)]) => Ok((
            SqlExpr::Cast {
                expr: Box::new(a.clone()),
                ty: "TEXT",
            },
            ScalarTy::Text,
            union_tags,
        )),
        (
            PrimOp::AddInt
            | PrimOp::SubInt
            | PrimOp::MulInt
            | PrimOp::DivInt
            | PrimOp::ModInt
            | PrimOp::NegInt,
            _,
        ) => Err(format!("checked integer op `{op:?}` requires local VM")),
        (
            PrimOp::AddDec
            | PrimOp::SubDec
            | PrimOp::MulDec
            | PrimOp::DivDec
            | PrimOp::NegDec
            | PrimOp::IntToDec,
            _,
        ) => Err(format!("checked decimal op `{op:?}` requires local VM")),
        (PrimOp::UnwrapBang, _) => Err("trapping unwrap (!) requires local VM".to_string()),
        _ => Err(format!("primitive op `{op:?}` requires local VM")),
    }
}

// ===========================================================================
// Core IR Pushdown Splitter (`core::Plan`)
// ===========================================================================

enum NodeSplit<P> {
    Pushed(PushedNode),
    Hybrid {
        pushed: PushedNode,
        placeholder_var: Ident,
        local_plan: P,
        reason: String,
    },
    LocalOnly {
        reason: String,
    },
}

struct CoreSplitCtx<'a> {
    prog: &'a Program,
    target_db: Option<&'a str>,
    dialect: SqlDialect,
    lock: Option<&'a SchemaLockFile>,
    db_vars: HashMap<Ident, Ident>,
    outer_var_tys: HashMap<Ident, (ScalarTy, TagSet)>,
}

impl<'a> CoreSplitCtx<'a> {
    fn new(
        prog: &'a Program,
        target_db: Option<&'a str>,
        dialect: SqlDialect,
        lock: Option<&'a SchemaLockFile>,
    ) -> Self {
        let mut db_vars = HashMap::new();
        let mut outer_var_tys = HashMap::new();
        for f in &prog.funs {
            for (name, lty) in &f.params {
                if let Ty::ReadDB(db) = &lty.ty {
                    db_vars.insert(name.clone(), db.clone());
                } else if let Some(sty) = lty.ty.to_scalar_ty() {
                    outer_var_tys.insert(name.clone(), (sty, lty.effective_tags()));
                }
            }
            collect_core_let_bindings(&f.body, &mut db_vars, &mut outer_var_tys);
        }
        Self {
            prog,
            target_db,
            dialect,
            lock,
            db_vars,
            outer_var_tys,
        }
    }

    fn resolve_source_db(&self, cap: &Expr) -> Option<Ident> {
        match cap {
            Expr::Host {
                op: HostOp::FakeDB(db),
                ..
            } => Some(db.clone()),
            Expr::Var(v) => {
                if let Some(db) = self.db_vars.get(v) {
                    Some(db.clone())
                } else if self.prog.funs.is_empty() {
                    self.target_db
                        .filter(|t| v == t || v == "db")
                        .map(str::to_string)
                        .or_else(|| Some(v.clone()))
                } else if let Some(t) = self.target_db
                    && v == t
                {
                    Some(t.to_string())
                } else {
                    None
                }
            }
            _ => None,
        }
    }
}

fn collect_core_let_bindings(
    expr: &Expr,
    db_vars: &mut HashMap<Ident, Ident>,
    outer_var_tys: &mut HashMap<Ident, (ScalarTy, TagSet)>,
) {
    let mut stack = vec![expr];
    while let Some(cur) = stack.pop() {
        match cur {
            Expr::LetE {
                name,
                lty,
                bound,
                body,
            } => {
                if let Ty::ReadDB(db) = &lty.ty {
                    db_vars.insert(name.clone(), db.clone());
                } else if let Some(sty) = lty.ty.to_scalar_ty() {
                    outer_var_tys.insert(name.clone(), (sty, lty.effective_tags()));
                }
                stack.push(body);
                stack.push(bound);
            }
            Expr::IfE {
                cond,
                then_br,
                else_br,
            } => {
                stack.push(else_br);
                stack.push(then_br);
                stack.push(cond);
            }
            Expr::CaseE { scrut, arms } => {
                stack.push(scrut);
                for a in arms {
                    stack.push(&a.body);
                }
            }
            Expr::Lam { params, body, .. } => {
                for (name, lty) in params {
                    if let Ty::ReadDB(db) = &lty.ty {
                        db_vars.insert(name.clone(), db.clone());
                    } else if let Some(sty) = lty.ty.to_scalar_ty() {
                        outer_var_tys.insert(name.clone(), (sty, lty.effective_tags()));
                    }
                }
                stack.push(body);
            }
            Expr::Join {
                params, rhs, body, ..
            } => {
                for (name, lty) in params {
                    if let Ty::ReadDB(db) = &lty.ty {
                        db_vars.insert(name.clone(), db.clone());
                    } else if let Some(sty) = lty.ty.to_scalar_ty() {
                        outer_var_tys.insert(name.clone(), (sty, lty.effective_tags()));
                    }
                }
                stack.push(body);
                stack.push(rhs);
            }
            Expr::App { fn_expr, args } => {
                stack.push(fn_expr);
                stack.extend(args);
            }
            Expr::Call { args, .. }
            | Expr::Jump { args, .. }
            | Expr::Tuple(args)
            | Expr::Ctor { args, .. }
            | Expr::Prim { args, .. }
            | Expr::Host { args, .. } => stack.extend(args),
            Expr::Proj { tup: e, .. } | Expr::Fail(e) => stack.push(e),
            Expr::Stop {
                detail: Some(d), ..
            } => stack.push(d),
            Expr::Lit(_)
            | Expr::Var(_)
            | Expr::ConstRef(_)
            | Expr::TableLit { .. }
            | Expr::Rel(_)
            | Expr::Stop { detail: None, .. } => {}
        }
    }
}

fn core_plan_has_source_db(plan: &Plan, ctx: &CoreSplitCtx<'_>, filter_db: Option<&str>) -> bool {
    let mut stack = vec![plan];
    while let Some(cur) = stack.pop() {
        match cur {
            Plan::SourceDB { cap, .. } => {
                if let Some(target) = filter_db {
                    if ctx.resolve_source_db(cap).as_deref() == Some(target) {
                        return true;
                    }
                } else {
                    return true;
                }
            }
            Plan::SourceExpr(_) => {}
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
            | Plan::Pseudonymize { input, .. } => stack.push(input),
            Plan::Join { left, right, .. } | Plan::Union { left, right } => {
                stack.push(left);
                stack.push(right);
            }
        }
    }
    false
}

/// Conservatively check whether a Core IR `Sort` is guaranteed to discard input row order.
fn core_sort_is_total_hint(plan: &Plan, keys: &[(Ident, SortDir)], ctx: &CoreSplitCtx<'_>) -> bool {
    if keys.is_empty() {
        return false;
    }
    let key_names: Vec<Ident> = keys.iter().map(|(k, _)| k.clone()).collect();
    if let Some((cols, uqs)) = core_plan_cols_and_uqs_hint(plan, ctx) {
        if cols.iter().all(|c| key_names.contains(c)) {
            return true;
        }
        if uqs
            .iter()
            .any(|uk| uk.iter().all(|k| key_names.contains(k)))
        {
            return true;
        }
    }
    false
}

fn join_cols_and_uqs_hint(
    kind: JoinKind,
    l_cols: Vec<Ident>,
    l_uqs: Vec<Vec<Ident>>,
    r_cols: &[Ident],
    r_uqs: &[Vec<Ident>],
    on: &JoinOn,
    suffixes: Option<&(Ident, Ident)>,
) -> Option<(Vec<Ident>, Vec<Vec<Ident>>)> {
    if matches!(kind, JoinKind::Semi | JoinKind::Anti) {
        return Some((l_cols, l_uqs));
    }
    let same_keys: &[Ident] = match on {
        JoinOn::SameKeys(ks) => ks,
        JoinOn::Pairs(_) => &[],
    };
    let r_kept: Vec<Ident> = r_cols
        .iter()
        .filter(|rc| !same_keys.contains(rc))
        .cloned()
        .collect();
    let has_collision = l_cols.iter().any(|lc| r_kept.contains(lc));
    let (out_cols, l_renames): (Vec<Ident>, HashMap<Ident, Ident>) = if !has_collision {
        let mut combined = l_cols;
        combined.extend(r_kept);
        (combined, HashMap::new())
    } else if let Some((sl, sr)) = suffixes {
        let mut ren = HashMap::new();
        let mut combined: Vec<Ident> = l_cols
            .iter()
            .map(|c| {
                if r_kept.contains(c) {
                    let nc = format!("{c}{sl}");
                    ren.insert(c.clone(), nc.clone());
                    nc
                } else {
                    c.clone()
                }
            })
            .collect();
        for c in &r_kept {
            if l_cols.contains(c) {
                combined.push(format!("{c}{sr}"));
            } else {
                combined.push(c.clone());
            }
        }
        (combined, ren)
    } else {
        return None;
    };
    let r_join_keys: Vec<Ident> = match on {
        JoinOn::SameKeys(ks) => ks.clone(),
        JoinOn::Pairs(ps) => ps.iter().map(|(_, r)| r.clone()).collect(),
    };
    let right_is_unique = r_uqs
        .iter()
        .any(|uk| uk.iter().all(|k| r_join_keys.contains(k)));
    let mut out_uqs = Vec::new();
    if right_is_unique {
        for uk in l_uqs {
            out_uqs.push(
                uk.into_iter()
                    .map(|k| l_renames.get(&k).cloned().unwrap_or(k))
                    .collect(),
            );
        }
    }
    Some((out_cols, out_uqs))
}

fn core_plan_cols_and_uqs_hint(
    plan: &Plan,
    ctx: &CoreSplitCtx<'_>,
) -> Option<(Vec<Ident>, Vec<Vec<Ident>>)> {
    match plan {
        Plan::SourceDB {
            cap,
            table_name,
            schema,
        } => {
            let cols = schema.col_names();
            let mut uqs = Vec::new();
            if let Some(db) = ctx.resolve_source_db(cap)
                && let Some(pk) = ctx
                    .lock
                    .and_then(|l| l.find_db(&db))
                    .and_then(|d| d.resolve_table(table_name).ok())
                    .map(|t| {
                        t.cols
                            .iter()
                            .filter(|c| c.pk)
                            .map(|c| c.name.clone())
                            .collect::<Vec<_>>()
                    })
                && !pk.is_empty()
                && pk.iter().all(|k| cols.contains(k))
            {
                uqs.push(pk);
            }
            Some((cols, uqs))
        }
        Plan::Select { input, cols } => {
            let (_, mut uqs) = core_plan_cols_and_uqs_hint(input, ctx)?;
            uqs.retain(|uk| uk.iter().all(|k| cols.contains(k)));
            Some((cols.clone(), uqs))
        }
        Plan::Drop { input, cols } => {
            let (mut c, mut uqs) = core_plan_cols_and_uqs_hint(input, ctx)?;
            c.retain(|x| !cols.contains(x));
            uqs.retain(|uk| uk.iter().all(|k| c.contains(k)));
            Some((c, uqs))
        }
        Plan::Rename { input, pairs } => {
            let (cols, uqs) = core_plan_cols_and_uqs_hint(input, ctx)?;
            let map_name = |c: Ident| {
                pairs
                    .iter()
                    .find(|(_, old_n)| *old_n == c)
                    .map_or(c, |(new_n, _)| new_n.clone())
            };
            let new_cols = cols.into_iter().map(map_name).collect();
            let new_uqs = uqs
                .into_iter()
                .map(|uk| uk.into_iter().map(map_name).collect())
                .collect();
            Some((new_cols, new_uqs))
        }
        Plan::Derive { input, items } => {
            let (mut cols, mut uqs) = core_plan_cols_and_uqs_hint(input, ctx)?;
            for it in items {
                let name = match it {
                    DeriveItem::ColExpr { name, .. } | DeriveItem::BucketCol { name, .. } => name,
                };
                if cols.contains(name) {
                    uqs.retain(|uk| !uk.contains(name));
                } else {
                    cols.push(name.clone());
                }
            }
            Some((cols, uqs))
        }
        Plan::Filter { input, .. }
        | Plan::Sort { input, .. }
        | Plan::Limit { input, .. }
        | Plan::GroupBy { input, .. }
        | Plan::SuppressSmallGroups { input, .. } => core_plan_cols_and_uqs_hint(input, ctx),
        Plan::Distinct { input, cols } => {
            let (in_cols, mut uqs) = core_plan_cols_and_uqs_hint(input, ctx)?;
            if cols.is_empty() || in_cols.iter().all(|c| cols.contains(c)) {
                uqs.push(in_cols.clone());
            }
            Some((in_cols, uqs))
        }
        Plan::Redact { input, col, .. } | Plan::Pseudonymize { input, col, .. } => {
            let (cols, mut uqs) = core_plan_cols_and_uqs_hint(input, ctx)?;
            uqs.retain(|uk| !uk.contains(col));
            Some((cols, uqs))
        }
        Plan::Summarize { input, aggs, .. } => {
            let (in_cols, _) = core_plan_cols_and_uqs_hint(input, ctx)?;
            let gks: Vec<Ident> = match input.as_ref() {
                Plan::GroupBy { keys, .. } => {
                    in_cols.into_iter().filter(|c| keys.contains(c)).collect()
                }
                _ => Vec::new(),
            };
            let mut out_cols = gks.clone();
            out_cols.extend(aggs.iter().map(|a| a.name.clone()));
            Some((out_cols, vec![gks]))
        }
        Plan::Join {
            kind,
            left,
            right,
            on,
            suffixes,
        } => {
            let (l_cols, l_uqs) = core_plan_cols_and_uqs_hint(left, ctx)?;
            if matches!(kind, JoinKind::Semi | JoinKind::Anti) {
                return Some((l_cols, l_uqs));
            }
            let (r_cols, r_uqs) = core_plan_cols_and_uqs_hint(right, ctx)?;
            join_cols_and_uqs_hint(*kind, l_cols, l_uqs, &r_cols, &r_uqs, on, suffixes.as_ref())
        }
        Plan::Union { left, .. } => {
            let (cols, _) = core_plan_cols_and_uqs_hint(left, ctx)?;
            Some((cols, Vec::new()))
        }
        _ => None,
    }
}

fn translate_core_row_expr(
    re: &RowExpr,
    schema: &TableTy,
    ctx: &CoreSplitCtx<'_>,
) -> Result<(SqlExpr, ScalarTy, TagSet), String> {
    match re {
        RowExpr::Lit(lit) => {
            let (param, sty, pg_cast) = literal_to_sql_param(lit, ctx.dialect)?;
            Ok((
                SqlExpr::Param {
                    slot: SqlParamSlot::Literal(param),
                    pg_cast,
                },
                sty,
                TagSet::empty(),
            ))
        }
        RowExpr::Col(name) => {
            let Some(col) = schema.find_col(name) else {
                return Err(format!("missing column `{name}` in RowExpr"));
            };
            Ok((
                SqlExpr::Col {
                    table_alias: None,
                    name: name.clone(),
                },
                col.ty.clone(),
                col.tags.clone(),
            ))
        }
        RowExpr::OuterVar(name) => {
            let Some((sty, tags)) = ctx.outer_var_tys.get(name) else {
                return Err(format!(
                    "outer variable `{name}` scalar type unavailable for SQL pushdown"
                ));
            };
            if !is_sql_column_supported(sty) {
                return Err(format!(
                    "outer variable `{name}` has non-SQL type `{sty:?}`"
                ));
            }
            Ok((
                SqlExpr::Param {
                    slot: SqlParamSlot::OuterVar(name.clone()),
                    pg_cast: pg_sql_type_name(sty),
                },
                sty.clone(),
                tags.clone(),
            ))
        }
        RowExpr::ConstRef(name) => {
            let Some(c_decl) = ctx.prog.find_const(name) else {
                return Err(format!("unknown constant `{name}` in RowExpr"));
            };
            let Some(sty) = c_decl.lty.ty.to_scalar_ty() else {
                return Err(format!("non-scalar constant `{name}` requires local VM"));
            };
            // Validate literal range as well.
            let _ = literal_to_sql_param(&c_decl.value, ctx.dialect)?;
            Ok((
                SqlExpr::Param {
                    slot: SqlParamSlot::ConstRef(name.clone()),
                    pg_cast: pg_sql_type_name(&sty),
                },
                sty,
                c_decl.lty.effective_tags(),
            ))
        }
        RowExpr::CallPure { fn_name, .. } => Err(format!(
            "pure UDF call `{fn_name}` requires local bytecode VM"
        )),
        RowExpr::IfE {
            cond,
            then_br,
            else_br,
        } => {
            let (c_e, c_ty, c_tags) = translate_core_row_expr(cond, schema, ctx)?;
            if c_ty != ScalarTy::Bool {
                return Err("IfE condition must be Bool".to_string());
            }
            let (t_e, t_ty, t_tags) = translate_core_row_expr(then_br, schema, ctx)?;
            let (e_e, e_ty, e_tags) = translate_core_row_expr(else_br, schema, ctx)?;
            if t_ty != e_ty {
                return Err("IfE branch type mismatch".to_string());
            }
            Ok((
                SqlExpr::Case {
                    whens: vec![(c_e, t_e)],
                    else_br: Box::new(e_e),
                },
                t_ty,
                c_tags.union(&t_tags).union(&e_tags),
            ))
        }
        RowExpr::Coalesce {
            opt_expr,
            default_expr,
        } => {
            let (o_e, o_ty, o_tags) = translate_core_row_expr(opt_expr, schema, ctx)?;
            let (d_e, d_ty, d_tags) = translate_core_row_expr(default_expr, schema, ctx)?;
            match &o_ty {
                ScalarTy::Option(inner) if **inner == d_ty => Ok((
                    SqlExpr::Coalesce(Box::new(o_e), Box::new(d_e)),
                    d_ty,
                    o_tags.union(&d_tags),
                )),
                _ => Err("Coalesce type mismatch".to_string()),
            }
        }
        RowExpr::Prim { op, args } => {
            let mut translated = Vec::with_capacity(args.len());
            for a in args {
                translated.push(translate_core_row_expr(a, schema, ctx)?);
            }
            translate_core_prim_sql(op, translated, ctx.dialect)
        }
    }
}

fn core_placeholder_plan(var: &str) -> Plan {
    Plan::SourceExpr(Box::new(Expr::Var(var.to_string())))
}

fn rebuild_core_unary(stage: &Plan, new_input: Plan) -> Plan {
    match stage {
        Plan::Select { cols, .. } => Plan::Select {
            input: Box::new(new_input),
            cols: cols.clone(),
        },
        Plan::Drop { cols, .. } => Plan::Drop {
            input: Box::new(new_input),
            cols: cols.clone(),
        },
        Plan::Rename { pairs, .. } => Plan::Rename {
            input: Box::new(new_input),
            pairs: pairs.clone(),
        },
        Plan::Derive { items, .. } => Plan::Derive {
            input: Box::new(new_input),
            items: items.clone(),
        },
        Plan::Filter { pred, .. } => Plan::Filter {
            input: Box::new(new_input),
            pred: pred.clone(),
        },
        Plan::Distinct { cols, .. } => Plan::Distinct {
            input: Box::new(new_input),
            cols: cols.clone(),
        },
        Plan::Sort { keys, .. } => Plan::Sort {
            input: Box::new(new_input),
            keys: keys.clone(),
        },
        Plan::Limit { n, .. } => Plan::Limit {
            input: Box::new(new_input),
            n: n.clone(),
        },
        Plan::GroupBy { keys, .. } => Plan::GroupBy {
            input: Box::new(new_input),
            keys: keys.clone(),
        },
        Plan::Summarize {
            aggs, distinct_key, ..
        } => Plan::Summarize {
            input: Box::new(new_input),
            aggs: aggs.clone(),
            distinct_key: distinct_key.clone(),
        },
        Plan::SuppressSmallGroups {
            min_k,
            distinct_by,
            mode,
            ..
        } => Plan::SuppressSmallGroups {
            input: Box::new(new_input),
            min_k: min_k.clone(),
            distinct_by: distinct_by.clone(),
            mode: *mode,
        },
        Plan::Window { items, .. } => Plan::Window {
            input: Box::new(new_input),
            items: items.clone(),
        },
        Plan::FillGaps {
            col,
            step_micros,
            over,
            fill,
            ..
        } => Plan::FillGaps {
            input: Box::new(new_input),
            col: col.clone(),
            step_micros: step_micros.clone(),
            over: over.clone(),
            fill: fill.clone(),
        },
        Plan::PivotWider {
            names_from,
            values_from,
            static_cols,
            fill,
            ..
        } => Plan::PivotWider {
            input: Box::new(new_input),
            names_from: names_from.clone(),
            values_from: values_from.clone(),
            static_cols: static_cols.clone(),
            fill: fill.clone(),
        },
        Plan::Crosstab {
            rows_col,
            cols_col,
            values_col,
            fill,
            ..
        } => Plan::Crosstab {
            input: Box::new(new_input),
            rows_col: rows_col.clone(),
            cols_col: cols_col.clone(),
            values_col: values_col.clone(),
            fill: fill.clone(),
        },
        Plan::Redact {
            col, replacement, ..
        } => Plan::Redact {
            input: Box::new(new_input),
            col: col.clone(),
            replacement: replacement.clone(),
        },
        Plan::Pseudonymize { col, secret, .. } => Plan::Pseudonymize {
            input: Box::new(new_input),
            col: col.clone(),
            secret: secret.clone(),
        },
        other => other.clone(),
    }
}

fn split_core_node(
    plan: &Plan,
    ctx: &CoreSplitCtx<'_>,
    order_insensitive: bool,
    parent_is_suppress: bool,
) -> NodeSplit<Plan> {
    const PLACEHOLDER: &str = "__dana_pushdown_0";

    match plan {
        Plan::SourceExpr(_) => NodeSplit::LocalOnly {
            reason: "in-memory source expression requires local VM".to_string(),
        },
        Plan::SourceDB {
            cap,
            table_name,
            schema,
        } => {
            let Some(resolved_db) = ctx.resolve_source_db(cap) else {
                return NodeSplit::LocalOnly {
                    reason: format!("unable to resolve database binding for table `{table_name}`"),
                };
            };
            if let Some(target) = ctx.target_db
                && resolved_db != target
            {
                return NodeSplit::LocalOnly {
                    reason: format!(
                        "table `{table_name}` belongs to database `{resolved_db}`, not `{target}`"
                    ),
                };
            }
            match PushedNode::from_source_db(
                &resolved_db,
                table_name,
                schema,
                ctx.lock,
                ctx.dialect,
            ) {
                Ok(node) => NodeSplit::Pushed(node),
                Err(reason) => NodeSplit::LocalOnly { reason },
            }
        }
        Plan::Select { input, cols } => match split_core_node(input, ctx, order_insensitive, false)
        {
            NodeSplit::Pushed(node) => match node.apply_select(cols) {
                Ok(next) => NodeSplit::Pushed(next),
                Err(reason) => NodeSplit::LocalOnly { reason },
            },
            NodeSplit::Hybrid {
                pushed,
                placeholder_var,
                local_plan,
                reason,
            } => NodeSplit::Hybrid {
                pushed,
                placeholder_var,
                local_plan: rebuild_core_unary(plan, local_plan),
                reason,
            },
            NodeSplit::LocalOnly { reason } => NodeSplit::LocalOnly { reason },
        },
        Plan::Drop { input, cols } => match split_core_node(input, ctx, order_insensitive, false) {
            NodeSplit::Pushed(node) => match node.apply_drop(cols) {
                Ok(next) => NodeSplit::Pushed(next),
                Err(reason) => NodeSplit::LocalOnly { reason },
            },
            NodeSplit::Hybrid {
                pushed,
                placeholder_var,
                local_plan,
                reason,
            } => NodeSplit::Hybrid {
                pushed,
                placeholder_var,
                local_plan: rebuild_core_unary(plan, local_plan),
                reason,
            },
            NodeSplit::LocalOnly { reason } => NodeSplit::LocalOnly { reason },
        },
        Plan::Rename { input, pairs } => {
            match split_core_node(input, ctx, order_insensitive, false) {
                NodeSplit::Pushed(node) => {
                    // Core IR `Plan::Rename` stores `(new_name, old_name)`!
                    let old_to_new: Vec<(Ident, Ident)> = pairs
                        .iter()
                        .map(|(new_n, old_n)| (old_n.clone(), new_n.clone()))
                        .collect();
                    match node.apply_rename(&old_to_new) {
                        Ok(next) => NodeSplit::Pushed(next),
                        Err(reason) => NodeSplit::LocalOnly { reason },
                    }
                }
                NodeSplit::Hybrid {
                    pushed,
                    placeholder_var,
                    local_plan,
                    reason,
                } => NodeSplit::Hybrid {
                    pushed,
                    placeholder_var,
                    local_plan: rebuild_core_unary(plan, local_plan),
                    reason,
                },
                NodeSplit::LocalOnly { reason } => NodeSplit::LocalOnly { reason },
            }
        }
        Plan::Filter { input, pred } => match split_core_node(input, ctx, order_insensitive, false)
        {
            NodeSplit::Pushed(node) => match translate_core_row_expr(pred, &node.schema, ctx) {
                Ok((sql_e, ScalarTy::Bool, p_tags)) => {
                    NodeSplit::Pushed(node.apply_filter(sql_e, &p_tags))
                }
                Ok(_) => NodeSplit::Hybrid {
                    pushed: node,
                    placeholder_var: PLACEHOLDER.to_string(),
                    local_plan: rebuild_core_unary(plan, core_placeholder_plan(PLACEHOLDER)),
                    reason: "filter predicate did not type-check as Bool".to_string(),
                },
                Err(reason) => NodeSplit::Hybrid {
                    pushed: node,
                    placeholder_var: PLACEHOLDER.to_string(),
                    local_plan: rebuild_core_unary(plan, core_placeholder_plan(PLACEHOLDER)),
                    reason,
                },
            },
            NodeSplit::Hybrid {
                pushed,
                placeholder_var,
                local_plan,
                reason,
            } => NodeSplit::Hybrid {
                pushed,
                placeholder_var,
                local_plan: rebuild_core_unary(plan, local_plan),
                reason,
            },
            NodeSplit::LocalOnly { reason } => NodeSplit::LocalOnly { reason },
        },
        Plan::Derive { input, items } => {
            match split_core_node(input, ctx, order_insensitive, false) {
                NodeSplit::Pushed(node) => {
                    let orig = node.clone();
                    let mut cur = node;
                    let mut waves = DeriveWaveState::new(cur.schema.clone(), items.len());
                    let mut names = Vec::with_capacity(items.len());
                    for item in items {
                        match item {
                            DeriveItem::ColExpr { name, expr } => {
                                match translate_core_row_expr(expr, &waves.working_schema, ctx) {
                                    Ok((sql_e, sty, tags)) => {
                                        let spec = ColSpec {
                                            name: name.clone(),
                                            ty: sty,
                                            tags,
                                            bucketed: false,
                                            agg_kind: AggKind::Raw,
                                        };
                                        cur = waves.push_item(cur, name, sql_e, spec);
                                        names.push(name.clone());
                                    }
                                    Err(reason) => {
                                        return NodeSplit::Hybrid {
                                            pushed: orig,
                                            placeholder_var: PLACEHOLDER.to_string(),
                                            local_plan: rebuild_core_unary(
                                                plan,
                                                core_placeholder_plan(PLACEHOLDER),
                                            ),
                                            reason,
                                        };
                                    }
                                }
                            }
                            DeriveItem::BucketCol {
                                name,
                                source,
                                cuts,
                                labels,
                            } => match translate_bucket_col(
                                &waves.working_schema,
                                name,
                                source,
                                cuts,
                                labels,
                                ctx.dialect,
                            ) {
                                Ok((sql_e, spec)) => {
                                    cur = waves.push_item(cur, name, sql_e, spec);
                                    names.push(name.clone());
                                }
                                Err(reason) => {
                                    return NodeSplit::Hybrid {
                                        pushed: orig,
                                        placeholder_var: PLACEHOLDER.to_string(),
                                        local_plan: rebuild_core_unary(
                                            plan,
                                            core_placeholder_plan(PLACEHOLDER),
                                        ),
                                        reason,
                                    };
                                }
                            },
                        }
                    }
                    cur = waves.finish(cur);
                    cur.pushed_ops
                        .push(format!("Derive([{}])", names.join(", ")));
                    NodeSplit::Pushed(cur)
                }
                NodeSplit::Hybrid {
                    pushed,
                    placeholder_var,
                    local_plan,
                    reason,
                } => NodeSplit::Hybrid {
                    pushed,
                    placeholder_var,
                    local_plan: rebuild_core_unary(plan, local_plan),
                    reason,
                },
                NodeSplit::LocalOnly { reason } => NodeSplit::LocalOnly { reason },
            }
        }
        Plan::Redact {
            input,
            col,
            replacement,
        } => match split_core_node(input, ctx, order_insensitive, false) {
            NodeSplit::Pushed(node) => {
                let orig = node.clone();
                match node.apply_redact(col, replacement) {
                    Ok(next) => NodeSplit::Pushed(next),
                    Err(reason) => NodeSplit::Hybrid {
                        pushed: orig,
                        placeholder_var: PLACEHOLDER.to_string(),
                        local_plan: rebuild_core_unary(plan, core_placeholder_plan(PLACEHOLDER)),
                        reason,
                    },
                }
            }
            NodeSplit::Hybrid {
                pushed,
                placeholder_var,
                local_plan,
                reason,
            } => NodeSplit::Hybrid {
                pushed,
                placeholder_var,
                local_plan: rebuild_core_unary(plan, local_plan),
                reason,
            },
            NodeSplit::LocalOnly { reason } => NodeSplit::LocalOnly { reason },
        },
        Plan::Sort { input, keys } => {
            let child_ord_insens = order_insensitive || core_sort_is_total_hint(input, keys, ctx);
            match split_core_node(input, ctx, child_ord_insens, false) {
                NodeSplit::Pushed(node) => {
                    let orig = node.clone();
                    match node.apply_sort(keys, ctx.dialect) {
                        Ok(next) => NodeSplit::Pushed(next),
                        Err(reason) => NodeSplit::Hybrid {
                            pushed: orig,
                            placeholder_var: PLACEHOLDER.to_string(),
                            local_plan: rebuild_core_unary(
                                plan,
                                core_placeholder_plan(PLACEHOLDER),
                            ),
                            reason,
                        },
                    }
                }
                NodeSplit::Hybrid {
                    pushed,
                    placeholder_var,
                    local_plan,
                    reason,
                } => NodeSplit::Hybrid {
                    pushed,
                    placeholder_var,
                    local_plan: rebuild_core_unary(plan, local_plan),
                    reason,
                },
                NodeSplit::LocalOnly { reason } => NodeSplit::LocalOnly { reason },
            }
        }
        Plan::Limit { input, n } => match split_core_node(input, ctx, false, false) {
            NodeSplit::Pushed(node) => {
                let orig = node.clone();
                match node.apply_limit(n) {
                    Ok(next) => NodeSplit::Pushed(next),
                    Err(reason) => NodeSplit::Hybrid {
                        pushed: orig,
                        placeholder_var: PLACEHOLDER.to_string(),
                        local_plan: rebuild_core_unary(plan, core_placeholder_plan(PLACEHOLDER)),
                        reason,
                    },
                }
            }
            NodeSplit::Hybrid {
                pushed,
                placeholder_var,
                local_plan,
                reason,
            } => NodeSplit::Hybrid {
                pushed,
                placeholder_var,
                local_plan: rebuild_core_unary(plan, local_plan),
                reason,
            },
            NodeSplit::LocalOnly { reason } => NodeSplit::LocalOnly { reason },
        },
        Plan::Distinct { input, cols } => {
            let covers_all_hint = cols.is_empty()
                || core_plan_cols_and_uqs_hint(input, ctx)
                    .is_some_and(|(in_cols, _)| in_cols.iter().all(|c| cols.contains(c)));
            let child_ord_insens = order_insensitive && covers_all_hint;
            match split_core_node(input, ctx, child_ord_insens, false) {
                NodeSplit::Pushed(node) => {
                    let orig = node.clone();
                    match node.apply_distinct(cols, ctx.dialect, order_insensitive) {
                        Ok(next) => NodeSplit::Pushed(next),
                        Err(reason) => NodeSplit::Hybrid {
                            pushed: orig,
                            placeholder_var: PLACEHOLDER.to_string(),
                            local_plan: rebuild_core_unary(
                                plan,
                                core_placeholder_plan(PLACEHOLDER),
                            ),
                            reason,
                        },
                    }
                }
                NodeSplit::Hybrid {
                    pushed,
                    placeholder_var,
                    local_plan,
                    reason,
                } => NodeSplit::Hybrid {
                    pushed,
                    placeholder_var,
                    local_plan: rebuild_core_unary(plan, local_plan),
                    reason,
                },
                NodeSplit::LocalOnly { reason } => NodeSplit::LocalOnly { reason },
            }
        }
        Plan::GroupBy { input, .. } => {
            // Standalone GroupBy (not paired with a pushable Summarize) stays in local_suffix
            // so `agg_kind = GroupKey` is preserved for the local Summarize.
            match split_core_node(input, ctx, order_insensitive, false) {
                NodeSplit::Pushed(node) => NodeSplit::Hybrid {
                    pushed: node,
                    placeholder_var: PLACEHOLDER.to_string(),
                    local_plan: rebuild_core_unary(plan, core_placeholder_plan(PLACEHOLDER)),
                    reason: "unpaired group_by stays local for downstream summarize".to_string(),
                },
                NodeSplit::Hybrid {
                    pushed,
                    placeholder_var,
                    local_plan,
                    reason,
                } => NodeSplit::Hybrid {
                    pushed,
                    placeholder_var,
                    local_plan: rebuild_core_unary(plan, local_plan),
                    reason,
                },
                NodeSplit::LocalOnly { reason } => NodeSplit::LocalOnly { reason },
            }
        }
        Plan::Summarize {
            input,
            aggs,
            distinct_key,
        } => {
            let (raw_inner, group_keys, has_gb) = match input.as_ref() {
                Plan::GroupBy { input: gb_in, keys } => (gb_in.as_ref(), keys.as_slice(), true),
                other => (other, &[][..], false),
            };
            let child_ord_insens = !aggs.iter().any(|a| a.op.is_order_sensitive());
            let wrap_local = |inner_local: Plan| {
                let mid = if has_gb {
                    Plan::GroupBy {
                        input: Box::new(inner_local),
                        keys: group_keys.to_vec(),
                    }
                } else {
                    inner_local
                };
                rebuild_core_unary(plan, mid)
            };

            match split_core_node(raw_inner, ctx, child_ord_insens, false) {
                NodeSplit::Pushed(node) => {
                    if parent_is_suppress {
                        return NodeSplit::Hybrid {
                            pushed: node,
                            placeholder_var: PLACEHOLDER.to_string(),
                            local_plan: wrap_local(core_placeholder_plan(PLACEHOLDER)),
                            reason: "suppress_small_groups requires local group cardinality metadata from summarize".to_string(),
                        };
                    }
                    let orig = node.clone();
                    let mut translated_aggs = Vec::with_capacity(aggs.len());
                    for AggItem { name, op, arg } in aggs {
                        let t_arg = match arg {
                            None => None,
                            Some(re) => match translate_core_row_expr(re, &node.schema, ctx) {
                                Ok(t) => Some(t),
                                Err(reason) => {
                                    return NodeSplit::Hybrid {
                                        pushed: orig,
                                        placeholder_var: PLACEHOLDER.to_string(),
                                        local_plan: wrap_local(core_placeholder_plan(PLACEHOLDER)),
                                        reason,
                                    };
                                }
                            },
                        };
                        translated_aggs.push((name.clone(), ExecAggOp::Core(*op), t_arg));
                    }
                    match node.apply_summarize(
                        group_keys,
                        &translated_aggs,
                        distinct_key.as_deref(),
                        ctx.dialect,
                        true,
                        None,
                    ) {
                        Ok(next) => NodeSplit::Pushed(next),
                        Err(reason) => NodeSplit::Hybrid {
                            pushed: orig,
                            placeholder_var: PLACEHOLDER.to_string(),
                            local_plan: wrap_local(core_placeholder_plan(PLACEHOLDER)),
                            reason,
                        },
                    }
                }
                NodeSplit::Hybrid {
                    pushed,
                    placeholder_var,
                    local_plan,
                    reason,
                } => NodeSplit::Hybrid {
                    pushed,
                    placeholder_var,
                    local_plan: wrap_local(local_plan),
                    reason,
                },
                NodeSplit::LocalOnly { reason } => NodeSplit::LocalOnly { reason },
            }
        }
        Plan::Union { left, right } => {
            let l_split = split_core_node(left, ctx, order_insensitive, false);
            let r_split = split_core_node(right, ctx, order_insensitive, false);
            match (l_split, r_split) {
                (NodeSplit::Pushed(l), NodeSplit::Pushed(r)) => {
                    match PushedNode::apply_union(l, r) {
                        Ok(u) => NodeSplit::Pushed(u),
                        Err(reason) => NodeSplit::LocalOnly { reason },
                    }
                }
                (NodeSplit::Pushed(l), NodeSplit::LocalOnly { .. })
                    if !core_plan_has_source_db(right, ctx, ctx.target_db) =>
                {
                    NodeSplit::Hybrid {
                        pushed: l,
                        placeholder_var: PLACEHOLDER.to_string(),
                        local_plan: Plan::Union {
                            left: Box::new(core_placeholder_plan(PLACEHOLDER)),
                            right: right.clone(),
                        },
                        reason: "cross-source union requires local VM".to_string(),
                    }
                }
                (NodeSplit::LocalOnly { .. }, NodeSplit::Pushed(r))
                    if !core_plan_has_source_db(left, ctx, ctx.target_db) =>
                {
                    NodeSplit::Hybrid {
                        pushed: r,
                        placeholder_var: PLACEHOLDER.to_string(),
                        local_plan: Plan::Union {
                            left: left.clone(),
                            right: Box::new(core_placeholder_plan(PLACEHOLDER)),
                        },
                        reason: "cross-source union requires local VM".to_string(),
                    }
                }
                (NodeSplit::LocalOnly { reason }, _) | (_, NodeSplit::LocalOnly { reason }) => {
                    NodeSplit::LocalOnly { reason }
                }
                _ => NodeSplit::LocalOnly {
                    reason:
                        "union with multiple partial DB branches requires multi-branch execution"
                            .to_string(),
                },
            }
        }
        Plan::Join {
            kind,
            left,
            right,
            on,
            suffixes,
        } => {
            let l_split = split_core_node(left, ctx, order_insensitive, false);
            let r_ord_insens = join_right_is_order_insensitive(*kind, order_insensitive);
            let r_split = split_core_node(right, ctx, r_ord_insens, false);
            match (l_split, r_split) {
                (NodeSplit::Pushed(l), NodeSplit::Pushed(r)) => match PushedNode::apply_join(
                    *kind,
                    l,
                    r,
                    on,
                    suffixes,
                    ctx.dialect,
                    order_insensitive,
                ) {
                    Ok(j) => NodeSplit::Pushed(j),
                    Err(reason) => NodeSplit::LocalOnly { reason },
                },
                (NodeSplit::Pushed(l), NodeSplit::LocalOnly { .. })
                    if !core_plan_has_source_db(right, ctx, ctx.target_db) =>
                {
                    NodeSplit::Hybrid {
                        pushed: l,
                        placeholder_var: PLACEHOLDER.to_string(),
                        local_plan: Plan::Join {
                            kind: *kind,
                            left: Box::new(core_placeholder_plan(PLACEHOLDER)),
                            right: right.clone(),
                            on: on.clone(),
                            suffixes: suffixes.clone(),
                        },
                        reason: "cross-source join requires local VM".to_string(),
                    }
                }
                (
                    NodeSplit::Hybrid {
                        pushed,
                        placeholder_var,
                        local_plan,
                        reason,
                    },
                    NodeSplit::LocalOnly { .. },
                ) if !core_plan_has_source_db(right, ctx, ctx.target_db) => NodeSplit::Hybrid {
                    pushed,
                    placeholder_var,
                    local_plan: Plan::Join {
                        kind: *kind,
                        left: Box::new(local_plan),
                        right: right.clone(),
                        on: on.clone(),
                        suffixes: suffixes.clone(),
                    },
                    reason,
                },
                (NodeSplit::LocalOnly { .. }, NodeSplit::Pushed(r))
                    if !core_plan_has_source_db(left, ctx, ctx.target_db) =>
                {
                    NodeSplit::Hybrid {
                        pushed: r,
                        placeholder_var: PLACEHOLDER.to_string(),
                        local_plan: Plan::Join {
                            kind: *kind,
                            left: left.clone(),
                            right: Box::new(core_placeholder_plan(PLACEHOLDER)),
                            on: on.clone(),
                            suffixes: suffixes.clone(),
                        },
                        reason: "cross-source join requires local VM".to_string(),
                    }
                }
                (
                    NodeSplit::LocalOnly { .. },
                    NodeSplit::Hybrid {
                        pushed,
                        placeholder_var,
                        local_plan,
                        reason,
                    },
                ) if !core_plan_has_source_db(left, ctx, ctx.target_db) => NodeSplit::Hybrid {
                    pushed,
                    placeholder_var,
                    local_plan: Plan::Join {
                        kind: *kind,
                        left: left.clone(),
                        right: Box::new(local_plan),
                        on: on.clone(),
                        suffixes: suffixes.clone(),
                    },
                    reason,
                },
                (NodeSplit::LocalOnly { reason }, _) | (_, NodeSplit::LocalOnly { reason }) => {
                    NodeSplit::LocalOnly { reason }
                }
                _ => NodeSplit::LocalOnly {
                    reason: "join with multiple partial DB branches requires local VM".to_string(),
                },
            }
        }
        // Mandatory local-VM barrier operators
        Plan::SuppressSmallGroups { input, .. } => split_core_local_barrier(
            plan,
            input,
            ctx,
            order_insensitive,
            true,
            "suppress_small_groups requires local VM",
        ),
        Plan::Window { input, .. } => split_core_local_barrier(
            plan,
            input,
            ctx,
            false,
            false,
            "window operator requires local VM",
        ),
        Plan::FillGaps { input, .. } => split_core_local_barrier(
            plan,
            input,
            ctx,
            false,
            false,
            "fill_gaps operator requires local VM",
        ),
        Plan::PivotWider { input, .. } => split_core_local_barrier(
            plan,
            input,
            ctx,
            false,
            false,
            "pivot_wider operator requires local VM",
        ),
        Plan::Crosstab { input, .. } => split_core_local_barrier(
            plan,
            input,
            ctx,
            false,
            false,
            "crosstab operator requires local VM",
        ),
        Plan::Pseudonymize { input, .. } => split_core_local_barrier(
            plan,
            input,
            ctx,
            false,
            false,
            "keyed pseudonymize requires local VM",
        ),
    }
}

fn split_core_local_barrier(
    plan: &Plan,
    input: &Plan,
    ctx: &CoreSplitCtx<'_>,
    child_order_insensitive: bool,
    child_parent_is_suppress: bool,
    barrier_msg: &str,
) -> NodeSplit<Plan> {
    const PLACEHOLDER: &str = "__dana_pushdown_0";
    match split_core_node(
        input,
        ctx,
        child_order_insensitive,
        child_parent_is_suppress,
    ) {
        NodeSplit::Pushed(node) => NodeSplit::Hybrid {
            pushed: node,
            placeholder_var: PLACEHOLDER.to_string(),
            local_plan: rebuild_core_unary(plan, core_placeholder_plan(PLACEHOLDER)),
            reason: barrier_msg.to_string(),
        },
        NodeSplit::Hybrid {
            pushed,
            placeholder_var,
            local_plan,
            reason,
        } => NodeSplit::Hybrid {
            pushed,
            placeholder_var,
            local_plan: rebuild_core_unary(plan, local_plan),
            reason,
        },
        NodeSplit::LocalOnly { reason } => NodeSplit::LocalOnly { reason },
    }
}

fn collect_core_rec(
    plan: &Plan,
    ctx: &CoreSplitCtx<'_>,
    order_insensitive: bool,
    parent_is_suppress: bool,
    next_id: &mut usize,
    branches: &mut Vec<CollectedBranchPushdown>,
    reasons: &mut Vec<String>,
) -> Plan {
    match split_core_node(plan, ctx, order_insensitive, parent_is_suppress) {
        NodeSplit::Pushed(node) => {
            let var = format!("__dana_pushdown_{}", *next_id);
            *next_id += 1;
            branches.push(CollectedBranchPushdown {
                placeholder_var: var.clone(),
                pushdown: node.into_query(ctx.dialect, None),
            });
            core_placeholder_plan(&var)
        }
        NodeSplit::Hybrid {
            pushed,
            placeholder_var,
            local_plan,
            reason,
        } => {
            let var = format!("__dana_pushdown_{}", *next_id);
            *next_id += 1;
            reasons.push(reason.clone());
            branches.push(CollectedBranchPushdown {
                placeholder_var: var.clone(),
                pushdown: pushed.into_query(ctx.dialect, Some(reason)),
            });
            rename_core_placeholder(&local_plan, &placeholder_var, &var)
        }
        NodeSplit::LocalOnly { reason } => match plan {
            Plan::Join {
                kind,
                left,
                right,
                on,
                suffixes,
            } => {
                reasons.push(reason);
                let new_l = collect_core_rec(
                    left,
                    ctx,
                    order_insensitive,
                    false,
                    next_id,
                    branches,
                    reasons,
                );
                let r_ord_insens = join_right_is_order_insensitive(*kind, order_insensitive);
                let new_r =
                    collect_core_rec(right, ctx, r_ord_insens, false, next_id, branches, reasons);
                Plan::Join {
                    kind: *kind,
                    left: Box::new(new_l),
                    right: Box::new(new_r),
                    on: on.clone(),
                    suffixes: suffixes.clone(),
                }
            }
            Plan::Union { left, right } => {
                reasons.push(reason);
                let new_l = collect_core_rec(
                    left,
                    ctx,
                    order_insensitive,
                    false,
                    next_id,
                    branches,
                    reasons,
                );
                let new_r = collect_core_rec(
                    right,
                    ctx,
                    order_insensitive,
                    false,
                    next_id,
                    branches,
                    reasons,
                );
                Plan::Union {
                    left: Box::new(new_l),
                    right: Box::new(new_r),
                }
            }
            Plan::SourceExpr(_) | Plan::SourceDB { .. } => {
                reasons.push(reason);
                plan.clone()
            }
            Plan::SuppressSmallGroups { input, .. } => {
                let new_in = collect_core_rec(
                    input,
                    ctx,
                    order_insensitive,
                    true,
                    next_id,
                    branches,
                    reasons,
                );
                rebuild_core_unary(plan, new_in)
            }
            Plan::Summarize { input, aggs, .. } => {
                let child_ord = !aggs.iter().any(|a| a.op.is_order_sensitive());
                let new_in =
                    collect_core_rec(input, ctx, child_ord, false, next_id, branches, reasons);
                rebuild_core_unary(plan, new_in)
            }
            Plan::Sort { input, keys } => {
                let child_ord = order_insensitive || core_sort_is_total_hint(input, keys, ctx);
                let new_in =
                    collect_core_rec(input, ctx, child_ord, false, next_id, branches, reasons);
                rebuild_core_unary(plan, new_in)
            }
            other => {
                if let Some(child) = core_unary_child(other) {
                    let new_in = collect_core_rec(
                        child,
                        ctx,
                        order_insensitive,
                        false,
                        next_id,
                        branches,
                        reasons,
                    );
                    rebuild_core_unary(other, new_in)
                } else {
                    reasons.push(reason);
                    other.clone()
                }
            }
        },
    }
}

fn core_unary_child(plan: &Plan) -> Option<&Plan> {
    match plan {
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
        | Plan::Pseudonymize { input, .. } => Some(input),
        Plan::SourceExpr(_) | Plan::SourceDB { .. } | Plan::Join { .. } | Plan::Union { .. } => {
            None
        }
    }
}

fn rename_core_placeholder(plan: &Plan, from: &str, to: &str) -> Plan {
    if from == to {
        return plan.clone();
    }
    match plan {
        Plan::SourceExpr(e) => {
            if let Expr::Var(v) = e.as_ref()
                && v == from
            {
                return core_placeholder_plan(to);
            }
            plan.clone()
        }
        Plan::SourceDB { .. } => plan.clone(),
        Plan::Join {
            kind,
            left,
            right,
            on,
            suffixes,
        } => Plan::Join {
            kind: *kind,
            left: Box::new(rename_core_placeholder(left, from, to)),
            right: Box::new(rename_core_placeholder(right, from, to)),
            on: on.clone(),
            suffixes: suffixes.clone(),
        },
        Plan::Union { left, right } => Plan::Union {
            left: Box::new(rename_core_placeholder(left, from, to)),
            right: Box::new(rename_core_placeholder(right, from, to)),
        },
        other => {
            if let Some(child) = core_unary_child(other) {
                rebuild_core_unary(other, rename_core_placeholder(child, from, to))
            } else {
                other.clone()
            }
        }
    }
}

// ===========================================================================
// Phase 2 Execution IR Pushdown Splitter (`runtime::ir::ExecPlan`)
// ===========================================================================

struct ExecSplitCtx<'a> {
    prog: &'a ExecProgram,
    target_db: Option<&'a str>,
    dialect: SqlDialect,
    lock: Option<&'a SchemaLockFile>,
    db_vars: HashMap<Ident, Ident>,
    outer_var_tys: HashMap<Ident, (ScalarTy, TagSet)>,
}

impl<'a> ExecSplitCtx<'a> {
    fn new(
        prog: &'a ExecProgram,
        target_db: Option<&'a str>,
        dialect: SqlDialect,
        lock: Option<&'a SchemaLockFile>,
    ) -> Self {
        let mut db_vars = HashMap::new();
        let mut outer_var_tys = HashMap::new();
        for f in &prog.funs {
            for (name, lty) in &f.params {
                if let Ty::ReadDB(db) = &lty.ty {
                    db_vars.insert(name.clone(), db.clone());
                } else if let Some(sty) = lty.ty.to_scalar_ty() {
                    outer_var_tys.insert(name.clone(), (sty, lty.effective_tags()));
                }
            }
            collect_exec_let_bindings(&f.body, &mut db_vars, &mut outer_var_tys);
        }
        Self {
            prog,
            target_db,
            dialect,
            lock,
            db_vars,
            outer_var_tys,
        }
    }

    fn resolve_source_db(&self, cap: &ExecExpr) -> Option<Ident> {
        match cap {
            ExecExpr::Host {
                op: ExecHostOp::Core(HostOp::FakeDB(db)) | ExecHostOp::FakeDbInMemory { db, .. },
                ..
            } => Some(db.clone()),
            ExecExpr::Var(v) => {
                if let Some(db) = self.db_vars.get(v) {
                    Some(db.clone())
                } else if self.prog.funs.is_empty() {
                    self.target_db
                        .filter(|t| v == t || v == "db")
                        .map(str::to_string)
                        .or_else(|| Some(v.clone()))
                } else if let Some(t) = self.target_db
                    && v == t
                {
                    Some(t.to_string())
                } else {
                    None
                }
            }
            _ => None,
        }
    }
}

fn collect_exec_let_bindings(
    expr: &ExecExpr,
    db_vars: &mut HashMap<Ident, Ident>,
    outer_var_tys: &mut HashMap<Ident, (ScalarTy, TagSet)>,
) {
    let mut stack = vec![expr];
    while let Some(cur) = stack.pop() {
        match cur {
            ExecExpr::LetE {
                name,
                lty,
                bound,
                body,
            } => {
                if let Ty::ReadDB(db) = &lty.ty {
                    db_vars.insert(name.clone(), db.clone());
                } else if let Some(sty) = lty.ty.to_scalar_ty() {
                    outer_var_tys.insert(name.clone(), (sty, lty.effective_tags()));
                }
                stack.push(body);
                stack.push(bound);
            }
            ExecExpr::IfE {
                cond,
                then_br,
                else_br,
            } => {
                stack.push(else_br);
                stack.push(then_br);
                stack.push(cond);
            }
            ExecExpr::CaseE { scrut, arms } => {
                stack.push(scrut);
                for a in arms {
                    stack.push(&a.body);
                }
            }
            ExecExpr::Lam { params, body, .. } => {
                for (name, lty) in params {
                    if let Ty::ReadDB(db) = &lty.ty {
                        db_vars.insert(name.clone(), db.clone());
                    } else if let Some(sty) = lty.ty.to_scalar_ty() {
                        outer_var_tys.insert(name.clone(), (sty, lty.effective_tags()));
                    }
                }
                stack.push(body);
            }
            ExecExpr::Join {
                params, rhs, body, ..
            } => {
                for (name, lty) in params {
                    if let Ty::ReadDB(db) = &lty.ty {
                        db_vars.insert(name.clone(), db.clone());
                    } else if let Some(sty) = lty.ty.to_scalar_ty() {
                        outer_var_tys.insert(name.clone(), (sty, lty.effective_tags()));
                    }
                }
                stack.push(body);
                stack.push(rhs);
            }
            ExecExpr::ForLoop {
                iter_expr,
                body,
                after,
                ..
            } => {
                stack.push(iter_expr);
                stack.push(body);
                stack.push(after);
            }
            ExecExpr::WhileLoop {
                cond, body, after, ..
            } => {
                stack.push(cond);
                stack.push(body);
                stack.push(after);
            }
            ExecExpr::App { fn_expr, args } => {
                stack.push(fn_expr);
                stack.extend(args);
            }
            ExecExpr::Call { args, .. }
            | ExecExpr::Jump { args, .. }
            | ExecExpr::Tuple(args)
            | ExecExpr::Ctor { args, .. }
            | ExecExpr::Prim { args, .. }
            | ExecExpr::Host { args, .. } => stack.extend(args),
            ExecExpr::Proj { tup: e, .. }
            | ExecExpr::Assert { cond: e, .. }
            | ExecExpr::Fail(e) => stack.push(e),
            ExecExpr::Stop {
                detail: Some(d), ..
            } => stack.push(d),
            ExecExpr::Lit(_)
            | ExecExpr::Var(_)
            | ExecExpr::ConstRef(_)
            | ExecExpr::TableLit { .. }
            | ExecExpr::Rel(_)
            | ExecExpr::CheckPromise { .. }
            | ExecExpr::Stop { detail: None, .. } => {}
        }
    }
}

fn exec_plan_has_source_db(
    plan: &ExecPlan,
    ctx: &ExecSplitCtx<'_>,
    filter_db: Option<&str>,
) -> bool {
    let mut stack = vec![plan];
    while let Some(cur) = stack.pop() {
        match cur {
            ExecPlan::SourceDB { cap, .. } => {
                if let Some(target) = filter_db {
                    if ctx.resolve_source_db(cap).as_deref() == Some(target) {
                        return true;
                    }
                } else {
                    return true;
                }
            }
            ExecPlan::SourceExpr(_) => {}
            ExecPlan::Join { left, right, .. } | ExecPlan::Union { left, right } => {
                stack.push(left);
                stack.push(right);
            }
            other => {
                if let Some(child) = exec_unary_child(other) {
                    stack.push(child);
                }
            }
        }
    }
    false
}

fn exec_unary_child(plan: &ExecPlan) -> Option<&ExecPlan> {
    match plan {
        ExecPlan::Select { input, .. }
        | ExecPlan::Drop { input, .. }
        | ExecPlan::Rename { input, .. }
        | ExecPlan::Derive { input, .. }
        | ExecPlan::Filter { input, .. }
        | ExecPlan::Distinct { input, .. }
        | ExecPlan::DedupeBy { input, .. }
        | ExecPlan::Sort { input, .. }
        | ExecPlan::Limit { input, .. }
        | ExecPlan::GroupBy { input, .. }
        | ExecPlan::Summarize { input, .. }
        | ExecPlan::SuppressSmallGroups { input, .. }
        | ExecPlan::Shuffle { input, .. }
        | ExecPlan::SuppressSmallCells { input, .. }
        | ExecPlan::Window { input, .. }
        | ExecPlan::FillGaps { input, .. }
        | ExecPlan::PivotWider { input, .. }
        | ExecPlan::PivotLonger { input, .. }
        | ExecPlan::Crosstab { input, .. }
        | ExecPlan::Redact { input, .. }
        | ExecPlan::Pseudonymize { input, .. } => Some(input),
        ExecPlan::SourceExpr(_)
        | ExecPlan::SourceDB { .. }
        | ExecPlan::Join { .. }
        | ExecPlan::Union { .. } => None,
    }
}

fn exec_placeholder_plan(var: &str) -> ExecPlan {
    ExecPlan::SourceExpr(Box::new(ExecExpr::Var(var.to_string())))
}

fn rebuild_exec_unary(stage: &ExecPlan, new_input: ExecPlan) -> ExecPlan {
    match stage {
        ExecPlan::Select { cols, .. } => ExecPlan::Select {
            input: Box::new(new_input),
            cols: cols.clone(),
        },
        ExecPlan::Drop { cols, .. } => ExecPlan::Drop {
            input: Box::new(new_input),
            cols: cols.clone(),
        },
        ExecPlan::Rename { pairs, .. } => ExecPlan::Rename {
            input: Box::new(new_input),
            pairs: pairs.clone(),
        },
        ExecPlan::Derive { items, .. } => ExecPlan::Derive {
            input: Box::new(new_input),
            items: items.clone(),
        },
        ExecPlan::Filter { pred, .. } => ExecPlan::Filter {
            input: Box::new(new_input),
            pred: pred.clone(),
        },
        ExecPlan::Distinct { cols, .. } => ExecPlan::Distinct {
            input: Box::new(new_input),
            cols: cols.clone(),
        },
        ExecPlan::DedupeBy {
            keys,
            order_by,
            keep,
            ..
        } => ExecPlan::DedupeBy {
            input: Box::new(new_input),
            keys: keys.clone(),
            order_by: order_by.clone(),
            keep: *keep,
        },
        ExecPlan::Sort { keys, .. } => ExecPlan::Sort {
            input: Box::new(new_input),
            keys: keys.clone(),
        },
        ExecPlan::Limit { n, .. } => ExecPlan::Limit {
            input: Box::new(new_input),
            n: n.clone(),
        },
        ExecPlan::GroupBy { keys, .. } => ExecPlan::GroupBy {
            input: Box::new(new_input),
            keys: keys.clone(),
        },
        ExecPlan::Summarize {
            aggs, distinct_key, ..
        } => ExecPlan::Summarize {
            input: Box::new(new_input),
            aggs: aggs.clone(),
            distinct_key: distinct_key.clone(),
        },
        ExecPlan::SuppressSmallGroups {
            min_k,
            distinct_by,
            mode,
            ..
        } => ExecPlan::SuppressSmallGroups {
            input: Box::new(new_input),
            min_k: min_k.clone(),
            distinct_by: distinct_by.clone(),
            mode: *mode,
        },
        ExecPlan::Shuffle { seed, .. } => ExecPlan::Shuffle {
            input: Box::new(new_input),
            seed: seed.clone(),
        },
        ExecPlan::SuppressSmallCells {
            by_cols,
            min_k,
            distinct_by,
            ..
        } => ExecPlan::SuppressSmallCells {
            input: Box::new(new_input),
            by_cols: by_cols.clone(),
            min_k: min_k.clone(),
            distinct_by: distinct_by.clone(),
        },
        ExecPlan::Window { items, .. } => ExecPlan::Window {
            input: Box::new(new_input),
            items: items.clone(),
        },
        ExecPlan::FillGaps {
            col,
            step_micros,
            over,
            fill,
            ..
        } => ExecPlan::FillGaps {
            input: Box::new(new_input),
            col: col.clone(),
            step_micros: step_micros.clone(),
            over: over.clone(),
            fill: fill.clone(),
        },
        ExecPlan::PivotWider {
            names_from,
            values_from,
            static_cols,
            fill,
            ..
        } => ExecPlan::PivotWider {
            input: Box::new(new_input),
            names_from: names_from.clone(),
            values_from: values_from.clone(),
            static_cols: static_cols.clone(),
            fill: fill.clone(),
        },
        ExecPlan::PivotLonger {
            cols,
            names_to,
            values_to,
            value_ty,
            value_tags,
            ..
        } => ExecPlan::PivotLonger {
            input: Box::new(new_input),
            cols: cols.clone(),
            names_to: names_to.clone(),
            values_to: values_to.clone(),
            value_ty: value_ty.clone(),
            value_tags: value_tags.clone(),
        },
        ExecPlan::Crosstab {
            rows_col,
            cols_col,
            values_col,
            fill,
            ..
        } => ExecPlan::Crosstab {
            input: Box::new(new_input),
            rows_col: rows_col.clone(),
            cols_col: cols_col.clone(),
            values_col: values_col.clone(),
            fill: fill.clone(),
        },
        ExecPlan::Redact {
            col, replacement, ..
        } => ExecPlan::Redact {
            input: Box::new(new_input),
            col: col.clone(),
            replacement: replacement.clone(),
        },
        ExecPlan::Pseudonymize { col, secret, .. } => ExecPlan::Pseudonymize {
            input: Box::new(new_input),
            col: col.clone(),
            secret: secret.clone(),
        },
        other => other.clone(),
    }
}

fn translate_exec_row_expr(
    re: &ExecRowExpr,
    schema: &TableTy,
    ctx: &ExecSplitCtx<'_>,
) -> Result<(SqlExpr, ScalarTy, TagSet), String> {
    match re {
        ExecRowExpr::Lit(lit) => {
            let (param, sty, pg_cast) = literal_to_sql_param(lit, ctx.dialect)?;
            Ok((
                SqlExpr::Param {
                    slot: SqlParamSlot::Literal(param),
                    pg_cast,
                },
                sty,
                TagSet::empty(),
            ))
        }
        ExecRowExpr::Col(name) => {
            let Some(col) = schema.find_col(name) else {
                return Err(format!("missing column `{name}` in ExecRowExpr"));
            };
            Ok((
                SqlExpr::Col {
                    table_alias: None,
                    name: name.clone(),
                },
                col.ty.clone(),
                col.tags.clone(),
            ))
        }
        ExecRowExpr::OuterVar(name) => {
            let Some((sty, tags)) = ctx.outer_var_tys.get(name) else {
                return Err(format!(
                    "outer variable `{name}` scalar type unavailable for SQL pushdown"
                ));
            };
            if !is_sql_column_supported(sty) {
                return Err(format!(
                    "outer variable `{name}` has non-SQL type `{sty:?}`"
                ));
            }
            Ok((
                SqlExpr::Param {
                    slot: SqlParamSlot::OuterVar(name.clone()),
                    pg_cast: pg_sql_type_name(sty),
                },
                sty.clone(),
                tags.clone(),
            ))
        }
        ExecRowExpr::ConstRef(name) => {
            let Some(c_decl) = ctx.prog.find_const(name) else {
                return Err(format!("unknown constant `{name}` in ExecRowExpr"));
            };
            let Some(sty) = c_decl.lty.ty.to_scalar_ty() else {
                return Err(format!("non-scalar constant `{name}` requires local VM"));
            };
            let _ = literal_to_sql_param(&c_decl.value, ctx.dialect)?;
            Ok((
                SqlExpr::Param {
                    slot: SqlParamSlot::ConstRef(name.clone()),
                    pg_cast: pg_sql_type_name(&sty),
                },
                sty,
                c_decl.lty.effective_tags(),
            ))
        }
        ExecRowExpr::CallPure { fn_name, .. } => Err(format!(
            "pure UDF call `{fn_name}` requires local bytecode VM"
        )),
        ExecRowExpr::IfE {
            cond,
            then_br,
            else_br,
        } => {
            let (c_e, c_ty, c_tags) = translate_exec_row_expr(cond, schema, ctx)?;
            if c_ty != ScalarTy::Bool {
                return Err("IfE condition must be Bool".to_string());
            }
            let (t_e, t_ty, t_tags) = translate_exec_row_expr(then_br, schema, ctx)?;
            let (e_e, e_ty, e_tags) = translate_exec_row_expr(else_br, schema, ctx)?;
            if t_ty != e_ty {
                return Err("IfE branch type mismatch".to_string());
            }
            Ok((
                SqlExpr::Case {
                    whens: vec![(c_e, t_e)],
                    else_br: Box::new(e_e),
                },
                t_ty,
                c_tags.union(&t_tags).union(&e_tags),
            ))
        }
        ExecRowExpr::Coalesce {
            opt_expr,
            default_expr,
        } => {
            let (o_e, o_ty, o_tags) = translate_exec_row_expr(opt_expr, schema, ctx)?;
            let (d_e, d_ty, d_tags) = translate_exec_row_expr(default_expr, schema, ctx)?;
            match &o_ty {
                ScalarTy::Option(inner) if **inner == d_ty => Ok((
                    SqlExpr::Coalesce(Box::new(o_e), Box::new(d_e)),
                    d_ty,
                    o_tags.union(&d_tags),
                )),
                _ => Err("Coalesce type mismatch".to_string()),
            }
        }
        ExecRowExpr::Prim { op, args } => match (op, args.as_slice()) {
            (ExecPrimOp::Core(core_op), _) => {
                let mut translated = Vec::with_capacity(args.len());
                for a in args {
                    translated.push(translate_exec_row_expr(a, schema, ctx)?);
                }
                translate_core_prim_sql(core_op, translated, ctx.dialect)
            }
            (ExecPrimOp::LowerText, [arg]) => {
                let (e, ty, tags) = translate_exec_row_expr(arg, schema, ctx)?;
                if ty != ScalarTy::Text {
                    return Err("LowerText expects Text".to_string());
                }
                Ok((
                    SqlExpr::Func {
                        name: "LOWER",
                        args: vec![e],
                    },
                    ScalarTy::Text,
                    tags,
                ))
            }
            (ExecPrimOp::UpperText, [arg]) => {
                let (e, ty, tags) = translate_exec_row_expr(arg, schema, ctx)?;
                if ty != ScalarTy::Text {
                    return Err("UpperText expects Text".to_string());
                }
                Ok((
                    SqlExpr::Func {
                        name: "UPPER",
                        args: vec![e],
                    },
                    ScalarTy::Text,
                    tags,
                ))
            }
            (ExecPrimOp::SliceText, [s_re, start_re, len_re]) => {
                let (s_e, s_ty, s_tags) = translate_exec_row_expr(s_re, schema, ctx)?;
                if s_ty != ScalarTy::Text {
                    return Err("SliceText expects Text".to_string());
                }
                let Some(start) = extract_static_int_literal(start_re, ctx.prog) else {
                    return Err("slice with dynamic start requires local VM".to_string());
                };
                let Some(len) = extract_static_int_literal(len_re, ctx.prog) else {
                    return Err("slice with dynamic len requires local VM".to_string());
                };
                if start < 0 || len < 0 {
                    return Err("slice with negative start or len requires local VM".to_string());
                }
                let Some(start_plus_1) = start.checked_add(1) else {
                    return Err("slice start overflow requires local VM".to_string());
                };
                if ctx.dialect == SqlDialect::Postgres
                    && (i32::try_from(start_plus_1).is_err() || i32::try_from(len).is_err())
                {
                    return Err("slice bounds outside 32-bit INTEGER require local VM".to_string());
                }
                Ok((
                    SqlExpr::Substring {
                        str_expr: Box::new(s_e),
                        start: Box::new(SqlExpr::Param {
                            slot: SqlParamSlot::Literal(SqlParam::Int(start_plus_1)),
                            pg_cast: Some("INTEGER"),
                        }),
                        len: Box::new(SqlExpr::Param {
                            slot: SqlParamSlot::Literal(SqlParam::Int(len)),
                            pg_cast: Some("INTEGER"),
                        }),
                    },
                    ScalarTy::Text,
                    s_tags,
                ))
            }
            (ExecPrimOp::StartsWithText, [s_re, pfx_re]) => {
                let (s_e, s_ty, s_tags) = translate_exec_row_expr(s_re, schema, ctx)?;
                let (p_e, p_ty, p_tags) = translate_exec_row_expr(pfx_re, schema, ctx)?;
                if s_ty != ScalarTy::Text || p_ty != ScalarTy::Text {
                    return Err("StartsWithText expects (Text, Text)".to_string());
                }
                let sub = SqlExpr::Substring {
                    str_expr: Box::new(s_e),
                    start: Box::new(SqlExpr::Param {
                        slot: SqlParamSlot::Literal(SqlParam::Int(1)),
                        pg_cast: Some("INTEGER"),
                    }),
                    len: Box::new(SqlExpr::Func {
                        name: "LENGTH",
                        args: vec![p_e.clone()],
                    }),
                };
                Ok((
                    SqlExpr::Binary {
                        op: "=",
                        left: Box::new(sub),
                        right: Box::new(p_e),
                    },
                    ScalarTy::Bool,
                    s_tags.union(&p_tags),
                ))
            }
            (ExecPrimOp::EndsWithText, [s_re, sfx_re]) => {
                let (s_e, s_ty, s_tags) = translate_exec_row_expr(s_re, schema, ctx)?;
                let (sfx_e, sfx_ty, sfx_tags) = translate_exec_row_expr(sfx_re, schema, ctx)?;
                if s_ty != ScalarTy::Text || sfx_ty != ScalarTy::Text {
                    return Err("EndsWithText expects (Text, Text)".to_string());
                }
                let len_s = SqlExpr::Func {
                    name: "LENGTH",
                    args: vec![s_e.clone()],
                };
                let len_sfx = SqlExpr::Func {
                    name: "LENGTH",
                    args: vec![sfx_e.clone()],
                };
                let zero = SqlExpr::Param {
                    slot: SqlParamSlot::Literal(SqlParam::Int(0)),
                    pg_cast: Some("INTEGER"),
                };
                let one = SqlExpr::Param {
                    slot: SqlParamSlot::Literal(SqlParam::Int(1)),
                    pg_cast: Some("INTEGER"),
                };
                let is_empty_sfx = SqlExpr::Binary {
                    op: "=",
                    left: Box::new(len_sfx.clone()),
                    right: Box::new(zero),
                };
                let too_short = SqlExpr::Binary {
                    op: "<",
                    left: Box::new(len_s.clone()),
                    right: Box::new(len_sfx.clone()),
                };
                let start_idx = SqlExpr::Binary {
                    op: "+",
                    left: Box::new(SqlExpr::Binary {
                        op: "-",
                        left: Box::new(len_s),
                        right: Box::new(len_sfx.clone()),
                    }),
                    right: Box::new(one),
                };
                let tail_match = SqlExpr::Binary {
                    op: "=",
                    left: Box::new(SqlExpr::Substring {
                        str_expr: Box::new(s_e),
                        start: Box::new(start_idx),
                        len: Box::new(len_sfx),
                    }),
                    right: Box::new(sfx_e),
                };
                Ok((
                    SqlExpr::Case {
                        whens: vec![
                            (is_empty_sfx, SqlExpr::BoolLit(true)),
                            (too_short, SqlExpr::BoolLit(false)),
                        ],
                        else_br: Box::new(tail_match),
                    },
                    ScalarTy::Bool,
                    s_tags.union(&sfx_tags),
                ))
            }
            (ExecPrimOp::InList, [val_re, list_re]) => {
                let (val_e, val_ty, val_tags) = translate_exec_row_expr(val_re, schema, ctx)?;
                let base_ty = base_of_scalar(&val_ty);
                if !is_dialect_exact_eq(ctx.dialect, base_ty) {
                    return Err(non_exact_type_reason(ctx.dialect, base_ty, "in?"));
                }
                let ExecRowExpr::Prim {
                    op: ExecPrimOp::Core(PrimOp::ListLit(_)),
                    args: elems,
                } = list_re
                else {
                    return Err("in? with dynamic/non-literal list requires local VM".to_string());
                };
                if elems.is_empty() {
                    return Ok((SqlExpr::BoolLit(false), ScalarTy::Bool, val_tags));
                }
                let mut item_exprs = Vec::with_capacity(elems.len());
                let mut all_tags = val_tags;
                for elem in elems {
                    let Some((lit, elem_tags)) = extract_static_scalar_lit(elem, ctx.prog) else {
                        return Err(
                            "in? list contains non-literal element; requires local VM".to_string()
                        );
                    };
                    let (param, elem_ty, pg_cast) = literal_to_sql_param(&lit, ctx.dialect)?;
                    if elem_ty != *base_ty {
                        return Err("in? list element type mismatch with receiver".to_string());
                    }
                    all_tags = all_tags.union(&elem_tags);
                    item_exprs.push(SqlExpr::Param {
                        slot: SqlParamSlot::Literal(param),
                        pg_cast,
                    });
                }
                let in_expr = SqlExpr::InList {
                    expr: Box::new(val_e),
                    items: item_exprs,
                };
                let final_expr = if val_ty.is_option() {
                    SqlExpr::Coalesce(Box::new(in_expr), Box::new(SqlExpr::BoolLit(false)))
                } else {
                    in_expr
                };
                Ok((final_expr, ScalarTy::Bool, all_tags))
            }
            (ExecPrimOp::ClampInt, [x_re, lo_re, hi_re]) => {
                let (x_e, x_ty, x_tags) = translate_exec_row_expr(x_re, schema, ctx)?;
                if x_ty != ScalarTy::Int {
                    return Err("ClampInt expects Int".to_string());
                }
                let (Some(lo), Some(hi)) = (
                    extract_static_int_literal(lo_re, ctx.prog),
                    extract_static_int_literal(hi_re, ctx.prog),
                ) else {
                    return Err("clamp with dynamic bounds requires local VM".to_string());
                };
                if lo > hi {
                    return Err("invalid clamp bounds (lo > hi) require local VM trap".to_string());
                }
                let lo_param = || SqlExpr::Param {
                    slot: SqlParamSlot::Literal(SqlParam::Int(lo)),
                    pg_cast: Some("BIGINT"),
                };
                let hi_param = || SqlExpr::Param {
                    slot: SqlParamSlot::Literal(SqlParam::Int(hi)),
                    pg_cast: Some("BIGINT"),
                };
                let lt_lo = SqlExpr::Binary {
                    op: "<",
                    left: Box::new(x_e.clone()),
                    right: Box::new(lo_param()),
                };
                let gt_hi = SqlExpr::Binary {
                    op: ">",
                    left: Box::new(x_e.clone()),
                    right: Box::new(hi_param()),
                };
                Ok((
                    SqlExpr::Case {
                        whens: vec![(lt_lo, lo_param()), (gt_hi, hi_param())],
                        else_br: Box::new(x_e),
                    },
                    ScalarTy::Int,
                    x_tags,
                ))
            }
            (ExecPrimOp::ClampDecimal, [x_re, lo_re, hi_re]) => {
                if ctx.dialect != SqlDialect::Postgres {
                    return Err("SQLite Decimal clamp requires local VM".to_string());
                }
                let (x_e, x_ty, x_tags) = translate_exec_row_expr(x_re, schema, ctx)?;
                if x_ty != ScalarTy::Decimal {
                    return Err("ClampDecimal expects Decimal".to_string());
                }
                let (Some((Literal::Decimal(lo), _)), Some((Literal::Decimal(hi), _))) = (
                    extract_static_scalar_lit(lo_re, ctx.prog),
                    extract_static_scalar_lit(hi_re, ctx.prog),
                ) else {
                    return Err("Decimal clamp with dynamic bounds requires local VM".to_string());
                };
                if !lo.in_decimal_range() || !hi.in_decimal_range() || lo > hi {
                    return Err("invalid Decimal clamp bounds require local VM trap".to_string());
                }
                let lo_param = || SqlExpr::Param {
                    slot: SqlParamSlot::Literal(SqlParam::Decimal(lo.clone())),
                    pg_cast: Some("NUMERIC"),
                };
                let hi_param = || SqlExpr::Param {
                    slot: SqlParamSlot::Literal(SqlParam::Decimal(hi.clone())),
                    pg_cast: Some("NUMERIC"),
                };
                let lt_lo = SqlExpr::Binary {
                    op: "<",
                    left: Box::new(x_e.clone()),
                    right: Box::new(lo_param()),
                };
                let gt_hi = SqlExpr::Binary {
                    op: ">",
                    left: Box::new(x_e.clone()),
                    right: Box::new(hi_param()),
                };
                Ok((
                    SqlExpr::Case {
                        whens: vec![(lt_lo, lo_param()), (gt_hi, hi_param())],
                        else_br: Box::new(x_e),
                    },
                    ScalarTy::Decimal,
                    x_tags,
                ))
            }
            (ExecPrimOp::TryParseDate, [s_re]) => {
                let (s_e, s_ty, s_tags) = translate_exec_row_expr(s_re, schema, ctx)?;
                if s_ty != ScalarTy::Text {
                    return Err("try_parse_date requires non-Option Text".to_string());
                }
                Ok((
                    SqlExpr::TryParseIsoDate {
                        inner: Box::new(s_e),
                        already_trimmed: false,
                    },
                    ScalarTy::Option(Box::new(ScalarTy::Date)),
                    s_tags,
                ))
            }
            (ExecPrimOp::AddDays, [d_re, n_re]) => {
                if ctx.dialect != SqlDialect::Postgres {
                    return Err("SQLite Date add_days requires local VM".to_string());
                }
                let (d_e, d_ty, d_tags) = translate_exec_row_expr(d_re, schema, ctx)?;
                if d_ty != ScalarTy::Date {
                    return Err("AddDays expects (Date, Int)".to_string());
                }
                let Some(n) = extract_static_int_literal(n_re, ctx.prog) else {
                    return Err("add_days with dynamic day count requires local VM".to_string());
                };
                if !(-365_000..=365_000).contains(&n) {
                    return Err("add_days out of pushed day range requires local VM".to_string());
                }
                Ok((
                    SqlExpr::Binary {
                        op: "+",
                        left: Box::new(d_e),
                        right: Box::new(SqlExpr::Param {
                            slot: SqlParamSlot::Literal(SqlParam::Int(n)),
                            pg_cast: Some("INTEGER"),
                        }),
                    },
                    ScalarTy::Date,
                    d_tags,
                ))
            }
            (ExecPrimOp::DaysBetween, [d1_re, d2_re]) => {
                if ctx.dialect != SqlDialect::Postgres {
                    return Err("SQLite days_between requires local VM".to_string());
                }
                let (d1_e, d1_ty, d1_tags) = translate_exec_row_expr(d1_re, schema, ctx)?;
                let (d2_e, d2_ty, d2_tags) = translate_exec_row_expr(d2_re, schema, ctx)?;
                if d1_ty != ScalarTy::Date || d2_ty != ScalarTy::Date {
                    return Err("DaysBetween expects (Date, Date)".to_string());
                }
                Ok((
                    SqlExpr::Cast {
                        expr: Box::new(SqlExpr::Binary {
                            op: "-",
                            left: Box::new(d2_e),
                            right: Box::new(d1_e),
                        }),
                        ty: "BIGINT",
                    },
                    ScalarTy::Int,
                    d1_tags.union(&d2_tags),
                ))
            }
            (ExecPrimOp::DateYear, [d_re]) => {
                if ctx.dialect != SqlDialect::Postgres {
                    return Err("SQLite Date.year requires local VM".to_string());
                }
                let (d_e, d_ty, d_tags) = translate_exec_row_expr(d_re, schema, ctx)?;
                if d_ty != ScalarTy::Date {
                    return Err("DateYear expects Date".to_string());
                }
                Ok((SqlExpr::ExtractYear(Box::new(d_e)), ScalarTy::Int, d_tags))
            }
            (ExecPrimOp::AtMidnightInTz, [d_re, tz_re]) => {
                if ctx.dialect != SqlDialect::Postgres {
                    return Err("SQLite at_midnight_in_tz requires local VM".to_string());
                }
                let (d_e, d_ty, d_tags) = translate_exec_row_expr(d_re, schema, ctx)?;
                if d_ty != ScalarTy::Date {
                    return Err("AtMidnightInTz expects (Date, Text)".to_string());
                }
                let Some((Literal::Text(tz), tz_tags)) = extract_static_scalar_lit(tz_re, ctx.prog)
                else {
                    return Err(
                        "at_midnight_in_tz with dynamic timezone requires local VM".to_string()
                    );
                };
                if crate::formats::time::load_timezone(&tz).is_err() {
                    return Err("unknown timezone requires local VM trap".to_string());
                }
                Ok((
                    SqlExpr::AtTimeZone {
                        expr: Box::new(SqlExpr::Cast {
                            expr: Box::new(d_e),
                            ty: "TIMESTAMP",
                        }),
                        tz: Box::new(SqlExpr::Param {
                            slot: SqlParamSlot::Literal(SqlParam::Text(tz)),
                            pg_cast: Some("TEXT"),
                        }),
                    },
                    ScalarTy::Timestamp,
                    d_tags.union(&tz_tags),
                ))
            }
            (
                ExecPrimOp::TryParseInt
                | ExecPrimOp::TryParseDecimal
                | ExecPrimOp::TryParseFloat
                | ExecPrimOp::ClampFloat
                | ExecPrimOp::RoundToFloat
                | ExecPrimOp::RoundToFloatEven
                | ExecPrimOp::RoundFloatEven
                | ExecPrimOp::RoundDecimalEven
                | ExecPrimOp::CeilFloat
                | ExecPrimOp::FloorFloat
                | ExecPrimOp::TruncFloat
                | ExecPrimOp::CeilDecimal
                | ExecPrimOp::FloorDecimal
                | ExecPrimOp::TruncDecimal,
                _,
            ) => Err(format!("op `{op:?}` requires local VM")),
            (other, _) => Err(format!(
                "runtime extension op `{other:?}` requires local VM"
            )),
        },
    }
}

fn extract_static_int_literal(re: &ExecRowExpr, prog: &ExecProgram) -> Option<i64> {
    match re {
        ExecRowExpr::Lit(Literal::Int(n)) => n.to_i64(),
        ExecRowExpr::ConstRef(name) => match prog.find_const(name).map(|c| &c.value) {
            Some(Literal::Int(n)) => n.to_i64(),
            _ => None,
        },
        ExecRowExpr::Prim {
            op: ExecPrimOp::Core(PrimOp::NegInt),
            args,
        } => match args.as_slice() {
            [inner] => extract_static_int_literal(inner, prog).and_then(i64::checked_neg),
            _ => None,
        },
        _ => None,
    }
}

fn extract_static_scalar_lit(re: &ExecRowExpr, prog: &ExecProgram) -> Option<(Literal, TagSet)> {
    match re {
        ExecRowExpr::Lit(lit) => Some((lit.clone(), TagSet::empty())),
        ExecRowExpr::ConstRef(name) => prog
            .find_const(name)
            .map(|c| (c.value.clone(), c.lty.effective_tags())),
        ExecRowExpr::Prim {
            op: ExecPrimOp::Core(PrimOp::NegInt),
            args,
        } => match args.as_slice() {
            [inner] => match extract_static_scalar_lit(inner, prog) {
                Some((Literal::Int(n), tags)) => Some((Literal::Int(-n), tags)),
                _ => None,
            },
            _ => None,
        },
        ExecRowExpr::Prim {
            op: ExecPrimOp::Core(PrimOp::NegDec),
            args,
        } => match args.as_slice() {
            [inner] => match extract_static_scalar_lit(inner, prog) {
                Some((Literal::Decimal(d), tags)) => Some((Literal::Decimal(-d), tags)),
                _ => None,
            },
            _ => None,
        },
        ExecRowExpr::Prim {
            op: ExecPrimOp::NegFloat,
            args,
        } => match args.as_slice() {
            [inner] => match extract_static_scalar_lit(inner, prog) {
                Some((Literal::Float(f), tags)) => {
                    Some((Literal::Float(Float64::from_f64(-f.to_f64())), tags))
                }
                _ => None,
            },
            _ => None,
        },
        _ => None,
    }
}

fn exec_sort_is_total_hint(
    plan: &ExecPlan,
    keys: &[(Ident, SortDir)],
    ctx: &ExecSplitCtx<'_>,
) -> bool {
    if keys.is_empty() {
        return false;
    }
    let key_names: Vec<Ident> = keys.iter().map(|(k, _)| k.clone()).collect();
    if let Some((cols, uqs)) = exec_plan_cols_and_uqs_hint(plan, ctx) {
        if cols.iter().all(|c| key_names.contains(c)) {
            return true;
        }
        if uqs
            .iter()
            .any(|uk| uk.iter().all(|k| key_names.contains(k)))
        {
            return true;
        }
    }
    false
}

fn exec_plan_cols_and_uqs_hint(
    plan: &ExecPlan,
    ctx: &ExecSplitCtx<'_>,
) -> Option<(Vec<Ident>, Vec<Vec<Ident>>)> {
    match plan {
        ExecPlan::SourceDB {
            cap,
            table_name,
            schema,
        } => {
            let cols = schema.col_names();
            let mut uqs = Vec::new();
            if let Some(db) = ctx.resolve_source_db(cap)
                && let Some(pk) = ctx
                    .lock
                    .and_then(|l| l.find_db(&db))
                    .and_then(|d| d.resolve_table(table_name).ok())
                    .map(|t| {
                        t.cols
                            .iter()
                            .filter(|c| c.pk)
                            .map(|c| c.name.clone())
                            .collect::<Vec<_>>()
                    })
                && !pk.is_empty()
                && pk.iter().all(|k| cols.contains(k))
            {
                uqs.push(pk);
            }
            Some((cols, uqs))
        }
        ExecPlan::Select { input, cols } => {
            let (_, mut uqs) = exec_plan_cols_and_uqs_hint(input, ctx)?;
            uqs.retain(|uk| uk.iter().all(|k| cols.contains(k)));
            Some((cols.clone(), uqs))
        }
        ExecPlan::Drop { input, cols } => {
            let (mut c, mut uqs) = exec_plan_cols_and_uqs_hint(input, ctx)?;
            c.retain(|x| !cols.contains(x));
            uqs.retain(|uk| uk.iter().all(|k| c.contains(k)));
            Some((c, uqs))
        }
        ExecPlan::Rename { input, pairs } => {
            let (cols, uqs) = exec_plan_cols_and_uqs_hint(input, ctx)?;
            // ExecPlan::Rename pairs are `(old_name, new_name)`.
            let map_name = |c: Ident| {
                pairs
                    .iter()
                    .find(|(old_n, _)| *old_n == c)
                    .map_or(c, |(_, new_n)| new_n.clone())
            };
            let new_cols = cols.into_iter().map(map_name).collect();
            let new_uqs = uqs
                .into_iter()
                .map(|uk| uk.into_iter().map(map_name).collect())
                .collect();
            Some((new_cols, new_uqs))
        }
        ExecPlan::Derive { input, items } => {
            let (mut cols, mut uqs) = exec_plan_cols_and_uqs_hint(input, ctx)?;
            for it in items {
                let name = it.target_name();
                if cols.contains(name) {
                    uqs.retain(|uk| !uk.contains(name));
                } else {
                    cols.push(name.clone());
                }
            }
            Some((cols, uqs))
        }
        ExecPlan::Filter { input, .. }
        | ExecPlan::Sort { input, .. }
        | ExecPlan::Limit { input, .. }
        | ExecPlan::GroupBy { input, .. }
        | ExecPlan::SuppressSmallGroups { input, .. }
        | ExecPlan::Shuffle { input, .. }
        | ExecPlan::SuppressSmallCells { input, .. } => exec_plan_cols_and_uqs_hint(input, ctx),
        ExecPlan::Distinct { input, cols } => {
            let (in_cols, mut uqs) = exec_plan_cols_and_uqs_hint(input, ctx)?;
            if cols.is_empty() || in_cols.iter().all(|c| cols.contains(c)) {
                uqs.push(in_cols.clone());
            }
            Some((in_cols, uqs))
        }
        ExecPlan::DedupeBy { input, keys, .. } => {
            let (in_cols, mut uqs) = exec_plan_cols_and_uqs_hint(input, ctx)?;
            uqs.push(keys.clone());
            Some((in_cols, uqs))
        }
        ExecPlan::Redact { input, col, .. } | ExecPlan::Pseudonymize { input, col, .. } => {
            let (cols, mut uqs) = exec_plan_cols_and_uqs_hint(input, ctx)?;
            uqs.retain(|uk| !uk.contains(col));
            Some((cols, uqs))
        }
        ExecPlan::Summarize { input, aggs, .. } => {
            let (in_cols, _) = exec_plan_cols_and_uqs_hint(input, ctx)?;
            let gks: Vec<Ident> = match input.as_ref() {
                ExecPlan::GroupBy { keys, .. } => {
                    in_cols.into_iter().filter(|c| keys.contains(c)).collect()
                }
                _ => Vec::new(),
            };
            let mut out_cols = gks.clone();
            out_cols.extend(aggs.iter().map(|a| a.name.clone()));
            Some((out_cols, vec![gks]))
        }
        ExecPlan::Join {
            kind,
            left,
            right,
            on,
            suffixes,
        } => {
            let (l_cols, l_uqs) = exec_plan_cols_and_uqs_hint(left, ctx)?;
            if matches!(kind, JoinKind::Semi | JoinKind::Anti) {
                return Some((l_cols, l_uqs));
            }
            let (r_cols, r_uqs) = exec_plan_cols_and_uqs_hint(right, ctx)?;
            join_cols_and_uqs_hint(*kind, l_cols, l_uqs, &r_cols, &r_uqs, on, suffixes.as_ref())
        }
        ExecPlan::Union { left, .. } => {
            let (cols, _) = exec_plan_cols_and_uqs_hint(left, ctx)?;
            Some((cols, Vec::new()))
        }
        _ => None,
    }
}

fn split_exec_node(
    plan: &ExecPlan,
    ctx: &ExecSplitCtx<'_>,
    order_insensitive: bool,
    suppress_ctx: SuppressPushCtx<'_>,
    parent_has_sort: bool,
) -> NodeSplit<ExecPlan> {
    const PLACEHOLDER: &str = "__dana_pushdown_0";

    match plan {
        ExecPlan::SourceExpr(_) => NodeSplit::LocalOnly {
            reason: "in-memory source expression requires local VM".to_string(),
        },
        ExecPlan::SourceDB {
            cap,
            table_name,
            schema,
        } => {
            let Some(resolved_db) = ctx.resolve_source_db(cap) else {
                return NodeSplit::LocalOnly {
                    reason: format!("unable to resolve database binding for table `{table_name}`"),
                };
            };
            if let Some(target) = ctx.target_db
                && resolved_db != target
            {
                return NodeSplit::LocalOnly {
                    reason: format!(
                        "table `{table_name}` belongs to database `{resolved_db}`, not `{target}`"
                    ),
                };
            }
            match PushedNode::from_source_db(
                &resolved_db,
                table_name,
                schema,
                ctx.lock,
                ctx.dialect,
            ) {
                Ok(node) => NodeSplit::Pushed(node),
                Err(reason) => NodeSplit::LocalOnly { reason },
            }
        }
        ExecPlan::Select { input, cols } => {
            match split_exec_node(
                input,
                ctx,
                order_insensitive,
                SuppressPushCtx::None,
                parent_has_sort,
            ) {
                NodeSplit::Pushed(node) => match node.apply_select(cols) {
                    Ok(next) => NodeSplit::Pushed(next),
                    Err(reason) => NodeSplit::LocalOnly { reason },
                },
                NodeSplit::Hybrid {
                    pushed,
                    placeholder_var,
                    local_plan,
                    reason,
                } => NodeSplit::Hybrid {
                    pushed,
                    placeholder_var,
                    local_plan: rebuild_exec_unary(plan, local_plan),
                    reason,
                },
                NodeSplit::LocalOnly { reason } => NodeSplit::LocalOnly { reason },
            }
        }
        ExecPlan::Drop { input, cols } => {
            match split_exec_node(
                input,
                ctx,
                order_insensitive,
                suppress_ctx.indirect_if_active(),
                parent_has_sort,
            ) {
                NodeSplit::Pushed(node) => match node.apply_drop(cols) {
                    Ok(next) => NodeSplit::Pushed(next),
                    Err(reason) => NodeSplit::LocalOnly { reason },
                },
                NodeSplit::Hybrid {
                    pushed,
                    placeholder_var,
                    local_plan,
                    reason,
                } => NodeSplit::Hybrid {
                    pushed,
                    placeholder_var,
                    local_plan: rebuild_exec_unary(plan, local_plan),
                    reason,
                },
                NodeSplit::LocalOnly { reason } => NodeSplit::LocalOnly { reason },
            }
        }
        ExecPlan::Rename { input, pairs } => {
            match split_exec_node(
                input,
                ctx,
                order_insensitive,
                SuppressPushCtx::None,
                parent_has_sort,
            ) {
                NodeSplit::Pushed(node) => {
                    // Phase 2 `ExecPlan::Rename` stores `(old_name, new_name)` directly.
                    match node.apply_rename(pairs) {
                        Ok(next) => NodeSplit::Pushed(next),
                        Err(reason) => NodeSplit::LocalOnly { reason },
                    }
                }
                NodeSplit::Hybrid {
                    pushed,
                    placeholder_var,
                    local_plan,
                    reason,
                } => NodeSplit::Hybrid {
                    pushed,
                    placeholder_var,
                    local_plan: rebuild_exec_unary(plan, local_plan),
                    reason,
                },
                NodeSplit::LocalOnly { reason } => NodeSplit::LocalOnly { reason },
            }
        }
        ExecPlan::Filter { input, pred } => {
            match split_exec_node(
                input,
                ctx,
                order_insensitive,
                SuppressPushCtx::None,
                parent_has_sort,
            ) {
                NodeSplit::Pushed(node) => match translate_exec_row_expr(pred, &node.schema, ctx) {
                    Ok((sql_e, ScalarTy::Bool, p_tags)) => {
                        NodeSplit::Pushed(node.apply_filter(sql_e, &p_tags))
                    }
                    Ok(_) => NodeSplit::Hybrid {
                        pushed: node,
                        placeholder_var: PLACEHOLDER.to_string(),
                        local_plan: rebuild_exec_unary(plan, exec_placeholder_plan(PLACEHOLDER)),
                        reason: "filter predicate did not type-check as Bool".to_string(),
                    },
                    Err(reason) => NodeSplit::Hybrid {
                        pushed: node,
                        placeholder_var: PLACEHOLDER.to_string(),
                        local_plan: rebuild_exec_unary(plan, exec_placeholder_plan(PLACEHOLDER)),
                        reason,
                    },
                },
                NodeSplit::Hybrid {
                    pushed,
                    placeholder_var,
                    local_plan,
                    reason,
                } => NodeSplit::Hybrid {
                    pushed,
                    placeholder_var,
                    local_plan: rebuild_exec_unary(plan, local_plan),
                    reason,
                },
                NodeSplit::LocalOnly { reason } => NodeSplit::LocalOnly { reason },
            }
        }
        ExecPlan::Derive { input, items } => {
            match split_exec_node(
                input,
                ctx,
                order_insensitive,
                suppress_ctx.indirect_if_active(),
                parent_has_sort,
            ) {
                NodeSplit::Pushed(node) => {
                    let orig = node.clone();
                    let mut cur = node;
                    let mut waves = DeriveWaveState::new(cur.schema.clone(), items.len());
                    let mut names = Vec::with_capacity(items.len());
                    for item in items {
                        match item {
                            ExecDeriveItem::ColExpr { name, expr }
                            | ExecDeriveItem::SummaryCol { name, expr, .. } => {
                                let ak = match item {
                                    ExecDeriveItem::SummaryCol { agg_kind, .. } => *agg_kind,
                                    _ => AggKind::Raw,
                                };
                                match translate_exec_row_expr(expr, &waves.working_schema, ctx) {
                                    Ok((sql_e, sty, tags)) => {
                                        let existing_tags = waves
                                            .working_schema
                                            .find_col(name)
                                            .map(|c| c.tags.clone())
                                            .unwrap_or_default();
                                        let spec = ColSpec {
                                            name: name.clone(),
                                            ty: sty,
                                            tags: existing_tags.union(&tags),
                                            bucketed: false,
                                            agg_kind: ak,
                                        };
                                        cur = waves.push_item(cur, name, sql_e, spec);
                                        names.push(name.clone());
                                    }
                                    Err(reason) => {
                                        return NodeSplit::Hybrid {
                                            pushed: orig,
                                            placeholder_var: PLACEHOLDER.to_string(),
                                            local_plan: rebuild_exec_unary(
                                                plan,
                                                exec_placeholder_plan(PLACEHOLDER),
                                            ),
                                            reason,
                                        };
                                    }
                                }
                            }
                            ExecDeriveItem::BucketCol {
                                name,
                                source,
                                cuts,
                                labels,
                            } => match translate_bucket_col(
                                &waves.working_schema,
                                name,
                                source,
                                cuts,
                                labels,
                                ctx.dialect,
                            ) {
                                Ok((sql_e, spec)) => {
                                    cur = waves.push_item(cur, name, sql_e, spec);
                                    names.push(name.clone());
                                }
                                Err(reason) => {
                                    return NodeSplit::Hybrid {
                                        pushed: orig,
                                        placeholder_var: PLACEHOLDER.to_string(),
                                        local_plan: rebuild_exec_unary(
                                            plan,
                                            exec_placeholder_plan(PLACEHOLDER),
                                        ),
                                        reason,
                                    };
                                }
                            },
                            ExecDeriveItem::CoarsenCol {
                                name,
                                source,
                                allow,
                                other,
                            } => match translate_coarsen_col(
                                &waves.working_schema,
                                name,
                                source,
                                allow,
                                other,
                                ctx.dialect,
                            ) {
                                Ok((sql_e, spec)) => {
                                    cur = waves.push_item(cur, name, sql_e, spec);
                                    names.push(name.clone());
                                }
                                Err(reason) => {
                                    return NodeSplit::Hybrid {
                                        pushed: orig,
                                        placeholder_var: PLACEHOLDER.to_string(),
                                        local_plan: rebuild_exec_unary(
                                            plan,
                                            exec_placeholder_plan(PLACEHOLDER),
                                        ),
                                        reason,
                                    };
                                }
                            },
                        }
                    }
                    cur = waves.finish(cur);
                    cur.pushed_ops
                        .push(format!("Derive([{}])", names.join(", ")));
                    NodeSplit::Pushed(cur)
                }
                NodeSplit::Hybrid {
                    pushed,
                    placeholder_var,
                    local_plan,
                    reason,
                } => NodeSplit::Hybrid {
                    pushed,
                    placeholder_var,
                    local_plan: rebuild_exec_unary(plan, local_plan),
                    reason,
                },
                NodeSplit::LocalOnly { reason } => NodeSplit::LocalOnly { reason },
            }
        }
        ExecPlan::Redact {
            input,
            col,
            replacement,
        } => match split_exec_node(
            input,
            ctx,
            order_insensitive,
            SuppressPushCtx::None,
            parent_has_sort,
        ) {
            NodeSplit::Pushed(node) => {
                let orig = node.clone();
                match node.apply_redact(col, replacement) {
                    Ok(next) => NodeSplit::Pushed(next),
                    Err(reason) => NodeSplit::Hybrid {
                        pushed: orig,
                        placeholder_var: PLACEHOLDER.to_string(),
                        local_plan: rebuild_exec_unary(plan, exec_placeholder_plan(PLACEHOLDER)),
                        reason,
                    },
                }
            }
            NodeSplit::Hybrid {
                pushed,
                placeholder_var,
                local_plan,
                reason,
            } => NodeSplit::Hybrid {
                pushed,
                placeholder_var,
                local_plan: rebuild_exec_unary(plan, local_plan),
                reason,
            },
            NodeSplit::LocalOnly { reason } => NodeSplit::LocalOnly { reason },
        },
        ExecPlan::Sort { input, keys } => {
            let child_ord_insens = order_insensitive || exec_sort_is_total_hint(input, keys, ctx);
            match split_exec_node(input, ctx, child_ord_insens, SuppressPushCtx::None, true) {
                NodeSplit::Pushed(node) => {
                    let orig = node.clone();
                    match node.apply_sort(keys, ctx.dialect) {
                        Ok(next) => NodeSplit::Pushed(next),
                        Err(reason) => NodeSplit::Hybrid {
                            pushed: orig,
                            placeholder_var: PLACEHOLDER.to_string(),
                            local_plan: rebuild_exec_unary(
                                plan,
                                exec_placeholder_plan(PLACEHOLDER),
                            ),
                            reason,
                        },
                    }
                }
                NodeSplit::Hybrid {
                    pushed,
                    placeholder_var,
                    local_plan,
                    reason,
                } => NodeSplit::Hybrid {
                    pushed,
                    placeholder_var,
                    local_plan: rebuild_exec_unary(plan, local_plan),
                    reason,
                },
                NodeSplit::LocalOnly { reason } => NodeSplit::LocalOnly { reason },
            }
        }
        ExecPlan::Limit { input, n } => {
            match split_exec_node(input, ctx, false, SuppressPushCtx::None, false) {
                NodeSplit::Pushed(node) => {
                    let orig = node.clone();
                    match node.apply_limit(n) {
                        Ok(next) => NodeSplit::Pushed(next),
                        Err(reason) => NodeSplit::Hybrid {
                            pushed: orig,
                            placeholder_var: PLACEHOLDER.to_string(),
                            local_plan: rebuild_exec_unary(
                                plan,
                                exec_placeholder_plan(PLACEHOLDER),
                            ),
                            reason,
                        },
                    }
                }
                NodeSplit::Hybrid {
                    pushed,
                    placeholder_var,
                    local_plan,
                    reason,
                } => NodeSplit::Hybrid {
                    pushed,
                    placeholder_var,
                    local_plan: rebuild_exec_unary(plan, local_plan),
                    reason,
                },
                NodeSplit::LocalOnly { reason } => NodeSplit::LocalOnly { reason },
            }
        }
        ExecPlan::DedupeBy {
            input,
            keys,
            order_by,
            keep,
        } => {
            let mut combined = keys.clone();
            for (c, _) in order_by {
                if !combined.contains(c) {
                    combined.push(c.clone());
                }
            }
            let unique_tie =
                exec_plan_cols_and_uqs_hint(input, ctx).is_some_and(|(in_cols, uqs)| {
                    in_cols.iter().all(|c| combined.contains(c))
                        || uqs.iter().any(|uk| uk.iter().all(|k| combined.contains(k)))
                });
            let child_ord_insens = order_insensitive && unique_tie;
            match split_exec_node(
                input,
                ctx,
                child_ord_insens,
                SuppressPushCtx::None,
                parent_has_sort,
            ) {
                NodeSplit::Pushed(node) => {
                    let orig = node.clone();
                    match node.apply_dedupe_by(
                        keys,
                        order_by,
                        *keep,
                        ctx.dialect,
                        order_insensitive,
                    ) {
                        Ok(next) => NodeSplit::Pushed(next),
                        Err(reason) => NodeSplit::Hybrid {
                            pushed: orig,
                            placeholder_var: PLACEHOLDER.to_string(),
                            local_plan: rebuild_exec_unary(
                                plan,
                                exec_placeholder_plan(PLACEHOLDER),
                            ),
                            reason,
                        },
                    }
                }
                NodeSplit::Hybrid {
                    pushed,
                    placeholder_var,
                    local_plan,
                    reason,
                } => NodeSplit::Hybrid {
                    pushed,
                    placeholder_var,
                    local_plan: rebuild_exec_unary(plan, local_plan),
                    reason,
                },
                NodeSplit::LocalOnly { reason } => NodeSplit::LocalOnly { reason },
            }
        }
        ExecPlan::Distinct { input, cols } => {
            let covers_all_hint = cols.is_empty()
                || exec_plan_cols_and_uqs_hint(input, ctx)
                    .is_some_and(|(in_cols, _)| in_cols.iter().all(|c| cols.contains(c)));
            let child_ord_insens = order_insensitive && covers_all_hint;
            match split_exec_node(
                input,
                ctx,
                child_ord_insens,
                SuppressPushCtx::None,
                parent_has_sort,
            ) {
                NodeSplit::Pushed(node) => {
                    let orig = node.clone();
                    match node.apply_distinct(cols, ctx.dialect, order_insensitive) {
                        Ok(next) => NodeSplit::Pushed(next),
                        Err(reason) => NodeSplit::Hybrid {
                            pushed: orig,
                            placeholder_var: PLACEHOLDER.to_string(),
                            local_plan: rebuild_exec_unary(
                                plan,
                                exec_placeholder_plan(PLACEHOLDER),
                            ),
                            reason,
                        },
                    }
                }
                NodeSplit::Hybrid {
                    pushed,
                    placeholder_var,
                    local_plan,
                    reason,
                } => NodeSplit::Hybrid {
                    pushed,
                    placeholder_var,
                    local_plan: rebuild_exec_unary(plan, local_plan),
                    reason,
                },
                NodeSplit::LocalOnly { reason } => NodeSplit::LocalOnly { reason },
            }
        }
        ExecPlan::GroupBy { input, .. } => {
            match split_exec_node(
                input,
                ctx,
                order_insensitive,
                SuppressPushCtx::None,
                parent_has_sort,
            ) {
                NodeSplit::Pushed(node) => NodeSplit::Hybrid {
                    pushed: node,
                    placeholder_var: PLACEHOLDER.to_string(),
                    local_plan: rebuild_exec_unary(plan, exec_placeholder_plan(PLACEHOLDER)),
                    reason: "unpaired group_by stays local for downstream summarize".to_string(),
                },
                NodeSplit::Hybrid {
                    pushed,
                    placeholder_var,
                    local_plan,
                    reason,
                } => NodeSplit::Hybrid {
                    pushed,
                    placeholder_var,
                    local_plan: rebuild_exec_unary(plan, local_plan),
                    reason,
                },
                NodeSplit::LocalOnly { reason } => NodeSplit::LocalOnly { reason },
            }
        }
        ExecPlan::Summarize {
            input,
            aggs,
            distinct_key,
        } => {
            let (raw_inner, group_keys, has_gb) = match input.as_ref() {
                ExecPlan::GroupBy { input: gb_in, keys } => (gb_in.as_ref(), keys.as_slice(), true),
                other => (other, &[][..], false),
            };
            let aggs_order_free = !aggs.iter().any(|a| a.op.is_order_sensitive());
            let child_ord_insens =
                aggs_order_free && (order_insensitive || group_keys.is_empty() || parent_has_sort);
            let wrap_local = |inner_local: ExecPlan| {
                let mid = if has_gb {
                    ExecPlan::GroupBy {
                        input: Box::new(inner_local),
                        keys: group_keys.to_vec(),
                    }
                } else {
                    inner_local
                };
                rebuild_exec_unary(plan, mid)
            };

            match split_exec_node(
                raw_inner,
                ctx,
                child_ord_insens,
                SuppressPushCtx::None,
                false,
            ) {
                NodeSplit::Pushed(node) => {
                    let emit_group_meta = match suppress_ctx {
                        SuppressPushCtx::None => None,
                        SuppressPushCtx::Direct(distinct_by) => Some(distinct_by),
                        SuppressPushCtx::Indirect => {
                            return NodeSplit::Hybrid {
                                pushed: node,
                                placeholder_var: PLACEHOLDER.to_string(),
                                local_plan: wrap_local(exec_placeholder_plan(PLACEHOLDER)),
                                reason: "suppress_small_groups requires local group cardinality metadata from summarize".to_string(),
                            };
                        }
                    };
                    if !group_keys.is_empty() && !order_insensitive {
                        let reason = if matches!(suppress_ctx, SuppressPushCtx::Direct(_)) {
                            "grouped ExecPlan summarize under suppress_small_groups preserves first-seen order unless followed by total sort"
                        } else {
                            "grouped ExecPlan summarize preserves first-seen order unless followed by total sort"
                        };
                        return NodeSplit::Hybrid {
                            pushed: node,
                            placeholder_var: PLACEHOLDER.to_string(),
                            local_plan: wrap_local(exec_placeholder_plan(PLACEHOLDER)),
                            reason: reason.to_string(),
                        };
                    }
                    let orig = node.clone();
                    let mut translated_aggs = Vec::with_capacity(aggs.len());
                    for ExecAggItem { name, op, arg } in aggs {
                        let t_arg = match arg {
                            None => None,
                            Some(re) => match translate_exec_row_expr(re, &node.schema, ctx) {
                                Ok(t) => Some(t),
                                Err(reason) => {
                                    return NodeSplit::Hybrid {
                                        pushed: orig,
                                        placeholder_var: PLACEHOLDER.to_string(),
                                        local_plan: wrap_local(exec_placeholder_plan(PLACEHOLDER)),
                                        reason,
                                    };
                                }
                            },
                        };
                        translated_aggs.push((name.clone(), *op, t_arg));
                    }
                    match node.apply_summarize(
                        group_keys,
                        &translated_aggs,
                        distinct_key.as_deref(),
                        ctx.dialect,
                        false,
                        emit_group_meta,
                    ) {
                        Ok(next) => NodeSplit::Pushed(next),
                        Err(reason) => NodeSplit::Hybrid {
                            pushed: orig,
                            placeholder_var: PLACEHOLDER.to_string(),
                            local_plan: wrap_local(exec_placeholder_plan(PLACEHOLDER)),
                            reason,
                        },
                    }
                }
                NodeSplit::Hybrid {
                    pushed,
                    placeholder_var,
                    local_plan,
                    reason,
                } => NodeSplit::Hybrid {
                    pushed,
                    placeholder_var,
                    local_plan: wrap_local(local_plan),
                    reason,
                },
                NodeSplit::LocalOnly { reason } => NodeSplit::LocalOnly { reason },
            }
        }
        ExecPlan::Union { left, right } => {
            let l_split =
                split_exec_node(left, ctx, order_insensitive, SuppressPushCtx::None, false);
            let r_split =
                split_exec_node(right, ctx, order_insensitive, SuppressPushCtx::None, false);
            match (l_split, r_split) {
                (NodeSplit::Pushed(l), NodeSplit::Pushed(r)) => {
                    match PushedNode::apply_union(l, r) {
                        Ok(u) => NodeSplit::Pushed(u),
                        Err(reason) => NodeSplit::LocalOnly { reason },
                    }
                }
                (NodeSplit::Pushed(l), NodeSplit::LocalOnly { .. })
                    if !exec_plan_has_source_db(right, ctx, ctx.target_db) =>
                {
                    NodeSplit::Hybrid {
                        pushed: l,
                        placeholder_var: PLACEHOLDER.to_string(),
                        local_plan: ExecPlan::Union {
                            left: Box::new(exec_placeholder_plan(PLACEHOLDER)),
                            right: right.clone(),
                        },
                        reason: "cross-source union requires local VM".to_string(),
                    }
                }
                (NodeSplit::LocalOnly { .. }, NodeSplit::Pushed(r))
                    if !exec_plan_has_source_db(left, ctx, ctx.target_db) =>
                {
                    NodeSplit::Hybrid {
                        pushed: r,
                        placeholder_var: PLACEHOLDER.to_string(),
                        local_plan: ExecPlan::Union {
                            left: left.clone(),
                            right: Box::new(exec_placeholder_plan(PLACEHOLDER)),
                        },
                        reason: "cross-source union requires local VM".to_string(),
                    }
                }
                (NodeSplit::LocalOnly { reason }, _) | (_, NodeSplit::LocalOnly { reason }) => {
                    NodeSplit::LocalOnly { reason }
                }
                _ => NodeSplit::LocalOnly {
                    reason: "union with multiple partial DB branches requires local VM".to_string(),
                },
            }
        }
        ExecPlan::Join {
            kind,
            left,
            right,
            on,
            suffixes,
        } => {
            let l_split =
                split_exec_node(left, ctx, order_insensitive, SuppressPushCtx::None, false);
            let r_ord_insens = join_right_is_order_insensitive(*kind, order_insensitive);
            let r_split = split_exec_node(right, ctx, r_ord_insens, SuppressPushCtx::None, false);
            match (l_split, r_split) {
                (NodeSplit::Pushed(l), NodeSplit::Pushed(r)) => match PushedNode::apply_join(
                    *kind,
                    l,
                    r,
                    on,
                    suffixes,
                    ctx.dialect,
                    order_insensitive,
                ) {
                    Ok(j) => NodeSplit::Pushed(j),
                    Err(reason) => NodeSplit::LocalOnly { reason },
                },
                (NodeSplit::Pushed(l), NodeSplit::LocalOnly { .. })
                    if !exec_plan_has_source_db(right, ctx, ctx.target_db) =>
                {
                    NodeSplit::Hybrid {
                        pushed: l,
                        placeholder_var: PLACEHOLDER.to_string(),
                        local_plan: ExecPlan::Join {
                            kind: *kind,
                            left: Box::new(exec_placeholder_plan(PLACEHOLDER)),
                            right: right.clone(),
                            on: on.clone(),
                            suffixes: suffixes.clone(),
                        },
                        reason: "cross-source join requires local VM".to_string(),
                    }
                }
                (NodeSplit::LocalOnly { .. }, NodeSplit::Pushed(r))
                    if !exec_plan_has_source_db(left, ctx, ctx.target_db) =>
                {
                    NodeSplit::Hybrid {
                        pushed: r,
                        placeholder_var: PLACEHOLDER.to_string(),
                        local_plan: ExecPlan::Join {
                            kind: *kind,
                            left: left.clone(),
                            right: Box::new(exec_placeholder_plan(PLACEHOLDER)),
                            on: on.clone(),
                            suffixes: suffixes.clone(),
                        },
                        reason: "cross-source join requires local VM".to_string(),
                    }
                }
                (NodeSplit::LocalOnly { reason }, _) | (_, NodeSplit::LocalOnly { reason }) => {
                    NodeSplit::LocalOnly { reason }
                }
                _ => NodeSplit::LocalOnly {
                    reason: "join with multiple partial DB branches requires local VM".to_string(),
                },
            }
        }
        ExecPlan::SuppressSmallGroups {
            input, distinct_by, ..
        } => {
            let child_suppress_ctx = if matches!(input.as_ref(), ExecPlan::Summarize { .. }) {
                SuppressPushCtx::Direct(distinct_by.as_deref())
            } else {
                SuppressPushCtx::Indirect
            };
            split_exec_local_barrier(
                plan,
                input,
                ctx,
                order_insensitive,
                child_suppress_ctx,
                parent_has_sort,
                "suppress_small_groups enforces k-anonymity locally over SQL-aggregated groups",
            )
        }
        ExecPlan::Shuffle { input, .. } => split_exec_local_barrier(
            plan,
            input,
            ctx,
            false,
            SuppressPushCtx::None,
            false,
            "shuffle requires local VM",
        ),
        ExecPlan::SuppressSmallCells { input, .. } => split_exec_local_barrier(
            plan,
            input,
            ctx,
            order_insensitive,
            SuppressPushCtx::None,
            parent_has_sort,
            "suppress_small_cells requires local VM",
        ),
        ExecPlan::Window { input, .. } => split_exec_local_barrier(
            plan,
            input,
            ctx,
            false,
            SuppressPushCtx::None,
            false,
            "window operator requires local VM",
        ),
        ExecPlan::FillGaps { input, .. } => split_exec_local_barrier(
            plan,
            input,
            ctx,
            false,
            SuppressPushCtx::None,
            false,
            "fill_gaps operator requires local VM",
        ),
        ExecPlan::PivotWider { input, .. } => split_exec_local_barrier(
            plan,
            input,
            ctx,
            false,
            SuppressPushCtx::None,
            false,
            "pivot_wider operator requires local VM",
        ),
        ExecPlan::PivotLonger { input, .. } => split_exec_local_barrier(
            plan,
            input,
            ctx,
            false,
            SuppressPushCtx::None,
            false,
            "pivot_longer operator requires local VM",
        ),
        ExecPlan::Crosstab { input, .. } => split_exec_local_barrier(
            plan,
            input,
            ctx,
            false,
            SuppressPushCtx::None,
            false,
            "crosstab operator requires local VM",
        ),
        ExecPlan::Pseudonymize { input, .. } => split_exec_local_barrier(
            plan,
            input,
            ctx,
            false,
            SuppressPushCtx::None,
            false,
            "keyed pseudonymize requires local VM",
        ),
    }
}

fn split_exec_local_barrier(
    plan: &ExecPlan,
    input: &ExecPlan,
    ctx: &ExecSplitCtx<'_>,
    child_order_insensitive: bool,
    child_suppress_ctx: SuppressPushCtx<'_>,
    child_parent_has_sort: bool,
    barrier_msg: &str,
) -> NodeSplit<ExecPlan> {
    const PLACEHOLDER: &str = "__dana_pushdown_0";
    match split_exec_node(
        input,
        ctx,
        child_order_insensitive,
        child_suppress_ctx,
        child_parent_has_sort,
    ) {
        NodeSplit::Pushed(node) => NodeSplit::Hybrid {
            pushed: node,
            placeholder_var: PLACEHOLDER.to_string(),
            local_plan: rebuild_exec_unary(plan, exec_placeholder_plan(PLACEHOLDER)),
            reason: barrier_msg.to_string(),
        },
        NodeSplit::Hybrid {
            pushed,
            placeholder_var,
            local_plan,
            reason,
        } => NodeSplit::Hybrid {
            pushed,
            placeholder_var,
            local_plan: rebuild_exec_unary(plan, local_plan),
            reason,
        },
        NodeSplit::LocalOnly { reason } => NodeSplit::LocalOnly { reason },
    }
}

#[expect(
    clippy::too_many_arguments,
    reason = "Multi-branch recursive collector threading branch list, reasons, and ordering flags"
)]
fn collect_exec_rec(
    plan: &ExecPlan,
    ctx: &ExecSplitCtx<'_>,
    order_insensitive: bool,
    suppress_ctx: SuppressPushCtx<'_>,
    parent_has_sort: bool,
    next_id: &mut usize,
    branches: &mut Vec<CollectedBranchPushdown>,
    reasons: &mut Vec<String>,
) -> ExecPlan {
    match split_exec_node(plan, ctx, order_insensitive, suppress_ctx, parent_has_sort) {
        NodeSplit::Pushed(node) => {
            let var = format!("__dana_pushdown_{}", *next_id);
            *next_id += 1;
            branches.push(CollectedBranchPushdown {
                placeholder_var: var.clone(),
                pushdown: node.into_query(ctx.dialect, None),
            });
            exec_placeholder_plan(&var)
        }
        NodeSplit::Hybrid {
            pushed,
            placeholder_var,
            local_plan,
            reason,
        } => {
            let var = format!("__dana_pushdown_{}", *next_id);
            *next_id += 1;
            reasons.push(reason.clone());
            branches.push(CollectedBranchPushdown {
                placeholder_var: var.clone(),
                pushdown: pushed.into_query(ctx.dialect, Some(reason)),
            });
            rename_exec_placeholder(&local_plan, &placeholder_var, &var)
        }
        NodeSplit::LocalOnly { reason } => match plan {
            ExecPlan::Join {
                kind,
                left,
                right,
                on,
                suffixes,
            } => {
                reasons.push(reason);
                let new_l = collect_exec_rec(
                    left,
                    ctx,
                    order_insensitive,
                    SuppressPushCtx::None,
                    false,
                    next_id,
                    branches,
                    reasons,
                );
                let r_ord_insens = join_right_is_order_insensitive(*kind, order_insensitive);
                let new_r = collect_exec_rec(
                    right,
                    ctx,
                    r_ord_insens,
                    SuppressPushCtx::None,
                    false,
                    next_id,
                    branches,
                    reasons,
                );
                ExecPlan::Join {
                    kind: *kind,
                    left: Box::new(new_l),
                    right: Box::new(new_r),
                    on: on.clone(),
                    suffixes: suffixes.clone(),
                }
            }
            ExecPlan::Union { left, right } => {
                reasons.push(reason);
                let new_l = collect_exec_rec(
                    left,
                    ctx,
                    order_insensitive,
                    SuppressPushCtx::None,
                    false,
                    next_id,
                    branches,
                    reasons,
                );
                let new_r = collect_exec_rec(
                    right,
                    ctx,
                    order_insensitive,
                    SuppressPushCtx::None,
                    false,
                    next_id,
                    branches,
                    reasons,
                );
                ExecPlan::Union {
                    left: Box::new(new_l),
                    right: Box::new(new_r),
                }
            }
            ExecPlan::SourceExpr(_) | ExecPlan::SourceDB { .. } => {
                reasons.push(reason);
                plan.clone()
            }
            ExecPlan::SuppressSmallGroups {
                input, distinct_by, ..
            } => {
                let child_suppress_ctx = if matches!(input.as_ref(), ExecPlan::Summarize { .. }) {
                    SuppressPushCtx::Direct(distinct_by.as_deref())
                } else {
                    SuppressPushCtx::Indirect
                };
                let new_in = collect_exec_rec(
                    input,
                    ctx,
                    order_insensitive,
                    child_suppress_ctx,
                    parent_has_sort,
                    next_id,
                    branches,
                    reasons,
                );
                rebuild_exec_unary(plan, new_in)
            }
            ExecPlan::SuppressSmallCells { input, .. } => {
                let new_in = collect_exec_rec(
                    input,
                    ctx,
                    order_insensitive,
                    SuppressPushCtx::None,
                    parent_has_sort,
                    next_id,
                    branches,
                    reasons,
                );
                rebuild_exec_unary(plan, new_in)
            }
            ExecPlan::Sort { input, keys } => {
                let child_ord = order_insensitive || exec_sort_is_total_hint(input, keys, ctx);
                let new_in = collect_exec_rec(
                    input,
                    ctx,
                    child_ord,
                    SuppressPushCtx::None,
                    true,
                    next_id,
                    branches,
                    reasons,
                );
                rebuild_exec_unary(plan, new_in)
            }
            ExecPlan::DedupeBy {
                input,
                keys,
                order_by,
                ..
            } => {
                let mut combined = keys.clone();
                for (c, _) in order_by {
                    if !combined.contains(c) {
                        combined.push(c.clone());
                    }
                }
                let unique_tie =
                    exec_plan_cols_and_uqs_hint(input, ctx).is_some_and(|(in_cols, uqs)| {
                        in_cols.iter().all(|c| combined.contains(c))
                            || uqs.iter().any(|uk| uk.iter().all(|k| combined.contains(k)))
                    });
                let child_ord = order_insensitive && unique_tie;
                let new_in = collect_exec_rec(
                    input,
                    ctx,
                    child_ord,
                    SuppressPushCtx::None,
                    parent_has_sort,
                    next_id,
                    branches,
                    reasons,
                );
                rebuild_exec_unary(plan, new_in)
            }
            other => {
                if let Some(child) = exec_unary_child(other) {
                    let child_suppress =
                        if matches!(other, ExecPlan::Drop { .. } | ExecPlan::Derive { .. }) {
                            suppress_ctx.indirect_if_active()
                        } else {
                            SuppressPushCtx::None
                        };
                    let new_in = collect_exec_rec(
                        child,
                        ctx,
                        order_insensitive,
                        child_suppress,
                        parent_has_sort,
                        next_id,
                        branches,
                        reasons,
                    );
                    rebuild_exec_unary(other, new_in)
                } else {
                    reasons.push(reason);
                    other.clone()
                }
            }
        },
    }
}

fn rename_exec_placeholder(plan: &ExecPlan, from: &str, to: &str) -> ExecPlan {
    if from == to {
        return plan.clone();
    }
    match plan {
        ExecPlan::SourceExpr(e) => {
            if let ExecExpr::Var(v) = e.as_ref()
                && v == from
            {
                return exec_placeholder_plan(to);
            }
            plan.clone()
        }
        ExecPlan::SourceDB { .. } => plan.clone(),
        ExecPlan::Join {
            kind,
            left,
            right,
            on,
            suffixes,
        } => ExecPlan::Join {
            kind: *kind,
            left: Box::new(rename_exec_placeholder(left, from, to)),
            right: Box::new(rename_exec_placeholder(right, from, to)),
            on: on.clone(),
            suffixes: suffixes.clone(),
        },
        ExecPlan::Union { left, right } => ExecPlan::Union {
            left: Box::new(rename_exec_placeholder(left, from, to)),
            right: Box::new(rename_exec_placeholder(right, from, to)),
        },
        other => {
            if let Some(child) = exec_unary_child(other) {
                rebuild_exec_unary(other, rename_exec_placeholder(child, from, to))
            } else {
                other.clone()
            }
        }
    }
}

// ===========================================================================
// Helper: Inspect Pushable SQL Table Names (used by explain & tests)
// ===========================================================================

/// Collect the distinct database names referenced by `SourceDB` leaves inside a Core IR [`Plan`].
#[must_use]
pub fn core_plan_db_names(plan: &Plan, prog: &Program) -> Vec<Ident> {
    let ctx = CoreSplitCtx::new(prog, None, SqlDialect::Sqlite, None);
    let mut seen = HashSet::new();
    let mut out = Vec::new();
    let mut stack = vec![plan];
    while let Some(cur) = stack.pop() {
        match cur {
            Plan::SourceDB { cap, .. } => {
                if let Some(db) = ctx.resolve_source_db(cap)
                    && seen.insert(db.clone())
                {
                    out.push(db);
                }
            }
            Plan::Join { left, right, .. } | Plan::Union { left, right } => {
                stack.push(right);
                stack.push(left);
            }
            other => {
                if let Some(child) = core_unary_child(other) {
                    stack.push(child);
                }
            }
        }
    }
    out
}

/// Collect the distinct database names referenced by `SourceDB` leaves inside an [`ExecPlan`].
#[must_use]
pub fn exec_plan_db_names(plan: &ExecPlan, prog: &ExecProgram) -> Vec<Ident> {
    let ctx = ExecSplitCtx::new(prog, None, SqlDialect::Sqlite, None);
    let mut seen = HashSet::new();
    let mut out = Vec::new();
    let mut stack = vec![plan];
    while let Some(cur) = stack.pop() {
        match cur {
            ExecPlan::SourceDB { cap, .. } => {
                if let Some(db) = ctx.resolve_source_db(cap)
                    && seen.insert(db.clone())
                {
                    out.push(db);
                }
            }
            ExecPlan::Join { left, right, .. } | ExecPlan::Union { left, right } => {
                stack.push(right);
                stack.push(left);
            }
            other => {
                if let Some(child) = exec_unary_child(other) {
                    stack.push(child);
                }
            }
        }
    }
    out
}
