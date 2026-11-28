//! Relational query optimizer, parameterized SQL pushdown splitter, and
//! sensitivity-aware plan explainer.
//!
//! Provides provably semantics-, stop-, tag-, and cardinality-preserving algebraic
//! rewrites and SQL pushdown splitting for both Dana Core IR v0.1 (`core::Plan` /
//! `core::Program`) and Phase 2 execution IR (`runtime::ir::ExecPlan` / `ExecProgram`):
//! - Filter fusion (`Filter(Filter(p, e1), e2)` -> short-circuit `IfE(e1, e2, false)`)
//! - Stop- and cardinality-preserving predicate pushdown (across `Select`, `Drop`,
//!   `Rename`, total independent `Derive`, `Redact`, `Sort`, `Union`, and safe `Join`
//!   sides whose uniqueness is never checked)
//! - Dead `Derive` item pruning, `Select` fusion, `Drop([])`/`Rename([])`/`Filter(true)`
//!   elimination, and `Limit` min-folding
//! - 100% parameterized SQL pushdown splitting (`split_core_plan_pushdown`,
//!   `split_exec_plan_pushdown`, `collect_core_plan_pushdowns`, `collect_exec_plan_pushdowns`)
//! - Readable logical/optimized/pushdown/sensitivity-provenance plan rendering.

pub mod explain;
pub mod opt;
pub mod pushdown;

pub use explain::{
    bind_lty_in_scope, explain_core_plan_with_pushdown, explain_exec_plan,
    explain_exec_plan_with_pushdown, explain_exec_plan_with_pushdown_scoped,
    explain_exec_sensitivity_provenance, explain_exec_sensitivity_provenance_scoped, explain_plan,
    explain_sensitivity_provenance,
};
pub use opt::{
    OptStats, optimize_exec_plan, optimize_exec_program, optimize_plan, optimize_program,
};
pub use pushdown::{
    CollectedBranchPushdown, CollectedPlanPushdowns, HIDDEN_GROUP_DISTINCT_COUNT_COL,
    HIDDEN_GROUP_ROW_COUNT_COL, SplitPlan, SqlParamSlot, SqlPushdownQuery, bind_exec_plan_sources,
    collect_core_plan_pushdowns, collect_exec_plan_pushdowns, core_plan_db_names,
    describe_sql_param, exec_plan_db_names, split_core_plan_pushdown, split_exec_plan_pushdown,
    split_exec_plan_pushdown_with_options, split_exec_plan_pushdown_with_table_refs,
};
