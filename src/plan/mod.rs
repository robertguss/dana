//! Relational query optimizer and human-readable plan explainer.
//!
//! Provides provably semantics-, stop-, tag-, and cardinality-preserving algebraic
//! rewrites for both Dana Core IR v0.1 (`core::Plan` / `core::Program`) and Phase 2
//! execution IR (`runtime::ir::ExecPlan` / `ExecProgram`):
//! - Filter fusion (`Filter(Filter(p, e1), e2)` -> short-circuit `IfE(e1, e2, false)`)
//! - Stop- and cardinality-preserving predicate pushdown (across `Select`, `Drop`,
//!   `Rename`, total independent `Derive`, `Redact`, `Sort`, `Union`, and safe `Join`
//!   sides whose uniqueness is never checked)
//! - Dead `Derive` item pruning, `Select` fusion, `Drop([])`/`Rename([])`/`Filter(true)`
//!   elimination, and `Limit` min-folding
//! - Readable logical vs. optimized plan tree rendering (`explain_plan` / `explain_exec_plan`).

pub mod explain;
pub mod opt;

pub use explain::{explain_exec_plan, explain_plan};
pub use opt::{
    OptStats, optimize_exec_plan, optimize_exec_program, optimize_plan, optimize_program,
};
