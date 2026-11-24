//! Compact, deterministic fuel-indexed naive row-by-row differential reference oracle
//! for Dana Core IR v0.1.
//!
//! Mirrors `formal/DanaCore/Eval.lean` and `formal/Main.lean` byte-for-byte.

pub mod cli;
pub mod eval;
pub mod value;
pub mod world;

pub use cli::{CliError, CliMode, CliOpts, parse_cli_args, parse_comma_tags};
pub use eval::{
    RuntimeError, eval, eval_literal, eval_plan, eval_prim_op, eval_row_expr, fnv1a64,
    pseudonymize_token, run_program,
};
pub use value::{
    Bug, CapHandle, ChartVal, Env, EnvEntry, GroupMeta, ProfileColSummary, ProfileVal, ReportVal,
    TableRow, TableVal, Val, float_order_key, format_diag_detail, redact_tags, render_decimal,
    render_public_val, val_cmp, val_eq, val_list_eq, val_list_lt, val_lt,
};
pub use world::{
    ExecReport, ExitStatus, FakeConsoleState, FakeDBState, FakeFilesState, FakeHttpsState, Outcome,
    StoredTable, World, extract_report,
};
