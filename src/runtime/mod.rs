//! Phase 2 execution IR (`ir`) and reference runtime evaluator (`exec`).
//!
//! Keeps `formal/` and `src/core/` (Core IR v0.1) untouched while providing clean,
//! deterministic execution for both pure Core IR v0.1 programs (verifiable by `src/core/check.rs`
//! and `danacore`) and Phase 2 surface operations (float arithmetic, `round`, `abs`,
//! `date_trunc` with duration, `months_between`, CSV/JSONL I/O, `Table` row helpers,
//! and isolated `dana test` fake capability inspection).

pub mod exec;
pub mod ir;

pub use exec::{RunConfig, RunResult, TestOutcome, run_exec_program, run_program_tests};
pub use ir::{
    CompiledSchema, ExecCaseArm, ExecDeriveItem, ExecExpr, ExecFun, ExecHostOp, ExecPlan,
    ExecPrimOp, ExecProgram, ExecPromise, ExecRowExpr, PseudonymizeMode, StructLayout,
};
