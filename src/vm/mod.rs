//! Vectorized 2,048-row columnar batch VM and deterministic parallel execution engine.
//!
//! Executes both Dana Core IR v0.1 (`core::Program` / `core::Plan`) and Phase 2
//! execution IR (`runtime::ir::ExecProgram` / `ExecPlan`) over cache-resident
//! 2,048-row columnar [`Batch`]es:
//! - Contiguous typed columns (`i64`, 128-bit fixed-point `Decimal`, `Float64` bits,
//!   Arrow-style UTF-8/bytes offset buffers, bit-packed [`NullBitmap`])
//! - Compiled register-based row-expression bytecode ([`expr::RowProgram`]) with
//!   automatic pure user-function inlining (zero UDF cliff)
//! - Vectorized physical operators: selection-vector `Filter`, `HashJoin`,
//!   radix-partitioned `HashAggregate`, `SuppressSmallGroups`, `Sort`, `Distinct`,
//!   `Window`, `FillGaps`, `PivotWider`, `Crosstab`, `Redact`, `Pseudonymize`
//! - Deterministic `std::thread::scope` multi-core parallelism preserving exact
//!   output order and earliest-row `Bug` semantics.

pub mod batch;
pub mod decimal;
pub mod exec;
pub mod expr;
pub mod key;
pub mod ops;
pub mod parallel;

use crate::runtime::ir::PseudonymizeMode;

pub use batch::{
    BATCH_SIZE, Batch, Column, ColumnData, NullBitmap, batches_to_table, rows_to_batches,
    table_to_batches,
};
pub use exec::{
    eval_core_plan_batches, run_core_program_vm, run_exec_program_vm, run_program_tests_vm,
};
pub use ops::{OpErr, OpExecConfig, VmMode, VmTable};

/// Configuration for the vectorized columnar batch VM.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct VmConfig {
    /// Target rows per columnar batch (default `2_048`).
    pub batch_size: usize,
    /// Minimum active rows before fanning out across `std::thread::scope` workers (default `8_192`).
    pub parallel_threshold_rows: usize,
    /// Optional explicit worker thread cap (`Some(1)` forces sequential execution).
    pub max_threads: Option<usize>,
    /// Enable the relational query optimizer (`src/plan/opt.rs`) before execution (default `true`).
    pub optimize: bool,
    /// Pseudonymization hash mode for Phase 2 `ExecProgram` execution (`CoreV01` always uses FNV-1a).
    pub pseudonymize_mode: PseudonymizeMode,
}

impl Default for VmConfig {
    fn default() -> Self {
        Self {
            batch_size: BATCH_SIZE,
            parallel_threshold_rows: 8_192,
            max_threads: None,
            optimize: true,
            pseudonymize_mode: PseudonymizeMode::HmacSha256,
        }
    }
}

impl VmConfig {
    /// Sequential, unoptimized VM configuration (useful for differential oracle checks).
    #[must_use]
    pub fn sequential_unoptimized() -> Self {
        Self {
            batch_size: BATCH_SIZE,
            parallel_threshold_rows: usize::MAX,
            max_threads: Some(1),
            optimize: false,
            pseudonymize_mode: PseudonymizeMode::CoreV01Fnv1a,
        }
    }

    /// Sequential, optimized VM configuration.
    #[must_use]
    pub fn sequential_optimized() -> Self {
        Self {
            batch_size: BATCH_SIZE,
            parallel_threshold_rows: usize::MAX,
            max_threads: Some(1),
            optimize: true,
            pseudonymize_mode: PseudonymizeMode::CoreV01Fnv1a,
        }
    }

    /// Parallel, optimized VM configuration with an explicit threshold and thread count.
    #[must_use]
    pub fn parallel_optimized(threshold_rows: usize, threads: usize) -> Self {
        Self {
            batch_size: BATCH_SIZE,
            parallel_threshold_rows: threshold_rows,
            max_threads: Some(threads.max(1)),
            optimize: true,
            pseudonymize_mode: PseudonymizeMode::CoreV01Fnv1a,
        }
    }
}
