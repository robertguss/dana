//! Top-level vectorized VM evaluators for both Core IR v0.1 (`core::Program`)
//! and Phase 2 `ExecProgram`, plus direct batch-level plan execution for benchmarks.

use std::collections::HashMap;
use std::sync::Arc;

use crate::core::bigint::BigInt;
use crate::core::check::{
    PlanTy, apply_derive_item_arc, apply_window_item, check_expr_arc, check_plan_arc,
    check_program, infer_jump_pc_arc, is_safe_relative_path, join_confined_path,
    quarantine_bad_row_table_ty,
};
use crate::core::stack::with_large_stack;
use crate::core::syntax::{
    AggKind, BugKind, CaseArm, ColSpec, DeriveItem, Expr, HostOp, Ident, LTy, Plan, PrimOp,
    Program, ScalarTy, TableTy, TagSet, Ty,
};
use crate::db::schema_lock::SchemaLockFile;
use crate::db::{SqlDialect, SqlParam, quote_sql_ident};
use crate::oracle::eval::{PrimResult, RuntimeError, eval_literal, eval_prim_op};
use crate::oracle::value::{
    Bug, CapHandle, ClosureVal, EnvEntry, EnvList, ReportVal, TableRow, TableVal, Val,
    format_diag_detail, render_public_val, repr_bug_kind,
};
use crate::oracle::world::{
    ExecReport, FakeConsoleState, FakeDBState, FakeFilesState, FakeHttpsState, Outcome,
    StoredTable, World, extract_report,
};
use crate::plan::{SplitPlan, optimize_exec_plan, optimize_program, split_exec_plan_pushdown};
use crate::runtime::exec::{
    EvalProgramResult, RunConfig, RunResult, TestOutcome, eval_exec_entry_with_engine,
    eval_pure_exec_call, run_exec_program_with_engine, run_program_tests_with_engine,
};
use crate::runtime::ir::{ExecDeriveItem, ExecExpr, ExecPlan, ExecProgram};
use crate::vm::VmConfig;
use crate::vm::expr::{RowEvalErr, RowEvalHost, compile_core_row_expr, compile_exec_row_expr};
use crate::vm::ops::agg::{CompiledAgg, op_hash_aggregate, op_suppress_small_groups};
use crate::vm::ops::join::op_hash_join;
use crate::vm::ops::sort_win::{
    op_crosstab, op_distinct, op_fill_gaps, op_pivot_longer, op_pivot_wider, op_sort, op_window,
};
use crate::vm::ops::{
    OpErr, OpExecConfig, VmMode, VmTable, op_derive_bucket, op_derive_col_expr, op_drop, op_filter,
    op_group_by, op_limit, op_pseudonymize, op_redact, op_rename, op_select, op_union,
};

// ===========================================================================
// Public Entry Points for Phase 2 `ExecProgram`
// ===========================================================================

/// Execute `main(...)` of a lowered [`ExecProgram`] using the vectorized columnar VM.
#[must_use]
pub fn run_exec_program_vm(
    prog: &ExecProgram,
    run_cfg: &RunConfig,
    vm_cfg: &VmConfig,
) -> RunResult {
    let mut cfg = *vm_cfg;
    cfg.pseudonymize_mode = run_cfg.pseudonymize_mode;
    run_exec_program_with_engine(prog, run_cfg, Some(cfg))
}

/// Evaluate a named entry function of a lowered [`ExecProgram`] on the vectorized columnar VM,
/// returning its typed runtime [`Val`] and static [`LTy`] (used by `dana repl`).
#[must_use]
pub fn eval_exec_entry_vm(
    prog: &ExecProgram,
    entry_name: &str,
    prebound: &[(Ident, Val)],
    run_cfg: &RunConfig,
    vm_cfg: &VmConfig,
) -> EvalProgramResult {
    let mut cfg = *vm_cfg;
    cfg.pseudonymize_mode = run_cfg.pseudonymize_mode;
    eval_exec_entry_with_engine(prog, entry_name, prebound, run_cfg, Some(cfg))
}

/// Run all `examples` and `test` spec blocks in a lowered [`ExecProgram`] using the
/// vectorized columnar VM.
#[must_use]
pub fn run_program_tests_vm(
    prog: &ExecProgram,
    filter: Option<&str>,
    run_cfg: &RunConfig,
    vm_cfg: &VmConfig,
) -> Vec<TestOutcome> {
    let mut cfg = *vm_cfg;
    cfg.pseudonymize_mode = run_cfg.pseudonymize_mode;
    run_program_tests_with_engine(prog, filter, run_cfg, Some(cfg))
}

// ===========================================================================
// `ExecPlan` Vectorized Execution Engine (called by `src/runtime/exec.rs`)
// ===========================================================================

struct ExecRowHost<'a> {
    prog: &'a ExecProgram,
    outer_env: &'a HashMap<Ident, Arc<Val>>,
    fuel: usize,
}

impl RowEvalHost for ExecRowHost<'_> {
    fn lookup_outer(&self, name: &str) -> Option<Val> {
        self.outer_env.get(name).map(|v| v.as_ref().clone())
    }

    fn lookup_const(&self, name: &str) -> Option<Val> {
        self.prog.find_const(name).map(|c| eval_literal(&c.value))
    }

    fn call_pure_fallback(&self, fn_name: &str, args: Vec<Val>) -> Result<Val, RowEvalErr> {
        eval_pure_exec_call(self.prog, fn_name, args, self.fuel)
    }
}

/// Callbacks bridging `ExecPlan` outer expressions & capabilities into the vectorized VM.
pub trait ExecPlanBridge {
    fn eval_outer_expr(
        &mut self,
        expr: &ExecExpr,
        env: &HashMap<Ident, Arc<Val>>,
    ) -> Result<Val, OpErr>;
    fn load_fake_db_table(
        &mut self,
        cap: Val,
        table_name: &str,
        schema: &TableTy,
    ) -> Result<TableVal, OpErr>;
    fn resolve_secret_material(&self, sec_val: &Val) -> String;

    /// If `cap_val` is a live `ReadDB(db_name)`, resolve/open its connection and return
    /// `(db_name, dialect)`. Returns `Ok(None)` for in-memory fake DB handles.
    fn live_db_info(&mut self, cap_val: &Val) -> Result<Option<(Ident, SqlDialect)>, OpErr>;

    /// Return the optional offline [`SchemaLockFile`] configured for this run.
    fn schema_lock(&self) -> Option<&SchemaLockFile>;

    /// Execute a parameterized SQL query against live logical database `db_name` and stream
    /// results directly into `batch_size`-row columnar batches.
    fn exec_live_sql_batches(
        &mut self,
        db_name: &str,
        sql: &str,
        params: &[SqlParam],
        expected_schema: &TableTy,
        batch_size: usize,
    ) -> Result<VmTable, OpErr>;
}

/// Execute a Phase 2 [`ExecPlan`] through the optional relational optimizer, automatic
/// parameterized SQL pushdown (for live `ReadDB` sources), and the 2,048-row vectorized
/// columnar batch VM.
pub fn eval_exec_plan_vm(
    plan: &ExecPlan,
    prog: &ExecProgram,
    env: &HashMap<Ident, Arc<Val>>,
    vm_cfg: &VmConfig,
    fuel: usize,
    bridge: &mut dyn ExecPlanBridge,
) -> Result<Val, OpErr> {
    let owned_opt;
    let effective_plan = if vm_cfg.optimize {
        let (opt, _) = optimize_exec_plan(plan, prog);
        owned_opt = opt;
        &owned_opt
    } else {
        plan
    };
    let op_cfg = OpExecConfig {
        batch_size: vm_cfg.batch_size,
        parallel_threshold_rows: vm_cfg.parallel_threshold_rows,
        max_threads: vm_cfg.max_threads,
        mode: VmMode::ExecSurface,
        pseudonymize_mode: vm_cfg.pseudonymize_mode,
    };
    let row_host = ExecRowHost {
        prog,
        outer_env: env,
        fuel,
    };
    let mut preloaded: Vec<(Ident, VmTable)> = Vec::new();
    if let ExecPlan::Crosstab {
        input,
        rows_col,
        cols_col,
        values_col,
        fill,
    } = effective_plan
    {
        let in_tbl = eval_exec_plan_to_table(
            input,
            prog,
            env,
            &mut preloaded,
            &row_host,
            &op_cfg,
            bridge,
            true,
        )?;
        return op_crosstab(in_tbl, rows_col, cols_col, values_col, fill, &op_cfg);
    }
    let out_tbl = eval_exec_plan_to_table(
        effective_plan,
        prog,
        env,
        &mut preloaded,
        &row_host,
        &op_cfg,
        bridge,
        true,
    )?;
    Ok(Val::Columnar(Arc::new(out_tbl)))
}

fn collect_exec_source_db_caps<'a>(plan: &'a ExecPlan, out: &mut Vec<&'a ExecExpr>) {
    let mut stack = vec![plan];
    while let Some(cur) = stack.pop() {
        match cur {
            ExecPlan::SourceDB { cap, .. } => out.push(cap),
            ExecPlan::SourceExpr(_) => {}
            ExecPlan::Join { left, right, .. } | ExecPlan::Union { left, right } => {
                stack.push(right);
                stack.push(left);
            }
            other => {
                if let Some(child) = exec_unary_input(other) {
                    stack.push(child);
                }
            }
        }
    }
}

#[expect(
    clippy::too_many_arguments,
    reason = "Vectorized ExecPlan evaluator threads preloaded SQL-pushdown batches and bridge callbacks without row marshalling"
)]
fn eval_exec_plan_to_table(
    plan: &ExecPlan,
    prog: &ExecProgram,
    env: &HashMap<Ident, Arc<Val>>,
    preloaded: &mut Vec<(Ident, VmTable)>,
    row_host: &ExecRowHost<'_>,
    cfg: &OpExecConfig,
    bridge: &mut dyn ExecPlanBridge,
    allow_pushdown: bool,
) -> Result<VmTable, OpErr> {
    if allow_pushdown {
        let mut db_caps = Vec::new();
        collect_exec_source_db_caps(plan, &mut db_caps);
        if !db_caps.is_empty() {
            let mut single_live: Option<(Ident, SqlDialect)> = None;
            let mut all_same_live = true;
            for cap in db_caps {
                let cap_v = bridge.eval_outer_expr(cap, env)?;
                match bridge.live_db_info(&cap_v)? {
                    Some((db_name, dialect)) => match &single_live {
                        None => single_live = Some((db_name, dialect)),
                        Some((prev_db, _)) if *prev_db == db_name => {}
                        Some(_) => {
                            all_same_live = false;
                            break;
                        }
                    },
                    None => {
                        all_same_live = false;
                        break;
                    }
                }
            }
            if all_same_live && let Some((db_name, dialect)) = single_live {
                let split =
                    split_exec_plan_pushdown(plan, prog, &db_name, dialect, bridge.schema_lock());
                match split {
                    SplitPlan::FullyPushed(q) => {
                        let params = q
                            .resolve_params(
                                |v| env.get(v).map(|val| val.as_ref().clone()),
                                |c| prog.find_const(c).map(|d| eval_literal(&d.value)),
                            )
                            .map_err(OpErr::Failed)?;
                        return bridge.exec_live_sql_batches(
                            &q.db_name,
                            &q.sql,
                            &params,
                            &q.out_schema,
                            cfg.batch_size,
                        );
                    }
                    SplitPlan::Hybrid {
                        pushdown,
                        placeholder_var,
                        local_suffix,
                    } => {
                        let params = pushdown
                            .resolve_params(
                                |v| env.get(v).map(|val| val.as_ref().clone()),
                                |c| prog.find_const(c).map(|d| eval_literal(&d.value)),
                            )
                            .map_err(OpErr::Failed)?;
                        let pushed_tbl = bridge.exec_live_sql_batches(
                            &pushdown.db_name,
                            &pushdown.sql,
                            &params,
                            &pushdown.out_schema,
                            cfg.batch_size,
                        )?;
                        preloaded.push((placeholder_var, pushed_tbl));
                        return eval_exec_plan_to_table(
                            &local_suffix,
                            prog,
                            env,
                            preloaded,
                            row_host,
                            cfg,
                            bridge,
                            true,
                        );
                    }
                    SplitPlan::LocalOnly { .. } => {}
                }
            }
        }
    }

    // Iteratively peel deep unary chains so 200,000-stage relational pipelines run in O(1) stack!
    let mut unary_stack: Vec<&ExecPlan> = Vec::new();
    let mut leaf = plan;
    while let Some(child) = exec_unary_input(leaf) {
        unary_stack.push(leaf);
        leaf = child;
    }

    let mut cur = match leaf {
        ExecPlan::SourceExpr(e) => {
            if let ExecExpr::Var(name) = e.as_ref()
                && let Some(pos) = preloaded.iter().rposition(|(k, _)| k == name)
            {
                preloaded.remove(pos).1
            } else if let ExecExpr::Var(name) = e.as_ref()
                && let Some(val) = env.get(name)
            {
                match val.as_ref() {
                    Val::Columnar(vm_arc) => {
                        // Fast-path `tbl |> limit(n)` directly on a shared columnar table
                        // without cloning batches past `n`.
                        if let Some(ExecPlan::Limit { n, .. }) = unary_stack.last() {
                            let lim = n.to_u64().unwrap_or(0) as usize;
                            unary_stack.pop();
                            vm_arc.slice_first(lim)
                        } else {
                            vm_arc.as_ref().clone()
                        }
                    }
                    Val::Table(tv) => VmTable::from_table_val(tv, cfg.batch_size),
                    _ => return Err(OpErr::Failed("plan did not evaluate to Table".to_string())),
                }
            } else {
                let v = bridge.eval_outer_expr(e, env)?;
                let Some(vm) = v.into_vm_table(cfg.batch_size) else {
                    return Err(OpErr::Failed("plan did not evaluate to Table".to_string()));
                };
                vm
            }
        }
        ExecPlan::SourceDB {
            cap,
            table_name,
            schema,
        } => {
            let cap_v = bridge.eval_outer_expr(cap, env)?;
            if let Some((db_name, _dialect)) = bridge.live_db_info(&cap_v)? {
                let effective_table = bridge
                    .schema_lock()
                    .and_then(|l| l.find_db(&db_name))
                    .and_then(|d| d.resolve_table(table_name).ok())
                    .map_or_else(|| table_name.clone(), |t| t.name.clone());
                let cols_sql: Vec<String> = schema
                    .cols
                    .iter()
                    .map(|c| quote_sql_ident(&c.name))
                    .collect();
                let sql = if cols_sql.is_empty() {
                    format!("SELECT 1 FROM {}", quote_sql_ident(&effective_table))
                } else {
                    format!(
                        "SELECT {} FROM {}",
                        cols_sql.join(", "),
                        quote_sql_ident(&effective_table)
                    )
                };
                bridge.exec_live_sql_batches(&db_name, &sql, &[], schema, cfg.batch_size)?
            } else {
                let tv = bridge.load_fake_db_table(cap_v, table_name, schema)?;
                VmTable::from_table_val(&tv, cfg.batch_size)
            }
        }
        ExecPlan::Union { left, right } => {
            let lt =
                eval_exec_plan_to_table(left, prog, env, preloaded, row_host, cfg, bridge, true)?;
            let rt =
                eval_exec_plan_to_table(right, prog, env, preloaded, row_host, cfg, bridge, true)?;
            op_union(lt, rt, cfg.mode)?
        }
        ExecPlan::Join {
            kind,
            left,
            right,
            on,
            suffixes,
        } => {
            // Borrow `Val::Columnar` inputs directly from `env` without cloning full tables!
            enum JoinInput<'a> {
                Borrowed(&'a VmTable),
                Owned(VmTable),
            }
            impl JoinInput<'_> {
                fn as_table(&self) -> &VmTable {
                    match self {
                        Self::Borrowed(t) => t,
                        Self::Owned(t) => t,
                    }
                }
            }
            let borrow_env_col = |side: &ExecPlan, pre: &[(Ident, VmTable)]| -> Option<&VmTable> {
                if let ExecPlan::SourceExpr(e) = side
                    && let ExecExpr::Var(name) = e.as_ref()
                    && !pre.iter().any(|(k, _)| k == name)
                    && let Some(val) = env.get(name)
                    && let Val::Columnar(vm_arc) = val.as_ref()
                {
                    return Some(vm_arc.as_ref());
                }
                None
            };
            let lt = if let Some(b) = borrow_env_col(left, preloaded) {
                JoinInput::Borrowed(b)
            } else {
                JoinInput::Owned(eval_exec_plan_to_table(
                    left, prog, env, preloaded, row_host, cfg, bridge, true,
                )?)
            };
            let rt = if let Some(b) = borrow_env_col(right, preloaded) {
                JoinInput::Borrowed(b)
            } else {
                JoinInput::Owned(eval_exec_plan_to_table(
                    right, prog, env, preloaded, row_host, cfg, bridge, true,
                )?)
            };
            op_hash_join(
                *kind,
                lt.as_table(),
                rt.as_table(),
                on,
                suffixes,
                &TagSet::empty(),
                cfg,
            )?
        }
        _ => {
            return Err(OpErr::Failed(
                "unexpected unary stage in exec plan leaf".to_string(),
            ));
        }
    };

    while let Some(stage) = unary_stack.pop() {
        cur = match stage {
            ExecPlan::Select { cols, .. } => op_select(cur, cols, cfg.mode)?,
            ExecPlan::Drop { cols, .. } => op_drop(cur, cols, cfg.mode)?,
            ExecPlan::Rename { pairs, .. } => op_rename(cur, pairs, cfg.mode),
            ExecPlan::Filter { pred, .. } => {
                let rp = compile_exec_row_expr(pred, prog);
                op_filter(cur, &rp, row_host, cfg)?
            }
            ExecPlan::Derive { items, .. } => {
                let mut t = cur;
                for item in items {
                    match item {
                        ExecDeriveItem::ColExpr { name, expr } => {
                            let rp = compile_exec_row_expr(expr, prog);
                            let spec = t
                                .cols
                                .iter()
                                .find(|c| c.name == *name)
                                .cloned()
                                .unwrap_or_else(|| ColSpec {
                                    name: name.clone(),
                                    ty: ScalarTy::Unit,
                                    tags: TagSet::empty(),
                                    bucketed: false,
                                    agg_kind: AggKind::Raw,
                                });
                            t = op_derive_col_expr(t, spec, &rp, row_host, cfg)?;
                        }
                        ExecDeriveItem::BucketCol {
                            name,
                            source,
                            cuts,
                            labels,
                        } => {
                            t = op_derive_bucket(t, name, source, cuts, labels, None, cfg)?;
                        }
                    }
                }
                t
            }
            ExecPlan::Distinct { cols, .. } => op_distinct(cur, cols, cfg)?,
            ExecPlan::Sort { keys, .. } => op_sort(cur, keys, cfg),
            ExecPlan::Limit { n, .. } => {
                let lim = n.to_u64().unwrap_or(0) as usize;
                op_limit(cur, lim, cfg.mode)
            }
            ExecPlan::GroupBy { keys, .. } => op_group_by(cur, keys, cfg.mode),
            ExecPlan::Summarize {
                input,
                aggs,
                distinct_key,
            } => {
                let gkeys = match input.as_ref() {
                    ExecPlan::GroupBy { keys, .. } => keys.clone(),
                    _ => Vec::new(),
                };
                let mut out_cols: Vec<ColSpec> = gkeys
                    .iter()
                    .filter_map(|k| cur.cols.iter().find(|c| c.name == *k).cloned())
                    .map(|mut c| {
                        c.agg_kind = AggKind::GroupKey;
                        c
                    })
                    .collect();
                let mut compiled_aggs = Vec::with_capacity(aggs.len());
                for a in aggs {
                    let spec = ColSpec {
                        name: a.name.clone(),
                        ty: ScalarTy::Unit,
                        tags: TagSet::empty(),
                        bucketed: false,
                        agg_kind: if a.op.is_blending() {
                            AggKind::Blending
                        } else {
                            AggKind::NonBlending
                        },
                    };
                    out_cols.push(spec.clone());
                    compiled_aggs.push(CompiledAgg {
                        name: a.name.clone(),
                        op: a.op,
                        out_spec: spec,
                        arg_prog: a.arg.as_ref().map(|re| compile_exec_row_expr(re, prog)),
                    });
                }
                op_hash_aggregate(
                    cur,
                    &gkeys,
                    &compiled_aggs,
                    distinct_key.as_deref(),
                    out_cols,
                    row_host,
                    cfg,
                )?
            }
            ExecPlan::SuppressSmallGroups {
                min_k,
                distinct_by,
                mode,
                ..
            } => {
                let floor = prog.min_group_floor().max(min_k.clone());
                op_suppress_small_groups(cur, &floor, distinct_by, *mode, &TagSet::empty(), cfg)
            }
            ExecPlan::Window { items, .. } => op_window(cur, items, None, cfg)?,
            ExecPlan::FillGaps {
                col,
                step_micros,
                over,
                fill,
                ..
            } => op_fill_gaps(cur, col, step_micros, over, fill, None, cfg)?,
            ExecPlan::PivotWider {
                names_from,
                values_from,
                static_cols,
                fill,
                ..
            } => op_pivot_wider(cur, names_from, values_from, static_cols, fill, None, cfg)?,
            ExecPlan::PivotLonger {
                cols,
                names_to,
                values_to,
                value_ty,
                value_tags,
                ..
            } => op_pivot_longer(cur, cols, names_to, values_to, value_ty, value_tags, cfg)?,
            ExecPlan::Redact {
                col, replacement, ..
            } => op_redact(cur, col, replacement, &TagSet::empty(), cfg)?,
            ExecPlan::Pseudonymize { col, secret, .. } => {
                let sec_val = bridge.eval_outer_expr(secret, env)?;
                let key_mat = bridge.resolve_secret_material(&sec_val);
                op_pseudonymize(cur, col, &key_mat, &TagSet::empty(), cfg)?
            }
            ExecPlan::Crosstab { .. } => {
                return Err(OpErr::Failed(
                    "crosstab cannot appear as non-root table stage".to_string(),
                ));
            }
            _ => {
                return Err(OpErr::Failed(
                    "unexpected leaf stage in exec unary loop".to_string(),
                ));
            }
        };
    }

    Ok(cur)
}

fn exec_unary_input(plan: &ExecPlan) -> Option<&ExecPlan> {
    match plan {
        ExecPlan::Select { input, .. }
        | ExecPlan::Drop { input, .. }
        | ExecPlan::Rename { input, .. }
        | ExecPlan::Derive { input, .. }
        | ExecPlan::Filter { input, .. }
        | ExecPlan::Distinct { input, .. }
        | ExecPlan::Sort { input, .. }
        | ExecPlan::Limit { input, .. }
        | ExecPlan::GroupBy { input, .. }
        | ExecPlan::Summarize { input, .. }
        | ExecPlan::SuppressSmallGroups { input, .. }
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

// ===========================================================================
// Core IR v0.1 Vectorized VM (`run_core_program_vm` & `eval_core_plan_batches`)
// ===========================================================================

/// Direct columnar batch plan evaluator over a pre-loaded [`VmTable`] source (used by
/// benchmarks, streaming tests, and hybrid SQL pushdown local suffixes to run columnar
/// batches without row-by-row `TableVal` marshalling).
pub fn eval_core_plan_batches(
    prog: &Program,
    source_var_name: &str,
    source_table: VmTable,
    plan: &Plan,
    vm_cfg: &VmConfig,
) -> Result<VmTable, OpErr> {
    let empty_env = EnvList::empty();
    eval_core_plan_batches_with_env(
        prog,
        &empty_env,
        source_var_name,
        source_table,
        plan,
        vm_cfg,
    )
}

/// Direct columnar batch plan evaluator over a pre-loaded [`VmTable`] source with an explicit
/// outer lexical environment [`EnvList`] (supporting `RowExpr::OuterVar` inside hybrid local suffixes).
pub fn eval_core_plan_batches_with_env(
    prog: &Program,
    env: &EnvList,
    source_var_name: &str,
    source_table: VmTable,
    plan: &Plan,
    vm_cfg: &VmConfig,
) -> Result<VmTable, OpErr> {
    let owned_plan;
    let effective_plan = if vm_cfg.optimize {
        let (opt, _) = crate::plan::optimize_plan(plan, prog);
        owned_plan = opt;
        &owned_plan
    } else {
        plan
    };
    let op_cfg = OpExecConfig {
        batch_size: vm_cfg.batch_size,
        parallel_threshold_rows: vm_cfg.parallel_threshold_rows,
        max_threads: vm_cfg.max_threads,
        mode: VmMode::CoreV01,
        pseudonymize_mode: crate::runtime::ir::PseudonymizeMode::CoreV01Fnv1a,
    };
    let mut world = World::default();
    let mut source_slot = Some(source_table);
    eval_core_plan_direct(
        100_000,
        prog,
        env,
        &TagSet::empty(),
        &mut world,
        effective_plan,
        &op_cfg,
        source_var_name,
        &mut source_slot,
    )
}

#[expect(
    clippy::too_many_arguments,
    reason = "Direct columnar batch evaluator threading pre-loaded source table without row conversion"
)]
fn eval_core_plan_direct(
    fuel: usize,
    prog: &Program,
    env: &EnvList,
    pc: &TagSet,
    world: &mut World,
    plan: &Plan,
    cfg: &OpExecConfig,
    source_var: &str,
    source_slot: &mut Option<VmTable>,
) -> Result<VmTable, OpErr> {
    let row_host = CoreRowHost { prog, env, fuel };
    match plan {
        Plan::SourceExpr(e) => {
            if let Expr::Var(v) = e.as_ref()
                && v == source_var
                && let Some(tbl) = source_slot.take()
            {
                return Ok(tbl);
            }
            match eval_core_expr_vm(fuel, prog, env, pc, world, e, cfg) {
                VmStep::Ok(v) => {
                    let tv = v.into_table().ok_or(OpErr::Wrong)?;
                    Ok(VmTable::from_table_val(&tv, cfg.batch_size))
                }
                VmStep::Stopped(b) => Err(OpErr::Stopped(b)),
                VmStep::Failed(m) => Err(OpErr::Failed(m)),
                _ => Err(OpErr::Wrong),
            }
        }
        Plan::Select { input, cols } => {
            let t = eval_core_plan_direct(
                fuel,
                prog,
                env,
                pc,
                world,
                input,
                cfg,
                source_var,
                source_slot,
            )?;
            op_select(t, cols, cfg.mode)
        }
        Plan::Drop { input, cols } => {
            let t = eval_core_plan_direct(
                fuel,
                prog,
                env,
                pc,
                world,
                input,
                cfg,
                source_var,
                source_slot,
            )?;
            op_drop(t, cols, cfg.mode)
        }
        Plan::Rename { input, pairs } => {
            let t = eval_core_plan_direct(
                fuel,
                prog,
                env,
                pc,
                world,
                input,
                cfg,
                source_var,
                source_slot,
            )?;
            Ok(op_rename(t, pairs, cfg.mode))
        }
        Plan::Filter { input, pred } => {
            let t = eval_core_plan_direct(
                fuel,
                prog,
                env,
                pc,
                world,
                input,
                cfg,
                source_var,
                source_slot,
            )?;
            let rp = compile_core_row_expr(pred, prog);
            op_filter(t, &rp, &row_host, cfg)
        }
        Plan::Derive { input, items } => {
            let mut t = eval_core_plan_direct(
                fuel,
                prog,
                env,
                pc,
                world,
                input,
                cfg,
                source_var,
                source_slot,
            )?;
            for c in &mut t.cols {
                c.agg_kind = AggKind::Raw;
            }
            for b in &mut t.batches {
                b.group_meta = None;
                for c in &mut b.cols {
                    c.spec.agg_kind = AggKind::Raw;
                }
            }
            for item in items {
                let next_cols = apply_derive_item_arc(prog, env.as_arc_ty_env(), &t.cols, item)
                    .map_err(|_| OpErr::Wrong)?;
                match item {
                    DeriveItem::ColExpr { name, expr } => {
                        let target_spec = next_cols
                            .iter()
                            .find(|c| c.name == *name)
                            .cloned()
                            .ok_or(OpErr::Wrong)?;
                        let rp = compile_core_row_expr(expr, prog);
                        t = op_derive_col_expr(t, target_spec, &rp, &row_host, cfg)?;
                    }
                    DeriveItem::BucketCol {
                        name,
                        source,
                        cuts,
                        labels,
                    } => {
                        let target_spec = next_cols.iter().find(|c| c.name == *name).cloned();
                        t = op_derive_bucket(t, name, source, cuts, labels, target_spec, cfg)?;
                    }
                }
            }
            Ok(t)
        }
        Plan::GroupBy { input, keys } => {
            let t = eval_core_plan_direct(
                fuel,
                prog,
                env,
                pc,
                world,
                input,
                cfg,
                source_var,
                source_slot,
            )?;
            Ok(op_group_by(t, keys, cfg.mode))
        }
        Plan::Summarize {
            input,
            aggs,
            distinct_key,
        } => {
            let t = eval_core_plan_direct(
                fuel,
                prog,
                env,
                pc,
                world,
                input,
                cfg,
                source_var,
                source_slot,
            )?;
            let group_keys: Vec<Ident> = t
                .cols
                .iter()
                .filter(|c| c.agg_kind == AggKind::GroupKey)
                .map(|c| c.name.clone())
                .collect();
            let in_tt = TableTy {
                cols: t.cols.clone(),
                grouped_by: if group_keys.is_empty() {
                    None
                } else {
                    Some(group_keys.clone())
                },
                ..TableTy::default()
            };
            let mut out_cols: Vec<ColSpec> = t
                .cols
                .iter()
                .filter(|c| c.agg_kind == AggKind::GroupKey)
                .cloned()
                .collect();
            let mut compiled_aggs = Vec::with_capacity(aggs.len());
            for a in aggs {
                let spec = crate::core::check::check_agg_item(prog, &env.to_ty_env(), &in_tt, a)
                    .map_err(|_| OpErr::Wrong)?;
                out_cols.push(spec.clone());
                compiled_aggs.push(CompiledAgg {
                    name: a.name.clone(),
                    op: a.op,
                    out_spec: spec,
                    arg_prog: a.arg.as_ref().map(|re| compile_core_row_expr(re, prog)),
                });
            }
            op_hash_aggregate(
                t,
                &group_keys,
                &compiled_aggs,
                distinct_key.as_deref(),
                out_cols,
                &row_host,
                cfg,
            )
        }
        Plan::Sort { input, keys } => {
            let t = eval_core_plan_direct(
                fuel,
                prog,
                env,
                pc,
                world,
                input,
                cfg,
                source_var,
                source_slot,
            )?;
            Ok(op_sort(t, keys, cfg))
        }
        Plan::Limit { input, n } => {
            let t = eval_core_plan_direct(
                fuel,
                prog,
                env,
                pc,
                world,
                input,
                cfg,
                source_var,
                source_slot,
            )?;
            Ok(op_limit(t, n.to_usize_saturating(), cfg.mode))
        }
        Plan::Distinct { input, cols } => {
            let t = eval_core_plan_direct(
                fuel,
                prog,
                env,
                pc,
                world,
                input,
                cfg,
                source_var,
                source_slot,
            )?;
            op_distinct(t, cols, cfg)
        }
        Plan::SuppressSmallGroups {
            input,
            min_k,
            distinct_by,
            mode,
        } => {
            let t = eval_core_plan_direct(
                fuel,
                prog,
                env,
                pc,
                world,
                input,
                cfg,
                source_var,
                source_slot,
            )?;
            Ok(op_suppress_small_groups(
                t,
                min_k,
                distinct_by,
                *mode,
                pc,
                cfg,
            ))
        }
        Plan::Window { input, items } => {
            let t = eval_core_plan_direct(
                fuel,
                prog,
                env,
                pc,
                world,
                input,
                cfg,
                source_var,
                source_slot,
            )?;
            let mut out_cols: Vec<ColSpec> = t
                .cols
                .iter()
                .map(|c| ColSpec {
                    agg_kind: AggKind::Raw,
                    ..c.clone()
                })
                .collect();
            for item in items {
                out_cols = apply_window_item(&out_cols, &TagSet::empty(), item)
                    .map_err(|_| OpErr::Wrong)?;
            }
            op_window(t, items, Some(out_cols), cfg)
        }
        Plan::Redact {
            input,
            col,
            replacement,
        } => {
            let t = eval_core_plan_direct(
                fuel,
                prog,
                env,
                pc,
                world,
                input,
                cfg,
                source_var,
                source_slot,
            )?;
            op_redact(t, col, replacement, pc, cfg)
        }
        Plan::Join {
            kind,
            left,
            right,
            on,
            suffixes,
        } => {
            let lt = eval_core_plan_direct(
                fuel,
                prog,
                env,
                pc,
                world,
                left,
                cfg,
                source_var,
                source_slot,
            )?;
            let rt = eval_core_plan_direct(
                fuel,
                prog,
                env,
                pc,
                world,
                right,
                cfg,
                source_var,
                source_slot,
            )?;
            op_hash_join(*kind, &lt, &rt, on, suffixes, pc, cfg)
        }
        Plan::Union { left, right } => {
            let lt = eval_core_plan_direct(
                fuel,
                prog,
                env,
                pc,
                world,
                left,
                cfg,
                source_var,
                source_slot,
            )?;
            let rt = eval_core_plan_direct(
                fuel,
                prog,
                env,
                pc,
                world,
                right,
                cfg,
                source_var,
                source_slot,
            )?;
            op_union(lt, rt, cfg.mode)
        }
        other => match eval_core_plan_vm(fuel, prog, env, pc, world, other, cfg) {
            VmStep::Ok(v) => {
                let tv = v.into_table().ok_or(OpErr::Wrong)?;
                Ok(VmTable::from_table_val(&tv, cfg.batch_size))
            }
            VmStep::Stopped(b) => Err(OpErr::Stopped(b)),
            VmStep::Failed(m) => Err(OpErr::Failed(m)),
            _ => Err(OpErr::Wrong),
        },
    }
}

struct CoreRowHost<'a> {
    prog: &'a Program,
    env: &'a EnvList,
    fuel: usize,
}

impl RowEvalHost for CoreRowHost<'_> {
    fn lookup_outer(&self, name: &str) -> Option<Val> {
        self.env.lookup(name).map(|(_, v)| v.clone())
    }

    fn lookup_const(&self, name: &str) -> Option<Val> {
        self.prog.find_const(name).map(|c| eval_literal(&c.value))
    }

    fn call_pure_fallback(&self, fn_name: &str, args: Vec<Val>) -> Result<Val, RowEvalErr> {
        let Some(f_decl) = self.prog.find_fun(fn_name) else {
            return Err(RowEvalErr::Failed(format!("unknown pure fn `{fn_name}`")));
        };
        if args.len() != f_decl.params.len() {
            return Err(RowEvalErr::Failed("pure fn arity mismatch".to_string()));
        }
        let entries: Vec<EnvEntry> = f_decl
            .params
            .iter()
            .zip(args)
            .rev()
            .map(|((p, p_lty), v)| EnvEntry {
                name: p.clone(),
                lty: p_lty.clone(),
                val: v,
            })
            .collect();
        let call_env = EnvList::from_vec(entries);
        let mut isolated = World::default();
        let seq_cfg = OpExecConfig {
            batch_size: crate::vm::BATCH_SIZE,
            parallel_threshold_rows: usize::MAX,
            max_threads: Some(1),
            mode: VmMode::CoreV01,
            pseudonymize_mode: crate::runtime::ir::PseudonymizeMode::CoreV01Fnv1a,
        };
        match eval_core_expr_vm(
            self.fuel,
            self.prog,
            &call_env,
            &TagSet::empty(),
            &mut isolated,
            &f_decl.body,
            &seq_cfg,
        ) {
            VmStep::Ok(v) => Ok(v),
            VmStep::Stopped(bug) => Err(RowEvalErr::Stopped { lane: 0, bug }),
            VmStep::Failed(m) => Err(RowEvalErr::Stopped {
                lane: 0,
                bug: Bug {
                    kind: BugKind::PromiseViolation,
                    message: m,
                },
            }),
            VmStep::OutOfFuel => Err(RowEvalErr::Failed("out of fuel".to_string())),
            VmStep::Jumped(_, _) | VmStep::Wrong => {
                Err(RowEvalErr::Failed("wrong in pure call".to_string()))
            }
        }
    }
}

enum VmStep {
    Ok(Val),
    Stopped(Bug),
    Failed(String),
    Jumped(Ident, Vec<Val>),
    Wrong,
    OutOfFuel,
}

impl VmStep {
    fn from_op_err(e: OpErr) -> Self {
        match e {
            OpErr::Stopped(b) => Self::Stopped(b),
            OpErr::Failed(m) => Self::Failed(m),
            OpErr::Wrong => Self::Wrong,
        }
    }

    fn boxed_op_err(e: OpErr) -> Box<Self> {
        Box::new(Self::from_op_err(e))
    }

    fn into_outcome(self, world: World) -> Outcome {
        match self {
            Self::Ok(v) => Outcome::Ok(v, world),
            Self::Stopped(b) => Outcome::Stopped(b, world),
            Self::Failed(m) => Outcome::Failed(m, world),
            Self::Jumped(l, vs) => Outcome::Jumped(l, vs, world),
            Self::Wrong => Outcome::Wrong,
            Self::OutOfFuel => Outcome::OutOfFuel,
        }
    }
}

/// Type-check, optionally optimize, and execute a Core IR v0.1 [`Program`] on the
/// vectorized columnar VM, producing an [`ExecReport`] matching `src/oracle::run_program`
/// and Lean 4 `danacore` byte-for-byte!
pub fn run_core_program_vm(
    fuel: usize,
    prog: &Program,
    init_world: World,
    vm_cfg: &VmConfig,
) -> Result<ExecReport, RuntimeError> {
    with_large_stack(|| run_core_program_vm_inner(fuel, prog, init_world, vm_cfg))
}

fn run_core_program_vm_inner(
    fuel: usize,
    prog: &Program,
    mut init_world: World,
    vm_cfg: &VmConfig,
) -> Result<ExecReport, RuntimeError> {
    check_program(prog).map_err(|e| RuntimeError::new(e.message))?;
    let owned_opt;
    let active_prog = if vm_cfg.optimize {
        let (opt_p, _) = optimize_program(prog);
        owned_opt = opt_p;
        &owned_opt
    } else {
        prog
    };

    let Some(main_name) = &active_prog.entry else {
        return extract_report(Outcome::Ok(Val::Unit, init_world))
            .ok_or_else(|| RuntimeError::new("internal error extracting empty report"));
    };
    let Some(main_fn) = active_prog.find_fun(main_name) else {
        return Err(RuntimeError::new(format!("entry '{main_name}' not found")));
    };

    let mut init_env = EnvList::default();
    for (p_name, p_lty) in &main_fn.params {
        let Some(cap_val) = build_core_entry_cap(&p_lty.ty) else {
            return Err(RuntimeError::new("entry has non-capability parameters"));
        };
        init_env = EnvList::cons(
            EnvEntry {
                name: p_name.clone(),
                lty: p_lty.clone(),
                val: cap_val,
            },
            init_env,
        );
    }

    if let Some(bug) = check_core_entry_export_gate(&main_fn.params, &init_world) {
        return extract_report(Outcome::Stopped(bug, init_world))
            .ok_or_else(|| RuntimeError::new("unable to extract report"));
    }

    let op_cfg = OpExecConfig {
        batch_size: vm_cfg.batch_size,
        parallel_threshold_rows: vm_cfg.parallel_threshold_rows,
        max_threads: vm_cfg.max_threads,
        mode: VmMode::CoreV01,
        pseudonymize_mode: crate::runtime::ir::PseudonymizeMode::CoreV01Fnv1a,
    };
    let step = eval_core_expr_vm(
        fuel,
        active_prog,
        &init_env,
        &TagSet::empty(),
        &mut init_world,
        &main_fn.body,
        &op_cfg,
    );
    match step.into_outcome(init_world) {
        Outcome::OutOfFuel => Err(RuntimeError::new("execution exhausted fuel")),
        Outcome::Wrong => Err(RuntimeError::new(
            "internal soundness violation: stuck state",
        )),
        Outcome::Jumped(lbl, _, _) => Err(RuntimeError::new(format!(
            "internal soundness violation: uncaught jump '{lbl}'"
        ))),
        other => extract_report(other).ok_or_else(|| RuntimeError::new("unable to extract report")),
    }
}

fn eval_core_plan_vm(
    fuel: usize,
    prog: &Program,
    env: &EnvList,
    pc: &TagSet,
    world: &mut World,
    plan: &Plan,
    cfg: &OpExecConfig,
) -> VmStep {
    if let Plan::Crosstab {
        input,
        rows_col,
        cols_col,
        values_col,
        fill,
    } = plan
    {
        let Some(fuel_next) = fuel.checked_sub(1) else {
            return VmStep::OutOfFuel;
        };
        let tbl = match eval_core_plan_to_table(fuel_next, prog, env, pc, world, input, cfg) {
            Ok(t) => t,
            Err(step) => return *step,
        };
        return match op_crosstab(tbl, rows_col, cols_col, values_col, fill, cfg) {
            Ok(v) => VmStep::Ok(v),
            Err(e) => VmStep::from_op_err(e),
        };
    }
    match eval_core_plan_to_table(fuel, prog, env, pc, world, plan, cfg) {
        Ok(tbl) => VmStep::Ok(Val::Table(tbl.into_table_val())),
        Err(step) => *step,
    }
}

fn eval_core_plan_to_table(
    fuel: usize,
    prog: &Program,
    env: &EnvList,
    pc: &TagSet,
    world: &mut World,
    plan: &Plan,
    cfg: &OpExecConfig,
) -> Result<VmTable, Box<VmStep>> {
    let Some(fuel_next) = fuel.checked_sub(1) else {
        return Err(Box::new(VmStep::OutOfFuel));
    };
    let row_host = CoreRowHost {
        prog,
        env,
        fuel: fuel_next,
    };

    match plan {
        Plan::SourceExpr(e) => match eval_core_expr_vm(fuel_next, prog, env, pc, world, e, cfg) {
            VmStep::Ok(v) => {
                let tv = v.into_table().ok_or_else(|| Box::new(VmStep::Wrong))?;
                Ok(VmTable::from_table_val(&tv, cfg.batch_size))
            }
            other => Err(Box::new(other)),
        },
        Plan::SourceDB {
            cap,
            table_name,
            schema,
        } => {
            let cap_v = match eval_core_expr_vm(fuel_next, prog, env, pc, world, cap, cfg) {
                VmStep::Ok(v) => v,
                other => return Err(Box::new(other)),
            };
            let Val::CapReadDB { handle: h, ref db } = cap_v else {
                return Err(Box::new(VmStep::Wrong));
            };
            let stored: Option<&StoredTable> = match h {
                CapHandle::Real => world
                    .real_db_tables
                    .iter()
                    .find(|st| st.db == *db && st.table_name == *table_name),
                CapHandle::Fake(id) => world
                    .fake_dbs
                    .get(id)
                    .and_then(|fdb| fdb.tables.iter().find(|st| st.table_name == *table_name)),
            };
            let tv = match stored {
                Some(st) => {
                    let st_tys: Vec<&ScalarTy> = st.schema.cols.iter().map(|c| &c.ty).collect();
                    let decl_tys: Vec<&ScalarTy> = schema.cols.iter().map(|c| &c.ty).collect();
                    if st_tys == decl_tys {
                        let rows = st
                            .rows
                            .iter()
                            .map(|cs| TableRow {
                                cells: cs.clone(),
                                group_meta: None,
                            })
                            .collect();
                        TableVal {
                            cols: schema.cols.clone(),
                            rows,
                        }
                    } else {
                        return Err(Box::new(VmStep::Stopped(Bug {
                            kind: BugKind::SchemaConstraint,
                            message: format!("schema drift on table '{table_name}'"),
                        })));
                    }
                }
                None => TableVal {
                    cols: schema.cols.clone(),
                    rows: Vec::new(),
                },
            };
            Ok(VmTable::from_table_val(&tv, cfg.batch_size))
        }
        Plan::Select { input, cols } => {
            let t = eval_core_plan_to_table(fuel_next, prog, env, pc, world, input, cfg)?;
            op_select(t, cols, cfg.mode).map_err(VmStep::boxed_op_err)
        }
        Plan::Drop { input, cols } => {
            let t = eval_core_plan_to_table(fuel_next, prog, env, pc, world, input, cfg)?;
            op_drop(t, cols, cfg.mode).map_err(VmStep::boxed_op_err)
        }
        Plan::Rename { input, pairs } => {
            let t = eval_core_plan_to_table(fuel_next, prog, env, pc, world, input, cfg)?;
            Ok(op_rename(t, pairs, cfg.mode))
        }
        Plan::Derive { input, items } => {
            let mut t = eval_core_plan_to_table(fuel_next, prog, env, pc, world, input, cfg)?;
            for c in &mut t.cols {
                c.agg_kind = AggKind::Raw;
            }
            for b in &mut t.batches {
                b.group_meta = None;
                for c in &mut b.cols {
                    c.spec.agg_kind = AggKind::Raw;
                }
            }
            for item in items {
                let next_cols = apply_derive_item_arc(prog, env.as_arc_ty_env(), &t.cols, item)
                    .map_err(|_| Box::new(VmStep::Wrong))?;
                match item {
                    DeriveItem::ColExpr { name, expr } => {
                        let target_spec = next_cols
                            .iter()
                            .find(|c| c.name == *name)
                            .cloned()
                            .ok_or_else(|| Box::new(VmStep::Wrong))?;
                        let rp = compile_core_row_expr(expr, prog);
                        t = op_derive_col_expr(t, target_spec, &rp, &row_host, cfg)
                            .map_err(VmStep::boxed_op_err)?;
                    }
                    DeriveItem::BucketCol {
                        name,
                        source,
                        cuts,
                        labels,
                    } => {
                        let target_spec = next_cols.iter().find(|c| c.name == *name).cloned();
                        t = op_derive_bucket(t, name, source, cuts, labels, target_spec, cfg)
                            .map_err(VmStep::boxed_op_err)?;
                    }
                }
            }
            Ok(t)
        }
        Plan::Filter { input, pred } => {
            let t = eval_core_plan_to_table(fuel_next, prog, env, pc, world, input, cfg)?;
            let rp = compile_core_row_expr(pred, prog);
            op_filter(t, &rp, &row_host, cfg).map_err(VmStep::boxed_op_err)
        }
        Plan::Distinct { input, cols } => {
            let t = eval_core_plan_to_table(fuel_next, prog, env, pc, world, input, cfg)?;
            op_distinct(t, cols, cfg).map_err(VmStep::boxed_op_err)
        }
        Plan::Sort { input, keys } => {
            let t = eval_core_plan_to_table(fuel_next, prog, env, pc, world, input, cfg)?;
            Ok(op_sort(t, keys, cfg))
        }
        Plan::Limit { input, n } => {
            let t = eval_core_plan_to_table(fuel_next, prog, env, pc, world, input, cfg)?;
            Ok(op_limit(t, n.to_usize_saturating(), cfg.mode))
        }
        Plan::Join {
            kind,
            left,
            right,
            on,
            suffixes,
        } => {
            let lt = eval_core_plan_to_table(fuel_next, prog, env, pc, world, left, cfg)?;
            let rt = eval_core_plan_to_table(fuel_next, prog, env, pc, world, right, cfg)?;
            op_hash_join(*kind, &lt, &rt, on, suffixes, pc, cfg).map_err(VmStep::boxed_op_err)
        }
        Plan::Union { left, right } => {
            let lt = eval_core_plan_to_table(fuel_next, prog, env, pc, world, left, cfg)?;
            let rt = eval_core_plan_to_table(fuel_next, prog, env, pc, world, right, cfg)?;
            op_union(lt, rt, cfg.mode).map_err(VmStep::boxed_op_err)
        }
        Plan::GroupBy { input, keys } => {
            let t = eval_core_plan_to_table(fuel_next, prog, env, pc, world, input, cfg)?;
            Ok(op_group_by(t, keys, cfg.mode))
        }
        Plan::Summarize {
            input,
            aggs,
            distinct_key,
        } => {
            let Ok(PlanTy::Table(out_tt)) =
                check_plan_arc(prog, env.as_arc_ty_env(), pc, true, plan, false)
            else {
                return Err(Box::new(VmStep::Wrong));
            };
            let t = eval_core_plan_to_table(fuel_next, prog, env, pc, world, input, cfg)?;
            let group_keys: Vec<Ident> = t
                .cols
                .iter()
                .filter(|c| c.agg_kind == AggKind::GroupKey)
                .map(|c| c.name.clone())
                .collect();
            let key_cols_len = group_keys.len();
            let agg_start = key_cols_len.min(out_tt.cols.len());
            if out_tt.cols.len() - agg_start != aggs.len() {
                return Err(Box::new(VmStep::Wrong));
            }
            let agg_specs = &out_tt.cols[agg_start..];
            let compiled_aggs: Vec<CompiledAgg> = aggs
                .iter()
                .zip(agg_specs)
                .map(|(a, spec)| CompiledAgg {
                    name: a.name.clone(),
                    op: a.op,
                    out_spec: spec.clone(),
                    arg_prog: a.arg.as_ref().map(|re| compile_core_row_expr(re, prog)),
                })
                .collect();
            op_hash_aggregate(
                t,
                &group_keys,
                &compiled_aggs,
                distinct_key.as_deref(),
                out_tt.cols,
                &row_host,
                cfg,
            )
            .map_err(VmStep::boxed_op_err)
        }
        Plan::SuppressSmallGroups {
            input,
            min_k,
            distinct_by,
            mode,
        } => {
            let t = eval_core_plan_to_table(fuel_next, prog, env, pc, world, input, cfg)?;
            Ok(op_suppress_small_groups(
                t,
                min_k,
                distinct_by,
                *mode,
                pc,
                cfg,
            ))
        }
        Plan::Window { input, items } => {
            let Ok(PlanTy::Table(out_tt)) =
                check_plan_arc(prog, env.as_arc_ty_env(), pc, true, plan, false)
            else {
                return Err(Box::new(VmStep::Wrong));
            };
            let t = eval_core_plan_to_table(fuel_next, prog, env, pc, world, input, cfg)?;
            op_window(t, items, Some(out_tt.cols), cfg).map_err(VmStep::boxed_op_err)
        }
        Plan::FillGaps {
            input,
            col,
            step_micros,
            over,
            fill,
        } => {
            let Ok(PlanTy::Table(out_tt)) =
                check_plan_arc(prog, env.as_arc_ty_env(), pc, true, plan, false)
            else {
                return Err(Box::new(VmStep::Wrong));
            };
            let t = eval_core_plan_to_table(fuel_next, prog, env, pc, world, input, cfg)?;
            op_fill_gaps(t, col, step_micros, over, fill, Some(out_tt.cols), cfg)
                .map_err(VmStep::boxed_op_err)
        }
        Plan::PivotWider {
            input,
            names_from,
            values_from,
            static_cols,
            fill,
        } => {
            let Ok(PlanTy::Table(out_tt)) =
                check_plan_arc(prog, env.as_arc_ty_env(), pc, true, plan, false)
            else {
                return Err(Box::new(VmStep::Wrong));
            };
            let t = eval_core_plan_to_table(fuel_next, prog, env, pc, world, input, cfg)?;
            op_pivot_wider(
                t,
                names_from,
                values_from,
                static_cols,
                fill,
                Some(out_tt.cols),
                cfg,
            )
            .map_err(VmStep::boxed_op_err)
        }
        Plan::Redact {
            input,
            col,
            replacement,
        } => {
            let t = eval_core_plan_to_table(fuel_next, prog, env, pc, world, input, cfg)?;
            op_redact(t, col, replacement, pc, cfg).map_err(VmStep::boxed_op_err)
        }
        Plan::Pseudonymize { input, col, secret } => {
            let t = eval_core_plan_to_table(fuel_next, prog, env, pc, world, input, cfg)?;
            let sec_val = match eval_core_expr_vm(fuel_next, prog, env, pc, world, secret, cfg) {
                VmStep::Ok(v) => v,
                other => return Err(Box::new(other)),
            };
            let Val::CapSecret {
                handle: h,
                name: ref s_name,
            } = sec_val
            else {
                return Err(Box::new(VmStep::Wrong));
            };
            let key_mat = match h {
                CapHandle::Real => world
                    .real_secrets
                    .iter()
                    .find(|(n, _)| n == s_name)
                    .map_or_else(|| s_name.clone(), |(_, sv)| sv.clone()),
                CapHandle::Fake(id) => world
                    .fake_secrets
                    .get(id)
                    .cloned()
                    .unwrap_or_else(|| s_name.clone()),
            };
            op_pseudonymize(t, col, &key_mat, pc, cfg).map_err(VmStep::boxed_op_err)
        }
        Plan::Crosstab { .. } => Err(Box::new(VmStep::Wrong)),
    }
}

// ===========================================================================
// Stack-Safe Outer Core IR Evaluator (`eval_core_expr_vm`)
// ===========================================================================

fn eval_core_expr_vm(
    init_fuel: usize,
    prog: &Program,
    init_env: &EnvList,
    init_pc: &TagSet,
    world: &mut World,
    init_expr: &Expr,
    cfg: &OpExecConfig,
) -> VmStep {
    enum SeqKind<'a> {
        Prim(&'a PrimOp),
        Host(&'a HostOp),
        Tuple,
        Ctor(&'a Ident, &'a Ident),
        Jump(&'a Ident),
        Call(&'a Ident),
        App {
            params: Vec<(Ident, LTy)>,
            fn_pc: TagSet,
            body: Arc<Expr>,
            captured_env: EnvList,
        },
    }
    enum Frame<'a> {
        LetBound {
            fuel_next: usize,
            name: &'a Ident,
            decl_lty: &'a LTy,
            env: EnvList,
            pc: TagSet,
            body: &'a Expr,
        },
        IfCond {
            fuel_next: usize,
            env: EnvList,
            br_pc: TagSet,
            then_br: &'a Expr,
            else_br: &'a Expr,
        },
        CaseScrut {
            fuel_next: usize,
            env: EnvList,
            scrut_lty: LTy,
            arm_pc: TagSet,
            arms: &'a [CaseArm],
        },
        AppFn {
            fuel_next: usize,
            env: EnvList,
            pc: TagSet,
            args: &'a [Expr],
        },
        Seq {
            fuel_next: usize,
            env: EnvList,
            pc: TagSet,
            remaining: &'a [Expr],
            vals: Vec<Val>,
            kind: SeqKind<'a>,
        },
        CallBoundary,
        JoinCatch {
            fuel_next: usize,
            base_env: EnvList,
            label: &'a Ident,
            params: &'a [(Ident, LTy)],
            join_pc: TagSet,
            rhs: &'a Expr,
        },
        Proj {
            idx: &'a BigInt,
        },
        StopDetail {
            kind: BugKind,
            eff_tags: TagSet,
        },
        FailMsg,
    }

    let mut frames: Vec<Frame<'_>> = Vec::new();
    let mut cur_target: Option<(usize, EnvList, TagSet, &Expr)> =
        Some((init_fuel, init_env.clone(), init_pc.clone(), init_expr));
    let mut cur_step: Option<VmStep> = None;

    loop {
        if let Some((fuel, env, pc, expr)) = cur_target.take() {
            let Some(fuel_next) = fuel.checked_sub(1) else {
                return VmStep::OutOfFuel;
            };
            match expr {
                Expr::Lit(l) => cur_step = Some(VmStep::Ok(eval_literal(l))),
                Expr::Var(name) => {
                    cur_step = Some(match env.lookup(name) {
                        Some((_, v)) => VmStep::Ok(v.clone()),
                        None => VmStep::Wrong,
                    });
                }
                Expr::ConstRef(name) => {
                    cur_step = Some(match prog.find_const(name) {
                        Some(c) => VmStep::Ok(eval_literal(&c.value)),
                        None => VmStep::Wrong,
                    });
                }
                Expr::LetE {
                    name,
                    lty,
                    bound,
                    body,
                } => {
                    frames.push(Frame::LetBound {
                        fuel_next,
                        name,
                        decl_lty: lty,
                        env: env.clone(),
                        pc: pc.clone(),
                        body,
                    });
                    cur_target = Some((fuel_next, env, pc, bound));
                }
                Expr::IfE {
                    cond,
                    then_br,
                    else_br,
                } => {
                    let cond_tags =
                        check_expr_arc(prog, env.as_arc_ty_env(), &pc, true, cond, false)
                            .map(|c| c.tags)
                            .unwrap_or_default();
                    let br_pc = if cond_tags.is_empty() {
                        pc.clone()
                    } else {
                        pc.union(&cond_tags)
                    };
                    frames.push(Frame::IfCond {
                        fuel_next,
                        env: env.clone(),
                        br_pc,
                        then_br,
                        else_br,
                    });
                    cur_target = Some((fuel_next, env, pc, cond));
                }
                Expr::CaseE { scrut, arms } => {
                    let Ok(scrut_lty) =
                        check_expr_arc(prog, env.as_arc_ty_env(), &pc, true, scrut, false)
                    else {
                        return VmStep::Wrong;
                    };
                    let arm_pc = pc.union(&scrut_lty.effective_tags());
                    frames.push(Frame::CaseScrut {
                        fuel_next,
                        env: env.clone(),
                        scrut_lty,
                        arm_pc,
                        arms,
                    });
                    cur_target = Some((fuel_next, env, pc, scrut));
                }
                Expr::Lam {
                    params,
                    pc: fn_pc,
                    ret,
                    body,
                } => {
                    cur_step = Some(VmStep::Ok(Val::Closure(Box::new(ClosureVal {
                        params: params.clone(),
                        fn_pc: fn_pc.clone(),
                        ret_lty: ret.clone(),
                        body: Arc::clone(body),
                        captured_env: env,
                    }))));
                }
                Expr::App { fn_expr, args } => {
                    frames.push(Frame::AppFn {
                        fuel_next,
                        env: env.clone(),
                        pc: pc.clone(),
                        args,
                    });
                    cur_target = Some((fuel_next, env, pc, fn_expr));
                }
                Expr::Call { fn_name, args } => {
                    if let Some((first, rest)) = args.split_first() {
                        frames.push(Frame::Seq {
                            fuel_next,
                            env: env.clone(),
                            pc: pc.clone(),
                            remaining: rest,
                            vals: Vec::with_capacity(args.len()),
                            kind: SeqKind::Call(fn_name),
                        });
                        cur_target = Some((fuel_next, env, pc, first));
                    } else {
                        let Some(f) = prog.find_fun(fn_name) else {
                            return VmStep::Wrong;
                        };
                        if !f.params.is_empty() {
                            return VmStep::Wrong;
                        }
                        if !matches!(frames.last(), Some(Frame::CallBoundary)) {
                            frames.push(Frame::CallBoundary);
                        }
                        cur_target = Some((fuel_next, EnvList::empty(), f.pc.clone(), &f.body));
                    }
                }
                Expr::Join {
                    label,
                    params,
                    rhs,
                    body,
                } => {
                    let t_env = env.as_arc_ty_env();
                    let g1 = pc.union(&infer_jump_pc_arc(prog, label, t_env, &pc, body));
                    let rhs_env = t_env.extend_slice(params);
                    let join_pc = g1.union(&infer_jump_pc_arc(prog, label, &rhs_env, &g1, rhs));
                    frames.push(Frame::JoinCatch {
                        fuel_next,
                        base_env: env.clone(),
                        label,
                        params,
                        join_pc,
                        rhs,
                    });
                    cur_target = Some((fuel_next, env, pc, body));
                }
                Expr::Jump { label, args } => {
                    if let Some((first, rest)) = args.split_first() {
                        frames.push(Frame::Seq {
                            fuel_next,
                            env: env.clone(),
                            pc: pc.clone(),
                            remaining: rest,
                            vals: Vec::with_capacity(args.len()),
                            kind: SeqKind::Jump(label),
                        });
                        cur_target = Some((fuel_next, env, pc, first));
                    } else {
                        cur_step = Some(VmStep::Jumped(label.clone(), Vec::new()));
                    }
                }
                Expr::Tuple(elems) => {
                    if let Some((first, rest)) = elems.split_first() {
                        frames.push(Frame::Seq {
                            fuel_next,
                            env: env.clone(),
                            pc: pc.clone(),
                            remaining: rest,
                            vals: Vec::with_capacity(elems.len()),
                            kind: SeqKind::Tuple,
                        });
                        cur_target = Some((fuel_next, env, pc, first));
                    } else {
                        cur_step = Some(VmStep::Ok(Val::Tuple(Vec::new())));
                    }
                }
                Expr::Proj { tup, idx } => {
                    frames.push(Frame::Proj { idx });
                    cur_target = Some((fuel_next, env, pc, tup));
                }
                Expr::Ctor {
                    type_name,
                    ctor_name,
                    args,
                } => {
                    if let Some((first, rest)) = args.split_first() {
                        frames.push(Frame::Seq {
                            fuel_next,
                            env: env.clone(),
                            pc: pc.clone(),
                            remaining: rest,
                            vals: Vec::with_capacity(args.len()),
                            kind: SeqKind::Ctor(type_name, ctor_name),
                        });
                        cur_target = Some((fuel_next, env, pc, first));
                    } else {
                        cur_step = Some(VmStep::Ok(Val::Ctor {
                            type_name: type_name.clone(),
                            ctor_name: ctor_name.clone(),
                            fields: Vec::new(),
                        }));
                    }
                }
                Expr::TableLit { schema, rows } => {
                    let tv_rows = rows
                        .iter()
                        .map(|rl| TableRow {
                            cells: rl.cells.iter().map(eval_literal).collect(),
                            group_meta: None,
                        })
                        .collect();
                    cur_step = Some(VmStep::Ok(Val::Table(TableVal {
                        cols: schema.cols.clone(),
                        rows: tv_rows,
                    })));
                }
                Expr::Prim { op, args } => {
                    if let Some((first, rest)) = args.split_first() {
                        frames.push(Frame::Seq {
                            fuel_next,
                            env: env.clone(),
                            pc: pc.clone(),
                            remaining: rest,
                            vals: Vec::with_capacity(args.len()),
                            kind: SeqKind::Prim(op),
                        });
                        cur_target = Some((fuel_next, env, pc, first));
                    } else {
                        cur_step = Some(prim_to_vm_step(eval_prim_op(op, &[])));
                    }
                }
                Expr::Rel(plan) => {
                    cur_step = Some(eval_core_plan_vm(
                        fuel_next, prog, &env, &pc, world, plan, cfg,
                    ));
                }
                Expr::Host { op, args } => {
                    if let Some((first, rest)) = args.split_first() {
                        frames.push(Frame::Seq {
                            fuel_next,
                            env: env.clone(),
                            pc: pc.clone(),
                            remaining: rest,
                            vals: Vec::with_capacity(args.len()),
                            kind: SeqKind::Host(op),
                        });
                        cur_target = Some((fuel_next, env, pc, first));
                    } else {
                        cur_step = Some(eval_core_host_vm(prog, op, &[], world));
                    }
                }
                Expr::Stop { kind, detail } => match detail {
                    None => {
                        cur_step = Some(VmStep::Stopped(Bug {
                            kind: *kind,
                            message: repr_bug_kind(*kind).to_string(),
                        }));
                    }
                    Some(d_expr) => {
                        let Ok(d_lty) =
                            check_expr_arc(prog, env.as_arc_ty_env(), &pc, true, d_expr, false)
                        else {
                            return VmStep::Wrong;
                        };
                        let eff_tags = d_lty.effective_tags().union(&pc);
                        frames.push(Frame::StopDetail {
                            kind: *kind,
                            eff_tags,
                        });
                        cur_target = Some((fuel_next, env, pc, d_expr));
                    }
                },
                Expr::Fail(msg_expr) => {
                    frames.push(Frame::FailMsg);
                    cur_target = Some((fuel_next, env, pc, msg_expr));
                }
            }
            continue;
        }

        let Some(step) = cur_step.take() else {
            return VmStep::Wrong;
        };
        match step {
            VmStep::Stopped(_) | VmStep::Failed(_) | VmStep::Wrong | VmStep::OutOfFuel => {
                return step;
            }
            VmStep::Jumped(lbl, mut j_vals) => {
                let mut caught = false;
                while let Some(frame) = frames.pop() {
                    match frame {
                        Frame::CallBoundary => return VmStep::Wrong,
                        Frame::JoinCatch {
                            fuel_next,
                            base_env,
                            label,
                            params,
                            join_pc,
                            rhs,
                        } if lbl == *label => {
                            if j_vals.len() != params.len() {
                                return VmStep::Wrong;
                            }
                            let Some(loop_fuel) = fuel_next.checked_sub(1) else {
                                return VmStep::OutOfFuel;
                            };
                            let entries: Vec<EnvEntry> = params
                                .iter()
                                .zip(std::mem::take(&mut j_vals))
                                .map(|((p, l), v)| EnvEntry {
                                    name: p.clone(),
                                    lty: l.clone(),
                                    val: v,
                                })
                                .collect();
                            let next_env = base_env.prepend_entries(entries);
                            frames.push(Frame::JoinCatch {
                                fuel_next: loop_fuel,
                                base_env,
                                label,
                                params,
                                join_pc: join_pc.clone(),
                                rhs,
                            });
                            cur_target = Some((loop_fuel, next_env, join_pc, rhs));
                            caught = true;
                            break;
                        }
                        _ => {}
                    }
                }
                if !caught {
                    return VmStep::Jumped(lbl, j_vals);
                }
            }
            VmStep::Ok(v) => {
                let Some(frame) = frames.pop() else {
                    return VmStep::Ok(v);
                };
                match frame {
                    Frame::CallBoundary | Frame::JoinCatch { .. } => {
                        cur_step = Some(VmStep::Ok(v));
                    }
                    Frame::LetBound {
                        fuel_next,
                        name,
                        decl_lty,
                        env,
                        pc,
                        body,
                    } => {
                        let next_env = EnvList::cons(
                            EnvEntry {
                                name: name.clone(),
                                lty: decl_lty.add_tags(&pc),
                                val: v,
                            },
                            env,
                        );
                        cur_target = Some((fuel_next, next_env, pc, body));
                    }
                    Frame::IfCond {
                        fuel_next,
                        env,
                        br_pc,
                        then_br,
                        else_br,
                    } => match v {
                        Val::Bool(true) => cur_target = Some((fuel_next, env, br_pc, then_br)),
                        Val::Bool(false) => cur_target = Some((fuel_next, env, br_pc, else_br)),
                        _ => return VmStep::Wrong,
                    },
                    Frame::CaseScrut {
                        fuel_next,
                        env,
                        scrut_lty,
                        arm_pc,
                        arms,
                    } => {
                        let Some((c_name, typed_vals)) =
                            match_core_case_val(prog, &v, &scrut_lty, &arm_pc)
                        else {
                            return VmStep::Wrong;
                        };
                        let Some(arm) = arms.iter().find(|a| a.ctor == c_name) else {
                            return VmStep::Wrong;
                        };
                        if arm.binders.len() != typed_vals.len() {
                            return VmStep::Wrong;
                        }
                        let entries: Vec<EnvEntry> = arm
                            .binders
                            .iter()
                            .zip(typed_vals)
                            .map(|(b_name, (b_lty, b_val))| EnvEntry {
                                name: b_name.clone(),
                                lty: b_lty,
                                val: b_val,
                            })
                            .collect();
                        let next_env = env.prepend_entries(entries);
                        cur_target = Some((fuel_next, next_env, arm_pc, &arm.body));
                    }
                    Frame::AppFn {
                        fuel_next,
                        env,
                        pc,
                        args,
                    } => {
                        let mut fn_val = v;
                        let Val::Closure(cl) = &mut fn_val else {
                            return VmStep::Wrong;
                        };
                        let kind = SeqKind::App {
                            params: std::mem::take(&mut cl.params),
                            fn_pc: std::mem::take(&mut cl.fn_pc),
                            body: Arc::clone(&cl.body),
                            captured_env: std::mem::take(&mut cl.captured_env),
                        };
                        if let Some((first, rest)) = args.split_first() {
                            frames.push(Frame::Seq {
                                fuel_next,
                                env: env.clone(),
                                pc: pc.clone(),
                                remaining: rest,
                                vals: Vec::with_capacity(args.len()),
                                kind,
                            });
                            cur_target = Some((fuel_next, env, pc, first));
                        } else if let SeqKind::App {
                            params,
                            fn_pc,
                            body,
                            captured_env,
                        } = kind
                        {
                            if !params.is_empty() {
                                return VmStep::Wrong;
                            }
                            let res = match eval_core_expr_vm(
                                fuel_next,
                                prog,
                                &captured_env,
                                &fn_pc,
                                world,
                                &body,
                                cfg,
                            ) {
                                VmStep::Jumped(_, _) => VmStep::Wrong,
                                other => other,
                            };
                            cur_step = Some(res);
                        }
                    }
                    Frame::Seq {
                        fuel_next,
                        env,
                        pc,
                        remaining,
                        mut vals,
                        kind,
                    } => {
                        vals.push(v);
                        if let Some((next_e, rest)) = remaining.split_first() {
                            frames.push(Frame::Seq {
                                fuel_next,
                                env: env.clone(),
                                pc: pc.clone(),
                                remaining: rest,
                                vals,
                                kind,
                            });
                            cur_target = Some((fuel_next, env, pc, next_e));
                        } else {
                            match kind {
                                SeqKind::Prim(op) => {
                                    cur_step = Some(prim_to_vm_step(eval_prim_op(op, &vals)));
                                }
                                SeqKind::Host(op) => {
                                    cur_step = Some(eval_core_host_vm(prog, op, &vals, world));
                                }
                                SeqKind::Tuple => cur_step = Some(VmStep::Ok(Val::Tuple(vals))),
                                SeqKind::Ctor(tn, cn) => {
                                    cur_step = Some(VmStep::Ok(Val::Ctor {
                                        type_name: tn.clone(),
                                        ctor_name: cn.clone(),
                                        fields: vals,
                                    }));
                                }
                                SeqKind::Jump(lbl) => {
                                    cur_step = Some(VmStep::Jumped(lbl.clone(), vals));
                                }
                                SeqKind::Call(fn_name) => {
                                    let Some(f) = prog.find_fun(fn_name) else {
                                        return VmStep::Wrong;
                                    };
                                    if vals.len() != f.params.len() {
                                        return VmStep::Wrong;
                                    }
                                    let entries: Vec<EnvEntry> = f
                                        .params
                                        .iter()
                                        .zip(vals)
                                        .rev()
                                        .map(|((p, l), av)| EnvEntry {
                                            name: p.clone(),
                                            lty: l.clone(),
                                            val: av,
                                        })
                                        .collect();
                                    let call_env = EnvList::from_vec(entries);
                                    if !matches!(frames.last(), Some(Frame::CallBoundary)) {
                                        frames.push(Frame::CallBoundary);
                                    }
                                    cur_target = Some((fuel_next, call_env, f.pc.clone(), &f.body));
                                }
                                SeqKind::App {
                                    params,
                                    fn_pc,
                                    body,
                                    captured_env,
                                } => {
                                    if vals.len() != params.len() {
                                        return VmStep::Wrong;
                                    }
                                    let entries: Vec<EnvEntry> = params
                                        .into_iter()
                                        .zip(vals)
                                        .map(|((p, l), av)| EnvEntry {
                                            name: p,
                                            lty: l,
                                            val: av,
                                        })
                                        .collect();
                                    let call_env = captured_env.prepend_entries(entries);
                                    let res = match eval_core_expr_vm(
                                        fuel_next, prog, &call_env, &fn_pc, world, &body, cfg,
                                    ) {
                                        VmStep::Jumped(_, _) => VmStep::Wrong,
                                        other => other,
                                    };
                                    cur_step = Some(res);
                                }
                            }
                        }
                    }
                    Frame::Proj { idx } => match v {
                        Val::Tuple(ref vs) => match idx.to_usize().and_then(|i| vs.get(i)) {
                            Some(item) => cur_step = Some(VmStep::Ok(item.clone())),
                            None => return VmStep::Wrong,
                        },
                        _ => return VmStep::Wrong,
                    },
                    Frame::StopDetail { kind, eff_tags } => {
                        let msg = format!(
                            "{}: {}",
                            repr_bug_kind(kind),
                            format_diag_detail(&eff_tags, &v)
                        );
                        return VmStep::Stopped(Bug { kind, message: msg });
                    }
                    Frame::FailMsg => {
                        let mut v = v;
                        match &mut v {
                            Val::Text(s) => return VmStep::Failed(std::mem::take(s)),
                            _ => return VmStep::Wrong,
                        }
                    }
                }
            }
        }
    }
}

fn prim_to_vm_step(res: PrimResult) -> VmStep {
    match res {
        PrimResult::Ok(v) => VmStep::Ok(v),
        PrimResult::Stopped(b) => VmStep::Stopped(b),
        PrimResult::OutOfFuel => VmStep::OutOfFuel,
        PrimResult::Wrong => VmStep::Wrong,
    }
}

fn match_core_case_val(
    prog: &Program,
    scrut_val: &Val,
    scrut_lty: &LTy,
    arm_pc: &TagSet,
) -> Option<(Ident, Vec<(LTy, Val)>)> {
    let s_tags = scrut_lty.effective_tags().union(arm_pc);
    match (&scrut_lty.ty, scrut_val) {
        (Ty::Bool, Val::Bool(true)) => Some(("true".to_string(), Vec::new())),
        (Ty::Bool, Val::Bool(false)) => Some(("false".to_string(), Vec::new())),
        (Ty::Option(_), Val::OptNone) => Some(("None".to_string(), Vec::new())),
        (Ty::Option(inner), Val::OptSome(u)) => Some((
            "Some".to_string(),
            vec![(LTy::new(inner.as_ref().clone(), s_tags), u.as_ref().clone())],
        )),
        (Ty::Result { ok_ty, .. }, Val::ResOk(u)) => Some((
            "Ok".to_string(),
            vec![(LTy::new(ok_ty.as_ref().clone(), s_tags), u.as_ref().clone())],
        )),
        (Ty::Result { err_ty, .. }, Val::ResErr(e)) => Some((
            "Error".to_string(),
            vec![(
                LTy::new(err_ty.as_ref().clone(), s_tags),
                e.as_ref().clone(),
            )],
        )),
        (
            Ty::Data(d_name),
            Val::Ctor {
                type_name,
                ctor_name,
                fields,
            },
        ) => {
            if d_name != type_name {
                return None;
            }
            let d_decl = prog.find_data(d_name)?;
            let c_decl = d_decl.ctors.iter().find(|c| c.name == *ctor_name)?;
            if fields.len() == c_decl.fields.len() {
                let bound = c_decl
                    .fields
                    .iter()
                    .map(|f| f.add_tags(&s_tags))
                    .zip(fields.iter().cloned())
                    .collect();
                Some((ctor_name.clone(), bound))
            } else {
                None
            }
        }
        _ => None,
    }
}

fn check_core_export_gate(h: CapHandle, allows: &TagSet, w: &World) -> Option<Bug> {
    match h {
        CapHandle::Fake(_) => None,
        CapHandle::Real => {
            if allows.is_empty() || allows.is_subset(&w.runtime_allow_export) {
                None
            } else {
                Some(Bug {
                    kind: BugKind::ExportGateDenied,
                    message:
                        "runtime --allow-export authorization required for sensitive external sink"
                            .to_string(),
                })
            }
        }
    }
}

fn render_core_table_text(tv: &TableVal) -> String {
    let hdr = tv
        .cols
        .iter()
        .map(|c| c.name.as_str())
        .collect::<Vec<_>>()
        .join(" | ");
    let mut lines = Vec::with_capacity(tv.rows.len() + 1);
    lines.push(hdr);
    for r in &tv.rows {
        let cells: Vec<String> = r.cells.iter().map(render_public_val).collect();
        lines.push(cells.join(" | "));
    }
    lines.join("\n")
}

fn render_core_report_html(rv: &ReportVal) -> String {
    format!(
        "<html><h1>{}</h1><p>{}</p><!-- charts:{} tables:{} --></html>",
        rv.title,
        rv.summaries.join("</p><p>"),
        rv.charts.len(),
        rv.tables.len()
    )
}

fn eval_core_host_vm(prog: &Program, op: &HostOp, args: &[Val], w: &mut World) -> VmStep {
    match (op, args) {
        (HostOp::ArgsGet, [Val::CapArgs]) => {
            VmStep::Ok(Val::List(w.args.iter().cloned().map(Val::Text).collect()))
        }
        (HostOp::ClockNow, [Val::CapClock]) => VmStep::Ok(Val::Timestamp(w.clock_micros.clone())),
        (HostOp::ConsolePrint, [Val::CapConsole { handle: h, allows }, Val::Text(msg)]) => {
            if let Some(bug) = check_core_export_gate(*h, allows, w) {
                return VmStep::Stopped(bug);
            }
            match *h {
                CapHandle::Real => w.stdout.push(msg.clone()),
                CapHandle::Fake(id) => {
                    if let Some(fc) = w.fake_consoles.get_mut(id) {
                        fc.stdout.push(msg.clone());
                    }
                }
            }
            VmStep::Ok(Val::Unit)
        }
        (HostOp::ConsoleError, [Val::CapConsole { handle: h, allows }, Val::Text(msg)]) => {
            if let Some(bug) = check_core_export_gate(*h, allows, w) {
                return VmStep::Stopped(bug);
            }
            match *h {
                CapHandle::Real => w.stderr.push(msg.clone()),
                CapHandle::Fake(id) => {
                    if let Some(fc) = w.fake_consoles.get_mut(id) {
                        fc.stderr.push(msg.clone());
                    }
                }
            }
            VmStep::Ok(Val::Unit)
        }
        (HostOp::ConsolePrintTable, [Val::CapConsole { handle: h, allows }, Val::Table(tv)]) => {
            if let Some(bug) = check_core_export_gate(*h, allows, w) {
                return VmStep::Stopped(bug);
            }
            let line = render_core_table_text(tv);
            match *h {
                CapHandle::Real => w.stdout.push(line),
                CapHandle::Fake(id) => {
                    if let Some(fc) = w.fake_consoles.get_mut(id) {
                        fc.stdout.push(line);
                    }
                }
            }
            VmStep::Ok(Val::Unit)
        }
        (HostOp::ReadCsv(schema_name), [Val::CapReadFiles(_), Val::Text(path)]) => {
            let Some(s_decl) = prog.find_schema(schema_name) else {
                return VmStep::Wrong;
            };
            let bad_tt = quarantine_bad_row_table_ty(&s_decl.schema);
            match w.real_csv_fixtures.iter().find(|(p, _, _)| p == path) {
                Some((_, good_tv, bad_tv)) => {
                    let good_tys: Vec<&ScalarTy> = good_tv.cols.iter().map(|c| &c.ty).collect();
                    let decl_tys: Vec<&ScalarTy> =
                        s_decl.schema.cols.iter().map(|c| &c.ty).collect();
                    let bad_tys: Vec<&ScalarTy> = bad_tv.cols.iter().map(|c| &c.ty).collect();
                    let decl_bad_tys: Vec<&ScalarTy> = bad_tt.cols.iter().map(|c| &c.ty).collect();
                    if good_tys == decl_tys && bad_tys == decl_bad_tys {
                        let g_tv = TableVal {
                            cols: s_decl.schema.cols.clone(),
                            rows: good_tv.rows.clone(),
                        };
                        let b_tv = TableVal {
                            cols: bad_tt.cols,
                            rows: bad_tv.rows.clone(),
                        };
                        VmStep::Ok(Val::ResOk(Box::new(Val::Tuple(vec![
                            Val::Table(g_tv),
                            Val::Table(b_tv),
                        ]))))
                    } else {
                        VmStep::Ok(Val::ResErr(Box::new(Val::Text(format!(
                            "CSV fixture schema mismatch at '{path}'"
                        )))))
                    }
                }
                None => VmStep::Ok(Val::ResOk(Box::new(Val::Tuple(vec![
                    Val::Table(TableVal {
                        cols: s_decl.schema.cols.clone(),
                        rows: Vec::new(),
                    }),
                    Val::Table(TableVal {
                        cols: bad_tt.cols,
                        rows: Vec::new(),
                    }),
                ])))),
            }
        }
        (
            HostOp::WriteFile,
            [
                Val::CapWriteFiles {
                    handle: h,
                    root,
                    allows,
                },
                Val::Text(rel_path),
                Val::Text(content),
            ],
        ) => {
            if let Some(bug) = check_core_export_gate(*h, allows, w) {
                return VmStep::Stopped(bug);
            }
            if !is_safe_relative_path(rel_path) {
                return VmStep::Ok(Val::ResErr(Box::new(Val::Text(format!(
                    "invalid relative export path '{rel_path}'"
                )))));
            }
            let full_path = join_confined_path(root, rel_path);
            match *h {
                CapHandle::Real => w.written_files.push((full_path, content.clone())),
                CapHandle::Fake(id) => {
                    if let Some(ff) = w.fake_files.get_mut(id) {
                        ff.files.push((full_path, content.clone()));
                    }
                }
            }
            VmStep::Ok(Val::ResOk(Box::new(Val::Unit)))
        }
        (
            HostOp::WriteReportHtml,
            [
                Val::CapWriteFiles {
                    handle: h,
                    root,
                    allows,
                },
                Val::Text(rel_path),
                Val::Report(rv),
            ],
        ) => {
            if let Some(bug) = check_core_export_gate(*h, allows, w) {
                return VmStep::Stopped(bug);
            }
            if !is_safe_relative_path(rel_path) {
                return VmStep::Ok(Val::ResErr(Box::new(Val::Text(format!(
                    "invalid relative export path '{rel_path}'"
                )))));
            }
            let full_path = join_confined_path(root, rel_path);
            let html = render_core_report_html(rv);
            match *h {
                CapHandle::Real => w.written_files.push((full_path, html)),
                CapHandle::Fake(id) => {
                    if let Some(ff) = w.fake_files.get_mut(id) {
                        ff.files.push((full_path, html));
                    }
                }
            }
            VmStep::Ok(Val::ResOk(Box::new(Val::Unit)))
        }
        (
            HostOp::WriteTable,
            [
                Val::CapWriteTable {
                    handle: h,
                    db,
                    table_name: tbl,
                },
                Val::Table(src_tv),
            ],
        ) => {
            let col_names: Vec<Ident> = src_tv.cols.iter().map(|c| c.name.clone()).collect();
            let raw_rows: Vec<Vec<Val>> = src_tv.rows.iter().map(|r| r.cells.clone()).collect();
            let cnt = BigInt::from(raw_rows.len());
            if !cnt.in_int64_range() {
                return VmStep::Stopped(Bug {
                    kind: BugKind::IntOverflow,
                    message: "Int64 arithmetic overflow".to_string(),
                });
            }
            if matches!(*h, CapHandle::Real) {
                w.written_tables
                    .push((db.clone(), tbl.clone(), col_names, raw_rows));
            }
            VmStep::Ok(Val::ResOk(Box::new(Val::Int(cnt))))
        }
        (HostOp::DeclassifyApprove(_), [Val::CapDeclassify(_), v, Val::Text(_)]) => {
            VmStep::Ok(v.clone())
        }
        (HostOp::RawSqlQuery { .. }, [Val::CapRawReadDB(_), Val::Text(_)]) => {
            VmStep::Stopped(Bug {
                kind: BugKind::OutsideBoundary,
                message: "outside boundary: live SQL wire query".to_string(),
            })
        }
        (
            HostOp::HttpsGetJson,
            [
                Val::CapHttpsAllow {
                    handle: h, allows, ..
                },
                Val::Text(url),
            ],
        ) => match *h {
            CapHandle::Real => VmStep::Stopped(Bug {
                kind: BugKind::OutsideBoundary,
                message: "outside boundary: live HTTPS socket".to_string(),
            }),
            CapHandle::Fake(id) => {
                if let Some(bug) = check_core_export_gate(*h, allows, w) {
                    return VmStep::Stopped(bug);
                }
                if let Some(fh) = w.fake_https.get_mut(id) {
                    fh.requests.push(url.clone());
                    let found = fh
                        .responses
                        .iter()
                        .find(|(u, _)| u == url)
                        .map(|(_, body)| body.clone());
                    match found {
                        Some(body) => VmStep::Ok(Val::ResOk(Box::new(Val::Text(body)))),
                        None => VmStep::Ok(Val::ResErr(Box::new(Val::Text(
                            "404 Not Found".to_string(),
                        )))),
                    }
                } else {
                    VmStep::Ok(Val::ResErr(Box::new(Val::Text(
                        "invalid fake https handle".to_string(),
                    ))))
                }
            }
        },
        (HostOp::ReadParquet(_), [Val::CapReadFiles(h), Val::Text(_)]) => match *h {
            CapHandle::Real => VmStep::Stopped(Bug {
                kind: BugKind::OutsideBoundary,
                message: "outside boundary: binary Parquet decoder".to_string(),
            }),
            CapHandle::Fake(_) => VmStep::Ok(Val::ResErr(Box::new(Val::Text(
                "in-memory Parquet fixture not found".to_string(),
            )))),
        },
        (
            HostOp::WriteParquet | HostOp::WriteXlsx,
            [
                Val::CapWriteFiles {
                    handle: h,
                    root,
                    allows,
                },
                Val::Text(rel_path),
                Val::Table(src_tv),
            ],
        ) => {
            if let Some(bug) = check_core_export_gate(*h, allows, w) {
                return VmStep::Stopped(bug);
            }
            if !is_safe_relative_path(rel_path) {
                return VmStep::Ok(Val::ResErr(Box::new(Val::Text(format!(
                    "invalid relative export path '{rel_path}'"
                )))));
            }
            match *h {
                CapHandle::Real => VmStep::Stopped(Bug {
                    kind: BugKind::OutsideBoundary,
                    message: if matches!(op, HostOp::WriteParquet) {
                        "outside boundary: binary Parquet encoder".to_string()
                    } else {
                        "outside boundary: binary XLSX encoder".to_string()
                    },
                }),
                CapHandle::Fake(id) => {
                    let full_path = join_confined_path(root, rel_path);
                    let repr_content = render_core_table_text(src_tv);
                    if let Some(ff) = w.fake_files.get_mut(id) {
                        ff.files.push((full_path, repr_content));
                    }
                    VmStep::Ok(Val::ResOk(Box::new(Val::Unit)))
                }
            }
        }
        (HostOp::FakeConsole(allows), []) => {
            let id = w.fake_consoles.len();
            w.fake_consoles.push(FakeConsoleState::default());
            VmStep::Ok(Val::CapConsole {
                handle: CapHandle::Fake(id),
                allows: allows.clone(),
            })
        }
        (HostOp::FakeFiles(allows), []) => {
            let id = w.fake_files.len();
            w.fake_files.push(FakeFilesState::default());
            VmStep::Ok(Val::CapWriteFiles {
                handle: CapHandle::Fake(id),
                root: "mem://".to_string(),
                allows: allows.clone(),
            })
        }
        (HostOp::FakeDB(db), []) => {
            let id = w.fake_dbs.len();
            w.fake_dbs.push(FakeDBState {
                db: db.clone(),
                tables: Vec::new(),
            });
            VmStep::Ok(Val::CapReadDB {
                handle: CapHandle::Fake(id),
                db: db.clone(),
            })
        }
        (HostOp::FakeHttps { host, allows }, []) => {
            let id = w.fake_https.len();
            w.fake_https.push(FakeHttpsState {
                host: host.clone(),
                responses: Vec::new(),
                requests: Vec::new(),
            });
            VmStep::Ok(Val::CapHttpsAllow {
                handle: CapHandle::Fake(id),
                host: host.clone(),
                allows: allows.clone(),
            })
        }
        (HostOp::FakeSecret(name), [Val::Text(secret_val)]) => {
            let id = w.fake_secrets.len();
            w.fake_secrets.push(secret_val.clone());
            VmStep::Ok(Val::CapSecret {
                handle: CapHandle::Fake(id),
                name: name.clone(),
            })
        }
        _ => VmStep::Wrong,
    }
}

fn build_core_entry_cap(ty: &Ty) -> Option<Val> {
    match ty {
        Ty::Args => Some(Val::CapArgs),
        Ty::Clock => Some(Val::CapClock),
        Ty::Console(allows) => Some(Val::CapConsole {
            handle: CapHandle::Real,
            allows: allows.clone(),
        }),
        Ty::ReadFiles => Some(Val::CapReadFiles(CapHandle::Real)),
        Ty::WriteFiles { root, allows } => Some(Val::CapWriteFiles {
            handle: CapHandle::Real,
            root: root.clone(),
            allows: allows.clone(),
        }),
        Ty::ReadDB(db) => Some(Val::CapReadDB {
            handle: CapHandle::Real,
            db: db.clone(),
        }),
        Ty::WriteTable { db, table_name, .. } => Some(Val::CapWriteTable {
            handle: CapHandle::Real,
            db: db.clone(),
            table_name: table_name.clone(),
        }),
        Ty::RawReadDB(db) => Some(Val::CapRawReadDB(db.clone())),
        Ty::HttpsAllow { host, allows } => Some(Val::CapHttpsAllow {
            handle: CapHandle::Real,
            host: host.clone(),
            allows: allows.clone(),
        }),
        Ty::Secret(name) => Some(Val::CapSecret {
            handle: CapHandle::Real,
            name: name.clone(),
        }),
        Ty::Declassify(allows) => Some(Val::CapDeclassify(allows.clone())),
        _ => None,
    }
}

fn check_core_entry_export_gate(params: &[(Ident, LTy)], w: &World) -> Option<Bug> {
    let req = TagSet::union_owned(params.iter().map(|(_, l)| match &l.ty {
        Ty::Console(allows) | Ty::WriteFiles { allows, .. } | Ty::HttpsAllow { allows, .. } => {
            allows.clone()
        }
        _ => TagSet::empty(),
    }));
    if req.is_empty() || req.is_subset(&w.runtime_allow_export) {
        None
    } else {
        Some(Bug {
            kind: BugKind::ExportGateDenied,
            message: "runtime --allow-export authorization required for sensitive external sink"
                .to_string(),
        })
    }
}
