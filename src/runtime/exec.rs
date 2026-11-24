//! Deterministic reference evaluator for [`ExecProgram`], supporting:
//! - Pure Core IR v0.1 primitives & all 21 relational plan operators (mirroring `src/oracle/`)
//! - Phase 2 surface extensions (float arithmetic, `round`, `abs`, `date_trunc`, `months_between`,
//!   Welch `t_test`, `Table` helpers, `for`/`while` loops, `promise` & `assert` checks)
//! - Real host capabilities (filesystem CSV, confined `WriteFiles` with `--allow-export`, stdout/stderr)
//! - Isolated `dana test` fake capabilities (`Args.of`, `Files.in_memory`, `DB.in_memory`, `Console.fake`, `Secret.fake`).

use std::collections::HashMap;
use std::fs::{self, File};
use std::io::{self, BufWriter, Cursor, Write};
use std::path::Path;

use crate::core::bigint::{BigInt, DEC_MAX, DEC_MIN, DEC_SCALE, INT64_MAX, INT64_MIN};
use crate::core::check::{is_safe_relative_path, join_confined_path};
use crate::core::syntax::*;
use crate::formats::compress::{
    AutoDecodeReader, AutoEncodeWriter, CompressionKind, detect_compression_path,
    open_auto_decoded_file, strip_compression_ext,
};
use crate::formats::crypto::hmac_sha256_pseudonym;
use crate::formats::csv::{format_csv_table, read_csv_stream_with_schema, write_csv_table};
use crate::formats::json::{format_jsonl_table, read_jsonl_stream_with_schema, write_jsonl_table};
use crate::formats::time::{
    date_trunc_date, date_trunc_timestamp_duration, date_trunc_timestamp_unit, format_iso_date,
    format_iso_timestamp, format_timestamp_in_tz, local_date_in_tz, months_between_days,
    round_decimal_bigint,
};
use crate::oracle::eval::{PrimResult, eval_literal, eval_prim_op, pseudonymize_token};
use crate::oracle::value::{
    Bug, CapHandle, GroupMeta, TableRow, TableVal, Val, render_decimal, render_public_val, val_cmp,
    val_eq, val_list_eq, val_list_lt, val_lt,
};
use crate::oracle::world::{FakeConsoleState, FakeDBState, FakeFilesState, StoredTable, World};
use crate::runtime::ir::*;

const DEFAULT_FUEL: usize = 500_000;

/// Configuration for running an [`ExecProgram`].
#[derive(Clone, Debug)]
pub struct RunConfig {
    pub args: Vec<String>,
    pub allow_export: TagSet,
    pub work_dir: Option<std::path::PathBuf>,
    pub live_io: bool,
    pub fuel: usize,
    pub pseudonymize_mode: PseudonymizeMode,
}

impl Default for RunConfig {
    fn default() -> Self {
        Self {
            args: Vec::new(),
            allow_export: TagSet::empty(),
            work_dir: None,
            live_io: true,
            fuel: DEFAULT_FUEL,
            pseudonymize_mode: PseudonymizeMode::HmacSha256,
        }
    }
}

/// Result of executing `main` on an [`ExecProgram`].
#[derive(Clone, Debug)]
pub enum RunResult {
    Ok {
        exit_code: i64,
        stdout: Vec<String>,
        stderr: Vec<String>,
    },
    Stopped {
        bug: Bug,
        stdout: Vec<String>,
        stderr: Vec<String>,
    },
    Failed {
        message: String,
        stdout: Vec<String>,
        stderr: Vec<String>,
    },
}

/// Result of executing one `test` or `examples` spec block.
#[derive(Clone, Debug)]
pub struct TestOutcome {
    pub name: String,
    pub kind: FunKind,
    pub passed: bool,
    pub message: Option<String>,
}

#[derive(Clone, Debug)]
struct ExecWorld {
    world: World,
    fake_args: Vec<Vec<String>>,
    fake_console_tables: Vec<Vec<TableVal>>,
    work_dir: Option<std::path::PathBuf>,
    live_io: bool,
    pseudonymize_mode: PseudonymizeMode,
}

impl ExecWorld {
    fn from_config(cfg: &RunConfig) -> Self {
        let world = World {
            args: cfg.args.clone(),
            runtime_allow_export: cfg.allow_export.clone(),
            ..World::default()
        };
        Self {
            world,
            fake_args: Vec::new(),
            fake_console_tables: Vec::new(),
            work_dir: cfg.work_dir.clone(),
            live_io: cfg.live_io,
            pseudonymize_mode: cfg.pseudonymize_mode,
        }
    }
}

#[derive(Clone, Debug)]
enum EvalOut {
    Ok(Val),
    Jumped(Ident, Vec<Val>),
    Stopped(Bug),
    Failed(String),
}

type RTEnv = HashMap<Ident, Val>;

/// Execute `main(...)` of a lowered [`ExecProgram`].
#[must_use]
pub fn run_exec_program(prog: &ExecProgram, cfg: &RunConfig) -> RunResult {
    let Some(entry_name) = &prog.entry else {
        return RunResult::Failed {
            message: "program has no `main` entry function".to_string(),
            stdout: Vec::new(),
            stderr: Vec::new(),
        };
    };
    let Some(entry_fn) = prog.find_fun(entry_name) else {
        return RunResult::Failed {
            message: format!("missing entry function `{entry_name}`"),
            stdout: Vec::new(),
            stderr: Vec::new(),
        };
    };

    let mut ew = ExecWorld::from_config(cfg);
    let mut env = RTEnv::new();
    for (pname, plty) in &entry_fn.params {
        let cap_val = real_cap_for_ty(&plty.ty);
        env.insert(pname.clone(), cap_val);
    }

    let mut ev = Evaluator {
        prog,
        ew: &mut ew,
        fuel: cfg.fuel,
    };
    let out = ev.eval_expr(&entry_fn.body, &env);
    match out {
        EvalOut::Ok(v) => {
            let code = match &v {
                Val::Int(n) => n.to_i64().unwrap_or(0),
                _ => 0,
            };
            RunResult::Ok {
                exit_code: code,
                stdout: ew.world.stdout,
                stderr: ew.world.stderr,
            }
        }
        EvalOut::Stopped(bug) => RunResult::Stopped {
            bug,
            stdout: ew.world.stdout,
            stderr: ew.world.stderr,
        },
        EvalOut::Failed(message) => RunResult::Failed {
            message,
            stdout: ew.world.stdout,
            stderr: ew.world.stderr,
        },
        EvalOut::Jumped(lbl, _) => RunResult::Failed {
            message: format!("uncaught jump `{lbl}`"),
            stdout: ew.world.stdout,
            stderr: ew.world.stderr,
        },
    }
}

/// Run all `examples` and `test` spec blocks in a lowered [`ExecProgram`].
#[must_use]
pub fn run_program_tests(
    prog: &ExecProgram,
    filter: Option<&str>,
    cfg: &RunConfig,
) -> Vec<TestOutcome> {
    let mut outcomes = Vec::new();
    for f in &prog.funs {
        if !f.kind.is_spec() {
            continue;
        }
        let display_name = prog
            .metadata
            .entries
            .iter()
            .find(|e| e.node_id == f.name)
            .and_then(|e| e.orig_name.clone())
            .unwrap_or_else(|| f.name.clone());
        if let Some(sub) = filter
            && !display_name.contains(sub)
            && !f.name.contains(sub)
        {
            continue;
        }
        let mut spec_cfg = cfg.clone();
        spec_cfg.live_io = false;
        let mut ew = ExecWorld::from_config(&spec_cfg);
        let env = RTEnv::new();
        let mut ev = Evaluator {
            prog,
            ew: &mut ew,
            fuel: cfg.fuel,
        };
        match ev.eval_expr(&f.body, &env) {
            EvalOut::Ok(_) => outcomes.push(TestOutcome {
                name: display_name,
                kind: f.kind,
                passed: true,
                message: None,
            }),
            EvalOut::Stopped(bug) => outcomes.push(TestOutcome {
                name: display_name,
                kind: f.kind,
                passed: false,
                message: Some(format!("{:?}: {}", bug.kind, bug.message)),
            }),
            EvalOut::Failed(msg) => outcomes.push(TestOutcome {
                name: display_name,
                kind: f.kind,
                passed: false,
                message: Some(msg),
            }),
            EvalOut::Jumped(lbl, _) => outcomes.push(TestOutcome {
                name: display_name,
                kind: f.kind,
                passed: false,
                message: Some(format!("uncaught jump `{lbl}`")),
            }),
        }
    }
    outcomes
}

fn real_cap_for_ty(ty: &Ty) -> Val {
    match ty {
        Ty::Args => Val::CapArgs,
        Ty::Clock => Val::CapClock,
        Ty::Console(allows) => Val::CapConsole {
            handle: CapHandle::Real,
            allows: allows.clone(),
        },
        Ty::ReadFiles => Val::CapReadFiles(CapHandle::Real),
        Ty::WriteFiles { root, allows } => Val::CapWriteFiles {
            handle: CapHandle::Real,
            root: root.clone(),
            allows: allows.clone(),
        },
        Ty::ReadDB(db) => Val::CapReadDB {
            handle: CapHandle::Real,
            db: db.clone(),
        },
        Ty::WriteTable { db, table_name, .. } => Val::CapWriteTable {
            handle: CapHandle::Real,
            db: db.clone(),
            table_name: table_name.clone(),
        },
        Ty::RawReadDB(db) => Val::CapRawReadDB(db.clone()),
        Ty::HttpsAllow { host, allows } => Val::CapHttpsAllow {
            handle: CapHandle::Real,
            host: host.clone(),
            allows: allows.clone(),
        },
        Ty::Secret(name) => Val::CapSecret {
            handle: CapHandle::Real,
            name: name.clone(),
        },
        Ty::Declassify(allows) => Val::CapDeclassify(allows.clone()),
        _ => Val::Unit,
    }
}

#[derive(Clone, Copy, Debug)]
enum TableWriteFmt {
    Csv(u8),
    Jsonl,
}

struct Evaluator<'a> {
    prog: &'a ExecProgram,
    ew: &'a mut ExecWorld,
    fuel: usize,
}

impl<'a> Evaluator<'a> {
    fn tick(&mut self) -> Option<EvalOut> {
        if self.fuel == 0 {
            return Some(EvalOut::Stopped(Bug {
                kind: BugKind::OutsideBoundary,
                message: "execution step limit exceeded".to_string(),
            }));
        }
        self.fuel -= 1;
        None
    }

    fn eval_expr(&mut self, expr: &ExecExpr, env: &RTEnv) -> EvalOut {
        // Tail-iterate `LetE` chains so long sequential blocks run in O(1) call stack.
        let mut cur_expr = expr;
        let mut owned_env: Option<RTEnv> = None;
        loop {
            if let Some(stop) = self.tick() {
                return stop;
            }
            let cur_env = owned_env.as_ref().unwrap_or(env);
            match cur_expr {
                ExecExpr::LetE {
                    name, bound, body, ..
                } => {
                    let val = match self.eval_expr(bound, cur_env) {
                        EvalOut::Ok(v) => v,
                        other => return other,
                    };
                    let map = owned_env.get_or_insert_with(|| env.clone());
                    map.insert(name.clone(), val);
                    cur_expr = body;
                    continue;
                }
                ExecExpr::Lit(l) => return EvalOut::Ok(eval_literal(l)),
                ExecExpr::Var(name) => {
                    return cur_env.get(name).cloned().map_or_else(
                        || EvalOut::Failed(format!("unbound runtime variable `{name}`")),
                        EvalOut::Ok,
                    );
                }
                ExecExpr::ConstRef(name) => {
                    return self
                        .prog
                        .find_const(name)
                        .map(|c| eval_literal(&c.value))
                        .map_or_else(
                            || EvalOut::Failed(format!("unbound constant `{name}`")),
                            EvalOut::Ok,
                        );
                }
                ExecExpr::IfE {
                    cond,
                    then_br,
                    else_br,
                } => {
                    let cv = match self.eval_expr(cond, cur_env) {
                        EvalOut::Ok(v) => v,
                        other => return other,
                    };
                    match cv {
                        Val::Bool(true) => {
                            cur_expr = then_br;
                            continue;
                        }
                        Val::Bool(false) => {
                            cur_expr = else_br;
                            continue;
                        }
                        _ => return EvalOut::Failed("non-Bool condition in `if`".to_string()),
                    }
                }
                ExecExpr::CaseE { scrut, arms } => {
                    let sv = match self.eval_expr(scrut, cur_env) {
                        EvalOut::Ok(v) => v,
                        other => return other,
                    };
                    let mut matched_body = None;
                    for arm in arms {
                        if let Some(bindings) = match_pattern(&arm.pattern, &sv) {
                            let map = owned_env.get_or_insert_with(|| env.clone());
                            for (k, v) in bindings {
                                map.insert(k, v);
                            }
                            matched_body = Some(&arm.body);
                            break;
                        }
                    }
                    if let Some(next_body) = matched_body {
                        cur_expr = next_body;
                        continue;
                    }
                    return EvalOut::Stopped(Bug {
                        kind: BugKind::UserStop,
                        message: "non-exhaustive `case` match at runtime".to_string(),
                    });
                }
                ExecExpr::Lam { .. } => {
                    return EvalOut::Stopped(Bug {
                        kind: BugKind::OutsideBoundary,
                        message: "lambda execution not yet lowered in Slice 2A".to_string(),
                    });
                }
                ExecExpr::App { .. } => {
                    return EvalOut::Stopped(Bug {
                        kind: BugKind::OutsideBoundary,
                        message: "higher-order function application not yet supported in Slice 2A"
                            .to_string(),
                    });
                }
                ExecExpr::Call { fn_name, args } => {
                    // Iteratively flatten deep left-leaning call chains (`x |> f() |> f() |> ...`)
                    // so 200,000-stage generic pipe chains run in O(1) call stack.
                    if let Some(ExecExpr::Call { .. }) = args.first() {
                        let mut chain: Vec<(&str, &[ExecExpr])> = Vec::new();
                        chain.push((fn_name.as_str(), &args[1..]));
                        let mut base = &args[0];
                        while let ExecExpr::Call {
                            fn_name: inner_fn,
                            args: inner_args,
                        } = base
                        {
                            if let Some(first) = inner_args.first() {
                                chain.push((inner_fn.as_str(), &inner_args[1..]));
                                base = first;
                            } else {
                                break;
                            }
                        }
                        let mut acc = match self.eval_expr(base, cur_env) {
                            EvalOut::Ok(v) => v,
                            other => return other,
                        };
                        while let Some((cname, rest_args)) = chain.pop() {
                            if let Some(stop) = self.tick() {
                                return stop;
                            }
                            let mut vals = Vec::with_capacity(1 + rest_args.len());
                            vals.push(acc);
                            for a in rest_args {
                                match self.eval_expr(a, cur_env) {
                                    EvalOut::Ok(v) => vals.push(v),
                                    other => return other,
                                }
                            }
                            acc = match self.eval_call(cname, vals) {
                                EvalOut::Ok(v) => v,
                                other => return other,
                            };
                        }
                        return EvalOut::Ok(acc);
                    }
                    let mut vals = Vec::with_capacity(args.len());
                    for a in args {
                        match self.eval_expr(a, cur_env) {
                            EvalOut::Ok(v) => vals.push(v),
                            other => return other,
                        }
                    }
                    return self.eval_call(fn_name, vals);
                }
                ExecExpr::Join {
                    label,
                    params,
                    rhs,
                    body,
                } => {
                    let mut cur = self.eval_expr(body, cur_env);
                    loop {
                        match cur {
                            EvalOut::Jumped(ref lbl, ref jargs) if lbl == label => {
                                let mut jenv = cur_env.clone();
                                for ((p, _), v) in params.iter().zip(jargs.iter()) {
                                    jenv.insert(p.clone(), v.clone());
                                }
                                cur = self.eval_expr(rhs, &jenv);
                            }
                            other => return other,
                        }
                    }
                }
                ExecExpr::Jump { label, args } => {
                    let mut vals = Vec::with_capacity(args.len());
                    for a in args {
                        match self.eval_expr(a, cur_env) {
                            EvalOut::Ok(v) => vals.push(v),
                            other => return other,
                        }
                    }
                    return EvalOut::Jumped(label.clone(), vals);
                }
                ExecExpr::ForLoop {
                    item_var,
                    iter_expr,
                    state_vars,
                    body,
                    after,
                } => {
                    let iter_val = match self.eval_expr(iter_expr, cur_env) {
                        EvalOut::Ok(v) => v,
                        other => return other,
                    };
                    let Val::List(ref items) = iter_val else {
                        return EvalOut::Failed("`for` loop iterable must be a list".to_string());
                    };
                    let items = items.clone();
                    let mut loop_env = cur_env.clone();
                    for item in items {
                        if let Some(stop) = self.tick() {
                            return stop;
                        }
                        loop_env.insert(item_var.clone(), item);
                        match self.eval_expr(body, &loop_env) {
                            EvalOut::Ok(Val::Tuple(ref updated)) => {
                                for ((k, _), v) in state_vars.iter().zip(updated.iter()) {
                                    loop_env.insert(k.clone(), v.clone());
                                }
                            }
                            EvalOut::Ok(_) => {}
                            EvalOut::Jumped(lbl, vals) if lbl == "__continue" => {
                                for ((k, _), v) in state_vars.iter().zip(vals) {
                                    loop_env.insert(k.clone(), v);
                                }
                            }
                            EvalOut::Jumped(lbl, vals) if lbl == "__break" => {
                                for ((k, _), v) in state_vars.iter().zip(vals) {
                                    loop_env.insert(k.clone(), v);
                                }
                                break;
                            }
                            other => return other,
                        }
                    }
                    owned_env = Some(loop_env);
                    cur_expr = after;
                    continue;
                }
                ExecExpr::WhileLoop {
                    cond,
                    state_vars,
                    body,
                    after,
                } => {
                    let mut loop_env = cur_env.clone();
                    loop {
                        if let Some(stop) = self.tick() {
                            return stop;
                        }
                        match self.eval_expr(cond, &loop_env) {
                            EvalOut::Ok(Val::Bool(true)) => {}
                            EvalOut::Ok(Val::Bool(false)) => break,
                            EvalOut::Ok(_) => {
                                return EvalOut::Failed(
                                    "non-Bool condition in `while`".to_string(),
                                );
                            }
                            other => return other,
                        }
                        match self.eval_expr(body, &loop_env) {
                            EvalOut::Ok(Val::Tuple(ref updated)) => {
                                for ((k, _), v) in state_vars.iter().zip(updated.iter()) {
                                    loop_env.insert(k.clone(), v.clone());
                                }
                            }
                            EvalOut::Ok(_) => {}
                            EvalOut::Jumped(lbl, vals) if lbl == "__continue" => {
                                for ((k, _), v) in state_vars.iter().zip(vals) {
                                    loop_env.insert(k.clone(), v);
                                }
                            }
                            EvalOut::Jumped(lbl, vals) if lbl == "__break" => {
                                for ((k, _), v) in state_vars.iter().zip(vals) {
                                    loop_env.insert(k.clone(), v);
                                }
                                break;
                            }
                            other => return other,
                        }
                    }
                    owned_env = Some(loop_env);
                    cur_expr = after;
                    continue;
                }
                ExecExpr::Tuple(elems) => {
                    let mut vals = Vec::with_capacity(elems.len());
                    for e in elems {
                        match self.eval_expr(e, cur_env) {
                            EvalOut::Ok(v) => vals.push(v),
                            other => return other,
                        }
                    }
                    return EvalOut::Ok(Val::Tuple(vals));
                }
                ExecExpr::Proj { tup, idx } => {
                    let mut tv = match self.eval_expr(tup, cur_env) {
                        EvalOut::Ok(v) => v,
                        other => return other,
                    };
                    let i = idx.to_u64().unwrap_or(usize::MAX as u64) as usize;
                    return match &mut tv {
                        Val::Tuple(xs) if i < xs.len() => EvalOut::Ok(xs.swap_remove(i)),
                        _ => EvalOut::Failed("tuple projection out of bounds".to_string()),
                    };
                }
                ExecExpr::Ctor {
                    type_name,
                    ctor_name,
                    args,
                } => {
                    let mut fields = Vec::with_capacity(args.len());
                    for a in args {
                        match self.eval_expr(a, cur_env) {
                            EvalOut::Ok(v) => fields.push(v),
                            other => return other,
                        }
                    }
                    return EvalOut::Ok(Val::Ctor {
                        type_name: type_name.clone(),
                        ctor_name: ctor_name.clone(),
                        fields,
                    });
                }
                ExecExpr::TableLit { schema, rows } => {
                    let trows = rows
                        .iter()
                        .map(|r| TableRow {
                            cells: r.cells.iter().map(eval_literal).collect(),
                            group_meta: None,
                        })
                        .collect();
                    return EvalOut::Ok(Val::Table(TableVal {
                        cols: schema.cols.clone(),
                        rows: trows,
                    }));
                }
                ExecExpr::Prim { op, args } => {
                    // Iteratively flatten deep left-leaning primitive chains (`1 + 1 + ...`)
                    // so 200,000-term arithmetic/field chains run in O(1) call stack.
                    if let Some(ExecExpr::Prim { .. }) = args.first() {
                        let mut chain: Vec<(&ExecPrimOp, &[ExecExpr])> = Vec::new();
                        chain.push((op, &args[1..]));
                        let mut base = &args[0];
                        while let ExecExpr::Prim {
                            op: inner_op,
                            args: inner_args,
                        } = base
                        {
                            if let Some(first) = inner_args.first() {
                                chain.push((inner_op, &inner_args[1..]));
                                base = first;
                            } else {
                                break;
                            }
                        }
                        let mut acc = match self.eval_expr(base, cur_env) {
                            EvalOut::Ok(v) => v,
                            other => return other,
                        };
                        while let Some((pop, rest_args)) = chain.pop() {
                            if let Some(stop) = self.tick() {
                                return stop;
                            }
                            let mut vals = Vec::with_capacity(1 + rest_args.len());
                            vals.push(acc);
                            for a in rest_args {
                                match self.eval_expr(a, cur_env) {
                                    EvalOut::Ok(v) => vals.push(v),
                                    other => return other,
                                }
                            }
                            acc = match self.eval_exec_prim(pop, &vals) {
                                EvalOut::Ok(v) => v,
                                other => return other,
                            };
                        }
                        return EvalOut::Ok(acc);
                    }
                    let mut vals = Vec::with_capacity(args.len());
                    for a in args {
                        match self.eval_expr(a, cur_env) {
                            EvalOut::Ok(v) => vals.push(v),
                            other => return other,
                        }
                    }
                    return self.eval_exec_prim(op, &vals);
                }
                ExecExpr::Rel(plan) => return self.eval_plan(plan, cur_env),
                ExecExpr::Host { op, args } => {
                    let mut vals = Vec::with_capacity(args.len());
                    for a in args {
                        match self.eval_expr(a, cur_env) {
                            EvalOut::Ok(v) => vals.push(v),
                            other => return other,
                        }
                    }
                    return self.eval_exec_host(op, &vals);
                }
                ExecExpr::Assert { cond, message } => {
                    return match self.eval_expr(cond, cur_env) {
                        EvalOut::Ok(Val::Bool(true)) => EvalOut::Ok(Val::Unit),
                        EvalOut::Ok(Val::Bool(false)) => EvalOut::Stopped(Bug {
                            kind: BugKind::PromiseViolation,
                            message: message.clone(),
                        }),
                        EvalOut::Ok(_) => {
                            EvalOut::Failed("`assert` evaluated to non-Bool".to_string())
                        }
                        other => other,
                    };
                }
                ExecExpr::CheckPromise { ret_var, promise } => {
                    return self.eval_promise(ret_var, promise, cur_env);
                }
                ExecExpr::Stop {
                    kind,
                    detail,
                    detail_tags,
                } => {
                    let msg = match detail {
                        Some(d) => match self.eval_expr(d, cur_env) {
                            EvalOut::Ok(v) => {
                                crate::oracle::value::format_diag_detail(detail_tags, &v)
                            }
                            other => return other,
                        },
                        None => format!("{kind:?}"),
                    };
                    return EvalOut::Stopped(Bug {
                        kind: *kind,
                        message: msg,
                    });
                }
                ExecExpr::Fail(e) => {
                    return match self.eval_expr(e, cur_env) {
                        EvalOut::Ok(v) => EvalOut::Failed(render_public_val(&v)),
                        other => other,
                    };
                }
            }
        }
    }

    fn eval_call(&mut self, fn_name: &str, args: Vec<Val>) -> EvalOut {
        let Some(f) = self.prog.find_fun(fn_name) else {
            return EvalOut::Failed(format!("unknown function `{fn_name}`"));
        };
        let mut fenv = RTEnv::new();
        for ((pname, _), val) in f.params.iter().zip(args) {
            fenv.insert(pname.clone(), val);
        }
        self.eval_expr(&f.body, &fenv)
    }

    fn eval_promise(&mut self, ret_var: &str, promise: &ExecPromise, env: &RTEnv) -> EvalOut {
        match promise {
            ExecPromise::UniqueCols(cols) => {
                let Some(Val::Table(tv)) = env.get(ret_var) else {
                    return EvalOut::Failed("`promise unique` expected Table".to_string());
                };
                let idxs: Vec<usize> = cols
                    .iter()
                    .filter_map(|c| tv.cols.iter().position(|cs| cs.name == *c))
                    .collect();
                let mut seen: Vec<Vec<Val>> = Vec::with_capacity(tv.rows.len());
                for row in &tv.rows {
                    let key: Vec<Val> = idxs.iter().map(|&i| row.cells[i].clone()).collect();
                    if seen.iter().any(|k| val_list_eq(k, &key)) {
                        return EvalOut::Stopped(Bug {
                            kind: BugKind::PromiseViolation,
                            message: format!("`promise unique({cols:?})` violated"),
                        });
                    }
                    seen.push(key);
                }
                EvalOut::Ok(Val::Unit)
            }
            ExecPromise::AllRows(pred) => {
                let Some(Val::Table(tv)) = env.get(ret_var) else {
                    return EvalOut::Failed("`promise all` expected Table".to_string());
                };
                for row in &tv.rows {
                    match self.eval_row_expr(pred, &tv.cols, &row.cells, env) {
                        EvalOut::Ok(Val::Bool(true)) => {}
                        EvalOut::Ok(Val::Bool(false)) => {
                            return EvalOut::Stopped(Bug {
                                kind: BugKind::PromiseViolation,
                                message: "`promise all(...)` violated".to_string(),
                            });
                        }
                        EvalOut::Ok(_) => {
                            return EvalOut::Failed("`promise all` returned non-Bool".to_string());
                        }
                        other => return other,
                    }
                }
                EvalOut::Ok(Val::Unit)
            }
            ExecPromise::BoolExpr(ex) => match self.eval_expr(ex, env) {
                EvalOut::Ok(Val::Bool(true)) => EvalOut::Ok(Val::Unit),
                EvalOut::Ok(Val::Bool(false)) => EvalOut::Stopped(Bug {
                    kind: BugKind::PromiseViolation,
                    message: "`promise` postcondition violated".to_string(),
                }),
                EvalOut::Ok(_) => EvalOut::Failed("`promise` evaluated to non-Bool".to_string()),
                other => other,
            },
        }
    }

    // -----------------------------------------------------------------------
    // Primitives
    // -----------------------------------------------------------------------

    fn eval_exec_prim(&self, op: &ExecPrimOp, args: &[Val]) -> EvalOut {
        match op {
            ExecPrimOp::Core(cop) => match eval_prim_op(cop, args) {
                PrimResult::Ok(v) => EvalOut::Ok(v),
                PrimResult::Stopped(b) => EvalOut::Stopped(b),
                PrimResult::OutOfFuel => EvalOut::Stopped(Bug {
                    kind: BugKind::OutsideBoundary,
                    message: "out of fuel".to_string(),
                }),
                PrimResult::Wrong => EvalOut::Failed(format!("primitive type error in `{cop:?}`")),
            },
            ExecPrimOp::AddFloat => match args {
                [Val::Float(a), Val::Float(b)] => {
                    EvalOut::Ok(Val::Float(Float64::from_f64(a.to_f64() + b.to_f64())))
                }
                _ => EvalOut::Failed("AddFloat requires two Float args".to_string()),
            },
            ExecPrimOp::SubFloat => match args {
                [Val::Float(a), Val::Float(b)] => {
                    EvalOut::Ok(Val::Float(Float64::from_f64(a.to_f64() - b.to_f64())))
                }
                _ => EvalOut::Failed("SubFloat requires two Float args".to_string()),
            },
            ExecPrimOp::MulFloat => match args {
                [Val::Float(a), Val::Float(b)] => {
                    EvalOut::Ok(Val::Float(Float64::from_f64(a.to_f64() * b.to_f64())))
                }
                _ => EvalOut::Failed("MulFloat requires two Float args".to_string()),
            },
            ExecPrimOp::DivFloat => match args {
                [Val::Float(a), Val::Float(b)] => {
                    if b.to_f64() == 0.0 {
                        EvalOut::Stopped(Bug {
                            kind: BugKind::DivByZero,
                            message: "Float division by zero".to_string(),
                        })
                    } else {
                        EvalOut::Ok(Val::Float(Float64::from_f64(a.to_f64() / b.to_f64())))
                    }
                }
                _ => EvalOut::Failed("DivFloat requires two Float args".to_string()),
            },
            ExecPrimOp::NegFloat => match args {
                [Val::Float(a)] => EvalOut::Ok(Val::Float(Float64::from_f64(-a.to_f64()))),
                _ => EvalOut::Failed("NegFloat requires Float".to_string()),
            },
            ExecPrimOp::AbsFloat => match args {
                [Val::Float(a)] => EvalOut::Ok(Val::Float(Float64::from_f64(a.to_f64().abs()))),
                _ => EvalOut::Failed("AbsFloat requires Float".to_string()),
            },
            ExecPrimOp::AbsDecimal => match args {
                [Val::Decimal(d)] => {
                    let abs = if d.is_negative() {
                        -d.clone()
                    } else {
                        d.clone()
                    };
                    EvalOut::Ok(Val::Decimal(abs))
                }
                _ => EvalOut::Failed("AbsDecimal requires Decimal".to_string()),
            },
            ExecPrimOp::AbsInt => match args {
                [Val::Int(n)] => {
                    let abs = if n.is_negative() {
                        -n.clone()
                    } else {
                        n.clone()
                    };
                    if abs.in_int64_range() {
                        EvalOut::Ok(Val::Int(abs))
                    } else {
                        EvalOut::Stopped(Bug {
                            kind: BugKind::IntOverflow,
                            message: "Int64 abs overflow".to_string(),
                        })
                    }
                }
                _ => EvalOut::Failed("AbsInt requires Int".to_string()),
            },
            ExecPrimOp::RoundFloat => match args {
                [Val::Float(a), Val::Int(p)] => {
                    let places = p.to_i64().unwrap_or(0).clamp(0, 15) as i32;
                    let factor = 10f64.powi(places);
                    let r = (a.to_f64() * factor).round() / factor;
                    EvalOut::Ok(Val::Float(Float64::from_f64(r)))
                }
                _ => EvalOut::Failed("RoundFloat requires (Float, Int)".to_string()),
            },
            ExecPrimOp::RoundDecimal => match args {
                [Val::Decimal(d), Val::Int(p)] => {
                    let places = p.to_i64().unwrap_or(0);
                    EvalOut::Ok(Val::Decimal(round_decimal_bigint(d, places)))
                }
                _ => EvalOut::Failed("RoundDecimal requires (Decimal, Int)".to_string()),
            },
            ExecPrimOp::IntToFloat => match args {
                [Val::Int(n)] => EvalOut::Ok(Val::Float(Float64::from_f64(
                    n.to_i64().unwrap_or(0) as f64,
                ))),
                _ => EvalOut::Failed("IntToFloat requires Int".to_string()),
            },
            ExecPrimOp::DecToFloat => match args {
                [Val::Decimal(d)] => {
                    let f = render_decimal(d).parse::<f64>().unwrap_or(0.0);
                    EvalOut::Ok(Val::Float(Float64::from_f64(f)))
                }
                _ => EvalOut::Failed("DecToFloat requires Decimal".to_string()),
            },
            ExecPrimOp::ValToText => match args {
                [v] => EvalOut::Ok(Val::Text(format_display_val(v))),
                _ => EvalOut::Failed("ValToText requires 1 arg".to_string()),
            },
            ExecPrimOp::DateTruncUnit(unit) => match args {
                [Val::Date(d)] => match date_trunc_date(d.to_i64().unwrap_or(0), unit) {
                    Ok(td) => EvalOut::Ok(Val::Date(BigInt::from(td))),
                    Err(e) => EvalOut::Failed(e.message),
                },
                [Val::Timestamp(ts)] => {
                    match date_trunc_timestamp_unit(ts.to_i64().unwrap_or(0), unit) {
                        Ok(t) => EvalOut::Ok(Val::Timestamp(BigInt::from(t))),
                        Err(e) => EvalOut::Failed(e.message),
                    }
                }
                _ => EvalOut::Failed("DateTruncUnit requires Date or Timestamp".to_string()),
            },
            ExecPrimOp::DateTruncDuration => match args {
                [Val::Timestamp(ts), Val::Duration(dur)] => {
                    match date_trunc_timestamp_duration(
                        ts.to_i64().unwrap_or(0),
                        dur.to_i64().unwrap_or(0),
                    ) {
                        Ok(t) => EvalOut::Ok(Val::Timestamp(BigInt::from(t))),
                        Err(e) => EvalOut::Failed(e.message),
                    }
                }
                _ => {
                    EvalOut::Failed("DateTruncDuration requires (Timestamp, Duration)".to_string())
                }
            },
            ExecPrimOp::MonthsBetween => match args {
                [Val::Date(d1), Val::Date(d2)] => {
                    let m = months_between_days(d1.to_i64().unwrap_or(0), d2.to_i64().unwrap_or(0));
                    EvalOut::Ok(Val::Int(BigInt::from(m)))
                }
                _ => EvalOut::Failed("MonthsBetween requires two Dates".to_string()),
            },
            ExecPrimOp::InTz => match args {
                [Val::Timestamp(ts), Val::Text(zone)] => match ts.to_i64() {
                    Some(us) => match format_timestamp_in_tz(us, zone) {
                        Ok(s) => EvalOut::Ok(Val::Text(s)),
                        Err(e) => EvalOut::Stopped(Bug {
                            kind: BugKind::OutsideBoundary,
                            message: e.message,
                        }),
                    },
                    None => EvalOut::Failed("InTz Timestamp overflow".to_string()),
                },
                _ => EvalOut::Failed("InTz requires (Timestamp, Text)".to_string()),
            },
            ExecPrimOp::DateInTz => match args {
                [Val::Timestamp(ts), Val::Text(zone)] => match ts.to_i64() {
                    Some(us) => match local_date_in_tz(us, zone) {
                        Ok(days) => EvalOut::Ok(Val::Date(BigInt::from(days))),
                        Err(e) => EvalOut::Stopped(Bug {
                            kind: BugKind::OutsideBoundary,
                            message: e.message,
                        }),
                    },
                    None => EvalOut::Failed("DateInTz Timestamp overflow".to_string()),
                },
                _ => EvalOut::Failed("DateInTz requires (Timestamp, Text)".to_string()),
            },
            ExecPrimOp::ListFirst => match args {
                [Val::List(xs)] => match xs.first() {
                    Some(v) => EvalOut::Ok(Val::OptSome(Box::new(v.clone()))),
                    None => EvalOut::Ok(Val::OptNone),
                },
                _ => EvalOut::Failed("ListFirst requires List".to_string()),
            },
            ExecPrimOp::ListFirstBang => match args {
                [Val::List(xs)] => match xs.first() {
                    Some(v) => EvalOut::Ok(v.clone()),
                    None => EvalOut::Stopped(Bug {
                        kind: BugKind::UnwrapNone,
                        message: "called `.first!` on an empty list".to_string(),
                    }),
                },
                _ => EvalOut::Failed("ListFirstBang requires List".to_string()),
            },
            ExecPrimOp::TableEmpty => match args {
                [Val::Table(tv)] => EvalOut::Ok(Val::Bool(tv.rows.is_empty())),
                _ => EvalOut::Failed("TableEmpty requires Table".to_string()),
            },
            ExecPrimOp::TableFirstBang => match args {
                [Val::Table(tv)] => match tv.rows.first() {
                    Some(r) => EvalOut::Ok(Val::Ctor {
                        type_name: "__TableRow".to_string(),
                        ctor_name: "__TableRow".to_string(),
                        fields: r.cells.clone(),
                    }),
                    None => EvalOut::Stopped(Bug {
                        kind: BugKind::UnwrapNone,
                        message: "called `.first!` on an empty table".to_string(),
                    }),
                },
                _ => EvalOut::Failed("TableFirstBang requires Table".to_string()),
            },
            ExecPrimOp::TableRowsToList => match args {
                [Val::Table(tv)] => {
                    let rows = tv
                        .rows
                        .iter()
                        .map(|r| Val::Ctor {
                            type_name: "__TableRow".to_string(),
                            ctor_name: "__TableRow".to_string(),
                            fields: r.cells.clone(),
                        })
                        .collect();
                    EvalOut::Ok(Val::List(rows))
                }
                _ => EvalOut::Failed("TableRowsToList requires Table".to_string()),
            },
            ExecPrimOp::TableColSum(col) => match args {
                [Val::Table(tv)] => eval_table_col_agg(tv, col, AggOp::Sum),
                _ => EvalOut::Failed("TableColSum requires Table".to_string()),
            },
            ExecPrimOp::TableColMean(col) => match args {
                [Val::Table(tv)] => eval_table_col_agg(tv, col, AggOp::Mean),
                _ => EvalOut::Failed("TableColMean requires Table".to_string()),
            },
            ExecPrimOp::TableColStddev(col) => match args {
                [Val::Table(tv)] => eval_table_col_agg(tv, col, AggOp::Stddev),
                _ => EvalOut::Failed("TableColStddev requires Table".to_string()),
            },
            ExecPrimOp::TableBuildDynamic(schema) => {
                let ncols = schema.cols.len();
                if ncols == 0 {
                    return EvalOut::Ok(Val::Table(TableVal::default()));
                }
                let mut rows = Vec::with_capacity(args.len() / ncols);
                for chunk in args.chunks_exact(ncols) {
                    rows.push(TableRow {
                        cells: chunk.to_vec(),
                        group_meta: None,
                    });
                }
                EvalOut::Ok(Val::Table(TableVal {
                    cols: schema.cols.clone(),
                    rows,
                }))
            }
            ExecPrimOp::TableCoerce(dst_tt) => match args {
                [Val::Table(tv)] => {
                    let src_idxs: Vec<Option<usize>> = dst_tt
                        .cols
                        .iter()
                        .map(|dc| tv.cols.iter().position(|sc| sc.name == dc.name))
                        .collect();
                    let mut rows = Vec::with_capacity(tv.rows.len());
                    for r in &tv.rows {
                        let mut cells = Vec::with_capacity(dst_tt.cols.len());
                        for (ci, dc) in dst_tt.cols.iter().enumerate() {
                            let v = src_idxs[ci]
                                .and_then(|si| r.cells.get(si))
                                .cloned()
                                .unwrap_or(Val::Unit);
                            let coerced = coerce_cell_to_scalar(v, &dc.ty);
                            cells.push(coerced);
                        }
                        rows.push(TableRow {
                            cells,
                            group_meta: r.group_meta,
                        });
                    }
                    EvalOut::Ok(Val::Table(TableVal {
                        cols: dst_tt.cols.clone(),
                        rows,
                    }))
                }
                _ => EvalOut::Failed("TableCoerce requires Table".to_string()),
            },
            ExecPrimOp::RecordField { field_idx, .. } => match args {
                [Val::Ctor { fields, .. }] => fields.get(*field_idx).cloned().map_or_else(
                    || EvalOut::Failed("record field index out of bounds".to_string()),
                    EvalOut::Ok,
                ),
                [
                    Val::LinearModel {
                        slope,
                        intercept,
                        r2,
                    },
                ] => {
                    let f = match field_idx {
                        0 => *slope,
                        1 => *intercept,
                        _ => *r2,
                    };
                    EvalOut::Ok(Val::Float(f))
                }
                [Val::StatTest { stat, p_value }] => {
                    let f = match field_idx {
                        0 => *stat,
                        1 => *p_value,
                        _ => Float64::ZERO,
                    };
                    EvalOut::Ok(Val::Float(f))
                }
                _ => EvalOut::Failed(
                    "RecordField requires Ctor, LinearModel, or StatTest".to_string(),
                ),
            },
            ExecPrimOp::StatsWelchTTest { col } => match args {
                [Val::Table(a), Val::Table(b)] => eval_welch_t_test(a, b, col),
                _ => EvalOut::Failed("StatsWelchTTest requires two Tables".to_string()),
            },
            ExecPrimOp::OptSubInt => match args {
                [Val::Int(_), Val::OptNone] => EvalOut::Ok(Val::OptNone),
                [Val::Int(a), Val::OptSome(b)] => match b.as_ref() {
                    Val::Int(bv) => {
                        let diff = a - bv;
                        if diff.in_int64_range() {
                            EvalOut::Ok(Val::OptSome(Box::new(Val::Int(diff))))
                        } else {
                            EvalOut::Stopped(Bug {
                                kind: BugKind::IntOverflow,
                                message: "Int64 overflow".to_string(),
                            })
                        }
                    }
                    _ => EvalOut::Failed("OptSubInt type error".to_string()),
                },
                _ => EvalOut::Failed("OptSubInt requires (Int, Option(Int))".to_string()),
            },
            ExecPrimOp::OptSubDec => match args {
                [Val::Decimal(_), Val::OptNone] => EvalOut::Ok(Val::OptNone),
                [Val::Decimal(a), Val::OptSome(b)] => match b.as_ref() {
                    Val::Decimal(bv) => {
                        let diff = a - bv;
                        if diff.in_decimal_range() {
                            EvalOut::Ok(Val::OptSome(Box::new(Val::Decimal(diff))))
                        } else {
                            EvalOut::Stopped(Bug {
                                kind: BugKind::DecimalOverflow,
                                message: "Decimal overflow".to_string(),
                            })
                        }
                    }
                    _ => EvalOut::Failed("OptSubDec type error".to_string()),
                },
                _ => EvalOut::Failed("OptSubDec requires (Decimal, Option(Decimal))".to_string()),
            },
            ExecPrimOp::OptSubFloat => match args {
                [Val::Float(_), Val::OptNone] => EvalOut::Ok(Val::OptNone),
                [Val::Float(a), Val::OptSome(b)] => match b.as_ref() {
                    Val::Float(bv) => EvalOut::Ok(Val::OptSome(Box::new(Val::Float(
                        Float64::from_f64(a.to_f64() - bv.to_f64()),
                    )))),
                    _ => EvalOut::Failed("OptSubFloat type error".to_string()),
                },
                _ => EvalOut::Failed("OptSubFloat requires (Float, Option(Float))".to_string()),
            },
            ExecPrimOp::TableEq => match args {
                [Val::Table(a), Val::Table(b)] => {
                    let same_cols = a.cols.len() == b.cols.len()
                        && a.cols.iter().zip(&b.cols).all(|(x, y)| x.name == y.name);
                    let same_rows = same_cols
                        && a.rows.len() == b.rows.len()
                        && a.rows
                            .iter()
                            .zip(&b.rows)
                            .all(|(ra, rb)| val_list_eq(&ra.cells, &rb.cells));
                    EvalOut::Ok(Val::Bool(same_rows))
                }
                _ => EvalOut::Failed("TableEq requires two Tables".to_string()),
            },
            ExecPrimOp::PromiseUnique(_) | ExecPrimOp::PromiseAll => EvalOut::Ok(Val::Bool(true)),
        }
    }

    // -----------------------------------------------------------------------
    // Host Operations & Spec Fake Capabilities
    // -----------------------------------------------------------------------

    fn eval_exec_host(&mut self, op: &ExecHostOp, args: &[Val]) -> EvalOut {
        match op {
            ExecHostOp::FakeArgsOf => match args {
                [Val::List(xs)] => {
                    let list: Vec<String> = xs
                        .iter()
                        .map(|v| match v {
                            Val::Text(s) => s.clone(),
                            other => render_public_val(other),
                        })
                        .collect();
                    let idx = self.ew.fake_args.len();
                    self.ew.fake_args.push(list);
                    EvalOut::Ok(Val::Ctor {
                        type_name: "__FakeArgs".to_string(),
                        ctor_name: "__FakeArgs".to_string(),
                        fields: vec![Val::Int(BigInt::from(idx))],
                    })
                }
                _ => EvalOut::Failed("Args.of requires List(Text)".to_string()),
            },
            ExecHostOp::ArgsFirst => {
                let list = self.extract_args_list(args.first());
                match list.first() {
                    Some(s) => EvalOut::Ok(Val::OptSome(Box::new(Val::Text(s.clone())))),
                    None => EvalOut::Ok(Val::OptNone),
                }
            }
            ExecHostOp::FakeFilesInMemory => match args {
                [Val::Map(pairs)] => {
                    let files: Vec<(String, String)> = pairs
                        .iter()
                        .map(|(k, v)| (format_display_val(k), format_display_val(v)))
                        .collect();
                    let idx = self.ew.world.fake_files.len();
                    self.ew.world.fake_files.push(FakeFilesState { files });
                    EvalOut::Ok(Val::CapReadFiles(CapHandle::Fake(idx)))
                }
                _ => EvalOut::Failed("Files.in_memory requires Map(Text, Text)".to_string()),
            },
            ExecHostOp::FakeDbInMemory { db, table_names } => {
                let mut tables = Vec::with_capacity(table_names.len());
                for (tname, val) in table_names.iter().zip(args.iter()) {
                    if let Val::Table(tv) = val {
                        let schema = self.prog.find_schema(tname).map_or_else(
                            || TableTy {
                                cols: tv.cols.clone(),
                                ..TableTy::default()
                            },
                            |s| s.decl.schema.clone(),
                        );
                        let rows = tv.rows.iter().map(|r| r.cells.clone()).collect();
                        tables.push(StoredTable {
                            db: db.clone(),
                            table_name: tname.clone(),
                            schema,
                            rows,
                        });
                    }
                }
                let idx = self.ew.world.fake_dbs.len();
                self.ew.world.fake_dbs.push(FakeDBState {
                    db: db.clone(),
                    tables,
                });
                EvalOut::Ok(Val::CapReadDB {
                    handle: CapHandle::Fake(idx),
                    db: db.clone(),
                })
            }
            ExecHostOp::FakeConsoleLines => match args {
                [
                    Val::CapConsole {
                        handle: CapHandle::Fake(idx),
                        ..
                    },
                ] => {
                    let lines = self
                        .ew
                        .world
                        .fake_consoles
                        .get(*idx)
                        .map(|fc| fc.stdout.iter().cloned().map(Val::Text).collect())
                        .unwrap_or_default();
                    EvalOut::Ok(Val::List(lines))
                }
                _ => EvalOut::Failed("printed_lines requires fake Console".to_string()),
            },
            ExecHostOp::FakeConsoleErrors => match args {
                [
                    Val::CapConsole {
                        handle: CapHandle::Fake(idx),
                        ..
                    },
                ] => {
                    let errs = self
                        .ew
                        .world
                        .fake_consoles
                        .get(*idx)
                        .map(|fc| fc.stderr.iter().cloned().map(Val::Text).collect())
                        .unwrap_or_default();
                    EvalOut::Ok(Val::List(errs))
                }
                _ => EvalOut::Failed("printed_errors requires fake Console".to_string()),
            },
            ExecHostOp::FakeConsoleTables => match args {
                [
                    Val::CapConsole {
                        handle: CapHandle::Fake(idx),
                        ..
                    },
                ] => {
                    let tbls = self
                        .ew
                        .fake_console_tables
                        .get(*idx)
                        .map(|ts| ts.iter().cloned().map(Val::Table).collect())
                        .unwrap_or_default();
                    EvalOut::Ok(Val::List(tbls))
                }
                _ => EvalOut::Failed("printed_tables requires fake Console".to_string()),
            },
            ExecHostOp::ConsolePrintChart | ExecHostOp::ConsolePrintProfile => {
                if let [Val::CapConsole { handle, .. }, payload] = args {
                    let rendered = format_display_val(payload);
                    match handle {
                        CapHandle::Real => self.ew.world.stdout.push(rendered),
                        CapHandle::Fake(idx) => {
                            if let Some(fc) = self.ew.world.fake_consoles.get_mut(*idx) {
                                fc.stdout.push(rendered);
                            }
                        }
                    }
                    EvalOut::Ok(Val::Unit)
                } else {
                    EvalOut::Failed("console print expects (Console, value)".to_string())
                }
            }
            ExecHostOp::ReadJsonl(schema_name) => {
                if let [Val::CapReadFiles(handle), Val::Text(path)] = args {
                    self.eval_read_jsonl(schema_name, *handle, path)
                } else {
                    EvalOut::Failed("read_jsonl expects (ReadFiles, path)".to_string())
                }
            }
            ExecHostOp::WriteJsonl => {
                if let [
                    Val::CapWriteFiles {
                        handle,
                        root,
                        allows,
                    },
                    Val::Text(rel),
                    Val::Table(tv),
                ] = args
                {
                    if let Some(bug) = self.check_export_gate(*handle, allows) {
                        return EvalOut::Stopped(bug);
                    }
                    if !is_safe_relative_path(rel) {
                        return EvalOut::Ok(Val::ResErr(Box::new(Val::Text(format!(
                            "unsafe write path `{rel}`"
                        )))));
                    }
                    let full_rel = join_confined_path(root, rel);
                    self.write_confined_table(*handle, &full_rel, tv, TableWriteFmt::Jsonl)
                } else {
                    EvalOut::Failed("write_jsonl expects (WriteFiles, path, table)".to_string())
                }
            }
            ExecHostOp::WriteCsv => {
                if let [
                    Val::CapWriteFiles {
                        handle,
                        root,
                        allows,
                    },
                    Val::Text(rel),
                    Val::Table(tv),
                ] = args
                {
                    if let Some(bug) = self.check_export_gate(*handle, allows) {
                        return EvalOut::Stopped(bug);
                    }
                    if !is_safe_relative_path(rel) {
                        return EvalOut::Ok(Val::ResErr(Box::new(Val::Text(format!(
                            "unsafe write path `{rel}`"
                        )))));
                    }
                    let full_rel = join_confined_path(root, rel);
                    let delim = if strip_compression_ext(rel).ends_with(".tsv") {
                        b'\t'
                    } else {
                        b','
                    };
                    self.write_confined_table(*handle, &full_rel, tv, TableWriteFmt::Csv(delim))
                } else {
                    EvalOut::Failed("write_csv expects (WriteFiles, path, table)".to_string())
                }
            }
            ExecHostOp::ReadXlsx(_)
            | ExecHostOp::WriteTableUpsert { .. }
            | ExecHostOp::JsonParseTable(_)
            | ExecHostOp::JsonBoolAt => EvalOut::Stopped(Bug {
                kind: BugKind::OutsideBoundary,
                message: "operation requires Phase 3/4 database/XLSX/HTTPS drivers".to_string(),
            }),
            ExecHostOp::Core(cop) => self.eval_core_host(cop, args),
        }
    }

    fn extract_args_list(&self, cap: Option<&Val>) -> Vec<String> {
        match cap {
            Some(Val::Ctor {
                type_name, fields, ..
            }) if type_name == "__FakeArgs" => {
                let idx = fields
                    .first()
                    .and_then(|v| match v {
                        Val::Int(n) => n.to_u64(),
                        _ => None,
                    })
                    .unwrap_or(usize::MAX as u64) as usize;
                self.ew.fake_args.get(idx).cloned().unwrap_or_default()
            }
            _ => self.ew.world.args.clone(),
        }
    }

    fn eval_core_host(&mut self, op: &HostOp, args: &[Val]) -> EvalOut {
        match (op, args) {
            (HostOp::ArgsGet, [cap]) => {
                let list = self.extract_args_list(Some(cap));
                EvalOut::Ok(Val::List(list.into_iter().map(Val::Text).collect()))
            }
            (HostOp::ClockNow, [Val::CapClock]) => {
                EvalOut::Ok(Val::Timestamp(self.ew.world.clock_micros.clone()))
            }
            (HostOp::ConsolePrint, [Val::CapConsole { handle, .. }, Val::Text(msg)]) => {
                match handle {
                    CapHandle::Real => self.ew.world.stdout.push(msg.clone()),
                    CapHandle::Fake(idx) => {
                        if let Some(fc) = self.ew.world.fake_consoles.get_mut(*idx) {
                            fc.stdout.push(msg.clone());
                        }
                    }
                }
                EvalOut::Ok(Val::Unit)
            }
            (HostOp::ConsoleError, [Val::CapConsole { handle, .. }, Val::Text(msg)]) => {
                match handle {
                    CapHandle::Real => self.ew.world.stderr.push(msg.clone()),
                    CapHandle::Fake(idx) => {
                        if let Some(fc) = self.ew.world.fake_consoles.get_mut(*idx) {
                            fc.stderr.push(msg.clone());
                        }
                    }
                }
                EvalOut::Ok(Val::Unit)
            }
            (HostOp::ConsolePrintTable, [Val::CapConsole { handle, .. }, Val::Table(tv)]) => {
                let rendered = format_pretty_table(tv);
                match handle {
                    CapHandle::Real => self.ew.world.stdout.push(rendered),
                    CapHandle::Fake(idx) => {
                        if let Some(fc) = self.ew.world.fake_consoles.get_mut(*idx) {
                            fc.stdout.push(rendered);
                        }
                        if let Some(ft) = self.ew.fake_console_tables.get_mut(*idx) {
                            ft.push(tv.clone());
                        }
                    }
                }
                EvalOut::Ok(Val::Unit)
            }
            (HostOp::ReadCsv(schema_name), [Val::CapReadFiles(handle), Val::Text(path)]) => {
                self.eval_read_csv(schema_name, *handle, path)
            }
            (
                HostOp::WriteFile,
                [
                    Val::CapWriteFiles {
                        handle,
                        root,
                        allows,
                    },
                    Val::Text(rel),
                    Val::Text(content),
                ],
            ) => {
                if let Some(bug) = self.check_export_gate(*handle, allows) {
                    return EvalOut::Stopped(bug);
                }
                if !is_safe_relative_path(rel) {
                    return EvalOut::Ok(Val::ResErr(Box::new(Val::Text(format!(
                        "unsafe write path `{rel}`"
                    )))));
                }
                let full_rel = join_confined_path(root, rel);
                self.write_confined_output(*handle, &full_rel, content.clone())
            }
            (
                HostOp::WriteReportHtml,
                [
                    Val::CapWriteFiles {
                        handle,
                        root,
                        allows,
                    },
                    Val::Text(rel),
                    Val::Report(rep),
                ],
            ) => {
                if let Some(bug) = self.check_export_gate(*handle, allows) {
                    return EvalOut::Stopped(bug);
                }
                if !is_safe_relative_path(rel) {
                    return EvalOut::Ok(Val::ResErr(Box::new(Val::Text(format!(
                        "unsafe write path `{rel}`"
                    )))));
                }
                let full_rel = join_confined_path(root, rel);
                let html = render_basic_html_report(rep);
                self.write_confined_output(*handle, &full_rel, html)
            }
            (HostOp::FakeConsole(allows), []) => {
                let idx = self.ew.world.fake_consoles.len();
                self.ew
                    .world
                    .fake_consoles
                    .push(FakeConsoleState::default());
                self.ew.fake_console_tables.push(Vec::new());
                EvalOut::Ok(Val::CapConsole {
                    handle: CapHandle::Fake(idx),
                    allows: allows.clone(),
                })
            }
            (HostOp::FakeSecret(name), [Val::Text(secret_val)]) => {
                let idx = self.ew.world.fake_secrets.len();
                self.ew.world.fake_secrets.push(secret_val.clone());
                EvalOut::Ok(Val::CapSecret {
                    handle: CapHandle::Fake(idx),
                    name: name.clone(),
                })
            }
            (
                HostOp::ReadParquet(_)
                | HostOp::WriteParquet
                | HostOp::WriteXlsx
                | HostOp::WriteTable
                | HostOp::RawSqlQuery { .. }
                | HostOp::HttpsGetJson,
                _,
            ) => EvalOut::Stopped(Bug {
                kind: BugKind::OutsideBoundary,
                message: format!("host operation `{op:?}` requires Phase 3/4 runtime drivers"),
            }),
            _ => EvalOut::Failed(format!("unsupported host operation `{op:?}`")),
        }
    }

    fn check_export_gate(&self, handle: CapHandle, allows: &TagSet) -> Option<Bug> {
        match handle {
            CapHandle::Fake(_) => None,
            CapHandle::Real => {
                if allows.is_empty() || allows.is_subset(&self.ew.world.runtime_allow_export) {
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

    fn eval_read_csv(&mut self, schema_name: &str, handle: CapHandle, path: &str) -> EvalOut {
        let Some(cs) = self.prog.find_schema(schema_name) else {
            return EvalOut::Failed(format!("unknown schema `{schema_name}`"));
        };
        let delimiter = if strip_compression_ext(path).ends_with(".tsv") {
            b'\t'
        } else {
            b','
        };
        let constraints = cs.constraints.clone();
        let schema_tt = cs.decl.schema.clone();
        let empty_env = RTEnv::new();

        let parsed = match handle {
            CapHandle::Fake(idx) => {
                let Some(ff) = self.ew.world.fake_files.get(idx) else {
                    return EvalOut::Ok(Val::ResErr(Box::new(Val::Text(format!(
                        "file not found: {path}"
                    )))));
                };
                let Some((_, content)) = ff.files.iter().find(|(p, _)| p == path) else {
                    return EvalOut::Ok(Val::ResErr(Box::new(Val::Text(format!(
                        "file not found: {path}"
                    )))));
                };
                let content = content.clone();
                let reader = match AutoDecodeReader::new(Cursor::new(content.as_bytes())) {
                    Ok(r) => r,
                    Err(e) => {
                        return EvalOut::Ok(Val::ResErr(Box::new(Val::Text(format!(
                            "{path}: {e}"
                        )))));
                    }
                };
                read_csv_stream_with_schema(reader, &schema_tt, delimiter, |ci, val| {
                    self.eval_schema_constraint(&schema_tt, &constraints, ci, val, &empty_env)
                })
            }
            CapHandle::Real => {
                if !self.ew.live_io {
                    return EvalOut::Ok(Val::ResErr(Box::new(Val::Text(format!(
                        "file I/O disabled in spec mode: {path}"
                    )))));
                }
                let resolved = match &self.ew.work_dir {
                    Some(base) if !Path::new(path).is_absolute() => base.join(path),
                    _ => std::path::PathBuf::from(path),
                };
                let reader = match open_auto_decoded_file(&resolved) {
                    Ok(r) => r,
                    Err(e) => {
                        return EvalOut::Ok(Val::ResErr(Box::new(Val::Text(format!(
                            "{path}: {e}"
                        )))));
                    }
                };
                read_csv_stream_with_schema(reader, &schema_tt, delimiter, |ci, val| {
                    self.eval_schema_constraint(&schema_tt, &constraints, ci, val, &empty_env)
                })
            }
        };
        match parsed {
            Ok((good, bad)) => EvalOut::Ok(Val::ResOk(Box::new(Val::Tuple(vec![
                Val::Table(good),
                Val::Table(bad),
            ])))),
            Err(msg) => EvalOut::Ok(Val::ResErr(Box::new(Val::Text(msg)))),
        }
    }

    fn eval_read_jsonl(&mut self, schema_name: &str, handle: CapHandle, path: &str) -> EvalOut {
        let Some(cs) = self.prog.find_schema(schema_name) else {
            return EvalOut::Failed(format!("unknown schema `{schema_name}`"));
        };
        let constraints = cs.constraints.clone();
        let schema_tt = cs.decl.schema.clone();
        let empty_env = RTEnv::new();

        let parsed = match handle {
            CapHandle::Fake(idx) => {
                let Some(ff) = self.ew.world.fake_files.get(idx) else {
                    return EvalOut::Ok(Val::ResErr(Box::new(Val::Text(format!(
                        "file not found: {path}"
                    )))));
                };
                let Some((_, content)) = ff.files.iter().find(|(p, _)| p == path) else {
                    return EvalOut::Ok(Val::ResErr(Box::new(Val::Text(format!(
                        "file not found: {path}"
                    )))));
                };
                let content = content.clone();
                let reader = match AutoDecodeReader::new(Cursor::new(content.as_bytes())) {
                    Ok(r) => r,
                    Err(e) => {
                        return EvalOut::Ok(Val::ResErr(Box::new(Val::Text(format!(
                            "{path}: {e}"
                        )))));
                    }
                };
                read_jsonl_stream_with_schema(reader, &schema_tt, |ci, val| {
                    self.eval_schema_constraint(&schema_tt, &constraints, ci, val, &empty_env)
                })
            }
            CapHandle::Real => {
                if !self.ew.live_io {
                    return EvalOut::Ok(Val::ResErr(Box::new(Val::Text(format!(
                        "file I/O disabled in spec mode: {path}"
                    )))));
                }
                let resolved = match &self.ew.work_dir {
                    Some(base) if !Path::new(path).is_absolute() => base.join(path),
                    _ => std::path::PathBuf::from(path),
                };
                let reader = match open_auto_decoded_file(&resolved) {
                    Ok(r) => r,
                    Err(e) => {
                        return EvalOut::Ok(Val::ResErr(Box::new(Val::Text(format!(
                            "{path}: {e}"
                        )))));
                    }
                };
                read_jsonl_stream_with_schema(reader, &schema_tt, |ci, val| {
                    self.eval_schema_constraint(&schema_tt, &constraints, ci, val, &empty_env)
                })
            }
        };
        match parsed {
            Ok((good, bad)) => EvalOut::Ok(Val::ResOk(Box::new(Val::Tuple(vec![
                Val::Table(good),
                Val::Table(bad),
            ])))),
            Err(msg) => EvalOut::Ok(Val::ResErr(Box::new(Val::Text(msg)))),
        }
    }

    fn eval_schema_constraint(
        &mut self,
        schema_tt: &TableTy,
        constraints: &[Option<ExecRowExpr>],
        ci: usize,
        val: &Val,
        empty_env: &RTEnv,
    ) -> bool {
        let Some(Some(re)) = constraints.get(ci) else {
            return true;
        };
        let self_cols = vec![ColSpec {
            name: "__self".to_string(),
            ty: schema_tt.cols[ci].ty.clone(),
            tags: TagSet::empty(),
            bucketed: false,
            agg_kind: AggKind::Raw,
        }];
        matches!(
            self.eval_row_expr(re, &self_cols, std::slice::from_ref(val), empty_env),
            EvalOut::Ok(Val::Bool(true))
        )
    }

    fn write_confined_table(
        &mut self,
        handle: CapHandle,
        full_rel: &str,
        tv: &TableVal,
        fmt: TableWriteFmt,
    ) -> EvalOut {
        let comp = detect_compression_path(full_rel);
        match handle {
            CapHandle::Fake(idx) => {
                let text = match fmt {
                    TableWriteFmt::Csv(delim) => format_csv_table(tv, delim),
                    TableWriteFmt::Jsonl => format_jsonl_table(tv),
                };
                if let Some(ff) = self.ew.world.fake_files.get_mut(idx) {
                    ff.files.push((full_rel.to_string(), text));
                }
                EvalOut::Ok(Val::ResOk(Box::new(Val::Unit)))
            }
            CapHandle::Real => {
                if self.ew.live_io {
                    let out_path = match &self.ew.work_dir {
                        Some(base) => base.join(full_rel),
                        None => std::path::PathBuf::from(full_rel),
                    };
                    if let Some(parent) = out_path.parent()
                        && let Err(e) = fs::create_dir_all(parent)
                    {
                        return EvalOut::Ok(Val::ResErr(Box::new(Val::Text(e.to_string()))));
                    }
                    let res = File::create(&out_path).and_then(|f| {
                        let mut enc = AutoEncodeWriter::new(BufWriter::new(f), comp)?;
                        match fmt {
                            TableWriteFmt::Csv(delim) => write_csv_table(&mut enc, tv, delim)?,
                            TableWriteFmt::Jsonl => write_jsonl_table(&mut enc, tv)?,
                        }
                        enc.finish()?;
                        Ok(())
                    });
                    if let Err(e) = res {
                        return EvalOut::Ok(Val::ResErr(Box::new(Val::Text(e.to_string()))));
                    }
                }
                let text = match fmt {
                    TableWriteFmt::Csv(delim) => format_csv_table(tv, delim),
                    TableWriteFmt::Jsonl => format_jsonl_table(tv),
                };
                self.ew
                    .world
                    .written_files
                    .push((full_rel.to_string(), text));
                EvalOut::Ok(Val::ResOk(Box::new(Val::Unit)))
            }
        }
    }

    fn write_confined_output(
        &mut self,
        handle: CapHandle,
        full_rel: &str,
        content: String,
    ) -> EvalOut {
        match handle {
            CapHandle::Fake(idx) => {
                if let Some(ff) = self.ew.world.fake_files.get_mut(idx) {
                    ff.files.push((full_rel.to_string(), content));
                }
                EvalOut::Ok(Val::ResOk(Box::new(Val::Unit)))
            }
            CapHandle::Real => {
                if self.ew.live_io {
                    let out_path = match &self.ew.work_dir {
                        Some(base) => base.join(full_rel),
                        None => std::path::PathBuf::from(full_rel),
                    };
                    if let Some(parent) = out_path.parent()
                        && let Err(e) = fs::create_dir_all(parent)
                    {
                        return EvalOut::Ok(Val::ResErr(Box::new(Val::Text(e.to_string()))));
                    }
                    let comp = detect_compression_path(full_rel);
                    let write_res: io::Result<()> = if comp == CompressionKind::Plain {
                        fs::write(&out_path, &content)
                    } else {
                        File::create(&out_path).and_then(|f| {
                            let mut enc = AutoEncodeWriter::new(BufWriter::new(f), comp)?;
                            enc.write_all(content.as_bytes())?;
                            enc.finish()?;
                            Ok(())
                        })
                    };
                    if let Err(e) = write_res {
                        return EvalOut::Ok(Val::ResErr(Box::new(Val::Text(e.to_string()))));
                    }
                }
                self.ew
                    .world
                    .written_files
                    .push((full_rel.to_string(), content));
                EvalOut::Ok(Val::ResOk(Box::new(Val::Unit)))
            }
        }
    }

    // -----------------------------------------------------------------------
    // Row Expression & Relational Plan Evaluation (All 21 Operators)
    // -----------------------------------------------------------------------

    fn eval_row_expr(
        &mut self,
        re: &ExecRowExpr,
        cols: &[ColSpec],
        cells: &[Val],
        outer_env: &RTEnv,
    ) -> EvalOut {
        // Tail-iterate `IfE` chains so deep row `else if` cascades run in O(1) call stack.
        let mut cur = re;
        loop {
            match cur {
                ExecRowExpr::Lit(l) => return EvalOut::Ok(eval_literal(l)),
                ExecRowExpr::Col(name) => {
                    return cols
                        .iter()
                        .position(|c| c.name == *name)
                        .and_then(|i| cells.get(i))
                        .cloned()
                        .map_or_else(
                            || EvalOut::Failed(format!("unknown row column `{name}`")),
                            EvalOut::Ok,
                        );
                }
                ExecRowExpr::OuterVar(name) => {
                    return outer_env.get(name).cloned().map_or_else(
                        || EvalOut::Failed(format!("unknown outer variable `{name}`")),
                        EvalOut::Ok,
                    );
                }
                ExecRowExpr::ConstRef(name) => {
                    return self
                        .prog
                        .find_const(name)
                        .map(|c| eval_literal(&c.value))
                        .map_or_else(
                            || EvalOut::Failed(format!("unknown constant `{name}`")),
                            EvalOut::Ok,
                        );
                }
                ExecRowExpr::IfE {
                    cond,
                    then_br,
                    else_br,
                } => match self.eval_row_expr(cond, cols, cells, outer_env) {
                    EvalOut::Ok(Val::Bool(true)) => {
                        cur = then_br;
                        continue;
                    }
                    EvalOut::Ok(Val::Bool(false)) => {
                        cur = else_br;
                        continue;
                    }
                    EvalOut::Ok(_) => {
                        return EvalOut::Failed("non-Bool condition in row `if`".to_string());
                    }
                    other => return other,
                },
                ExecRowExpr::Coalesce {
                    opt_expr,
                    default_expr,
                } => match self.eval_row_expr(opt_expr, cols, cells, outer_env) {
                    EvalOut::Ok(Val::OptSome(ref v)) => return EvalOut::Ok(v.as_ref().clone()),
                    EvalOut::Ok(Val::OptNone) => {
                        cur = default_expr;
                        continue;
                    }
                    EvalOut::Ok(_) => return EvalOut::Failed("coalesce on non-Option".to_string()),
                    other => return other,
                },
                ExecRowExpr::Prim { op, args } => {
                    // Iteratively flatten left-leaning non-short-circuit row primitive chains
                    // (`a + b + c + ...`) so long row expressions run in O(1) call stack.
                    let is_short_circuit = |o: &ExecPrimOp| {
                        matches!(
                            o,
                            ExecPrimOp::Core(PrimOp::AndBool) | ExecPrimOp::Core(PrimOp::OrBool)
                        )
                    };
                    if !is_short_circuit(op)
                        && let Some(ExecRowExpr::Prim { op: inner_op, .. }) = args.first()
                        && !is_short_circuit(inner_op)
                    {
                        let mut chain: Vec<(&ExecPrimOp, &[ExecRowExpr])> = Vec::new();
                        chain.push((op, &args[1..]));
                        let mut base = &args[0];
                        while let ExecRowExpr::Prim {
                            op: iop,
                            args: iargs,
                        } = base
                        {
                            if is_short_circuit(iop) {
                                break;
                            }
                            if let Some(first) = iargs.first() {
                                chain.push((iop, &iargs[1..]));
                                base = first;
                            } else {
                                break;
                            }
                        }
                        let mut acc = match self.eval_row_expr(base, cols, cells, outer_env) {
                            EvalOut::Ok(v) => v,
                            other => return other,
                        };
                        while let Some((pop, rest_args)) = chain.pop() {
                            let mut vals = Vec::with_capacity(1 + rest_args.len());
                            vals.push(acc);
                            for a in rest_args {
                                match self.eval_row_expr(a, cols, cells, outer_env) {
                                    EvalOut::Ok(v) => vals.push(v),
                                    other => return other,
                                }
                            }
                            acc = match self.eval_exec_prim(pop, &vals) {
                                EvalOut::Ok(v) => v,
                                other => return other,
                            };
                        }
                        return EvalOut::Ok(acc);
                    }
                    // Short-circuit `AndBool` and `OrBool`.
                    if matches!(op, ExecPrimOp::Core(PrimOp::AndBool)) && args.len() == 2 {
                        return match self.eval_row_expr(&args[0], cols, cells, outer_env) {
                            EvalOut::Ok(Val::Bool(false)) => EvalOut::Ok(Val::Bool(false)),
                            EvalOut::Ok(Val::Bool(true)) => {
                                self.eval_row_expr(&args[1], cols, cells, outer_env)
                            }
                            EvalOut::Ok(_) => EvalOut::Failed("AndBool non-Bool".to_string()),
                            other => other,
                        };
                    }
                    if matches!(op, ExecPrimOp::Core(PrimOp::OrBool)) && args.len() == 2 {
                        return match self.eval_row_expr(&args[0], cols, cells, outer_env) {
                            EvalOut::Ok(Val::Bool(true)) => EvalOut::Ok(Val::Bool(true)),
                            EvalOut::Ok(Val::Bool(false)) => {
                                self.eval_row_expr(&args[1], cols, cells, outer_env)
                            }
                            EvalOut::Ok(_) => EvalOut::Failed("OrBool non-Bool".to_string()),
                            other => other,
                        };
                    }
                    let mut vals = Vec::with_capacity(args.len());
                    for a in args {
                        match self.eval_row_expr(a, cols, cells, outer_env) {
                            EvalOut::Ok(v) => vals.push(v),
                            other => return other,
                        }
                    }
                    return self.eval_exec_prim(op, &vals);
                }
                ExecRowExpr::CallPure { fn_name, args } => {
                    let mut vals = Vec::with_capacity(args.len());
                    for a in args {
                        match self.eval_row_expr(a, cols, cells, outer_env) {
                            EvalOut::Ok(v) => vals.push(v),
                            other => return other,
                        }
                    }
                    return self.eval_call(fn_name, vals);
                }
            }
        }
    }

    fn eval_plan(&mut self, plan: &ExecPlan, env: &RTEnv) -> EvalOut {
        // Iteratively peel arbitrarily deep unary plan chains so 200,000-stage
        // relational pipelines evaluate in O(1) call stack.
        let mut unary_stack: Vec<&ExecPlan> = Vec::new();
        let mut leaf = plan;
        while let Some(child) = unary_plan_input(leaf) {
            unary_stack.push(leaf);
            leaf = child;
        }
        let mut cur_val = match self.eval_plan_leaf(leaf, env) {
            EvalOut::Ok(v) => v,
            other => return other,
        };
        while let Some(stage) = unary_stack.pop() {
            if let Some(stop) = self.tick() {
                return stop;
            }
            let Some(tv) = cur_val.into_table() else {
                return EvalOut::Failed("plan did not evaluate to Table".to_string());
            };
            cur_val = match self.eval_plan_unary_stage(stage, tv, env) {
                EvalOut::Ok(v) => v,
                other => return other,
            };
        }
        EvalOut::Ok(cur_val)
    }

    fn eval_plan_leaf(&mut self, plan: &ExecPlan, env: &RTEnv) -> EvalOut {
        if let Some(stop) = self.tick() {
            return stop;
        }
        match plan {
            ExecPlan::SourceExpr(e) => self.eval_expr(e, env),
            ExecPlan::SourceDB {
                cap,
                table_name,
                schema,
            } => {
                let cap_v = match self.eval_expr(cap, env) {
                    EvalOut::Ok(v) => v,
                    other => return other,
                };
                match cap_v {
                    Val::CapReadDB {
                        handle: CapHandle::Fake(idx),
                        ..
                    } => {
                        let stored =
                            self.ew.world.fake_dbs.get(idx).and_then(|db| {
                                db.tables.iter().find(|t| t.table_name == *table_name)
                            });
                        match stored {
                            Some(st) => {
                                let rows = st
                                    .rows
                                    .iter()
                                    .map(|r| TableRow {
                                        cells: r.clone(),
                                        group_meta: None,
                                    })
                                    .collect();
                                EvalOut::Ok(Val::Table(TableVal {
                                    cols: schema.cols.clone(),
                                    rows,
                                }))
                            }
                            None => EvalOut::Ok(Val::Table(TableVal {
                                cols: schema.cols.clone(),
                                rows: Vec::new(),
                            })),
                        }
                    }
                    _ => EvalOut::Stopped(Bug {
                        kind: BugKind::OutsideBoundary,
                        message: "live ReadDB queries require Phase 3 database driver".to_string(),
                    }),
                }
            }
            ExecPlan::Union { left, right } => {
                let mut ltv = match self.eval_plan_table(left, env) {
                    Ok(t) => t,
                    Err(out) => return *out,
                };
                let rtv = match self.eval_plan_table(right, env) {
                    Ok(t) => t,
                    Err(out) => return *out,
                };
                ltv.rows.extend(rtv.rows);
                EvalOut::Ok(Val::Table(ltv))
            }
            ExecPlan::Join {
                kind,
                left,
                right,
                on,
                suffixes,
            } => {
                let ltv = match self.eval_plan_table(left, env) {
                    Ok(t) => t,
                    Err(out) => return *out,
                };
                let rtv = match self.eval_plan_table(right, env) {
                    Ok(t) => t,
                    Err(out) => return *out,
                };
                eval_join(*kind, ltv, rtv, on, suffixes.as_ref())
            }
            _ => EvalOut::Failed("unexpected unary stage in eval_plan_leaf".to_string()),
        }
    }

    fn eval_plan_unary_stage(&mut self, stage: &ExecPlan, tv: TableVal, env: &RTEnv) -> EvalOut {
        match stage {
            ExecPlan::Select { cols, .. } => {
                let mut idxs = Vec::with_capacity(cols.len());
                let mut out_cols = Vec::with_capacity(cols.len());
                for c in cols {
                    let Some(i) = tv.cols.iter().position(|cs| cs.name == *c) else {
                        return EvalOut::Failed(format!("select: missing col `{c}`"));
                    };
                    idxs.push(i);
                    out_cols.push(tv.cols[i].clone());
                }
                let rows = tv
                    .rows
                    .iter()
                    .map(|r| TableRow {
                        cells: idxs.iter().map(|&i| r.cells[i].clone()).collect(),
                        group_meta: r.group_meta,
                    })
                    .collect();
                EvalOut::Ok(Val::Table(TableVal {
                    cols: out_cols,
                    rows,
                }))
            }
            ExecPlan::Drop { cols, .. } => {
                let keep: Vec<usize> = tv
                    .cols
                    .iter()
                    .enumerate()
                    .filter(|(_, c)| !cols.contains(&c.name))
                    .map(|(i, _)| i)
                    .collect();
                let out_cols = keep.iter().map(|&i| tv.cols[i].clone()).collect();
                let rows = tv
                    .rows
                    .iter()
                    .map(|r| TableRow {
                        cells: keep.iter().map(|&i| r.cells[i].clone()).collect(),
                        group_meta: r.group_meta,
                    })
                    .collect();
                EvalOut::Ok(Val::Table(TableVal {
                    cols: out_cols,
                    rows,
                }))
            }
            ExecPlan::Rename { pairs, .. } => {
                let mut tv = tv;
                for (old, new) in pairs {
                    if let Some(c) = tv.cols.iter_mut().find(|c| c.name == *old) {
                        c.name = new.clone();
                    }
                }
                EvalOut::Ok(Val::Table(tv))
            }
            ExecPlan::Filter { pred, .. } => {
                let mut kept = Vec::new();
                for row in tv.rows {
                    match self.eval_row_expr(pred, &tv.cols, &row.cells, env) {
                        EvalOut::Ok(Val::Bool(true)) => kept.push(row),
                        EvalOut::Ok(Val::Bool(false)) => {}
                        EvalOut::Ok(_) => {
                            return EvalOut::Failed(
                                "filter predicate returned non-Bool".to_string(),
                            );
                        }
                        other => return other,
                    }
                }
                EvalOut::Ok(Val::Table(TableVal {
                    cols: tv.cols,
                    rows: kept,
                }))
            }
            ExecPlan::Derive { items, .. } => {
                let mut tv = tv;
                for item in items {
                    match item {
                        ExecDeriveItem::ColExpr { name, expr } => {
                            let existing_idx = tv.cols.iter().position(|c| c.name == *name);
                            let mut new_vals = Vec::with_capacity(tv.rows.len());
                            for row in &tv.rows {
                                match self.eval_row_expr(expr, &tv.cols, &row.cells, env) {
                                    EvalOut::Ok(v) => new_vals.push(v),
                                    other => return other,
                                }
                            }
                            if let Some(idx) = existing_idx {
                                for (row, v) in tv.rows.iter_mut().zip(new_vals) {
                                    row.cells[idx] = v;
                                }
                            } else {
                                tv.cols.push(ColSpec {
                                    name: name.clone(),
                                    ty: ScalarTy::Unit,
                                    tags: TagSet::empty(),
                                    bucketed: false,
                                    agg_kind: AggKind::Raw,
                                });
                                for (row, v) in tv.rows.iter_mut().zip(new_vals) {
                                    row.cells.push(v);
                                }
                            }
                        }
                        ExecDeriveItem::BucketCol {
                            name,
                            source,
                            cuts,
                            labels,
                        } => {
                            let Some(src_idx) = tv.cols.iter().position(|c| c.name == *source)
                            else {
                                return EvalOut::Failed(format!("bucket: missing col `{source}`"));
                            };
                            let cut_vals: Vec<Val> = cuts.iter().map(eval_literal).collect();
                            let existing_idx = tv.cols.iter().position(|c| c.name == *name);
                            let mut new_vals = Vec::with_capacity(tv.rows.len());
                            for row in &tv.rows {
                                let v = &row.cells[src_idx];
                                let mut bidx = cut_vals.len();
                                for (i, cv) in cut_vals.iter().enumerate() {
                                    if val_lt(v, cv) {
                                        bidx = i;
                                        break;
                                    }
                                }
                                let lbl = labels.get(bidx).cloned().unwrap_or_default();
                                new_vals.push(Val::Text(lbl));
                            }
                            if let Some(idx) = existing_idx {
                                tv.cols[idx].ty = ScalarTy::Text;
                                tv.cols[idx].bucketed = true;
                                for (row, v) in tv.rows.iter_mut().zip(new_vals) {
                                    row.cells[idx] = v;
                                }
                            } else {
                                tv.cols.push(ColSpec {
                                    name: name.clone(),
                                    ty: ScalarTy::Text,
                                    tags: tv.cols[src_idx].tags.clone(),
                                    bucketed: true,
                                    agg_kind: AggKind::Raw,
                                });
                                for (row, v) in tv.rows.iter_mut().zip(new_vals) {
                                    row.cells.push(v);
                                }
                            }
                        }
                    }
                }
                EvalOut::Ok(Val::Table(tv))
            }
            ExecPlan::Distinct { cols, .. } => {
                let idxs: Vec<usize> = if cols.is_empty() {
                    (0..tv.cols.len()).collect()
                } else {
                    cols.iter()
                        .filter_map(|c| tv.cols.iter().position(|cs| cs.name == *c))
                        .collect()
                };
                let mut seen: Vec<Vec<Val>> = Vec::new();
                let mut out_rows = Vec::new();
                for r in tv.rows {
                    let key: Vec<Val> = idxs.iter().map(|&i| r.cells[i].clone()).collect();
                    if !seen.iter().any(|k| val_list_eq(k, &key)) {
                        seen.push(key);
                        out_rows.push(r);
                    }
                }
                EvalOut::Ok(Val::Table(TableVal {
                    cols: tv.cols,
                    rows: out_rows,
                }))
            }
            ExecPlan::Sort { keys, .. } => {
                let mut tv = tv;
                let key_specs: Vec<(usize, SortDir)> = keys
                    .iter()
                    .filter_map(|(c, d)| {
                        tv.cols.iter().position(|cs| cs.name == *c).map(|i| (i, *d))
                    })
                    .collect();
                tv.rows.sort_by(|a, b| {
                    for &(idx, dir) in &key_specs {
                        let ord = val_cmp(&a.cells[idx], &b.cells[idx]);
                        let directed = match dir {
                            SortDir::Asc => ord,
                            SortDir::Desc => ord.reverse(),
                        };
                        if directed != std::cmp::Ordering::Equal {
                            return directed;
                        }
                    }
                    std::cmp::Ordering::Equal
                });
                EvalOut::Ok(Val::Table(tv))
            }
            ExecPlan::Limit { n, .. } => {
                let mut tv = tv;
                let lim = n.to_u64().unwrap_or(0) as usize;
                tv.rows.truncate(lim);
                EvalOut::Ok(Val::Table(tv))
            }
            ExecPlan::GroupBy { .. } => EvalOut::Ok(Val::Table(tv)),
            ExecPlan::Summarize {
                input,
                aggs,
                distinct_key,
            } => {
                let gkeys = extract_group_keys(input);
                self.eval_summarize(&tv, &gkeys, aggs, distinct_key.as_deref(), env)
            }
            ExecPlan::SuppressSmallGroups {
                min_k,
                distinct_by,
                mode,
                ..
            } => {
                let floor = self
                    .prog
                    .min_group_floor()
                    .max(min_k.clone())
                    .to_u64()
                    .unwrap_or(5) as usize;
                let group_size = |r: &TableRow| -> usize {
                    match (distinct_by, r.group_meta) {
                        (Some(_), Some(m)) => m.distinct_count.unwrap_or(m.row_count),
                        (None, Some(m)) => m.row_count,
                        (_, None) => 0,
                    }
                };
                let out_cols: Vec<ColSpec> = tv
                    .cols
                    .iter()
                    .map(|c| {
                        let mut out = c.clone();
                        if let (
                            SuppressMode::MaskComplementary,
                            AggKind::Blending | AggKind::NonBlending,
                        ) = (mode, c.agg_kind)
                        {
                            out.ty = crate::core::check::ensure_option_scalar(&c.ty);
                            out.bucketed = false;
                        }
                        out
                    })
                    .collect();
                match mode {
                    SuppressMode::Drop => {
                        let kept = tv
                            .rows
                            .into_iter()
                            .filter(|r| group_size(r) >= floor)
                            .map(|r| TableRow {
                                cells: r.cells,
                                group_meta: None,
                            })
                            .collect();
                        EvalOut::Ok(Val::Table(TableVal {
                            cols: out_cols,
                            rows: kept,
                        }))
                    }
                    SuppressMode::MaskComplementary => {
                        let small_sum: usize = tv
                            .rows
                            .iter()
                            .filter(|r| group_size(r) < floor)
                            .map(group_size)
                            .sum();
                        let has_small = tv.rows.iter().any(|r| group_size(r) < floor);
                        let key_idxs: Vec<usize> = tv
                            .cols
                            .iter()
                            .enumerate()
                            .filter(|(_, c)| c.agg_kind == AggKind::GroupKey)
                            .map(|(i, _)| i)
                            .collect();
                        let comp_key: Option<Vec<Val>> = if has_small && small_sum < floor {
                            let mut valid: Vec<&TableRow> =
                                tv.rows.iter().filter(|r| group_size(r) >= floor).collect();
                            valid.sort_by(|a, b| {
                                group_size(a).cmp(&group_size(b)).then_with(|| {
                                    let ka: Vec<Val> =
                                        key_idxs.iter().map(|&i| a.cells[i].clone()).collect();
                                    let kb: Vec<Val> =
                                        key_idxs.iter().map(|&i| b.cells[i].clone()).collect();
                                    if val_list_lt(&ka, &kb) {
                                        std::cmp::Ordering::Less
                                    } else if val_list_lt(&kb, &ka) {
                                        std::cmp::Ordering::Greater
                                    } else {
                                        std::cmp::Ordering::Equal
                                    }
                                })
                            });
                            valid
                                .first()
                                .map(|r| key_idxs.iter().map(|&i| r.cells[i].clone()).collect())
                        } else {
                            None
                        };
                        let out_rows = tv
                            .rows
                            .iter()
                            .map(|r| {
                                let rk: Vec<Val> =
                                    key_idxs.iter().map(|&i| r.cells[i].clone()).collect();
                                let should_mask = group_size(r) < floor
                                    || comp_key.as_ref().is_some_and(|ck| val_list_eq(&rk, ck));
                                let cells = tv
                                    .cols
                                    .iter()
                                    .zip(&r.cells)
                                    .map(|(c, v)| {
                                        if matches!(
                                            c.agg_kind,
                                            AggKind::Blending | AggKind::NonBlending
                                        ) {
                                            if should_mask {
                                                Val::OptNone
                                            } else {
                                                wrap_opt_if_needed(v.clone())
                                            }
                                        } else {
                                            v.clone()
                                        }
                                    })
                                    .collect();
                                TableRow {
                                    cells,
                                    group_meta: None,
                                }
                            })
                            .collect();
                        EvalOut::Ok(Val::Table(TableVal {
                            cols: out_cols,
                            rows: out_rows,
                        }))
                    }
                }
            }
            ExecPlan::Window { items, .. } => eval_window(tv, items),
            ExecPlan::FillGaps {
                col,
                step_micros,
                over,
                fill,
                ..
            } => eval_fill_gaps(tv, col, step_micros.to_i64().unwrap_or(1), over, fill),
            ExecPlan::PivotWider {
                names_from,
                values_from,
                static_cols,
                fill,
                ..
            } => eval_pivot_wider(tv, names_from, values_from, static_cols, eval_literal(fill)),
            ExecPlan::Crosstab {
                rows_col,
                cols_col,
                values_col,
                fill,
                ..
            } => eval_crosstab(tv, rows_col, cols_col, values_col, eval_literal(fill)),
            ExecPlan::Redact {
                col, replacement, ..
            } => {
                let mut tv = tv;
                if let Some(idx) = tv.cols.iter().position(|c| c.name == *col) {
                    tv.cols[idx].ty = ScalarTy::Text;
                    tv.cols[idx].tags = TagSet::empty();
                    for r in &mut tv.rows {
                        r.cells[idx] = Val::Text(replacement.clone());
                    }
                }
                EvalOut::Ok(Val::Table(tv))
            }
            ExecPlan::Pseudonymize { col, secret, .. } => {
                let mut tv = tv;
                let sec_val = match self.eval_expr(secret, env) {
                    EvalOut::Ok(v) => v,
                    other => return other,
                };
                let sec_material = match &sec_val {
                    Val::CapSecret {
                        handle: CapHandle::Fake(idx),
                        ..
                    } => self
                        .ew
                        .world
                        .fake_secrets
                        .get(*idx)
                        .cloned()
                        .unwrap_or_default(),
                    Val::CapSecret {
                        handle: CapHandle::Real,
                        name,
                    } => self
                        .ew
                        .world
                        .real_secrets
                        .iter()
                        .find(|(n, _)| n == name)
                        .map(|(_, v)| v.clone())
                        .or_else(|| std::env::var(name.to_ascii_uppercase()).ok())
                        .unwrap_or_else(|| format!("env:{name}")),
                    _ => String::new(),
                };
                if let Some(idx) = tv.cols.iter().position(|c| c.name == *col) {
                    tv.cols[idx].ty = ScalarTy::Text;
                    tv.cols[idx].tags = tv.cols[idx].tags.remove("pii");
                    let mode = self.ew.pseudonymize_mode;
                    for r in &mut tv.rows {
                        let tok = match mode {
                            PseudonymizeMode::CoreV01Fnv1a => {
                                pseudonymize_token(&sec_material, &r.cells[idx])
                            }
                            PseudonymizeMode::HmacSha256 => {
                                hmac_sha256_pseudonym(sec_material.as_bytes(), &r.cells[idx])
                            }
                        };
                        r.cells[idx] = Val::Text(tok);
                    }
                }
                EvalOut::Ok(Val::Table(tv))
            }
            _ => EvalOut::Failed("unexpected leaf in eval_plan_unary_stage".to_string()),
        }
    }

    fn eval_plan_table(&mut self, plan: &ExecPlan, env: &RTEnv) -> Result<TableVal, Box<EvalOut>> {
        match self.eval_plan(plan, env) {
            EvalOut::Ok(v) => v.into_table().ok_or_else(|| {
                Box::new(EvalOut::Failed(
                    "plan did not evaluate to Table".to_string(),
                ))
            }),
            other => Err(Box::new(other)),
        }
    }

    fn eval_summarize(
        &mut self,
        tv: &TableVal,
        gkeys: &[Ident],
        aggs: &[ExecAggItem],
        distinct_key: Option<&str>,
        env: &RTEnv,
    ) -> EvalOut {
        let gidxs: Vec<usize> = gkeys
            .iter()
            .filter_map(|k| tv.cols.iter().position(|c| c.name == *k))
            .collect();
        let dk_idx = distinct_key.and_then(|k| tv.cols.iter().position(|c| c.name == k));

        // Partition rows into groups preserving first-seen key order.
        let mut groups: Vec<(Vec<Val>, Vec<&TableRow>)> = Vec::new();
        if gkeys.is_empty() {
            if !tv.rows.is_empty() || !aggs.is_empty() {
                groups.push((Vec::new(), tv.rows.iter().collect()));
            }
        } else {
            for row in &tv.rows {
                let key: Vec<Val> = gidxs.iter().map(|&i| row.cells[i].clone()).collect();
                if let Some((_, rows)) = groups.iter_mut().find(|(k, _)| val_list_eq(k, &key)) {
                    rows.push(row);
                } else {
                    groups.push((key, vec![row]));
                }
            }
        }

        let mut out_cols: Vec<ColSpec> = gidxs
            .iter()
            .map(|&i| {
                let mut c = tv.cols[i].clone();
                c.agg_kind = AggKind::GroupKey;
                c
            })
            .collect();
        for agg in aggs {
            out_cols.push(ColSpec {
                name: agg.name.clone(),
                ty: ScalarTy::Unit,
                tags: TagSet::empty(),
                bucketed: false,
                agg_kind: if agg.op.is_blending() {
                    AggKind::Blending
                } else {
                    AggKind::NonBlending
                },
            });
        }

        let mut out_rows = Vec::with_capacity(groups.len());
        for (gkey_vals, group_rows) in groups {
            let mut cells = gkey_vals;
            let distinct_count = dk_idx.map(|didx| {
                let mut seen: Vec<&Val> = Vec::new();
                for r in &group_rows {
                    let v = &r.cells[didx];
                    if !matches!(v, Val::OptNone) && !seen.iter().any(|x| val_eq(x, v)) {
                        seen.push(v);
                    }
                }
                seen.len()
            });

            for agg in aggs {
                let mut arg_vals = Vec::with_capacity(group_rows.len());
                if let Some(re) = &agg.arg {
                    for r in &group_rows {
                        match self.eval_row_expr(re, &tv.cols, &r.cells, env) {
                            EvalOut::Ok(v) => arg_vals.push(v),
                            other => return other,
                        }
                    }
                }
                match eval_agg_values(agg.op, &arg_vals, group_rows.len()) {
                    EvalOut::Ok(v) => cells.push(v),
                    other => return other,
                }
            }

            out_rows.push(TableRow {
                cells,
                group_meta: Some(GroupMeta {
                    row_count: group_rows.len(),
                    distinct_count,
                }),
            });
        }

        EvalOut::Ok(Val::Table(TableVal {
            cols: out_cols,
            rows: out_rows,
        }))
    }
}

fn extract_group_keys(plan: &ExecPlan) -> Vec<Ident> {
    match plan {
        ExecPlan::GroupBy { keys, .. } => keys.clone(),
        _ => Vec::new(),
    }
}

fn eval_agg_values(op: AggOp, vals: &[Val], row_count: usize) -> EvalOut {
    match op {
        AggOp::Count => EvalOut::Ok(Val::Int(BigInt::from(row_count))),
        AggOp::CountDistinct => {
            let mut seen: Vec<&Val> = Vec::new();
            for v in vals {
                let inner = unwrap_opt_ref(v);
                if let Some(iv) = inner
                    && !seen.iter().any(|x| val_eq(x, iv))
                {
                    seen.push(iv);
                }
            }
            EvalOut::Ok(Val::Int(BigInt::from(seen.len())))
        }
        AggOp::Sum => {
            let non_null: Vec<&Val> = vals.iter().filter_map(unwrap_opt_ref).collect();
            if non_null.is_empty() {
                return EvalOut::Ok(Val::Int(BigInt::ZERO));
            }
            match non_null[0] {
                Val::Int(_) => {
                    let mut acc = BigInt::ZERO;
                    for v in non_null {
                        if let Val::Int(n) = v {
                            acc = &acc + n;
                        }
                    }
                    if acc.in_int64_range() {
                        EvalOut::Ok(Val::Int(acc))
                    } else {
                        EvalOut::Stopped(Bug {
                            kind: BugKind::IntOverflow,
                            message: "sum Int64 overflow".to_string(),
                        })
                    }
                }
                Val::Decimal(_) => {
                    let mut acc = BigInt::ZERO;
                    for v in non_null {
                        if let Val::Decimal(d) = v {
                            acc = &acc + d;
                        }
                    }
                    if acc.in_decimal_range() {
                        EvalOut::Ok(Val::Decimal(acc))
                    } else {
                        EvalOut::Stopped(Bug {
                            kind: BugKind::DecimalOverflow,
                            message: "sum Decimal overflow".to_string(),
                        })
                    }
                }
                Val::Float(_) => {
                    let s: f64 = non_null
                        .iter()
                        .filter_map(|v| match v {
                            Val::Float(f) => Some(f.to_f64()),
                            _ => None,
                        })
                        .sum();
                    EvalOut::Ok(Val::Float(Float64::from_f64(s)))
                }
                _ => EvalOut::Failed("sum on non-numeric column".to_string()),
            }
        }
        AggOp::Mean => {
            let non_null: Vec<&Val> = vals.iter().filter_map(unwrap_opt_ref).collect();
            if non_null.is_empty() {
                return EvalOut::Ok(Val::OptNone);
            }
            match non_null[0] {
                Val::Decimal(_) => {
                    let mut acc = BigInt::ZERO;
                    for v in &non_null {
                        if let Val::Decimal(d) = v {
                            acc = &acc + d;
                        }
                    }
                    let q = if acc.is_negative() {
                        -acc.abs()
                            .div_euclid(&BigInt::from(non_null.len()))
                            .unwrap_or(BigInt::ZERO)
                    } else {
                        acc.div_euclid(&BigInt::from(non_null.len()))
                            .unwrap_or(BigInt::ZERO)
                    };
                    EvalOut::Ok(Val::OptSome(Box::new(Val::Decimal(q))))
                }
                _ => {
                    let fs = to_f64_vec(&non_null);
                    let m = fs.iter().sum::<f64>() / (fs.len() as f64);
                    EvalOut::Ok(Val::OptSome(Box::new(Val::Float(Float64::from_f64(m)))))
                }
            }
        }
        AggOp::Stddev | AggOp::Variance => {
            let non_null: Vec<&Val> = vals.iter().filter_map(unwrap_opt_ref).collect();
            if non_null.len() < 2 {
                return EvalOut::Ok(Val::OptNone);
            }
            let fs = to_f64_vec(&non_null);
            let mean = fs.iter().sum::<f64>() / (fs.len() as f64);
            let var =
                fs.iter().map(|&x| (x - mean) * (x - mean)).sum::<f64>() / ((fs.len() - 1) as f64);
            let res = if matches!(op, AggOp::Stddev) {
                var.sqrt()
            } else {
                var
            };
            EvalOut::Ok(Val::OptSome(Box::new(Val::Float(Float64::from_f64(res)))))
        }
        AggOp::Median | AggOp::Percentile(_) => {
            let non_null: Vec<&Val> = vals.iter().filter_map(unwrap_opt_ref).collect();
            if non_null.is_empty() {
                return EvalOut::Ok(Val::OptNone);
            }
            let mut fs = to_f64_vec(&non_null);
            fs.sort_by(|a, b| a.total_cmp(b));
            let q = match op {
                AggOp::Percentile(f) => f.to_f64().clamp(0.0, 1.0),
                _ => 0.5,
            };
            let pos = q * ((fs.len() - 1) as f64);
            let lo = pos.floor() as usize;
            let hi = pos.ceil() as usize;
            let frac = pos - (lo as f64);
            let interp = fs[lo] * (1.0 - frac) + fs[hi] * frac;
            EvalOut::Ok(Val::OptSome(Box::new(Val::Float(Float64::from_f64(
                interp,
            )))))
        }
        AggOp::Min => {
            let non_null: Vec<&Val> = vals.iter().filter_map(unwrap_opt_ref).collect();
            match non_null.into_iter().min_by(|a, b| val_cmp(a, b)) {
                Some(v) => EvalOut::Ok(Val::OptSome(Box::new(v.clone()))),
                None => EvalOut::Ok(Val::OptNone),
            }
        }
        AggOp::Max => {
            let non_null: Vec<&Val> = vals.iter().filter_map(unwrap_opt_ref).collect();
            match non_null.into_iter().max_by(|a, b| val_cmp(a, b)) {
                Some(v) => EvalOut::Ok(Val::OptSome(Box::new(v.clone()))),
                None => EvalOut::Ok(Val::OptNone),
            }
        }
        AggOp::First => match vals.first().and_then(unwrap_opt_ref) {
            Some(v) => EvalOut::Ok(Val::OptSome(Box::new(v.clone()))),
            None => EvalOut::Ok(Val::OptNone),
        },
        AggOp::Last => match vals.last().and_then(unwrap_opt_ref) {
            Some(v) => EvalOut::Ok(Val::OptSome(Box::new(v.clone()))),
            None => EvalOut::Ok(Val::OptNone),
        },
    }
}

fn eval_table_col_agg(tv: &TableVal, col: &str, op: AggOp) -> EvalOut {
    let Some(idx) = tv.cols.iter().position(|c| c.name == col) else {
        return EvalOut::Failed(format!("unknown column `{col}`"));
    };
    let vals: Vec<Val> = tv.rows.iter().map(|r| r.cells[idx].clone()).collect();
    // Preserve Decimal(0) for empty Decimal table `sum(.amount)`!
    if matches!(op, AggOp::Sum) && vals.is_empty() {
        return match &tv.cols[idx].ty {
            ScalarTy::Decimal => EvalOut::Ok(Val::Decimal(BigInt::ZERO)),
            ScalarTy::Float => EvalOut::Ok(Val::Float(Float64::ZERO)),
            _ => EvalOut::Ok(Val::Int(BigInt::ZERO)),
        };
    }
    eval_agg_values(op, &vals, tv.rows.len())
}

fn unary_plan_input(plan: &ExecPlan) -> Option<&ExecPlan> {
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
        | ExecPlan::Crosstab { input, .. }
        | ExecPlan::Redact { input, .. }
        | ExecPlan::Pseudonymize { input, .. } => Some(input),
        ExecPlan::SourceExpr(_)
        | ExecPlan::SourceDB { .. }
        | ExecPlan::Join { .. }
        | ExecPlan::Union { .. } => None,
    }
}

fn eval_join(
    kind: JoinKind,
    ltv: TableVal,
    rtv: TableVal,
    on: &JoinOn,
    suffixes: Option<&(String, String)>,
) -> EvalOut {
    let pairs: Vec<(usize, usize)> = match on {
        JoinOn::SameKeys(ks) => ks
            .iter()
            .filter_map(|k| {
                Some((
                    ltv.cols.iter().position(|c| c.name == *k)?,
                    rtv.cols.iter().position(|c| c.name == *k)?,
                ))
            })
            .collect(),
        JoinOn::Pairs(ps) => ps
            .iter()
            .filter_map(|(lk, rk)| {
                Some((
                    ltv.cols.iter().position(|c| c.name == *lk)?,
                    rtv.cols.iter().position(|c| c.name == *rk)?,
                ))
            })
            .collect(),
    };

    if matches!(kind, JoinKind::Semi | JoinKind::Anti) {
        let mut rows = Vec::new();
        for lr in &ltv.rows {
            let lkey: Vec<Val> = pairs.iter().map(|&(li, _)| lr.cells[li].clone()).collect();
            let matched = rtv.rows.iter().any(|rr| {
                let rkey: Vec<Val> = pairs.iter().map(|&(_, ri)| rr.cells[ri].clone()).collect();
                val_list_eq(&lkey, &rkey)
            });
            if (kind == JoinKind::Semi && matched) || (kind == JoinKind::Anti && !matched) {
                rows.push(lr.clone());
            }
        }
        return EvalOut::Ok(Val::Table(TableVal {
            cols: ltv.cols,
            rows,
        }));
    }

    let is_left = matches!(kind, JoinKind::LeftOne | JoinKind::LeftManyToOne);
    let check_right_unique = matches!(
        kind,
        JoinKind::InnerOne | JoinKind::InnerManyToOne | JoinKind::LeftOne | JoinKind::LeftManyToOne
    );
    let check_left_unique = matches!(kind, JoinKind::InnerOne | JoinKind::LeftOne);

    // Check right-key uniqueness on matched or all right keys when required.
    let right_skip: Vec<usize> = match on {
        JoinOn::SameKeys(ks) => ks
            .iter()
            .filter_map(|k| rtv.cols.iter().position(|c| c.name == *k))
            .collect(),
        JoinOn::Pairs(_) => Vec::new(),
    };
    let left_names: std::collections::HashSet<&str> =
        ltv.cols.iter().map(|c| c.name.as_str()).collect();
    let mut out_cols = Vec::new();
    for lc in &ltv.cols {
        let mut c = lc.clone();
        let collides = rtv
            .cols
            .iter()
            .enumerate()
            .any(|(ri, rc)| !right_skip.contains(&ri) && rc.name == c.name);
        if collides && let Some((ls, _)) = suffixes {
            c.name.push_str(ls);
        }
        out_cols.push(c);
    }
    let mut right_keep = Vec::new();
    for (ri, rc) in rtv.cols.iter().enumerate() {
        if right_skip.contains(&ri) {
            continue;
        }
        right_keep.push(ri);
        let mut c = rc.clone();
        if left_names.contains(c.name.as_str())
            && let Some((_, rs)) = suffixes
        {
            c.name.push_str(rs);
        }
        out_cols.push(c);
    }

    let mut matched_right_idxs: Vec<usize> = Vec::new();
    let mut out_rows = Vec::new();
    for lr in &ltv.rows {
        let lkey: Vec<Val> = pairs.iter().map(|&(li, _)| lr.cells[li].clone()).collect();
        let matches: Vec<(usize, &TableRow)> = rtv
            .rows
            .iter()
            .enumerate()
            .filter(|(_, rr)| {
                let rkey: Vec<Val> = pairs.iter().map(|&(_, ri)| rr.cells[ri].clone()).collect();
                val_list_eq(&lkey, &rkey)
            })
            .collect();

        if check_right_unique && matches.len() > 1 {
            return EvalOut::Stopped(Bug {
                kind: BugKind::JoinCardinality,
                message: "join cardinality violated: multiple right rows matched key".to_string(),
            });
        }
        if matches.is_empty() {
            if is_left {
                let mut cells = lr.cells.clone();
                for _ in &right_keep {
                    cells.push(Val::OptNone);
                }
                out_rows.push(TableRow {
                    cells,
                    group_meta: None,
                });
            }
        } else {
            for (ridx, rr) in matches {
                if check_left_unique && matched_right_idxs.contains(&ridx) {
                    return EvalOut::Stopped(Bug {
                        kind: BugKind::JoinCardinality,
                        message: "1:1 join cardinality violated: multiple left rows matched same right row".to_string(),
                    });
                }
                matched_right_idxs.push(ridx);
                let mut cells = lr.cells.clone();
                for &ri in &right_keep {
                    let rv = rr.cells[ri].clone();
                    if is_left && !matches!(rv, Val::OptNone | Val::OptSome(_)) {
                        cells.push(Val::OptSome(Box::new(rv)));
                    } else {
                        cells.push(rv);
                    }
                }
                out_rows.push(TableRow {
                    cells,
                    group_meta: None,
                });
            }
        }
    }

    EvalOut::Ok(Val::Table(TableVal {
        cols: out_cols,
        rows: out_rows,
    }))
}

fn eval_window(mut tv: TableVal, items: &[WindowItem]) -> EvalOut {
    for item in items {
        let over_idxs: Vec<usize> = item
            .over
            .iter()
            .filter_map(|c| tv.cols.iter().position(|cs| cs.name == *c))
            .collect();
        let order_specs: Vec<(usize, SortDir)> = item
            .order
            .iter()
            .filter_map(|(c, d)| tv.cols.iter().position(|cs| cs.name == *c).map(|i| (i, *d)))
            .collect();

        // Partition row indices by `over` keys.
        let mut parts: Vec<(Vec<Val>, Vec<usize>)> = Vec::new();
        for (ridx, row) in tv.rows.iter().enumerate() {
            let key: Vec<Val> = over_idxs.iter().map(|&i| row.cells[i].clone()).collect();
            if let Some((_, list)) = parts.iter_mut().find(|(k, _)| val_list_eq(k, &key)) {
                list.push(ridx);
            } else {
                parts.push((key, vec![ridx]));
            }
        }

        let mut results: Vec<Val> = vec![Val::OptNone; tv.rows.len()];
        for (_, mut ridxs) in parts {
            if !order_specs.is_empty() {
                ridxs.sort_by(|&ia, &ib| {
                    for &(cidx, dir) in &order_specs {
                        let o = val_cmp(&tv.rows[ia].cells[cidx], &tv.rows[ib].cells[cidx]);
                        let d = match dir {
                            SortDir::Asc => o,
                            SortDir::Desc => o.reverse(),
                        };
                        if d != std::cmp::Ordering::Equal {
                            return d;
                        }
                    }
                    std::cmp::Ordering::Equal
                });
            }
            for (pos, &ridx) in ridxs.iter().enumerate() {
                let v = match &item.win_fn {
                    WindowFn::RowNumber => Val::Int(BigInt::from(pos + 1)),
                    WindowFn::Lag { col, offset } => {
                        let off = offset.to_u64().unwrap_or(1) as usize;
                        let Some(cidx) = tv.cols.iter().position(|c| c.name == *col) else {
                            return EvalOut::Failed(format!("lag: missing col `{col}`"));
                        };
                        if pos >= off {
                            wrap_opt_if_needed(tv.rows[ridxs[pos - off]].cells[cidx].clone())
                        } else {
                            Val::OptNone
                        }
                    }
                    WindowFn::Lead { col, offset } => {
                        let off = offset.to_u64().unwrap_or(1) as usize;
                        let Some(cidx) = tv.cols.iter().position(|c| c.name == *col) else {
                            return EvalOut::Failed(format!("lead: missing col `{col}`"));
                        };
                        if pos + off < ridxs.len() {
                            wrap_opt_if_needed(tv.rows[ridxs[pos + off]].cells[cidx].clone())
                        } else {
                            Val::OptNone
                        }
                    }
                    WindowFn::Rank { col } => {
                        let Some(cidx) = tv.cols.iter().position(|c| c.name == *col) else {
                            return EvalOut::Failed(format!("rank: missing col `{col}`"));
                        };
                        let cur = &tv.rows[ridx].cells[cidx];
                        let rank = ridxs
                            .iter()
                            .take(pos)
                            .filter(|&&prev| val_lt(&tv.rows[prev].cells[cidx], cur))
                            .count()
                            + 1;
                        Val::Int(BigInt::from(rank))
                    }
                    WindowFn::RunningSum { col } => {
                        let Some(cidx) = tv.cols.iter().position(|c| c.name == *col) else {
                            return EvalOut::Failed(format!("running_sum: missing col `{col}`"));
                        };
                        let slice: Vec<Val> = ridxs[..=pos]
                            .iter()
                            .map(|&i| tv.rows[i].cells[cidx].clone())
                            .collect();
                        match eval_agg_values(AggOp::Sum, &slice, slice.len()) {
                            EvalOut::Ok(s) => s,
                            other => return other,
                        }
                    }
                    WindowFn::RollingMean { col, window_size } => {
                        let Some(cidx) = tv.cols.iter().position(|c| c.name == *col) else {
                            return EvalOut::Failed(format!("rolling_mean: missing col `{col}`"));
                        };
                        let w = window_size.to_u64().unwrap_or(1).max(1) as usize;
                        let start = (pos + 1).saturating_sub(w);
                        let slice: Vec<Val> = ridxs[start..=pos]
                            .iter()
                            .map(|&i| tv.rows[i].cells[cidx].clone())
                            .collect();
                        let non_null: Vec<&Val> = slice.iter().filter_map(unwrap_opt_ref).collect();
                        if non_null.is_empty() {
                            Val::OptNone
                        } else {
                            let fs = to_f64_vec(&non_null);
                            let m = fs.iter().sum::<f64>() / (fs.len() as f64);
                            Val::OptSome(Box::new(Val::Float(Float64::from_f64(m))))
                        }
                    }
                };
                results[ridx] = v;
            }
        }

        tv.cols.push(ColSpec {
            name: item.name.clone(),
            ty: ScalarTy::Unit,
            tags: TagSet::empty(),
            bucketed: false,
            agg_kind: AggKind::Raw,
        });
        for (row, val) in tv.rows.iter_mut().zip(results) {
            row.cells.push(val);
        }
    }
    EvalOut::Ok(Val::Table(tv))
}

fn eval_fill_gaps(
    tv: TableVal,
    col: &str,
    step_micros: i64,
    over: &[Ident],
    fill: &[(Ident, Literal)],
) -> EvalOut {
    let Some(t_idx) = tv.cols.iter().position(|c| c.name == col) else {
        return EvalOut::Failed(format!("fill_gaps: missing col `{col}`"));
    };
    if step_micros <= 0 || tv.rows.is_empty() {
        return EvalOut::Ok(Val::Table(tv));
    }
    let over_idxs: Vec<usize> = over
        .iter()
        .filter_map(|c| tv.cols.iter().position(|cs| cs.name == *c))
        .collect();
    let fill_map: HashMap<&str, Val> = fill
        .iter()
        .map(|(k, l)| (k.as_str(), eval_literal(l)))
        .collect();

    let mut groups: Vec<(Vec<Val>, Vec<&TableRow>)> = Vec::new();
    for r in &tv.rows {
        let key: Vec<Val> = over_idxs.iter().map(|&i| r.cells[i].clone()).collect();
        if let Some((_, list)) = groups.iter_mut().find(|(k, _)| val_list_eq(k, &key)) {
            list.push(r);
        } else {
            groups.push((key, vec![r]));
        }
    }

    let mut out_rows = Vec::new();
    for (gkey, grows) in groups {
        let ts_vals: Vec<i64> = grows
            .iter()
            .filter_map(|r| match &r.cells[t_idx] {
                Val::Timestamp(t) => t.to_i64(),
                Val::Date(d) => d.to_i64(),
                _ => None,
            })
            .collect();
        let (Some(&min_t), Some(&max_t)) = (ts_vals.iter().min(), ts_vals.iter().max()) else {
            for r in grows {
                out_rows.push(r.clone());
            }
            continue;
        };
        let is_date = matches!(grows[0].cells[t_idx], Val::Date(_));
        let mut cur = min_t;
        while cur <= max_t {
            let t_val = if is_date {
                Val::Date(BigInt::from(cur))
            } else {
                Val::Timestamp(BigInt::from(cur))
            };
            if let Some(existing) = grows.iter().find(|r| val_eq(&r.cells[t_idx], &t_val)) {
                out_rows.push((*existing).clone());
            } else {
                let mut cells = Vec::with_capacity(tv.cols.len());
                for (ci, cs) in tv.cols.iter().enumerate() {
                    if ci == t_idx {
                        cells.push(t_val.clone());
                    } else if let Some(pos) = over_idxs.iter().position(|&oi| oi == ci) {
                        cells.push(gkey[pos].clone());
                    } else if let Some(fv) = fill_map.get(cs.name.as_str()) {
                        cells.push(fv.clone());
                    } else {
                        cells.push(Val::OptNone);
                    }
                }
                out_rows.push(TableRow {
                    cells,
                    group_meta: None,
                });
            }
            match cur.checked_add(step_micros) {
                Some(n) => cur = n,
                None => break,
            }
        }
    }

    EvalOut::Ok(Val::Table(TableVal {
        cols: tv.cols,
        rows: out_rows,
    }))
}

fn eval_pivot_wider(
    tv: TableVal,
    names_from: &str,
    values_from: &str,
    static_cols: &[Ident],
    fill: Val,
) -> EvalOut {
    let (Some(n_idx), Some(v_idx)) = (
        tv.cols.iter().position(|c| c.name == names_from),
        tv.cols.iter().position(|c| c.name == values_from),
    ) else {
        return EvalOut::Failed("pivot_wider: missing names_from/values_from".to_string());
    };
    let key_idxs: Vec<usize> = (0..tv.cols.len())
        .filter(|&i| i != n_idx && i != v_idx)
        .collect();
    let mut out_cols: Vec<ColSpec> = key_idxs.iter().map(|&i| tv.cols[i].clone()).collect();
    let val_spec = tv.cols[v_idx].clone();
    for sc in static_cols {
        out_cols.push(ColSpec {
            name: sc.clone(),
            ty: val_spec.ty.clone(),
            tags: val_spec.tags.clone(),
            bucketed: false,
            agg_kind: AggKind::Raw,
        });
    }

    let mut groups: Vec<(Vec<Val>, Vec<Val>)> = Vec::new();
    for r in &tv.rows {
        let key: Vec<Val> = key_idxs.iter().map(|&i| r.cells[i].clone()).collect();
        let col_name = format_display_val(&r.cells[n_idx]);
        let cell_val = r.cells[v_idx].clone();
        let entry = if let Some((_, vals)) = groups.iter_mut().find(|(k, _)| val_list_eq(k, &key)) {
            vals
        } else {
            groups.push((key, vec![fill.clone(); static_cols.len()]));
            let last_idx = groups.len() - 1;
            &mut groups[last_idx].1
        };
        if let Some(pos) = static_cols.iter().position(|c| *c == col_name) {
            entry[pos] = cell_val;
        }
    }

    let out_rows = groups
        .into_iter()
        .map(|(mut k, vals)| {
            k.extend(vals);
            TableRow {
                cells: k,
                group_meta: None,
            }
        })
        .collect();
    EvalOut::Ok(Val::Table(TableVal {
        cols: out_cols,
        rows: out_rows,
    }))
}

fn eval_crosstab(
    tv: TableVal,
    rows_col: &str,
    cols_col: &str,
    values_col: &str,
    fill: Val,
) -> EvalOut {
    let (Some(ri), Some(ci), Some(vi)) = (
        tv.cols.iter().position(|c| c.name == rows_col),
        tv.cols.iter().position(|c| c.name == cols_col),
        tv.cols.iter().position(|c| c.name == values_col),
    ) else {
        return EvalOut::Failed("crosstab: missing columns".to_string());
    };
    let mut dyn_cols: Vec<String> = Vec::new();
    for r in &tv.rows {
        let cname = format_display_val(&r.cells[ci]);
        if !dyn_cols.contains(&cname) {
            dyn_cols.push(cname);
        }
    }
    dyn_cols.sort();
    let mut headers = vec![rows_col.to_string()];
    headers.extend(dyn_cols.iter().cloned());

    let mut row_keys: Vec<Val> = Vec::new();
    for r in &tv.rows {
        if !row_keys.iter().any(|k| val_eq(k, &r.cells[ri])) {
            row_keys.push(r.cells[ri].clone());
        }
    }
    row_keys.sort_by(val_cmp);

    let mut out_rows = Vec::with_capacity(row_keys.len());
    for rk in row_keys {
        let mut cells = vec![rk.clone()];
        for dc in &dyn_cols {
            let found = tv
                .rows
                .iter()
                .find(|r| val_eq(&r.cells[ri], &rk) && format_display_val(&r.cells[ci]) == *dc);
            cells.push(found.map_or_else(|| fill.clone(), |r| r.cells[vi].clone()));
        }
        out_rows.push(cells);
    }
    EvalOut::Ok(Val::DynTable {
        headers,
        rows: out_rows,
    })
}

fn eval_welch_t_test(a: &TableVal, b: &TableVal, col: &str) -> EvalOut {
    let (Some(ia), Some(ib)) = (
        a.cols.iter().position(|c| c.name == col),
        b.cols.iter().position(|c| c.name == col),
    ) else {
        return EvalOut::Failed(format!("Stats.t_test: missing column `{col}`"));
    };
    let xa: Vec<f64> = a
        .rows
        .iter()
        .filter_map(|r| unwrap_opt_ref(&r.cells[ia]).and_then(val_to_f64))
        .collect();
    let xb: Vec<f64> = b
        .rows
        .iter()
        .filter_map(|r| unwrap_opt_ref(&r.cells[ib]).and_then(val_to_f64))
        .collect();
    if xa.len() < 2 || xb.len() < 2 {
        return EvalOut::Ok(Val::StatTest {
            stat: Float64::CANONICAL_NAN,
            p_value: Float64::CANONICAL_NAN,
        });
    }
    let na = xa.len() as f64;
    let nb = xb.len() as f64;
    let ma = xa.iter().sum::<f64>() / na;
    let mb = xb.iter().sum::<f64>() / nb;
    let va = xa.iter().map(|&x| (x - ma) * (x - ma)).sum::<f64>() / (na - 1.0);
    let vb = xb.iter().map(|&x| (x - mb) * (x - mb)).sum::<f64>() / (nb - 1.0);
    let se2 = va / na + vb / nb;
    if se2 == 0.0 {
        return EvalOut::Ok(Val::StatTest {
            stat: Float64::ZERO,
            p_value: Float64::from_f64(1.0),
        });
    }
    let t = (ma - mb) / se2.sqrt();
    let df_num = se2 * se2;
    let df_den = (va / na).powi(2) / (na - 1.0) + (vb / nb).powi(2) / (nb - 1.0);
    let df = if df_den > 0.0 {
        df_num / df_den
    } else {
        na + nb - 2.0
    };
    let p_val = student_t_two_tailed_p(t.abs(), df);
    EvalOut::Ok(Val::StatTest {
        stat: Float64::from_f64(t),
        p_value: Float64::from_f64(p_val),
    })
}

/// Two-tailed Student-t p-value via regularized incomplete beta `I_{df/(df+t^2)}(df/2, 1/2)`.
fn student_t_two_tailed_p(t_abs: f64, df: f64) -> f64 {
    if !t_abs.is_finite() || df <= 0.0 {
        return f64::NAN;
    }
    let x = df / (df + t_abs * t_abs);
    reg_incomplete_beta(df * 0.5, 0.5, x).clamp(0.0, 1.0)
}

fn reg_incomplete_beta(a: f64, b: f64, x: f64) -> f64 {
    if x <= 0.0 {
        return 0.0;
    }
    if x >= 1.0 {
        return 1.0;
    }
    let bt = (ln_gamma(a + b) - ln_gamma(a) - ln_gamma(b) + a * x.ln() + b * (1.0 - x).ln()).exp();
    if x < (a + 1.0) / (a + b + 2.0) {
        bt * betacf(a, b, x) / a
    } else {
        1.0 - bt * betacf(b, a, 1.0 - x) / b
    }
}

fn betacf(a: f64, b: f64, x: f64) -> f64 {
    let mut qab = a + b;
    let mut qap = a + 1.0;
    let mut qam = a - 1.0;
    let mut c = 1.0f64;
    let mut d = 1.0 - qab * x / qap;
    if d.abs() < 1e-30 {
        d = 1e-30;
    }
    d = 1.0 / d;
    let mut h = d;
    for m in 1..=200 {
        let mf = f64::from(m);
        let m2 = 2.0 * mf;
        let aa = mf * (b - mf) * x / ((qam + m2) * (a + m2));
        d = 1.0 + aa * d;
        if d.abs() < 1e-30 {
            d = 1e-30;
        }
        c = 1.0 + aa / c;
        if c.abs() < 1e-30 {
            c = 1e-30;
        }
        d = 1.0 / d;
        h *= d * c;
        let aa2 = -(a + mf) * (qab + mf) * x / ((a + m2) * (qap + m2));
        d = 1.0 + aa2 * d;
        if d.abs() < 1e-30 {
            d = 1e-30;
        }
        c = 1.0 + aa2 / c;
        if c.abs() < 1e-30 {
            c = 1e-30;
        }
        d = 1.0 / d;
        let del = d * c;
        h *= del;
        if (del - 1.0).abs() < 1e-12 {
            break;
        }
    }
    let _ = (&mut qab, &mut qap, &mut qam);
    h
}

/// Lanczos approximation for `ln(Gamma(z))`.
fn ln_gamma(z: f64) -> f64 {
    const COEFFS: [f64; 9] = [
        0.999_999_999_999_809_9,
        676.520_368_121_885_1,
        -1_259.139_216_722_402_8,
        771.323_428_777_653_1,
        -176.615_029_162_140_6,
        12.507_343_278_686_905,
        -0.138_571_095_265_720_12,
        9.984_369_578_019_572e-6,
        1.505_632_735_149_311_6e-7,
    ];
    let z = z - 1.0;
    let mut x = COEFFS[0];
    for (i, &c) in COEFFS.iter().enumerate().skip(1) {
        x += c / (z + i as f64);
    }
    let t = z + 7.5;
    0.5 * (2.0 * std::f64::consts::PI).ln() + (z + 0.5) * t.ln() - t + x.ln()
}

fn match_pattern(pat: &ExecPattern, val: &Val) -> Option<Vec<(Ident, Val)>> {
    match pat {
        ExecPattern::Wildcard => Some(Vec::new()),
        ExecPattern::Bind(name) => Some(vec![(name.clone(), val.clone())]),
        ExecPattern::Lit(l) => {
            if val_eq(&eval_literal(l), val) {
                Some(Vec::new())
            } else {
                None
            }
        }
        ExecPattern::ListExact(binders) => match val {
            Val::List(xs) if xs.len() == binders.len() => {
                Some(binders.iter().cloned().zip(xs.iter().cloned()).collect())
            }
            _ => None,
        },
        ExecPattern::Ctor { ctor, binders } => match (ctor.as_str(), val) {
            ("Ok", Val::ResOk(v)) if binders.len() == 1 => {
                Some(vec![(binders[0].clone(), v.as_ref().clone())])
            }
            ("Error", Val::ResErr(v)) if binders.len() == 1 => {
                Some(vec![(binders[0].clone(), v.as_ref().clone())])
            }
            ("Some", Val::OptSome(v)) if binders.len() == 1 => {
                Some(vec![(binders[0].clone(), v.as_ref().clone())])
            }
            ("None", Val::OptNone) if binders.is_empty() => Some(Vec::new()),
            (
                c,
                Val::Ctor {
                    ctor_name, fields, ..
                },
            ) if c == ctor_name && fields.len() == binders.len() => Some(
                binders
                    .iter()
                    .cloned()
                    .zip(fields.iter().cloned())
                    .collect(),
            ),
            _ => None,
        },
    }
}

fn unwrap_opt_ref(v: &Val) -> Option<&Val> {
    match v {
        Val::OptNone => None,
        Val::OptSome(inner) => Some(inner.as_ref()),
        other => Some(other),
    }
}

fn wrap_opt_if_needed(v: Val) -> Val {
    match v {
        Val::OptNone | Val::OptSome(_) => v,
        other => Val::OptSome(Box::new(other)),
    }
}

fn val_to_f64(v: &Val) -> Option<f64> {
    match v {
        Val::Float(f) => Some(f.to_f64()),
        Val::Int(n) => n.to_i64().map(|x| x as f64),
        Val::Decimal(d) => render_decimal(d).parse::<f64>().ok(),
        _ => None,
    }
}

fn to_f64_vec(vals: &[&Val]) -> Vec<f64> {
    vals.iter().filter_map(|v| val_to_f64(v)).collect()
}

fn coerce_cell_to_scalar(val: Val, target: &ScalarTy) -> Val {
    match (&val, target) {
        (Val::OptNone, ScalarTy::Option(_)) => Val::OptNone,
        (Val::OptSome(inner), ScalarTy::Option(t)) => {
            Val::OptSome(Box::new(coerce_cell_to_scalar(inner.as_ref().clone(), t)))
        }
        (_, ScalarTy::Option(t)) => Val::OptSome(Box::new(coerce_cell_to_scalar(val, t))),
        (Val::Int(n), ScalarTy::Decimal) => Val::Decimal(n * &BigInt::from(DEC_SCALE)),
        (Val::Int(n), ScalarTy::Float) => {
            Val::Float(Float64::from_f64(n.to_i64().unwrap_or(0) as f64))
        }
        (Val::Decimal(d), ScalarTy::Float) => Val::Float(Float64::from_f64(
            render_decimal(d).parse::<f64>().unwrap_or(0.0),
        )),
        _ => val,
    }
}

fn format_display_val(v: &Val) -> String {
    match v {
        Val::Text(s) => s.clone(),
        Val::Date(d) => d.to_i64().map_or_else(|| d.to_string(), format_iso_date),
        Val::Timestamp(ts) => ts
            .to_i64()
            .map_or_else(|| ts.to_string(), format_iso_timestamp),
        Val::Decimal(d) => render_decimal(d),
        Val::Float(f) => format!("{}", f.to_f64()),
        Val::OptNone => "none".to_string(),
        Val::OptSome(inner) => format_display_val(inner),
        other => render_public_val(other),
    }
}

fn format_pretty_table(tv: &TableVal) -> String {
    let mut widths: Vec<usize> = tv.cols.iter().map(|c| c.name.len()).collect();
    let rendered: Vec<Vec<String>> = tv
        .rows
        .iter()
        .map(|r| {
            r.cells
                .iter()
                .enumerate()
                .map(|(i, c)| {
                    let s = format_display_val(c);
                    if i < widths.len() {
                        widths[i] = widths[i].max(s.len());
                    }
                    s
                })
                .collect()
        })
        .collect();
    let mut out = String::new();
    out.push('|');
    for (i, c) in tv.cols.iter().enumerate() {
        let w = widths[i];
        out.push_str(&format!(" {:<w$} |", c.name));
    }
    out.push('\n');
    out.push('|');
    for &w in &widths {
        out.push(' ');
        for _ in 0..w {
            out.push('-');
        }
        out.push_str(" |");
    }
    for row in rendered {
        out.push('\n');
        out.push('|');
        for (i, cell) in row.iter().enumerate() {
            let w = widths.get(i).copied().unwrap_or(cell.len());
            out.push_str(&format!(" {cell:<w$} |"));
        }
    }
    out
}

fn render_basic_html_report(rep: &crate::oracle::value::ReportVal) -> String {
    let mut out = format!(
        "<!doctype html><html><head><meta charset=\"utf-8\"><title>{}</title></head><body><h1>{}</h1>",
        html_escape(&rep.title),
        html_escape(&rep.title)
    );
    for s in &rep.summaries {
        out.push_str(&format!("<p>{}</p>", html_escape(s)));
    }
    for (hdrs, rows) in &rep.tables {
        out.push_str("<table><thead><tr>");
        for h in hdrs {
            out.push_str(&format!("<th>{}</th>", html_escape(h)));
        }
        out.push_str("</tr></thead><tbody>");
        for r in rows {
            out.push_str("<tr>");
            for cell in r {
                out.push_str(&format!(
                    "<td>{}</td>",
                    html_escape(&format_display_val(cell))
                ));
            }
            out.push_str("</tr>");
        }
        out.push_str("</tbody></table>");
    }
    out.push_str("</body></html>\n");
    out
}

fn html_escape(s: &str) -> String {
    s.replace('&', "&amp;")
        .replace('<', "&lt;")
        .replace('>', "&gt;")
        .replace('"', "&quot;")
}

// Keep reference constants visible for checked range consistency.
const _: (i64, i64, i128, i128) = (INT64_MIN, INT64_MAX, DEC_MIN, DEC_MAX);
