//! Deterministic reference evaluator for [`ExecProgram`], supporting:
//! - Pure Core IR v0.1 primitives & all 21 relational plan operators (mirroring `src/oracle/`)
//! - Phase 2 surface extensions (float arithmetic, `round`, `abs`, `date_trunc`, `months_between`,
//!   Welch `t_test`, `Table` helpers, `for`/`while` loops, `promise` & `assert` checks)
//! - Real host capabilities (filesystem CSV, confined `WriteFiles` with `--allow-export`, stdout/stderr)
//! - Isolated `dana test` fake capabilities (`Args.of`, `Files.in_memory`, `DB.in_memory`, `Console.fake`, `Secret.fake`).

use std::collections::HashMap;
use std::fs::{self, File, OpenOptions};
use std::hash::BuildHasherDefault;
use std::io::{self, BufWriter, Cursor, Write};
#[cfg(unix)]
use std::os::unix::fs::{DirBuilderExt, OpenOptionsExt, PermissionsExt};
use std::path::{Component, Path, PathBuf};
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};

use crate::core::bigint::{BigInt, DEC_MAX, DEC_MIN, DEC_SCALE, INT64_MAX, INT64_MIN};
use crate::core::check::{check_cap_against_policy, is_safe_relative_path, join_confined_path};
use crate::core::syntax::*;
use crate::db::schema_lock::{SchemaLockFile, to_snake_case};
use crate::db::{DbError, DbRegistry, SqlDialect, SqlParam, quote_sql_ident};
use crate::formats::compress::{
    AutoDecodeReader, AutoEncodeWriter, CompressionKind, detect_compression_path,
    open_auto_decoded_file, strip_compression_ext,
};
use crate::formats::constraint::FastColConstraint;
use crate::formats::crypto::hmac_sha256_pseudonym;
use crate::formats::csv::{
    CsvReadOptions, format_csv_table_with_options, format_csv_vm_table_with_options,
    read_csv_stream_to_vm_table_with_options, read_csv_stream_with_options,
    write_csv_table_with_options, write_csv_vm_table_with_options,
};
use crate::formats::json::{
    format_jsonl_table, format_jsonl_vm_table, read_jsonl_stream_with_schema, write_jsonl_table,
    write_jsonl_vm_table,
};
use crate::formats::parquet::{
    ParquetCompression, read_parquet_bytes_to_vm_table, read_parquet_bytes_with_schema,
    write_parquet_bytes, write_parquet_vm_table_bytes,
};
use crate::formats::time::{
    DecimalIntKind, date_trunc_date, date_trunc_timestamp_duration, date_trunc_timestamp_unit,
    decimal_to_int_bigint, format_iso_date, format_iso_timestamp, format_timestamp_in_tz,
    local_date_in_tz, months_between_days, parse_decimal_i128, parse_iso_date,
    round_decimal_bigint, round_decimal_even_bigint,
};
use crate::formats::xlsx::{read_xlsx_bytes_with_schema, write_xlsx_sheets};
use crate::net::{HttpsClientConfig, JsonResponse, ParsedHttpsUrl, https_get_json};
use crate::oracle::eval::{PrimResult, eval_literal, eval_prim_op, pseudonymize_token};
use crate::oracle::value::{
    Bug, CapHandle, GroupMeta, TableRow, TableVal, Val, render_decimal, render_decimal_i128_into,
    render_public_val, val_cmp, val_eq, val_list_eq, val_list_lt, val_lt,
};
use crate::oracle::world::{
    FakeConsoleState, FakeDBState, FakeFilesState, FakeHttpsState, StoredTable, World,
};
use crate::runtime::ir::*;
use crate::vm::batch::{Batch, Column, ColumnData, NullBitmap};
use crate::vm::key::{FastHasher, eq_col_cells, hash_row_key, hash_val, hash_val_slice};
use crate::vm::ops::VmTable;
use crate::vm::ops::sort_win::{fisher_yates_shuffle, seed_from_bigint};

const DEFAULT_FUEL: usize = 500_000;
static PRIVATE_TMP_SEQ: AtomicU64 = AtomicU64::new(0);

/// Configuration for running an [`ExecProgram`].
#[derive(Clone, Debug)]
pub struct RunConfig {
    pub args: Vec<String>,
    pub allow_export: TagSet,
    pub work_dir: Option<std::path::PathBuf>,
    pub live_io: bool,
    pub fuel: usize,
    pub pseudonymize_mode: PseudonymizeMode,
    /// Logical Dana DB name -> connection URI bindings (e.g. `"Seminary" -> "sqlite:///..."`).
    pub db_bindings: HashMap<String, String>,
    /// SQLite `ATTACH DATABASE` specifications (`(optional db_name filter, schema, file path)`).
    pub sqlite_attachments: Vec<(Option<String>, String, String)>,
    /// Optional offline `schema.lock` snapshot for table-name resolution and pushdown PK proofs.
    pub schema_lock: Option<SchemaLockFile>,
    /// When `true`, suppresses all live DB/filesystem mutations and prints redacted dry-run diffs.
    pub dry_run: bool,
    /// Optional PEM CA certificate file used by `HttpsAllow` (falls back to `DANA_HTTPS_CA_CERT`).
    pub https_ca_cert: Option<std::path::PathBuf>,
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
            db_bindings: HashMap::new(),
            sqlite_attachments: Vec::new(),
            schema_lock: None,
            dry_run: false,
            https_ca_cert: None,
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

/// Typed value result returned by evaluating a named entry function (used by `dana repl`).
#[derive(Clone, Debug)]
pub enum EvalProgramResult {
    Ok {
        val: Box<Val>,
        ret_lty: Box<LTy>,
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

#[derive(Debug)]
struct ExecWorld {
    world: World,
    fake_args: Vec<Vec<String>>,
    fake_console_tables: Vec<Vec<TableVal>>,
    fake_binary_files: HashMap<usize, Vec<(String, Vec<u8>)>>,
    written_binary_files: Vec<(String, Vec<u8>)>,
    json_responses: Vec<JsonResponse>,
    work_dir: Option<std::path::PathBuf>,
    live_io: bool,
    pseudonymize_mode: PseudonymizeMode,
    db_registry: DbRegistry,
    schema_lock: Option<SchemaLockFile>,
    dry_run: bool,
    https_ca_cert: Option<std::path::PathBuf>,
}

impl ExecWorld {
    fn from_config(cfg: &RunConfig) -> Self {
        let world = World {
            args: cfg.args.clone(),
            runtime_allow_export: cfg.allow_export.clone(),
            ..World::default()
        };
        let mut db_registry = DbRegistry::new();
        for (name, uri) in &cfg.db_bindings {
            db_registry.register(name.clone(), uri.clone());
        }
        for (db_filter, schema, path) in &cfg.sqlite_attachments {
            db_registry.attach_sqlite(db_filter.clone(), schema.clone(), path.clone());
        }
        let https_ca_cert = cfg
            .https_ca_cert
            .clone()
            .or_else(|| std::env::var_os("DANA_HTTPS_CA_CERT").map(std::path::PathBuf::from));
        Self {
            world,
            fake_args: Vec::new(),
            fake_console_tables: Vec::new(),
            fake_binary_files: HashMap::new(),
            written_binary_files: Vec::new(),
            json_responses: Vec::new(),
            work_dir: cfg.work_dir.clone(),
            live_io: cfg.live_io,
            pseudonymize_mode: cfg.pseudonymize_mode,
            db_registry,
            schema_lock: cfg.schema_lock.clone(),
            dry_run: cfg.dry_run,
            https_ca_cert,
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

type RTEnv = HashMap<Ident, Arc<Val>>;

/// Execute `main(...)` of a lowered [`ExecProgram`] using the reference row-by-row engine (`--oracle`).
#[must_use]
pub fn run_exec_program(prog: &ExecProgram, cfg: &RunConfig) -> RunResult {
    run_exec_program_with_engine(prog, cfg, None)
}

/// Evaluate a named entry function of a lowered [`ExecProgram`] on the reference row-by-row
/// engine (`--oracle`), returning its typed runtime [`Val`] and static [`LTy`].
#[must_use]
pub fn eval_exec_entry(
    prog: &ExecProgram,
    entry_name: &str,
    prebound: &[(Ident, Val)],
    cfg: &RunConfig,
) -> EvalProgramResult {
    eval_exec_entry_with_engine(prog, entry_name, prebound, cfg, None)
}

/// Execute `main(...)` of a lowered [`ExecProgram`] on either the reference engine (`vm_cfg = None`)
/// or the vectorized columnar batch VM (`vm_cfg = Some(...)`).
#[must_use]
pub(crate) fn run_exec_program_with_engine(
    prog: &ExecProgram,
    cfg: &RunConfig,
    vm_cfg: Option<crate::vm::VmConfig>,
) -> RunResult {
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
        env.insert(pname.clone(), Arc::new(cap_val));
    }

    let mut ev = Evaluator {
        prog,
        ew: &mut ew,
        fuel: cfg.fuel,
        initial_fuel: cfg.fuel,
        vm_cfg,
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

/// Evaluate a named entry function on an [`ExecProgram`] with optional pre-bound runtime values
/// (e.g. `untyped` exploration tables in `dana repl`), returning the resulting [`Val`] and static [`LTy`].
#[must_use]
pub(crate) fn eval_exec_entry_with_engine(
    prog: &ExecProgram,
    entry_name: &str,
    prebound: &[(Ident, Val)],
    cfg: &RunConfig,
    vm_cfg: Option<crate::vm::VmConfig>,
) -> EvalProgramResult {
    let Some(entry_fn) = prog.find_fun(entry_name) else {
        return EvalProgramResult::Failed {
            message: format!("missing entry function `{entry_name}`"),
            stdout: Vec::new(),
            stderr: Vec::new(),
        };
    };

    let mut ew = ExecWorld::from_config(cfg);
    let mut env = RTEnv::new();
    for (pname, plty) in &entry_fn.params {
        if let Some((_, v)) = prebound.iter().find(|(n, _)| n == pname) {
            env.insert(pname.clone(), Arc::new(v.clone()));
        } else {
            let cap_val = real_cap_for_ty(&plty.ty);
            env.insert(pname.clone(), Arc::new(cap_val));
        }
    }

    let mut ev = Evaluator {
        prog,
        ew: &mut ew,
        fuel: cfg.fuel,
        initial_fuel: cfg.fuel,
        vm_cfg,
    };
    match ev.eval_expr(&entry_fn.body, &env) {
        EvalOut::Ok(val) => EvalProgramResult::Ok {
            val: Box::new(val),
            ret_lty: Box::new(entry_fn.ret.clone()),
            stdout: ew.world.stdout,
            stderr: ew.world.stderr,
        },
        EvalOut::Stopped(bug) => EvalProgramResult::Stopped {
            bug,
            stdout: ew.world.stdout,
            stderr: ew.world.stderr,
        },
        EvalOut::Failed(message) => EvalProgramResult::Failed {
            message,
            stdout: ew.world.stdout,
            stderr: ew.world.stderr,
        },
        EvalOut::Jumped(lbl, _) => EvalProgramResult::Failed {
            message: format!("uncaught jump `{lbl}`"),
            stdout: ew.world.stdout,
            stderr: ew.world.stderr,
        },
    }
}

/// Run all `examples` and `test` spec blocks in a lowered [`ExecProgram`] using the reference engine.
#[must_use]
pub fn run_program_tests(
    prog: &ExecProgram,
    filter: Option<&str>,
    cfg: &RunConfig,
) -> Vec<TestOutcome> {
    run_program_tests_with_engine(prog, filter, cfg, None)
}

/// Run all `examples` and `test` spec blocks on either the reference engine (`vm_cfg = None`)
/// or the vectorized columnar batch VM (`vm_cfg = Some(...)`).
#[must_use]
pub(crate) fn run_program_tests_with_engine(
    prog: &ExecProgram,
    filter: Option<&str>,
    cfg: &RunConfig,
    vm_cfg: Option<crate::vm::VmConfig>,
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
            initial_fuel: cfg.fuel,
            vm_cfg,
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

/// Evaluate a pure user function call in an isolated world (used by vectorized VM
/// fallback when a pure UDF is recursive or uses non-inlinable control flow).
pub(crate) fn eval_pure_exec_call(
    prog: &ExecProgram,
    fn_name: &str,
    args: Vec<Val>,
    fuel: usize,
) -> Result<Val, crate::vm::expr::RowEvalErr> {
    let cfg = RunConfig {
        live_io: false,
        fuel,
        ..RunConfig::default()
    };
    let mut ew = ExecWorld::from_config(&cfg);
    let mut ev = Evaluator {
        prog,
        ew: &mut ew,
        fuel,
        initial_fuel: fuel,
        vm_cfg: None,
    };
    match ev.eval_call(fn_name, args) {
        EvalOut::Ok(v) => Ok(v),
        EvalOut::Stopped(bug) => Err(crate::vm::expr::RowEvalErr::Stopped { lane: 0, bug }),
        EvalOut::Failed(m) => Err(crate::vm::expr::RowEvalErr::Failed(m)),
        EvalOut::Jumped(lbl, _) => Err(crate::vm::expr::RowEvalErr::Failed(format!(
            "uncaught jump `{lbl}`"
        ))),
    }
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
    Csv {
        delimiter: u8,
        sanitize_formulas: bool,
    },
    Jsonl,
}

struct Evaluator<'a> {
    prog: &'a ExecProgram,
    ew: &'a mut ExecWorld,
    fuel: usize,
    initial_fuel: usize,
    vm_cfg: Option<crate::vm::VmConfig>,
}

fn map_db_err_to_bug(err: DbError) -> Bug {
    match err {
        DbError::SchemaDrift(m) | DbError::TypeConversion(m) => Bug {
            kind: BugKind::SchemaConstraint,
            message: m,
        },
        other => Bug {
            kind: BugKind::OutsideBoundary,
            message: other.to_string(),
        },
    }
}

fn build_constraint_self_cols(schema_tt: &TableTy) -> Vec<[ColSpec; 1]> {
    schema_tt
        .cols
        .iter()
        .map(|c| {
            [ColSpec {
                name: "__self".to_string(),
                ty: c.ty.clone(),
                tags: TagSet::empty(),
                bucketed: false,
                agg_kind: AggKind::Raw,
            }]
        })
        .collect()
}

fn find_fake_db_table_single<'a>(db: &'a FakeDBState, table_name: &str) -> Option<&'a StoredTable> {
    if let Some(exact) = db.tables.iter().find(|t| t.table_name == table_name) {
        return Some(exact);
    }
    if let Some(ci) = db
        .tables
        .iter()
        .find(|t| t.table_name.eq_ignore_ascii_case(table_name))
    {
        return Some(ci);
    }
    let target_snake = to_snake_case(table_name);
    db.tables
        .iter()
        .find(|t| to_snake_case(&t.table_name) == target_snake)
}

fn find_fake_db_table<'a>(db: &'a FakeDBState, table_name: &str) -> Option<&'a StoredTable> {
    if let Some(found) = find_fake_db_table_single(db, table_name) {
        return Some(found);
    }
    if let Some((schema, rel)) = table_name.split_once('.')
        && !schema.is_empty()
        && !rel.is_empty()
        && !rel.contains('.')
    {
        return find_fake_db_table_single(db, &format!("{schema}_{rel}"));
    }
    None
}

impl crate::vm::exec::ExecPlanBridge for Evaluator<'_> {
    fn eval_outer_expr(
        &mut self,
        expr: &ExecExpr,
        env: &HashMap<Ident, Arc<Val>>,
    ) -> Result<Val, crate::vm::OpErr> {
        match self.eval_expr(expr, env) {
            EvalOut::Ok(v) => Ok(v),
            EvalOut::Stopped(b) => Err(crate::vm::OpErr::Stopped(b)),
            EvalOut::Failed(m) => Err(crate::vm::OpErr::Failed(m)),
            EvalOut::Jumped(lbl, _) => {
                Err(crate::vm::OpErr::Failed(format!("uncaught jump `{lbl}`")))
            }
        }
    }

    fn load_fake_db_table(
        &mut self,
        cap_v: Val,
        table_name: &str,
        schema: &TableTy,
    ) -> Result<TableVal, crate::vm::OpErr> {
        match cap_v {
            Val::CapReadDB {
                handle: CapHandle::Fake(idx),
                ..
            } => {
                let stored = self
                    .ew
                    .world
                    .fake_dbs
                    .get(idx)
                    .and_then(|db| find_fake_db_table(db, table_name));
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
                        Ok(TableVal {
                            cols: schema.cols.clone(),
                            rows,
                        })
                    }
                    None => Ok(TableVal {
                        cols: schema.cols.clone(),
                        rows: Vec::new(),
                    }),
                }
            }
            _ => Err(crate::vm::OpErr::Stopped(Bug {
                kind: BugKind::OutsideBoundary,
                message: "live ReadDB queries require a bound database URI (--db Name=URI or DANA_DB_<NAME>)"
                    .to_string(),
            })),
        }
    }

    fn resolve_secret_material(&self, sec_val: &Val) -> String {
        match sec_val {
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
        }
    }

    fn live_db_info(
        &mut self,
        cap_val: &Val,
    ) -> Result<Option<(Ident, SqlDialect)>, crate::vm::OpErr> {
        match cap_val {
            Val::CapReadDB {
                handle: CapHandle::Real,
                db,
            } => {
                let conn = self
                    .ew
                    .db_registry
                    .open(db)
                    .map_err(|e| crate::vm::OpErr::Stopped(map_db_err_to_bug(e)))?;
                Ok(Some((db.clone(), conn.dialect())))
            }
            _ => Ok(None),
        }
    }

    fn schema_lock(&self) -> Option<&SchemaLockFile> {
        self.ew.schema_lock.as_ref()
    }

    fn resolve_live_table_ref(
        &mut self,
        db_name: &str,
        table_name: &str,
    ) -> Result<String, crate::vm::OpErr> {
        let conn = self
            .ew
            .db_registry
            .open(db_name)
            .map_err(|e| crate::vm::OpErr::Stopped(map_db_err_to_bug(e)))?;
        Ok(conn.resolve_table_sql_ref(table_name))
    }

    fn exec_live_sql_batches(
        &mut self,
        db_name: &str,
        sql: &str,
        params: &[SqlParam],
        expected_schema: &TableTy,
        batch_size: usize,
    ) -> Result<crate::vm::ops::VmTable, crate::vm::OpErr> {
        let conn = self
            .ew
            .db_registry
            .open(db_name)
            .map_err(|e| crate::vm::OpErr::Stopped(map_db_err_to_bug(e)))?;
        conn.query_batches(sql, params, expected_schema, batch_size)
            .map_err(|e| crate::vm::OpErr::Stopped(map_db_err_to_bug(e)))
    }
}

impl<'a> Evaluator<'a> {
    fn tick(&mut self) -> Option<EvalOut> {
        if self.fuel == 0 {
            return Some(EvalOut::Stopped(Bug {
                kind: BugKind::OutsideBoundary,
                message: format!(
                    "execution step limit exceeded ({} steps); pass `--oracle-steps N` to increase the oracle step budget, or omit `--oracle` to run on the vectorized VM",
                    self.initial_fuel
                ),
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
                    map.insert(name.clone(), Arc::new(val));
                    cur_expr = body;
                    continue;
                }
                ExecExpr::Lit(l) => return EvalOut::Ok(eval_literal(l)),
                ExecExpr::Var(name) => {
                    return cur_env.get(name).map(|v| v.as_ref().clone()).map_or_else(
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
                    let mut sv = match self.eval_expr(scrut, cur_env) {
                        EvalOut::Ok(v) => v,
                        other => return other,
                    };
                    let mut matched_body = None;
                    for arm in arms {
                        if let Some(bindings) = match_pattern_take(&arm.pattern, &mut sv) {
                            let map = owned_env.get_or_insert_with(|| env.clone());
                            for (k, v) in bindings {
                                map.insert(k, Arc::new(v));
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
                    let mut arg_arcs = Vec::with_capacity(args.len());
                    for a in args {
                        if let ExecExpr::Var(vname) = a
                            && let Some(val) = cur_env.get(vname)
                        {
                            arg_arcs.push(Arc::clone(val));
                            continue;
                        }
                        match self.eval_expr(a, cur_env) {
                            EvalOut::Ok(v) => arg_arcs.push(Arc::new(v)),
                            other => return other,
                        }
                    }
                    return self.eval_call_arcs(fn_name, arg_arcs);
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
                                    jenv.insert(p.clone(), Arc::new(v.clone()));
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
                        loop_env.insert(item_var.clone(), Arc::new(item));
                        match self.eval_expr(body, &loop_env) {
                            EvalOut::Ok(Val::Tuple(ref updated)) => {
                                for ((k, _), v) in state_vars.iter().zip(updated.iter()) {
                                    loop_env.insert(k.clone(), Arc::new(v.clone()));
                                }
                            }
                            EvalOut::Ok(_) => {}
                            EvalOut::Jumped(lbl, vals) if lbl == "__continue" => {
                                for ((k, _), v) in state_vars.iter().zip(vals) {
                                    loop_env.insert(k.clone(), Arc::new(v));
                                }
                            }
                            EvalOut::Jumped(lbl, vals) if lbl == "__break" => {
                                for ((k, _), v) in state_vars.iter().zip(vals) {
                                    loop_env.insert(k.clone(), Arc::new(v));
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
                                    loop_env.insert(k.clone(), Arc::new(v.clone()));
                                }
                            }
                            EvalOut::Ok(_) => {}
                            EvalOut::Jumped(lbl, vals) if lbl == "__continue" => {
                                for ((k, _), v) in state_vars.iter().zip(vals) {
                                    loop_env.insert(k.clone(), Arc::new(v));
                                }
                            }
                            EvalOut::Jumped(lbl, vals) if lbl == "__break" => {
                                for ((k, _), v) in state_vars.iter().zip(vals) {
                                    loop_env.insert(k.clone(), Arc::new(v));
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
                    let i = idx.to_u64().unwrap_or(usize::MAX as u64) as usize;
                    if let ExecExpr::Var(name) = tup.as_ref()
                        && let Some(val) = cur_env.get(name)
                    {
                        return match val.as_ref() {
                            Val::Tuple(xs) if i < xs.len() => EvalOut::Ok(xs[i].clone()),
                            _ => EvalOut::Failed("tuple projection out of bounds".to_string()),
                        };
                    }
                    let mut tv = match self.eval_expr(tup, cur_env) {
                        EvalOut::Ok(v) => v,
                        other => return other,
                    };
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
                    if let [ExecExpr::Var(vname)] = args.as_slice()
                        && let Some(val) = cur_env.get(vname)
                    {
                        return self.eval_exec_prim(op, std::slice::from_ref(val.as_ref()));
                    }
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
                ExecExpr::Rel(plan) => {
                    if let Some(vm_cfg) = self.vm_cfg {
                        let prog = self.prog;
                        let fuel = self.fuel;
                        return match crate::vm::exec::eval_exec_plan_vm(
                            plan, prog, cur_env, &vm_cfg, fuel, self,
                        ) {
                            Ok(v) => EvalOut::Ok(v),
                            Err(crate::vm::OpErr::Stopped(b)) => EvalOut::Stopped(b),
                            Err(crate::vm::OpErr::Failed(m)) => EvalOut::Failed(m),
                            Err(crate::vm::OpErr::Wrong) => {
                                EvalOut::Failed("internal VM plan evaluation error".to_string())
                            }
                        };
                    }
                    return self.eval_plan(plan, cur_env);
                }
                ExecExpr::Host { op, args } => {
                    let fast_match = match args.as_slice() {
                        [a0, a1, ExecExpr::Var(vname)] => Some((a0, a1, vname, None, None)),
                        [a0, a1, ExecExpr::Var(vname), a3] => Some((a0, a1, vname, Some(a3), None)),
                        [a0, a1, ExecExpr::Var(vname), a3, a4] => {
                            Some((a0, a1, vname, Some(a3), Some(a4)))
                        }
                        _ => None,
                    };
                    if let Some((a0, a1, vname, priv_arg, san_arg)) = fast_match
                        && matches!(
                            op,
                            ExecHostOp::Core(HostOp::WriteParquet)
                                | ExecHostOp::WritePrivate {
                                    inner: HostOp::WriteParquet
                                }
                                | ExecHostOp::WriteCsv
                                | ExecHostOp::WriteJsonl
                        )
                        && let Some(tbl_arc) = cur_env.get(vname).cloned()
                        && matches!(tbl_arc.as_ref(), Val::Table(_) | Val::Columnar(_))
                    {
                        let cap_v = match self.eval_expr(a0, cur_env) {
                            EvalOut::Ok(v) => v,
                            other => return other,
                        };
                        let path_v = match self.eval_expr(a1, cur_env) {
                            EvalOut::Ok(v) => v,
                            other => return other,
                        };
                        let explicit_private = match priv_arg {
                            Some(pa) => match self.eval_expr(pa, cur_env) {
                                EvalOut::Ok(Val::Bool(b)) => b,
                                EvalOut::Ok(_) => {
                                    return EvalOut::Failed("`private:` expects Bool".to_string());
                                }
                                other => return other,
                            },
                            None => false,
                        };
                        let sanitize_formulas = match san_arg {
                            Some(sa) => match self.eval_expr(sa, cur_env) {
                                EvalOut::Ok(Val::Bool(b)) => b,
                                EvalOut::Ok(_) => {
                                    return EvalOut::Failed(
                                        "`sanitize_formulas:` expects Bool".to_string(),
                                    );
                                }
                                other => return other,
                            },
                            None => false,
                        };
                        if let (
                            Val::CapWriteFiles {
                                handle,
                                root,
                                allows,
                            },
                            Val::Text(rel),
                        ) = (&cap_v, &path_v)
                        {
                            if !self.ew.dry_run
                                && let Some(bug) = self.check_export_gate(*handle, allows)
                            {
                                return EvalOut::Stopped(bug);
                            }
                            if !is_safe_relative_path(rel) {
                                return EvalOut::Ok(Val::ResErr(Box::new(Val::Text(format!(
                                    "unsafe write path `{rel}`"
                                )))));
                            }
                            let is_private = explicit_private || !allows.is_empty();
                            let full_rel = join_confined_path(root, rel);
                            return match (op, tbl_arc.as_ref()) {
                                (
                                    ExecHostOp::Core(HostOp::WriteParquet)
                                    | ExecHostOp::WritePrivate {
                                        inner: HostOp::WriteParquet,
                                    },
                                    Val::Table(tv),
                                ) => {
                                    if matches!(handle, CapHandle::Real) && self.ew.dry_run {
                                        self.ew.world.stdout.push(format!(
                                            "[DRY-RUN] would write parquet \"{full_rel}\" ({} rows, {} cols)",
                                            tv.rows.len(),
                                            tv.cols.len()
                                        ));
                                        EvalOut::Ok(Val::ResOk(Box::new(Val::Unit)))
                                    } else {
                                        match write_parquet_bytes(tv, ParquetCompression::Zstd) {
                                            Ok(bytes) => self.write_confined_bytes(
                                                *handle, &full_rel, bytes, is_private,
                                            ),
                                            Err(e) => {
                                                EvalOut::Ok(Val::ResErr(Box::new(Val::Text(e))))
                                            }
                                        }
                                    }
                                }
                                (
                                    ExecHostOp::Core(HostOp::WriteParquet)
                                    | ExecHostOp::WritePrivate {
                                        inner: HostOp::WriteParquet,
                                    },
                                    Val::Columnar(vm),
                                ) => {
                                    if matches!(handle, CapHandle::Real) && self.ew.dry_run {
                                        self.ew.world.stdout.push(format!(
                                            "[DRY-RUN] would write parquet \"{full_rel}\" ({} rows, {} cols)",
                                            vm.total_rows(),
                                            vm.cols.len()
                                        ));
                                        EvalOut::Ok(Val::ResOk(Box::new(Val::Unit)))
                                    } else {
                                        match write_parquet_vm_table_bytes(
                                            vm,
                                            ParquetCompression::Zstd,
                                        ) {
                                            Ok(bytes) => self.write_confined_bytes(
                                                *handle, &full_rel, bytes, is_private,
                                            ),
                                            Err(e) => {
                                                EvalOut::Ok(Val::ResErr(Box::new(Val::Text(e))))
                                            }
                                        }
                                    }
                                }
                                (ExecHostOp::WriteCsv, Val::Table(tv)) => {
                                    let delim = if strip_compression_ext(rel).ends_with(".tsv") {
                                        b'\t'
                                    } else {
                                        b','
                                    };
                                    self.write_confined_table(
                                        *handle,
                                        &full_rel,
                                        tv,
                                        TableWriteFmt::Csv {
                                            delimiter: delim,
                                            sanitize_formulas,
                                        },
                                        is_private,
                                    )
                                }
                                (ExecHostOp::WriteCsv, Val::Columnar(vm)) => {
                                    let delim = if strip_compression_ext(rel).ends_with(".tsv") {
                                        b'\t'
                                    } else {
                                        b','
                                    };
                                    self.write_confined_vm_table(
                                        *handle,
                                        &full_rel,
                                        vm,
                                        TableWriteFmt::Csv {
                                            delimiter: delim,
                                            sanitize_formulas,
                                        },
                                        is_private,
                                    )
                                }
                                (ExecHostOp::WriteJsonl, Val::Table(tv)) => self
                                    .write_confined_table(
                                        *handle,
                                        &full_rel,
                                        tv,
                                        TableWriteFmt::Jsonl,
                                        is_private,
                                    ),
                                (ExecHostOp::WriteJsonl, Val::Columnar(vm)) => self
                                    .write_confined_vm_table(
                                        *handle,
                                        &full_rel,
                                        vm,
                                        TableWriteFmt::Jsonl,
                                        is_private,
                                    ),
                                _ => EvalOut::Failed("unexpected host write op".to_string()),
                            };
                        }
                    }
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
            fenv.insert(pname.clone(), Arc::new(val));
        }
        self.eval_expr(&f.body, &fenv)
    }

    fn eval_call_arcs(&mut self, fn_name: &str, args: Vec<Arc<Val>>) -> EvalOut {
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
            ExecPromise::UniqueCols(cols) => match env.get(ret_var).map(Arc::as_ref) {
                Some(Val::Table(tv)) => {
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
                Some(Val::Columnar(vm)) => {
                    let idxs: Vec<usize> = cols.iter().filter_map(|c| vm.find_col_idx(c)).collect();
                    let mut seen: HashMap<u64, Vec<(u32, u16)>, BuildHasherDefault<FastHasher>> =
                        HashMap::default();
                    for (bi, b) in vm.batches.iter().enumerate() {
                        for &r_u16 in &b.active_indices() {
                            let ri = usize::from(r_u16);
                            let h = hash_row_key(&b.cols, &idxs, ri);
                            let bucket = seen.entry(h).or_default();
                            if bucket.iter().any(|&(pbi, pri_u16)| {
                                let pb = &vm.batches[pbi as usize];
                                let pri = usize::from(pri_u16);
                                idxs.iter()
                                    .all(|&ci| eq_col_cells(&pb.cols[ci], pri, &b.cols[ci], ri))
                            }) {
                                return EvalOut::Stopped(Bug {
                                    kind: BugKind::PromiseViolation,
                                    message: format!("`promise unique({cols:?})` violated"),
                                });
                            }
                            bucket.push((bi as u32, r_u16));
                        }
                    }
                    EvalOut::Ok(Val::Unit)
                }
                _ => EvalOut::Failed("`promise unique` expected Table".to_string()),
            },
            ExecPromise::AllRows(pred) => match env.get(ret_var).map(Arc::as_ref) {
                Some(Val::Table(tv)) => {
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
                                return EvalOut::Failed(
                                    "`promise all` returned non-Bool".to_string(),
                                );
                            }
                            other => return other,
                        }
                    }
                    EvalOut::Ok(Val::Unit)
                }
                Some(Val::Columnar(vm)) => {
                    let mut cells = Vec::with_capacity(vm.cols.len());
                    for b in &vm.batches {
                        for &r_u16 in &b.active_indices() {
                            let ri = usize::from(r_u16);
                            cells.clear();
                            for c in &b.cols {
                                cells.push(c.get_val(ri));
                            }
                            match self.eval_row_expr(pred, &vm.cols, &cells, env) {
                                EvalOut::Ok(Val::Bool(true)) => {}
                                EvalOut::Ok(Val::Bool(false)) => {
                                    return EvalOut::Stopped(Bug {
                                        kind: BugKind::PromiseViolation,
                                        message: "`promise all(...)` violated".to_string(),
                                    });
                                }
                                EvalOut::Ok(_) => {
                                    return EvalOut::Failed(
                                        "`promise all` returned non-Bool".to_string(),
                                    );
                                }
                                other => return other,
                            }
                        }
                    }
                    EvalOut::Ok(Val::Unit)
                }
                _ => EvalOut::Failed("`promise all` expected Table".to_string()),
            },
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
            ExecPrimOp::Core(PrimOp::StatsCorr { col_x, col_y }) => match args {
                [Val::Table(tv)] => match crate::stats::pearson_corr_table(tv, col_x, col_y) {
                    Ok(Some(r)) => EvalOut::Ok(Val::Float(Float64::from_f64(r))),
                    Ok(None) => EvalOut::Ok(Val::Float(Float64::CANONICAL_NAN)),
                    Err(e) => EvalOut::Failed(format!("Stats.corr: {e}")),
                },
                [Val::Columnar(vm)] => {
                    match crate::stats::pearson_corr_vm_table(vm, col_x, col_y) {
                        Ok(Some(r)) => EvalOut::Ok(Val::Float(Float64::from_f64(r))),
                        Ok(None) => EvalOut::Ok(Val::Float(Float64::CANONICAL_NAN)),
                        Err(e) => EvalOut::Failed(format!("Stats.corr: {e}")),
                    }
                }
                _ => EvalOut::Failed("Stats.corr requires a Table".to_string()),
            },
            ExecPrimOp::Core(PrimOp::StatsLinReg { col_x, col_y }) => match args {
                [Val::Table(tv)] => match crate::stats::linear_regression_table(tv, col_x, col_y) {
                    Ok(Some(res)) => EvalOut::Ok(Val::LinearModel {
                        slope: Float64::from_f64(res.slope),
                        intercept: Float64::from_f64(res.intercept),
                        r2: Float64::from_f64(res.r_squared),
                    }),
                    Ok(None) => EvalOut::Stopped(Bug {
                        kind: BugKind::DivByZero,
                        message: "degenerate linear regression: fewer than 2 points, non-finite inputs, or zero variance in x".to_string(),
                    }),
                    Err(e) => EvalOut::Failed(format!("Stats.linear_regression: {e}")),
                },
                [Val::Columnar(vm)] => {
                    match crate::stats::linear_regression_vm_table(vm, col_x, col_y) {
                        Ok(Some(res)) => EvalOut::Ok(Val::LinearModel {
                            slope: Float64::from_f64(res.slope),
                            intercept: Float64::from_f64(res.intercept),
                            r2: Float64::from_f64(res.r_squared),
                        }),
                        Ok(None) => EvalOut::Stopped(Bug {
                            kind: BugKind::DivByZero,
                            message: "degenerate linear regression: fewer than 2 points, non-finite inputs, or zero variance in x".to_string(),
                        }),
                        Err(e) => EvalOut::Failed(format!("Stats.linear_regression: {e}")),
                    }
                }
                _ => EvalOut::Failed("Stats.linear_regression requires a Table".to_string()),
            },
            ExecPrimOp::Core(PrimOp::TableProfile) => match args {
                [Val::Table(tv)] => EvalOut::Ok(Val::Profile(
                    crate::stats::profile::profile_table(tv, &TagSet::empty(), &[]),
                )),
                [Val::Columnar(vm)] => EvalOut::Ok(Val::Profile(
                    crate::stats::profile::profile_vm_table(vm, &TagSet::empty(), &[]),
                )),
                _ => EvalOut::Failed("table.profile() requires a Table".to_string()),
            },
            ExecPrimOp::Core(PrimOp::TableCount) => match args {
                [Val::Columnar(vm)] => {
                    let b = BigInt::from(vm.total_rows());
                    if b.in_int64_range() {
                        EvalOut::Ok(Val::Int(b))
                    } else {
                        EvalOut::Stopped(Bug {
                            kind: BugKind::IntOverflow,
                            message: "Int64 arithmetic overflow".to_string(),
                        })
                    }
                }
                _ => match eval_prim_op(&PrimOp::TableCount, args) {
                    PrimResult::Ok(v) => EvalOut::Ok(v),
                    PrimResult::Stopped(b) => EvalOut::Stopped(b),
                    PrimResult::OutOfFuel => EvalOut::Stopped(Bug {
                        kind: BugKind::OutsideBoundary,
                        message: "out of fuel".to_string(),
                    }),
                    PrimResult::Wrong => {
                        EvalOut::Failed("primitive type error in `TableCount`".to_string())
                    }
                },
            },
            ExecPrimOp::Core(PrimOp::TableConcat(schema))
                if matches!(args, [Val::List(tbls)] if tbls.iter().any(|t| matches!(t, Val::Columnar(_)))) =>
            {
                let [Val::List(tbls)] = args else {
                    return EvalOut::Failed("primitive type error in `TableConcat`".to_string());
                };
                let out_cols: Vec<ColSpec> = schema
                    .cols
                    .iter()
                    .map(|c| ColSpec {
                        agg_kind: AggKind::Raw,
                        ..c.clone()
                    })
                    .collect();
                let batch_size = self
                    .vm_cfg
                    .map_or(crate::vm::batch::BATCH_SIZE, |c| c.batch_size);
                let mut batches = Vec::new();
                for item in tbls {
                    let Some(vm) = item.clone().into_vm_table(batch_size) else {
                        return EvalOut::Failed(
                            "primitive type error in `TableConcat`".to_string(),
                        );
                    };
                    for mut b in vm.batches {
                        b.group_meta = None;
                        for (c, spec) in b.cols.iter_mut().zip(&out_cols) {
                            c.spec = spec.clone();
                        }
                        batches.push(b);
                    }
                }
                EvalOut::Ok(Val::Columnar(Arc::new(VmTable {
                    cols: out_cols,
                    batches,
                })))
            }
            ExecPrimOp::Core(PrimOp::StatsTTest { col_x, col_y })
                if matches!(args, [Val::Columnar(_)]) =>
            {
                let [Val::Columnar(vm)] = args else {
                    return EvalOut::Failed("primitive type error in `StatsTTest`".to_string());
                };
                if vm.find_col_idx(col_x).is_some() && vm.find_col_idx(col_y).is_some() {
                    EvalOut::Stopped(Bug {
                        kind: BugKind::OutsideBoundary,
                        message: "outside boundary: statsTTest is outside the Lean Core oracle"
                            .to_string(),
                    })
                } else {
                    EvalOut::Failed("primitive type error in `StatsTTest`".to_string())
                }
            }
            ExecPrimOp::Core(PrimOp::ChartMake { kind, cols, title })
                if matches!(args, [Val::Columnar(_)]) =>
            {
                let [Val::Columnar(vm)] = args else {
                    return EvalOut::Failed("primitive type error in `ChartMake`".to_string());
                };
                let total_rows = vm.total_rows();
                let mut series = Vec::with_capacity(cols.len());
                for cn in cols {
                    let Some(idx) = vm.find_col_idx(cn) else {
                        return EvalOut::Failed(format!("chart: missing column `{cn}`"));
                    };
                    let mut vals = Vec::with_capacity(total_rows);
                    for b in &vm.batches {
                        let col = &b.cols[idx];
                        for &r_u16 in &b.active_indices() {
                            vals.push(col.get_val(usize::from(r_u16)));
                        }
                    }
                    series.push(vals);
                }
                EvalOut::Ok(Val::Chart(Box::new(crate::oracle::value::ChartVal {
                    kind: *kind,
                    title: title.clone(),
                    col_names: cols.clone(),
                    series,
                    ..crate::oracle::value::ChartVal::default()
                })))
            }
            ExecPrimOp::Core(PrimOp::ReportAddTable)
                if matches!(args, [Val::Report(_), Val::Columnar(_)]) =>
            {
                let [Val::Report(rv), Val::Columnar(vm)] = args else {
                    return EvalOut::Failed("primitive type error in `ReportAddTable`".to_string());
                };
                let mut out = rv.as_ref().clone();
                let headers = vm.cols.iter().map(|c| c.name.clone()).collect();
                let mut raw_rows = Vec::with_capacity(vm.total_rows());
                for b in &vm.batches {
                    for &r_u16 in &b.active_indices() {
                        let ri = usize::from(r_u16);
                        raw_rows.push(b.cols.iter().map(|c| c.get_val(ri)).collect());
                    }
                }
                out.tables.push((headers, raw_rows));
                EvalOut::Ok(Val::Report(Box::new(out)))
            }
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
                    EvalOut::Ok(Val::Float(round_float_val(*a, p, false)))
                }
                _ => EvalOut::Failed("RoundFloat requires (Float, Int)".to_string()),
            },
            ExecPrimOp::RoundFloatEven => match args {
                [Val::Float(a), Val::Int(p)] => {
                    EvalOut::Ok(Val::Float(round_float_val(*a, p, true)))
                }
                _ => EvalOut::Failed("RoundFloatEven requires (Float, Int)".to_string()),
            },
            ExecPrimOp::RoundDecimal => match args {
                [Val::Decimal(d), Val::Int(p)] => {
                    let places = p.to_i64().unwrap_or(0);
                    EvalOut::Ok(Val::Decimal(round_decimal_bigint(d, places)))
                }
                _ => EvalOut::Failed("RoundDecimal requires (Decimal, Int)".to_string()),
            },
            ExecPrimOp::RoundDecimalEven => match args {
                [Val::Decimal(d), Val::Int(p)] => {
                    let places = p.to_i64().unwrap_or(0);
                    EvalOut::Ok(Val::Decimal(round_decimal_even_bigint(d, places)))
                }
                _ => EvalOut::Failed("RoundDecimalEven requires (Decimal, Int)".to_string()),
            },
            ExecPrimOp::CeilFloat | ExecPrimOp::FloorFloat | ExecPrimOp::TruncFloat => {
                match args {
                    [Val::Float(a)] => {
                        let (op_fn, name): (fn(f64) -> f64, &str) = match op {
                            ExecPrimOp::CeilFloat => (f64::ceil, "ceil"),
                            ExecPrimOp::FloorFloat => (f64::floor, "floor"),
                            _ => (f64::trunc, "trunc"),
                        };
                        match float_to_int_checked(*a, op_fn, name) {
                            Ok(n) => EvalOut::Ok(Val::Int(n)),
                            Err(bug) => EvalOut::Stopped(bug),
                        }
                    }
                    _ => EvalOut::Failed(format!("{op:?} requires Float")),
                }
            }
            ExecPrimOp::CeilDecimal | ExecPrimOp::FloorDecimal | ExecPrimOp::TruncDecimal => {
                match args {
                    [Val::Decimal(d)] => {
                        let kind = match op {
                            ExecPrimOp::CeilDecimal => DecimalIntKind::Ceil,
                            ExecPrimOp::FloorDecimal => DecimalIntKind::Floor,
                            _ => DecimalIntKind::Trunc,
                        };
                        match decimal_to_int_checked(d, kind) {
                            Ok(n) => EvalOut::Ok(Val::Int(n)),
                            Err(bug) => EvalOut::Stopped(bug),
                        }
                    }
                    _ => EvalOut::Failed(format!("{op:?} requires Decimal")),
                }
            }
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
                [v @ Val::CapSecret { .. }] => EvalOut::Ok(Val::Text(
                    <Self as crate::vm::exec::ExecPlanBridge>::resolve_secret_material(self, v),
                )),
                [v] => EvalOut::Ok(Val::Text(format_display_val(v))),
                _ => EvalOut::Failed("ValToText requires 1 arg".to_string()),
            },
            ExecPrimOp::LowerText => match args {
                [Val::Text(s)] => EvalOut::Ok(Val::Text(s.to_lowercase())),
                _ => EvalOut::Failed("LowerText requires Text".to_string()),
            },
            ExecPrimOp::UpperText => match args {
                [Val::Text(s)] => EvalOut::Ok(Val::Text(s.to_uppercase())),
                _ => EvalOut::Failed("UpperText requires Text".to_string()),
            },
            ExecPrimOp::SliceText => match args {
                [Val::Text(s), Val::Int(start), Val::Int(len)] => {
                    let st = bigint_to_slice_bound(start);
                    let ln = bigint_to_slice_bound(len);
                    EvalOut::Ok(Val::Text(slice_text(s, st, ln)))
                }
                _ => EvalOut::Failed("SliceText requires (Text, Int, Int)".to_string()),
            },
            ExecPrimOp::StartsWithText => match args {
                [Val::Text(s), Val::Text(prefix)] => EvalOut::Ok(Val::Bool(s.starts_with(prefix.as_str()))),
                _ => EvalOut::Failed("StartsWithText requires (Text, Text)".to_string()),
            },
            ExecPrimOp::EndsWithText => match args {
                [Val::Text(s), Val::Text(suffix)] => EvalOut::Ok(Val::Bool(s.ends_with(suffix.as_str()))),
                _ => EvalOut::Failed("EndsWithText requires (Text, Text)".to_string()),
            },
            ExecPrimOp::TryParseDate => match args {
                [Val::Text(s)] => EvalOut::Ok(try_parse_date_text(s)),
                _ => EvalOut::Failed("TryParseDate requires Text".to_string()),
            },
            ExecPrimOp::TryParseInt => match args {
                [Val::Text(s)] => EvalOut::Ok(try_parse_int_text(s)),
                _ => EvalOut::Failed("TryParseInt requires Text".to_string()),
            },
            ExecPrimOp::TryParseDecimal => match args {
                [Val::Text(s)] => EvalOut::Ok(try_parse_decimal_text(s)),
                _ => EvalOut::Failed("TryParseDecimal requires Text".to_string()),
            },
            ExecPrimOp::TryParseFloat => match args {
                [Val::Text(s)] => EvalOut::Ok(try_parse_float_text(s)),
                _ => EvalOut::Failed("TryParseFloat requires Text".to_string()),
            },
            ExecPrimOp::InList => match args {
                [v, Val::List(xs)] => EvalOut::Ok(Val::Bool(eval_in_list(v, xs))),
                _ => EvalOut::Failed("InList requires (Val, List)".to_string()),
            },
            ExecPrimOp::ClampInt => match args {
                [Val::Int(x), Val::Int(lo), Val::Int(hi)] => match clamp_int_bigint(x, lo, hi) {
                    Ok(v) => EvalOut::Ok(Val::Int(v)),
                    Err(bug) => EvalOut::Stopped(bug),
                },
                _ => EvalOut::Failed("ClampInt requires (Int, Int, Int)".to_string()),
            },
            ExecPrimOp::ClampFloat => match args {
                [Val::Float(x), Val::Float(lo), Val::Float(hi)] => match clamp_float_val(*x, *lo, *hi) {
                    Ok(v) => EvalOut::Ok(Val::Float(v)),
                    Err(bug) => EvalOut::Stopped(bug),
                },
                _ => EvalOut::Failed("ClampFloat requires (Float, Float, Float)".to_string()),
            },
            ExecPrimOp::ClampDecimal => match args {
                [Val::Decimal(x), Val::Decimal(lo), Val::Decimal(hi)] => {
                    match clamp_decimal_val(x, lo, hi) {
                        Ok(v) => EvalOut::Ok(Val::Decimal(v)),
                        Err(bug) => EvalOut::Stopped(bug),
                    }
                }
                _ => EvalOut::Failed("ClampDecimal requires (Decimal, Decimal, Decimal)".to_string()),
            },
            ExecPrimOp::RoundToFloat => match args {
                [Val::Float(x), Val::Float(step)] => match round_to_float_val(*x, *step) {
                    Ok(v) => EvalOut::Ok(Val::Float(v)),
                    Err(bug) => EvalOut::Stopped(bug),
                },
                _ => EvalOut::Failed("RoundToFloat requires (Float, Float)".to_string()),
            },
            ExecPrimOp::RoundToFloatEven => match args {
                [Val::Float(x), Val::Float(step)] => match round_to_float_even_val(*x, *step) {
                    Ok(v) => EvalOut::Ok(Val::Float(v)),
                    Err(bug) => EvalOut::Stopped(bug),
                },
                _ => EvalOut::Failed("RoundToFloatEven requires (Float, Float)".to_string()),
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
                [Val::Columnar(vm)] => EvalOut::Ok(Val::Bool(vm.total_rows() == 0)),
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
                [Val::Columnar(vm)] => match vm.first_row_cells() {
                    Some(fields) => EvalOut::Ok(Val::Ctor {
                        type_name: "__TableRow".to_string(),
                        ctor_name: "__TableRow".to_string(),
                        fields,
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
                [Val::Columnar(vm)] => {
                    let mut rows = Vec::with_capacity(vm.total_rows());
                    for b in &vm.batches {
                        for &r_u16 in &b.active_indices() {
                            let ri = usize::from(r_u16);
                            let fields = b.cols.iter().map(|c| c.get_val(ri)).collect();
                            rows.push(Val::Ctor {
                                type_name: "__TableRow".to_string(),
                                ctor_name: "__TableRow".to_string(),
                                fields,
                            });
                        }
                    }
                    EvalOut::Ok(Val::List(rows))
                }
                _ => EvalOut::Failed("TableRowsToList requires Table".to_string()),
            },
            ExecPrimOp::TableColSum(col) => match args {
                [Val::Table(tv)] => eval_table_col_agg(tv, col, AggOp::Sum),
                [Val::Columnar(vm)] => eval_vm_table_col_agg(vm, col, AggOp::Sum),
                _ => EvalOut::Failed("TableColSum requires Table".to_string()),
            },
            ExecPrimOp::TableColMean(col) => match args {
                [Val::Table(tv)] => eval_table_col_agg(tv, col, AggOp::Mean),
                [Val::Columnar(vm)] => eval_vm_table_col_agg(vm, col, AggOp::Mean),
                _ => EvalOut::Failed("TableColMean requires Table".to_string()),
            },
            ExecPrimOp::TableColStddev(col) => match args {
                [Val::Table(tv)] => eval_table_col_agg(tv, col, AggOp::Stddev),
                [Val::Columnar(vm)] => eval_vm_table_col_agg(vm, col, AggOp::Stddev),
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
                [Val::Columnar(vm)] => {
                    if vm_table_matches_schema_exact(vm, dst_tt) {
                        EvalOut::Ok(Val::Columnar(Arc::clone(vm)))
                    } else {
                        EvalOut::Ok(Val::Columnar(Arc::new(coerce_vm_table(vm, dst_tt))))
                    }
                }
                _ => EvalOut::Failed("TableCoerce requires Table".to_string()),
            },
            ExecPrimOp::FormatCsv => match args {
                [Val::Table(tv), Val::Bool(san)] => {
                    EvalOut::Ok(Val::Text(format_csv_table_with_options(tv, b',', *san)))
                }
                [Val::Columnar(vm), Val::Bool(san)] => EvalOut::Ok(Val::Text(
                    format_csv_vm_table_with_options(vm, b',', *san),
                )),
                _ => EvalOut::Failed("format_csv expects (Table, Bool)".to_string()),
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
                [a @ (Val::Table(_) | Val::Columnar(_)), b @ (Val::Table(_) | Val::Columnar(_))] => {
                    let res = match (a, b) {
                        (Val::Table(ta), Val::Table(tb)) => {
                            crate::stats::welch_t_test_tables(ta, tb, col)
                        }
                        (Val::Columnar(va), Val::Columnar(vb)) => {
                            crate::stats::welch_t_test_vm_tables(va, vb, col)
                        }
                        (a_val, b_val) => (|| -> Result<Option<crate::stats::WelchTTestResult>, String> {
                            let xa = match a_val {
                                Val::Table(t) => crate::stats::extract_numeric_col(t, col)?,
                                Val::Columnar(v) => crate::stats::extract_numeric_col_vm(v, col)?,
                                _ => return Err("StatsWelchTTest requires two Tables".to_string()),
                            };
                            let xb = match b_val {
                                Val::Table(t) => crate::stats::extract_numeric_col(t, col)?,
                                Val::Columnar(v) => crate::stats::extract_numeric_col_vm(v, col)?,
                                _ => return Err("StatsWelchTTest requires two Tables".to_string()),
                            };
                            Ok(crate::stats::welch_t_test(&xa, &xb))
                        })(),
                    };
                    match res {
                        Ok(Some(res)) => EvalOut::Ok(Val::StatTest {
                            stat: Float64::from_f64(res.t_stat),
                            p_value: Float64::from_f64(res.p_value),
                        }),
                        Ok(None) => EvalOut::Ok(Val::StatTest {
                            stat: Float64::CANONICAL_NAN,
                            p_value: Float64::CANONICAL_NAN,
                        }),
                        Err(e) => EvalOut::Failed(format!("Stats.t_test: {e}")),
                    }
                }
                _ => EvalOut::Failed("StatsWelchTTest requires two Tables".to_string()),
            },
            ExecPrimOp::StatsCorrSpearman { col_x, col_y } => match args {
                [Val::Table(tv)] => match crate::stats::spearman_corr_table(tv, col_x, col_y) {
                    Ok(Some(rho)) => EvalOut::Ok(Val::Float(Float64::from_f64(rho))),
                    Ok(None) => EvalOut::Ok(Val::Float(Float64::CANONICAL_NAN)),
                    Err(e) => EvalOut::Failed(format!("Stats.corr(:spearman): {e}")),
                },
                [Val::Columnar(vm)] => {
                    match crate::stats::spearman_corr_vm_table(vm, col_x, col_y) {
                        Ok(Some(rho)) => EvalOut::Ok(Val::Float(Float64::from_f64(rho))),
                        Ok(None) => EvalOut::Ok(Val::Float(Float64::CANONICAL_NAN)),
                        Err(e) => EvalOut::Failed(format!("Stats.corr(:spearman): {e}")),
                    }
                }
                _ => EvalOut::Failed("StatsCorrSpearman requires a Table".to_string()),
            },
            ExecPrimOp::LinearModelPredict => match args {
                [
                    Val::LinearModel {
                        slope, intercept, ..
                    },
                    x_val,
                ] => match val_to_f64(x_val) {
                    Some(x) => EvalOut::Ok(Val::Float(Float64::from_f64(
                        slope.to_f64() * x + intercept.to_f64(),
                    ))),
                    None => EvalOut::Failed(
                        "LinearModel.predict requires a numeric argument".to_string(),
                    ),
                },
                _ => EvalOut::Failed(
                    "LinearModel.predict requires (LinearModel, numeric)".to_string(),
                ),
            },
            ExecPrimOp::StatsChiSquareIndependence { col_x, col_y } => match args {
                [Val::Table(tv)] => {
                    match crate::stats::chi_square_independence_table(tv, col_x, col_y) {
                        Ok(Some(res)) => EvalOut::Ok(Val::StatTest {
                            stat: Float64::from_f64(res.stat),
                            p_value: Float64::from_f64(res.p_value),
                        }),
                        Ok(None) => EvalOut::Ok(Val::StatTest {
                            stat: Float64::CANONICAL_NAN,
                            p_value: Float64::CANONICAL_NAN,
                        }),
                        Err(e) => EvalOut::Failed(e),
                    }
                }
                [Val::Columnar(vm)] => {
                    match crate::stats::chi_square_independence_vm_table(vm, col_x, col_y) {
                        Ok(Some(res)) => EvalOut::Ok(Val::StatTest {
                            stat: Float64::from_f64(res.stat),
                            p_value: Float64::from_f64(res.p_value),
                        }),
                        Ok(None) => EvalOut::Ok(Val::StatTest {
                            stat: Float64::CANONICAL_NAN,
                            p_value: Float64::CANONICAL_NAN,
                        }),
                        Err(e) => EvalOut::Failed(e),
                    }
                }
                _ => EvalOut::Failed("StatsChiSquareIndependence requires a Table".to_string()),
            },
            ExecPrimOp::StatsChiSquareGof { observed, expected } => match args {
                [Val::Table(tv)] => {
                    match crate::stats::chi_square_gof_table(tv, observed, expected) {
                        Ok(Some(res)) => EvalOut::Ok(Val::StatTest {
                            stat: Float64::from_f64(res.stat),
                            p_value: Float64::from_f64(res.p_value),
                        }),
                        Ok(None) => EvalOut::Ok(Val::StatTest {
                            stat: Float64::CANONICAL_NAN,
                            p_value: Float64::CANONICAL_NAN,
                        }),
                        Err(e) => EvalOut::Failed(e),
                    }
                }
                [Val::Columnar(vm)] => {
                    match crate::stats::chi_square_gof_vm_table(vm, observed, expected) {
                        Ok(Some(res)) => EvalOut::Ok(Val::StatTest {
                            stat: Float64::from_f64(res.stat),
                            p_value: Float64::from_f64(res.p_value),
                        }),
                        Ok(None) => EvalOut::Ok(Val::StatTest {
                            stat: Float64::CANONICAL_NAN,
                            p_value: Float64::CANONICAL_NAN,
                        }),
                        Err(e) => EvalOut::Failed(e),
                    }
                }
                _ => EvalOut::Failed("StatsChiSquareGof requires a Table".to_string()),
            },
            ExecPrimOp::StatsOutliers {
                col,
                method,
                flag_col,
                flag_tags,
            } => match args {
                [Val::Table(tv), thresh_val] => {
                    let threshold = val_to_f64(thresh_val).unwrap_or(f64::NAN);
                    match crate::stats::detect_outliers_table(
                        tv, col, *method, threshold, flag_col, flag_tags,
                    ) {
                        Ok(out_tv) => EvalOut::Ok(Val::Table(out_tv)),
                        Err(e) => EvalOut::Failed(e),
                    }
                }
                [Val::Columnar(vm), thresh_val] => {
                    let threshold = val_to_f64(thresh_val).unwrap_or(f64::NAN);
                    match crate::stats::detect_outliers_vm_table(
                        vm, col, *method, threshold, flag_col, flag_tags,
                    ) {
                        Ok(out_vm) => EvalOut::Ok(Val::Columnar(Arc::new(out_vm))),
                        Err(e) => EvalOut::Failed(e),
                    }
                }
                _ => EvalOut::Failed("StatsOutliers requires (Table, threshold)".to_string()),
            },
            ExecPrimOp::TableProfileEx { row_tags, col_tags } => match args {
                [Val::Table(tv)] => EvalOut::Ok(Val::Profile(
                    crate::stats::profile::profile_table(tv, row_tags, col_tags),
                )),
                [Val::Columnar(vm)] => EvalOut::Ok(Val::Profile(
                    crate::stats::profile::profile_vm_table(vm, row_tags, col_tags),
                )),
                _ => EvalOut::Failed("TableProfileEx requires a Table".to_string()),
            },
            ExecPrimOp::ChartMakeEx {
                kind,
                x_col,
                y_col,
                color_col,
                value_col,
                has_title_expr,
                has_trendline_expr,
                has_bins_expr,
            } => {
                let first_tbl = match args.first() {
                    Some(v @ (Val::Table(_) | Val::Columnar(_))) => v,
                    _ => {
                        return EvalOut::Failed(
                            "ChartMakeEx requires a Table as first arg".to_string(),
                        );
                    }
                };
                let mut cursor = 1usize;
                let title = if *has_title_expr {
                    let t = args.get(cursor).map(format_display_val).unwrap_or_default();
                    cursor += 1;
                    t
                } else {
                    String::new()
                };
                let trendline = if *has_trendline_expr {
                    let tr = match args.get(cursor) {
                        Some(Val::LinearModel {
                            slope,
                            intercept,
                            r2,
                        }) => Some((slope.to_f64(), intercept.to_f64(), r2.to_f64())),
                        _ => None,
                    };
                    cursor += 1;
                    tr
                } else {
                    None
                };
                let bins = if *has_bins_expr {
                    match args.get(cursor) {
                        Some(Val::Int(n)) => n
                            .to_i64()
                            .filter(|&k| k > 0)
                            .map(|k| (k as usize).clamp(1, 200)),
                        _ => None,
                    }
                } else {
                    None
                };
                let mut col_names: Vec<Ident> = Vec::new();
                for opt_c in [x_col, y_col, color_col, value_col] {
                    if let Some(cn) = opt_c
                        && !col_names.contains(cn)
                    {
                        col_names.push(cn.clone());
                    }
                }
                let mut series = Vec::with_capacity(col_names.len());
                match first_tbl {
                    Val::Table(tv) => {
                        for cn in &col_names {
                            let Some(idx) = tv.cols.iter().position(|c| &c.name == cn) else {
                                return EvalOut::Failed(format!("chart: missing column `{cn}`"));
                            };
                            let vals = tv
                                .rows
                                .iter()
                                .map(|r| r.cells.get(idx).cloned().unwrap_or(Val::OptNone))
                                .collect();
                            series.push(vals);
                        }
                    }
                    Val::Columnar(vm) => {
                        let total_rows = vm.total_rows();
                        for cn in &col_names {
                            let Some(idx) = vm.find_col_idx(cn) else {
                                return EvalOut::Failed(format!("chart: missing column `{cn}`"));
                            };
                            let mut vals = Vec::with_capacity(total_rows);
                            for b in &vm.batches {
                                let col = &b.cols[idx];
                                for &r_u16 in &b.active_indices() {
                                    vals.push(col.get_val(usize::from(r_u16)));
                                }
                            }
                            series.push(vals);
                        }
                    }
                    _ => {}
                }
                EvalOut::Ok(Val::Chart(Box::new(crate::oracle::value::ChartVal {
                    kind: *kind,
                    title,
                    col_names,
                    series,
                    x_col: x_col.clone(),
                    y_col: y_col.clone(),
                    color_col: color_col.clone(),
                    value_col: value_col.clone(),
                    bins,
                    trendline,
                })))
            }
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
                [
                    a @ (Val::Table(_) | Val::Columnar(_)),
                    b @ (Val::Table(_) | Val::Columnar(_)),
                ] => EvalOut::Ok(Val::Bool(val_eq(a, b))),
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
                    let mut text_files = Vec::new();
                    let mut bin_files = Vec::new();
                    for (k, v) in pairs {
                        let path = format_display_val(k);
                        match v {
                            Val::Bytes(bs) => bin_files.push((path, bs.clone())),
                            other => {
                                let text = format_display_val(other);
                                bin_files.push((path.clone(), text.as_bytes().to_vec()));
                                text_files.push((path, text));
                            }
                        }
                    }
                    let idx = self.ew.world.fake_files.len();
                    self.ew
                        .world
                        .fake_files
                        .push(FakeFilesState { files: text_files });
                    self.ew.fake_binary_files.insert(idx, bin_files);
                    EvalOut::Ok(Val::CapReadFiles(CapHandle::Fake(idx)))
                }
                _ => EvalOut::Failed("Files.in_memory requires Map(Text, Text|Bytes)".to_string()),
            },
            ExecHostOp::FakeDbInMemory { db, table_names } => {
                let mut tables = Vec::with_capacity(table_names.len());
                for (tname, val) in table_names.iter().zip(args.iter()) {
                    if let Some(tv) = val.to_table_val() {
                        let schema = self.prog.find_schema(tname).map_or_else(
                            || TableTy {
                                cols: tv.cols.clone(),
                                ..TableTy::default()
                            },
                            |s| s.decl.schema.clone(),
                        );
                        let rows = tv.rows.into_iter().map(|r| r.cells).collect();
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
            ExecHostOp::ConsolePrintChart => {
                if let [Val::CapConsole { handle, .. }, payload] = args {
                    let rendered = match payload {
                        Val::Chart(ch) => crate::viz::terminal::render_chart_terminal(ch),
                        other => format_display_val(other),
                    };
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
                    EvalOut::Failed("console.print_chart expects (Console, Chart)".to_string())
                }
            }
            ExecHostOp::ConsolePrintProfile => {
                if let [Val::CapConsole { handle, .. }, payload] = args {
                    let rendered = match payload {
                        Val::Profile(prof) => crate::stats::profile::render_profile_terminal(prof),
                        other => format_display_val(other),
                    };
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
                    EvalOut::Failed("console.print_profile expects (Console, Profile)".to_string())
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
                let (cap, rel, tbl, explicit_private) = match args {
                    [
                        cap,
                        Val::Text(rel),
                        tbl @ (Val::Table(_) | Val::Columnar(_)),
                    ] => (cap, rel, tbl, false),
                    [
                        cap,
                        Val::Text(rel),
                        tbl @ (Val::Table(_) | Val::Columnar(_)),
                        Val::Bool(p),
                    ] => (cap, rel, tbl, *p),
                    _ => {
                        return EvalOut::Failed(
                            "write_jsonl expects (WriteFiles, path, table)".to_string(),
                        );
                    }
                };
                if let Val::CapWriteFiles {
                    handle,
                    root,
                    allows,
                } = cap
                {
                    if !self.ew.dry_run
                        && let Some(bug) = self.check_export_gate(*handle, allows)
                    {
                        return EvalOut::Stopped(bug);
                    }
                    if !is_safe_relative_path(rel) {
                        return EvalOut::Ok(Val::ResErr(Box::new(Val::Text(format!(
                            "unsafe write path `{rel}`"
                        )))));
                    }
                    let is_private = explicit_private || !allows.is_empty();
                    let full_rel = join_confined_path(root, rel);
                    match tbl {
                        Val::Table(tv) => self.write_confined_table(
                            *handle,
                            &full_rel,
                            tv,
                            TableWriteFmt::Jsonl,
                            is_private,
                        ),
                        Val::Columnar(vm) => self.write_confined_vm_table(
                            *handle,
                            &full_rel,
                            vm,
                            TableWriteFmt::Jsonl,
                            is_private,
                        ),
                        _ => EvalOut::Failed(
                            "write_jsonl expects (WriteFiles, path, table)".to_string(),
                        ),
                    }
                } else {
                    EvalOut::Failed("write_jsonl expects (WriteFiles, path, table)".to_string())
                }
            }
            ExecHostOp::WriteCsv => {
                let (cap, rel, tbl, explicit_private, sanitize_formulas) = match args {
                    [
                        cap,
                        Val::Text(rel),
                        tbl @ (Val::Table(_) | Val::Columnar(_)),
                    ] => (cap, rel, tbl, false, false),
                    [
                        cap,
                        Val::Text(rel),
                        tbl @ (Val::Table(_) | Val::Columnar(_)),
                        Val::Bool(p),
                        Val::Bool(s),
                    ] => (cap, rel, tbl, *p, *s),
                    _ => {
                        return EvalOut::Failed(
                            "write_csv expects (WriteFiles, path, table)".to_string(),
                        );
                    }
                };
                if let Val::CapWriteFiles {
                    handle,
                    root,
                    allows,
                } = cap
                {
                    if !self.ew.dry_run
                        && let Some(bug) = self.check_export_gate(*handle, allows)
                    {
                        return EvalOut::Stopped(bug);
                    }
                    if !is_safe_relative_path(rel) {
                        return EvalOut::Ok(Val::ResErr(Box::new(Val::Text(format!(
                            "unsafe write path `{rel}`"
                        )))));
                    }
                    let is_private = explicit_private || !allows.is_empty();
                    let full_rel = join_confined_path(root, rel);
                    let delim = if strip_compression_ext(rel).ends_with(".tsv") {
                        b'\t'
                    } else {
                        b','
                    };
                    let fmt = TableWriteFmt::Csv {
                        delimiter: delim,
                        sanitize_formulas,
                    };
                    match tbl {
                        Val::Table(tv) => {
                            self.write_confined_table(*handle, &full_rel, tv, fmt, is_private)
                        }
                        Val::Columnar(vm) => {
                            self.write_confined_vm_table(*handle, &full_rel, vm, fmt, is_private)
                        }
                        _ => EvalOut::Failed(
                            "write_csv expects (WriteFiles, path, table)".to_string(),
                        ),
                    }
                } else {
                    EvalOut::Failed("write_csv expects (WriteFiles, path, table)".to_string())
                }
            }
            ExecHostOp::WriteReportMarkdown => {
                let (cap, rel, rep, explicit_private) = match args {
                    [cap, Val::Text(rel), Val::Report(rep)] => (cap, rel, rep, false),
                    [cap, Val::Text(rel), Val::Report(rep), Val::Bool(p)] => (cap, rel, rep, *p),
                    _ => {
                        return EvalOut::Failed(
                            "write_markdown expects (WriteFiles, path, Report)".to_string(),
                        );
                    }
                };
                if let Val::CapWriteFiles {
                    handle,
                    root,
                    allows,
                } = cap
                {
                    if !self.ew.dry_run
                        && let Some(bug) = self.check_export_gate(*handle, allows)
                    {
                        return EvalOut::Stopped(bug);
                    }
                    if !is_safe_relative_path(rel) {
                        return EvalOut::Ok(Val::ResErr(Box::new(Val::Text(format!(
                            "unsafe write path `{rel}`"
                        )))));
                    }
                    let is_private = explicit_private || !allows.is_empty();
                    let full_rel = join_confined_path(root, rel);
                    let md = crate::viz::report::render_markdown_report(rep);
                    self.write_confined_output(*handle, &full_rel, md, is_private)
                } else {
                    EvalOut::Failed("write_markdown expects (WriteFiles, path, Report)".to_string())
                }
            }
            ExecHostOp::WriteChartSvg => {
                let (cap, rel, chart, explicit_private) = match args {
                    [cap, Val::Text(rel), Val::Chart(chart)] => (cap, rel, chart, false),
                    [cap, Val::Text(rel), Val::Chart(chart), Val::Bool(p)] => (cap, rel, chart, *p),
                    _ => {
                        return EvalOut::Failed(
                            "write_svg expects (WriteFiles, path, Chart)".to_string(),
                        );
                    }
                };
                if let Val::CapWriteFiles {
                    handle,
                    root,
                    allows,
                } = cap
                {
                    if !self.ew.dry_run
                        && let Some(bug) = self.check_export_gate(*handle, allows)
                    {
                        return EvalOut::Stopped(bug);
                    }
                    if !is_safe_relative_path(rel) {
                        return EvalOut::Ok(Val::ResErr(Box::new(Val::Text(format!(
                            "unsafe write path `{rel}`"
                        )))));
                    }
                    let is_private = explicit_private || !allows.is_empty();
                    let full_rel = join_confined_path(root, rel);
                    let svg = crate::viz::svg::render_chart_svg(chart);
                    self.write_confined_output(*handle, &full_rel, svg, is_private)
                } else {
                    EvalOut::Failed("write_svg expects (WriteFiles, path, Chart)".to_string())
                }
            }
            ExecHostOp::WritePrivate { inner } => match args {
                [cap, path, payload, Val::Bool(priv_flag)] => {
                    self.eval_core_write_host(inner.clone(), cap, path, payload, *priv_flag)
                }
                _ => EvalOut::Failed(format!("write op `{inner:?}` expects 4 arguments")),
            },
            ExecHostOp::WriteTableUpsert { key_col, allows } => {
                if let [
                    Val::CapWriteTable {
                        handle,
                        db,
                        table_name,
                    },
                    tbl_val @ (Val::Table(_) | Val::Columnar(_)),
                ] = args
                {
                    let owned_tv;
                    let tv: &TableVal = match tbl_val {
                        Val::Table(tv) => tv,
                        Val::Columnar(vm) => {
                            owned_tv = vm.to_table_val();
                            &owned_tv
                        }
                        _ => {
                            return EvalOut::Failed(
                                "WriteTable.upsert expects (WriteTable, table)".to_string(),
                            );
                        }
                    };
                    let cap_ty = Ty::WriteTable {
                        db: db.clone(),
                        table_name: table_name.clone(),
                        dest_cols: Vec::new(),
                        dest_row_tags: TagSet::empty(),
                        allows: allows.clone(),
                    };
                    if let Err(err) = check_cap_against_policy(self.prog.policy.as_ref(), &cap_ty) {
                        return EvalOut::Stopped(Bug {
                            kind: BugKind::ExportGateDenied,
                            message: err.message,
                        });
                    }
                    let mut required_tags = allows.clone();
                    for col in &tv.cols {
                        required_tags = required_tags.union(&col.tags);
                    }
                    if !self.ew.dry_run
                        && let Some(bug) = self.check_export_gate(*handle, &required_tags)
                    {
                        return EvalOut::Stopped(bug);
                    }
                    let effective_table = self
                        .ew
                        .schema_lock
                        .as_ref()
                        .and_then(|l| l.find_db(db))
                        .and_then(|d| d.resolve_table(table_name).ok())
                        .map_or_else(|| table_name.clone(), |t| t.name.clone());
                    let dry_run = self.ew.dry_run;
                    let conn = match self.ew.db_registry.open(db) {
                        Ok(c) => c,
                        Err(e) => {
                            return EvalOut::Ok(Val::ResErr(Box::new(Val::Text(e.to_string()))));
                        }
                    };
                    match conn.upsert_table(&effective_table, key_col, tv, dry_run) {
                        Ok(diff) => {
                            if dry_run {
                                let display_allow = match &self.prog.policy {
                                    Some(pol) => {
                                        let permitted: Vec<String> = self
                                            .ew
                                            .world
                                            .runtime_allow_export
                                            .elems()
                                            .iter()
                                            .filter(|t| pol.allow_console.contains(t))
                                            .cloned()
                                            .collect();
                                        TagSet::of_list(permitted)
                                    }
                                    None => self.ew.world.runtime_allow_export.clone(),
                                };
                                let rendered = diff.render_redacted(&display_allow);
                                let mut preview = format!(
                                    "[DRY-RUN] WriteTable({db}, \"{effective_table}\"):\n{rendered}"
                                );
                                if preview.ends_with('\n') {
                                    preview.pop();
                                }
                                self.ew.world.stdout.push(preview);
                            }
                            EvalOut::Ok(Val::ResOk(Box::new(Val::Ctor {
                                type_name: "__UpsertStats".to_string(),
                                ctor_name: "__UpsertStats".to_string(),
                                fields: vec![
                                    Val::Int(BigInt::from(diff.inserted as i64)),
                                    Val::Int(BigInt::from(diff.updated as i64)),
                                    Val::Int(BigInt::from(diff.unchanged as i64)),
                                ],
                            })))
                        }
                        Err(e) => EvalOut::Ok(Val::ResErr(Box::new(Val::Text(e.to_string())))),
                    }
                } else {
                    EvalOut::Failed("WriteTable.upsert expects (WriteTable, table)".to_string())
                }
            }
            ExecHostOp::RawSqlQuery {
                db,
                sql,
                out_schema,
            } => {
                if let [Val::CapRawReadDB(cap_db), params_val] = args {
                    let raw_params: &[Val] = match params_val {
                        Val::Tuple(xs) | Val::List(xs) => xs.as_slice(),
                        _ => {
                            return EvalOut::Failed(
                                "RawReadDB.raw_sql expects a tuple or list of scalar parameters"
                                    .to_string(),
                            );
                        }
                    };
                    let mut sql_params = Vec::with_capacity(raw_params.len());
                    for p in raw_params {
                        match SqlParam::from_val(p) {
                            Ok(sp) => sql_params.push(sp),
                            Err(e) => {
                                return EvalOut::Ok(Val::ResErr(Box::new(Val::Text(
                                    e.to_string(),
                                ))));
                            }
                        }
                    }
                    let target_db = if cap_db.is_empty() { db } else { cap_db };
                    let conn = match self.ew.db_registry.open(target_db) {
                        Ok(c) => c,
                        Err(e) => {
                            return EvalOut::Ok(Val::ResErr(Box::new(Val::Text(e.to_string()))));
                        }
                    };
                    match conn.query_rows(sql, &sql_params, out_schema) {
                        Ok(tv) => EvalOut::Ok(Val::ResOk(Box::new(Val::Table(tv)))),
                        Err(e) => EvalOut::Ok(Val::ResErr(Box::new(Val::Text(e.to_string())))),
                    }
                } else {
                    EvalOut::Failed("RawReadDB.raw_sql expects (RawReadDB, params)".to_string())
                }
            }
            ExecHostOp::ReadCsvEx {
                schema,
                error_on_bad_rows,
                coerce_integral_floats,
            } => match args {
                [Val::CapReadFiles(handle), Val::Text(path)] => self.eval_read_csv_with_opts(
                    schema,
                    *handle,
                    path,
                    *error_on_bad_rows,
                    *coerce_integral_floats,
                ),
                _ => EvalOut::Failed("read_csv expects (ReadFiles, path)".to_string()),
            },
            ExecHostOp::ReadXlsx { schema, sheet } => match args {
                [Val::CapReadFiles(handle), Val::Text(path)] => {
                    self.eval_read_xlsx(schema, *handle, path, sheet.as_deref())
                }
                [
                    Val::CapReadFiles(handle),
                    Val::Text(path),
                    Val::Text(dyn_sheet),
                ] => self.eval_read_xlsx(schema, *handle, path, Some(dyn_sheet.as_str())),
                _ => EvalOut::Failed("read_xlsx expects (ReadFiles, path[, sheet])".to_string()),
            },
            ExecHostOp::FakeHttps { host } => {
                let responses: Vec<(String, String)> = match args {
                    [Val::Map(pairs)] => pairs
                        .iter()
                        .map(|(k, v)| (format_display_val(k), format_display_val(v)))
                        .collect(),
                    [Val::Unit] | [] => Vec::new(),
                    _ => {
                        return EvalOut::Failed(
                            "Https.fake requires `responses: Map(Text, Text)`".to_string(),
                        );
                    }
                };
                let idx = self.ew.world.fake_https.len();
                self.ew.world.fake_https.push(FakeHttpsState {
                    host: host.clone(),
                    responses,
                    requests: Vec::new(),
                });
                EvalOut::Ok(Val::CapHttpsAllow {
                    handle: CapHandle::Fake(idx),
                    host: host.clone(),
                    allows: TagSet::empty(),
                })
            }
            ExecHostOp::JsonParseTable(schema_name) => {
                if let [resp_val, Val::Text(field)] = args {
                    self.eval_json_parse_table(resp_val, field, schema_name)
                } else {
                    EvalOut::Failed("parse_table expects (JsonResponse, field)".to_string())
                }
            }
            ExecHostOp::JsonBoolAt => {
                if let [resp_val, Val::Text(field)] = args {
                    let Some(jresp) = self.extract_json_response(resp_val) else {
                        return EvalOut::Failed("invalid JsonResponse handle".to_string());
                    };
                    match jresp.bool_at(field) {
                        Ok(b) => EvalOut::Ok(Val::Bool(b)),
                        Err(e) => EvalOut::Failed(e),
                    }
                } else {
                    EvalOut::Failed("bool_at expects (JsonResponse, field)".to_string())
                }
            }
            ExecHostOp::JsonTextAt => {
                if let [resp_val, Val::Text(field)] = args {
                    let Some(jresp) = self.extract_json_response(resp_val) else {
                        return EvalOut::Failed("invalid JsonResponse handle".to_string());
                    };
                    match jresp.text_at(field) {
                        Ok(s) => EvalOut::Ok(Val::Text(s)),
                        Err(e) => EvalOut::Failed(e),
                    }
                } else {
                    EvalOut::Failed("text_at expects (JsonResponse, field)".to_string())
                }
            }
            ExecHostOp::JsonIntAt => {
                if let [resp_val, Val::Text(field)] = args {
                    let Some(jresp) = self.extract_json_response(resp_val) else {
                        return EvalOut::Failed("invalid JsonResponse handle".to_string());
                    };
                    match jresp.int_at(field) {
                        Ok(n) => EvalOut::Ok(Val::Int(BigInt::from(n))),
                        Err(e) => EvalOut::Failed(e),
                    }
                } else {
                    EvalOut::Failed("int_at expects (JsonResponse, field)".to_string())
                }
            }
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
            (
                HostOp::ConsolePrintTable,
                [
                    Val::CapConsole { handle, .. },
                    tbl_val @ (Val::Table(_) | Val::Columnar(_)),
                ],
            ) => {
                let owned_tv;
                let tv: &TableVal = match tbl_val {
                    Val::Table(tv) => tv,
                    Val::Columnar(vm) => {
                        owned_tv = vm.to_table_val();
                        &owned_tv
                    }
                    _ => return EvalOut::Failed("console.print_table expects Table".to_string()),
                };
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
                self.eval_read_csv_with_opts(schema_name, *handle, path, false, false)
            }
            (
                HostOp::WriteFile
                | HostOp::WriteReportHtml
                | HostOp::WriteParquet
                | HostOp::WriteXlsx,
                [cap, path, payload],
            ) => self.eval_core_write_host(op.clone(), cap, path, payload, false),
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
            (HostOp::ReadParquet(schema_tt), [Val::CapReadFiles(handle), Val::Text(path)]) => {
                self.eval_read_parquet(schema_tt, *handle, path)
            }
            (
                HostOp::HttpsGetJson,
                [
                    Val::CapHttpsAllow {
                        handle,
                        host,
                        allows,
                    },
                    Val::Text(url),
                    hdr_val,
                ],
            ) => self.eval_https_get_json(*handle, host, allows, url, hdr_val),
            (HostOp::WriteTable | HostOp::RawSqlQuery { .. }, _) => EvalOut::Stopped(Bug {
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

    fn eval_read_csv_with_opts(
        &mut self,
        schema_name: &str,
        handle: CapHandle,
        path: &str,
        error_on_bad_rows: bool,
        coerce_integral_floats: bool,
    ) -> EvalOut {
        let Some(cs) = self.prog.find_schema(schema_name) else {
            return EvalOut::Failed(format!("unknown schema `{schema_name}`"));
        };
        let delimiter = if strip_compression_ext(path).ends_with(".tsv") {
            b'\t'
        } else {
            b','
        };
        let opts = CsvReadOptions {
            coerce_integral_floats,
        };
        let constraints = cs.constraints.clone();
        let schema_tt = cs.decl.schema.clone();
        let self_cols = build_constraint_self_cols(&schema_tt);
        let empty_env = RTEnv::new();

        let format_bad_err = |bad: &TableVal| -> EvalOut {
            let first = &bad.rows[0];
            let line_s = first
                .cells
                .first()
                .map_or_else(|| "?".to_string(), format_display_val);
            let col_s = first
                .cells
                .get(1)
                .map_or_else(|| "?".to_string(), format_display_val);
            let kind_s = first
                .cells
                .get(2)
                .map_or_else(|| "BadRow".to_string(), format_display_val);
            EvalOut::Ok(Val::ResErr(Box::new(Val::Text(format!(
                "{path}: {} invalid CSV row(s) under schema `{schema_name}` (first error at line {line_s}, column `{col_s}`: {kind_s})",
                bad.rows.len()
            )))))
        };

        if let Some(vm_cfg) = self.vm_cfg {
            let fast_constraints: Vec<FastColConstraint> = constraints
                .iter()
                .zip(&schema_tt.cols)
                .map(|(c_opt, col)| {
                    FastColConstraint::compile(c_opt.as_ref(), &col.ty, &|name| {
                        self.prog.find_const(name).map(|c| c.value.clone())
                    })
                })
                .collect();
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
                    read_csv_stream_to_vm_table_with_options(
                        reader,
                        &schema_tt,
                        delimiter,
                        vm_cfg.batch_size,
                        opts,
                        &fast_constraints,
                        |ci, val| {
                            self.eval_schema_constraint(
                                &self_cols,
                                &constraints,
                                ci,
                                val,
                                &empty_env,
                            )
                        },
                    )
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
                    read_csv_stream_to_vm_table_with_options(
                        reader,
                        &schema_tt,
                        delimiter,
                        vm_cfg.batch_size,
                        opts,
                        &fast_constraints,
                        |ci, val| {
                            self.eval_schema_constraint(
                                &self_cols,
                                &constraints,
                                ci,
                                val,
                                &empty_env,
                            )
                        },
                    )
                }
            };
            return match parsed {
                Ok((good_vm, bad)) => {
                    if error_on_bad_rows {
                        if !bad.rows.is_empty() {
                            format_bad_err(&bad)
                        } else {
                            EvalOut::Ok(Val::ResOk(Box::new(Val::Columnar(Arc::new(good_vm)))))
                        }
                    } else {
                        EvalOut::Ok(Val::ResOk(Box::new(Val::Tuple(vec![
                            Val::Columnar(Arc::new(good_vm)),
                            Val::Table(bad),
                        ]))))
                    }
                }
                Err(msg) => EvalOut::Ok(Val::ResErr(Box::new(Val::Text(msg)))),
            };
        }

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
                read_csv_stream_with_options(reader, &schema_tt, delimiter, opts, |ci, val| {
                    self.eval_schema_constraint(&self_cols, &constraints, ci, val, &empty_env)
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
                read_csv_stream_with_options(reader, &schema_tt, delimiter, opts, |ci, val| {
                    self.eval_schema_constraint(&self_cols, &constraints, ci, val, &empty_env)
                })
            }
        };
        match parsed {
            Ok((good, bad)) => {
                if error_on_bad_rows {
                    if !bad.rows.is_empty() {
                        format_bad_err(&bad)
                    } else {
                        EvalOut::Ok(Val::ResOk(Box::new(Val::Table(good))))
                    }
                } else {
                    EvalOut::Ok(Val::ResOk(Box::new(Val::Tuple(vec![
                        Val::Table(good),
                        Val::Table(bad),
                    ]))))
                }
            }
            Err(msg) => EvalOut::Ok(Val::ResErr(Box::new(Val::Text(msg)))),
        }
    }

    fn eval_read_jsonl(&mut self, schema_name: &str, handle: CapHandle, path: &str) -> EvalOut {
        let Some(cs) = self.prog.find_schema(schema_name) else {
            return EvalOut::Failed(format!("unknown schema `{schema_name}`"));
        };
        let constraints = cs.constraints.clone();
        let schema_tt = cs.decl.schema.clone();
        let self_cols = build_constraint_self_cols(&schema_tt);
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
                    self.eval_schema_constraint(&self_cols, &constraints, ci, val, &empty_env)
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
                    self.eval_schema_constraint(&self_cols, &constraints, ci, val, &empty_env)
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
        self_cols: &[[ColSpec; 1]],
        constraints: &[Option<ExecRowExpr>],
        ci: usize,
        val: &Val,
        empty_env: &RTEnv,
    ) -> bool {
        let Some(Some(re)) = constraints.get(ci) else {
            return true;
        };
        let Some(col_slice) = self_cols.get(ci) else {
            return false;
        };
        matches!(
            self.eval_row_expr(re, col_slice, std::slice::from_ref(val), empty_env),
            EvalOut::Ok(Val::Bool(true))
        )
    }

    fn eval_core_write_host(
        &mut self,
        op: HostOp,
        cap: &Val,
        path: &Val,
        payload: &Val,
        explicit_private: bool,
    ) -> EvalOut {
        let (
            Val::CapWriteFiles {
                handle,
                root,
                allows,
            },
            Val::Text(rel),
        ) = (cap, path)
        else {
            return EvalOut::Failed(format!(
                "write op `{op:?}` expects (WriteFiles, path, payload)"
            ));
        };
        if !self.ew.dry_run
            && let Some(bug) = self.check_export_gate(*handle, allows)
        {
            return EvalOut::Stopped(bug);
        }
        if !is_safe_relative_path(rel) {
            return EvalOut::Ok(Val::ResErr(Box::new(Val::Text(format!(
                "unsafe write path `{rel}`"
            )))));
        }
        let is_private = explicit_private || !allows.is_empty();
        let full_rel = join_confined_path(root, rel);
        match (op.clone(), payload) {
            (HostOp::WriteFile, Val::Text(content)) => {
                self.write_confined_output(*handle, &full_rel, content.clone(), is_private)
            }
            (HostOp::WriteReportHtml, Val::Report(rep)) => {
                let html = crate::viz::report::render_html_report(rep);
                self.write_confined_output(*handle, &full_rel, html, is_private)
            }
            (HostOp::WriteParquet, Val::Table(tv)) => {
                if matches!(handle, CapHandle::Real) && self.ew.dry_run {
                    self.ew.world.stdout.push(format!(
                        "[DRY-RUN] would write parquet \"{full_rel}\" ({} rows, {} cols)",
                        tv.rows.len(),
                        tv.cols.len()
                    ));
                    return EvalOut::Ok(Val::ResOk(Box::new(Val::Unit)));
                }
                match write_parquet_bytes(tv, ParquetCompression::Zstd) {
                    Ok(bytes) => self.write_confined_bytes(*handle, &full_rel, bytes, is_private),
                    Err(e) => EvalOut::Ok(Val::ResErr(Box::new(Val::Text(e)))),
                }
            }
            (HostOp::WriteParquet, Val::Columnar(vm)) => {
                if matches!(handle, CapHandle::Real) && self.ew.dry_run {
                    self.ew.world.stdout.push(format!(
                        "[DRY-RUN] would write parquet \"{full_rel}\" ({} rows, {} cols)",
                        vm.total_rows(),
                        vm.cols.len()
                    ));
                    return EvalOut::Ok(Val::ResOk(Box::new(Val::Unit)));
                }
                match write_parquet_vm_table_bytes(vm, ParquetCompression::Zstd) {
                    Ok(bytes) => self.write_confined_bytes(*handle, &full_rel, bytes, is_private),
                    Err(e) => EvalOut::Ok(Val::ResErr(Box::new(Val::Text(e)))),
                }
            }
            (HostOp::WriteXlsx, payload) => {
                let sheets: Vec<(String, TableVal)> = match payload {
                    Val::Table(tv) => vec![("Sheet1".to_string(), tv.clone())],
                    Val::Columnar(vm) => vec![("Sheet1".to_string(), vm.to_table_val())],
                    Val::Map(pairs) => {
                        let mut out = Vec::with_capacity(pairs.len());
                        for (k, v) in pairs {
                            let Some(tv) = v.to_table_val() else {
                                return EvalOut::Failed(
                                    "write_xlsx `sheets:` map values must be Tables".to_string(),
                                );
                            };
                            out.push((format_display_val(k), tv));
                        }
                        out
                    }
                    _ => {
                        return EvalOut::Failed(
                            "write_xlsx expects a Table or `sheets: Map(Text, Table)`".to_string(),
                        );
                    }
                };
                if matches!(handle, CapHandle::Real) && self.ew.dry_run {
                    self.ew.world.stdout.push(format!(
                        "[DRY-RUN] would write xlsx \"{full_rel}\" ({} sheet(s))",
                        sheets.len()
                    ));
                    return EvalOut::Ok(Val::ResOk(Box::new(Val::Unit)));
                }
                match write_xlsx_sheets(&sheets) {
                    Ok(bytes) => self.write_confined_bytes(*handle, &full_rel, bytes, is_private),
                    Err(e) => EvalOut::Ok(Val::ResErr(Box::new(Val::Text(e)))),
                }
            }
            _ => EvalOut::Failed(format!("invalid payload for `{op:?}`")),
        }
    }

    fn write_confined_table(
        &mut self,
        handle: CapHandle,
        full_rel: &str,
        tv: &TableVal,
        fmt: TableWriteFmt,
        private: bool,
    ) -> EvalOut {
        let comp = detect_compression_path(full_rel);
        match handle {
            CapHandle::Fake(idx) => {
                let text = match fmt {
                    TableWriteFmt::Csv {
                        delimiter,
                        sanitize_formulas,
                    } => format_csv_table_with_options(tv, delimiter, sanitize_formulas),
                    TableWriteFmt::Jsonl => format_jsonl_table(tv),
                };
                if let Some(ff) = self.ew.world.fake_files.get_mut(idx) {
                    ff.files.push((full_rel.to_string(), text));
                }
                EvalOut::Ok(Val::ResOk(Box::new(Val::Unit)))
            }
            CapHandle::Real => {
                if self.ew.dry_run {
                    self.ew.world.stdout.push(format!(
                        "[DRY-RUN] would write table \"{full_rel}\" ({} rows, {} cols)",
                        tv.rows.len(),
                        tv.cols.len()
                    ));
                    return EvalOut::Ok(Val::ResOk(Box::new(Val::Unit)));
                }
                if self.ew.live_io {
                    let res = write_file_maybe_private(
                        self.ew.work_dir.as_deref(),
                        full_rel,
                        private,
                        |file| {
                            let mut enc = AutoEncodeWriter::new(BufWriter::new(file), comp)?;
                            match fmt {
                                TableWriteFmt::Csv {
                                    delimiter,
                                    sanitize_formulas,
                                } => write_csv_table_with_options(
                                    &mut enc,
                                    tv,
                                    delimiter,
                                    sanitize_formulas,
                                )?,
                                TableWriteFmt::Jsonl => write_jsonl_table(&mut enc, tv)?,
                            }
                            enc.finish()?;
                            Ok(())
                        },
                    );
                    if let Err(e) = res {
                        return EvalOut::Ok(Val::ResErr(Box::new(Val::Text(e.to_string()))));
                    }
                } else {
                    let text = match fmt {
                        TableWriteFmt::Csv {
                            delimiter,
                            sanitize_formulas,
                        } => format_csv_table_with_options(tv, delimiter, sanitize_formulas),
                        TableWriteFmt::Jsonl => format_jsonl_table(tv),
                    };
                    self.ew
                        .world
                        .written_files
                        .push((full_rel.to_string(), text));
                }
                EvalOut::Ok(Val::ResOk(Box::new(Val::Unit)))
            }
        }
    }

    fn write_confined_vm_table(
        &mut self,
        handle: CapHandle,
        full_rel: &str,
        vm: &VmTable,
        fmt: TableWriteFmt,
        private: bool,
    ) -> EvalOut {
        let comp = detect_compression_path(full_rel);
        match handle {
            CapHandle::Fake(idx) => {
                let text = match fmt {
                    TableWriteFmt::Csv {
                        delimiter,
                        sanitize_formulas,
                    } => format_csv_vm_table_with_options(vm, delimiter, sanitize_formulas),
                    TableWriteFmt::Jsonl => format_jsonl_vm_table(vm),
                };
                if let Some(ff) = self.ew.world.fake_files.get_mut(idx) {
                    ff.files.push((full_rel.to_string(), text));
                }
                EvalOut::Ok(Val::ResOk(Box::new(Val::Unit)))
            }
            CapHandle::Real => {
                if self.ew.dry_run {
                    self.ew.world.stdout.push(format!(
                        "[DRY-RUN] would write table \"{full_rel}\" ({} rows, {} cols)",
                        vm.total_rows(),
                        vm.cols.len()
                    ));
                    return EvalOut::Ok(Val::ResOk(Box::new(Val::Unit)));
                }
                if self.ew.live_io {
                    let res = write_file_maybe_private(
                        self.ew.work_dir.as_deref(),
                        full_rel,
                        private,
                        |file| {
                            let mut enc = AutoEncodeWriter::new(BufWriter::new(file), comp)?;
                            match fmt {
                                TableWriteFmt::Csv {
                                    delimiter,
                                    sanitize_formulas,
                                } => write_csv_vm_table_with_options(
                                    &mut enc,
                                    vm,
                                    delimiter,
                                    sanitize_formulas,
                                )?,
                                TableWriteFmt::Jsonl => write_jsonl_vm_table(&mut enc, vm)?,
                            }
                            enc.finish()?;
                            Ok(())
                        },
                    );
                    if let Err(e) = res {
                        return EvalOut::Ok(Val::ResErr(Box::new(Val::Text(e.to_string()))));
                    }
                } else {
                    let text = match fmt {
                        TableWriteFmt::Csv {
                            delimiter,
                            sanitize_formulas,
                        } => format_csv_vm_table_with_options(vm, delimiter, sanitize_formulas),
                        TableWriteFmt::Jsonl => format_jsonl_vm_table(vm),
                    };
                    self.ew
                        .world
                        .written_files
                        .push((full_rel.to_string(), text));
                }
                EvalOut::Ok(Val::ResOk(Box::new(Val::Unit)))
            }
        }
    }

    fn write_confined_output(
        &mut self,
        handle: CapHandle,
        full_rel: &str,
        content: String,
        private: bool,
    ) -> EvalOut {
        match handle {
            CapHandle::Fake(idx) => {
                if let Some(ff) = self.ew.world.fake_files.get_mut(idx) {
                    ff.files.push((full_rel.to_string(), content));
                }
                EvalOut::Ok(Val::ResOk(Box::new(Val::Unit)))
            }
            CapHandle::Real => {
                if self.ew.dry_run {
                    self.ew.world.stdout.push(format!(
                        "[DRY-RUN] would write file \"{full_rel}\" ({} bytes)",
                        content.len()
                    ));
                    return EvalOut::Ok(Val::ResOk(Box::new(Val::Unit)));
                }
                if self.ew.live_io {
                    let comp = detect_compression_path(full_rel);
                    let write_res = write_file_maybe_private(
                        self.ew.work_dir.as_deref(),
                        full_rel,
                        private,
                        |file| {
                            if comp == CompressionKind::Plain {
                                file.write_all(content.as_bytes())
                            } else {
                                let mut enc = AutoEncodeWriter::new(BufWriter::new(file), comp)?;
                                enc.write_all(content.as_bytes())?;
                                enc.finish()?;
                                Ok(())
                            }
                        },
                    );
                    if let Err(e) = write_res {
                        return EvalOut::Ok(Val::ResErr(Box::new(Val::Text(e.to_string()))));
                    }
                } else {
                    self.ew
                        .world
                        .written_files
                        .push((full_rel.to_string(), content));
                }
                EvalOut::Ok(Val::ResOk(Box::new(Val::Unit)))
            }
        }
    }

    fn read_file_bytes(&self, handle: CapHandle, path: &str) -> Result<Vec<u8>, String> {
        match handle {
            CapHandle::Fake(idx) => {
                if let Some(files) = self.ew.fake_binary_files.get(&idx)
                    && let Some((_, bs)) = files.iter().find(|(p, _)| p == path)
                {
                    return Ok(bs.clone());
                }
                if let Some(ff) = self.ew.world.fake_files.get(idx)
                    && let Some((_, content)) = ff.files.iter().find(|(p, _)| p == path)
                {
                    return Ok(content.as_bytes().to_vec());
                }
                Err(format!("file not found: {path}"))
            }
            CapHandle::Real => {
                if !self.ew.live_io {
                    return Err(format!("file I/O disabled in spec mode: {path}"));
                }
                let resolved = match &self.ew.work_dir {
                    Some(base) if !Path::new(path).is_absolute() => base.join(path),
                    _ => std::path::PathBuf::from(path),
                };
                fs::read(&resolved).map_err(|e| format!("{path}: {e}"))
            }
        }
    }

    fn write_confined_bytes(
        &mut self,
        handle: CapHandle,
        full_rel: &str,
        bytes: Vec<u8>,
        private: bool,
    ) -> EvalOut {
        match handle {
            CapHandle::Fake(idx) => {
                self.ew
                    .fake_binary_files
                    .entry(idx)
                    .or_default()
                    .push((full_rel.to_string(), bytes));
                EvalOut::Ok(Val::ResOk(Box::new(Val::Unit)))
            }
            CapHandle::Real => {
                if self.ew.dry_run {
                    self.ew.world.stdout.push(format!(
                        "[DRY-RUN] would write binary file \"{full_rel}\" ({} bytes)",
                        bytes.len()
                    ));
                    return EvalOut::Ok(Val::ResOk(Box::new(Val::Unit)));
                }
                if self.ew.live_io {
                    let write_res = write_file_maybe_private(
                        self.ew.work_dir.as_deref(),
                        full_rel,
                        private,
                        |file| file.write_all(&bytes),
                    );
                    if let Err(e) = write_res {
                        return EvalOut::Ok(Val::ResErr(Box::new(Val::Text(e.to_string()))));
                    }
                } else {
                    self.ew
                        .written_binary_files
                        .push((full_rel.to_string(), bytes));
                }
                EvalOut::Ok(Val::ResOk(Box::new(Val::Unit)))
            }
        }
    }

    fn eval_read_parquet(&mut self, schema_tt: &TableTy, handle: CapHandle, path: &str) -> EvalOut {
        let bytes = match self.read_file_bytes(handle, path) {
            Ok(b) => b,
            Err(e) => return EvalOut::Ok(Val::ResErr(Box::new(Val::Text(e)))),
        };
        let constraints: Vec<Option<ExecRowExpr>> = self
            .prog
            .schemas
            .iter()
            .find(|cs| cs.decl.schema == *schema_tt)
            .or_else(|| {
                self.prog.schemas.iter().find(|cs| {
                    cs.decl.schema.cols.len() == schema_tt.cols.len()
                        && cs
                            .decl
                            .schema
                            .cols
                            .iter()
                            .zip(&schema_tt.cols)
                            .all(|(a, b)| a.name == b.name && a.ty == b.ty)
                })
            })
            .map_or_else(
                || vec![None; schema_tt.cols.len()],
                |cs| cs.constraints.clone(),
            );
        let self_cols = build_constraint_self_cols(schema_tt);
        let empty_env = RTEnv::new();
        if let Some(vm_cfg) = self.vm_cfg {
            let fast_constraints: Vec<FastColConstraint> = constraints
                .iter()
                .zip(&schema_tt.cols)
                .map(|(c_opt, col)| {
                    FastColConstraint::compile(c_opt.as_ref(), &col.ty, &|name| {
                        self.prog.find_const(name).map(|c| c.value.clone())
                    })
                })
                .collect();
            return match read_parquet_bytes_to_vm_table(
                &bytes,
                schema_tt,
                vm_cfg.batch_size,
                &fast_constraints,
                |ci, val| {
                    self.eval_schema_constraint(&self_cols, &constraints, ci, val, &empty_env)
                },
            ) {
                Ok(vm_tbl) => EvalOut::Ok(Val::ResOk(Box::new(Val::Columnar(Arc::new(vm_tbl))))),
                Err(msg) => EvalOut::Ok(Val::ResErr(Box::new(Val::Text(msg)))),
            };
        }
        match read_parquet_bytes_with_schema(&bytes, schema_tt, |ci, val| {
            self.eval_schema_constraint(&self_cols, &constraints, ci, val, &empty_env)
        }) {
            Ok(tv) => EvalOut::Ok(Val::ResOk(Box::new(Val::Table(tv)))),
            Err(msg) => EvalOut::Ok(Val::ResErr(Box::new(Val::Text(msg)))),
        }
    }

    fn eval_read_xlsx(
        &mut self,
        schema_name: &str,
        handle: CapHandle,
        path: &str,
        sheet: Option<&str>,
    ) -> EvalOut {
        let Some(cs) = self.prog.find_schema(schema_name) else {
            return EvalOut::Failed(format!("unknown schema `{schema_name}`"));
        };
        let constraints = cs.constraints.clone();
        let schema_tt = cs.decl.schema.clone();
        let self_cols = build_constraint_self_cols(&schema_tt);
        let bytes = match self.read_file_bytes(handle, path) {
            Ok(b) => b,
            Err(e) => return EvalOut::Ok(Val::ResErr(Box::new(Val::Text(e)))),
        };
        let empty_env = RTEnv::new();
        match read_xlsx_bytes_with_schema(&bytes, sheet, &schema_tt, |ci, val| {
            self.eval_schema_constraint(&self_cols, &constraints, ci, val, &empty_env)
        }) {
            Ok((good, bad)) => EvalOut::Ok(Val::ResOk(Box::new(Val::Tuple(vec![
                Val::Table(good),
                Val::Table(bad),
            ])))),
            Err(msg) => EvalOut::Ok(Val::ResErr(Box::new(Val::Text(msg)))),
        }
    }

    fn eval_https_get_json(
        &mut self,
        handle: CapHandle,
        host: &str,
        allows: &TagSet,
        url: &str,
        hdr_val: &Val,
    ) -> EvalOut {
        let req_headers: Vec<(String, String)> = match hdr_val {
            Val::Unit => Vec::new(),
            Val::Map(pairs) => pairs
                .iter()
                .map(|(k, v)| (format_display_val(k), format_display_val(v)))
                .collect(),
            _ => {
                return EvalOut::Failed(
                    "HttpsAllow.get_json `headers:` must be a Map(Text, Text)".to_string(),
                );
            }
        };

        match handle {
            CapHandle::Fake(idx) => {
                let parsed = match ParsedHttpsUrl::parse_and_check_host(url, host) {
                    Ok(p) => p,
                    Err(e) => return EvalOut::Ok(Val::ResErr(Box::new(Val::Text(e.to_string())))),
                };
                let Some(fh) = self.ew.world.fake_https.get_mut(idx) else {
                    return EvalOut::Ok(Val::ResErr(Box::new(Val::Text(
                        "invalid fake HTTPS handle".to_string(),
                    ))));
                };
                fh.requests.push(url.to_string());
                let body_opt = fh
                    .responses
                    .iter()
                    .find(|(k, _)| k == url || k == &parsed.path_and_query)
                    .map(|(_, v)| v.clone());
                let Some(body) = body_opt else {
                    return EvalOut::Ok(Val::ResErr(Box::new(Val::Text(format!(
                        "no fake HTTPS response registered for `{url}`"
                    )))));
                };
                match JsonResponse::from_json_str(&body) {
                    Ok(jresp) => {
                        let resp_idx = self.ew.json_responses.len();
                        self.ew.json_responses.push(jresp);
                        EvalOut::Ok(Val::ResOk(Box::new(make_json_response_val(resp_idx))))
                    }
                    Err(e) => EvalOut::Ok(Val::ResErr(Box::new(Val::Text(e.to_string())))),
                }
            }
            CapHandle::Real => {
                let cap_ty = Ty::HttpsAllow {
                    host: host.to_string(),
                    allows: allows.clone(),
                };
                if let Err(err) = check_cap_against_policy(self.prog.policy.as_ref(), &cap_ty) {
                    return EvalOut::Stopped(Bug {
                        kind: BugKind::ExportGateDenied,
                        message: err.message,
                    });
                }
                if let Some(bug) = self.check_export_gate(handle, allows) {
                    return EvalOut::Stopped(bug);
                }
                if !self.ew.live_io {
                    return EvalOut::Ok(Val::ResErr(Box::new(Val::Text(format!(
                        "HTTPS I/O disabled in spec mode: {url}"
                    )))));
                }
                let https_cfg = HttpsClientConfig {
                    ca_cert_path: self
                        .ew
                        .https_ca_cert
                        .as_ref()
                        .map(|p| p.to_string_lossy().into_owned()),
                    ..HttpsClientConfig::default()
                };
                match https_get_json(url, host, &req_headers, &https_cfg) {
                    Ok(jresp) => {
                        let resp_idx = self.ew.json_responses.len();
                        self.ew.json_responses.push(jresp);
                        EvalOut::Ok(Val::ResOk(Box::new(make_json_response_val(resp_idx))))
                    }
                    Err(e) => EvalOut::Ok(Val::ResErr(Box::new(Val::Text(e.to_string())))),
                }
            }
        }
    }

    fn extract_json_response(&self, val: &Val) -> Option<&JsonResponse> {
        if let Val::Ctor {
            type_name, fields, ..
        } = val
            && type_name == "__JsonResponse"
            && let Some(Val::Int(n)) = fields.first()
            && let Some(idx) = n.to_usize()
        {
            return self.ew.json_responses.get(idx);
        }
        None
    }

    fn eval_json_parse_table(&mut self, resp_val: &Val, field: &str, schema_name: &str) -> EvalOut {
        let Some(cs) = self.prog.find_schema(schema_name) else {
            return EvalOut::Failed(format!("unknown schema `{schema_name}`"));
        };
        let constraints = cs.constraints.clone();
        let schema_tt = cs.decl.schema.clone();
        let self_cols = build_constraint_self_cols(&schema_tt);
        let Some(jresp) = self.extract_json_response(resp_val).cloned() else {
            return EvalOut::Failed("invalid JsonResponse handle".to_string());
        };
        let empty_env = RTEnv::new();
        match jresp.parse_table(field, &schema_tt, |ci, val| {
            self.eval_schema_constraint(&self_cols, &constraints, ci, val, &empty_env)
        }) {
            Ok((good, bad)) => EvalOut::Ok(Val::Tuple(vec![Val::Table(good), Val::Table(bad)])),
            Err(e) => EvalOut::Failed(e),
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
                    return outer_env.get(name).map(|v| v.as_ref().clone()).map_or_else(
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
                        let stored = self
                            .ew
                            .world
                            .fake_dbs
                            .get(idx)
                            .and_then(|db| find_fake_db_table(db, table_name));
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
                    Val::CapReadDB {
                        handle: CapHandle::Real,
                        ref db,
                    } => {
                        let effective_table = self
                            .ew
                            .schema_lock
                            .as_ref()
                            .and_then(|l| l.find_db(db))
                            .and_then(|d| d.resolve_table(table_name).ok())
                            .map_or_else(|| table_name.clone(), |t| t.name.clone());
                        let conn = match self.ew.db_registry.open(db) {
                            Ok(c) => c,
                            Err(e) => return EvalOut::Stopped(map_db_err_to_bug(e)),
                        };
                        let table_sql = conn.resolve_table_sql_ref(&effective_table);
                        let cols_sql: Vec<String> = schema
                            .cols
                            .iter()
                            .map(|c| quote_sql_ident(&c.name))
                            .collect();
                        let sql = if cols_sql.is_empty() {
                            format!("SELECT 1 FROM {table_sql}")
                        } else {
                            format!("SELECT {} FROM {table_sql}", cols_sql.join(", "))
                        };
                        match conn.query_rows(&sql, &[], schema) {
                            Ok(tv) => EvalOut::Ok(Val::Table(tv)),
                            Err(e) => EvalOut::Stopped(map_db_err_to_bug(e)),
                        }
                    }
                    _ => EvalOut::Stopped(Bug {
                        kind: BugKind::OutsideBoundary,
                        message: "expected ReadDB capability handle".to_string(),
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
                        ExecDeriveItem::SummaryCol {
                            name,
                            expr,
                            agg_kind,
                        } => {
                            let existing_idx = tv.cols.iter().position(|c| c.name == *name);
                            let mut new_vals = Vec::with_capacity(tv.rows.len());
                            for row in &tv.rows {
                                match self.eval_row_expr(expr, &tv.cols, &row.cells, env) {
                                    EvalOut::Ok(v) => new_vals.push(v),
                                    other => return other,
                                }
                            }
                            if let Some(idx) = existing_idx {
                                tv.cols[idx].agg_kind = *agg_kind;
                                for (row, v) in tv.rows.iter_mut().zip(new_vals) {
                                    row.cells[idx] = v;
                                }
                            } else {
                                tv.cols.push(ColSpec {
                                    name: name.clone(),
                                    ty: ScalarTy::Unit,
                                    tags: TagSet::empty(),
                                    bucketed: false,
                                    agg_kind: *agg_kind,
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
                        ExecDeriveItem::CoarsenCol {
                            name,
                            source,
                            allow,
                            other,
                        } => {
                            let Some(src_idx) = tv.cols.iter().position(|c| c.name == *source)
                            else {
                                return EvalOut::Failed(format!("coarsen: missing col `{source}`"));
                            };
                            let src_tags = tv.cols[src_idx].tags.clone();
                            let existing_idx = tv.cols.iter().position(|c| c.name == *name);
                            let mut new_vals = Vec::with_capacity(tv.rows.len());
                            for row in &tv.rows {
                                let kept = match unwrap_opt_ref(&row.cells[src_idx]) {
                                    Some(Val::Text(s)) if allow.iter().any(|a| a == s) => s.clone(),
                                    _ => other.clone(),
                                };
                                new_vals.push(Val::Text(kept));
                            }
                            if let Some(idx) = existing_idx {
                                tv.cols[idx].ty = ScalarTy::Text;
                                tv.cols[idx].tags = src_tags;
                                tv.cols[idx].bucketed = true;
                                tv.cols[idx].agg_kind = AggKind::Raw;
                                for (row, v) in tv.rows.iter_mut().zip(new_vals) {
                                    row.cells[idx] = v;
                                }
                            } else {
                                tv.cols.push(ColSpec {
                                    name: name.clone(),
                                    ty: ScalarTy::Text,
                                    tags: src_tags,
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
            ExecPlan::DedupeBy {
                keys,
                order_by,
                keep,
                ..
            } => {
                if keys.is_empty() {
                    return EvalOut::Failed(
                        "dedupe_by requires at least one key column".to_string(),
                    );
                }
                let mut key_idxs = Vec::with_capacity(keys.len());
                for k in keys {
                    let Some(idx) = tv.cols.iter().position(|c| c.name == *k) else {
                        return EvalOut::Failed(format!("dedupe_by: missing column `{k}`"));
                    };
                    key_idxs.push(idx);
                }
                let mut order_specs = Vec::with_capacity(order_by.len());
                for (c, dir) in order_by {
                    let Some(idx) = tv.cols.iter().position(|cs| cs.name == *c) else {
                        return EvalOut::Failed(format!("dedupe_by: missing order column `{c}`"));
                    };
                    order_specs.push((idx, *dir));
                }
                let mut seen: HashMap<u64, Vec<usize>> = HashMap::new();
                for (ri, r) in tv.rows.iter().enumerate() {
                    let key_vals: Vec<Val> =
                        key_idxs.iter().map(|&ki| r.cells[ki].clone()).collect();
                    let h = hash_val_slice(&key_vals);
                    let bucket = seen.entry(h).or_default();
                    if let Some(slot) = bucket.iter_mut().find(|&&mut wi| {
                        key_idxs
                            .iter()
                            .all(|&ki| val_eq(&tv.rows[wi].cells[ki], &r.cells[ki]))
                    }) {
                        let wi = *slot;
                        let mut ord = std::cmp::Ordering::Equal;
                        for &(ci, dir) in &order_specs {
                            let c_ord = val_cmp(&r.cells[ci], &tv.rows[wi].cells[ci]);
                            let directed = match dir {
                                SortDir::Asc => c_ord,
                                SortDir::Desc => c_ord.reverse(),
                            };
                            if directed != std::cmp::Ordering::Equal {
                                ord = directed;
                                break;
                            }
                        }
                        let replace = match keep {
                            DedupeKeep::First => ord == std::cmp::Ordering::Less,
                            DedupeKeep::Last => ord != std::cmp::Ordering::Less,
                        };
                        if replace {
                            *slot = ri;
                        }
                    } else {
                        bucket.push(ri);
                    }
                }
                let mut win_indices: Vec<usize> = seen.into_values().flatten().collect();
                win_indices.sort_unstable();
                let mut rows_opt: Vec<Option<TableRow>> = tv.rows.into_iter().map(Some).collect();
                let out_rows: Vec<TableRow> = win_indices
                    .into_iter()
                    .filter_map(|i| {
                        let mut row = rows_opt.get_mut(i)?.take()?;
                        row.group_meta = None;
                        Some(row)
                    })
                    .collect();
                let out_cols = tv
                    .cols
                    .into_iter()
                    .map(|mut c| {
                        c.agg_kind = AggKind::Raw;
                        c
                    })
                    .collect();
                EvalOut::Ok(Val::Table(TableVal {
                    cols: out_cols,
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
            ExecPlan::Shuffle { seed, .. } => {
                let seed_val = match self.eval_expr(seed, env) {
                    EvalOut::Ok(v) => v,
                    other => return other,
                };
                let Val::Int(ref n) = seed_val else {
                    return EvalOut::Failed("shuffle(seed:) expects Int".to_string());
                };
                let mut tv = tv;
                for r in &mut tv.rows {
                    r.group_meta = None;
                }
                fisher_yates_shuffle(&mut tv.rows, seed_from_bigint(n));
                EvalOut::Ok(Val::Table(tv))
            }
            ExecPlan::SuppressSmallCells {
                by_cols,
                min_k,
                distinct_by,
                ..
            } => eval_suppress_small_cells_table(
                tv,
                by_cols,
                &self.prog.min_cell_floor().max(min_k.clone()),
                distinct_by.as_deref(),
            ),
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
            ExecPlan::PivotLonger {
                cols,
                names_to,
                values_to,
                value_ty,
                value_tags,
                ..
            } => eval_pivot_longer(tv, cols, names_to, values_to, value_ty, value_tags),
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

fn eval_agg_values(op: ExecAggOp, vals: &[Val], row_count: usize) -> EvalOut {
    let op = match op {
        ExecAggOp::CountIf => {
            let cnt = vals
                .iter()
                .filter(|v| matches!(unwrap_opt_ref(v), Some(Val::Bool(true))))
                .count();
            return EvalOut::Ok(Val::Int(BigInt::from(cnt)));
        }
        ExecAggOp::Core(c) => c,
    };
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
    eval_agg_values(ExecAggOp::Core(op), &vals, tv.rows.len())
}

fn eval_vm_table_col_agg(vm: &VmTable, col: &str, op: AggOp) -> EvalOut {
    let Some(idx) = vm.find_col_idx(col) else {
        return EvalOut::Failed(format!("unknown column `{col}`"));
    };
    let total_rows = vm.total_rows();
    if total_rows == 0 {
        return match op {
            AggOp::Sum => match &vm.cols[idx].ty {
                ScalarTy::Decimal => EvalOut::Ok(Val::Decimal(BigInt::ZERO)),
                ScalarTy::Float => EvalOut::Ok(Val::Float(Float64::ZERO)),
                _ => EvalOut::Ok(Val::Int(BigInt::ZERO)),
            },
            AggOp::Mean | AggOp::Stddev => EvalOut::Ok(Val::OptNone),
            _ => eval_agg_values(ExecAggOp::Core(op), &[], 0),
        };
    }

    // Check if all non-empty batches share a uniform typed numeric layout.
    enum NumLayout {
        Int,
        Decimal,
        Float,
        Other,
    }
    let mut layout: Option<NumLayout> = None;
    for b in &vm.batches {
        if b.is_empty() {
            continue;
        }
        let k = match &b.cols[idx].data {
            ColumnData::Int(_) => NumLayout::Int,
            ColumnData::Decimal(_) => NumLayout::Decimal,
            ColumnData::Float(_) => NumLayout::Float,
            _ => NumLayout::Other,
        };
        match (&layout, &k) {
            (None, _) => layout = Some(k),
            (Some(NumLayout::Int), NumLayout::Int)
            | (Some(NumLayout::Decimal), NumLayout::Decimal)
            | (Some(NumLayout::Float), NumLayout::Float) => {}
            _ => {
                layout = Some(NumLayout::Other);
                break;
            }
        }
    }

    match (op, layout.unwrap_or(NumLayout::Other)) {
        (AggOp::Sum, NumLayout::Int) => {
            let mut sum: i128 = 0;
            let mut overflow: Option<BigInt> = None;
            let mut seen_any = false;
            for b in &vm.batches {
                let c = &b.cols[idx];
                if let ColumnData::Int(vs) = &c.data {
                    for &r_u16 in &b.active_indices() {
                        let r = usize::from(r_u16);
                        if c.validity.as_ref().is_some_and(|bm| !bm.is_valid(r)) {
                            continue;
                        }
                        seen_any = true;
                        let v = vs[r];
                        if let Some(big) = &mut overflow {
                            *big = &*big + &BigInt::from(v);
                        } else if let Some(next) = sum.checked_add(i128::from(v)) {
                            sum = next;
                        } else {
                            overflow = Some(&BigInt::from(sum) + &BigInt::from(v));
                        }
                    }
                }
            }
            if !seen_any {
                return EvalOut::Ok(Val::Int(BigInt::ZERO));
            }
            if let Some(big) = overflow {
                if big.in_int64_range() {
                    EvalOut::Ok(Val::Int(big))
                } else {
                    EvalOut::Stopped(Bug {
                        kind: BugKind::IntOverflow,
                        message: "sum Int64 overflow".to_string(),
                    })
                }
            } else if let Ok(v) = i64::try_from(sum) {
                EvalOut::Ok(Val::Int(BigInt::from(v)))
            } else {
                EvalOut::Stopped(Bug {
                    kind: BugKind::IntOverflow,
                    message: "sum Int64 overflow".to_string(),
                })
            }
        }
        (AggOp::Sum, NumLayout::Decimal) => {
            let mut sum: i128 = 0;
            let mut overflow: Option<BigInt> = None;
            let mut seen_any = false;
            for b in &vm.batches {
                let c = &b.cols[idx];
                if let ColumnData::Decimal(vs) = &c.data {
                    for &r_u16 in &b.active_indices() {
                        let r = usize::from(r_u16);
                        if c.validity.as_ref().is_some_and(|bm| !bm.is_valid(r)) {
                            continue;
                        }
                        seen_any = true;
                        let d = vs[r];
                        if let Some(big) = &mut overflow {
                            *big = &*big + &BigInt::from(d);
                        } else if let Some(next) = sum.checked_add(d) {
                            sum = next;
                        } else {
                            overflow = Some(&BigInt::from(sum) + &BigInt::from(d));
                        }
                    }
                }
            }
            if !seen_any {
                return EvalOut::Ok(Val::Int(BigInt::ZERO));
            }
            if let Some(big) = overflow {
                if big.in_decimal_range() {
                    EvalOut::Ok(Val::Decimal(big))
                } else {
                    EvalOut::Stopped(Bug {
                        kind: BugKind::DecimalOverflow,
                        message: "sum Decimal overflow".to_string(),
                    })
                }
            } else if (DEC_MIN..=DEC_MAX).contains(&sum) {
                EvalOut::Ok(Val::Decimal(BigInt::from(sum)))
            } else {
                EvalOut::Stopped(Bug {
                    kind: BugKind::DecimalOverflow,
                    message: "sum Decimal overflow".to_string(),
                })
            }
        }
        (AggOp::Sum, NumLayout::Float) => {
            let mut sum = 0.0_f64;
            let mut seen_any = false;
            for b in &vm.batches {
                let c = &b.cols[idx];
                if let ColumnData::Float(vs) = &c.data {
                    for &r_u16 in &b.active_indices() {
                        let r = usize::from(r_u16);
                        if c.validity.as_ref().is_some_and(|bm| !bm.is_valid(r)) {
                            continue;
                        }
                        seen_any = true;
                        sum += f64::from_bits(vs[r]);
                    }
                }
            }
            if !seen_any {
                EvalOut::Ok(Val::Int(BigInt::ZERO))
            } else {
                EvalOut::Ok(Val::Float(Float64::from_f64(sum)))
            }
        }
        (AggOp::Mean, NumLayout::Decimal) => {
            let mut sum: i128 = 0;
            let mut overflow: Option<BigInt> = None;
            let mut count = 0usize;
            for b in &vm.batches {
                let c = &b.cols[idx];
                if let ColumnData::Decimal(vs) = &c.data {
                    for &r_u16 in &b.active_indices() {
                        let r = usize::from(r_u16);
                        if c.validity.as_ref().is_some_and(|bm| !bm.is_valid(r)) {
                            continue;
                        }
                        count += 1;
                        let d = vs[r];
                        if let Some(big) = &mut overflow {
                            *big = &*big + &BigInt::from(d);
                        } else if let Some(next) = sum.checked_add(d) {
                            sum = next;
                        } else {
                            overflow = Some(&BigInt::from(sum) + &BigInt::from(d));
                        }
                    }
                }
            }
            if count == 0 {
                return EvalOut::Ok(Val::OptNone);
            }
            let q = if let Some(big) = overflow {
                let denom = BigInt::from(count);
                if big.is_negative() {
                    -big.abs().div_euclid(&denom).unwrap_or(BigInt::ZERO)
                } else {
                    big.div_euclid(&denom).unwrap_or(BigInt::ZERO)
                }
            } else {
                BigInt::from(sum / (count as i128))
            };
            EvalOut::Ok(Val::OptSome(Box::new(Val::Decimal(q))))
        }
        (AggOp::Mean, NumLayout::Float | NumLayout::Int) => {
            let mut sum = 0.0_f64;
            let mut count = 0usize;
            for b in &vm.batches {
                let c = &b.cols[idx];
                match &c.data {
                    ColumnData::Float(vs) => {
                        for &r_u16 in &b.active_indices() {
                            let r = usize::from(r_u16);
                            if c.validity.as_ref().is_some_and(|bm| !bm.is_valid(r)) {
                                continue;
                            }
                            sum += f64::from_bits(vs[r]);
                            count += 1;
                        }
                    }
                    ColumnData::Int(vs) => {
                        for &r_u16 in &b.active_indices() {
                            let r = usize::from(r_u16);
                            if c.validity.as_ref().is_some_and(|bm| !bm.is_valid(r)) {
                                continue;
                            }
                            sum += vs[r] as f64;
                            count += 1;
                        }
                    }
                    _ => {}
                }
            }
            if count == 0 {
                EvalOut::Ok(Val::OptNone)
            } else {
                EvalOut::Ok(Val::OptSome(Box::new(Val::Float(Float64::from_f64(
                    sum / (count as f64),
                )))))
            }
        }
        (AggOp::Stddev, NumLayout::Float | NumLayout::Int) => {
            let mut fs = Vec::with_capacity(total_rows);
            for b in &vm.batches {
                let c = &b.cols[idx];
                match &c.data {
                    ColumnData::Float(vs) => {
                        for &r_u16 in &b.active_indices() {
                            let r = usize::from(r_u16);
                            if c.validity.as_ref().is_some_and(|bm| !bm.is_valid(r)) {
                                continue;
                            }
                            fs.push(f64::from_bits(vs[r]));
                        }
                    }
                    ColumnData::Int(vs) => {
                        for &r_u16 in &b.active_indices() {
                            let r = usize::from(r_u16);
                            if c.validity.as_ref().is_some_and(|bm| !bm.is_valid(r)) {
                                continue;
                            }
                            fs.push(vs[r] as f64);
                        }
                    }
                    _ => {}
                }
            }
            if fs.len() < 2 {
                return EvalOut::Ok(Val::OptNone);
            }
            let mean = fs.iter().sum::<f64>() / (fs.len() as f64);
            let var =
                fs.iter().map(|&x| (x - mean) * (x - mean)).sum::<f64>() / ((fs.len() - 1) as f64);
            EvalOut::Ok(Val::OptSome(Box::new(Val::Float(Float64::from_f64(
                var.sqrt(),
            )))))
        }
        _ => {
            let mut vals = Vec::with_capacity(total_rows);
            for b in &vm.batches {
                let c = &b.cols[idx];
                for &r_u16 in &b.active_indices() {
                    vals.push(c.get_val(usize::from(r_u16)));
                }
            }
            eval_agg_values(ExecAggOp::Core(op), &vals, total_rows)
        }
    }
}

fn unary_plan_input(plan: &ExecPlan) -> Option<&ExecPlan> {
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
        if is_left {
            c.ty = crate::core::check::ensure_option_scalar(&c.ty);
        }
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
                        match eval_agg_values(ExecAggOp::Core(AggOp::Sum), &slice, slice.len()) {
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

fn eval_pivot_longer(
    tv: TableVal,
    cols: &[Ident],
    names_to: &str,
    values_to: &str,
    value_ty: &ScalarTy,
    value_tags: &TagSet,
) -> EvalOut {
    let mut melt_idxs = Vec::with_capacity(cols.len());
    let mut eff_val_tags = value_tags.clone();
    for cn in cols {
        let Some(idx) = tv.cols.iter().position(|c| &c.name == cn) else {
            return EvalOut::Failed(format!("pivot_longer: missing column `{cn}`"));
        };
        eff_val_tags = eff_val_tags.union(&tv.cols[idx].tags);
        melt_idxs.push(idx);
    }
    let id_idxs: Vec<usize> = (0..tv.cols.len())
        .filter(|i| !melt_idxs.contains(i))
        .collect();

    let mut out_cols: Vec<ColSpec> = id_idxs
        .iter()
        .map(|&i| ColSpec {
            agg_kind: AggKind::Raw,
            ..tv.cols[i].clone()
        })
        .collect();
    out_cols.push(ColSpec {
        name: names_to.to_string(),
        ty: ScalarTy::Text,
        tags: TagSet::empty(),
        bucketed: false,
        agg_kind: AggKind::Raw,
    });
    out_cols.push(ColSpec {
        name: values_to.to_string(),
        ty: value_ty.clone(),
        tags: eff_val_tags,
        bucketed: false,
        agg_kind: AggKind::Raw,
    });

    let mut out_rows = Vec::with_capacity(tv.rows.len().saturating_mul(cols.len()));
    for r in &tv.rows {
        let base_ids: Vec<Val> = id_idxs.iter().map(|&i| r.cells[i].clone()).collect();
        for (cn, &mi) in cols.iter().zip(&melt_idxs) {
            let mut cells = Vec::with_capacity(base_ids.len() + 2);
            cells.extend(base_ids.iter().cloned());
            cells.push(Val::Text(cn.clone()));
            cells.push(coerce_cell_to_scalar(r.cells[mi].clone(), value_ty));
            out_rows.push(TableRow {
                cells,
                group_meta: None,
            });
        }
    }

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

fn match_pattern_take(pat: &ExecPattern, val: &mut Val) -> Option<Vec<(Ident, Val)>> {
    match pat {
        ExecPattern::Wildcard => Some(Vec::new()),
        ExecPattern::Bind(name) => Some(vec![(name.clone(), std::mem::take(val))]),
        ExecPattern::Lit(l) => {
            if val_eq(&eval_literal(l), val) {
                Some(Vec::new())
            } else {
                None
            }
        }
        ExecPattern::ListExact(binders) => match val {
            Val::List(xs) if xs.len() == binders.len() => {
                let moved = std::mem::take(xs);
                Some(binders.iter().cloned().zip(moved).collect())
            }
            _ => None,
        },
        ExecPattern::Ctor { ctor, binders } => match (ctor.as_str(), val) {
            ("Ok", Val::ResOk(v)) if binders.len() == 1 => {
                Some(vec![(binders[0].clone(), std::mem::take(v.as_mut()))])
            }
            ("Error", Val::ResErr(v)) if binders.len() == 1 => {
                Some(vec![(binders[0].clone(), std::mem::take(v.as_mut()))])
            }
            ("Some", Val::OptSome(v)) if binders.len() == 1 => {
                Some(vec![(binders[0].clone(), std::mem::take(v.as_mut()))])
            }
            ("None", Val::OptNone) if binders.is_empty() => Some(Vec::new()),
            (
                c,
                Val::Ctor {
                    ctor_name, fields, ..
                },
            ) if c == ctor_name && fields.len() == binders.len() => {
                let moved = std::mem::take(fields);
                Some(binders.iter().cloned().zip(moved).collect())
            }
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

#[inline]
fn column_data_matches_scalar(data: &ColumnData, ty: &ScalarTy) -> bool {
    matches!(
        (data, ty),
        (ColumnData::Unit(_), ScalarTy::Unit)
            | (ColumnData::Bool(_), ScalarTy::Bool)
            | (ColumnData::Int(_), ScalarTy::Int)
            | (ColumnData::Decimal(_), ScalarTy::Decimal)
            | (ColumnData::Float(_), ScalarTy::Float)
            | (ColumnData::Text { .. }, ScalarTy::Text)
            | (ColumnData::Bytes { .. }, ScalarTy::Bytes)
            | (ColumnData::Date(_), ScalarTy::Date)
            | (ColumnData::Timestamp(_), ScalarTy::Timestamp)
            | (ColumnData::Duration(_), ScalarTy::Duration)
    )
}

fn vm_table_matches_schema_exact(vm: &VmTable, dst_tt: &TableTy) -> bool {
    if vm.cols.len() != dst_tt.cols.len() {
        return false;
    }
    if !vm.cols.iter().zip(&dst_tt.cols).all(|(sc, dc)| sc == dc) {
        return false;
    }
    for b in &vm.batches {
        if b.cols.len() != dst_tt.cols.len() {
            return false;
        }
        for (col, dc) in b.cols.iter().zip(&dst_tt.cols) {
            if col.spec != *dc {
                return false;
            }
            match &dc.ty {
                ScalarTy::Option(inner) => {
                    if inner.is_option()
                        || col.validity.is_none()
                        || !column_data_matches_scalar(&col.data, inner)
                    {
                        return false;
                    }
                }
                other => {
                    if col.validity.is_some() || !column_data_matches_scalar(&col.data, other) {
                        return false;
                    }
                }
            }
        }
    }
    true
}

fn coerce_vm_column_data(
    src_data: &ColumnData,
    target: &ScalarTy,
    validity: Option<NullBitmap>,
    spec: &ColSpec,
) -> Option<Column> {
    if column_data_matches_scalar(src_data, target) {
        return Some(Column {
            spec: spec.clone(),
            data: src_data.clone(),
            validity,
        });
    }
    match (src_data, target) {
        (ColumnData::Int(vs), ScalarTy::Float) => Some(Column {
            spec: spec.clone(),
            data: ColumnData::Float(
                vs.iter()
                    .map(|&n| Float64::from_f64(n as f64).bits)
                    .collect(),
            ),
            validity,
        }),
        (ColumnData::Int(vs), ScalarTy::Decimal) => Some(Column {
            spec: spec.clone(),
            data: ColumnData::Decimal(vs.iter().map(|&n| i128::from(n) * DEC_SCALE).collect()),
            validity,
        }),
        (ColumnData::Decimal(vs), ScalarTy::Float) => {
            let mut scratch = String::with_capacity(48);
            let mut out = Vec::with_capacity(vs.len());
            for &d in vs {
                scratch.clear();
                render_decimal_i128_into(&mut scratch, d);
                let f = scratch.parse::<f64>().unwrap_or(0.0);
                out.push(Float64::from_f64(f).bits);
            }
            Some(Column {
                spec: spec.clone(),
                data: ColumnData::Float(out),
                validity,
            })
        }
        _ => None,
    }
}

fn coerce_vm_column(sc: &Column, dc: &ColSpec, batch_len: usize) -> Column {
    if !matches!(sc.data, ColumnData::Generic(_)) {
        match &dc.ty {
            ScalarTy::Option(inner) if !inner.is_option() => {
                let out_validity = Some(
                    sc.validity
                        .clone()
                        .unwrap_or_else(|| NullBitmap::all_valid(batch_len)),
                );
                if let Some(col) = coerce_vm_column_data(&sc.data, inner, out_validity, dc) {
                    return col;
                }
            }
            other if !matches!(other, ScalarTy::Option(_)) && sc.validity.is_none() => {
                if let Some(col) = coerce_vm_column_data(&sc.data, other, None, dc) {
                    return col;
                }
            }
            _ => {}
        }
    }
    let vals: Vec<Val> = (0..batch_len)
        .map(|r| coerce_cell_to_scalar(sc.get_val(r), &dc.ty))
        .collect();
    Column::from_vals(dc.clone(), &vals)
}

fn coerce_vm_table(vm: &VmTable, dst_tt: &TableTy) -> VmTable {
    let src_idxs: Vec<Option<usize>> = dst_tt
        .cols
        .iter()
        .map(|dc| vm.cols.iter().position(|sc| sc.name == dc.name))
        .collect();
    let mut batches = Vec::with_capacity(vm.batches.len());
    for b in &vm.batches {
        let mut cols = Vec::with_capacity(dst_tt.cols.len());
        for (ci, dc) in dst_tt.cols.iter().enumerate() {
            let col = match src_idxs[ci].and_then(|si| b.cols.get(si)) {
                Some(sc) => coerce_vm_column(sc, dc, b.len),
                None => {
                    let missing = coerce_cell_to_scalar(Val::Unit, &dc.ty);
                    let vals = vec![missing; b.len];
                    Column::from_vals(dc.clone(), &vals)
                }
            };
            cols.push(col);
        }
        batches.push(Batch {
            cols,
            len: b.len,
            selection: b.selection.clone(),
            group_meta: b.group_meta.clone(),
        });
    }
    VmTable {
        cols: dst_tt.cols.clone(),
        batches,
    }
}

fn make_json_response_val(idx: usize) -> Val {
    Val::Ctor {
        type_name: "__JsonResponse".to_string(),
        ctor_name: "__JsonResponse".to_string(),
        fields: vec![Val::Int(BigInt::from(idx))],
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

pub(crate) fn bigint_to_slice_bound(n: &BigInt) -> i64 {
    n.to_i64()
        .unwrap_or_else(|| if n.is_negative() { -1 } else { i64::MAX })
}

pub(crate) fn slice_text(s: &str, start: i64, len: i64) -> String {
    if len <= 0 {
        return String::new();
    }
    let start_idx = if start <= 0 {
        0usize
    } else {
        usize::try_from(start).unwrap_or(usize::MAX)
    };
    let take_len = usize::try_from(len).unwrap_or(usize::MAX);
    s.chars().skip(start_idx).take(take_len).collect()
}

pub(crate) fn try_parse_date_text(s: &str) -> Val {
    let trimmed = s.trim_matches([' ', '\t', '\n', '\r']);
    if trimmed.starts_with("0000-") {
        return Val::OptNone;
    }
    match parse_iso_date(trimmed) {
        Ok(days) => Val::OptSome(Box::new(Val::Date(BigInt::from(days)))),
        Err(_) => Val::OptNone,
    }
}

pub(crate) fn try_parse_int_text(s: &str) -> Val {
    match s.trim().parse::<i64>() {
        Ok(n) => Val::OptSome(Box::new(Val::Int(BigInt::from(n)))),
        Err(_) => Val::OptNone,
    }
}

pub(crate) fn try_parse_decimal_text(s: &str) -> Val {
    match parse_decimal_i128(s) {
        Some(d) => Val::OptSome(Box::new(Val::Decimal(BigInt::from(d)))),
        None => Val::OptNone,
    }
}

pub(crate) fn try_parse_float_text(s: &str) -> Val {
    match s.trim().parse::<f64>() {
        Ok(f) if f.is_finite() => {
            Val::OptSome(Box::new(Val::Float(Float64::from_f64(if f == 0.0 {
                0.0
            } else {
                f
            }))))
        }
        _ => Val::OptNone,
    }
}

pub(crate) fn eval_in_list(val: &Val, elems: &[Val]) -> bool {
    match val {
        Val::OptNone => false,
        Val::OptSome(inner) => elems.iter().any(|e| val_eq(inner.as_ref(), e)),
        other => elems.iter().any(|e| val_eq(other, e)),
    }
}

pub(crate) fn clamp_int_bigint(x: &BigInt, lo: &BigInt, hi: &BigInt) -> Result<BigInt, Bug> {
    if lo > hi {
        return Err(Bug {
            kind: BugKind::OutsideBoundary,
            message: format!("DomainError: clamp bounds invalid ({lo} > {hi})"),
        });
    }
    if x < lo {
        Ok(lo.clone())
    } else if x > hi {
        Ok(hi.clone())
    } else {
        Ok(x.clone())
    }
}

pub(crate) fn clamp_decimal_val(x: &BigInt, lo: &BigInt, hi: &BigInt) -> Result<BigInt, Bug> {
    if lo > hi {
        return Err(Bug {
            kind: BugKind::OutsideBoundary,
            message: format!(
                "DomainError: clamp bounds invalid ({} > {})",
                render_decimal(lo),
                render_decimal(hi)
            ),
        });
    }
    if x < lo {
        Ok(lo.clone())
    } else if x > hi {
        Ok(hi.clone())
    } else {
        Ok(x.clone())
    }
}

pub(crate) fn clamp_float_val(x: Float64, lo: Float64, hi: Float64) -> Result<Float64, Bug> {
    let xf = x.to_f64();
    let lof = lo.to_f64();
    let hif = hi.to_f64();
    if !lof.is_finite() || !hif.is_finite() || lof > hif {
        return Err(Bug {
            kind: BugKind::OutsideBoundary,
            message: format!("DomainError: clamp bounds invalid ({lof} > {hif})"),
        });
    }
    if !xf.is_finite() {
        return Err(Bug {
            kind: BugKind::OutsideBoundary,
            message: format!("DomainError: clamp input is non-finite ({xf})"),
        });
    }
    Ok(Float64::from_f64(xf.clamp(lof, hif)))
}

pub(crate) fn round_float_val(a: Float64, places: &BigInt, even: bool) -> Float64 {
    let xf = a.to_f64();
    if !xf.is_finite() || xf.abs() >= 4_503_599_627_370_496.0 {
        return a;
    }
    let p = places.to_i64().unwrap_or(0).clamp(0, 15) as i32;
    let factor = 10f64.powi(p);
    let scaled = xf * factor;
    if !scaled.is_finite() {
        return a;
    }
    let rounded = if even {
        scaled.round_ties_even()
    } else {
        scaled.round()
    };
    let r = rounded / factor;
    Float64::from_f64(if r == 0.0 { 0.0 } else { r })
}

pub(crate) fn float_to_int_checked(
    x: Float64,
    op_fn: fn(f64) -> f64,
    op_name: &str,
) -> Result<BigInt, Bug> {
    const MIN_I64_F64: f64 = -9_223_372_036_854_775_808.0;
    const EXCL_MAX_I64_F64: f64 = 9_223_372_036_854_775_808.0;
    let xf = x.to_f64();
    if !xf.is_finite() {
        return Err(Bug {
            kind: BugKind::OutsideBoundary,
            message: format!("DomainError: {op_name} input is non-finite ({xf})"),
        });
    }
    let v = op_fn(xf);
    if !(MIN_I64_F64..EXCL_MAX_I64_F64).contains(&v) {
        return Err(Bug {
            kind: BugKind::IntOverflow,
            message: format!("Int64 overflow in `{op_name}` converting {xf}"),
        });
    }
    Ok(BigInt::from(v as i64))
}

pub(crate) fn decimal_to_int_checked(d: &BigInt, kind: DecimalIntKind) -> Result<BigInt, Bug> {
    let n = decimal_to_int_bigint(d, kind);
    if !n.in_int64_range() {
        return Err(Bug {
            kind: BugKind::IntOverflow,
            message: format!("Int64 overflow converting Decimal `{}`", render_decimal(d)),
        });
    }
    Ok(n)
}

pub(crate) fn round_to_float_val(x: Float64, step: Float64) -> Result<Float64, Bug> {
    round_to_float_impl(x, step, false)
}

pub(crate) fn round_to_float_even_val(x: Float64, step: Float64) -> Result<Float64, Bug> {
    round_to_float_impl(x, step, true)
}

fn round_to_float_impl(x: Float64, step: Float64, even: bool) -> Result<Float64, Bug> {
    let xf = x.to_f64();
    let sf = step.to_f64();
    if !sf.is_finite() || sf <= 0.0 {
        return Err(Bug {
            kind: BugKind::OutsideBoundary,
            message: format!("DomainError: round_to step must be positive finite, got {sf}"),
        });
    }
    if !xf.is_finite() {
        return Err(Bug {
            kind: BugKind::OutsideBoundary,
            message: format!("DomainError: round_to input is non-finite ({xf})"),
        });
    }
    let ratio = xf / sf;
    let q = (if even {
        ratio.round_ties_even()
    } else {
        ratio.round()
    }) * sf;
    if !q.is_finite() {
        return Err(Bug {
            kind: BugKind::OutsideBoundary,
            message: "DomainError: round_to overflowed f64".to_string(),
        });
    }
    Ok(Float64::from_f64(if q == 0.0 { 0.0 } else { q }))
}

#[cfg(unix)]
fn ensure_private_dir_chain(work_dir: Option<&Path>, full_rel: &str) -> io::Result<()> {
    if let Some(base) = work_dir {
        fs::create_dir_all(base)?;
    }
    let Some(parent) = Path::new(full_rel).parent() else {
        return Ok(());
    };
    let mut cur = work_dir.map_or_else(PathBuf::new, Path::to_path_buf);
    for comp in parent.components() {
        match comp {
            Component::CurDir => continue,
            Component::RootDir | Component::Prefix(_) => {
                cur.push(comp.as_os_str());
            }
            Component::ParentDir => {
                cur.push(comp.as_os_str());
            }
            Component::Normal(seg) => {
                cur.push(seg);
                match fs::DirBuilder::new().mode(0o700).create(&cur) {
                    Ok(()) => {
                        fs::set_permissions(&cur, fs::Permissions::from_mode(0o700))?;
                    }
                    Err(e) if e.kind() == io::ErrorKind::AlreadyExists => {}
                    Err(e) => return Err(e),
                }
            }
        }
    }
    Ok(())
}

fn write_file_maybe_private(
    work_dir: Option<&Path>,
    full_rel: &str,
    private: bool,
    writer: impl FnOnce(&mut File) -> io::Result<()>,
) -> io::Result<()> {
    let out_path = match work_dir {
        Some(base) => base.join(full_rel),
        None => PathBuf::from(full_rel),
    };
    if !private {
        if let Some(parent) = out_path.parent()
            && !parent.as_os_str().is_empty()
        {
            fs::create_dir_all(parent)?;
        }
        let mut f = File::create(&out_path)?;
        writer(&mut f)?;
        f.flush()?;
        return Ok(());
    }

    #[cfg(unix)]
    ensure_private_dir_chain(work_dir, full_rel)?;
    #[cfg(not(unix))]
    if let Some(parent) = out_path.parent()
        && !parent.as_os_str().is_empty()
    {
        fs::create_dir_all(parent)?;
    }

    let parent_dir = match out_path.parent() {
        Some(p) if !p.as_os_str().is_empty() => p,
        _ => Path::new("."),
    };
    let file_name = out_path
        .file_name()
        .and_then(|s| s.to_str())
        .filter(|s| !s.is_empty())
        .unwrap_or("dana_out");
    let pid = std::process::id();
    let mut tmp_opt: Option<(PathBuf, File)> = None;
    let mut last_err: Option<io::Error> = None;
    for _ in 0..16 {
        let seq = PRIVATE_TMP_SEQ.fetch_add(1, Ordering::Relaxed);
        let candidate = parent_dir.join(format!(".{file_name}.dana-tmp.{pid}.{seq}"));
        let mut opts = OpenOptions::new();
        opts.write(true).create_new(true);
        #[cfg(unix)]
        {
            opts.mode(0o600);
        }
        match opts.open(&candidate) {
            Ok(f) => {
                tmp_opt = Some((candidate, f));
                break;
            }
            Err(e) if e.kind() == io::ErrorKind::AlreadyExists => {
                last_err = Some(e);
            }
            Err(e) => return Err(e),
        }
    }
    let Some((tmp_path, mut file)) = tmp_opt else {
        return Err(last_err.unwrap_or_else(|| {
            io::Error::new(
                io::ErrorKind::AlreadyExists,
                "failed to allocate temporary private output file",
            )
        }));
    };

    let write_res: io::Result<()> = (|| {
        writer(&mut file)?;
        file.flush()?;
        file.sync_all()?;
        Ok(())
    })();
    if let Err(e) = write_res {
        drop(file);
        let _ = fs::remove_file(&tmp_path);
        return Err(e);
    }
    drop(file);

    #[cfg(unix)]
    if let Err(e) = fs::set_permissions(&tmp_path, fs::Permissions::from_mode(0o600)) {
        let _ = fs::remove_file(&tmp_path);
        return Err(e);
    }
    if let Err(e) = fs::rename(&tmp_path, &out_path) {
        let _ = fs::remove_file(&tmp_path);
        return Err(e);
    }
    Ok(())
}

fn unwrap_opt_cell(mut v: &Val) -> Option<&Val> {
    loop {
        match v {
            Val::OptNone => return None,
            Val::OptSome(inner) => v = inner.as_ref(),
            other => return Some(other),
        }
    }
}

fn eval_suppress_small_cells_table(
    tv: TableVal,
    by_cols: &[Ident],
    min_k: &BigInt,
    distinct_by: Option<&str>,
) -> EvalOut {
    if by_cols.is_empty() {
        return EvalOut::Failed(
            "suppress_small_cells requires non-empty `by:` columns".to_string(),
        );
    }
    let mut by_indices = Vec::with_capacity(by_cols.len());
    for name in by_cols {
        let Some(idx) = tv.cols.iter().position(|c| c.name == *name) else {
            return EvalOut::Failed(format!(
                "unknown column `.{name}` in `suppress_small_cells`"
            ));
        };
        by_indices.push(idx);
    }
    let distinct_idx = match distinct_by {
        Some(dn) => {
            let Some(idx) = tv.cols.iter().position(|c| c.name == dn) else {
                return EvalOut::Failed(format!(
                    "unknown column `.{dn}` in `suppress_small_cells(distinct_by: ...)`"
                ));
            };
            Some(idx)
        }
        None => None,
    };

    let floor = min_k.to_usize_saturating();
    let out_cols: Vec<ColSpec> = tv
        .cols
        .iter()
        .map(|c| {
            let clear_ferpa = by_cols.contains(&c.name) || c.bucketed;
            ColSpec {
                name: c.name.clone(),
                ty: c.ty.clone(),
                tags: if clear_ferpa {
                    c.tags.remove("ferpa")
                } else {
                    c.tags.clone()
                },
                bucketed: c.bucketed,
                agg_kind: AggKind::Raw,
            }
        })
        .collect();

    type DistinctMap = HashMap<u64, Vec<Val>, BuildHasherDefault<FastHasher>>;
    let mut hash_buckets: HashMap<u64, Vec<usize>, BuildHasherDefault<FastHasher>> =
        HashMap::default();
    let mut exemplars: Vec<usize> = Vec::new();
    let mut group_counts: Vec<usize> = Vec::new();
    let mut group_distinct: Vec<(DistinctMap, usize)> = Vec::new();
    let mut row_groups: Vec<usize> = Vec::with_capacity(tv.rows.len());

    for (r_idx, row) in tv.rows.iter().enumerate() {
        let mut h = FastHasher::new();
        for &ci in &by_indices {
            hash_val(&row.cells[ci], &mut h);
        }
        let hv = h.finish_u64();
        let candidates = hash_buckets.entry(hv).or_default();
        let found_gid = candidates.iter().copied().find(|&gid| {
            let ex_row = &tv.rows[exemplars[gid]];
            by_indices
                .iter()
                .all(|&ci| val_eq(&ex_row.cells[ci], &row.cells[ci]))
        });
        let gid = if let Some(gid) = found_gid {
            gid
        } else {
            let gid = exemplars.len();
            exemplars.push(r_idx);
            candidates.push(gid);
            group_counts.push(0);
            if distinct_idx.is_some() {
                group_distinct.push((DistinctMap::default(), 0));
            }
            gid
        };
        if let Some(d_idx) = distinct_idx {
            if let Some(inner) = unwrap_opt_cell(&row.cells[d_idx]) {
                let mut dh = FastHasher::new();
                hash_val(inner, &mut dh);
                let dhv = dh.finish_u64();
                let (map, total) = &mut group_distinct[gid];
                let bucket = map.entry(dhv).or_default();
                if !bucket.iter().any(|existing| val_eq(existing, inner)) {
                    bucket.push(inner.clone());
                    *total += 1;
                }
            }
        } else {
            group_counts[gid] += 1;
        }
        row_groups.push(gid);
    }

    let mut kept_rows = Vec::new();
    for (r_idx, mut row) in tv.rows.into_iter().enumerate() {
        let Some(&gid) = row_groups.get(r_idx) else {
            continue;
        };
        let sz = if distinct_idx.is_some() {
            group_distinct[gid].1
        } else {
            group_counts[gid]
        };
        if sz >= floor {
            row.group_meta = None;
            kept_rows.push(row);
        }
    }

    EvalOut::Ok(Val::Table(TableVal {
        cols: out_cols,
        rows: kept_rows,
    }))
}

// Keep reference constants visible for checked range consistency.
const _: (i64, i64, i128, i128) = (INT64_MIN, INT64_MAX, DEC_MIN, DEC_MAX);
const _: fn(&[Val]) -> u64 = hash_val_slice;
