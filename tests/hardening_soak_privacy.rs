#![forbid(unsafe_code)]

//! Phase 5A — Extended Differential Soak & Adversarial Privacy Red-Team Audit.
//!
//! 1. **Extended Differential Soak** (configurable via `DANA_SOAK_CASES`, default `2_000`,
//!    scalable to `20_000`): generates randomized multi-stage `ExecProgram` pipelines covering
//!    `where`, `derive` (with bytecode-inlined pure UDFs & `bucket`), explicit-cardinality joins
//!    (`join_one`, `join_many_to_one`, `left_join_one`, `semi_join`, `anti_join`),
//!    `group_by`/`summarize`, `window`, `fill_gaps`, `pivot_wider`, `pivot_longer`,
//!    `suppress_small_groups` (`:drop` & `:mask`), `redact`, `pseudonymize` (HMAC-SHA256 & FNV-1a),
//!    `sort_by`, `limit`, and live SQLite SQL pushdown hybrid subsets, asserting 100% cell-for-cell
//!    parity across `Oracle == VM(seq_unopt) == VM(seq_opt) == VM(par_opt)` and SQLite pushdown.
//! 2. **Adversarial Privacy & Security Red-Team Audit (35+ explicit probes)**: verifies every
//!    implicit control-flow, relational, statistical, diagnostic, quarantine, profiler, dry-run,
//!    REPL, chart/report XSS, `dana.policy` ceiling, `vendor/` hash-pinning/purity, SQL injection,
//!    HTTPS host/scheme/redirect, and `--allow-export` boundary either fails statically (`E0202`/
//!    `E0203`/`E0100`/`E0101`) or strictly redacts at runtime.

use std::collections::HashMap;
use std::fs;
use std::io::Cursor;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};

use dana::base::{DiagCode, FileId, SourceMap, render_diagnostic};
use dana::check::{
    check_module, check_resolved, parse_policy, pin_vendor_dir, resolve_path, verify_vendor_dir,
};
use dana::core::{
    AggKind, AggOp, BigInt, BugKind, ChartKind, ColSpec, DEC_SCALE, Float64, FunKind, JoinKind,
    JoinOn, LTy, Literal, Policy, PrimOp, RowLit, ScalarTy, SortDir, SuppressMode, TableTy, TagSet,
    Ty, WindowFn, WindowItem,
};
use dana::db::schema_lock::{LockedCol, LockedDb, LockedTable, SchemaLockFile};
use dana::db::{SqlDialect, SqlParam, open_connection};
use dana::formats::csv::parse_csv_with_schema;
use dana::formats::json::parse_jsonl_with_schema;
use dana::formats::time::{MICROS_PER_DAY, MICROS_PER_HOUR};
use dana::formats::xlsx::{read_xlsx_bytes_with_schema, write_xlsx_sheets};
use dana::lower::lower_program;
use dana::net::{HttpsConfig, ParsedHttpsUrl, parse_http_response_from_reader};
use dana::oracle::value::{ChartVal, ReportVal, TableRow, TableVal, Val, val_eq};
use dana::plan::{SplitPlan, split_exec_plan_pushdown};
use dana::repl::{ReplConfig, ReplOutput, ReplSession};
use dana::runtime::ir::{
    ExecAggItem, ExecDeriveItem, ExecExpr, ExecFun, ExecPlan, ExecPrimOp, ExecProgram, ExecRowExpr,
    PseudonymizeMode,
};
use dana::runtime::{
    EvalProgramResult, RunConfig, RunResult, eval_exec_entry, run_exec_program, run_program_tests,
};
use dana::stats::profile::{profile_table, render_profile_terminal};
use dana::syntax::parse_module;
use dana::viz::report::{render_html_report, render_markdown_report};
use dana::viz::svg::render_chart_svg;
use dana::vm::{VmConfig, eval_exec_entry_vm, run_exec_program_vm, run_program_tests_vm};

type TestResult<T = ()> = Result<T, Box<dyn std::error::Error>>;

const DEFAULT_SOAK_CASES: usize = 2_000;
const BASE_SOAK_SEED: u64 = 0xDA4A_5A02_2026_0505;

static TMP_SEQ: AtomicU64 = AtomicU64::new(1);

struct TempDir {
    path: PathBuf,
}

impl TempDir {
    fn new(prefix: &str) -> TestResult<Self> {
        let n = TMP_SEQ.fetch_add(1, Ordering::Relaxed);
        let path =
            std::env::temp_dir().join(format!("dana_soak_{prefix}_{}_{}", std::process::id(), n));
        if path.exists() {
            fs::remove_dir_all(&path)?;
        }
        fs::create_dir_all(&path)?;
        Ok(Self { path })
    }

    fn path(&self) -> &Path {
        &self.path
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}

fn dana_bin() -> &'static str {
    env!("CARGO_BIN_EXE_dana")
}

fn soak_cases() -> usize {
    std::env::var("DANA_SOAK_CASES")
        .ok()
        .and_then(|s| s.trim().replace('_', "").parse::<usize>().ok())
        .filter(|&n| n > 0)
        .unwrap_or(DEFAULT_SOAK_CASES)
}

fn soak_seed() -> u64 {
    std::env::var("DANA_SOAK_SEED")
        .ok()
        .and_then(|s| s.trim().parse::<u64>().ok())
        .unwrap_or(BASE_SOAK_SEED)
}

// ===========================================================================
// Deterministic Seeded Xoshiro256++ PRNG
// ===========================================================================

#[derive(Clone, Debug)]
struct Xoshiro256Pp {
    s: [u64; 4],
}

impl Xoshiro256Pp {
    fn from_seed(mut seed: u64) -> Self {
        let mut next_sm64 = || -> u64 {
            seed = seed.wrapping_add(0x9E37_79B9_7F4A_7C15);
            let mut z = seed;
            z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
            z ^ (z >> 31)
        };
        Self {
            s: [next_sm64(), next_sm64(), next_sm64(), next_sm64()],
        }
    }

    fn next_u64(&mut self) -> u64 {
        let result = self.s[0]
            .wrapping_add(self.s[3])
            .rotate_left(23)
            .wrapping_add(self.s[0]);
        let t = self.s[1] << 17;
        self.s[2] ^= self.s[0];
        self.s[3] ^= self.s[1];
        self.s[1] ^= self.s[2];
        self.s[0] ^= self.s[3];
        self.s[2] ^= t;
        self.s[3] = self.s[3].rotate_left(45);
        result
    }

    fn gen_usize(&mut self, bound: usize) -> usize {
        if bound <= 1 {
            0
        } else {
            (self.next_u64() as usize) % bound
        }
    }

    fn gen_bool(&mut self, num: usize, den: usize) -> bool {
        self.gen_usize(den) < num
    }

    fn pick_int(&mut self) -> i64 {
        const POOL: &[i64] = &[-25, -7, -1, 0, 1, 2, 3, 5, 10, 15, 20, 42, 100];
        POOL[self.gen_usize(POOL.len())]
    }

    fn pick_dec_scaled(&mut self) -> i128 {
        const POOL: &[i128] = &[
            -10 * DEC_SCALE,
            -DEC_SCALE / 2,
            0,
            DEC_SCALE / 4,
            DEC_SCALE,
            3 * DEC_SCALE + DEC_SCALE / 2,
            25 * DEC_SCALE,
        ];
        POOL[self.gen_usize(POOL.len())]
    }

    fn pick_group(&mut self) -> String {
        const POOL: &[&str] = &["A", "B", "C", "D"];
        POOL[self.gen_usize(POOL.len())].to_string()
    }

    fn pick_dir(&mut self) -> SortDir {
        if self.gen_bool(1, 2) {
            SortDir::Asc
        } else {
            SortDir::Desc
        }
    }
}

// ===========================================================================
// Shared Helpers & Cell-for-Cell Parity Comparator
// ===========================================================================

fn col(name: &str, ty: ScalarTy, tags: &[&str]) -> ColSpec {
    ColSpec {
        name: name.to_string(),
        ty,
        tags: TagSet::of_list(tags.iter().map(|s| (*s).to_string()).collect()),
        bucketed: false,
        agg_kind: AggKind::Raw,
    }
}

fn opt(ty: ScalarTy) -> ScalarTy {
    ScalarTy::Option(Box::new(ty))
}

fn table_ty(cols: Vec<ColSpec>) -> TableTy {
    TableTy {
        cols,
        ..TableTy::default()
    }
}

fn table_lit_plan(schema: TableTy, rows: Vec<RowLit>) -> ExecPlan {
    ExecPlan::SourceExpr(Box::new(ExecExpr::TableLit { schema, rows }))
}

fn make_plan_prog(
    params: Vec<(String, LTy)>,
    extra_funs: Vec<ExecFun>,
    plan: ExecPlan,
) -> ExecProgram {
    let mut funs = extra_funs;
    funs.push(ExecFun {
        name: "soak_entry".to_string(),
        kind: FunKind::Function,
        is_pure: false,
        params,
        pc: TagSet::empty(),
        ret: LTy::public(Ty::Table(TableTy::default())),
        body: ExecExpr::Rel(Box::new(plan)),
    });
    ExecProgram {
        funs,
        entry: Some("soak_entry".to_string()),
        ..ExecProgram::default()
    }
}

fn assert_tables_cell_for_cell(
    actual: &TableVal,
    expected: &TableVal,
    label: &str,
) -> Result<(), String> {
    if actual.cols.len() != expected.cols.len() {
        return Err(format!(
            "{label}: col count mismatch: actual={} expected={}",
            actual.cols.len(),
            expected.cols.len()
        ));
    }
    for (ci, (ac, ec)) in actual.cols.iter().zip(&expected.cols).enumerate() {
        if ac.name != ec.name {
            return Err(format!(
                "{label}: col {ci} name mismatch: actual=`{}` expected=`{}`",
                ac.name, ec.name
            ));
        }
        if ac.ty != ec.ty {
            return Err(format!(
                "{label}: col {ci} (`{}`) type mismatch: actual={:?} expected={:?}",
                ac.name, ac.ty, ec.ty
            ));
        }
    }
    if actual.rows.len() != expected.rows.len() {
        return Err(format!(
            "{label}: row count mismatch: actual={} expected={}",
            actual.rows.len(),
            expected.rows.len()
        ));
    }
    for (ri, (ar, er)) in actual.rows.iter().zip(&expected.rows).enumerate() {
        if ar.cells.len() != er.cells.len() {
            return Err(format!(
                "{label}: row {ri} cell count mismatch: actual={} expected={}",
                ar.cells.len(),
                er.cells.len()
            ));
        }
        for (ci, (av, ev)) in ar.cells.iter().zip(&er.cells).enumerate() {
            if !val_eq(av, ev) {
                return Err(format!(
                    "{label}: row {ri} col {ci} (`{}`) cell mismatch: actual={av:?} expected={ev:?}",
                    expected.cols[ci].name
                ));
            }
        }
    }
    Ok(())
}

fn assert_all_engines_match(
    prog: &ExecProgram,
    run_cfg: &RunConfig,
    case_label: &str,
) -> Result<usize, String> {
    let vm_seq_unopt = VmConfig {
        batch_size: 4,
        parallel_threshold_rows: usize::MAX,
        max_threads: Some(1),
        optimize: false,
        pseudonymize_mode: run_cfg.pseudonymize_mode,
    };
    let vm_seq_opt = VmConfig {
        batch_size: 4,
        parallel_threshold_rows: usize::MAX,
        max_threads: Some(1),
        optimize: true,
        pseudonymize_mode: run_cfg.pseudonymize_mode,
    };
    let vm_par_opt = VmConfig {
        batch_size: 4,
        parallel_threshold_rows: 4,
        max_threads: Some(4),
        optimize: true,
        pseudonymize_mode: run_cfg.pseudonymize_mode,
    };

    let oracle = eval_exec_entry(prog, "soak_entry", &[], run_cfg);
    let seq_u = eval_exec_entry_vm(prog, "soak_entry", &[], run_cfg, &vm_seq_unopt);
    let seq_o = eval_exec_entry_vm(prog, "soak_entry", &[], run_cfg, &vm_seq_opt);
    let par_o = eval_exec_entry_vm(prog, "soak_entry", &[], run_cfg, &vm_par_opt);

    let variants: [(&str, EvalProgramResult); 3] = [
        ("vm_seq_unopt", seq_u),
        ("vm_seq_opt", seq_o),
        ("vm_par_opt", par_o),
    ];

    match oracle {
        EvalProgramResult::Ok { val: o_val, .. } => {
            let Val::Table(o_tbl) = o_val.as_ref() else {
                return Err(format!("{case_label}: oracle returned non-Table {o_val:?}"));
            };
            for (vname, vres) in variants {
                match vres {
                    EvalProgramResult::Ok { val: v_val, .. } => {
                        let Some(v_tbl) = v_val.to_table_val() else {
                            return Err(format!(
                                "{case_label}/{vname}: returned non-Table {v_val:?}"
                            ));
                        };
                        assert_tables_cell_for_cell(
                            &v_tbl,
                            o_tbl,
                            &format!("{case_label} ({vname} vs oracle)"),
                        )?;
                    }
                    other => {
                        return Err(format!(
                            "{case_label}/{vname}: diverged from oracle Ok: {other:?}"
                        ));
                    }
                }
            }
            Ok(o_tbl.rows.len())
        }
        EvalProgramResult::Stopped { bug: o_bug, .. } => {
            for (vname, vres) in variants {
                match vres {
                    EvalProgramResult::Stopped { bug: v_bug, .. } => {
                        if v_bug.kind != o_bug.kind {
                            return Err(format!(
                                "{case_label}/{vname}: bug kind mismatch: {:?} vs oracle {:?}",
                                v_bug.kind, o_bug.kind
                            ));
                        }
                    }
                    other => {
                        return Err(format!(
                            "{case_label}/{vname}: expected Stopped({:?}), got {other:?}",
                            o_bug.kind
                        ));
                    }
                }
            }
            Ok(0)
        }
        EvalProgramResult::Failed { message, .. } => {
            Err(format!("{case_label}: unexpected oracle Failed: {message}"))
        }
    }
}

// ===========================================================================
// 1. Extended Differential Soak (Default 2,000 cases, scalable to 20,000+)
// ===========================================================================

#[test]
fn soak_extended_differential_exec_and_sqlite_pushdown() -> TestResult {
    let total_cases = soak_cases();
    let mut rng = Xoshiro256Pp::from_seed(soak_seed());
    let tmp = TempDir::new("diff_sqlite")?;
    let db_path = tmp.path().join("soak.db");
    let db_uri = format!("sqlite://{}", db_path.display());

    // Prepare reusable SQLite tables for DB-backed pushdown soak cases.
    {
        let mut conn = open_connection(&db_uri)?;
        conn.execute(
            r#"CREATE TABLE "orders" (
                "id" INTEGER PRIMARY KEY NOT NULL,
                "grp" TEXT NOT NULL,
                "val" INTEGER NOT NULL,
                "amt" TEXT NOT NULL,
                "flag" INTEGER NOT NULL
            )"#,
            &[],
        )?;
        conn.execute(
            r#"CREATE TABLE "dims" (
                "grp" TEXT PRIMARY KEY NOT NULL,
                "weight" INTEGER NOT NULL,
                "label" TEXT NOT NULL
            )"#,
            &[],
        )?;
    }

    let lock = SchemaLockFile {
        version: 1,
        dbs: vec![LockedDb {
            name: "SoakDb".to_string(),
            dialect: SqlDialect::Sqlite,
            tables: vec![
                LockedTable {
                    name: "orders".to_string(),
                    cols: vec![
                        LockedCol {
                            name: "id".to_string(),
                            ty: ScalarTy::Int,
                            nullable: false,
                            pk: true,
                            tags: TagSet::empty(),
                        },
                        LockedCol {
                            name: "grp".to_string(),
                            ty: ScalarTy::Text,
                            nullable: false,
                            pk: false,
                            tags: TagSet::empty(),
                        },
                        LockedCol {
                            name: "val".to_string(),
                            ty: ScalarTy::Int,
                            nullable: false,
                            pk: false,
                            tags: TagSet::empty(),
                        },
                        LockedCol {
                            name: "amt".to_string(),
                            ty: ScalarTy::Decimal,
                            nullable: false,
                            pk: false,
                            tags: TagSet::empty(),
                        },
                        LockedCol {
                            name: "flag".to_string(),
                            ty: ScalarTy::Bool,
                            nullable: false,
                            pk: false,
                            tags: TagSet::empty(),
                        },
                    ],
                },
                LockedTable {
                    name: "dims".to_string(),
                    cols: vec![
                        LockedCol {
                            name: "grp".to_string(),
                            ty: ScalarTy::Text,
                            nullable: false,
                            pk: true,
                            tags: TagSet::empty(),
                        },
                        LockedCol {
                            name: "weight".to_string(),
                            ty: ScalarTy::Int,
                            nullable: false,
                            pk: false,
                            tags: TagSet::empty(),
                        },
                        LockedCol {
                            name: "label".to_string(),
                            ty: ScalarTy::Text,
                            nullable: false,
                            pk: false,
                            tags: TagSet::empty(),
                        },
                    ],
                },
            ],
        }],
    };

    // Pure UDF helper used in Derive soak cases (`bonus_score(x, mult) = if x > 0 then x * mult + 3 else 0 - x`)
    let pure_udf = ExecFun {
        name: "bonus_score".to_string(),
        kind: FunKind::Function,
        is_pure: true,
        params: vec![
            ("x".to_string(), LTy::public(Ty::Int)),
            ("m".to_string(), LTy::public(Ty::Int)),
        ],
        pc: TagSet::empty(),
        ret: LTy::public(Ty::Int),
        body: ExecExpr::IfE {
            cond: Box::new(ExecExpr::Prim {
                op: ExecPrimOp::Core(PrimOp::Gt),
                args: vec![
                    ExecExpr::Var("x".to_string()),
                    ExecExpr::Lit(Literal::int(0)),
                ],
            }),
            then_br: Box::new(ExecExpr::Prim {
                op: ExecPrimOp::Core(PrimOp::AddInt),
                args: vec![
                    ExecExpr::Prim {
                        op: ExecPrimOp::Core(PrimOp::MulInt),
                        args: vec![
                            ExecExpr::Var("x".to_string()),
                            ExecExpr::Var("m".to_string()),
                        ],
                    },
                    ExecExpr::Lit(Literal::int(3)),
                ],
            }),
            else_br: Box::new(ExecExpr::Prim {
                op: ExecPrimOp::Core(PrimOp::SubInt),
                args: vec![
                    ExecExpr::Lit(Literal::int(0)),
                    ExecExpr::Var("x".to_string()),
                ],
            }),
        },
    };

    let mut total_rows_verified = 0usize;
    let mut db_pushed_cases = 0usize;
    let mut family_counts = [0usize; 8];

    for case_idx in 0..total_cases {
        let family = case_idx % 8;
        family_counts[family] += 1;

        match family {
            // Family 0: where + derive (pure UDF + bucket) + sort_by + limit
            0 => {
                let schema = table_ty(vec![
                    col("id", ScalarTy::Int, &[]),
                    col("grp", ScalarTy::Text, &[]),
                    col("val", ScalarTy::Int, &[]),
                    col("mult", ScalarTy::Int, &[]),
                    col("has_opt", ScalarTy::Bool, &[]),
                ]);
                let nrows = rng.gen_usize(24);
                let mut rows = Vec::with_capacity(nrows);
                for r in 0..nrows {
                    rows.push(RowLit {
                        cells: vec![
                            Literal::int(r as i64 + 1),
                            Literal::Text(rng.pick_group()),
                            Literal::int(rng.pick_int()),
                            Literal::int((rng.gen_usize(5) as i64) - 1),
                            Literal::Bool(rng.gen_bool(2, 3)),
                        ],
                    });
                }
                let with_opt = ExecPlan::Derive {
                    input: Box::new(table_lit_plan(schema, rows)),
                    items: vec![ExecDeriveItem::ColExpr {
                        name: "opt_n".to_string(),
                        expr: Box::new(ExecRowExpr::IfE {
                            cond: Box::new(ExecRowExpr::Col("has_opt".into())),
                            then_br: Box::new(ExecRowExpr::Prim {
                                op: ExecPrimOp::Core(PrimOp::SomeVal(Ty::Int)),
                                args: vec![ExecRowExpr::Col("val".into())],
                            }),
                            else_br: Box::new(ExecRowExpr::Lit(Literal::NoneLit(Ty::Int))),
                        }),
                    }],
                };
                let thresh = rng.pick_int();
                let lim = rng.gen_usize(15) as u64;
                let plan = ExecPlan::Limit {
                    input: Box::new(ExecPlan::Sort {
                        input: Box::new(ExecPlan::Derive {
                            input: Box::new(ExecPlan::Filter {
                                input: Box::new(with_opt),
                                pred: ExecRowExpr::Prim {
                                    op: ExecPrimOp::Core(PrimOp::Ge),
                                    args: vec![
                                        ExecRowExpr::Coalesce {
                                            opt_expr: Box::new(ExecRowExpr::Col("opt_n".into())),
                                            default_expr: Box::new(ExecRowExpr::Col("val".into())),
                                        },
                                        ExecRowExpr::Lit(Literal::int(thresh)),
                                    ],
                                },
                            }),
                            items: vec![
                                ExecDeriveItem::ColExpr {
                                    name: "score".to_string(),
                                    expr: Box::new(ExecRowExpr::CallPure {
                                        fn_name: "bonus_score".to_string(),
                                        args: vec![
                                            ExecRowExpr::Col("val".to_string()),
                                            ExecRowExpr::Col("mult".to_string()),
                                        ],
                                    }),
                                },
                                ExecDeriveItem::BucketCol {
                                    name: "band".to_string(),
                                    source: "val".to_string(),
                                    cuts: vec![Literal::int(0), Literal::int(10)],
                                    labels: vec![
                                        "neg".to_string(),
                                        "mid".to_string(),
                                        "high".to_string(),
                                    ],
                                },
                            ],
                        }),
                        keys: vec![
                            ("score".to_string(), rng.pick_dir()),
                            ("id".to_string(), SortDir::Asc),
                        ],
                    }),
                    n: BigInt::from(lim),
                };
                let prog = make_plan_prog(Vec::new(), vec![pure_udf.clone()], plan);
                total_rows_verified += assert_all_engines_match(
                    &prog,
                    &RunConfig::default(),
                    &format!("f0#{case_idx}"),
                )?;
            }

            // Family 1: Explicit-cardinality joins (join_one, join_many_to_one, left_join_one, semi_join, anti_join)
            1 => {
                let kinds = [
                    JoinKind::InnerOne,
                    JoinKind::InnerManyToOne,
                    JoinKind::LeftOne,
                    JoinKind::Semi,
                    JoinKind::Anti,
                ];
                let kind = kinds[rng.gen_usize(kinds.len())];
                let inject_dup = matches!(
                    kind,
                    JoinKind::InnerOne | JoinKind::InnerManyToOne | JoinKind::LeftOne
                ) && rng.gen_bool(1, 5);

                let left_schema = table_ty(vec![
                    col("k", ScalarTy::Int, &["pii"]),
                    col("lv", ScalarTy::Int, &[]),
                ]);
                let right_schema = table_ty(vec![
                    col("k", ScalarTy::Int, &["pii"]),
                    col("rv", ScalarTy::Text, &[]),
                ]);

                let ln = 1 + rng.gen_usize(14);
                let mut lrows = Vec::with_capacity(ln);
                for i in 0..ln {
                    let k = if matches!(kind, JoinKind::InnerOne | JoinKind::LeftOne) && !inject_dup
                    {
                        i as i64 + 1
                    } else {
                        (rng.gen_usize(6) as i64) + 1
                    };
                    lrows.push(RowLit {
                        cells: vec![Literal::int(k), Literal::int(rng.pick_int())],
                    });
                }

                let rn = 2 + rng.gen_usize(8);
                let mut rrows = Vec::with_capacity(rn);
                for i in 0..rn {
                    let k = if inject_dup && i == 1 {
                        1i64
                    } else if matches!(kind, JoinKind::Semi | JoinKind::Anti) {
                        (rng.gen_usize(6) as i64) + 1
                    } else {
                        i as i64 + 1
                    };
                    rrows.push(RowLit {
                        cells: vec![Literal::int(k), Literal::Text(rng.pick_group())],
                    });
                }

                let joined = ExecPlan::Join {
                    kind,
                    left: Box::new(table_lit_plan(left_schema, lrows)),
                    right: Box::new(table_lit_plan(right_schema, rrows)),
                    on: JoinOn::SameKeys(vec!["k".to_string()]),
                    suffixes: None,
                };
                let plan = ExecPlan::Sort {
                    input: Box::new(joined),
                    keys: vec![
                        ("k".to_string(), SortDir::Asc),
                        ("lv".to_string(), SortDir::Asc),
                    ],
                };
                let prog = make_plan_prog(Vec::new(), Vec::new(), plan);
                total_rows_verified += assert_all_engines_match(
                    &prog,
                    &RunConfig::default(),
                    &format!("f1_{kind:?}#{case_idx}"),
                )?;
            }

            // Family 2: group_by + summarize + suppress_small_groups (:drop & :mask) + sort_by + limit
            2 => {
                let schema = table_ty(vec![
                    col("grp", ScalarTy::Text, &[]),
                    col("uid", ScalarTy::Int, &["pii"]),
                    col("amt", ScalarTy::Decimal, &[]),
                    col("score", ScalarTy::Int, &[]),
                ]);
                let nrows = 8 + rng.gen_usize(24);
                let mut rows = Vec::with_capacity(nrows);
                for i in 0..nrows {
                    // Bias group "A" so at least some runs survive k >= 5 suppression.
                    let grp = if i < 7 && rng.gen_bool(3, 4) {
                        "A".to_string()
                    } else {
                        rng.pick_group()
                    };
                    rows.push(RowLit {
                        cells: vec![
                            Literal::Text(grp),
                            Literal::int((i as i64) % 10 + 1),
                            Literal::decimal(rng.pick_dec_scaled()),
                            Literal::int(rng.pick_int()),
                        ],
                    });
                }
                let use_distinct = rng.gen_bool(1, 2);
                let mode = if rng.gen_bool(1, 2) {
                    SuppressMode::Drop
                } else {
                    SuppressMode::MaskComplementary
                };
                let aggs = vec![
                    ExecAggItem {
                        name: "n".to_string(),
                        op: if use_distinct {
                            AggOp::CountDistinct
                        } else {
                            AggOp::Count
                        },
                        arg: if use_distinct {
                            Some(ExecRowExpr::Col("uid".to_string()))
                        } else {
                            None
                        },
                    },
                    ExecAggItem {
                        name: "total_amt".to_string(),
                        op: AggOp::Sum,
                        arg: Some(ExecRowExpr::Col("amt".to_string())),
                    },
                    ExecAggItem {
                        name: "avg_score".to_string(),
                        op: AggOp::Mean,
                        arg: Some(ExecRowExpr::Col("score".to_string())),
                    },
                    ExecAggItem {
                        name: "med_score".to_string(),
                        op: AggOp::Median,
                        arg: Some(ExecRowExpr::Col("score".to_string())),
                    },
                ];
                let plan = ExecPlan::Limit {
                    input: Box::new(ExecPlan::Sort {
                        input: Box::new(ExecPlan::SuppressSmallGroups {
                            input: Box::new(ExecPlan::Summarize {
                                input: Box::new(ExecPlan::GroupBy {
                                    input: Box::new(table_lit_plan(schema, rows)),
                                    keys: vec!["grp".to_string()],
                                }),
                                aggs,
                                distinct_key: if use_distinct {
                                    Some("uid".to_string())
                                } else {
                                    None
                                },
                            }),
                            min_k: BigInt::from(5u64),
                            distinct_by: if use_distinct {
                                Some("uid".to_string())
                            } else {
                                None
                            },
                            mode,
                        }),
                        keys: vec![("grp".to_string(), SortDir::Asc)],
                    }),
                    n: BigInt::from(10u64),
                };
                let prog = make_plan_prog(Vec::new(), Vec::new(), plan);
                total_rows_verified += assert_all_engines_match(
                    &prog,
                    &RunConfig::default(),
                    &format!("f2_{mode:?}#{case_idx}"),
                )?;
            }

            // Family 3: Window functions (RowNumber, Rank, Lag, Lead, RunningSum, RollingMean)
            3 => {
                let schema = table_ty(vec![
                    col("grp", ScalarTy::Text, &[]),
                    col("seq", ScalarTy::Int, &[]),
                    col("val", ScalarTy::Int, &[]),
                ]);
                let nrows = rng.gen_usize(22);
                let mut rows = Vec::with_capacity(nrows);
                for i in 0..nrows {
                    rows.push(RowLit {
                        cells: vec![
                            Literal::Text(rng.pick_group()),
                            Literal::int((i as i64) * 2 + (rng.gen_usize(2) as i64)),
                            Literal::int(rng.pick_int()),
                        ],
                    });
                }
                let plan = ExecPlan::Limit {
                    input: Box::new(ExecPlan::Sort {
                        input: Box::new(ExecPlan::Window {
                            input: Box::new(table_lit_plan(schema, rows)),
                            items: vec![
                                WindowItem {
                                    name: "rn".to_string(),
                                    win_fn: WindowFn::RowNumber,
                                    over: vec!["grp".to_string()],
                                    order: vec![("seq".to_string(), SortDir::Asc)],
                                },
                                WindowItem {
                                    name: "rk".to_string(),
                                    win_fn: WindowFn::Rank {
                                        col: "val".to_string(),
                                    },
                                    over: vec!["grp".to_string()],
                                    order: vec![("seq".to_string(), SortDir::Asc)],
                                },
                                WindowItem {
                                    name: "prev".to_string(),
                                    win_fn: WindowFn::Lag {
                                        col: "val".to_string(),
                                        offset: BigInt::from(1u64),
                                    },
                                    over: vec!["grp".to_string()],
                                    order: vec![("seq".to_string(), SortDir::Asc)],
                                },
                                WindowItem {
                                    name: "next_v".to_string(),
                                    win_fn: WindowFn::Lead {
                                        col: "val".to_string(),
                                        offset: BigInt::from(1u64),
                                    },
                                    over: vec!["grp".to_string()],
                                    order: vec![("seq".to_string(), SortDir::Asc)],
                                },
                                WindowItem {
                                    name: "rsum".to_string(),
                                    win_fn: WindowFn::RunningSum {
                                        col: "val".to_string(),
                                    },
                                    over: vec!["grp".to_string()],
                                    order: vec![("seq".to_string(), SortDir::Asc)],
                                },
                                WindowItem {
                                    name: "rmean".to_string(),
                                    win_fn: WindowFn::RollingMean {
                                        col: "val".to_string(),
                                        window_size: BigInt::from(3u64),
                                    },
                                    over: vec!["grp".to_string()],
                                    order: vec![("seq".to_string(), SortDir::Asc)],
                                },
                            ],
                        }),
                        keys: vec![
                            ("grp".to_string(), SortDir::Asc),
                            ("seq".to_string(), SortDir::Asc),
                            ("rn".to_string(), SortDir::Asc),
                        ],
                    }),
                    n: BigInt::from(16u64),
                };
                let prog = make_plan_prog(Vec::new(), Vec::new(), plan);
                total_rows_verified += assert_all_engines_match(
                    &prog,
                    &RunConfig::default(),
                    &format!("f3#{case_idx}"),
                )?;
            }

            // Family 4: fill_gaps + window + sort_by
            4 => {
                let use_date = rng.gen_bool(1, 2);
                let step = if use_date {
                    MICROS_PER_DAY
                } else {
                    MICROS_PER_HOUR
                };
                let schema = table_ty(vec![
                    col("grp", ScalarTy::Text, &[]),
                    col(
                        "t",
                        if use_date {
                            ScalarTy::Date
                        } else {
                            ScalarTy::Timestamp
                        },
                        &[],
                    ),
                    col("v", ScalarTy::Int, &[]),
                ]);
                let base_day = 20_000i64;
                let base_ts = 1_700_000_000_000_000i64;
                let mut rows = Vec::new();
                for grp in ["A", "B"] {
                    let mut cur = 0i64;
                    let pts = 1 + rng.gen_usize(5);
                    for _ in 0..pts {
                        cur += 1 + (rng.gen_usize(3) as i64);
                        let t_lit = if use_date {
                            Literal::date(base_day + cur)
                        } else {
                            Literal::timestamp(base_ts + cur * MICROS_PER_HOUR)
                        };
                        rows.push(RowLit {
                            cells: vec![
                                Literal::Text(grp.to_string()),
                                t_lit,
                                Literal::int(rng.pick_int()),
                            ],
                        });
                    }
                }
                let plan = ExecPlan::Sort {
                    input: Box::new(ExecPlan::Window {
                        input: Box::new(ExecPlan::FillGaps {
                            input: Box::new(table_lit_plan(schema, rows)),
                            col: "t".to_string(),
                            step_micros: BigInt::from(step),
                            over: vec!["grp".to_string()],
                            fill: vec![("v".to_string(), Literal::int(0))],
                        }),
                        items: vec![WindowItem {
                            name: "cum_v".to_string(),
                            win_fn: WindowFn::RunningSum {
                                col: "v".to_string(),
                            },
                            over: vec!["grp".to_string()],
                            order: vec![("t".to_string(), SortDir::Asc)],
                        }],
                    }),
                    keys: vec![
                        ("grp".to_string(), SortDir::Asc),
                        ("t".to_string(), SortDir::Asc),
                    ],
                };
                let prog = make_plan_prog(Vec::new(), Vec::new(), plan);
                total_rows_verified += assert_all_engines_match(
                    &prog,
                    &RunConfig::default(),
                    &format!("f4#{case_idx}"),
                )?;
            }

            // Family 5: pivot_wider -> derive -> pivot_longer -> filter -> sort_by -> limit
            5 => {
                let schema = table_ty(vec![
                    col("grp", ScalarTy::Text, &[]),
                    col("metric", ScalarTy::Text, &[]),
                    col("val", ScalarTy::Int, &[]),
                ]);
                let metrics = ["m1", "m2", "m3"];
                let mut rows = Vec::new();
                for grp in ["A", "B", "C"] {
                    for &m in &metrics {
                        if rng.gen_bool(2, 3) {
                            rows.push(RowLit {
                                cells: vec![
                                    Literal::Text(grp.to_string()),
                                    Literal::Text(m.to_string()),
                                    Literal::int(rng.pick_int()),
                                ],
                            });
                        }
                    }
                }
                let widened = ExecPlan::PivotWider {
                    input: Box::new(table_lit_plan(schema, rows)),
                    names_from: "metric".to_string(),
                    values_from: "val".to_string(),
                    static_cols: vec!["m1".to_string(), "m2".to_string(), "m3".to_string()],
                    fill: Literal::int(0),
                };
                let derived = ExecPlan::Derive {
                    input: Box::new(widened),
                    items: vec![ExecDeriveItem::ColExpr {
                        name: "sum_m".to_string(),
                        expr: Box::new(ExecRowExpr::Prim {
                            op: ExecPrimOp::Core(PrimOp::AddInt),
                            args: vec![
                                ExecRowExpr::Col("m1".to_string()),
                                ExecRowExpr::Col("m2".to_string()),
                            ],
                        }),
                    }],
                };
                let melted = ExecPlan::PivotLonger {
                    input: Box::new(derived),
                    cols: vec!["m1".to_string(), "m2".to_string(), "m3".to_string()],
                    names_to: "k".to_string(),
                    values_to: "v".to_string(),
                    value_ty: ScalarTy::Int,
                    value_tags: TagSet::empty(),
                };
                let plan = ExecPlan::Limit {
                    input: Box::new(ExecPlan::Sort {
                        input: Box::new(ExecPlan::Filter {
                            input: Box::new(melted),
                            pred: ExecRowExpr::Prim {
                                op: ExecPrimOp::Core(PrimOp::Ge),
                                args: vec![
                                    ExecRowExpr::Col("v".to_string()),
                                    ExecRowExpr::Lit(Literal::int(-10)),
                                ],
                            },
                        }),
                        keys: vec![
                            ("grp".to_string(), SortDir::Asc),
                            ("k".to_string(), SortDir::Asc),
                        ],
                    }),
                    n: BigInt::from(12u64),
                };
                let prog = make_plan_prog(Vec::new(), Vec::new(), plan);
                total_rows_verified += assert_all_engines_match(
                    &prog,
                    &RunConfig::default(),
                    &format!("f5#{case_idx}"),
                )?;
            }

            // Family 6: redact + pseudonymize (both HMAC-SHA256 & FNV-1a) + group_by + summarize + sort_by
            6 => {
                let schema = table_ty(vec![
                    col("email", ScalarTy::Text, &["pii"]),
                    col("ssn", opt(ScalarTy::Text), &["pii"]),
                    col("val", ScalarTy::Int, &[]),
                ]);
                let nrows = 2 + rng.gen_usize(18);
                let emails = ["a@u.edu", "b@u.edu", "c@u.edu", "d@u.edu"];
                let mut rows = Vec::with_capacity(nrows);
                for _ in 0..nrows {
                    let ssn = if rng.gen_bool(1, 3) {
                        Literal::NoneLit(Ty::Text)
                    } else {
                        Literal::Text("123-45-6789".to_string())
                    };
                    rows.push(RowLit {
                        cells: vec![
                            Literal::Text(emails[rng.gen_usize(emails.len())].to_string()),
                            ssn,
                            Literal::int(rng.pick_int()),
                        ],
                    });
                }
                let plan = ExecPlan::Sort {
                    input: Box::new(ExecPlan::Summarize {
                        input: Box::new(ExecPlan::GroupBy {
                            input: Box::new(ExecPlan::Pseudonymize {
                                input: Box::new(ExecPlan::Redact {
                                    input: Box::new(table_lit_plan(schema, rows)),
                                    col: "ssn".to_string(),
                                    replacement: "[MASKED]".to_string(),
                                }),
                                col: "email".to_string(),
                                secret: Box::new(ExecExpr::Var("salt".to_string())),
                            }),
                            keys: vec!["email".to_string()],
                        }),
                        aggs: vec![
                            ExecAggItem {
                                name: "cnt".to_string(),
                                op: AggOp::Count,
                                arg: None,
                            },
                            ExecAggItem {
                                name: "tot".to_string(),
                                op: AggOp::Sum,
                                arg: Some(ExecRowExpr::Col("val".to_string())),
                            },
                        ],
                        distinct_key: None,
                    }),
                    keys: vec![("email".to_string(), SortDir::Asc)],
                };
                let prog = make_plan_prog(
                    vec![(
                        "salt".to_string(),
                        LTy::public(Ty::Secret("SOAK_SALT".to_string())),
                    )],
                    Vec::new(),
                    plan,
                );
                let mode = if rng.gen_bool(1, 2) {
                    PseudonymizeMode::HmacSha256
                } else {
                    PseudonymizeMode::CoreV01Fnv1a
                };
                let cfg = RunConfig {
                    pseudonymize_mode: mode,
                    ..RunConfig::default()
                };
                total_rows_verified +=
                    assert_all_engines_match(&prog, &cfg, &format!("f6_{mode:?}#{case_idx}"))?;
            }

            // Family 7: Live SQLite DB-backed SQL pushdown hybrid pipelines
            _ => {
                let mut conn = open_connection(&db_uri)?;
                conn.execute("BEGIN", &[])?;
                conn.execute(r#"DELETE FROM "orders""#, &[])?;
                conn.execute(r#"DELETE FROM "dims""#, &[])?;

                for (g, w, lbl) in [("A", 2i64, "Alpha"), ("B", 3, "Beta"), ("C", 5, "Gamma")] {
                    conn.execute(
                        r#"INSERT INTO "dims" ("grp", "weight", "label") VALUES (?, ?, ?)"#,
                        &[
                            SqlParam::Text(g.to_string()),
                            SqlParam::Int(w),
                            SqlParam::Text(lbl.to_string()),
                        ],
                    )?;
                }
                let nrows = 4 + rng.gen_usize(16);
                for id in 1..=(nrows as i64) {
                    let grp = if id <= 5 {
                        "A".to_string()
                    } else {
                        ["A", "B", "C"][rng.gen_usize(3)].to_string()
                    };
                    let val = rng.pick_int();
                    let amt = BigInt::from(rng.pick_dec_scaled());
                    let flag = rng.gen_bool(2, 3);
                    conn.execute(
                        r#"INSERT INTO "orders" ("id", "grp", "val", "amt", "flag") VALUES (?, ?, ?, ?, ?)"#,
                        &[
                            SqlParam::Int(id),
                            SqlParam::Text(grp),
                            SqlParam::Int(val),
                            SqlParam::Decimal(amt),
                            SqlParam::Bool(flag),
                        ],
                    )?;
                }
                conn.execute("COMMIT", &[])?;
                drop(conn);

                let orders_schema = table_ty(vec![
                    col("id", ScalarTy::Int, &[]),
                    col("grp", ScalarTy::Text, &[]),
                    col("val", ScalarTy::Int, &[]),
                    col("amt", ScalarTy::Decimal, &[]),
                    col("flag", ScalarTy::Bool, &[]),
                ]);
                let dims_schema = table_ty(vec![
                    col("grp", ScalarTy::Text, &[]),
                    col("weight", ScalarTy::Int, &[]),
                    col("label", ScalarTy::Text, &[]),
                ]);

                let orders_src = ExecPlan::SourceDB {
                    cap: Box::new(ExecExpr::Var("db".to_string())),
                    table_name: "orders".to_string(),
                    schema: orders_schema,
                };
                let dims_src = ExecPlan::SourceDB {
                    cap: Box::new(ExecExpr::Var("db".to_string())),
                    table_name: "dims".to_string(),
                    schema: dims_schema,
                };

                let min_v = (rng.gen_usize(10) as i64) - 5;
                let db_plan = if rng.gen_bool(1, 2) {
                    // Pushdown Join + Filter -> local Summarize + SuppressSmallGroups + Sort
                    ExecPlan::Sort {
                        input: Box::new(ExecPlan::SuppressSmallGroups {
                            input: Box::new(ExecPlan::Summarize {
                                input: Box::new(ExecPlan::GroupBy {
                                    input: Box::new(ExecPlan::Join {
                                        kind: JoinKind::InnerManyToOne,
                                        left: Box::new(ExecPlan::Filter {
                                            input: Box::new(orders_src),
                                            pred: ExecRowExpr::Prim {
                                                op: ExecPrimOp::Core(PrimOp::AndBool),
                                                args: vec![
                                                    ExecRowExpr::Col("flag".to_string()),
                                                    ExecRowExpr::Prim {
                                                        op: ExecPrimOp::Core(PrimOp::Ge),
                                                        args: vec![
                                                            ExecRowExpr::Col("val".to_string()),
                                                            ExecRowExpr::Lit(Literal::int(min_v)),
                                                        ],
                                                    },
                                                ],
                                            },
                                        }),
                                        right: Box::new(dims_src),
                                        on: JoinOn::SameKeys(vec!["grp".to_string()]),
                                        suffixes: None,
                                    }),
                                    keys: vec!["label".to_string()],
                                }),
                                aggs: vec![
                                    ExecAggItem {
                                        name: "n".to_string(),
                                        op: AggOp::Count,
                                        arg: None,
                                    },
                                    ExecAggItem {
                                        name: "sum_v".to_string(),
                                        op: AggOp::Sum,
                                        arg: Some(ExecRowExpr::Col("val".to_string())),
                                    },
                                ],
                                distinct_key: None,
                            }),
                            min_k: BigInt::from(5u64),
                            distinct_by: None,
                            mode: SuppressMode::Drop,
                        }),
                        keys: vec![("label".to_string(), SortDir::Asc)],
                    }
                } else {
                    // Pushdown Filter + Select -> local Derive(pure UDF) + Window + Sort + Limit
                    ExecPlan::Limit {
                        input: Box::new(ExecPlan::Sort {
                            input: Box::new(ExecPlan::Window {
                                input: Box::new(ExecPlan::Derive {
                                    input: Box::new(ExecPlan::Select {
                                        input: Box::new(ExecPlan::Filter {
                                            input: Box::new(orders_src),
                                            pred: ExecRowExpr::Prim {
                                                op: ExecPrimOp::Core(PrimOp::Ge),
                                                args: vec![
                                                    ExecRowExpr::Col("val".to_string()),
                                                    ExecRowExpr::Lit(Literal::int(min_v)),
                                                ],
                                            },
                                        }),
                                        cols: vec![
                                            "id".to_string(),
                                            "grp".to_string(),
                                            "val".to_string(),
                                        ],
                                    }),
                                    items: vec![ExecDeriveItem::ColExpr {
                                        name: "weighted".to_string(),
                                        expr: Box::new(ExecRowExpr::CallPure {
                                            fn_name: "bonus_score".to_string(),
                                            args: vec![
                                                ExecRowExpr::Col("val".to_string()),
                                                ExecRowExpr::Lit(Literal::int(2)),
                                            ],
                                        }),
                                    }],
                                }),
                                items: vec![WindowItem {
                                    name: "rn".to_string(),
                                    win_fn: WindowFn::RowNumber,
                                    over: vec!["grp".to_string()],
                                    order: vec![("id".to_string(), SortDir::Asc)],
                                }],
                            }),
                            keys: vec![("id".to_string(), SortDir::Asc)],
                        }),
                        n: BigInt::from(10u64),
                    }
                };

                let prog = make_plan_prog(
                    vec![(
                        "db".to_string(),
                        LTy::public(Ty::ReadDB("SoakDb".to_string())),
                    )],
                    vec![pure_udf.clone()],
                    db_plan,
                );
                // Verify SQL pushdown actually fires on every DB-backed soak plan!
                if let Some(entry_fn) = prog.find_fun("soak_entry")
                    && let ExecExpr::Rel(ref plan) = entry_fn.body
                {
                    let split = split_exec_plan_pushdown(
                        plan,
                        &prog,
                        "SoakDb",
                        SqlDialect::Sqlite,
                        Some(&lock),
                    );
                    if matches!(split, SplitPlan::FullyPushed(_) | SplitPlan::Hybrid { .. }) {
                        db_pushed_cases += 1;
                    }
                }
                let mut db_bindings = HashMap::new();
                db_bindings.insert("SoakDb".to_string(), db_uri.clone());
                let run_cfg = RunConfig {
                    db_bindings,
                    schema_lock: Some(lock.clone()),
                    ..RunConfig::default()
                };
                total_rows_verified +=
                    assert_all_engines_match(&prog, &run_cfg, &format!("f7_sqlite#{case_idx}"))?;
            }
        }
    }

    assert!(
        db_pushed_cases > 0,
        "expected SQLite pushdown to fire on DB-backed soak cases"
    );
    eprintln!(
        "[soak] cases={total_cases} (families={family_counts:?}), db_pushed={db_pushed_cases}, verified_output_rows={total_rows_verified}, 100% Oracle==VM(seq_unopt/seq_opt/par_opt)==SQLite parity"
    );
    Ok(())
}

// ===========================================================================
// 2. Adversarial Privacy & Security Red-Team Audit (35+ Explicit Probes)
// ===========================================================================

fn assert_compile_rejected(
    name: &str,
    src: &str,
    policy_src: Option<&str>,
    expected_codes: &[DiagCode],
) -> TestResult {
    let mut sm = SourceMap::new();
    let policy = match policy_src {
        Some(ps) => {
            let pfid = sm.add_file(format!("{name}.policy"), ps.to_string());
            Some(parse_policy(pfid, ps).map_err(|d| {
                format!("{name} policy parse error: {}", render_diagnostic(&d, &sm))
            })?)
        }
        None => None,
    };
    let fid = sm.add_file(format!("{name}.dana"), src.to_string());
    let ast = parse_module(fid, src)
        .map_err(|d| format!("{name} parse error:\n{}", render_diagnostic(&d, &sm)))?;
    match check_module(fid, ast, policy, &sm) {
        Ok(_) => Err(format!(
            "PRIVACY RED-TEAM FAILURE: probe `{name}` unexpectedly passed type/privacy check!"
        )
        .into()),
        Err(diags) => {
            let matched = diags.iter().any(|d| expected_codes.contains(&d.code()));
            if !matched {
                let got: Vec<(DiagCode, &str)> =
                    diags.iter().map(|d| (d.code(), d.message())).collect();
                return Err(format!(
                    "probe `{name}` expected one of {expected_codes:?}, got {got:?}"
                )
                .into());
            }
            Ok(())
        }
    }
}

fn compile_dana_source(src: &str, policy: Option<Policy>) -> Result<ExecProgram, String> {
    let mut sm = SourceMap::new();
    let fid = sm.add_file("redteam.dana".to_string(), src.to_string());
    let ast = parse_module(fid, src).map_err(|d| render_diagnostic(&d, &sm))?;
    let checked = check_module(fid, ast, policy, &sm).map_err(|ds| {
        ds.iter()
            .map(|d| render_diagnostic(d, &sm))
            .collect::<String>()
    })?;
    let lowered = lower_program(checked).map_err(|d| render_diagnostic(&d, &sm))?;
    Ok(lowered.exec)
}

#[test]
fn redteam_01_implicit_control_flow_laundering_probes() -> TestResult {
    let probes: &[(&str, &str)] = &[
        // 1. `if` branch console leak & variable assignment laundering
        (
            "cf_01_if_branch_and_var_assign",
            r##"
module ProbeIf
fn main(secret: Bool [pii], console: Console) : Int
  var out = 0
  if secret
    out = 1
  end
  console.print("#{out}")
  0
end
"##,
        ),
        // 2. `case` arm laundering on sensitive scrutinee
        (
            "cf_02_case_scrutinee_launder",
            r##"
module ProbeCase
fn main(secret: Int [pii], console: Console) : Int
  var out = "no"
  case secret
    42:
      out = "yes"
    _:
      out = "no"
  end
  console.print(out)
  0
end
"##,
        ),
        // 3. `while` loop condition / indirect cross-iteration fixpoint laundering
        (
            "cf_03_while_loop_launder",
            r#"
module ProbeWhile
fn main(secret: Bool [pii], console: Console) : Int
  var running = true
  while running
    console.print("tick")
    running = secret
  end
  0
end
"#,
        ),
        // 4. `for` loop body & mutable accumulator laundering
        (
            "cf_04_for_loop_accumulator",
            r##"
module ProbeFor
fn main(secret: Int [pii], console: Console) : Int
  var acc = 0
  for i in [1, 2, 3, 4]
    if i == secret
      acc = acc + 1
    end
  end
  console.print("#{acc}")
  0
end
"##,
        ),
        // 5. `return if` guarded early-return post-statement PC laundering
        (
            "cf_05_return_if_post_pc",
            r#"
module ProbeReturnIf
fn main(secret: Int [pii], console: Console) : Int [pii]
  return 1 if secret == 7
  console.print("not 7")
  0
end
"#,
        ),
        // 6. `break if` guarded loop-exit value laundering
        (
            "cf_06_break_if_value",
            r#"
module ProbeBreakIf
fn leak(secret: Int [pii]) : Int
  var found = 0
  for i in [10, 20, 30]
    found = i
    break if i == secret
  end
  found
end
"#,
        ),
        // 7. `continue if` guarded skip accumulator laundering
        (
            "cf_07_continue_if_skip",
            r#"
module ProbeContinueIf
fn leak(secret: Int [pii]) : Int
  var total = 0
  for i in [1, 2, 3]
    continue if i == secret
    total = total + i
  end
  total
end
"#,
        ),
        // 8. Short-circuit `and` side-effect laundering
        (
            "cf_08_short_circuit_and",
            r#"
module ProbeAnd
fn side(console: Console) : Bool
  console.print("rhs ran")
  true
end
fn main(secret: Bool [pii], console: Console) : Int
  _ = secret and side(console)
  0
end
"#,
        ),
        // 9. Short-circuit `or` side-effect laundering
        (
            "cf_09_short_circuit_or",
            r#"
module ProbeOr
fn side(console: Console) : Bool
  console.print("rhs ran")
  true
end
fn main(secret: Bool [pii], console: Console) : Int
  _ = secret or side(console)
  0
end
"#,
        ),
        // 10. Null-coalescing `??` side-effect & value laundering
        (
            "cf_10_coalesce_side_effect",
            r#"
module ProbeCoalesceSide
fn fallback(console: Console) : Int
  console.print("was none")
  0
end
fn main(secret: Int? [pii], console: Console) : Int
  _ = secret ?? fallback(console)
  0
end
"#,
        ),
        (
            "cf_10b_coalesce_value_launder",
            r##"
module ProbeCoalesceVal
fn main(secret: Int? [pii], console: Console) : Int
  v = secret ?? 0
  console.print("#{v}")
  0
end
"##,
        ),
        // 11. Closure capturing sensitive variable & closure called under sensitive PC
        (
            "cf_11a_closure_capture_launder",
            r##"
module ProbeClosureCapture
fn main(secret: Int [pii], console: Console) : Int
  f = fn(x)
    x + secret
  end
  console.print("#{f(1)}")
  0
end
"##,
        ),
        (
            "cf_11b_closure_effect_under_sensitive_pc",
            r#"
module ProbeClosurePc
fn main(secret: Bool [pii], console: Console) : Int
  say = fn(msg)
    console.print(msg)
  end
  if secret
    say("leaked via closure")
  end
  0
end
"#,
        ),
        // 12. `.or_return` post-statement PC laundering
        (
            "cf_12_or_return_post_pc",
            r#"
module ProbeOrReturn
fn main(secret: Int? [pii], console: Console) : Int [pii]
  _ = secret.or_return(0)
  console.print("secret was Some")
  1
end
"#,
        ),
        // 13. `try` on sensitive Result laundering (both Result-returning & Int-returning main!)
        (
            "cf_13a_try_result_fn_post_pc",
            r#"
module ProbeTryRes
fn check(secret: Result(Int, Text) [pii], console: Console) : Result(Int, Text) [pii]
  _ = try secret
  console.print("secret was Ok")
  Ok(0)
end
"#,
        ),
        (
            "cf_13b_try_main_post_pc",
            r#"
module ProbeTryMain
fn main(secret: Result(Int, Text) [pii], console: Console) : Int
  _ = try secret
  console.print("secret was Ok in main")
  0
end
"#,
        ),
    ];

    for (name, src) in probes {
        assert_compile_rejected(name, src, None, &[DiagCode::PrivacyError])?;
    }
    eprintln!(
        "[redteam/01_implicit_cf] {} implicit control-flow probes statically blocked (E0202)",
        probes.len()
    );
    Ok(())
}

#[test]
fn redteam_02_relational_and_statistical_side_channels() -> TestResult {
    let probes: &[(&str, &str)] = &[
        // 1. `where` on [pii] col -> `.count()` membership oracle
        (
            "rel_01_where_count_oracle",
            r##"
module RelWhereCount
schema User
  ssn: Text [pii]
  dept: Text
end
fn main(u: Table(User), console: Console) : Int
  n = (u |> where(.ssn == "123-45-6789")).count()
  console.print("#{n}")
  0
end
"##,
        ),
        // 2. `sort_by` on [pii] col -> `.first!` order-channel leak
        (
            "rel_02_sort_first_order_channel",
            r#"
module RelSortFirst
schema User
  salary: Int [pii]
  dept: Text
end
fn main(u: Table(User), console: Console) : Int
  top = (u |> sort_by(.salary, :desc)).first!
  console.print(top.dept)
  0
end
"#,
        ),
        // 3. `distinct` on [pii] col -> `.count()` cardinality oracle
        (
            "rel_03_distinct_count_oracle",
            r##"
module RelDistinctCount
schema User
  ssn: Text [pii]
  dept: Text
end
fn main(u: Table(User), console: Console) : Int
  n = (u |> distinct(.ssn)).count()
  console.print("#{n}")
  0
end
"##,
        ),
        // 4. `join` (`join_one`, `semi_join`, `anti_join`) on [pii] key
        (
            "rel_04a_join_one_sensitive_key",
            r##"
module RelJoinKey
schema A
  ssn: Text [pii]
  dept: Text
end
schema B
  ssn: Text [pii]
  flag: Text
end
fn main(a: Table(A), b: Table(B), console: Console) : Int
  j = a |> join_one(b, on: .ssn) |> select(.dept, .flag)
  console.print("#{j.count()}")
  0
end
"##,
        ),
        (
            "rel_04b_semi_join_sensitive_key",
            r#"
module RelSemiJoinKey
schema A
  ssn: Text [pii]
  dept: Text
end
schema B
  ssn: Text [pii]
end
fn main(a: Table(A), b: Table(B), console: Console) : Int
  j = a |> semi_join(b, on: .ssn) |> select(.dept)
  console.print_table(j)
  0
end
"#,
        ),
        // 5. `pivot_longer` melting a [pii] col alongside a public col
        (
            "rel_05_pivot_longer_melt_pii_with_public",
            r#"
module RelPivotLonger
schema Scores
  dept: Text
  pub_score: Float
  priv_score: Float [pii]
end
fn main(s: Table(Scores), console: Console) : Int
  melted = s |> pivot_longer(cols: [.pub_score, .priv_score], names_to: "kind", values_to: "v")
  console.print_table(melted)
  0
end
"#,
        ),
        // 6. `pivot_wider` on sensitive `names_from` or `values_from`
        (
            "rel_06a_pivot_wider_sensitive_names",
            r#"
module RelPivotWiderNames
schema Long
  dept: Text
  secret_cat: Text [pii]
  v: Int
end
fn main(t: Table(Long), console: Console) : Int
  w = t |> pivot_wider(names_from: .secret_cat, values_from: .v, columns: ["x", "y"], fill: 0)
  console.print_table(w)
  0
end
"#,
        ),
        (
            "rel_06b_pivot_wider_sensitive_values",
            r#"
module RelPivotWiderVals
schema Long
  dept: Text
  cat: Text
  secret_v: Int [pii]
end
fn main(t: Table(Long), console: Console) : Int
  w = t |> pivot_wider(names_from: .cat, values_from: .secret_v, columns: ["x", "y"], fill: 0)
  console.print_table(w)
  0
end
"#,
        ),
        // 7. `Stats.corr` (:pearson & :spearman) on [pii] col
        (
            "rel_07a_stats_corr_pearson",
            r##"
module RelStatsCorrP
use Stats
schema Row
  x: Float [pii]
  y: Float
end
fn main(t: Table(Row), console: Console) : Int
  r = Stats.corr(t, x: .x, y: .y, method: :pearson)
  console.print("#{r}")
  0
end
"##,
        ),
        (
            "rel_07b_stats_corr_spearman",
            r##"
module RelStatsCorrS
use Stats
schema Row
  x: Float
  y: Float [pii]
end
fn main(t: Table(Row), console: Console) : Int
  r = Stats.corr(t, x: .x, y: .y, method: :spearman)
  console.print("#{r}")
  0
end
"##,
        ),
        // 8. `Stats.t_test` on [pii] column
        (
            "rel_08_stats_t_test",
            r##"
module RelStatsTTest
use Stats
schema Row
  v: Float [pii]
end
fn main(a: Table(Row), b: Table(Row), console: Console) : Int
  res = Stats.t_test(a, b, column: .v)
  console.print("#{res.p_value}")
  0
end
"##,
        ),
        // 9. `Stats.chi_square` (independence & GOF) on [pii] column
        (
            "rel_09a_stats_chi_square_ind",
            r##"
module RelStatsChiInd
use Stats
schema Row
  grp: Text [pii]
  out: Text
end
fn main(t: Table(Row), console: Console) : Int
  res = Stats.chi_square(t, x: .grp, y: .out)
  console.print("#{res.p_value}")
  0
end
"##,
        ),
        (
            "rel_09b_stats_chi_square_gof",
            r##"
module RelStatsChiGof
use Stats
schema Row
  obs: Float [pii]
  exp: Float
end
fn main(t: Table(Row), console: Console) : Int
  res = Stats.chi_square(t, observed: .obs, expected: .exp)
  console.print("#{res.p_value}")
  0
end
"##,
        ),
        // 10. `Stats.outliers` (:zscore & :iqr) flag column inherits [pii]
        (
            "rel_10_stats_outliers",
            r#"
module RelStatsOutliers
use Stats
schema Row
  dept: Text
  income: Float [pii]
end
fn main(t: Table(Row), console: Console) : Int
  flagged = Stats.outliers(t, column: .income, method: :iqr, threshold: 1.5, flag: "is_out")
  console.print_table(flagged |> select(.dept, .is_out))
  0
end
"#,
        ),
        // 11. `model.predict` with sensitive model OR sensitive input
        (
            "rel_11a_model_predict_sensitive_model",
            r##"
module RelPredictModel
use Stats
schema Row
  x: Float [pii]
  y: Float
end
fn main(t: Table(Row), console: Console) : Int
  m = Stats.linear_regression(t, x: .x, y: .y)
  console.print("#{m.predict(3.0)}")
  0
end
"##,
        ),
        (
            "rel_11b_model_predict_sensitive_arg",
            r##"
module RelPredictArg
use Stats
schema Row
  x: Float
  y: Float
end
fn main(t: Table(Row), sx: Float [pii], console: Console) : Int
  m = Stats.linear_regression(t, x: .x, y: .y)
  console.print("#{m.predict(sx)}")
  0
end
"##,
        ),
        // 12. ALL 4 order statistics (min, max, median, percentile) remain tagged after suppress_small_groups!
        (
            "rel_12a_order_stat_min_after_suppress",
            r#"
module RelSuppressMin
schema Patient
  id: Int [pii]
  dept: Text
  score: Float [health]
end
fn main(p: Table(Patient), console: Console) : Int
  s = p
    |> group_by(.dept)
    |> summarize(n: count_distinct(.id), lo: min(.score))
    |> suppress_small_groups(min: 5, distinct_by: .id)
  console.print_table(s)
  0
end
"#,
        ),
        (
            "rel_12b_order_stat_max_after_suppress",
            r#"
module RelSuppressMax
schema Patient
  id: Int [pii]
  dept: Text
  score: Float [health]
end
fn main(p: Table(Patient), console: Console) : Int
  s = p
    |> group_by(.dept)
    |> summarize(n: count_distinct(.id), hi: max(.score))
    |> suppress_small_groups(min: 5, distinct_by: .id)
  console.print_table(s)
  0
end
"#,
        ),
        (
            "rel_12c_order_stat_median_after_suppress",
            r#"
module RelSuppressMedian
schema Patient
  id: Int [pii]
  dept: Text
  score: Float [health]
end
fn main(p: Table(Patient), console: Console) : Int
  s = p
    |> group_by(.dept)
    |> summarize(n: count_distinct(.id), med: median(.score))
    |> suppress_small_groups(min: 5, distinct_by: .id)
  console.print_table(s)
  0
end
"#,
        ),
        (
            "rel_12d_order_stat_percentile_after_suppress",
            r#"
module RelSuppressPct
schema Patient
  id: Int [pii]
  dept: Text
  score: Float [health]
end
fn main(p: Table(Patient), console: Console) : Int
  s = p
    |> group_by(.dept)
    |> summarize(n: count_distinct(.id), p90: percentile(.score, 0.9))
    |> suppress_small_groups(min: 5, distinct_by: .id)
  console.print_table(s)
  0
end
"#,
        ),
    ];

    for (name, src) in probes {
        assert_compile_rejected(name, src, None, &[DiagCode::PrivacyError])?;
    }
    eprintln!(
        "[redteam/02_relational_stats] {} relational & statistical side-channel probes statically blocked (E0202)",
        probes.len()
    );
    Ok(())
}

#[test]
fn redteam_03_runtime_and_system_boundaries() -> TestResult {
    let mut verified_boundaries = 0usize;

    // -----------------------------------------------------------------------
    // B1. Crash `Bug` diagnostics redaction (JoinCardinality on [pii] key)
    // -----------------------------------------------------------------------
    {
        let secret_ssn = "999-SECRET-8888";
        let left_schema = table_ty(vec![
            col("ssn", ScalarTy::Text, &["pii"]),
            col("v", ScalarTy::Int, &[]),
        ]);
        let right_schema = table_ty(vec![
            col("ssn", ScalarTy::Text, &["pii"]),
            col("r", ScalarTy::Int, &[]),
        ]);
        let plan = ExecPlan::Join {
            kind: JoinKind::InnerOne,
            left: Box::new(table_lit_plan(
                left_schema,
                vec![RowLit {
                    cells: vec![Literal::Text(secret_ssn.to_string()), Literal::int(1)],
                }],
            )),
            right: Box::new(table_lit_plan(
                right_schema,
                vec![
                    RowLit {
                        cells: vec![Literal::Text(secret_ssn.to_string()), Literal::int(10)],
                    },
                    RowLit {
                        cells: vec![Literal::Text(secret_ssn.to_string()), Literal::int(20)],
                    },
                ],
            )),
            on: JoinOn::SameKeys(vec!["ssn".to_string()]),
            suffixes: None,
        };
        let prog = make_plan_prog(Vec::new(), Vec::new(), plan);
        let cfg = RunConfig::default();
        let vm_cfg = VmConfig::default();
        for (engine, res) in [
            ("oracle", eval_exec_entry(&prog, "soak_entry", &[], &cfg)),
            (
                "vm",
                eval_exec_entry_vm(&prog, "soak_entry", &[], &cfg, &vm_cfg),
            ),
        ] {
            match res {
                EvalProgramResult::Stopped { bug, .. } => {
                    assert_eq!(bug.kind, BugKind::JoinCardinality, "{engine}");
                    assert!(
                        !bug.message.contains(secret_ssn),
                        "{engine}: JoinCardinality Bug leaked raw PII key `{secret_ssn}`: {}",
                        bug.message
                    );
                }
                other => {
                    return Err(
                        format!("{engine}: expected JoinCardinality stop, got {other:?}").into(),
                    );
                }
            }
        }
        // Also verify Core IR JoinCardinality emits explicit `[REDACTED:pii]` across Oracle & VM!
        let core_prog = dana::core::Program {
            funs: vec![dana::core::FunDecl {
                name: "main".to_string(),
                kind: FunKind::Function,
                is_pure: false,
                params: Vec::new(),
                pc: TagSet::empty(),
                ret: LTy::public(Ty::Table(TableTy {
                    cols: vec![
                        col("ssn", ScalarTy::Text, &["pii"]),
                        col("v", ScalarTy::Int, &[]),
                        col("r", ScalarTy::Int, &[]),
                    ],
                    row_tags: TagSet::singleton("pii"),
                    ..TableTy::default()
                })),
                body: dana::core::Expr::Rel(Box::new(dana::core::Plan::Join {
                    kind: JoinKind::InnerOne,
                    left: Box::new(dana::core::Plan::SourceExpr(Box::new(
                        dana::core::Expr::TableLit {
                            schema: table_ty(vec![
                                col("ssn", ScalarTy::Text, &["pii"]),
                                col("v", ScalarTy::Int, &[]),
                            ]),
                            rows: vec![RowLit {
                                cells: vec![Literal::Text(secret_ssn.to_string()), Literal::int(1)],
                            }],
                        },
                    ))),
                    right: Box::new(dana::core::Plan::SourceExpr(Box::new(
                        dana::core::Expr::TableLit {
                            schema: table_ty(vec![
                                col("ssn", ScalarTy::Text, &["pii"]),
                                col("r", ScalarTy::Int, &[]),
                            ]),
                            rows: vec![
                                RowLit {
                                    cells: vec![
                                        Literal::Text(secret_ssn.to_string()),
                                        Literal::int(10),
                                    ],
                                },
                                RowLit {
                                    cells: vec![
                                        Literal::Text(secret_ssn.to_string()),
                                        Literal::int(20),
                                    ],
                                },
                            ],
                        },
                    ))),
                    on: JoinOn::SameKeys(vec!["ssn".to_string()]),
                    suffixes: None,
                })),
            }],
            entry: Some("main".to_string()),
            ..dana::core::Program::default()
        };
        let core_oracle =
            dana::oracle::run_program(10_000, &core_prog, dana::oracle::World::default())?;
        let core_vm = dana::vm::run_core_program_vm(
            10_000,
            &core_prog,
            dana::oracle::World::default(),
            &VmConfig::default(),
        )?;
        for (label, rep) in [("core_oracle", core_oracle), ("core_vm", core_vm)] {
            assert_eq!(rep.status, dana::oracle::ExitStatus::Stopped, "{label}");
            let diag = rep.diagnostic.as_deref().unwrap_or("");
            assert!(
                !diag.contains(secret_ssn),
                "{label}: leaked secret_ssn: {diag}"
            );
            assert!(
                diag.contains("[REDACTED:pii]"),
                "{label}: expected [REDACTED:pii] in Core IR Bug: {diag}"
            );
        }
        verified_boundaries += 1;
    }

    // -----------------------------------------------------------------------
    // B2. CSV / JSONL / XLSX `bad_rows` quarantine redaction (static + runtime)
    // -----------------------------------------------------------------------
    {
        let schema = table_ty(vec![
            col("id", ScalarTy::Int, &[]),
            col("ssn", ScalarTy::Text, &["pii"]),
            col("gpa", ScalarTy::Decimal, &["ferpa"]),
        ]);
        let (_, csv_bad) = parse_csv_with_schema(
            "id,ssn,gpa\n1,999-88-7777,not_a_dec\n",
            &schema,
            b',',
            |_, _| true,
        )?;
        assert_eq!(csv_bad.rows.len(), 1);
        let (_, jsonl_bad) = parse_jsonl_with_schema(
            r#"{"id":1,"ssn":"999-88-7777","gpa":"not_a_dec"}"#,
            &schema,
            |_, _| true,
        )?;
        assert_eq!(jsonl_bad.rows.len(), 1);

        let xlsx_src_table = TableVal {
            cols: vec![
                col("id", ScalarTy::Text, &[]),
                col("ssn", ScalarTy::Text, &[]),
                col("gpa", ScalarTy::Text, &[]),
            ],
            rows: vec![TableRow {
                cells: vec![
                    Val::Text("1".to_string()),
                    Val::Text("999-88-7777".to_string()),
                    Val::Text("not_a_dec".to_string()),
                ],
                group_meta: None,
            }],
        };
        let xlsx_bytes = write_xlsx_sheets(&[("Sheet1".to_string(), xlsx_src_table)])?;
        let (_, xlsx_bad) = read_xlsx_bytes_with_schema(&xlsx_bytes, None, &schema, |_, _| true)?;
        assert_eq!(xlsx_bad.rows.len(), 1);

        for (fmt_name, bad_tv) in [
            ("csv", &csv_bad),
            ("jsonl", &jsonl_bad),
            ("xlsx", &xlsx_bad),
        ] {
            let raw_col = bad_tv
                .cols
                .iter()
                .find(|c| c.name == "raw_line")
                .ok_or("missing raw_line col in bad_rows")?;
            assert!(
                raw_col.tags.elems().iter().any(|t| t == "pii")
                    && raw_col.tags.elems().iter().any(|t| t == "ferpa"),
                "{fmt_name} bad_rows raw_line must inherit both [pii, ferpa]: {:?}",
                raw_col.tags
            );
        }

        // Static rejection when attempting to print `bad_rows` to public console
        assert_compile_rejected(
            "bad_rows_console_leak",
            r#"
module BadRowsLeak
schema Student
  id: Int
  ssn: Text [pii]
  gpa: Decimal [ferpa]
end
fn main(files: ReadFiles, console: Console) : Int
  (good, bad) = try files.read_csv("students.csv", as: Student)
  _ = good
  console.print_table(bad)
  0
end
"#,
            None,
            &[DiagCode::PrivacyError],
        )?;
        verified_boundaries += 1;
    }

    // -----------------------------------------------------------------------
    // B3. `table.profile()` strict `[REDACTED:<tags>]` + filtered row_tags rejection
    // -----------------------------------------------------------------------
    {
        let tv = TableVal {
            cols: vec![
                col("ssn", ScalarTy::Text, &["pii"]),
                col("gpa", ScalarTy::Float, &["ferpa"]),
                col("dept", ScalarTy::Text, &[]),
            ],
            rows: vec![
                TableRow {
                    cells: vec![
                        Val::Text("888-77-6666".to_string()),
                        Val::Float(Float64::from_f64(3.99)),
                        Val::Text("Math".to_string()),
                    ],
                    group_meta: None,
                },
                TableRow {
                    cells: vec![
                        Val::Text("777-66-5555".to_string()),
                        Val::Float(Float64::from_f64(3.11)),
                        Val::Text("Math".to_string()),
                    ],
                    group_meta: None,
                },
            ],
        };
        let prof = profile_table(&tv, &TagSet::empty(), &[]);
        let rendered = render_profile_terminal(&prof);
        assert!(rendered.contains("[REDACTED:pii]"), "{rendered}");
        assert!(rendered.contains("[REDACTED:ferpa]"), "{rendered}");
        for leak in ["888-77-6666", "777-66-5555", "3.99", "3.11"] {
            assert!(
                !rendered.contains(leak),
                "profile leaked `{leak}`:\n{rendered}"
            );
        }
        assert!(
            rendered.contains("Math"),
            "public col should render:\n{rendered}"
        );

        // Filtered table profile (`row_tags = [pii]`) must be statically rejected by public Console!
        assert_compile_rejected(
            "filtered_profile_console_leak",
            r#"
module FilteredProfLeak
schema User
  ssn: Text [pii]
  dept: Text
end
fn main(u: Table(User), console: Console) : Int
  f = u |> where(.ssn == "888-77-6666")
  console.print_profile(f.profile())
  0
end
"#,
            None,
            &[DiagCode::PrivacyError],
        )?;
        verified_boundaries += 1;
    }

    // -----------------------------------------------------------------------
    // B4. `dana dry-run` redacted diffs with 0 SQLite mutations
    // -----------------------------------------------------------------------
    {
        let tmp = TempDir::new("dry_run")?;
        let db_path = tmp.path().join("dry.db");
        let uri = format!("sqlite://{}", db_path.display());
        let mut conn = open_connection(&uri)?;
        conn.execute(
            r#"CREATE TABLE "students" (
                "id" INTEGER PRIMARY KEY NOT NULL,
                "ssn" TEXT NOT NULL,
                "gpa" TEXT NOT NULL
            )"#,
            &[],
        )?;
        conn.execute(
            r#"INSERT INTO "students" ("id", "ssn", "gpa") VALUES (?, ?, ?)"#,
            &[
                SqlParam::Int(1),
                SqlParam::Text("111-11-1111".to_string()),
                SqlParam::Text("3.40".to_string()),
            ],
        )?;
        drop(conn);

        let script = tmp.path().join("dry_sync.dana");
        fs::write(
            &script,
            r#"module DrySync
schema Students
  id: Int [pii]
  ssn: Text [pii]
  gpa: Decimal [ferpa]
end
fn main(
  dbr: ReadDB(Reg),
  dbw: WriteTable(Reg, "students", allows: [pii, ferpa]),
  console: Console
) : Int
  existing = dbr.table(Students)
  updates = existing |> derive(gpa: 3.98)
  extra = table
    | id | ssn           | gpa  |
    | 2  | "222-22-2222" | 3.77 |
  end
  combined = updates |> union(extra)
  _ = try dbw.upsert(combined, key: .id)
  console.print("done")
  0
end
"#,
        )?;
        let out = Command::new(dana_bin())
            .args([
                "dry-run",
                "--db",
                &format!("Reg={uri}"),
                &script.to_string_lossy(),
            ])
            .output()?;
        let stdout = String::from_utf8_lossy(&out.stdout);
        let stderr = String::from_utf8_lossy(&out.stderr);
        assert!(
            out.status.success(),
            "dana dry-run failed: stderr={stderr}\nstdout={stdout}"
        );
        assert!(
            stdout.contains("[REDACTED:pii]") && stdout.contains("[REDACTED:ferpa]"),
            "dry-run diff must redact pii & ferpa:\n{stdout}"
        );
        for secret in ["111-11-1111", "222-22-2222", "3.98", "3.77", "3.40"] {
            assert!(
                !stdout.contains(secret) && !stderr.contains(secret),
                "dry-run leaked secret `{secret}`!\nstdout={stdout}\nstderr={stderr}"
            );
        }
        // Verify 0 mutations occurred in SQLite
        let mut verify = open_connection(&uri)?;
        let cnt_tbl = verify.query_rows(
            r#"SELECT COUNT(*) AS "n" FROM "students""#,
            &[],
            &table_ty(vec![col("n", ScalarTy::Int, &[])]),
        )?;
        assert!(val_eq(
            &cnt_tbl.rows[0].cells[0],
            &Val::Int(BigInt::from(1))
        ));
        verified_boundaries += 1;
    }

    // -----------------------------------------------------------------------
    // B5. `dana repl` redaction (scalars, tables, row_tags, order_tags, filtered :profile, forbid policy)
    // -----------------------------------------------------------------------
    {
        let tmp = TempDir::new("repl_redteam")?;
        let mut repl = ReplSession::new(ReplConfig {
            work_dir: tmp.path().to_path_buf(),
            ..ReplConfig::default()
        })
        .map_err(|d| format!("ReplSession::new: {}", d.message()))?;

        let _ = repl.eval_input(
            r#"schema Sec
  ssn: Text [pii]
  salary: Int [pii]
  dept: Text
end"#,
        );
        let _ = repl.eval_input(
            r#"fn mk() : Table(Sec)
  table
    | ssn           | salary | dept    |
    | "555-44-3333" | 195000 | "Legal" |
    | "666-55-4444" | 110000 | "Sales" |
  end
end"#,
        );
        let _ = repl.eval_input("fn sec_s() : Text [pii]\n  \"TOP-SECRET-TOKEN\"\nend");
        let _ = repl.eval_input("t = mk()");

        // (a) Scalar [pii]
        match repl.eval_input("sec_s()") {
            ReplOutput::Value { rendered, .. } => {
                assert_eq!(rendered, "[REDACTED:pii]");
            }
            other => return Err(format!("expected redacted scalar, got {other:?}").into()),
        }
        // (b) Table [pii] columns
        match repl.eval_input("t") {
            ReplOutput::Value { rendered, .. } => {
                assert!(rendered.contains("[REDACTED:pii]"));
                assert!(rendered.contains("Legal"));
                assert!(!rendered.contains("555-44-3333"));
                assert!(!rendered.contains("195000"));
            }
            other => return Err(format!("expected redacted table, got {other:?}").into()),
        }
        // (c) `row_tags` from filtering on [pii] redacts even public `dept`!
        match repl.eval_input("t |> where(.ssn == \"555-44-3333\")") {
            ReplOutput::Value { rendered, .. } => {
                assert!(rendered.contains("[REDACTED:pii]"));
                assert!(!rendered.contains("Legal"));
                assert!(!rendered.contains("555-44-3333"));
            }
            other => return Err(format!("expected row_tags redaction, got {other:?}").into()),
        }
        // (d) `order_tags` from `sort_by(.salary)` redacts even public `dept`!
        match repl.eval_input("t |> sort_by(.salary, :desc) |> select(.dept)") {
            ReplOutput::Value { rendered, .. } => {
                assert!(
                    rendered.contains("[REDACTED:pii]"),
                    "order_tags not redacted:\n{rendered}"
                );
                assert!(
                    !rendered.contains("Legal"),
                    "order_tags leaked Legal:\n{rendered}"
                );
                assert!(
                    !rendered.contains("Sales"),
                    "order_tags leaked Sales:\n{rendered}"
                );
            }
            other => return Err(format!("expected order_tags redaction, got {other:?}").into()),
        }
        // (e) `:profile` on filtered [pii] table redacts completely (Regression fix!)
        match repl.eval_input(":profile t |> where(.ssn == \"555-44-3333\")") {
            ReplOutput::Info(rendered) => {
                assert_eq!(
                    rendered, "[REDACTED:pii]",
                    "filtered :profile leaked row count or details: {rendered}"
                );
            }
            other => return Err(format!("expected redacted :profile, got {other:?}").into()),
        }
        // (f) `dana.policy` `forbid repl_show_sensitive` hard-fails with E0202
        let pol = parse_policy(FileId(0), "version 1\nforbid repl_show_sensitive\n")
            .map_err(|d| d.message().to_string())?;
        let denied = ReplSession::new(ReplConfig {
            policy: Some(pol),
            allowed_show_tags: TagSet::singleton("pii"),
            work_dir: tmp.path().to_path_buf(),
            ..ReplConfig::default()
        });
        match denied {
            Err(d) => assert_eq!(d.code(), DiagCode::PrivacyError),
            Ok(_) => {
                return Err("forbid repl_show_sensitive failed to block --show-sensitive".into());
            }
        }
        verified_boundaries += 1;
    }

    // -----------------------------------------------------------------------
    // B6. SVG / HTML / Markdown reports: XSS escaping + tagged chart/report rejection
    // -----------------------------------------------------------------------
    {
        let xss = "<script>alert('xss')</script><img src=x onerror=alert(1)>";
        let chart = ChartVal {
            kind: ChartKind::Bar,
            title: xss.to_string(),
            col_names: vec!["x".to_string(), "y".to_string()],
            series: vec![
                vec![Val::Text(xss.to_string())],
                vec![Val::Float(Float64::from_f64(10.0))],
            ],
            x_col: Some("x".to_string()),
            y_col: Some("y".to_string()),
            color_col: None,
            value_col: None,
            trendline: None,
            bins: None,
        };
        let svg = render_chart_svg(&chart);
        assert!(
            !svg.contains("<script>"),
            "SVG failed to escape <script>:\n{svg}"
        );
        assert!(!svg.contains("<img"), "SVG failed to escape <img>:\n{svg}");
        assert!(
            svg.contains("&lt;script&gt;"),
            "expected escaped entity in SVG:\n{svg}"
        );

        let report = ReportVal {
            title: xss.to_string(),
            summaries: vec![xss.to_string()],
            charts: vec![chart],
            tables: vec![(
                vec![xss.to_string()],
                vec![vec![Val::Text(xss.to_string())]],
            )],
        };
        let html = render_html_report(&report);
        assert!(
            !html.contains("<script>"),
            "HTML failed to escape <script>:\n{html}"
        );
        assert!(
            !html.contains("<img"),
            "HTML failed to escape <img>:\n{html}"
        );
        assert!(html.contains("&lt;script&gt;"));

        let md = render_markdown_report(&report);
        assert!(!md.is_empty());

        // Tagged chart & tagged report static rejection (E0202)
        assert_compile_rejected(
            "tagged_chart_write_svg",
            r#"
module TaggedChart
schema Row
  dept: Text
  salary: Float [pii]
end
fn main(t: Table(Row), out: WriteFiles("out/")) : Int
  c = t |> chart_bar(x: .dept, y: .salary, title: "Salaries")
  try out.write_svg("sal.svg", c)
  0
end
"#,
            None,
            &[DiagCode::PrivacyError],
        )?;
        assert_compile_rejected(
            "tagged_report_write_html",
            r##"
module TaggedReport
fn main(secret: Text [pii], out: WriteFiles("out/")) : Int
  r = Report.new("Audit") |> add_summary("secret=#{secret}")
  try out.write_html("audit.html", r)
  0
end
"##,
            None,
            &[DiagCode::PrivacyError],
        )?;
        verified_boundaries += 1;
    }

    // -----------------------------------------------------------------------
    // B7. `dana.policy` ceiling enforcement (6 distinct ceiling violations)
    // -----------------------------------------------------------------------
    {
        let strict_policy = r#"
version 1
min_group_size 10
forbid manual_declassify
forbid repl_show_sensitive
allow console tags []
allow export "reports/" tags []
allow https "api.trusted.edu" tags []
allow write Analytics.summary tags []
"#;
        // (a) manual declassify forbidden by policy
        assert_compile_rejected(
            "policy_forbid_declassify",
            r#"
module PolDecl
fn main(dec: Declassify(allows: [pii])) : Int
  _ = dec
  0
end
"#,
            Some(strict_policy),
            &[DiagCode::PrivacyError, DiagCode::PolicyError],
        )?;
        // (b) min_group_size 10 rejects suppress_small_groups(min: 5)
        assert_compile_rejected(
            "policy_min_group_size_10",
            r#"
module PolMinK
schema S
  id: Int [pii]
  dept: Text
end
fn main(t: Table(S), console: Console) : Int
  s = t
    |> group_by(.dept)
    |> summarize(n: count_distinct(.id))
    |> suppress_small_groups(min: 5, distinct_by: .id)
  console.print_table(s)
  0
end
"#,
            Some(strict_policy),
            &[DiagCode::PrivacyError, DiagCode::PolicyError],
        )?;
        // (c) allow console tags [] rejects Console(allows: [pii])
        assert_compile_rejected(
            "policy_console_ceiling",
            r#"
module PolConsole
fn main(console: Console(allows: [pii])) : Int
  console.print("hi")
  0
end
"#,
            Some(strict_policy),
            &[DiagCode::PrivacyError, DiagCode::PolicyError],
        )?;
        // (d) allow export "reports/" tags [] rejects WriteFiles("reports/", allows: [pii])
        assert_compile_rejected(
            "policy_export_ceiling",
            r#"
module PolExport
fn main(out: WriteFiles("reports/", allows: [pii])) : Int
  _ = out
  0
end
"#,
            Some(strict_policy),
            &[DiagCode::PrivacyError, DiagCode::PolicyError],
        )?;
        // (e) allow https "api.trusted.edu" tags [] rejects HttpsAllow(..., allows: [pii])
        assert_compile_rejected(
            "policy_https_host_ceiling",
            r#"
module PolHttpsHost
fn main(http: HttpsAllow("evil.attacker.test", allows: [pii])) : Int
  _ = http
  0
end
"#,
            Some(strict_policy),
            &[
                DiagCode::PrivacyError,
                DiagCode::PolicyError,
                DiagCode::CapabilityError,
            ],
        )?;
        // (e2) path traversal export prefix with sensitive allows rejected even when prefix allows pii
        assert_compile_rejected(
            "policy_export_path_traversal",
            r#"
module PolExportTrav
fn main(out: WriteFiles("reports/../secret/", allows: [pii])) : Int
  _ = out
  0
end
"#,
            Some("version 1\nallow export \"reports/\" tags [pii]\n"),
            &[
                DiagCode::PrivacyError,
                DiagCode::PolicyError,
                DiagCode::CapabilityError,
            ],
        )?;
        // (f) allow write Analytics.summary tags [] rejects WriteTable(..., allows: [pii])
        assert_compile_rejected(
            "policy_write_table_ceiling",
            r#"
module PolWriteTable
fn main(w: WriteTable(Analytics, "summary", allows: [pii])) : Int
  _ = w
  0
end
"#,
            Some(strict_policy),
            &[DiagCode::PrivacyError, DiagCode::PolicyError],
        )?;
        verified_boundaries += 1;
    }

    // -----------------------------------------------------------------------
    // B8. Tampered / unpinned `vendor/` modules, `use Vendor.*` bypass, & ambient capability rejection
    // -----------------------------------------------------------------------
    {
        let tmp = TempDir::new("vendor_redteam")?;
        let vdir = tmp.path().join("vendor");
        fs::create_dir_all(&vdir)?;
        let helper_path = vdir.join("helper.dana");
        fs::write(
            &helper_path,
            "module Helper\n\nfn clean(x: Int) : Int\n  x + 1\nend\n",
        )?;
        let _ = pin_vendor_dir(&vdir)?;
        assert!(verify_vendor_dir(&vdir).is_ok());

        let app_path = tmp.path().join("app.dana");
        fs::write(
            &app_path,
            "module App\nuse Helper\nfn main() : Int\n  Helper.clean(41)\nend\n",
        )?;

        // (a) Unpinned extra file in vendor/ fails verify_vendor_dir
        let rogue_path = vdir.join("rogue.dana");
        fs::write(&rogue_path, "module Rogue\nfn bad() : Int\n  1\nend\n")?;
        assert!(
            verify_vendor_dir(&vdir).is_err(),
            "unpinned vendor file must fail verify_vendor_dir"
        );
        fs::remove_file(&rogue_path)?;

        // (b) Tampered byte in pinned module fails both verify_vendor_dir and resolve_path!
        fs::write(
            &helper_path,
            "module Helper\n\nfn clean(x: Int) : Int\n  x + 2\nend\n",
        )?;
        assert!(
            verify_vendor_dir(&vdir).is_err(),
            "tampered vendor file must fail verify_vendor_dir"
        );
        let mut sm_t = SourceMap::new();
        assert!(
            resolve_path(&app_path, None, &mut sm_t).is_err(),
            "tampered vendor file must fail module resolution"
        );

        // (b2) Adversarial `use Vendor.Bypass` prefix-escape attack MUST NOT treat `vendor/bypass.dana`
        // as `ModuleOrigin::Local` to evade `vendor/vendor.lock` SHA-256 verification!
        let bypass_path = vdir.join("bypass.dana");
        fs::write(
            &bypass_path,
            "module Vendor.Bypass\n\nfn main() : Int\n  0\nend\n",
        )?;
        let bypass_app = tmp.path().join("bypass_app.dana");
        fs::write(
            &bypass_app,
            "module BypassApp\nuse Vendor.Bypass\nfn main() : Int\n  0\nend\n",
        )?;
        let mut sm_b = SourceMap::new();
        assert!(
            resolve_path(&bypass_app, None, &mut sm_b).is_err(),
            "unpinned `use Vendor.Bypass` must NEVER bypass vendor.lock verification!"
        );
        // Even after pinning, `Vendor.Bypass` stays `ModuleOrigin::Vendor`, so `fn main` is rejected!
        fs::write(
            &helper_path,
            "module Helper\n\nfn clean(x: Int) : Int\n  x + 1\nend\n",
        )?;
        let _ = pin_vendor_dir(&vdir)?;
        let mut sm_b2 = SourceMap::new();
        let resolved_b = resolve_path(&bypass_app, None, &mut sm_b2).map_err(|ds| {
            ds.iter()
                .map(|d| d.message().to_string())
                .collect::<Vec<_>>()
                .join("; ")
        })?;
        assert!(
            check_resolved(&resolved_b, &sm_b2).is_err(),
            "pinned `use Vendor.Bypass` defining `fn main` must still be rejected as Vendor!"
        );
        fs::remove_file(&bypass_path)?;

        // (c) Vendored module minting ambient capability (`Files.in_memory` / `Https.fake`) is rejected!
        fs::write(
            &helper_path,
            "module Helper\n\nfn steal() : Int\n  _ = Files.in_memory({\"a.txt\": \"x\"})\n  0\nend\n",
        )?;
        let _ = pin_vendor_dir(&vdir)?;
        fs::write(
            &app_path,
            "module App\nuse Helper\nfn main() : Int\n  Helper.steal()\nend\n",
        )?;
        let mut sm_c = SourceMap::new();
        let resolved = resolve_path(&app_path, None, &mut sm_c).map_err(|ds| {
            ds.iter()
                .map(|d| d.message().to_string())
                .collect::<Vec<_>>()
                .join("; ")
        })?;
        match check_resolved(&resolved, &sm_c) {
            Ok(_) => {
                return Err(
                    "vendored module minting ambient Files.in_memory must be statically rejected!"
                        .into(),
                );
            }
            Err(diags) => {
                assert!(
                    diags.iter().any(|d| matches!(
                        d.code(),
                        DiagCode::CapabilityError | DiagCode::PrivacyError | DiagCode::TypeError
                    )),
                    "unexpected diag codes for impure vendor module: {diags:?}"
                );
            }
        }
        verified_boundaries += 1;
    }

    // -----------------------------------------------------------------------
    // B9. SQL injection attempts across ReadDB pushdown, RawReadDB.raw_sql & WriteTable.upsert
    // -----------------------------------------------------------------------
    {
        let tmp = TempDir::new("sqli_redteam")?;
        let db_path = tmp.path().join("sqli.db");
        let uri = format!("sqlite://{}", db_path.display());
        let mut conn = open_connection(&uri)?;
        conn.execute(
            r#"CREATE TABLE "items" ("id" INTEGER PRIMARY KEY NOT NULL, "name" TEXT NOT NULL)"#,
            &[],
        )?;
        conn.execute(
            r#"INSERT INTO "items" ("id", "name") VALUES (?, ?)"#,
            &[SqlParam::Int(1), SqlParam::Text("safe".to_string())],
        )?;
        drop(conn);

        // (a) Static rejection of interpolated SQL and dynamic variable SQL in raw_sql
        assert_compile_rejected(
            "sqli_raw_sql_interpolated",
            r##"
module SqliInterp
schema Item
  id: Int
  name: Text
end
fn main(raw: RawReadDB(Db), evil: Text) : Int
  _ = try raw.raw_sql("SELECT id, name FROM items WHERE name = '#{evil}'", as: Item)
  0
end
"##,
            None,
            &[
                DiagCode::CapabilityError,
                DiagCode::TypeError,
                DiagCode::PrivacyError,
            ],
        )?;
        assert_compile_rejected(
            "sqli_raw_sql_dynamic_var",
            r#"
module SqliDyn
schema Item
  id: Int
  name: Text
end
fn main(raw: RawReadDB(Db), q: Text) : Int
  _ = try raw.raw_sql(q, as: Item)
  0
end
"#,
            None,
            &[
                DiagCode::CapabilityError,
                DiagCode::TypeError,
                DiagCode::PrivacyError,
            ],
        )?;
        // (b) Runtime parameterized SQLi probes on ReadDB pushdown, raw_sql, and WriteTable.upsert
        let sqli_prog = compile_dana_source(
            r#"module SqliRuntime
schema Items
  id: Int
  name: Text
end
fn main(
  db: ReadDB(Db),
  raw: RawReadDB(Db),
  dbw: WriteTable(Db, "items"),
  console: Console
) : Int
  payload = "' OR '1'='1'; DROP TABLE items; --"
  r1 = db.table(Items) |> where(.name == payload)
  r2 = try raw.raw_sql("SELECT id, name FROM items WHERE name = ?", params: [payload], as: Items)
  up = table
    | id | name                                 |
    | 2  | "' OR '1'='1'; DROP TABLE items; --" |
  end
  _ = try dbw.upsert(up, key: .id)
  after = db.table(Items)
  console.print("r1=#{r1.count()} r2=#{r2.count()} after=#{after.count()}")
  0
end
"#,
            None,
        )?;
        let mut db_bindings = HashMap::new();
        db_bindings.insert("Db".to_string(), uri.clone());
        let run_cfg = RunConfig {
            db_bindings,
            ..RunConfig::default()
        };
        let res = run_exec_program_vm(&sqli_prog, &run_cfg, &VmConfig::default());
        match res {
            RunResult::Ok {
                exit_code: 0,
                stdout,
                ..
            } => {
                let joined = stdout.join("\n");
                assert!(
                    joined.contains("r1=0 r2=0 after=2"),
                    "SQLi payload altered query semantics or dropped table: {joined}"
                );
            }
            other => return Err(format!("SQLi runtime test failed: {other:?}").into()),
        }
        verified_boundaries += 1;
    }

    // -----------------------------------------------------------------------
    // B10. HTTPS security boundaries & `--allow-export` bypass denials
    // -----------------------------------------------------------------------
    {
        // Plaintext HTTP, cross-host, userinfo, CRLF injection, and 3xx redirects must ALL fail!
        assert!(ParsedHttpsUrl::parse("http://api.example.com/v1").is_err());
        assert!(
            ParsedHttpsUrl::parse_and_check_host("https://evil.example.com/v1", "api.example.com")
                .is_err()
        );
        assert!(ParsedHttpsUrl::parse("https://user:pass@api.example.com/v1").is_err());
        assert!(ParsedHttpsUrl::parse("https://api.example.com/v1\r\nX-Inject: 1").is_err());
        assert!(
            parse_http_response_from_reader(
                Cursor::new(
                    b"HTTP/1.1 301 Moved Permanently\r\nLocation: https://evil.test/\r\n\r\n"
                ),
                &HttpsConfig::default(),
            )
            .is_err()
        );

        // `--allow-export` runtime gate denial on WriteFiles("out/", allows: [pii]) with 0 files created
        let tmp = TempDir::new("export_gate")?;
        let exp_prog = compile_dana_source(
            r#"module ExportGateTest
schema Row
  ssn: Text [pii]
end
fn main(out: WriteFiles("out/", allows: [pii])) : Int
  rows = table
    | ssn           |
    | "111-22-3333" |
  end
  try out.write_csv("leaked.csv", rows)
  0
end
"#,
            None,
        )?;
        let denied_cfg = RunConfig {
            work_dir: Some(tmp.path().to_path_buf()),
            allow_export: TagSet::empty(),
            ..RunConfig::default()
        };
        for (engine, res) in [
            ("oracle", run_exec_program(&exp_prog, &denied_cfg)),
            (
                "vm",
                run_exec_program_vm(&exp_prog, &denied_cfg, &VmConfig::default()),
            ),
        ] {
            match res {
                RunResult::Stopped { bug, .. } => {
                    assert_eq!(bug.kind, BugKind::ExportGateDenied, "{engine}");
                }
                other => {
                    return Err(
                        format!("{engine}: expected ExportGateDenied, got {other:?}").into(),
                    );
                }
            }
        }
        assert!(
            !tmp.path().join("out/leaked.csv").exists(),
            "denied export created leaked.csv on disk!"
        );
        verified_boundaries += 1;
    }

    // -----------------------------------------------------------------------
    // B11. Runtime `try` on sensitive `Result` redacts `Error(...)` payload on Fail!
    // -----------------------------------------------------------------------
    {
        let try_err_prog = compile_dana_source(
            r#"module TryRedactFail
fn make_secret_err(flag: Bool [pii]) : Result(Int, Text) [pii]
  if flag
    Error("SSN-999-SECRET-LEAK")
  else
    Ok(1)
  end
end
test "try_redact_fail"
  v = try make_secret_err(true)
  assert v == 1
end
"#,
            None,
        )?;
        for (engine, outcomes) in [
            (
                "oracle",
                run_program_tests(&try_err_prog, None, &RunConfig::default()),
            ),
            (
                "vm",
                run_program_tests_vm(
                    &try_err_prog,
                    None,
                    &RunConfig::default(),
                    &VmConfig::default(),
                ),
            ),
        ] {
            assert_eq!(outcomes.len(), 1, "{engine}: expected 1 test outcome");
            let outcome = &outcomes[0];
            assert!(!outcome.passed, "{engine}: expected failing outcome");
            let message = outcome.message.as_deref().unwrap_or("");
            assert!(
                !message.contains("SSN-999-SECRET-LEAK"),
                "{engine}: `try` Fail leaked sensitive Error payload: {message}"
            );
            assert!(
                message.contains("[REDACTED:pii]"),
                "{engine}: expected [REDACTED:pii] in Fail message: {message}"
            );
        }
        verified_boundaries += 1;
    }

    eprintln!(
        "[redteam/03_runtime_boundaries] {verified_boundaries} runtime & system boundary suites passed (0 leaks, 0 bypasses)"
    );
    Ok(())
}
