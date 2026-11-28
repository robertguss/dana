//! Phase 2C Wave 5 — Differential VM Verification Gate.
//!
//! Verifies 100% byte-for-byte `print_report` parity across:
//! 1. **5,040+ generated Core IR v0.1 programs** covering all 21 relational `Plan` verbs,
//!    all 7 `JoinKind`s, all 12 `AggOp`s, all 6 `WindowFn`s, both `SuppressMode`s,
//!    non-recursive bytecode-inlined pure UDFs, recursive fallback pure UDFs, and
//!    intentional stop/trap inputs (`DivByZero`, `IntOverflow`, `DecimalOverflow`,
//!    `UnwrapNone`, `JoinCardinality` with public & redacted `[pii]` keys).
//!    Every program is checked for:
//!    - `check_program(&prog).is_ok()`
//!    - `check_program(&optimize_program(&prog).0).is_ok()`
//!    - `oracle == vm_seq_unopt == vm_seq_opt == vm_par_opt` (with `batch_size = 4`,
//!      `parallel_threshold_rows = 4`, `max_threads = Some(4)`).
//! 2. **Curated Triple-Parity Corpus** (~28 programs) run through Lean 4 `danacore`,
//!    Rust `oracle::run_program`, and Rust `vm::run_core_program_vm` (seq unopt, seq opt,
//!    par opt) asserting 100% byte-for-byte `print_report` agreement.
//! 3. **Optimizer Rewrites, Stop/Cardinality Safety Barriers, and Plan Explainer** tests.
//! 4. **Large Multi-Batch (12,000-row) Parallel vs. Sequential vs. Oracle Parity** test
//!    plus deterministic earliest-row trap ordering across parallel workers.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::OnceLock;
use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};

use dana::core::{
    AggItem, AggKind, AggOp, BigInt, ColSpec, ConstDecl, DEC_MAX, DEC_SCALE, DeriveItem, Expr,
    Float64, FunDecl, FunKind, HostOp, JoinKind, JoinOn, LTy, Literal, Plan, PrimOp, Program,
    RowExpr, RowLit, ScalarTy, SortDir, SuppressMode, TableTy, TagSet, Ty, WindowFn, WindowItem,
    check_program, print_program, print_report,
};
use dana::oracle::{ExitStatus, StoredTable, Val, World, run_program};
use dana::plan::{explain_exec_plan, explain_plan, optimize_plan, optimize_program};
use dana::runtime::ir::{ExecDeriveItem, ExecExpr, ExecPlan, ExecPrimOp, ExecRowExpr};
use dana::vm::{BATCH_SIZE, VmConfig, run_core_program_vm};

// ===========================================================================
// Deterministic SplitMix64 PRNG
// ===========================================================================

struct SplitMix64 {
    state: u64,
}

impl SplitMix64 {
    const fn new(seed: u64) -> Self {
        Self { state: seed }
    }

    fn next_u64(&mut self) -> u64 {
        self.state = self.state.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.state;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    fn gen_range(&mut self, bound: usize) -> usize {
        if bound <= 1 {
            0
        } else {
            (self.next_u64() as usize) % bound
        }
    }

    fn gen_bool(&mut self, num: usize, den: usize) -> bool {
        self.gen_range(den) < num
    }

    fn pick_small_int(&mut self) -> i64 {
        const POOL: &[i64] = &[-10, -5, -2, -1, 0, 1, 2, 3, 5, 7, 10, 15, 25, 42, 100];
        POOL[self.gen_range(POOL.len())]
    }

    fn pick_dec_scaled(&mut self) -> i128 {
        const POOL: &[i128] = &[
            -25 * DEC_SCALE,
            -3 * DEC_SCALE,
            -DEC_SCALE / 2,
            0,
            DEC_SCALE / 4,
            DEC_SCALE,
            5 * DEC_SCALE,
            12 * DEC_SCALE + DEC_SCALE / 2,
            50 * DEC_SCALE,
        ];
        POOL[self.gen_range(POOL.len())]
    }

    fn pick_float(&mut self) -> Float64 {
        const POOL: &[f64] = &[
            -12.5,
            -1.0,
            -0.0,
            0.0,
            0.5,
            1.0,
            2.5,
            10.0,
            42.25,
            100.0,
            f64::INFINITY,
            f64::NEG_INFINITY,
            f64::NAN,
        ];
        Float64::from_f64(POOL[self.gen_range(POOL.len())])
    }

    fn pick_group(&mut self) -> String {
        const POOL: &[&str] = &["A", "B", "C", "D"];
        POOL[self.gen_range(POOL.len())].to_string()
    }

    fn pick_text(&mut self) -> String {
        const POOL: &[&str] = &[
            "alpha",
            "beta",
            "gamma",
            "delta",
            "  MiXeD ",
            "josé@uni.edu",
            "",
        ];
        POOL[self.gen_range(POOL.len())].to_string()
    }
}

// ===========================================================================
// Shared Core IR Builder Helpers
// ===========================================================================

fn ts(tags: &[&str]) -> TagSet {
    TagSet::of_list(tags.iter().map(|s| (*s).to_string()).collect())
}

fn col(name: &str, ty: ScalarTy, tags: TagSet) -> ColSpec {
    ColSpec {
        name: name.to_string(),
        ty,
        tags,
        bucketed: false,
        agg_kind: AggKind::Raw,
    }
}

fn print_table(plan: Plan) -> Expr {
    Expr::Host {
        op: HostOp::ConsolePrintTable,
        args: vec![Expr::Var("c".into()), Expr::Rel(Box::new(plan))],
    }
}

fn let_seq(name: &str, lty: LTy, bound: Expr, body: Expr) -> Expr {
    Expr::LetE {
        name: name.into(),
        lty,
        bound: Box::new(bound),
        body: Box::new(body),
    }
}

fn mk_console_prog(body: Expr) -> Program {
    mk_console_prog_with(vec![], vec![], TagSet::empty(), body)
}

fn mk_console_prog_with(
    consts: Vec<ConstDecl>,
    extra_funs: Vec<FunDecl>,
    console_allows: TagSet,
    body: Expr,
) -> Program {
    let mut funs = extra_funs;
    funs.push(FunDecl {
        name: "main".into(),
        kind: FunKind::Function,
        is_pure: false,
        params: vec![("c".into(), LTy::public(Ty::Console(console_allows)))],
        pc: TagSet::empty(),
        ret: LTy::public(Ty::Unit),
        body,
    });
    Program {
        consts,
        funs,
        entry: Some("main".into()),
        ..Program::default()
    }
}

fn pure_udf_non_recursive_funs() -> Vec<FunDecl> {
    vec![
        // helper(a: Int) : Int = a * 2 + 1
        FunDecl {
            name: "helper_mul".into(),
            kind: FunKind::Function,
            is_pure: true,
            params: vec![("a".into(), LTy::public(Ty::Int))],
            pc: TagSet::empty(),
            ret: LTy::public(Ty::Int),
            body: Expr::Prim {
                op: PrimOp::AddInt,
                args: vec![
                    Expr::Prim {
                        op: PrimOp::MulInt,
                        args: vec![Expr::Var("a".into()), Expr::Lit(Literal::int(2))],
                    },
                    Expr::Lit(Literal::int(1)),
                ],
            },
        },
        // score_udf(x: Int, y: Int?) : Int =
        //   let base = unwrapOr(y, 3) in
        //   if x > 0 then helper_mul(x) + base else base - x
        FunDecl {
            name: "score_udf".into(),
            kind: FunKind::Function,
            is_pure: true,
            params: vec![
                ("x".into(), LTy::public(Ty::Int)),
                ("y".into(), LTy::public(Ty::Option(Box::new(Ty::Int)))),
            ],
            pc: TagSet::empty(),
            ret: LTy::public(Ty::Int),
            body: let_seq(
                "base",
                LTy::public(Ty::Int),
                Expr::Prim {
                    op: PrimOp::UnwrapOr,
                    args: vec![Expr::Var("y".into()), Expr::Lit(Literal::int(3))],
                },
                Expr::IfE {
                    cond: Box::new(Expr::Prim {
                        op: PrimOp::Gt,
                        args: vec![Expr::Var("x".into()), Expr::Lit(Literal::int(0))],
                    }),
                    then_br: Box::new(Expr::Prim {
                        op: PrimOp::AddInt,
                        args: vec![
                            Expr::Call {
                                fn_name: "helper_mul".into(),
                                args: vec![Expr::Var("x".into())],
                            },
                            Expr::Var("base".into()),
                        ],
                    }),
                    else_br: Box::new(Expr::Prim {
                        op: PrimOp::SubInt,
                        args: vec![Expr::Var("base".into()), Expr::Var("x".into())],
                    }),
                },
            ),
        },
        // net_dec_udf(amt: Decimal, rate: Decimal) : Decimal =
        //   let prod = amt * rate in
        //   if amt > 5.0 then prod - 1.0 else prod + 0.5
        FunDecl {
            name: "net_dec_udf".into(),
            kind: FunKind::Function,
            is_pure: true,
            params: vec![
                ("amt".into(), LTy::public(Ty::Decimal)),
                ("rate".into(), LTy::public(Ty::Decimal)),
            ],
            pc: TagSet::empty(),
            ret: LTy::public(Ty::Decimal),
            body: let_seq(
                "prod",
                LTy::public(Ty::Decimal),
                Expr::Prim {
                    op: PrimOp::MulDec,
                    args: vec![Expr::Var("amt".into()), Expr::Var("rate".into())],
                },
                Expr::IfE {
                    cond: Box::new(Expr::Prim {
                        op: PrimOp::Gt,
                        args: vec![
                            Expr::Var("amt".into()),
                            Expr::Lit(Literal::decimal(5 * DEC_SCALE)),
                        ],
                    }),
                    then_br: Box::new(Expr::Prim {
                        op: PrimOp::SubDec,
                        args: vec![
                            Expr::Var("prod".into()),
                            Expr::Lit(Literal::decimal(DEC_SCALE)),
                        ],
                    }),
                    else_br: Box::new(Expr::Prim {
                        op: PrimOp::AddDec,
                        args: vec![
                            Expr::Var("prod".into()),
                            Expr::Lit(Literal::decimal(DEC_SCALE / 2)),
                        ],
                    }),
                },
            ),
        },
        // trap_div_udf(x: Int, d: Int) : Int =
        //   if x < 0 then 0 else x / d   (conditional DivByZero when x >= 0 && d == 0!)
        FunDecl {
            name: "trap_div_udf".into(),
            kind: FunKind::Function,
            is_pure: true,
            params: vec![
                ("x".into(), LTy::public(Ty::Int)),
                ("d".into(), LTy::public(Ty::Int)),
            ],
            pc: TagSet::empty(),
            ret: LTy::public(Ty::Int),
            body: Expr::IfE {
                cond: Box::new(Expr::Prim {
                    op: PrimOp::Lt,
                    args: vec![Expr::Var("x".into()), Expr::Lit(Literal::int(0))],
                }),
                then_br: Box::new(Expr::Lit(Literal::int(0))),
                else_br: Box::new(Expr::Prim {
                    op: PrimOp::DivInt,
                    args: vec![Expr::Var("x".into()), Expr::Var("d".into())],
                }),
            },
        },
        // unwrap_udf(opt: Int?) : Int = unwrapBang(opt) + 1
        FunDecl {
            name: "unwrap_udf".into(),
            kind: FunKind::Function,
            is_pure: true,
            params: vec![("opt".into(), LTy::public(Ty::Option(Box::new(Ty::Int))))],
            pc: TagSet::empty(),
            ret: LTy::public(Ty::Int),
            body: Expr::Prim {
                op: PrimOp::AddInt,
                args: vec![
                    Expr::Prim {
                        op: PrimOp::UnwrapBang,
                        args: vec![Expr::Var("opt".into())],
                    },
                    Expr::Lit(Literal::int(1)),
                ],
            },
        },
    ]
}

fn pure_udf_recursive_funs() -> Vec<FunDecl> {
    vec![
        // rec_tri(n: Int) : Int = if n <= 0 then 0 else n + rec_tri(n - 1)
        FunDecl {
            name: "rec_tri".into(),
            kind: FunKind::Function,
            is_pure: true,
            params: vec![("n".into(), LTy::public(Ty::Int))],
            pc: TagSet::empty(),
            ret: LTy::public(Ty::Int),
            body: Expr::IfE {
                cond: Box::new(Expr::Prim {
                    op: PrimOp::Le,
                    args: vec![Expr::Var("n".into()), Expr::Lit(Literal::int(0))],
                }),
                then_br: Box::new(Expr::Lit(Literal::int(0))),
                else_br: Box::new(Expr::Prim {
                    op: PrimOp::AddInt,
                    args: vec![
                        Expr::Var("n".into()),
                        Expr::Call {
                            fn_name: "rec_tri".into(),
                            args: vec![Expr::Prim {
                                op: PrimOp::SubInt,
                                args: vec![Expr::Var("n".into()), Expr::Lit(Literal::int(1))],
                            }],
                        },
                    ],
                }),
            },
        },
        // rec_trap(n: Int) : Int = if n <= 0 then 1 / n else n + rec_trap(n - 1)
        FunDecl {
            name: "rec_trap".into(),
            kind: FunKind::Function,
            is_pure: true,
            params: vec![("n".into(), LTy::public(Ty::Int))],
            pc: TagSet::empty(),
            ret: LTy::public(Ty::Int),
            body: Expr::IfE {
                cond: Box::new(Expr::Prim {
                    op: PrimOp::Le,
                    args: vec![Expr::Var("n".into()), Expr::Lit(Literal::int(0))],
                }),
                then_br: Box::new(Expr::Prim {
                    op: PrimOp::DivInt,
                    args: vec![Expr::Lit(Literal::int(1)), Expr::Var("n".into())],
                }),
                else_br: Box::new(Expr::Prim {
                    op: PrimOp::AddInt,
                    args: vec![
                        Expr::Var("n".into()),
                        Expr::Call {
                            fn_name: "rec_trap".into(),
                            args: vec![Expr::Prim {
                                op: PrimOp::SubInt,
                                args: vec![Expr::Var("n".into()), Expr::Lit(Literal::int(1))],
                            }],
                        },
                    ],
                }),
            },
        },
    ]
}

fn raw_table_schema() -> TableTy {
    TableTy {
        cols: vec![
            col("id", ScalarTy::Int, TagSet::empty()),
            col("g", ScalarTy::Text, TagSet::empty()),
            col("x", ScalarTy::Int, TagSet::empty()),
            col("d", ScalarTy::Decimal, TagSet::empty()),
            col("f", ScalarTy::Float, TagSet::empty()),
            col("has_opt", ScalarTy::Bool, TagSet::empty()),
            col("opt_raw", ScalarTy::Int, TagSet::empty()),
        ],
        ..TableTy::default()
    }
}

fn base_table_schema() -> TableTy {
    TableTy {
        cols: vec![
            col("id", ScalarTy::Int, TagSet::empty()),
            col("g", ScalarTy::Text, TagSet::empty()),
            col("x", ScalarTy::Int, TagSet::empty()),
            col("d", ScalarTy::Decimal, TagSet::empty()),
            col("f", ScalarTy::Float, TagSet::empty()),
            col(
                "opt",
                ScalarTy::Option(Box::new(ScalarTy::Int)),
                TagSet::empty(),
            ),
        ],
        ..TableTy::default()
    }
}

/// Build a base relational plan producing columns `(id, g, x, d, f, opt: Int?)`
/// with genuine mixed `Some(Int)` and `None` values in `opt`!
fn gen_base_table_plan(rng: &mut SplitMix64, min_rows: usize, max_rows: usize) -> Plan {
    let span = max_rows.saturating_sub(min_rows) + 1;
    let n = min_rows + rng.gen_range(span);
    let mut rows = Vec::with_capacity(n);
    for i in 0..n {
        rows.push(RowLit {
            cells: vec![
                Literal::int((i as i64) + 1),
                Literal::Text(rng.pick_group()),
                Literal::int(rng.pick_small_int()),
                Literal::decimal(rng.pick_dec_scaled()),
                Literal::Float(rng.pick_float()),
                Literal::Bool(rng.gen_bool(2, 3)),
                Literal::int(rng.pick_small_int()),
            ],
        });
    }
    let raw = Expr::TableLit {
        schema: raw_table_schema(),
        rows,
    };
    Plan::Drop {
        input: Box::new(Plan::Derive {
            input: Box::new(Plan::SourceExpr(Box::new(raw))),
            items: vec![DeriveItem::ColExpr {
                name: "opt".into(),
                expr: Box::new(RowExpr::IfE {
                    cond: Box::new(RowExpr::Col("has_opt".into())),
                    then_br: Box::new(RowExpr::Prim {
                        op: PrimOp::SomeVal(Ty::Int),
                        args: vec![RowExpr::Col("opt_raw".into())],
                    }),
                    else_br: Box::new(RowExpr::Lit(Literal::NoneLit(Ty::Int))),
                }),
            }],
        }),
        cols: vec!["has_opt".into(), "opt_raw".into()],
    }
}

// ===========================================================================
// 5,040-Case Deterministic Core IR Pipeline Generator
// ===========================================================================

fn gen_core_pipeline_case(rng: &mut SplitMix64, idx: usize) -> (Program, World) {
    let family = idx % 14;
    match family {
        // Family 0: Select / Drop / Rename / Filter (chained) / Derive (ColExpr + BucketCol) /
        //           Distinct / Sort / Limit (including nested Limit) + OuterVar + ConstRef
        0 => {
            let mut plan = gen_base_table_plan(rng, 5, 16);
            let thresh = rng.pick_small_int();
            plan = Plan::Filter {
                input: Box::new(plan),
                pred: RowExpr::Prim {
                    op: PrimOp::Ge,
                    args: vec![RowExpr::Col("x".into()), RowExpr::OuterVar("min_x".into())],
                },
            };
            plan = Plan::Filter {
                input: Box::new(plan),
                pred: RowExpr::Prim {
                    op: PrimOp::Ne,
                    args: vec![
                        RowExpr::Col("g".into()),
                        RowExpr::Lit(Literal::Text("Z".into())),
                    ],
                },
            };
            plan = Plan::Derive {
                input: Box::new(plan),
                items: vec![
                    DeriveItem::ColExpr {
                        name: "score".into(),
                        expr: Box::new(RowExpr::Prim {
                            op: PrimOp::AddInt,
                            args: vec![
                                RowExpr::Col("x".into()),
                                RowExpr::Coalesce {
                                    opt_expr: Box::new(RowExpr::Col("opt".into())),
                                    default_expr: Box::new(RowExpr::ConstRef("K_DEF".into())),
                                },
                            ],
                        }),
                    },
                    DeriveItem::BucketCol {
                        name: "tier".into(),
                        source: "x".into(),
                        cuts: vec![Literal::int(0), Literal::int(10)],
                        labels: vec!["neg".into(), "mid".into(), "high".into()],
                    },
                ],
            };
            if rng.gen_bool(1, 2) {
                plan = Plan::Drop {
                    input: Box::new(plan),
                    cols: vec!["f".into()],
                };
            }
            if rng.gen_bool(2, 3) {
                plan = Plan::Rename {
                    input: Box::new(plan),
                    pairs: vec![("grp".into(), "g".into()), ("val_x".into(), "x".into())],
                };
                if rng.gen_bool(1, 2) {
                    plan = Plan::Filter {
                        input: Box::new(plan),
                        pred: RowExpr::Prim {
                            op: PrimOp::Gt,
                            args: vec![
                                RowExpr::Col("val_x".into()),
                                RowExpr::Lit(Literal::int(-50)),
                            ],
                        },
                    };
                }
                plan = Plan::Select {
                    input: Box::new(plan),
                    cols: vec!["grp".into(), "val_x".into(), "score".into(), "tier".into()],
                };
                if rng.gen_bool(1, 2) {
                    plan = Plan::Distinct {
                        input: Box::new(plan),
                        cols: vec!["grp".into(), "tier".into()],
                    };
                }
                let dir1 = if rng.gen_bool(1, 2) {
                    SortDir::Asc
                } else {
                    SortDir::Desc
                };
                let dir2 = if rng.gen_bool(1, 2) {
                    SortDir::Asc
                } else {
                    SortDir::Desc
                };
                plan = Plan::Sort {
                    input: Box::new(plan),
                    keys: vec![("grp".into(), dir1), ("score".into(), dir2)],
                };
            } else {
                plan = Plan::Sort {
                    input: Box::new(plan),
                    keys: vec![("id".into(), SortDir::Desc)],
                };
            }
            if rng.gen_bool(2, 3) {
                let lim1 = (rng.gen_range(12) + 2) as u64;
                plan = Plan::Limit {
                    input: Box::new(plan),
                    n: BigInt::from(lim1),
                };
                if rng.gen_bool(1, 2) {
                    let lim2 = (rng.gen_range(8) + 1) as u64;
                    plan = Plan::Limit {
                        input: Box::new(plan),
                        n: BigInt::from(lim2),
                    };
                }
            }
            let body = let_seq(
                "min_x",
                LTy::public(Ty::Int),
                Expr::Lit(Literal::int(thresh)),
                print_table(plan),
            );
            let consts = vec![ConstDecl {
                name: "K_DEF".into(),
                lty: LTy::public(Ty::Int),
                value: Literal::int(rng.pick_small_int()),
            }];
            (
                mk_console_prog_with(consts, vec![], TagSet::empty(), body),
                World::default(),
            )
        }

        // Family 1: Non-recursive pure UDFs (bytecode inlining) in Filter, Derive, Summarize + traps
        1 => {
            let base = gen_base_table_plan(rng, 6, 16);
            let mode = rng.gen_range(5);
            let plan = match mode {
                0 => {
                    // UDF in Filter + Derive + Decimal UDF + Sort
                    let p1 = Plan::Filter {
                        input: Box::new(base),
                        pred: RowExpr::Prim {
                            op: PrimOp::Gt,
                            args: vec![
                                RowExpr::CallPure {
                                    fn_name: "score_udf".into(),
                                    args: vec![
                                        RowExpr::Col("x".into()),
                                        RowExpr::Col("opt".into()),
                                    ],
                                },
                                RowExpr::Lit(Literal::int(5)),
                            ],
                        },
                    };
                    let p2 = Plan::Derive {
                        input: Box::new(p1),
                        items: vec![
                            DeriveItem::ColExpr {
                                name: "sc".into(),
                                expr: Box::new(RowExpr::CallPure {
                                    fn_name: "score_udf".into(),
                                    args: vec![
                                        RowExpr::Col("x".into()),
                                        RowExpr::Col("opt".into()),
                                    ],
                                }),
                            },
                            DeriveItem::ColExpr {
                                name: "net".into(),
                                expr: Box::new(RowExpr::CallPure {
                                    fn_name: "net_dec_udf".into(),
                                    args: vec![
                                        RowExpr::Col("d".into()),
                                        RowExpr::Lit(Literal::decimal(DEC_SCALE / 10)),
                                    ],
                                }),
                            },
                        ],
                    };
                    Plan::Sort {
                        input: Box::new(p2),
                        keys: vec![("id".into(), SortDir::Asc)],
                    }
                }
                1 => {
                    // Non-recursive UDF inside Summarize arg!
                    Plan::Summarize {
                        input: Box::new(Plan::GroupBy {
                            input: Box::new(base),
                            keys: vec!["g".into()],
                        }),
                        aggs: vec![
                            AggItem {
                                name: "sum_sc".into(),
                                op: AggOp::Sum,
                                arg: Some(RowExpr::CallPure {
                                    fn_name: "score_udf".into(),
                                    args: vec![
                                        RowExpr::Col("x".into()),
                                        RowExpr::Col("opt".into()),
                                    ],
                                }),
                            },
                            AggItem {
                                name: "sum_net".into(),
                                op: AggOp::Sum,
                                arg: Some(RowExpr::CallPure {
                                    fn_name: "net_dec_udf".into(),
                                    args: vec![
                                        RowExpr::Col("d".into()),
                                        RowExpr::Lit(Literal::decimal(DEC_SCALE / 5)),
                                    ],
                                }),
                            },
                        ],
                        distinct_key: None,
                    }
                }
                2 => {
                    // Conditional DivByZero trap inside inlined UDF (sometimes traps, sometimes avoids!)
                    let denom = if rng.gen_bool(1, 2) { 0 } else { 2 };
                    Plan::Derive {
                        input: Box::new(base),
                        items: vec![DeriveItem::ColExpr {
                            name: "q".into(),
                            expr: Box::new(RowExpr::CallPure {
                                fn_name: "trap_div_udf".into(),
                                args: vec![
                                    RowExpr::Col("x".into()),
                                    RowExpr::Lit(Literal::int(denom)),
                                ],
                            }),
                        }],
                    }
                }
                3 => {
                    // UnwrapNone trap inside inlined UDF (in Filter or Derive)
                    if rng.gen_bool(1, 2) {
                        Plan::Derive {
                            input: Box::new(base),
                            items: vec![DeriveItem::ColExpr {
                                name: "u".into(),
                                expr: Box::new(RowExpr::CallPure {
                                    fn_name: "unwrap_udf".into(),
                                    args: vec![RowExpr::Col("opt".into())],
                                }),
                            }],
                        }
                    } else {
                        Plan::Filter {
                            input: Box::new(base),
                            pred: RowExpr::Prim {
                                op: PrimOp::Gt,
                                args: vec![
                                    RowExpr::CallPure {
                                        fn_name: "unwrap_udf".into(),
                                        args: vec![RowExpr::Col("opt".into())],
                                    },
                                    RowExpr::Lit(Literal::int(0)),
                                ],
                            },
                        }
                    }
                }
                _ => {
                    // Guarded Option unwrap (`if isSome(opt) then unwrap_udf(opt) else -1`)
                    Plan::Derive {
                        input: Box::new(base),
                        items: vec![DeriveItem::ColExpr {
                            name: "safe_u".into(),
                            expr: Box::new(RowExpr::IfE {
                                cond: Box::new(RowExpr::Prim {
                                    op: PrimOp::IsSome,
                                    args: vec![RowExpr::Col("opt".into())],
                                }),
                                then_br: Box::new(RowExpr::CallPure {
                                    fn_name: "unwrap_udf".into(),
                                    args: vec![RowExpr::Col("opt".into())],
                                }),
                                else_br: Box::new(RowExpr::Lit(Literal::int(-1))),
                            }),
                        }],
                    }
                }
            };
            (
                mk_console_prog_with(
                    vec![],
                    pure_udf_non_recursive_funs(),
                    TagSet::empty(),
                    print_table(plan),
                ),
                World::default(),
            )
        }

        // Family 2: Recursive pure UDFs (RowEvalHost::call_pure_fallback) in Filter, Derive, Summarize
        2 => {
            let schema = TableTy {
                cols: vec![
                    col("id", ScalarTy::Int, TagSet::empty()),
                    col("g", ScalarTy::Text, TagSet::empty()),
                    col("n", ScalarTy::Int, TagSet::empty()),
                ],
                ..TableTy::default()
            };
            let nrows = 5 + rng.gen_range(9);
            let rows: Vec<RowLit> = (0..nrows)
                .map(|i| RowLit {
                    cells: vec![
                        Literal::int(i as i64),
                        Literal::Text(rng.pick_group()),
                        Literal::int((rng.gen_range(7) as i64) - 1), // -1..=5
                    ],
                })
                .collect();
            let tbl = Expr::TableLit { schema, rows };
            let plan = match rng.gen_range(4) {
                0 => Plan::Derive {
                    input: Box::new(Plan::SourceExpr(Box::new(tbl))),
                    items: vec![DeriveItem::ColExpr {
                        name: "tri".into(),
                        expr: Box::new(RowExpr::CallPure {
                            fn_name: "rec_tri".into(),
                            args: vec![RowExpr::Col("n".into())],
                        }),
                    }],
                },
                1 => Plan::Filter {
                    input: Box::new(Plan::SourceExpr(Box::new(tbl))),
                    pred: RowExpr::Prim {
                        op: PrimOp::Ge,
                        args: vec![
                            RowExpr::CallPure {
                                fn_name: "rec_tri".into(),
                                args: vec![RowExpr::Col("n".into())],
                            },
                            RowExpr::Lit(Literal::int(3)),
                        ],
                    },
                },
                2 => Plan::Summarize {
                    input: Box::new(Plan::GroupBy {
                        input: Box::new(Plan::SourceExpr(Box::new(tbl))),
                        keys: vec!["g".into()],
                    }),
                    aggs: vec![AggItem {
                        name: "s_tri".into(),
                        op: AggOp::Sum,
                        arg: Some(RowExpr::CallPure {
                            fn_name: "rec_tri".into(),
                            args: vec![RowExpr::Col("n".into())],
                        }),
                    }],
                    distinct_key: None,
                },
                _ => {
                    // Recursive trapping UDF (div by zero when n hits 0!)
                    Plan::Derive {
                        input: Box::new(Plan::SourceExpr(Box::new(tbl))),
                        items: vec![DeriveItem::ColExpr {
                            name: "boom".into(),
                            expr: Box::new(RowExpr::CallPure {
                                fn_name: "rec_trap".into(),
                                args: vec![RowExpr::Col("n".into())],
                            }),
                        }],
                    }
                }
            };
            (
                mk_console_prog_with(
                    vec![],
                    pure_udf_recursive_funs(),
                    TagSet::empty(),
                    print_table(plan),
                ),
                World::default(),
            )
        }

        // Family 3: All 7 JoinKinds + Pairs/SameKeys + suffixes + tagged & public duplicate-key traps
        3 => {
            let key_tags = if rng.gen_bool(1, 3) {
                ts(&["pii"])
            } else {
                TagSet::empty()
            };
            let l_schema = TableTy {
                cols: vec![
                    col("id", ScalarTy::Int, key_tags.clone()),
                    col("lv", ScalarTy::Int, TagSet::empty()),
                    col("tag_c", ScalarTy::Text, TagSet::empty()),
                ],
                ..TableTy::default()
            };
            let r_key_name = if rng.gen_bool(2, 3) { "id" } else { "rid" };
            let r_schema = TableTy {
                cols: vec![
                    col(r_key_name, ScalarTy::Int, key_tags.clone()),
                    col("rv", ScalarTy::Int, TagSet::empty()),
                    col("tag_c", ScalarTy::Text, TagSet::empty()),
                ],
                ..TableTy::default()
            };
            let kind = match rng.gen_range(7) {
                0 => JoinKind::InnerOne,
                1 => JoinKind::InnerManyToOne,
                2 => JoinKind::InnerMany,
                3 => JoinKind::LeftOne,
                4 => JoinKind::LeftManyToOne,
                5 => JoinKind::Semi,
                _ => JoinKind::Anti,
            };
            let ln = 5 + rng.gen_range(10);
            let rn = 4 + rng.gen_range(8);
            let force_l_unique = rng.gen_bool(2, 3);
            let force_r_unique = rng.gen_bool(2, 3);
            let l_rows: Vec<RowLit> = (0..ln)
                .map(|i| {
                    let k = if force_l_unique {
                        i as i64
                    } else {
                        (rng.gen_range(5)) as i64
                    };
                    RowLit {
                        cells: vec![
                            Literal::int(k),
                            Literal::int(rng.pick_small_int()),
                            Literal::Text(rng.pick_group()),
                        ],
                    }
                })
                .collect();
            let r_rows: Vec<RowLit> = (0..rn)
                .map(|i| {
                    let k = if force_r_unique {
                        (i * 2) as i64
                    } else {
                        (rng.gen_range(5)) as i64
                    };
                    RowLit {
                        cells: vec![
                            Literal::int(k),
                            Literal::int(rng.pick_small_int()),
                            Literal::Text(rng.pick_group()),
                        ],
                    }
                })
                .collect();
            let on = if r_key_name == "id" && rng.gen_bool(2, 3) {
                JoinOn::SameKeys(vec!["id".into()])
            } else {
                JoinOn::Pairs(vec![("id".into(), r_key_name.into())])
            };
            let suffixes = if matches!(kind, JoinKind::Semi | JoinKind::Anti) {
                None
            } else {
                Some(("_l".into(), "_r".into()))
            };
            let id_col = if matches!(on, JoinOn::Pairs(_))
                && r_key_name == "id"
                && !matches!(kind, JoinKind::Semi | JoinKind::Anti)
            {
                "id_l"
            } else {
                "id"
            };
            let mut plan = Plan::Join {
                kind,
                left: Box::new(Plan::SourceExpr(Box::new(Expr::TableLit {
                    schema: l_schema,
                    rows: l_rows,
                }))),
                right: Box::new(Plan::SourceExpr(Box::new(Expr::TableLit {
                    schema: r_schema,
                    rows: r_rows,
                }))),
                on,
                suffixes,
            };
            if rng.gen_bool(1, 2) {
                let pred = match rng.gen_range(3) {
                    0 => RowExpr::Prim {
                        op: PrimOp::Ge,
                        args: vec![RowExpr::Col("lv".into()), RowExpr::Lit(Literal::int(0))],
                    },
                    1 => RowExpr::Prim {
                        op: PrimOp::Ge,
                        args: vec![RowExpr::Col(id_col.into()), RowExpr::Lit(Literal::int(1))],
                    },
                    _ => match kind {
                        JoinKind::InnerOne | JoinKind::InnerManyToOne | JoinKind::InnerMany => {
                            RowExpr::Prim {
                                op: PrimOp::Gt,
                                args: vec![
                                    RowExpr::Col("rv".into()),
                                    RowExpr::Lit(Literal::int(-5)),
                                ],
                            }
                        }
                        JoinKind::LeftOne | JoinKind::LeftManyToOne => RowExpr::Prim {
                            op: PrimOp::IsSome,
                            args: vec![RowExpr::Col("rv".into())],
                        },
                        JoinKind::Semi | JoinKind::Anti => RowExpr::Prim {
                            op: PrimOp::Ne,
                            args: vec![
                                RowExpr::Col("tag_c".into()),
                                RowExpr::Lit(Literal::Text("D".into())),
                            ],
                        },
                    },
                };
                plan = Plan::Filter {
                    input: Box::new(plan),
                    pred,
                };
            }
            let world = World {
                runtime_allow_export: key_tags.clone(),
                ..World::default()
            };
            (
                mk_console_prog_with(vec![], vec![], key_tags, print_table(plan)),
                world,
            )
        }

        // Family 4: Union + Filter pushdown + Distinct + Sort + Limit
        4 => {
            let p1 = gen_base_table_plan(rng, 4, 10);
            let p2 = gen_base_table_plan(rng, 4, 10);
            let mut plan = Plan::Union {
                left: Box::new(p1),
                right: Box::new(p2),
            };
            plan = Plan::Filter {
                input: Box::new(plan),
                pred: RowExpr::Prim {
                    op: PrimOp::Ge,
                    args: vec![RowExpr::Col("x".into()), RowExpr::Lit(Literal::int(-2))],
                },
            };
            if rng.gen_bool(1, 2) {
                plan = Plan::Distinct {
                    input: Box::new(plan),
                    cols: vec!["g".into(), "x".into()],
                };
            }
            plan = Plan::Sort {
                input: Box::new(plan),
                keys: vec![
                    ("g".into(), SortDir::Asc),
                    ("x".into(), SortDir::Desc),
                    ("id".into(), SortDir::Asc),
                ],
            };
            if rng.gen_bool(1, 2) {
                plan = Plan::Limit {
                    input: Box::new(plan),
                    n: BigInt::from((rng.gen_range(10) + 1) as u64),
                };
            }
            (mk_console_prog(print_table(plan)), World::default())
        }

        // Family 5: GroupBy + Summarize across all 12 AggOps + empty tables + distinct_key
        5 => {
            let empty_case = rng.gen_bool(1, 6);
            let src_plan = if empty_case {
                Plan::SourceExpr(Box::new(Expr::TableLit {
                    schema: base_table_schema(),
                    rows: vec![],
                }))
            } else {
                gen_base_table_plan(rng, 5, 18)
            };
            let grouped = rng.gen_bool(3, 4);
            let input_plan = if grouped {
                Plan::GroupBy {
                    input: Box::new(src_plan),
                    keys: vec!["g".into()],
                }
            } else {
                src_plan
            };
            let agg_pool = [
                AggOp::Count,
                AggOp::CountDistinct,
                AggOp::Sum,
                AggOp::Mean,
                AggOp::Stddev,
                AggOp::Variance,
                AggOp::Median,
                AggOp::Percentile(Float64::from_f64(
                    [0.0, 0.25, 0.5, 0.75, 1.0][rng.gen_range(5)],
                )),
                AggOp::Min,
                AggOp::Max,
                AggOp::First,
                AggOp::Last,
            ];
            let n_aggs = 2 + rng.gen_range(5);
            let mut aggs = Vec::with_capacity(n_aggs);
            for ai in 0..n_aggs {
                let op = agg_pool[rng.gen_range(agg_pool.len())];
                let arg = match op {
                    AggOp::Count => None,
                    AggOp::CountDistinct | AggOp::Min | AggOp::Max | AggOp::First | AggOp::Last => {
                        let col_name = ["x", "d", "f", "opt"][rng.gen_range(4)];
                        Some(RowExpr::Col(col_name.into()))
                    }
                    AggOp::Sum
                    | AggOp::Mean
                    | AggOp::Median
                    | AggOp::Stddev
                    | AggOp::Variance
                    | AggOp::Percentile(_) => {
                        let col_name = ["x", "d", "f", "opt"][rng.gen_range(4)];
                        Some(RowExpr::Col(col_name.into()))
                    }
                };
                aggs.push(AggItem {
                    name: format!("a{ai}"),
                    op,
                    arg,
                });
            }
            let plan = Plan::Summarize {
                input: Box::new(input_plan),
                aggs,
                distinct_key: if grouped && rng.gen_bool(1, 2) {
                    Some("id".into())
                } else {
                    None
                },
            };
            (mk_console_prog(print_table(plan)), World::default())
        }

        // Family 6: Summarize Int/Decimal overflow traps + trapping agg args across multiple groups
        6 => {
            let kind = rng.gen_range(4);
            let plan = match kind {
                0 => {
                    // Int sum overflow (including right-fold sorted sum order!)
                    let schema = TableTy {
                        cols: vec![
                            col("g", ScalarTy::Text, TagSet::empty()),
                            col("x", ScalarTy::Int, TagSet::empty()),
                        ],
                        ..TableTy::default()
                    };
                    let rows = vec![
                        RowLit {
                            cells: vec![Literal::Text("B".into()), Literal::int(i64::MAX)],
                        },
                        RowLit {
                            cells: vec![Literal::Text("A".into()), Literal::int(i64::MIN)],
                        },
                        RowLit {
                            cells: vec![
                                Literal::Text("A".into()),
                                Literal::int(5_000_000_000_000_000_000i64),
                            ],
                        },
                        RowLit {
                            cells: vec![
                                Literal::Text("A".into()),
                                Literal::int(5_000_000_000_000_000_000i64),
                            ],
                        },
                        RowLit {
                            cells: vec![Literal::Text("B".into()), Literal::int(1)],
                        },
                        RowLit {
                            cells: vec![Literal::Text("C".into()), Literal::int(10)],
                        },
                    ];
                    Plan::Summarize {
                        input: Box::new(Plan::GroupBy {
                            input: Box::new(Plan::SourceExpr(Box::new(Expr::TableLit {
                                schema,
                                rows,
                            }))),
                            keys: vec!["g".into()],
                        }),
                        aggs: vec![AggItem {
                            name: "s".into(),
                            op: AggOp::Sum,
                            arg: Some(RowExpr::Col("x".into())),
                        }],
                        distinct_key: None,
                    }
                }
                1 => {
                    // Decimal sum overflow
                    let schema = TableTy {
                        cols: vec![
                            col("g", ScalarTy::Text, TagSet::empty()),
                            col("d", ScalarTy::Decimal, TagSet::empty()),
                        ],
                        ..TableTy::default()
                    };
                    let rows = vec![
                        RowLit {
                            cells: vec![Literal::Text("A".into()), Literal::decimal(DEC_MAX)],
                        },
                        RowLit {
                            cells: vec![Literal::Text("B".into()), Literal::decimal(DEC_SCALE)],
                        },
                        RowLit {
                            cells: vec![Literal::Text("A".into()), Literal::decimal(1)],
                        },
                        RowLit {
                            cells: vec![Literal::Text("C".into()), Literal::decimal(DEC_SCALE)],
                        },
                        RowLit {
                            cells: vec![Literal::Text("B".into()), Literal::decimal(DEC_SCALE)],
                        },
                    ];
                    Plan::Summarize {
                        input: Box::new(Plan::GroupBy {
                            input: Box::new(Plan::SourceExpr(Box::new(Expr::TableLit {
                                schema,
                                rows,
                            }))),
                            keys: vec!["g".into()],
                        }),
                        aggs: vec![AggItem {
                            name: "sd".into(),
                            op: AggOp::Sum,
                            arg: Some(RowExpr::Col("d".into())),
                        }],
                        distinct_key: None,
                    }
                }
                2 => {
                    // Trapping DivInt inside Summarize agg arg across multiple batches & groups
                    let base = gen_base_table_plan(rng, 6, 14);
                    Plan::Summarize {
                        input: Box::new(Plan::GroupBy {
                            input: Box::new(base),
                            keys: vec!["g".into()],
                        }),
                        aggs: vec![
                            AggItem {
                                name: "cnt".into(),
                                op: AggOp::Count,
                                arg: None,
                            },
                            AggItem {
                                name: "qsum".into(),
                                op: AggOp::Sum,
                                arg: Some(RowExpr::Prim {
                                    op: PrimOp::DivInt,
                                    args: vec![
                                        RowExpr::Lit(Literal::int(100)),
                                        RowExpr::Col("x".into()),
                                    ],
                                }),
                            },
                        ],
                        distinct_key: None,
                    }
                }
                _ => {
                    // Trapping UnwrapBang inside Summarize agg arg
                    let base = gen_base_table_plan(rng, 6, 14);
                    Plan::Summarize {
                        input: Box::new(Plan::GroupBy {
                            input: Box::new(base),
                            keys: vec!["g".into()],
                        }),
                        aggs: vec![AggItem {
                            name: "usum".into(),
                            op: AggOp::Sum,
                            arg: Some(RowExpr::Prim {
                                op: PrimOp::UnwrapBang,
                                args: vec![RowExpr::Col("opt".into())],
                            }),
                        }],
                        distinct_key: None,
                    }
                }
            };
            (mk_console_prog(print_table(plan)), World::default())
        }

        // Family 7: SuppressSmallGroups (Drop & MaskComplementary) on PII/FERPA schemas
        7 => {
            let schema = TableTy {
                cols: vec![
                    col("pid", ScalarTy::Int, ts(&["pii"])),
                    col("dept", ScalarTy::Text, TagSet::empty()),
                    col("score", ScalarTy::Int, ts(&["ferpa"])),
                    col("gpa", ScalarTy::Decimal, ts(&["ferpa"])),
                ],
                ..TableTy::default()
            };
            let n_rows = 8 + rng.gen_range(16);
            let depts = ["A", "B", "C1", "C2"];
            let mut rows = Vec::with_capacity(n_rows);
            for i in 0..n_rows {
                let dept = if i < 2 {
                    "A"
                } else if i < 7 {
                    "C1"
                } else if i < 12 {
                    "C2"
                } else {
                    depts[rng.gen_range(depts.len())]
                };
                rows.push(RowLit {
                    cells: vec![
                        Literal::int((i as i64) + 1),
                        Literal::Text(dept.into()),
                        Literal::int(50 + (rng.gen_range(50) as i64)),
                        Literal::decimal((2 + rng.gen_range(3) as i128) * DEC_SCALE),
                    ],
                });
            }
            let use_bucket = rng.gen_bool(1, 3);
            let grouped = if use_bucket {
                Plan::GroupBy {
                    input: Box::new(Plan::Derive {
                        input: Box::new(Plan::SourceExpr(Box::new(Expr::TableLit {
                            schema,
                            rows,
                        }))),
                        items: vec![DeriveItem::BucketCol {
                            name: "band".into(),
                            source: "score".into(),
                            cuts: vec![Literal::int(70)],
                            labels: vec!["low".into(), "high".into()],
                        }],
                    }),
                    keys: vec!["band".into()],
                }
            } else {
                Plan::GroupBy {
                    input: Box::new(Plan::SourceExpr(Box::new(Expr::TableLit { schema, rows }))),
                    keys: vec!["dept".into()],
                }
            };
            let use_distinct = rng.gen_bool(2, 3);
            let summarized = Plan::Summarize {
                input: Box::new(grouped),
                aggs: vec![
                    AggItem {
                        name: "n".into(),
                        op: AggOp::Count,
                        arg: None,
                    },
                    AggItem {
                        name: "nd".into(),
                        op: AggOp::CountDistinct,
                        arg: Some(RowExpr::Col("pid".into())),
                    },
                    AggItem {
                        name: "avg_s".into(),
                        op: AggOp::Mean,
                        arg: Some(RowExpr::Col("score".into())),
                    },
                    AggItem {
                        name: "sum_g".into(),
                        op: AggOp::Sum,
                        arg: Some(RowExpr::Col("gpa".into())),
                    },
                ],
                distinct_key: if use_distinct {
                    Some("pid".into())
                } else {
                    None
                },
            };
            let mode = if rng.gen_bool(1, 2) {
                SuppressMode::Drop
            } else {
                SuppressMode::MaskComplementary
            };
            let plan = Plan::SuppressSmallGroups {
                input: Box::new(summarized),
                min_k: BigInt::from((5 + rng.gen_range(3)) as u64),
                distinct_by: if use_distinct {
                    Some("pid".into())
                } else {
                    None
                },
                mode,
            };
            (mk_console_prog(print_table(plan)), World::default())
        }

        // Family 8: Window across all 6 WindowFns + RunningSum Int/Decimal overflow traps
        8 => {
            if rng.gen_bool(1, 5) {
                // RunningSum overflow (Int or Decimal)
                let is_dec = rng.gen_bool(1, 2);
                let schema = TableTy {
                    cols: vec![
                        col("p", ScalarTy::Text, TagSet::empty()),
                        col(
                            "v",
                            if is_dec {
                                ScalarTy::Decimal
                            } else {
                                ScalarTy::Int
                            },
                            TagSet::empty(),
                        ),
                    ],
                    ..TableTy::default()
                };
                let big = if is_dec {
                    Literal::decimal(DEC_MAX)
                } else {
                    Literal::int(i64::MAX)
                };
                let one = if is_dec {
                    Literal::decimal(1)
                } else {
                    Literal::int(1)
                };
                let rows = vec![
                    RowLit {
                        cells: vec![Literal::Text("A".into()), big],
                    },
                    RowLit {
                        cells: vec![Literal::Text("B".into()), one.clone()],
                    },
                    RowLit {
                        cells: vec![Literal::Text("A".into()), one.clone()],
                    },
                    RowLit {
                        cells: vec![Literal::Text("B".into()), one],
                    },
                ];
                let plan = Plan::Window {
                    input: Box::new(Plan::SourceExpr(Box::new(Expr::TableLit { schema, rows }))),
                    items: vec![WindowItem {
                        name: "rs".into(),
                        win_fn: WindowFn::RunningSum { col: "v".into() },
                        over: vec!["p".into()],
                        order: vec![("v".into(), SortDir::Desc)],
                    }],
                };
                return (mk_console_prog(print_table(plan)), World::default());
            }
            let base = gen_base_table_plan(rng, 6, 16);
            let dir = if rng.gen_bool(1, 2) {
                SortDir::Asc
            } else {
                SortDir::Desc
            };
            let over = if rng.gen_bool(3, 4) {
                vec!["g".into()]
            } else {
                vec![]
            };
            let off = (rng.gen_range(3) + 1) as u64;
            let wsize = (rng.gen_range(3) + 1) as u64;
            let items = vec![
                WindowItem {
                    name: "rn".into(),
                    win_fn: WindowFn::RowNumber,
                    over: over.clone(),
                    order: vec![("x".into(), dir), ("id".into(), SortDir::Asc)],
                },
                WindowItem {
                    name: "rk".into(),
                    win_fn: WindowFn::Rank { col: "x".into() },
                    over: over.clone(),
                    order: vec![("x".into(), dir)],
                },
                WindowItem {
                    name: "lg".into(),
                    win_fn: WindowFn::Lag {
                        col: "x".into(),
                        offset: BigInt::from(off),
                    },
                    over: over.clone(),
                    order: vec![("id".into(), SortDir::Asc)],
                },
                WindowItem {
                    name: "ld".into(),
                    win_fn: WindowFn::Lead {
                        col: "d".into(),
                        offset: BigInt::from(off),
                    },
                    over: over.clone(),
                    order: vec![("id".into(), SortDir::Asc)],
                },
                WindowItem {
                    name: "rsum".into(),
                    win_fn: WindowFn::RunningSum {
                        col: if rng.gen_bool(1, 2) { "x" } else { "d" }.into(),
                    },
                    over: over.clone(),
                    order: vec![("id".into(), SortDir::Asc)],
                },
                WindowItem {
                    name: "rmean".into(),
                    win_fn: WindowFn::RollingMean {
                        col: if rng.gen_bool(1, 2) { "f" } else { "x" }.into(),
                        window_size: BigInt::from(wsize),
                    },
                    over,
                    order: vec![("id".into(), SortDir::Asc)],
                },
            ];
            let plan = Plan::Window {
                input: Box::new(base),
                items,
            };
            (mk_console_prog(print_table(plan)), World::default())
        }

        // Family 9: FillGaps (Int, Date, Timestamp) with partitions & fill defaults
        9 => {
            let key_kind = rng.gen_range(3);
            let (k_ty, step, mk_k): (ScalarTy, i64, fn(i64) -> Literal) = match key_kind {
                0 => (ScalarTy::Int, 1, |v| Literal::int(v)),
                1 => (ScalarTy::Date, 1, |v| Literal::date(19_000 + v)),
                _ => (ScalarTy::Timestamp, 1_000_000, |v| {
                    Literal::timestamp(v * 1_000_000)
                }),
            };
            let schema = TableTy {
                cols: vec![
                    col("grp", ScalarTy::Text, TagSet::empty()),
                    col("t", k_ty, TagSet::empty()),
                    col("val", ScalarTy::Int, TagSet::empty()),
                ],
                ..TableTy::default()
            };
            let nrows = 4 + rng.gen_range(8);
            let mut rows = Vec::with_capacity(nrows);
            for _ in 0..nrows {
                let t = (rng.gen_range(6) * 2) as i64;
                rows.push(RowLit {
                    cells: vec![
                        Literal::Text(["A", "B"][rng.gen_range(2)].into()),
                        mk_k(t),
                        Literal::int(rng.pick_small_int()),
                    ],
                });
            }
            let plan = Plan::FillGaps {
                input: Box::new(Plan::SourceExpr(Box::new(Expr::TableLit { schema, rows }))),
                col: "t".into(),
                step_micros: BigInt::from(step),
                over: vec!["grp".into()],
                fill: vec![("val".into(), Literal::int(-1))],
            };
            (mk_console_prog(print_table(plan)), World::default())
        }

        // Family 10: PivotWider and Crosstab
        10 => {
            let schema = TableTy {
                cols: vec![
                    col("id", ScalarTy::Text, TagSet::empty()),
                    col("k", ScalarTy::Text, TagSet::empty()),
                    col("v", ScalarTy::Int, TagSet::empty()),
                ],
                ..TableTy::default()
            };
            let nrows = 5 + rng.gen_range(10);
            let ids = ["r1", "r2", "r3", "r4"];
            let ks = ["q1", "q2", "q3"];
            let rows: Vec<RowLit> = (0..nrows)
                .map(|_| RowLit {
                    cells: vec![
                        Literal::Text(ids[rng.gen_range(ids.len())].into()),
                        Literal::Text(ks[rng.gen_range(ks.len())].into()),
                        Literal::int(rng.pick_small_int()),
                    ],
                })
                .collect();
            let tbl = Expr::TableLit { schema, rows };
            if rng.gen_bool(1, 2) {
                let plan = Plan::Sort {
                    input: Box::new(Plan::PivotWider {
                        input: Box::new(Plan::SourceExpr(Box::new(tbl))),
                        names_from: "k".into(),
                        values_from: "v".into(),
                        static_cols: vec!["q1".into(), "q2".into(), "q3".into()],
                        fill: Literal::int(0),
                    }),
                    keys: vec![("id".into(), SortDir::Asc)],
                };
                (mk_console_prog(print_table(plan)), World::default())
            } else {
                let plan = Plan::Crosstab {
                    input: Box::new(Plan::SourceExpr(Box::new(tbl))),
                    rows_col: "id".into(),
                    cols_col: "k".into(),
                    values_col: "v".into(),
                    fill: Literal::int(-1),
                };
                let prog = Program {
                    funs: vec![FunDecl {
                        name: "main".into(),
                        kind: FunKind::Function,
                        is_pure: false,
                        params: vec![],
                        pc: TagSet::empty(),
                        ret: LTy::public(Ty::DynamicTable(TagSet::empty())),
                        body: Expr::Rel(Box::new(plan)),
                    }],
                    entry: Some("main".into()),
                    ..Program::default()
                };
                (prog, World::default())
            }
        }

        // Family 11: Redact and Pseudonymize on PII/FERPA-tagged schemas (+ Filter pushdown)
        11 => {
            let schema = TableTy {
                cols: vec![
                    col("email", ScalarTy::Text, ts(&["pii"])),
                    col("dept", ScalarTy::Text, TagSet::empty()),
                    col("x", ScalarTy::Int, TagSet::empty()),
                ],
                ..TableTy::default()
            };
            let nrows = 5 + rng.gen_range(10);
            let rows: Vec<RowLit> = (0..nrows)
                .map(|_| RowLit {
                    cells: vec![
                        Literal::Text(rng.pick_text()),
                        Literal::Text(rng.pick_group()),
                        Literal::int(rng.pick_small_int()),
                    ],
                })
                .collect();
            let tbl = Expr::TableLit { schema, rows };
            let declass = if rng.gen_bool(1, 2) {
                Plan::Redact {
                    input: Box::new(Plan::SourceExpr(Box::new(tbl))),
                    col: "email".into(),
                    replacement: "[MASKED]".into(),
                }
            } else {
                Plan::Pseudonymize {
                    input: Box::new(Plan::SourceExpr(Box::new(tbl))),
                    col: "email".into(),
                    secret: Box::new(Expr::Var("sec".into())),
                }
            };
            let plan = Plan::Sort {
                input: Box::new(Plan::Filter {
                    input: Box::new(declass),
                    pred: RowExpr::Prim {
                        op: PrimOp::Ge,
                        args: vec![RowExpr::Col("x".into()), RowExpr::Lit(Literal::int(0))],
                    },
                }),
                keys: vec![("dept".into(), SortDir::Asc), ("x".into(), SortDir::Desc)],
            };
            let prog = Program {
                funs: vec![FunDecl {
                    name: "main".into(),
                    kind: FunKind::Function,
                    is_pure: false,
                    params: vec![
                        (
                            "sec".into(),
                            LTy::new(Ty::Secret("salt_k".into()), ts(&["secret"])),
                        ),
                        ("c".into(), LTy::public(Ty::Console(TagSet::empty()))),
                    ],
                    pc: TagSet::empty(),
                    ret: LTy::public(Ty::Unit),
                    body: print_table(plan),
                }],
                entry: Some("main".into()),
                ..Program::default()
            };
            let world = World {
                real_secrets: vec![("salt_k".into(), "dana-test-salt-2026".into())],
                ..World::default()
            };
            (prog, world)
        }

        // Family 12: SourceDB (populated World.real_db_tables + empty fallback)
        12 => {
            let db_schema = TableTy {
                cols: vec![
                    col("id", ScalarTy::Int, TagSet::empty()),
                    col("g", ScalarTy::Text, TagSet::empty()),
                    col("amt", ScalarTy::Int, TagSet::empty()),
                ],
                ..TableTy::default()
            };
            let nrows = if rng.gen_bool(1, 5) {
                0
            } else {
                6 + rng.gen_range(10)
            };
            let db_rows: Vec<Vec<Val>> = (0..nrows)
                .map(|i| {
                    vec![
                        Val::Int(BigInt::from(i as i64)),
                        Val::Text(rng.pick_group()),
                        Val::Int(BigInt::from(rng.pick_small_int())),
                    ]
                })
                .collect();
            let world = World {
                real_db_tables: if nrows == 0 {
                    vec![]
                } else {
                    vec![StoredTable {
                        db: "wh".into(),
                        table_name: "orders".into(),
                        schema: db_schema.clone(),
                        rows: db_rows,
                    }]
                },
                ..World::default()
            };
            let plan = Plan::Sort {
                input: Box::new(Plan::Summarize {
                    input: Box::new(Plan::GroupBy {
                        input: Box::new(Plan::Filter {
                            input: Box::new(Plan::SourceDB {
                                cap: Box::new(Expr::Var("db".into())),
                                table_name: "orders".into(),
                                schema: db_schema,
                            }),
                            pred: RowExpr::Prim {
                                op: PrimOp::Gt,
                                args: vec![
                                    RowExpr::Col("amt".into()),
                                    RowExpr::Lit(Literal::int(-5)),
                                ],
                            },
                        }),
                        keys: vec!["g".into()],
                    }),
                    aggs: vec![
                        AggItem {
                            name: "n".into(),
                            op: AggOp::Count,
                            arg: None,
                        },
                        AggItem {
                            name: "tot".into(),
                            op: AggOp::Sum,
                            arg: Some(RowExpr::Col("amt".into())),
                        },
                    ],
                    distinct_key: None,
                }),
                keys: vec![("g".into(), SortDir::Asc)],
            };
            let prog = Program {
                funs: vec![FunDecl {
                    name: "main".into(),
                    kind: FunKind::Function,
                    is_pure: false,
                    params: vec![
                        ("db".into(), LTy::public(Ty::ReadDB("wh".into()))),
                        ("c".into(), LTy::public(Ty::Console(TagSet::empty()))),
                    ],
                    pc: TagSet::empty(),
                    ret: LTy::public(Ty::Unit),
                    body: print_table(plan),
                }],
                entry: Some("main".into()),
                ..Program::default()
            };
            (prog, world)
        }

        // Family 13: Optimizer stress & stop-preservation (Filter fusion, pushdown across
        //            Select/Drop/Rename/Derive/Sort, dead Derive pruning, Limit folding,
        //            and trapping predicates/derives across Sort/Limit/Join)
        _ => {
            let base = gen_base_table_plan(rng, 7, 16);
            let sub = rng.gen_range(7);
            let plan = match sub {
                0 => {
                    // Dead Derive pruning + chained Derive dependency (a -> b, only b selected)
                    // + Filter fusion + Select fusion + Limit fold
                    Plan::Limit {
                        input: Box::new(Plan::Limit {
                            input: Box::new(Plan::Select {
                                input: Box::new(Plan::Select {
                                    input: Box::new(Plan::Filter {
                                        input: Box::new(Plan::Filter {
                                            input: Box::new(Plan::Derive {
                                                input: Box::new(base),
                                                items: vec![
                                                    DeriveItem::ColExpr {
                                                        name: "unused_pure".into(),
                                                        expr: Box::new(RowExpr::Prim {
                                                            op: PrimOp::Eq,
                                                            args: vec![
                                                                RowExpr::Col("x".into()),
                                                                RowExpr::Lit(Literal::int(0)),
                                                            ],
                                                        }),
                                                    },
                                                    DeriveItem::ColExpr {
                                                        name: "inter".into(),
                                                        expr: Box::new(RowExpr::Prim {
                                                            op: PrimOp::AddInt,
                                                            args: vec![
                                                                RowExpr::Col("x".into()),
                                                                RowExpr::Lit(Literal::int(1)),
                                                            ],
                                                        }),
                                                    },
                                                    DeriveItem::ColExpr {
                                                        name: "kept".into(),
                                                        expr: Box::new(RowExpr::Prim {
                                                            op: PrimOp::MulInt,
                                                            args: vec![
                                                                RowExpr::Col("inter".into()),
                                                                RowExpr::Lit(Literal::int(2)),
                                                            ],
                                                        }),
                                                    },
                                                ],
                                            }),
                                            pred: RowExpr::Prim {
                                                op: PrimOp::Ge,
                                                args: vec![
                                                    RowExpr::Col("x".into()),
                                                    RowExpr::Lit(Literal::int(0)),
                                                ],
                                            },
                                        }),
                                        pred: RowExpr::Prim {
                                            op: PrimOp::Le,
                                            args: vec![
                                                RowExpr::Col("x".into()),
                                                RowExpr::Lit(Literal::int(50)),
                                            ],
                                        },
                                    }),
                                    cols: vec!["id".into(), "g".into(), "kept".into()],
                                }),
                                cols: vec!["id".into(), "kept".into()],
                            }),
                            n: BigInt::from(10u64),
                        }),
                        n: BigInt::from(4u64),
                    }
                }
                1 => {
                    // Simultaneous Rename swap (`x <-> id`) + Filter pushdown across Rename!
                    Plan::Filter {
                        input: Box::new(Plan::Rename {
                            input: Box::new(base),
                            pairs: vec![("id".into(), "x".into()), ("x".into(), "id".into())],
                        }),
                        pred: RowExpr::Prim {
                            op: PrimOp::Gt,
                            args: vec![RowExpr::Col("id".into()), RowExpr::Lit(Literal::int(0))],
                        },
                    }
                }
                2 => {
                    // Derive overwriting an existing column `x` followed by Filter on `x`
                    Plan::Filter {
                        input: Box::new(Plan::Derive {
                            input: Box::new(base),
                            items: vec![DeriveItem::ColExpr {
                                name: "x".into(),
                                expr: Box::new(RowExpr::Prim {
                                    op: PrimOp::AddInt,
                                    args: vec![
                                        RowExpr::Col("x".into()),
                                        RowExpr::Lit(Literal::int(10)),
                                    ],
                                }),
                            }],
                        }),
                        pred: RowExpr::Prim {
                            op: PrimOp::Gt,
                            args: vec![RowExpr::Col("x".into()), RowExpr::Lit(Literal::int(12))],
                        },
                    }
                }
                3 => {
                    // Trapping Filter after Sort (must NOT push trapping predicate across Sort!)
                    Plan::Filter {
                        input: Box::new(Plan::Sort {
                            input: Box::new(base),
                            keys: vec![("x".into(), SortDir::Desc), ("id".into(), SortDir::Asc)],
                        }),
                        pred: RowExpr::Prim {
                            op: PrimOp::Gt,
                            args: vec![
                                RowExpr::Prim {
                                    op: PrimOp::DivInt,
                                    args: vec![
                                        RowExpr::Lit(Literal::int(100)),
                                        RowExpr::Col("x".into()),
                                    ],
                                },
                                RowExpr::Lit(Literal::int(1)),
                            ],
                        },
                    }
                }
                4 => {
                    // Trapping Filter after Limit (must NOT push across Limit!)
                    Plan::Filter {
                        input: Box::new(Plan::Limit {
                            input: Box::new(base),
                            n: BigInt::from((rng.gen_range(5) + 1) as u64),
                        }),
                        pred: RowExpr::Prim {
                            op: PrimOp::Gt,
                            args: vec![
                                RowExpr::Prim {
                                    op: PrimOp::DivInt,
                                    args: vec![
                                        RowExpr::Lit(Literal::int(100)),
                                        RowExpr::Col("x".into()),
                                    ],
                                },
                                RowExpr::Lit(Literal::int(0)),
                            ],
                        },
                    }
                }
                5 => {
                    // Non-trapping Filter above trapping Derive (must NOT push Filter below Derive!)
                    Plan::Filter {
                        input: Box::new(Plan::Derive {
                            input: Box::new(base),
                            items: vec![DeriveItem::ColExpr {
                                name: "q".into(),
                                expr: Box::new(RowExpr::Prim {
                                    op: PrimOp::DivInt,
                                    args: vec![
                                        RowExpr::Lit(Literal::int(100)),
                                        RowExpr::Col("x".into()),
                                    ],
                                }),
                            }],
                        }),
                        pred: RowExpr::Prim {
                            op: PrimOp::Gt,
                            args: vec![RowExpr::Col("id".into()), RowExpr::Lit(Literal::int(999))],
                        },
                    }
                }
                _ => {
                    // Int/Decimal overflow inside Derive followed by Filter(false)
                    let is_dec = rng.gen_bool(1, 2);
                    let trap_expr = if is_dec {
                        RowExpr::Prim {
                            op: PrimOp::AddDec,
                            args: vec![
                                RowExpr::Col("d".into()),
                                RowExpr::Lit(Literal::decimal(DEC_MAX)),
                            ],
                        }
                    } else {
                        RowExpr::Prim {
                            op: PrimOp::AddInt,
                            args: vec![
                                RowExpr::Col("x".into()),
                                RowExpr::Lit(Literal::int(i64::MAX)),
                            ],
                        }
                    };
                    Plan::Filter {
                        input: Box::new(Plan::Derive {
                            input: Box::new(base),
                            items: vec![DeriveItem::ColExpr {
                                name: "ov".into(),
                                expr: Box::new(trap_expr),
                            }],
                        }),
                        pred: RowExpr::Lit(Literal::Bool(false)),
                    }
                }
            };
            (mk_console_prog(print_table(plan)), World::default())
        }
    }
}

#[test]
fn differential_5000_generated_core_pipelines_oracle_vs_vm() -> Result<(), String> {
    const TOTAL_CASES: usize = 5_040;
    const SEED: u64 = 0xDA4A_2026_C0DE_5040;
    const FUEL: usize = 50_000;

    let mut rng = SplitMix64::new(SEED);
    let cases: Vec<(usize, Program, World)> = (0..TOTAL_CASES)
        .map(|i| {
            let (prog, world) = gen_core_pipeline_case(&mut rng, i);
            (i, prog, world)
        })
        .collect();

    let cfg_seq_unopt = VmConfig {
        batch_size: 4,
        parallel_threshold_rows: usize::MAX,
        max_threads: Some(1),
        optimize: false,
        ..VmConfig::sequential_unoptimized()
    };
    let cfg_seq_opt = VmConfig {
        batch_size: 4,
        parallel_threshold_rows: usize::MAX,
        max_threads: Some(1),
        optimize: true,
        ..VmConfig::sequential_optimized()
    };
    let cfg_par_opt = VmConfig {
        batch_size: 4,
        parallel_threshold_rows: 4,
        max_threads: Some(4),
        optimize: true,
        ..VmConfig::parallel_optimized(4, 4)
    };

    let ok_count = AtomicUsize::new(0);
    let stop_count = AtomicUsize::new(0);
    let first_err: std::sync::Mutex<Option<String>> = std::sync::Mutex::new(None);

    let outer_threads = std::thread::available_parallelism()
        .map(std::num::NonZeroUsize::get)
        .unwrap_or(4)
        .min(4);
    let chunk_size = cases.len().div_ceil(outer_threads);

    std::thread::scope(|scope| {
        for chunk in cases.chunks(chunk_size) {
            let ok_ref = &ok_count;
            let stop_ref = &stop_count;
            let err_ref = &first_err;
            scope.spawn(move || {
                for (i, prog, world) in chunk {
                    if err_ref
                        .lock()
                        .unwrap_or_else(std::sync::PoisonError::into_inner)
                        .is_some()
                    {
                        return;
                    }
                    let record_err = |msg: String| {
                        let mut guard = err_ref
                            .lock()
                            .unwrap_or_else(std::sync::PoisonError::into_inner);
                        if guard.is_none() {
                            *guard = Some(msg);
                        }
                    };

                    if let Err(e) = check_program(prog) {
                        record_err(format!(
                            "case {i} (family {}) failed check_program: {}\nwire:\n{}",
                            i % 14,
                            e.message,
                            print_program(prog)
                        ));
                        return;
                    }
                    let (opt_prog, _) = optimize_program(prog);
                    if let Err(e) = check_program(&opt_prog) {
                        record_err(format!(
                            "case {i} (family {}) optimized program failed check_program: {}\norig:\n{}\nopt:\n{}",
                            i % 14,
                            e.message,
                            print_program(prog),
                            print_program(&opt_prog)
                        ));
                        return;
                    }

                    let oracle = match run_program(FUEL, prog, world.clone()) {
                        Ok(r) => r,
                        Err(e) => {
                            record_err(format!(
                                "case {i} (family {}) oracle runtime error: {e:?}\nwire:\n{}",
                                i % 14,
                                print_program(prog)
                            ));
                            return;
                        }
                    };
                    let vm_seq_unopt =
                        match run_core_program_vm(FUEL, prog, world.clone(), &cfg_seq_unopt) {
                            Ok(r) => r,
                            Err(e) => {
                                record_err(format!(
                                    "case {i} (family {}) vm_seq_unopt error: {e:?}\nwire:\n{}",
                                    i % 14,
                                    print_program(prog)
                                ));
                                return;
                            }
                        };
                    let vm_seq_opt =
                        match run_core_program_vm(FUEL, prog, world.clone(), &cfg_seq_opt) {
                            Ok(r) => r,
                            Err(e) => {
                                record_err(format!(
                                    "case {i} (family {}) vm_seq_opt error: {e:?}\nwire:\n{}",
                                    i % 14,
                                    print_program(prog)
                                ));
                                return;
                            }
                        };
                    let vm_par_opt =
                        match run_core_program_vm(FUEL, prog, world.clone(), &cfg_par_opt) {
                            Ok(r) => r,
                            Err(e) => {
                                record_err(format!(
                                    "case {i} (family {}) vm_par_opt error: {e:?}\nwire:\n{}",
                                    i % 14,
                                    print_program(prog)
                                ));
                                return;
                            }
                        };

                    let rep_oracle = print_report(&oracle);
                    let rep_seq_unopt = print_report(&vm_seq_unopt);
                    let rep_seq_opt = print_report(&vm_seq_opt);
                    let rep_par_opt = print_report(&vm_par_opt);

                    if rep_oracle != rep_seq_unopt {
                        record_err(format!(
                            "case {i} (family {}) MISMATCH oracle vs vm_seq_unopt:\noracle:\n{rep_oracle}\nvm_seq_unopt:\n{rep_seq_unopt}\nwire:\n{}",
                            i % 14,
                            print_program(prog)
                        ));
                        return;
                    }
                    if rep_oracle != rep_seq_opt {
                        record_err(format!(
                            "case {i} (family {}) MISMATCH oracle vs vm_seq_opt:\noracle:\n{rep_oracle}\nvm_seq_opt:\n{rep_seq_opt}\norig:\n{}\nopt:\n{}",
                            i % 14,
                            print_program(prog),
                            print_program(&opt_prog)
                        ));
                        return;
                    }
                    if rep_oracle != rep_par_opt {
                        record_err(format!(
                            "case {i} (family {}) MISMATCH oracle vs vm_par_opt:\noracle:\n{rep_oracle}\nvm_par_opt:\n{rep_par_opt}\nwire:\n{}",
                            i % 14,
                            print_program(prog)
                        ));
                        return;
                    }

                    match oracle.status {
                        ExitStatus::Ok => {
                            ok_ref.fetch_add(1, Ordering::Relaxed);
                        }
                        ExitStatus::Stopped | ExitStatus::Failed => {
                            stop_ref.fetch_add(1, Ordering::Relaxed);
                        }
                    }
                }
            });
        }
    });

    if let Some(err) = first_err
        .into_inner()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
    {
        return Err(err);
    }

    let ok_n = ok_count.load(Ordering::Relaxed);
    let stop_n = stop_count.load(Ordering::Relaxed);
    assert_eq!(ok_n + stop_n, TOTAL_CASES);
    assert!(ok_n > 2_500, "expected > 2,500 Ok runs, got {ok_n}");
    assert!(
        stop_n > 500,
        "expected > 500 Stopped runs (traps), got {stop_n}"
    );
    eprintln!(
        "[differential_vm] {TOTAL_CASES} generated Core IR programs verified 100% parity (Ok={ok_n}, Stopped={stop_n})"
    );
    Ok(())
}

// ===========================================================================
// Curated Triple-Parity Test: Lean 4 `danacore` == Rust `oracle` == Rust `vm`
// ===========================================================================

static LEAN_BIN: OnceLock<PathBuf> = OnceLock::new();
static TMP_COUNTER: AtomicU64 = AtomicU64::new(0);

fn lean_danacore_bin() -> &'static Path {
    LEAN_BIN.get_or_init(|| {
        let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        let local_bin = manifest_dir.join("formal/.lake/build/bin/danacore");
        if local_bin.exists() {
            return local_bin;
        }
        let shared_bin = PathBuf::from("/home/exedev/code/dana/formal/.lake/build/bin/danacore");
        if shared_bin.exists() {
            return shared_bin;
        }
        let formal_dir = manifest_dir.join("formal");
        let home = std::env::var("HOME").unwrap_or_default();
        let cur_path = std::env::var("PATH").unwrap_or_default();
        let full_path = format!("{home}/.elan/bin:/opt/elan/bin:{cur_path}");
        let status = Command::new("lake")
            .args(["build", "DanaCore", "danacore"])
            .current_dir(&formal_dir)
            .env("PATH", full_path)
            .status();
        let ok = status.as_ref().is_ok_and(|s| s.success());
        assert!(
            ok && local_bin.exists(),
            "`lake build DanaCore danacore` failed ({status:?}); run `make formal` first"
        );
        local_bin
    })
}

struct TempCoreFile {
    path: PathBuf,
}

impl TempCoreFile {
    fn new(name: &str, content: &str) -> Result<Self, String> {
        let id = TMP_COUNTER.fetch_add(1, Ordering::Relaxed);
        let pid = std::process::id();
        let path = std::env::temp_dir().join(format!("dana_vm_triple_{name}_{pid}_{id}.core"));
        fs::write(&path, content).map_err(|e| format!("write temp core file: {e}"))?;
        Ok(Self { path })
    }
}

impl Drop for TempCoreFile {
    fn drop(&mut self) {
        let _ = fs::remove_file(&self.path);
    }
}

fn build_triple_parity_corpus() -> Vec<(&'static str, Program, Option<&'static str>)> {
    let mut cases: Vec<(&'static str, Program, Option<&'static str>)> = Vec::new();
    let mut rng = SplitMix64::new(0x0003_BEEF_1234_5678);

    // 1. Select + Drop + Rename + Filter fusion + Sort + nested Limit
    {
        let base = gen_base_table_plan(&mut rng, 10, 10);
        let plan = Plan::Limit {
            input: Box::new(Plan::Limit {
                input: Box::new(Plan::Sort {
                    input: Box::new(Plan::Select {
                        input: Box::new(Plan::Rename {
                            input: Box::new(Plan::Drop {
                                input: Box::new(Plan::Filter {
                                    input: Box::new(Plan::Filter {
                                        input: Box::new(base),
                                        pred: RowExpr::Prim {
                                            op: PrimOp::Ge,
                                            args: vec![
                                                RowExpr::Col("x".into()),
                                                RowExpr::Lit(Literal::int(-5)),
                                            ],
                                        },
                                    }),
                                    pred: RowExpr::Prim {
                                        op: PrimOp::Le,
                                        args: vec![
                                            RowExpr::Col("x".into()),
                                            RowExpr::Lit(Literal::int(100)),
                                        ],
                                    },
                                }),
                                cols: vec!["f".into()],
                            }),
                            pairs: vec![("grp".into(), "g".into()), ("val".into(), "x".into())],
                        }),
                        cols: vec!["id".into(), "grp".into(), "val".into()],
                    }),
                    keys: vec![("grp".into(), SortDir::Asc), ("val".into(), SortDir::Desc)],
                }),
                n: BigInt::from(8u64),
            }),
            n: BigInt::from(5u64),
        };
        cases.push((
            "01_select_drop_rename_filter_sort_nested_limit",
            mk_console_prog(print_table(plan)),
            None,
        ));
    }

    // 2. Derive ColExpr + BucketCol + OuterVar + ConstRef + Coalesce
    {
        let base = gen_base_table_plan(&mut rng, 9, 9);
        let plan = Plan::Derive {
            input: Box::new(base),
            items: vec![
                DeriveItem::ColExpr {
                    name: "calc".into(),
                    expr: Box::new(RowExpr::Prim {
                        op: PrimOp::AddInt,
                        args: vec![
                            RowExpr::OuterVar("bias".into()),
                            RowExpr::Coalesce {
                                opt_expr: Box::new(RowExpr::Col("opt".into())),
                                default_expr: Box::new(RowExpr::ConstRef("DEF_VAL".into())),
                            },
                        ],
                    }),
                },
                DeriveItem::BucketCol {
                    name: "band".into(),
                    source: "x".into(),
                    cuts: vec![Literal::int(0), Literal::int(10)],
                    labels: vec!["neg".into(), "mid".into(), "high".into()],
                },
            ],
        };
        let prog = mk_console_prog_with(
            vec![ConstDecl {
                name: "DEF_VAL".into(),
                lty: LTy::public(Ty::Int),
                value: Literal::int(7),
            }],
            vec![],
            TagSet::empty(),
            let_seq(
                "bias",
                LTy::public(Ty::Int),
                Expr::Lit(Literal::int(10)),
                print_table(plan),
            ),
        );
        cases.push(("02_derive_bucket_outervar_constref", prog, None));
    }

    // 3. Non-recursive pure UDF inlining (IfE, LetE, Decimal math, nested UDF call)
    {
        let base = gen_base_table_plan(&mut rng, 10, 10);
        let plan = Plan::Derive {
            input: Box::new(Plan::Filter {
                input: Box::new(base),
                pred: RowExpr::Prim {
                    op: PrimOp::Gt,
                    args: vec![
                        RowExpr::CallPure {
                            fn_name: "score_udf".into(),
                            args: vec![RowExpr::Col("x".into()), RowExpr::Col("opt".into())],
                        },
                        RowExpr::Lit(Literal::int(0)),
                    ],
                },
            }),
            items: vec![
                DeriveItem::ColExpr {
                    name: "sc".into(),
                    expr: Box::new(RowExpr::CallPure {
                        fn_name: "score_udf".into(),
                        args: vec![RowExpr::Col("x".into()), RowExpr::Col("opt".into())],
                    }),
                },
                DeriveItem::ColExpr {
                    name: "net".into(),
                    expr: Box::new(RowExpr::CallPure {
                        fn_name: "net_dec_udf".into(),
                        args: vec![
                            RowExpr::Col("d".into()),
                            RowExpr::Lit(Literal::decimal(DEC_SCALE / 4)),
                        ],
                    }),
                },
            ],
        };
        cases.push((
            "03_non_recursive_udf_inlining",
            mk_console_prog_with(
                vec![],
                pure_udf_non_recursive_funs(),
                TagSet::empty(),
                print_table(plan),
            ),
            None,
        ));
    }

    // 4. Recursive pure UDF fallback in Derive
    {
        let schema = TableTy {
            cols: vec![col("n", ScalarTy::Int, TagSet::empty())],
            ..TableTy::default()
        };
        let rows = (0..8)
            .map(|i| RowLit {
                cells: vec![Literal::int((i as i64) - 1)],
            })
            .collect();
        let plan = Plan::Derive {
            input: Box::new(Plan::SourceExpr(Box::new(Expr::TableLit { schema, rows }))),
            items: vec![DeriveItem::ColExpr {
                name: "tri".into(),
                expr: Box::new(RowExpr::CallPure {
                    fn_name: "rec_tri".into(),
                    args: vec![RowExpr::Col("n".into())],
                }),
            }],
        };
        cases.push((
            "04_recursive_udf_fallback",
            mk_console_prog_with(
                vec![],
                pure_udf_recursive_funs(),
                TagSet::empty(),
                print_table(plan),
            ),
            None,
        ));
    }

    // 5-11. All 7 JoinKinds
    {
        let l_schema = TableTy {
            cols: vec![
                col("id", ScalarTy::Int, TagSet::empty()),
                col("v", ScalarTy::Text, TagSet::empty()),
            ],
            ..TableTy::default()
        };
        let r_schema = TableTy {
            cols: vec![
                col("id", ScalarTy::Int, TagSet::empty()),
                col("v", ScalarTy::Text, TagSet::empty()),
            ],
            ..TableTy::default()
        };
        let l_uniq = Expr::TableLit {
            schema: l_schema.clone(),
            rows: (1..=8)
                .map(|i| RowLit {
                    cells: vec![Literal::int(i), Literal::Text(format!("L{i}"))],
                })
                .collect(),
        };
        let l_dup = Expr::TableLit {
            schema: l_schema,
            rows: [1, 1, 2, 3, 3, 4, 5, 6]
                .iter()
                .enumerate()
                .map(|(idx, &k)| RowLit {
                    cells: vec![Literal::int(k), Literal::Text(format!("LD{idx}"))],
                })
                .collect(),
        };
        let r_uniq = Expr::TableLit {
            schema: r_schema.clone(),
            rows: [1, 3, 5, 7, 9]
                .iter()
                .map(|&k| RowLit {
                    cells: vec![Literal::int(k), Literal::Text(format!("R{k}"))],
                })
                .collect(),
        };
        let r_dup = Expr::TableLit {
            schema: r_schema,
            rows: [1, 1, 3, 3, 5]
                .iter()
                .enumerate()
                .map(|(idx, &k)| RowLit {
                    cells: vec![Literal::int(k), Literal::Text(format!("RD{idx}"))],
                })
                .collect(),
        };

        let join_specs = [
            (
                "05_join_inner_one",
                JoinKind::InnerOne,
                &l_uniq,
                &r_uniq,
                JoinOn::SameKeys(vec!["id".into()]),
                Some(("_l", "_r")),
            ),
            (
                "06_join_inner_many_to_one",
                JoinKind::InnerManyToOne,
                &l_dup,
                &r_uniq,
                JoinOn::Pairs(vec![("id".into(), "id".into())]),
                Some(("_l", "_r")),
            ),
            (
                "07_join_inner_many",
                JoinKind::InnerMany,
                &l_dup,
                &r_dup,
                JoinOn::SameKeys(vec!["id".into()]),
                Some(("_l", "_r")),
            ),
            (
                "08_join_left_one",
                JoinKind::LeftOne,
                &l_uniq,
                &r_uniq,
                JoinOn::SameKeys(vec!["id".into()]),
                Some(("_l", "_r")),
            ),
            (
                "09_join_left_many_to_one",
                JoinKind::LeftManyToOne,
                &l_dup,
                &r_uniq,
                JoinOn::SameKeys(vec!["id".into()]),
                Some(("_l", "_r")),
            ),
            (
                "10_join_semi",
                JoinKind::Semi,
                &l_uniq,
                &r_uniq,
                JoinOn::SameKeys(vec!["id".into()]),
                None,
            ),
            (
                "11_join_anti",
                JoinKind::Anti,
                &l_uniq,
                &r_uniq,
                JoinOn::SameKeys(vec!["id".into()]),
                None,
            ),
        ];
        for (name, kind, lp, rp, on, suf) in join_specs {
            let plan = Plan::Join {
                kind,
                left: Box::new(Plan::SourceExpr(Box::new((*lp).clone()))),
                right: Box::new(Plan::SourceExpr(Box::new((*rp).clone()))),
                on,
                suffixes: suf.map(|(a, b)| (a.to_string(), b.to_string())),
            };
            cases.push((name, mk_console_prog(print_table(plan)), None));
        }

        // 12. JoinCardinality trap on left (public key)
        cases.push((
            "12_join_cardinality_trap_left_public",
            mk_console_prog(print_table(Plan::Join {
                kind: JoinKind::LeftOne,
                left: Box::new(Plan::SourceExpr(Box::new(l_dup))),
                right: Box::new(Plan::SourceExpr(Box::new(r_uniq))),
                on: JoinOn::SameKeys(vec!["id".into()]),
                suffixes: Some(("_l".into(), "_r".into())),
            })),
            None,
        ));
    }

    // 13. JoinCardinality trap on right with [pii] key (redacted!)
    {
        let sl = TableTy {
            cols: vec![
                col("ssn", ScalarTy::Text, ts(&["pii"])),
                col("dept", ScalarTy::Text, TagSet::empty()),
            ],
            ..TableTy::default()
        };
        let sr = TableTy {
            cols: vec![
                col("ssn", ScalarTy::Text, ts(&["pii"])),
                col("role", ScalarTy::Text, TagSet::empty()),
            ],
            ..TableTy::default()
        };
        let plan = Plan::Join {
            kind: JoinKind::InnerManyToOne,
            left: Box::new(Plan::SourceExpr(Box::new(Expr::TableLit {
                schema: sl,
                rows: vec![RowLit {
                    cells: vec![
                        Literal::Text("123-45-6789".into()),
                        Literal::Text("Eng".into()),
                    ],
                }],
            }))),
            right: Box::new(Plan::SourceExpr(Box::new(Expr::TableLit {
                schema: sr,
                rows: vec![
                    RowLit {
                        cells: vec![
                            Literal::Text("123-45-6789".into()),
                            Literal::Text("Staff".into()),
                        ],
                    },
                    RowLit {
                        cells: vec![
                            Literal::Text("123-45-6789".into()),
                            Literal::Text("Lead".into()),
                        ],
                    },
                ],
            }))),
            on: JoinOn::SameKeys(vec!["ssn".into()]),
            suffixes: None,
        };
        cases.push((
            "13_join_cardinality_trap_right_pii_redacted",
            mk_console_prog_with(vec![], vec![], ts(&["pii"]), print_table(plan)),
            Some("pii"),
        ));
    }

    // 14. Union + Distinct + Sort
    {
        let p1 = gen_base_table_plan(&mut rng, 6, 6);
        let p2 = gen_base_table_plan(&mut rng, 6, 6);
        let plan = Plan::Sort {
            input: Box::new(Plan::Distinct {
                input: Box::new(Plan::Union {
                    left: Box::new(p1),
                    right: Box::new(p2),
                }),
                cols: vec!["g".into(), "x".into()],
            }),
            keys: vec![("g".into(), SortDir::Asc), ("id".into(), SortDir::Asc)],
        };
        cases.push((
            "14_union_distinct_sort",
            mk_console_prog(print_table(plan)),
            None,
        ));
    }

    // 15. GroupBy + Summarize all 12 AggOps
    {
        let base = gen_base_table_plan(&mut rng, 12, 12);
        let plan = Plan::Summarize {
            input: Box::new(Plan::GroupBy {
                input: Box::new(base),
                keys: vec!["g".into()],
            }),
            aggs: vec![
                AggItem {
                    name: "c".into(),
                    op: AggOp::Count,
                    arg: None,
                },
                AggItem {
                    name: "cd".into(),
                    op: AggOp::CountDistinct,
                    arg: Some(RowExpr::Col("x".into())),
                },
                AggItem {
                    name: "si".into(),
                    op: AggOp::Sum,
                    arg: Some(RowExpr::Col("x".into())),
                },
                AggItem {
                    name: "sd".into(),
                    op: AggOp::Sum,
                    arg: Some(RowExpr::Col("d".into())),
                },
                AggItem {
                    name: "sf".into(),
                    op: AggOp::Sum,
                    arg: Some(RowExpr::Col("f".into())),
                },
                AggItem {
                    name: "mi".into(),
                    op: AggOp::Mean,
                    arg: Some(RowExpr::Col("x".into())),
                },
                AggItem {
                    name: "md".into(),
                    op: AggOp::Mean,
                    arg: Some(RowExpr::Col("d".into())),
                },
                AggItem {
                    name: "std".into(),
                    op: AggOp::Stddev,
                    arg: Some(RowExpr::Col("f".into())),
                },
                AggItem {
                    name: "var".into(),
                    op: AggOp::Variance,
                    arg: Some(RowExpr::Col("f".into())),
                },
                AggItem {
                    name: "med".into(),
                    op: AggOp::Median,
                    arg: Some(RowExpr::Col("f".into())),
                },
                AggItem {
                    name: "p75".into(),
                    op: AggOp::Percentile(Float64::from_f64(0.75)),
                    arg: Some(RowExpr::Col("f".into())),
                },
                AggItem {
                    name: "mn".into(),
                    op: AggOp::Min,
                    arg: Some(RowExpr::Col("x".into())),
                },
                AggItem {
                    name: "mx".into(),
                    op: AggOp::Max,
                    arg: Some(RowExpr::Col("x".into())),
                },
                AggItem {
                    name: "fst".into(),
                    op: AggOp::First,
                    arg: Some(RowExpr::Col("x".into())),
                },
                AggItem {
                    name: "lst".into(),
                    op: AggOp::Last,
                    arg: Some(RowExpr::Col("x".into())),
                },
            ],
            distinct_key: None,
        };
        cases.push((
            "15_summarize_all_12_agg_ops",
            mk_console_prog(print_table(plan)),
            None,
        ));
    }

    // 16. Summarize empty table (ungrouped & grouped)
    {
        let empty = Expr::TableLit {
            schema: base_table_schema(),
            rows: vec![],
        };
        let body = let_seq(
            "u",
            LTy::public(Ty::Unit),
            print_table(Plan::Summarize {
                input: Box::new(Plan::SourceExpr(Box::new(empty.clone()))),
                aggs: vec![
                    AggItem {
                        name: "n".into(),
                        op: AggOp::Count,
                        arg: None,
                    },
                    AggItem {
                        name: "m".into(),
                        op: AggOp::Mean,
                        arg: Some(RowExpr::Col("f".into())),
                    },
                ],
                distinct_key: None,
            }),
            print_table(Plan::Summarize {
                input: Box::new(Plan::GroupBy {
                    input: Box::new(Plan::SourceExpr(Box::new(empty))),
                    keys: vec!["g".into()],
                }),
                aggs: vec![AggItem {
                    name: "n".into(),
                    op: AggOp::Count,
                    arg: None,
                }],
                distinct_key: None,
            }),
        );
        cases.push(("16_summarize_empty", mk_console_prog(body), None));
    }

    // 17. Summarize Int sum right-fold overflow trap
    {
        let schema = TableTy {
            cols: vec![col("x", ScalarTy::Int, TagSet::empty())],
            ..TableTy::default()
        };
        let tbl = Expr::TableLit {
            schema,
            rows: vec![
                RowLit {
                    cells: vec![Literal::int(i64::MIN)],
                },
                RowLit {
                    cells: vec![Literal::int(5_000_000_000_000_000_000i64)],
                },
                RowLit {
                    cells: vec![Literal::int(5_000_000_000_000_000_000i64)],
                },
            ],
        };
        cases.push((
            "17_summarize_int_overflow",
            mk_console_prog(print_table(Plan::Summarize {
                input: Box::new(Plan::SourceExpr(Box::new(tbl))),
                aggs: vec![AggItem {
                    name: "s".into(),
                    op: AggOp::Sum,
                    arg: Some(RowExpr::Col("x".into())),
                }],
                distinct_key: None,
            })),
            None,
        ));
    }

    // 18 & 19. SuppressSmallGroups (Drop & MaskComplementary with tie-breaking)
    {
        let schema = TableTy {
            cols: vec![
                col("pid", ScalarTy::Int, ts(&["pii"])),
                col("dept", ScalarTy::Text, TagSet::empty()),
                col("score", ScalarTy::Int, ts(&["ferpa"])),
            ],
            ..TableTy::default()
        };
        let mut rows = vec![
            RowLit {
                cells: vec![Literal::int(1), Literal::Text("A".into()), Literal::int(90)],
            },
            RowLit {
                cells: vec![Literal::int(2), Literal::Text("B".into()), Literal::int(80)],
            },
        ];
        for i in 0..5 {
            rows.push(RowLit {
                cells: vec![
                    Literal::int(10 + i),
                    Literal::Text("C1".into()),
                    Literal::int(70 + i),
                ],
            });
            rows.push(RowLit {
                cells: vec![
                    Literal::int(20 + i),
                    Literal::Text("C2".into()),
                    Literal::int(60 + i),
                ],
            });
        }
        let tbl = Expr::TableLit { schema, rows };
        for (name, mode) in [
            ("18_suppress_small_groups_drop", SuppressMode::Drop),
            (
                "19_suppress_small_groups_mask_complementary",
                SuppressMode::MaskComplementary,
            ),
        ] {
            let plan = Plan::SuppressSmallGroups {
                input: Box::new(Plan::Summarize {
                    input: Box::new(Plan::GroupBy {
                        input: Box::new(Plan::SourceExpr(Box::new(tbl.clone()))),
                        keys: vec!["dept".into()],
                    }),
                    aggs: vec![
                        AggItem {
                            name: "n".into(),
                            op: AggOp::Count,
                            arg: None,
                        },
                        AggItem {
                            name: "avg".into(),
                            op: AggOp::Mean,
                            arg: Some(RowExpr::Col("score".into())),
                        },
                    ],
                    distinct_key: Some("pid".into()),
                }),
                min_k: BigInt::from(5u64),
                distinct_by: Some("pid".into()),
                mode,
            };
            cases.push((name, mk_console_prog(print_table(plan)), None));
        }
    }

    // 20. Window all 6 WindowFns
    {
        let base = gen_base_table_plan(&mut rng, 10, 10);
        let plan = Plan::Window {
            input: Box::new(base),
            items: vec![
                WindowItem {
                    name: "rn".into(),
                    win_fn: WindowFn::RowNumber,
                    over: vec!["g".into()],
                    order: vec![("x".into(), SortDir::Asc), ("id".into(), SortDir::Asc)],
                },
                WindowItem {
                    name: "rk".into(),
                    win_fn: WindowFn::Rank { col: "x".into() },
                    over: vec!["g".into()],
                    order: vec![("x".into(), SortDir::Asc)],
                },
                WindowItem {
                    name: "lg".into(),
                    win_fn: WindowFn::Lag {
                        col: "x".into(),
                        offset: BigInt::from(1u64),
                    },
                    over: vec!["g".into()],
                    order: vec![("id".into(), SortDir::Asc)],
                },
                WindowItem {
                    name: "ld".into(),
                    win_fn: WindowFn::Lead {
                        col: "x".into(),
                        offset: BigInt::from(1u64),
                    },
                    over: vec!["g".into()],
                    order: vec![("id".into(), SortDir::Asc)],
                },
                WindowItem {
                    name: "rs".into(),
                    win_fn: WindowFn::RunningSum { col: "x".into() },
                    over: vec!["g".into()],
                    order: vec![("id".into(), SortDir::Asc)],
                },
                WindowItem {
                    name: "rm".into(),
                    win_fn: WindowFn::RollingMean {
                        col: "f".into(),
                        window_size: BigInt::from(2u64),
                    },
                    over: vec!["g".into()],
                    order: vec![("id".into(), SortDir::Asc)],
                },
            ],
        };
        cases.push((
            "20_window_all_6_fns",
            mk_console_prog(print_table(plan)),
            None,
        ));
    }

    // 21. Window RunningSum overflow trap
    {
        let schema = TableTy {
            cols: vec![
                col("p", ScalarTy::Text, TagSet::empty()),
                col("v", ScalarTy::Int, TagSet::empty()),
            ],
            ..TableTy::default()
        };
        let tbl = Expr::TableLit {
            schema,
            rows: vec![
                RowLit {
                    cells: vec![Literal::Text("A".into()), Literal::int(i64::MAX)],
                },
                RowLit {
                    cells: vec![Literal::Text("A".into()), Literal::int(1)],
                },
            ],
        };
        cases.push((
            "21_window_running_sum_overflow",
            mk_console_prog(print_table(Plan::Window {
                input: Box::new(Plan::SourceExpr(Box::new(tbl))),
                items: vec![WindowItem {
                    name: "rs".into(),
                    win_fn: WindowFn::RunningSum { col: "v".into() },
                    over: vec!["p".into()],
                    order: vec![("v".into(), SortDir::Desc)],
                }],
            })),
            None,
        ));
    }

    // 22. FillGaps
    {
        let schema = TableTy {
            cols: vec![
                col("grp", ScalarTy::Text, TagSet::empty()),
                col("t", ScalarTy::Int, TagSet::empty()),
                col("v", ScalarTy::Int, TagSet::empty()),
            ],
            ..TableTy::default()
        };
        let tbl = Expr::TableLit {
            schema,
            rows: vec![
                RowLit {
                    cells: vec![Literal::Text("A".into()), Literal::int(1), Literal::int(10)],
                },
                RowLit {
                    cells: vec![Literal::Text("A".into()), Literal::int(4), Literal::int(40)],
                },
                RowLit {
                    cells: vec![Literal::Text("B".into()), Literal::int(2), Literal::int(20)],
                },
                RowLit {
                    cells: vec![Literal::Text("B".into()), Literal::int(5), Literal::int(50)],
                },
            ],
        };
        cases.push((
            "22_fill_gaps",
            mk_console_prog(print_table(Plan::FillGaps {
                input: Box::new(Plan::SourceExpr(Box::new(tbl))),
                col: "t".into(),
                step_micros: BigInt::from(1),
                over: vec!["grp".into()],
                fill: vec![("v".into(), Literal::int(0))],
            })),
            None,
        ));
    }

    // 23 & 24. PivotWider & Crosstab
    {
        let schema = TableTy {
            cols: vec![
                col("id", ScalarTy::Text, TagSet::empty()),
                col("k", ScalarTy::Text, TagSet::empty()),
                col("v", ScalarTy::Int, TagSet::empty()),
            ],
            ..TableTy::default()
        };
        let tbl = Expr::TableLit {
            schema,
            rows: vec![
                RowLit {
                    cells: vec![
                        Literal::Text("r1".into()),
                        Literal::Text("q1".into()),
                        Literal::int(10),
                    ],
                },
                RowLit {
                    cells: vec![
                        Literal::Text("r1".into()),
                        Literal::Text("q2".into()),
                        Literal::int(20),
                    ],
                },
                RowLit {
                    cells: vec![
                        Literal::Text("r2".into()),
                        Literal::Text("q1".into()),
                        Literal::int(30),
                    ],
                },
            ],
        };
        cases.push((
            "23_pivot_wider",
            mk_console_prog(print_table(Plan::PivotWider {
                input: Box::new(Plan::SourceExpr(Box::new(tbl.clone()))),
                names_from: "k".into(),
                values_from: "v".into(),
                static_cols: vec!["q1".into(), "q2".into(), "q3".into()],
                fill: Literal::int(0),
            })),
            None,
        ));
        cases.push((
            "24_crosstab",
            Program {
                funs: vec![FunDecl {
                    name: "main".into(),
                    kind: FunKind::Function,
                    is_pure: false,
                    params: vec![],
                    pc: TagSet::empty(),
                    ret: LTy::public(Ty::DynamicTable(TagSet::empty())),
                    body: Expr::Rel(Box::new(Plan::Crosstab {
                        input: Box::new(Plan::SourceExpr(Box::new(tbl))),
                        rows_col: "id".into(),
                        cols_col: "k".into(),
                        values_col: "v".into(),
                        fill: Literal::int(0),
                    })),
                }],
                entry: Some("main".into()),
                ..Program::default()
            },
            None,
        ));
    }

    // 25. Redact & Pseudonymize (with Unicode!)
    {
        let schema = TableTy {
            cols: vec![
                col("email", ScalarTy::Text, ts(&["pii"])),
                col("dept", ScalarTy::Text, TagSet::empty()),
            ],
            ..TableTy::default()
        };
        let tbl = Expr::TableLit {
            schema,
            rows: vec![
                RowLit {
                    cells: vec![
                        Literal::Text("josé@uni.edu".into()),
                        Literal::Text("CS".into()),
                    ],
                },
                RowLit {
                    cells: vec![
                        Literal::Text("alice@uni.edu".into()),
                        Literal::Text("Math".into()),
                    ],
                },
            ],
        };
        cases.push((
            "25_redact_and_pseudonymize",
            Program {
                funs: vec![FunDecl {
                    name: "main".into(),
                    kind: FunKind::Function,
                    is_pure: false,
                    params: vec![
                        (
                            "salt".into(),
                            LTy::new(Ty::Secret("k1".into()), ts(&["secret"])),
                        ),
                        ("c".into(), LTy::public(Ty::Console(TagSet::empty()))),
                    ],
                    pc: TagSet::empty(),
                    ret: LTy::public(Ty::Unit),
                    body: let_seq(
                        "p1",
                        LTy::public(Ty::Unit),
                        print_table(Plan::Redact {
                            input: Box::new(Plan::SourceExpr(Box::new(tbl.clone()))),
                            col: "email".into(),
                            replacement: "[REDACTED]".into(),
                        }),
                        print_table(Plan::Pseudonymize {
                            input: Box::new(Plan::SourceExpr(Box::new(tbl))),
                            col: "email".into(),
                            secret: Box::new(Expr::Var("salt".into())),
                        }),
                    ),
                }],
                entry: Some("main".into()),
                ..Program::default()
            },
            None,
        ));
    }

    // 26. Decimal arithmetic & negative Euclidean division in Derive + Summarize
    {
        let schema = TableTy {
            cols: vec![
                col("g", ScalarTy::Text, TagSet::empty()),
                col("a", ScalarTy::Decimal, TagSet::empty()),
                col("b", ScalarTy::Decimal, TagSet::empty()),
            ],
            ..TableTy::default()
        };
        let tbl = Expr::TableLit {
            schema,
            rows: vec![
                RowLit {
                    cells: vec![
                        Literal::Text("X".into()),
                        Literal::decimal(-DEC_SCALE),
                        Literal::decimal(3 * DEC_SCALE),
                    ],
                },
                RowLit {
                    cells: vec![
                        Literal::Text("X".into()),
                        Literal::decimal(7 * DEC_SCALE),
                        Literal::decimal(-2 * DEC_SCALE),
                    ],
                },
                RowLit {
                    cells: vec![
                        Literal::Text("Y".into()),
                        Literal::decimal(-5 * DEC_SCALE),
                        Literal::decimal(-2 * DEC_SCALE),
                    ],
                },
            ],
        };
        let plan = Plan::Summarize {
            input: Box::new(Plan::GroupBy {
                input: Box::new(Plan::Derive {
                    input: Box::new(Plan::SourceExpr(Box::new(tbl))),
                    items: vec![DeriveItem::ColExpr {
                        name: "q".into(),
                        expr: Box::new(RowExpr::Prim {
                            op: PrimOp::DivDec,
                            args: vec![RowExpr::Col("a".into()), RowExpr::Col("b".into())],
                        }),
                    }],
                }),
                keys: vec!["g".into()],
            }),
            aggs: vec![
                AggItem {
                    name: "sq".into(),
                    op: AggOp::Sum,
                    arg: Some(RowExpr::Col("q".into())),
                },
                AggItem {
                    name: "mq".into(),
                    op: AggOp::Mean,
                    arg: Some(RowExpr::Col("q".into())),
                },
            ],
            distinct_key: None,
        };
        cases.push((
            "26_decimal_arith_and_neg_div",
            mk_console_prog(print_table(plan)),
            None,
        ));
    }

    // 27. Filter pushdown + fusion with conditional DivByZero trap
    {
        let schema = TableTy {
            cols: vec![
                col("id", ScalarTy::Int, TagSet::empty()),
                col("d", ScalarTy::Int, TagSet::empty()),
            ],
            ..TableTy::default()
        };
        let tbl = Expr::TableLit {
            schema,
            rows: (0..8)
                .map(|i| RowLit {
                    cells: vec![Literal::int(i), Literal::int(i % 3)],
                })
                .collect(),
        };
        let plan = Plan::Filter {
            input: Box::new(Plan::Filter {
                input: Box::new(Plan::SourceExpr(Box::new(tbl))),
                pred: RowExpr::Prim {
                    op: PrimOp::Ne,
                    args: vec![RowExpr::Col("d".into()), RowExpr::Lit(Literal::int(0))],
                },
            }),
            pred: RowExpr::Prim {
                op: PrimOp::Gt,
                args: vec![
                    RowExpr::Prim {
                        op: PrimOp::DivInt,
                        args: vec![RowExpr::Lit(Literal::int(12)), RowExpr::Col("d".into())],
                    },
                    RowExpr::Lit(Literal::int(5)),
                ],
            },
        };
        cases.push((
            "27_filter_fusion_short_circuit_div_guard",
            mk_console_prog(print_table(plan)),
            None,
        ));
    }

    // 28. SourceDB empty fallback (matches CLI danacore empty realDBTables)
    {
        let schema = TableTy {
            cols: vec![col("id", ScalarTy::Int, TagSet::empty())],
            ..TableTy::default()
        };
        cases.push((
            "28_source_db_empty_fallback",
            Program {
                funs: vec![FunDecl {
                    name: "main".into(),
                    kind: FunKind::Function,
                    is_pure: false,
                    params: vec![
                        ("db".into(), LTy::public(Ty::ReadDB("wh".into()))),
                        ("c".into(), LTy::public(Ty::Console(TagSet::empty()))),
                    ],
                    pc: TagSet::empty(),
                    ret: LTy::public(Ty::Unit),
                    body: print_table(Plan::SourceDB {
                        cap: Box::new(Expr::Var("db".into())),
                        table_name: "empty_tbl".into(),
                        schema,
                    }),
                }],
                entry: Some("main".into()),
                ..Program::default()
            },
            None,
        ));
    }

    cases
}

#[test]
fn triple_parity_lean_danacore_vs_oracle_vs_vm() -> Result<(), String> {
    let lean_bin = lean_danacore_bin();
    let corpus = build_triple_parity_corpus();
    assert!(
        corpus.len() >= 25,
        "expected >= 25 curated triple-parity programs, got {}",
        corpus.len()
    );

    let cfg_seq_unopt = VmConfig {
        batch_size: 4,
        parallel_threshold_rows: usize::MAX,
        max_threads: Some(1),
        optimize: false,
        ..VmConfig::sequential_unoptimized()
    };
    let cfg_seq_opt = VmConfig {
        batch_size: 4,
        parallel_threshold_rows: usize::MAX,
        max_threads: Some(1),
        optimize: true,
        ..VmConfig::sequential_optimized()
    };
    let cfg_par_opt = VmConfig {
        batch_size: 4,
        parallel_threshold_rows: 4,
        max_threads: Some(4),
        optimize: true,
        ..VmConfig::parallel_optimized(4, 4)
    };

    for (name, prog, allow_export) in &corpus {
        check_program(prog).map_err(|e| format!("[{name}] check_program failed: {}", e.message))?;
        let (opt_prog, _) = optimize_program(prog);
        check_program(&opt_prog)
            .map_err(|e| format!("[{name}] optimized check_program failed: {}", e.message))?;

        let wire = print_program(prog);
        let tmp = TempCoreFile::new(name, &wire)?;
        let path_str = tmp
            .path
            .to_str()
            .ok_or_else(|| format!("[{name}] non-utf8 temp path"))?;

        let mut args = vec!["run", path_str, "--fuel", "20000"];
        if let Some(ae) = allow_export {
            args.push("--allow-export");
            args.push(ae);
        }
        let lean_out = Command::new(lean_bin)
            .args(&args)
            .output()
            .map_err(|e| format!("[{name}] execute danacore: {e}"))?;
        let lean_stdout = String::from_utf8_lossy(&lean_out.stdout).into_owned();
        let lean_stderr = String::from_utf8_lossy(&lean_out.stderr).into_owned();

        let mut world = World::default();
        if let Some(ae) = allow_export {
            world.runtime_allow_export = TagSet::of_list(ae.split(',').map(String::from).collect());
        }

        let oracle_rep = run_program(20_000, prog, world.clone())
            .map_err(|e| format!("[{name}] oracle run err: {e:?}"))?;
        let vm_su = run_core_program_vm(20_000, prog, world.clone(), &cfg_seq_unopt)
            .map_err(|e| format!("[{name}] vm seq unopt err: {e:?}"))?;
        let vm_so = run_core_program_vm(20_000, prog, world.clone(), &cfg_seq_opt)
            .map_err(|e| format!("[{name}] vm seq opt err: {e:?}"))?;
        let vm_po = run_core_program_vm(20_000, prog, world, &cfg_par_opt)
            .map_err(|e| format!("[{name}] vm par opt err: {e:?}"))?;

        let s_oracle = print_report(&oracle_rep);
        let s_su = print_report(&vm_su);
        let s_so = print_report(&vm_so);
        let s_po = print_report(&vm_po);

        assert_eq!(
            lean_stdout, s_oracle,
            "[{name}] Lean vs Oracle mismatch\nlean stderr: {lean_stderr}"
        );
        assert_eq!(lean_stdout, s_su, "[{name}] Lean vs VM(seq_unopt) mismatch");
        assert_eq!(lean_stdout, s_so, "[{name}] Lean vs VM(seq_opt) mismatch");
        assert_eq!(lean_stdout, s_po, "[{name}] Lean vs VM(par_opt) mismatch");
    }

    eprintln!(
        "[triple_parity] {} curated Core IR programs matched byte-for-byte across Lean danacore, Rust oracle, and Rust VM (seq_unopt/seq_opt/par_opt)",
        corpus.len()
    );
    Ok(())
}

// ===========================================================================
// Optimizer Correctness, Stop/Cardinality Safety Barriers & Plan Explainer
// ===========================================================================

#[test]
fn optimizer_rewrites_stop_safety_and_explain() -> Result<(), String> {
    let schema = TableTy {
        cols: vec![
            col("id", ScalarTy::Int, TagSet::empty()),
            col("x", ScalarTy::Int, TagSet::empty()),
            col("y", ScalarTy::Int, TagSet::empty()),
        ],
        ..TableTy::default()
    };
    let src = Expr::TableLit {
        schema: schema.clone(),
        rows: vec![
            RowLit {
                cells: vec![Literal::int(1), Literal::int(0), Literal::int(10)],
            },
            RowLit {
                cells: vec![Literal::int(2), Literal::int(5), Literal::int(20)],
            },
            RowLit {
                cells: vec![Literal::int(3), Literal::int(10), Literal::int(30)],
            },
        ],
    };

    // 1. Trigger all 5 OptStats counters: filters_fused, predicates_pushed,
    //    derive_items_pruned, dead_ops_eliminated, limits_folded.
    let rich_plan = Plan::Limit {
        input: Box::new(Plan::Limit {
            input: Box::new(Plan::Select {
                input: Box::new(Plan::Select {
                    input: Box::new(Plan::Filter {
                        input: Box::new(Plan::Filter {
                            input: Box::new(Plan::Rename {
                                input: Box::new(Plan::Drop {
                                    input: Box::new(Plan::Derive {
                                        input: Box::new(Plan::SourceExpr(Box::new(src.clone()))),
                                        items: vec![
                                            DeriveItem::ColExpr {
                                                name: "dead_col".into(),
                                                expr: Box::new(RowExpr::Prim {
                                                    op: PrimOp::Eq,
                                                    args: vec![
                                                        RowExpr::Col("x".into()),
                                                        RowExpr::Lit(Literal::int(0)),
                                                    ],
                                                }),
                                            },
                                            DeriveItem::ColExpr {
                                                name: "alive_col".into(),
                                                expr: Box::new(RowExpr::Col("y".into())),
                                            },
                                        ],
                                    }),
                                    cols: vec![],
                                }),
                                pairs: vec![("x2".into(), "x".into())],
                            }),
                            pred: RowExpr::Prim {
                                op: PrimOp::Ge,
                                args: vec![
                                    RowExpr::Col("x2".into()),
                                    RowExpr::Lit(Literal::int(0)),
                                ],
                            },
                        }),
                        pred: RowExpr::Prim {
                            op: PrimOp::Le,
                            args: vec![RowExpr::Col("x2".into()), RowExpr::Lit(Literal::int(100))],
                        },
                    }),
                    cols: vec!["id".into(), "x2".into(), "alive_col".into()],
                }),
                cols: vec!["id".into(), "alive_col".into()],
            }),
            n: BigInt::from(10u64),
        }),
        n: BigInt::from(2u64),
    };

    let empty_prog = Program::default();
    let (opt_plan, stats) = optimize_plan(&rich_plan, &empty_prog);
    assert!(
        stats.filters_fused > 0,
        "expected filters_fused > 0, got {stats:?}"
    );
    assert!(
        stats.predicates_pushed > 0,
        "expected predicates_pushed > 0, got {stats:?}"
    );
    assert!(
        stats.derive_items_pruned > 0,
        "expected derive_items_pruned > 0, got {stats:?}"
    );
    assert!(
        stats.dead_ops_eliminated > 0,
        "expected dead_ops_eliminated > 0, got {stats:?}"
    );
    assert!(
        stats.limits_folded > 0,
        "expected limits_folded > 0, got {stats:?}"
    );

    // Verify `explain_plan` renders readable logical & optimized trees.
    let logical_tree = explain_plan(&rich_plan);
    let optimized_tree = explain_plan(&opt_plan);
    assert!(logical_tree.contains("Limit(10)"), "{logical_tree}");
    assert!(logical_tree.contains("dead_col"), "{logical_tree}");
    assert!(optimized_tree.contains("Limit(2)"), "{optimized_tree}");
    assert!(!optimized_tree.contains("Limit(10)"), "{optimized_tree}");
    assert!(!optimized_tree.contains("dead_col"), "{optimized_tree}");

    // Verify `explain_exec_plan` renders readable ExecPlan tree too.
    let exec_plan = ExecPlan::Limit {
        input: Box::new(ExecPlan::Derive {
            input: Box::new(ExecPlan::Filter {
                input: Box::new(ExecPlan::SourceExpr(Box::new(ExecExpr::Var("t".into())))),
                pred: ExecRowExpr::Prim {
                    op: ExecPrimOp::Core(PrimOp::Gt),
                    args: vec![
                        ExecRowExpr::Col("x".into()),
                        ExecRowExpr::Lit(Literal::int(0)),
                    ],
                },
            }),
            items: vec![ExecDeriveItem::ColExpr {
                name: "z".into(),
                expr: Box::new(ExecRowExpr::Col("x".into())),
                spec: ColSpec {
                    name: "z".into(),
                    ty: ScalarTy::Int,
                    tags: TagSet::empty(),
                    bucketed: false,
                    agg_kind: AggKind::Raw,
                },
            }],
        }),
        n: BigInt::from(5u64),
    };
    let exec_tree = explain_exec_plan(&exec_plan);
    assert!(exec_tree.contains("Limit(5)"), "{exec_tree}");
    assert!(exec_tree.contains("Derive([z])"), "{exec_tree}");
    assert!(exec_tree.contains("Filter"), "{exec_tree}");
    assert!(exec_tree.contains("SourceExpr"), "{exec_tree}");

    // 2. Stop safety barrier: partial/trapping predicate (`100 / .x > 0`) MUST NOT be pushed
    //    across `Sort`, `Limit`, or `Derive`.
    let trap_pred = RowExpr::Prim {
        op: PrimOp::Gt,
        args: vec![
            RowExpr::Prim {
                op: PrimOp::DivInt,
                args: vec![RowExpr::Lit(Literal::int(100)), RowExpr::Col("x".into())],
            },
            RowExpr::Lit(Literal::int(0)),
        ],
    };

    // 2a. Filter(trap) over Sort: must stay above Sort.
    let trap_over_sort = Plan::Filter {
        input: Box::new(Plan::Sort {
            input: Box::new(Plan::SourceExpr(Box::new(src.clone()))),
            keys: vec![("x".into(), SortDir::Desc)],
        }),
        pred: trap_pred.clone(),
    };
    let (opt_tos, tos_stats) = optimize_plan(&trap_over_sort, &empty_prog);
    assert_eq!(
        tos_stats.predicates_pushed, 0,
        "partial predicate must NOT be pushed across Sort"
    );
    assert!(matches!(opt_tos, Plan::Filter { .. }));

    // 2b. Filter(trap) over Limit(1) on Desc-sorted rows: row 0 has x=10, row 2 has x=0.
    //     Pushing below Limit would trigger DivByZero! With barrier, it succeeds cleanly!
    let trap_over_limit = Plan::Filter {
        input: Box::new(Plan::Limit {
            input: Box::new(Plan::Sort {
                input: Box::new(Plan::SourceExpr(Box::new(src.clone()))),
                keys: vec![("x".into(), SortDir::Desc)],
            }),
            n: BigInt::from(1u64),
        }),
        pred: trap_pred,
    };
    let prog_limit = mk_console_prog(print_table(trap_over_limit));
    let r_oracle =
        run_program(10_000, &prog_limit, World::default()).map_err(|e| format!("{e:?}"))?;
    let r_vm = run_core_program_vm(
        10_000,
        &prog_limit,
        World::default(),
        &VmConfig::sequential_optimized(),
    )
    .map_err(|e| format!("{e:?}"))?;
    assert_eq!(r_oracle.status, ExitStatus::Ok);
    assert_eq!(print_report(&r_oracle), print_report(&r_vm));

    // 2c. Total Filter over trapping Derive: trapping Derive on row 0 (x=0) MUST STILL fire!
    let filter_over_trap_derive = Plan::Filter {
        input: Box::new(Plan::Derive {
            input: Box::new(Plan::SourceExpr(Box::new(src))),
            items: vec![DeriveItem::ColExpr {
                name: "q".into(),
                expr: Box::new(RowExpr::Prim {
                    op: PrimOp::DivInt,
                    args: vec![RowExpr::Lit(Literal::int(100)), RowExpr::Col("x".into())],
                }),
            }],
        }),
        pred: RowExpr::Prim {
            op: PrimOp::Gt,
            args: vec![RowExpr::Col("id".into()), RowExpr::Lit(Literal::int(1))],
        },
    };
    let (opt_ftd, ftd_stats) = optimize_plan(&filter_over_trap_derive, &empty_prog);
    assert_eq!(
        ftd_stats.predicates_pushed, 0,
        "Filter must NOT push below trapping Derive"
    );
    assert!(matches!(opt_ftd, Plan::Filter { .. }));
    let prog_ftd = mk_console_prog(print_table(filter_over_trap_derive));
    let ftd_oracle =
        run_program(10_000, &prog_ftd, World::default()).map_err(|e| format!("{e:?}"))?;
    let ftd_vm = run_core_program_vm(
        10_000,
        &prog_ftd,
        World::default(),
        &VmConfig::sequential_optimized(),
    )
    .map_err(|e| format!("{e:?}"))?;
    assert_eq!(ftd_oracle.status, ExitStatus::Stopped);
    assert_eq!(print_report(&ftd_oracle), print_report(&ftd_vm));

    // 3. Cardinality safety barrier: Filter MUST NOT push below uniqueness-checked Join right side!
    //    `InnerManyToOne` checks uniqueness of right key `id`. Right has duplicate `id=1` with
    //    `rv=10` and `rv=20`. Outer filter `.rv > 15` would drop one duplicate if pushed,
    //    falsely hiding the `JoinCardinality` stop!
    let jl_schema = TableTy {
        cols: vec![
            col("id", ScalarTy::Int, TagSet::empty()),
            col("lv", ScalarTy::Int, TagSet::empty()),
        ],
        ..TableTy::default()
    };
    let jr_schema = TableTy {
        cols: vec![
            col("id", ScalarTy::Int, TagSet::empty()),
            col("rv", ScalarTy::Int, TagSet::empty()),
        ],
        ..TableTy::default()
    };
    let join_dup_right = Plan::Filter {
        input: Box::new(Plan::Join {
            kind: JoinKind::InnerManyToOne,
            left: Box::new(Plan::SourceExpr(Box::new(Expr::TableLit {
                schema: jl_schema,
                rows: vec![RowLit {
                    cells: vec![Literal::int(1), Literal::int(100)],
                }],
            }))),
            right: Box::new(Plan::SourceExpr(Box::new(Expr::TableLit {
                schema: jr_schema,
                rows: vec![
                    RowLit {
                        cells: vec![Literal::int(1), Literal::int(10)],
                    },
                    RowLit {
                        cells: vec![Literal::int(1), Literal::int(20)],
                    },
                ],
            }))),
            on: JoinOn::SameKeys(vec!["id".into()]),
            suffixes: None,
        }),
        pred: RowExpr::Prim {
            op: PrimOp::Gt,
            args: vec![RowExpr::Col("rv".into()), RowExpr::Lit(Literal::int(15))],
        },
    };
    let (opt_jdr, jdr_stats) = optimize_plan(&join_dup_right, &empty_prog);
    assert_eq!(
        jdr_stats.predicates_pushed, 0,
        "Filter on right col must NOT push into uniqueness-checked InnerManyToOne right side"
    );
    assert!(matches!(opt_jdr, Plan::Filter { .. }));
    let prog_jdr = mk_console_prog(print_table(join_dup_right));
    let jdr_oracle =
        run_program(10_000, &prog_jdr, World::default()).map_err(|e| format!("{e:?}"))?;
    let jdr_vm = run_core_program_vm(
        10_000,
        &prog_jdr,
        World::default(),
        &VmConfig::parallel_optimized(1, 4),
    )
    .map_err(|e| format!("{e:?}"))?;
    assert_eq!(jdr_oracle.status, ExitStatus::Stopped);
    assert!(
        jdr_oracle
            .diagnostic
            .as_deref()
            .is_some_and(|d| d.contains("duplicate key")),
        "expected JoinCardinality stop, got {:?}",
        jdr_oracle.diagnostic
    );
    assert_eq!(print_report(&jdr_oracle), print_report(&jdr_vm));

    Ok(())
}

// ===========================================================================
// Large Multi-Batch (12,000 rows) Parallel vs. Sequential vs. Oracle Parity
// + Deterministic Earliest-Row Trap Ordering Across Parallel Workers
// ===========================================================================

#[test]
fn large_multibatch_parallel_vs_sequential_parity() -> Result<(), String> {
    const N_ROWS: usize = 12_000;
    const { assert!(N_ROWS >= BATCH_SIZE * 5) };

    let fact_schema = TableTy {
        cols: vec![
            col("row_id", ScalarTy::Int, TagSet::empty()),
            col("dept_id", ScalarTy::Int, TagSet::empty()),
            col("qty", ScalarTy::Int, TagSet::empty()),
            col("amt", ScalarTy::Decimal, TagSet::empty()),
        ],
        ..TableTy::default()
    };
    let dim_schema = TableTy {
        cols: vec![
            col("dept_id", ScalarTy::Int, TagSet::empty()),
            col("region", ScalarTy::Text, TagSet::empty()),
        ],
        ..TableTy::default()
    };

    let mut fact_rows = Vec::with_capacity(N_ROWS);
    for i in 0..N_ROWS {
        let qty = if i.is_multiple_of(10) {
            0
        } else {
            (i % 7) as i64 + 1
        };
        let amt = ((i % 97) as i128 + 1) * DEC_SCALE;
        fact_rows.push(RowLit {
            cells: vec![
                Literal::int(i as i64),
                Literal::int((i % 16) as i64),
                Literal::int(qty),
                Literal::decimal(amt),
            ],
        });
    }
    let dim_rows: Vec<RowLit> = (0..16)
        .map(|d| RowLit {
            cells: vec![Literal::int(d), Literal::Text(format!("reg_{:02}", d % 8))],
        })
        .collect();

    let plan = Plan::Sort {
        input: Box::new(Plan::Window {
            input: Box::new(Plan::Summarize {
                input: Box::new(Plan::GroupBy {
                    input: Box::new(Plan::Join {
                        kind: JoinKind::InnerManyToOne,
                        left: Box::new(Plan::Derive {
                            input: Box::new(Plan::Filter {
                                input: Box::new(Plan::SourceExpr(Box::new(Expr::TableLit {
                                    schema: fact_schema,
                                    rows: fact_rows,
                                }))),
                                pred: RowExpr::Prim {
                                    op: PrimOp::Gt,
                                    args: vec![
                                        RowExpr::Col("qty".into()),
                                        RowExpr::Lit(Literal::int(0)),
                                    ],
                                },
                            }),
                            items: vec![DeriveItem::ColExpr {
                                name: "net".into(),
                                expr: Box::new(RowExpr::CallPure {
                                    fn_name: "net_dec_udf".into(),
                                    args: vec![
                                        RowExpr::Col("amt".into()),
                                        RowExpr::Lit(Literal::decimal(DEC_SCALE / 10)),
                                    ],
                                }),
                            }],
                        }),
                        right: Box::new(Plan::SourceExpr(Box::new(Expr::TableLit {
                            schema: dim_schema,
                            rows: dim_rows,
                        }))),
                        on: JoinOn::SameKeys(vec!["dept_id".into()]),
                        suffixes: None,
                    }),
                    keys: vec!["region".into()],
                }),
                aggs: vec![
                    AggItem {
                        name: "cnt".into(),
                        op: AggOp::Count,
                        arg: None,
                    },
                    AggItem {
                        name: "total_net".into(),
                        op: AggOp::Sum,
                        arg: Some(RowExpr::Col("net".into())),
                    },
                    AggItem {
                        name: "avg_net".into(),
                        op: AggOp::Mean,
                        arg: Some(RowExpr::Col("net".into())),
                    },
                    AggItem {
                        name: "min_qty".into(),
                        op: AggOp::Min,
                        arg: Some(RowExpr::Col("qty".into())),
                    },
                    AggItem {
                        name: "max_qty".into(),
                        op: AggOp::Max,
                        arg: Some(RowExpr::Col("qty".into())),
                    },
                ],
                distinct_key: None,
            }),
            items: vec![
                WindowItem {
                    name: "rn".into(),
                    win_fn: WindowFn::RowNumber,
                    over: vec![],
                    order: vec![("region".into(), SortDir::Asc)],
                },
                WindowItem {
                    name: "cum_net".into(),
                    win_fn: WindowFn::RunningSum {
                        col: "total_net".into(),
                    },
                    over: vec![],
                    order: vec![("region".into(), SortDir::Asc)],
                },
            ],
        }),
        keys: vec![("region".into(), SortDir::Asc)],
    };

    let prog = mk_console_prog_with(
        vec![],
        pure_udf_non_recursive_funs(),
        TagSet::empty(),
        print_table(plan),
    );
    check_program(&prog)
        .map_err(|e| format!("large pipeline check_program failed: {}", e.message))?;

    let rep_oracle =
        run_program(200_000, &prog, World::default()).map_err(|e| format!("oracle: {e:?}"))?;
    let rep_seq = run_core_program_vm(
        200_000,
        &prog,
        World::default(),
        &VmConfig::sequential_optimized(),
    )
    .map_err(|e| format!("vm_seq: {e:?}"))?;
    let rep_par = run_core_program_vm(
        200_000,
        &prog,
        World::default(),
        &VmConfig::parallel_optimized(BATCH_SIZE, 4),
    )
    .map_err(|e| format!("vm_par: {e:?}"))?;

    assert_eq!(rep_oracle.status, ExitStatus::Ok);
    let s_o = print_report(&rep_oracle);
    let s_s = print_report(&rep_seq);
    let s_p = print_report(&rep_par);
    assert_eq!(s_o, s_s, "12k-row oracle vs sequential VM mismatch");
    assert_eq!(s_o, s_p, "12k-row oracle vs parallel VM mismatch");

    // Deterministic earliest-row trap test across parallel workers:
    // Row 9,500 triggers `DivByZero`, while row 11,000 triggers `IntOverflow`!
    // Even if the thread handling batch 5 (row 11,000) finishes before the thread handling
    // batch 4 (row 9,500), parallel VM MUST report row 9,500's `DivByZero` deterministically!
    let trap_schema = TableTy {
        cols: vec![
            col("i", ScalarTy::Int, TagSet::empty()),
            col("d", ScalarTy::Int, TagSet::empty()),
            col("big", ScalarTy::Int, TagSet::empty()),
        ],
        ..TableTy::default()
    };
    let trap_rows: Vec<RowLit> = (0..N_ROWS)
        .map(|i| {
            let d = if i == 9_500 { 0 } else { 1 };
            let big = if i == 11_000 { i64::MAX } else { 1 };
            RowLit {
                cells: vec![Literal::int(i as i64), Literal::int(d), Literal::int(big)],
            }
        })
        .collect();
    let trap_plan = Plan::Derive {
        input: Box::new(Plan::SourceExpr(Box::new(Expr::TableLit {
            schema: trap_schema,
            rows: trap_rows,
        }))),
        items: vec![DeriveItem::ColExpr {
            name: "res".into(),
            expr: Box::new(RowExpr::Prim {
                op: PrimOp::AddInt,
                args: vec![
                    RowExpr::Prim {
                        op: PrimOp::DivInt,
                        args: vec![RowExpr::Lit(Literal::int(100)), RowExpr::Col("d".into())],
                    },
                    RowExpr::Col("big".into()),
                ],
            }),
        }],
    };
    let trap_prog = mk_console_prog(print_table(trap_plan));
    check_program(&trap_prog).map_err(|e| format!("trap prog check: {}", e.message))?;

    let trap_oracle =
        run_program(200_000, &trap_prog, World::default()).map_err(|e| format!("{e:?}"))?;
    let trap_seq = run_core_program_vm(
        200_000,
        &trap_prog,
        World::default(),
        &VmConfig::sequential_optimized(),
    )
    .map_err(|e| format!("{e:?}"))?;
    let trap_par = run_core_program_vm(
        200_000,
        &trap_prog,
        World::default(),
        &VmConfig::parallel_optimized(BATCH_SIZE, 4),
    )
    .map_err(|e| format!("{e:?}"))?;

    assert_eq!(trap_oracle.status, ExitStatus::Stopped);
    assert!(
        trap_oracle
            .diagnostic
            .as_deref()
            .is_some_and(|d| d.contains("division by zero")),
        "expected earliest-row DivByZero at row 9,500, got {:?}",
        trap_oracle.diagnostic
    );
    assert_eq!(print_report(&trap_oracle), print_report(&trap_seq));
    assert_eq!(print_report(&trap_oracle), print_report(&trap_par));
    Ok(())
}
