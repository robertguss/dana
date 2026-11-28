//! Automated Rust (`dana-oracle`) vs. Lean 4 (`danacore`) Differential Test Suite.
//!
//! Asserts 100% byte-for-byte agreement on:
//! - `fmt` (canonical wire acceptance/rejection and exact formatted bytes),
//! - `check` (type/schema/privacy/policy static verification accept/reject),
//! - `run` (canonical `(dana-report 0.1 ...)\n` output and exit status),
//! - CLI argument validation (exit codes `0` / `1` / `2`).
//!
//! Covers:
//! 1. A curated corpus of 70+ Core IR programs + wire/CLI error cases covering every
//!    expression form, primitive, relational plan operator, join kind, window function,
//!    aggregate, privacy/policy rule, float/stats edge case, and runtime confinement check.
//! 2. A deterministic seeded SplitMix64 PRNG differential fuzzer generating 300 diverse
//!    Core IR programs (valid & invalid; scalar, relational, join, aggregate, privacy,
//!    policy, and mutated programs).

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::OnceLock;
use std::sync::atomic::{AtomicU64, Ordering};

use dana::core::{
    AggItem, AggKind, AggOp, BigInt, BugKind, CaseArm, ChartKind, ColSpec, CompilerMetadata,
    ConstDecl, CoreVersion, CtorDecl, DEC_MAX, DEC_SCALE, DataDecl, DeriveItem, Expr, Float64,
    FunDecl, FunKind, HostOp, JoinKind, JoinOn, LTy, Literal, MetaEntry, Plan, Policy, PrimOp,
    Program, RowExpr, RowLit, ScalarTy, SchemaDecl, SortDir, SourceSpan, SuppressMode, TableTy,
    TagSet, Ty, WindowFn, WindowItem, check_program, parse_program, print_program, print_report,
};
use dana::oracle::{ExitStatus, World, run_program};

static LEAN_BIN: OnceLock<PathBuf> = OnceLock::new();
static TMP_COUNTER: AtomicU64 = AtomicU64::new(0);

fn lean_danacore_bin() -> &'static Path {
    LEAN_BIN.get_or_init(|| {
        let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        let bin = manifest_dir.join("formal/.lake/build/bin/danacore");
        if bin.exists() {
            return bin;
        }
        // Build Lean `danacore` automatically if absent (e.g., fresh checkout).
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
            ok && bin.exists(),
            "`lake build DanaCore danacore` failed ({status:?}); run `make formal` first"
        );
        bin
    })
}

fn rust_oracle_bin() -> &'static Path {
    Path::new(env!("CARGO_BIN_EXE_dana-oracle"))
}

struct CmdResult {
    code: i32,
    stdout: String,
    stderr: String,
}

fn run_bin(bin: &Path, args: &[&str]) -> CmdResult {
    let out_res = Command::new(bin).args(args).output();
    assert!(
        out_res.is_ok(),
        "failed to execute {}: {:?}",
        bin.display(),
        out_res.as_ref().err()
    );
    let Ok(out) = out_res else {
        return CmdResult {
            code: -1,
            stdout: String::new(),
            stderr: String::new(),
        };
    };
    CmdResult {
        code: out.status.code().unwrap_or(-1),
        stdout: String::from_utf8_lossy(&out.stdout).into_owned(),
        stderr: String::from_utf8_lossy(&out.stderr).into_owned(),
    }
}

struct TempWireFile {
    path: PathBuf,
}

impl TempWireFile {
    fn new(prefix: &str, content: &str) -> Self {
        let id = TMP_COUNTER.fetch_add(1, Ordering::Relaxed);
        let pid = std::process::id();
        let path = std::env::temp_dir().join(format!("dana_diff_{prefix}_{pid}_{id}.core"));
        let res = fs::write(&path, content);
        assert!(res.is_ok(), "write temp core file failed: {res:?}");
        Self { path }
    }

    fn as_str(&self) -> &str {
        self.path.to_str().unwrap_or("")
    }
}

impl Drop for TempWireFile {
    fn drop(&mut self) {
        let _ = fs::remove_file(&self.path);
    }
}

/// Assert 100% byte-for-byte differential parity between Lean `danacore`, Rust `dana-oracle`,
/// and the in-process Rust API on `fmt`, `check`, and `run`.
fn assert_diff_program(label: &str, wire: &str, fuel: Option<usize>, allow_export: Option<&str>) {
    let lean = lean_danacore_bin();
    let rust = rust_oracle_bin();
    let tmp = TempWireFile::new("prog", wire);
    let path_str = tmp.as_str();

    // 1. `fmt`
    let l_fmt = run_bin(lean, &["fmt", path_str]);
    let r_fmt = run_bin(rust, &["fmt", path_str]);
    assert_eq!(
        l_fmt.code, r_fmt.code,
        "[{label}] fmt exit code mismatch\nlean stderr: {}\nrust stderr: {}\nwire: {wire}",
        l_fmt.stderr, r_fmt.stderr
    );
    assert_eq!(
        l_fmt.stdout, r_fmt.stdout,
        "[{label}] fmt stdout mismatch\nwire: {wire}"
    );

    // In-process parse/print check
    let prog = match parse_program(wire) {
        Ok(p) => {
            assert_eq!(
                l_fmt.code, 0,
                "[{label}] in-process parsed ok but Lean fmt failed"
            );
            assert_eq!(
                print_program(&p),
                l_fmt.stdout,
                "[{label}] in-process print mismatch"
            );
            p
        }
        Err(_) => {
            assert_ne!(
                l_fmt.code, 0,
                "[{label}] in-process parse failed but Lean fmt succeeded"
            );
            return;
        }
    };

    // 2. `check`
    let l_chk = run_bin(lean, &["check", path_str]);
    let r_chk = run_bin(rust, &["check", path_str]);
    assert_eq!(
        l_chk.code, r_chk.code,
        "[{label}] check exit code mismatch\nlean stderr: {}\nrust stderr: {}\nwire: {wire}",
        l_chk.stderr, r_chk.stderr
    );
    assert_eq!(
        l_chk.stdout, r_chk.stdout,
        "[{label}] check stdout mismatch\nwire: {wire}"
    );

    // 3. `run`
    let fuel_str = fuel.map(|f| f.to_string());
    let mut run_args: Vec<&str> = vec!["run", path_str];
    if let Some(ref fs) = fuel_str {
        run_args.push("--fuel");
        run_args.push(fs);
    }
    if let Some(ae) = allow_export {
        run_args.push("--allow-export");
        run_args.push(ae);
    }
    let l_run = run_bin(lean, &run_args);
    let r_run = run_bin(rust, &run_args);
    assert_eq!(
        l_run.code, r_run.code,
        "[{label}] run exit code mismatch\nlean stdout: {}\nlean stderr: {}\nrust stdout: {}\nrust stderr: {}\nwire: {wire}",
        l_run.stdout, l_run.stderr, r_run.stdout, r_run.stderr
    );
    assert_eq!(
        l_run.stdout, r_run.stdout,
        "[{label}] run stdout mismatch\nlean stderr: {}\nrust stderr: {}\nwire: {wire}",
        l_run.stderr, r_run.stderr
    );

    // Verify in-process Rust `run_program` agrees with CLI output as well.
    if check_program(&prog).is_ok() {
        let mut world = World::default();
        if let Some(ae) = allow_export {
            world.runtime_allow_export = TagSet::of_list(ae.split(',').map(String::from).collect());
        }
        match run_program(fuel.unwrap_or(4096), &prog, world) {
            Ok(rep) => {
                assert_eq!(
                    print_report(&rep),
                    l_run.stdout,
                    "[{label}] in-process report mismatch"
                );
                let expected_code = match rep.status {
                    ExitStatus::Ok => 0,
                    ExitStatus::Stopped | ExitStatus::Failed => 1,
                };
                assert_eq!(
                    expected_code, l_run.code,
                    "[{label}] in-process status code mismatch"
                );
            }
            Err(_) => {
                assert_eq!(
                    l_run.code, 1,
                    "[{label}] in-process runtime err but Lean succeeded"
                );
                assert!(
                    l_run.stdout.is_empty(),
                    "[{label}] unexpected Lean stdout on runtime err"
                );
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Helpers for Constructing Curated & Fuzzed Programs
// ---------------------------------------------------------------------------

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

fn f64_lit(x: f64) -> Literal {
    Literal::Float(Float64::from_f64(x))
}

fn mk_console_prog(body: Expr) -> Program {
    Program {
        funs: vec![FunDecl {
            name: "main".into(),
            kind: FunKind::Function,
            is_pure: false,
            params: vec![("c".into(), LTy::public(Ty::Console(TagSet::empty())))],
            pc: TagSet::empty(),
            ret: LTy::public(Ty::Unit),
            body,
        }],
        entry: Some("main".into()),
        ..Program::default()
    }
}

fn print_str(expr: Expr) -> Expr {
    Expr::Host {
        op: HostOp::ConsolePrint,
        args: vec![Expr::Var("c".into()), expr],
    }
}

fn print_table(plan: Plan) -> Expr {
    Expr::Host {
        op: HostOp::ConsolePrintTable,
        args: vec![Expr::Var("c".into()), Expr::Rel(Box::new(plan))],
    }
}

fn print_int(expr: Expr) -> Expr {
    print_str(Expr::Prim {
        op: PrimOp::IntToText,
        args: vec![expr],
    })
}

fn print_dec(expr: Expr) -> Expr {
    print_str(Expr::Prim {
        op: PrimOp::DecToText,
        args: vec![expr],
    })
}

fn print_bool(expr: Expr) -> Expr {
    print_str(Expr::IfE {
        cond: Box::new(expr),
        then_br: Box::new(Expr::Lit(Literal::Text("true".into()))),
        else_br: Box::new(Expr::Lit(Literal::Text("false".into()))),
    })
}

fn let_seq(name: &str, lty: LTy, bound: Expr, body: Expr) -> Expr {
    Expr::LetE {
        name: name.into(),
        lty,
        bound: Box::new(bound),
        body: Box::new(body),
    }
}

struct CorpusCase {
    name: &'static str,
    prog: Program,
    fuel: Option<usize>,
    allow_export: Option<&'static str>,
}

fn build_curated_corpus() -> Vec<CorpusCase> {
    let mut cases = Vec::new();
    macro_rules! add {
        ($name:expr, $prog:expr $(,)?) => {
            cases.push(CorpusCase {
                name: $name,
                prog: $prog,
                fuel: None,
                allow_export: None,
            });
        };
    }

    // 1. Empty program (no entry)
    add!("01_empty_program", Program::default());

    // 2. Checked Int64 arithmetic & negative Euclidean div/mod (all 4 sign combinations)
    {
        let pairs = [
            (-7, 2),
            (7, -2),
            (-7, -2),
            (-6, 2),
            (-1, 2),
            (1, -2),
            (-1, -2),
            (13, 5),
        ];
        let mut body = Expr::Lit(Literal::Unit);
        for (idx, (a, b)) in pairs.into_iter().enumerate().rev() {
            let q = Expr::Prim {
                op: PrimOp::DivInt,
                args: vec![Expr::Lit(Literal::int(a)), Expr::Lit(Literal::int(b))],
            };
            let r = Expr::Prim {
                op: PrimOp::ModInt,
                args: vec![Expr::Lit(Literal::int(a)), Expr::Lit(Literal::int(b))],
            };
            let line = Expr::Prim {
                op: PrimOp::ConcatText,
                args: vec![
                    Expr::Prim {
                        op: PrimOp::IntToText,
                        args: vec![q],
                    },
                    Expr::Prim {
                        op: PrimOp::ConcatText,
                        args: vec![
                            Expr::Lit(Literal::Text(",".into())),
                            Expr::Prim {
                                op: PrimOp::IntToText,
                                args: vec![r],
                            },
                        ],
                    },
                ],
            };
            body = let_seq(
                &format!("s{idx}"),
                LTy::public(Ty::Unit),
                print_str(line),
                body,
            );
        }
        add!("02_neg_div_mod_euclidean", mk_console_prog(body));
    }

    // 3. Int64 add/sub/mul/neg normal + i64::MIN % -1 == 0
    add!(
        "03_int_arith_and_min_mod_neg1",
        mk_console_prog(let_seq(
            "a",
            LTy::public(Ty::Unit),
            print_int(Expr::Prim {
                op: PrimOp::ModInt,
                args: vec![
                    Expr::Lit(Literal::int(i64::MIN)),
                    Expr::Lit(Literal::int(-1)),
                ],
            }),
            print_int(Expr::Prim {
                op: PrimOp::NegInt,
                args: vec![Expr::Prim {
                    op: PrimOp::SubInt,
                    args: vec![
                        Expr::Prim {
                            op: PrimOp::MulInt,
                            args: vec![Expr::Lit(Literal::int(6)), Expr::Lit(Literal::int(7))],
                        },
                        Expr::Prim {
                            op: PrimOp::AddInt,
                            args: vec![Expr::Lit(Literal::int(2)), Expr::Lit(Literal::int(3))],
                        },
                    ],
                }],
            }),
        )),
    );

    // 4. Int64 overflow: i64::MAX + 1
    add!(
        "04_int_add_overflow",
        mk_console_prog(print_int(Expr::Prim {
            op: PrimOp::AddInt,
            args: vec![
                Expr::Lit(Literal::int(i64::MAX)),
                Expr::Lit(Literal::int(1)),
            ],
        })),
    );

    // 5. Int64 overflow: i64::MIN / -1
    add!(
        "05_int_div_min_neg1_overflow",
        mk_console_prog(print_int(Expr::Prim {
            op: PrimOp::DivInt,
            args: vec![
                Expr::Lit(Literal::int(i64::MIN)),
                Expr::Lit(Literal::int(-1)),
            ],
        })),
    );

    // 6. Int64 overflow: -i64::MIN
    add!(
        "06_int_neg_min_overflow",
        mk_console_prog(print_int(Expr::Prim {
            op: PrimOp::NegInt,
            args: vec![Expr::Lit(Literal::int(i64::MIN))],
        })),
    );

    // 7. Int64 div by zero
    add!(
        "07_int_div_by_zero",
        mk_console_prog(print_int(Expr::Prim {
            op: PrimOp::DivInt,
            args: vec![Expr::Lit(Literal::int(10)), Expr::Lit(Literal::int(0))],
        })),
    );

    // 8. Int64 mod by zero
    add!(
        "08_int_mod_by_zero",
        mk_console_prog(print_int(Expr::Prim {
            op: PrimOp::ModInt,
            args: vec![Expr::Lit(Literal::int(10)), Expr::Lit(Literal::int(0))],
        })),
    );

    // 9. Decimal arithmetic (add, sub, mul, div with negative Euclidean rounding, neg, intToDec, boolToDec)
    add!(
        "09_decimal_arith_and_neg_div",
        mk_console_prog(let_seq(
            "d1",
            LTy::public(Ty::Unit),
            print_dec(Expr::Prim {
                op: PrimOp::DivDec,
                args: vec![
                    Expr::Lit(Literal::decimal(-DEC_SCALE)),
                    Expr::Lit(Literal::decimal(3 * DEC_SCALE)),
                ],
            }),
            let_seq(
                "d2",
                LTy::public(Ty::Unit),
                print_dec(Expr::Prim {
                    op: PrimOp::MulDec,
                    args: vec![
                        Expr::Lit(Literal::decimal(-3)),
                        Expr::Lit(Literal::decimal(500_000_000_000_000_000i128)),
                    ],
                }),
                print_dec(Expr::Prim {
                    op: PrimOp::AddDec,
                    args: vec![
                        Expr::Prim {
                            op: PrimOp::IntToDec,
                            args: vec![Expr::Lit(Literal::int(4))],
                        },
                        Expr::Prim {
                            op: PrimOp::NegDec,
                            args: vec![Expr::Prim {
                                op: PrimOp::BoolToDec,
                                args: vec![Expr::Lit(Literal::Bool(true))],
                            }],
                        },
                    ],
                }),
            ),
        )),
    );

    // 10. Decimal overflow & div-by-zero
    add!(
        "10_decimal_overflow",
        mk_console_prog(print_dec(Expr::Prim {
            op: PrimOp::AddDec,
            args: vec![
                Expr::Lit(Literal::decimal(DEC_MAX)),
                Expr::Lit(Literal::decimal(1)),
            ],
        })),
    );
    add!(
        "11_decimal_div_by_zero",
        mk_console_prog(print_dec(Expr::Prim {
            op: PrimOp::DivDec,
            args: vec![
                Expr::Lit(Literal::decimal(DEC_SCALE)),
                Expr::Lit(Literal::decimal(0)),
            ],
        })),
    );

    // 12. Text & Bool primitives + comparisons (eq, ne, lt, le, gt, ge, not, and, or)
    add!(
        "12_text_and_bool_ops",
        mk_console_prog(let_seq(
            "t",
            LTy::public(Ty::Unit),
            print_str(Expr::Prim {
                op: PrimOp::LowerAsciiText,
                args: vec![Expr::Prim {
                    op: PrimOp::TrimText,
                    args: vec![Expr::Lit(Literal::Text("  HeLLo_DaNa\t\n".into()))],
                }],
            }),
            print_bool(Expr::Prim {
                op: PrimOp::AndBool,
                args: vec![
                    Expr::Prim {
                        op: PrimOp::ContainsText,
                        args: vec![
                            Expr::Lit(Literal::Text("alphabet".into())),
                            Expr::Lit(Literal::Text("pha".into())),
                        ],
                    },
                    Expr::Prim {
                        op: PrimOp::OrBool,
                        args: vec![
                            Expr::Prim {
                                op: PrimOp::EmptyText,
                                args: vec![Expr::Lit(Literal::Text("x".into()))],
                            },
                            Expr::Prim {
                                op: PrimOp::NotBool,
                                args: vec![Expr::Prim {
                                    op: PrimOp::Ge,
                                    args: vec![
                                        Expr::Lit(Literal::int(1)),
                                        Expr::Lit(Literal::int(5)),
                                    ],
                                }],
                            },
                        ],
                    },
                ],
            }),
        )),
    );

    // 13. Date & Timestamp & Duration ops (positive, leap day, pre-1970, negative era multiple)
    {
        let date_schema = TableTy {
            cols: vec![
                col("d", ScalarTy::Date, TagSet::empty()),
                col("ts", ScalarTy::Timestamp, TagSet::empty()),
                col("dur", ScalarTy::Duration, TagSet::empty()),
            ],
            ..TableTy::default()
        };
        let tbl = Expr::TableLit {
            schema: date_schema,
            rows: vec![
                RowLit {
                    cells: vec![
                        Literal::date(19782), // 2024-02-29 (leap day)
                        Literal::timestamp(1_000_000),
                        Literal::duration(500_000),
                    ],
                },
                RowLit {
                    cells: vec![
                        Literal::date(-1), // 1969-12-31
                        Literal::timestamp(-100),
                        Literal::duration(-900),
                    ],
                },
                RowLit {
                    cells: vec![
                        Literal::date(-719_468 - 146_097), // negative era boundary
                        Literal::timestamp(0),
                        Literal::duration(42),
                    ],
                },
            ],
        };
        let plan = Plan::Derive {
            input: Box::new(Plan::SourceExpr(Box::new(tbl))),
            items: vec![
                DeriveItem::ColExpr {
                    name: "m".into(),
                    expr: Box::new(RowExpr::Prim {
                        op: PrimOp::DateTruncMonth,
                        args: vec![RowExpr::Col("d".into())],
                    }),
                },
                DeriveItem::ColExpr {
                    name: "ts2".into(),
                    expr: Box::new(RowExpr::Prim {
                        op: PrimOp::AddDuration,
                        args: vec![RowExpr::Col("ts".into()), RowExpr::Col("dur".into())],
                    }),
                },
                DeriveItem::ColExpr {
                    name: "delta".into(),
                    expr: Box::new(RowExpr::Prim {
                        op: PrimOp::DiffTimestamp,
                        args: vec![RowExpr::Col("ts2".into()), RowExpr::Col("ts".into())],
                    }),
                },
            ],
        };
        add!(
            "13_date_timestamp_duration",
            mk_console_prog(print_table(plan)),
        );
    }

    // 14. Option & Result primitives + unwrapBang ok and stop
    add!(
        "14_option_result_ops",
        mk_console_prog(let_seq(
            "o",
            LTy::public(Ty::Option(Box::new(Ty::Int))),
            Expr::Prim {
                op: PrimOp::SomeVal(Ty::Int),
                args: vec![Expr::Lit(Literal::int(99))],
            },
            let_seq(
                "p1",
                LTy::public(Ty::Unit),
                print_bool(Expr::Prim {
                    op: PrimOp::IsSome,
                    args: vec![Expr::Var("o".into())],
                }),
                let_seq(
                    "p2",
                    LTy::public(Ty::Unit),
                    print_bool(Expr::Prim {
                        op: PrimOp::IsNone,
                        args: vec![Expr::Lit(Literal::NoneLit(Ty::Int))],
                    }),
                    let_seq(
                        "p3",
                        LTy::public(Ty::Unit),
                        print_int(Expr::Prim {
                            op: PrimOp::UnwrapOr,
                            args: vec![
                                Expr::Lit(Literal::NoneLit(Ty::Int)),
                                Expr::Lit(Literal::int(7)),
                            ],
                        }),
                        print_int(Expr::Prim {
                            op: PrimOp::UnwrapBang,
                            args: vec![Expr::Var("o".into())],
                        }),
                    ),
                ),
            ),
        )),
    );
    add!(
        "15_unwrap_bang_none_stop",
        mk_console_prog(print_int(Expr::Prim {
            op: PrimOp::UnwrapBang,
            args: vec![Expr::Lit(Literal::NoneLit(Ty::Int))],
        })),
    );

    // 16. Tuple, Proj, List, Map primitives
    add!(
        "16_tuple_list_map",
        mk_console_prog(let_seq(
            "tup",
            LTy::public(Ty::Tuple(vec![LTy::public(Ty::Int), LTy::public(Ty::Text)])),
            Expr::Tuple(vec![
                Expr::Lit(Literal::int(11)),
                Expr::Lit(Literal::Text("ok".into())),
            ]),
            let_seq(
                "xs",
                LTy::public(Ty::List(Box::new(LTy::public(Ty::Int)))),
                Expr::Prim {
                    op: PrimOp::ListConcat,
                    args: vec![Expr::Prim {
                        op: PrimOp::ListLit(LTy::public(Ty::List(Box::new(LTy::public(Ty::Int))))),
                        args: vec![
                            Expr::Prim {
                                op: PrimOp::ListAppend,
                                args: vec![
                                    Expr::Prim {
                                        op: PrimOp::ListLit(LTy::public(Ty::Int)),
                                        args: vec![Expr::Proj {
                                            tup: Box::new(Expr::Var("tup".into())),
                                            idx: BigInt::from(0u64),
                                        }],
                                    },
                                    Expr::Lit(Literal::int(22)),
                                ],
                            },
                            Expr::Prim {
                                op: PrimOp::ListLit(LTy::public(Ty::Int)),
                                args: vec![Expr::Lit(Literal::int(33))],
                            },
                        ],
                    }],
                },
                let_seq(
                    "m",
                    LTy::public(Ty::Map {
                        key: Box::new(LTy::public(Ty::Text)),
                        val: Box::new(LTy::public(Ty::Int)),
                    }),
                    Expr::Prim {
                        op: PrimOp::MapLit {
                            key_lty: LTy::public(Ty::Text),
                            val_lty: LTy::public(Ty::Int),
                        },
                        args: vec![
                            Expr::Lit(Literal::Text("k1".into())),
                            Expr::Prim {
                                op: PrimOp::ListLen,
                                args: vec![Expr::Var("xs".into())],
                            },
                        ],
                    },
                    let_seq(
                        "hit",
                        LTy::public(Ty::Unit),
                        print_int(Expr::Prim {
                            op: PrimOp::UnwrapOr,
                            args: vec![
                                Expr::Prim {
                                    op: PrimOp::MapGet,
                                    args: vec![
                                        Expr::Var("m".into()),
                                        Expr::Lit(Literal::Text("k1".into())),
                                    ],
                                },
                                Expr::Lit(Literal::int(-1)),
                            ],
                        }),
                        print_int(Expr::Prim {
                            op: PrimOp::UnwrapOr,
                            args: vec![
                                Expr::Prim {
                                    op: PrimOp::MapGet,
                                    args: vec![
                                        Expr::Var("m".into()),
                                        Expr::Lit(Literal::Text("missing".into())),
                                    ],
                                },
                                Expr::Lit(Literal::int(-9)),
                            ],
                        }),
                    ),
                ),
            ),
        )),
    );

    // 17. Data decl, Ctor, Case (Data + Result + Option + Bool)
    add!(
        "17_data_ctor_case_exhaustive",
        Program {
            datas: vec![DataDecl {
                name: "Shape".into(),
                ctors: vec![
                    CtorDecl {
                        name: "Circle".into(),
                        fields: vec![LTy::public(Ty::Int)],
                    },
                    CtorDecl {
                        name: "Empty".into(),
                        fields: vec![],
                    },
                ],
            }],
            consts: vec![ConstDecl {
                name: "BASE".into(),
                lty: LTy::public(Ty::Int),
                value: Literal::int(100),
            }],
            funs: vec![FunDecl {
                name: "main".into(),
                kind: FunKind::Function,
                is_pure: false,
                params: vec![("c".into(), LTy::public(Ty::Console(TagSet::empty())))],
                pc: TagSet::empty(),
                ret: LTy::public(Ty::Unit),
                body: let_seq(
                    "v",
                    LTy::public(Ty::Int),
                    Expr::CaseE {
                        scrut: Box::new(Expr::Ctor {
                            type_name: "Shape".into(),
                            ctor_name: "Circle".into(),
                            args: vec![Expr::Lit(Literal::int(5))],
                        }),
                        arms: vec![
                            CaseArm {
                                ctor: "Circle".into(),
                                binders: vec!["r".into()],
                                body: Expr::Prim {
                                    op: PrimOp::AddInt,
                                    args: vec![
                                        Expr::Var("r".into()),
                                        Expr::ConstRef("BASE".into()),
                                    ],
                                },
                            },
                            CaseArm {
                                ctor: "Empty".into(),
                                binders: vec![],
                                body: Expr::Lit(Literal::int(0)),
                            },
                        ],
                    },
                    let_seq(
                        "rv",
                        LTy::public(Ty::Int),
                        Expr::CaseE {
                            scrut: Box::new(Expr::Prim {
                                op: PrimOp::OkVal(Ty::Text),
                                args: vec![Expr::Var("v".into())],
                            }),
                            arms: vec![
                                CaseArm {
                                    ctor: "Ok".into(),
                                    binders: vec!["x".into()],
                                    body: Expr::Var("x".into()),
                                },
                                CaseArm {
                                    ctor: "Error".into(),
                                    binders: vec!["_e".into()],
                                    body: Expr::Lit(Literal::int(-1)),
                                },
                            ],
                        },
                        print_int(Expr::Var("rv".into())),
                    ),
                ),
            }],
            entry: Some("main".into()),
            ..Program::default()
        },
    );

    // 18. Closures (Lam/App) + Top-level Call + Join/Jump loop summing 1..5
    add!(
        "18_closures_call_join_loop",
        Program {
            funs: vec![
                FunDecl {
                    name: "add_k".into(),
                    kind: FunKind::Function,
                    is_pure: true,
                    params: vec![("x".into(), LTy::public(Ty::Int))],
                    pc: TagSet::empty(),
                    ret: LTy::public(Ty::Int),
                    body: Expr::Prim {
                        op: PrimOp::AddInt,
                        args: vec![Expr::Var("x".into()), Expr::Lit(Literal::int(10))],
                    },
                },
                FunDecl {
                    name: "main".into(),
                    kind: FunKind::Function,
                    is_pure: false,
                    params: vec![("c".into(), LTy::public(Ty::Console(TagSet::empty())))],
                    pc: TagSet::empty(),
                    ret: LTy::public(Ty::Unit),
                    body: let_seq(
                        "offset",
                        LTy::public(Ty::Int),
                        Expr::Call {
                            fn_name: "add_k".into(),
                            args: vec![Expr::Lit(Literal::int(5))],
                        },
                        let_seq(
                            "adder",
                            LTy::public(Ty::Fn {
                                params: vec![LTy::public(Ty::Int)],
                                pc: TagSet::empty(),
                                ret: Box::new(LTy::public(Ty::Int)),
                            }),
                            Expr::Lam {
                                params: vec![("y".into(), LTy::public(Ty::Int))],
                                pc: TagSet::empty(),
                                ret: LTy::public(Ty::Int),
                                body: std::sync::Arc::new(Expr::Prim {
                                    op: PrimOp::AddInt,
                                    args: vec![Expr::Var("offset".into()), Expr::Var("y".into())],
                                }),
                            },
                            let_seq(
                                "loop_sum",
                                LTy::public(Ty::Int),
                                Expr::Join {
                                    label: "lp".into(),
                                    params: vec![
                                        ("i".into(), LTy::public(Ty::Int)),
                                        ("acc".into(), LTy::public(Ty::Int)),
                                    ],
                                    rhs: Box::new(Expr::IfE {
                                        cond: Box::new(Expr::Prim {
                                            op: PrimOp::Le,
                                            args: vec![
                                                Expr::Var("i".into()),
                                                Expr::Lit(Literal::int(5)),
                                            ],
                                        }),
                                        then_br: Box::new(Expr::Jump {
                                            label: "lp".into(),
                                            args: vec![
                                                Expr::Prim {
                                                    op: PrimOp::AddInt,
                                                    args: vec![
                                                        Expr::Var("i".into()),
                                                        Expr::Lit(Literal::int(1)),
                                                    ],
                                                },
                                                Expr::Prim {
                                                    op: PrimOp::AddInt,
                                                    args: vec![
                                                        Expr::Var("acc".into()),
                                                        Expr::Var("i".into()),
                                                    ],
                                                },
                                            ],
                                        }),
                                        else_br: Box::new(Expr::Var("acc".into())),
                                    }),
                                    body: Box::new(Expr::Jump {
                                        label: "lp".into(),
                                        args: vec![
                                            Expr::Lit(Literal::int(1)),
                                            Expr::Lit(Literal::int(0)),
                                        ],
                                    }),
                                },
                                print_int(Expr::App {
                                    fn_expr: Box::new(Expr::Var("adder".into())),
                                    args: vec![Expr::Var("loop_sum".into())],
                                }),
                            ),
                        ),
                    ),
                },
            ],
            entry: Some("main".into()),
            ..Program::default()
        },
    );

    // 19. Tight fuel exhaustion test on loop (exact fuel boundary parity!)
    if let Some(last) = cases.last() {
        let loop_prog = last.prog.clone();
        cases.push(CorpusCase {
            name: "19_tight_fuel_exhaustion",
            prog: loop_prog,
            fuel: Some(8),
            allow_export: None,
        });
    }

    // Shared sample table for relational plans
    let emp_schema = TableTy {
        cols: vec![
            col("dept", ScalarTy::Text, TagSet::empty()),
            col("emp", ScalarTy::Text, TagSet::empty()),
            col("sal", ScalarTy::Int, TagSet::empty()),
            col(
                "bonus",
                ScalarTy::Option(Box::new(ScalarTy::Int)),
                TagSet::empty(),
            ),
        ],
        ..TableTy::default()
    };
    let emp_tbl = Expr::TableLit {
        schema: emp_schema.clone(),
        rows: vec![
            RowLit {
                cells: vec![
                    Literal::Text("Eng".into()),
                    Literal::Text("Alice".into()),
                    Literal::int(100),
                    Literal::NoneLit(Ty::Int),
                ],
            },
            RowLit {
                cells: vec![
                    Literal::Text("Sales".into()),
                    Literal::Text("Bob".into()),
                    Literal::int(80),
                    Literal::NoneLit(Ty::Int),
                ],
            },
            RowLit {
                cells: vec![
                    Literal::Text("Eng".into()),
                    Literal::Text("Carol".into()),
                    Literal::int(120),
                    Literal::NoneLit(Ty::Int),
                ],
            },
            RowLit {
                cells: vec![
                    Literal::Text("Eng".into()),
                    Literal::Text("Alice".into()),
                    Literal::int(100),
                    Literal::NoneLit(Ty::Int),
                ],
            },
        ],
    };

    // 20. Select, Drop, Rename, Filter, Distinct, Sort (asc & desc), Limit
    {
        let plan = Plan::Limit {
            input: Box::new(Plan::Sort {
                input: Box::new(Plan::Distinct {
                    input: Box::new(Plan::Rename {
                        input: Box::new(Plan::Drop {
                            input: Box::new(Plan::Select {
                                input: Box::new(Plan::Filter {
                                    input: Box::new(Plan::SourceExpr(Box::new(emp_tbl.clone()))),
                                    pred: RowExpr::Prim {
                                        op: PrimOp::Ge,
                                        args: vec![
                                            RowExpr::Col("sal".into()),
                                            RowExpr::Lit(Literal::int(80)),
                                        ],
                                    },
                                }),
                                cols: vec![
                                    "dept".into(),
                                    "emp".into(),
                                    "sal".into(),
                                    "bonus".into(),
                                ],
                            }),
                            cols: vec!["bonus".into()],
                        }),
                        pairs: vec![("salary".into(), "sal".into())],
                    }),
                    cols: vec!["dept".into(), "emp".into()],
                }),
                keys: vec![
                    ("dept".into(), SortDir::Asc),
                    ("salary".into(), SortDir::Desc),
                ],
            }),
            n: BigInt::from(2u64),
        };
        add!(
            "20_select_drop_rename_filter_distinct_sort_limit",
            mk_console_prog(print_table(plan)),
        );
    }

    // 21. Derive with RowExpr (outerVar, constRef, ifE, coalesce, callPure, bucketCol)
    {
        let prog = Program {
            consts: vec![ConstDecl {
                name: "BONUS_DEF".into(),
                lty: LTy::public(Ty::Int),
                value: Literal::int(5),
            }],
            funs: vec![
                FunDecl {
                    name: "double_int".into(),
                    kind: FunKind::Function,
                    is_pure: true,
                    params: vec![("x".into(), LTy::public(Ty::Int))],
                    pc: TagSet::empty(),
                    ret: LTy::public(Ty::Int),
                    body: Expr::Prim {
                        op: PrimOp::MulInt,
                        args: vec![Expr::Var("x".into()), Expr::Lit(Literal::int(2))],
                    },
                },
                FunDecl {
                    name: "main".into(),
                    kind: FunKind::Function,
                    is_pure: false,
                    params: vec![("c".into(), LTy::public(Ty::Console(TagSet::empty())))],
                    pc: TagSet::empty(),
                    ret: LTy::public(Ty::Unit),
                    body: let_seq(
                        "bump",
                        LTy::public(Ty::Int),
                        Expr::Lit(Literal::int(1)),
                        print_table(Plan::Derive {
                            input: Box::new(Plan::SourceExpr(Box::new(emp_tbl.clone()))),
                            items: vec![
                                DeriveItem::ColExpr {
                                    name: "adj".into(),
                                    expr: Box::new(RowExpr::IfE {
                                        cond: Box::new(RowExpr::Prim {
                                            op: PrimOp::Gt,
                                            args: vec![
                                                RowExpr::Col("sal".into()),
                                                RowExpr::Lit(Literal::int(90)),
                                            ],
                                        }),
                                        then_br: Box::new(RowExpr::CallPure {
                                            fn_name: "double_int".into(),
                                            args: vec![RowExpr::Prim {
                                                op: PrimOp::AddInt,
                                                args: vec![
                                                    RowExpr::OuterVar("bump".into()),
                                                    RowExpr::Coalesce {
                                                        opt_expr: Box::new(RowExpr::Col(
                                                            "bonus".into(),
                                                        )),
                                                        default_expr: Box::new(RowExpr::ConstRef(
                                                            "BONUS_DEF".into(),
                                                        )),
                                                    },
                                                ],
                                            }],
                                        }),
                                        else_br: Box::new(RowExpr::Lit(Literal::int(0))),
                                    }),
                                },
                                DeriveItem::BucketCol {
                                    name: "band".into(),
                                    source: "sal".into(),
                                    cuts: vec![Literal::int(90), Literal::int(110)],
                                    labels: vec!["low".into(), "mid".into(), "high".into()],
                                },
                            ],
                        }),
                    ),
                },
            ],
            entry: Some("main".into()),
            ..Program::default()
        };
        add!("21_derive_rowexpr_callpure_bucket", prog);
    }

    // 22-28. All 7 JoinKinds + Pairs + Suffixes + Public & PII Duplicate Key Cardinality Stops
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
        let l_unique = Expr::TableLit {
            schema: l_schema.clone(),
            rows: vec![
                RowLit {
                    cells: vec![Literal::int(1), Literal::Text("L1".into())],
                },
                RowLit {
                    cells: vec![Literal::int(2), Literal::Text("L2".into())],
                },
                RowLit {
                    cells: vec![Literal::int(3), Literal::Text("L3".into())],
                },
            ],
        };
        let l_dup = Expr::TableLit {
            schema: l_schema.clone(),
            rows: vec![
                RowLit {
                    cells: vec![Literal::int(1), Literal::Text("L1a".into())],
                },
                RowLit {
                    cells: vec![Literal::int(1), Literal::Text("L1b".into())],
                },
                RowLit {
                    cells: vec![Literal::int(2), Literal::Text("L2".into())],
                },
            ],
        };
        let r_unique = Expr::TableLit {
            schema: r_schema.clone(),
            rows: vec![
                RowLit {
                    cells: vec![Literal::int(1), Literal::Text("R1".into())],
                },
                RowLit {
                    cells: vec![Literal::int(3), Literal::Text("R3".into())],
                },
            ],
        };
        let r_dup = Expr::TableLit {
            schema: r_schema.clone(),
            rows: vec![
                RowLit {
                    cells: vec![Literal::int(1), Literal::Text("R1a".into())],
                },
                RowLit {
                    cells: vec![Literal::int(1), Literal::Text("R1b".into())],
                },
            ],
        };

        type JoinCase<'a> = (
            &'static str,
            JoinKind,
            &'a Expr,
            &'a Expr,
            JoinOn,
            Option<(&'static str, &'static str)>,
        );
        let join_cases: &[JoinCase<'_>] = &[
            (
                "22_join_inner_one_suffix",
                JoinKind::InnerOne,
                &l_unique,
                &r_unique,
                JoinOn::SameKeys(vec!["id".into()]),
                Some(("_l", "_r")),
            ),
            (
                "23_join_inner_many_to_one",
                JoinKind::InnerManyToOne,
                &l_dup,
                &r_unique,
                JoinOn::SameKeys(vec!["id".into()]),
                Some(("_l", "_r")),
            ),
            (
                "24_join_inner_many_pairs",
                JoinKind::InnerMany,
                &l_dup,
                &r_dup,
                JoinOn::Pairs(vec![("id".into(), "id".into())]),
                Some(("_l", "_r")),
            ),
            (
                "25_join_left_one",
                JoinKind::LeftOne,
                &l_unique,
                &r_unique,
                JoinOn::SameKeys(vec!["id".into()]),
                Some(("_l", "_r")),
            ),
            (
                "26_join_left_many_to_one",
                JoinKind::LeftManyToOne,
                &l_dup,
                &r_unique,
                JoinOn::SameKeys(vec!["id".into()]),
                Some(("_l", "_r")),
            ),
            (
                "27_join_semi",
                JoinKind::Semi,
                &l_unique,
                &r_unique,
                JoinOn::SameKeys(vec!["id".into()]),
                None,
            ),
            (
                "28_join_anti",
                JoinKind::Anti,
                &l_unique,
                &r_unique,
                JoinOn::SameKeys(vec!["id".into()]),
                None,
            ),
            (
                "29_join_public_dup_stop",
                JoinKind::InnerOne,
                &l_unique,
                &r_dup,
                JoinOn::SameKeys(vec!["id".into()]),
                Some(("_l", "_r")),
            ),
        ];
        for (name, kind, lp, rp, on, suf) in join_cases {
            let plan = Plan::Join {
                kind: *kind,
                left: Box::new(Plan::SourceExpr(Box::new((*lp).clone()))),
                right: Box::new(Plan::SourceExpr(Box::new((*rp).clone()))),
                on: on.clone(),
                suffixes: suf.map(|(a, b)| (a.to_string(), b.to_string())),
            };
            add!(name, mk_console_prog(print_table(plan)));
        }

        // 30. PII Duplicate Join Key Redaction
        let ssn_l = TableTy {
            cols: vec![
                col("ssn", ScalarTy::Text, ts(&["pii"])),
                col("dept", ScalarTy::Text, TagSet::empty()),
            ],
            ..TableTy::default()
        };
        let ssn_r = TableTy {
            cols: vec![
                col("ssn", ScalarTy::Text, ts(&["pii"])),
                col("role", ScalarTy::Text, TagSet::empty()),
            ],
            ..TableTy::default()
        };
        add!(
            "30_join_pii_dup_redacted_stop",
            Program {
                funs: vec![FunDecl {
                    name: "main".into(),
                    kind: FunKind::Function,
                    is_pure: false,
                    params: vec![],
                    pc: TagSet::empty(),
                    ret: LTy::public(Ty::Unit),
                    body: let_seq(
                        "j",
                        LTy::public(Ty::Table(TableTy {
                            cols: vec![
                                col("ssn", ScalarTy::Text, ts(&["pii"])),
                                col("dept", ScalarTy::Text, TagSet::empty()),
                                col("role", ScalarTy::Text, TagSet::empty()),
                            ],
                            row_tags: ts(&["pii"]),
                            ..TableTy::default()
                        })),
                        Expr::Rel(Box::new(Plan::Join {
                            kind: JoinKind::InnerOne,
                            left: Box::new(Plan::SourceExpr(Box::new(Expr::TableLit {
                                schema: ssn_l,
                                rows: vec![RowLit {
                                    cells: vec![
                                        Literal::Text("123-45-6789".into()),
                                        Literal::Text("Physics".into()),
                                    ],
                                }],
                            }))),
                            right: Box::new(Plan::SourceExpr(Box::new(Expr::TableLit {
                                schema: ssn_r,
                                rows: vec![
                                    RowLit {
                                        cells: vec![
                                            Literal::Text("123-45-6789".into()),
                                            Literal::Text("Faculty".into()),
                                        ],
                                    },
                                    RowLit {
                                        cells: vec![
                                            Literal::Text("123-45-6789".into()),
                                            Literal::Text("Chair".into()),
                                        ],
                                    },
                                ],
                            }))),
                            on: JoinOn::SameKeys(vec!["ssn".into()]),
                            suffixes: None,
                        })),
                        Expr::Lit(Literal::Unit),
                    ),
                }],
                entry: Some("main".into()),
                ..Program::default()
            },
        );
    }

    // 31. Union + tableCount + tableConcat
    {
        let s = TableTy {
            cols: vec![col("k", ScalarTy::Int, TagSet::empty())],
            ..TableTy::default()
        };
        let t1 = Expr::TableLit {
            schema: s.clone(),
            rows: vec![RowLit {
                cells: vec![Literal::int(1)],
            }],
        };
        let t2 = Expr::TableLit {
            schema: s.clone(),
            rows: vec![
                RowLit {
                    cells: vec![Literal::int(2)],
                },
                RowLit {
                    cells: vec![Literal::int(3)],
                },
            ],
        };
        add!(
            "31_union_and_table_concat",
            mk_console_prog(let_seq(
                "u",
                LTy::public(Ty::Unit),
                print_table(Plan::Union {
                    left: Box::new(Plan::SourceExpr(Box::new(t1.clone()))),
                    right: Box::new(Plan::SourceExpr(Box::new(t2.clone()))),
                }),
                print_int(Expr::Prim {
                    op: PrimOp::TableCount,
                    args: vec![Expr::Prim {
                        op: PrimOp::TableConcat(s.clone()),
                        args: vec![Expr::Prim {
                            op: PrimOp::ListLit(LTy::public(Ty::Table(s))),
                            args: vec![t1, t2],
                        }],
                    }],
                }),
            )),
        );
    }

    // 32. Summarize all 12 AggOps across Int, Decimal, Float (grouped & ungrouped empty)
    {
        let m_schema = TableTy {
            cols: vec![
                col("g", ScalarTy::Text, TagSet::empty()),
                col("xi", ScalarTy::Int, TagSet::empty()),
                col("xd", ScalarTy::Decimal, TagSet::empty()),
                col("xf", ScalarTy::Float, TagSet::empty()),
            ],
            ..TableTy::default()
        };
        let m_tbl = Expr::TableLit {
            schema: m_schema.clone(),
            rows: vec![
                RowLit {
                    cells: vec![
                        Literal::Text("A".into()),
                        Literal::int(10),
                        Literal::decimal(-3),
                        f64_lit(10.0),
                    ],
                },
                RowLit {
                    cells: vec![
                        Literal::Text("A".into()),
                        Literal::int(20),
                        Literal::decimal(2),
                        f64_lit(20.0),
                    ],
                },
                RowLit {
                    cells: vec![
                        Literal::Text("A".into()),
                        Literal::int(30),
                        Literal::decimal(4),
                        f64_lit(30.0),
                    ],
                },
                RowLit {
                    cells: vec![
                        Literal::Text("B".into()),
                        Literal::int(5),
                        Literal::decimal(-1),
                        f64_lit(5.0),
                    ],
                },
                RowLit {
                    cells: vec![
                        Literal::Text("B".into()),
                        Literal::int(5),
                        Literal::decimal(-2),
                        f64_lit(15.0),
                    ],
                },
            ],
        };
        let plan = Plan::Summarize {
            input: Box::new(Plan::GroupBy {
                input: Box::new(Plan::SourceExpr(Box::new(m_tbl))),
                keys: vec!["g".into()],
            }),
            aggs: vec![
                AggItem {
                    name: "cnt".into(),
                    op: AggOp::Count,
                    arg: None,
                },
                AggItem {
                    name: "cd".into(),
                    op: AggOp::CountDistinct,
                    arg: Some(RowExpr::Col("xi".into())),
                },
                AggItem {
                    name: "si".into(),
                    op: AggOp::Sum,
                    arg: Some(RowExpr::Col("xi".into())),
                },
                AggItem {
                    name: "sd_dec".into(),
                    op: AggOp::Sum,
                    arg: Some(RowExpr::Col("xd".into())),
                },
                AggItem {
                    name: "sf".into(),
                    op: AggOp::Sum,
                    arg: Some(RowExpr::Col("xf".into())),
                },
                AggItem {
                    name: "mi".into(),
                    op: AggOp::Mean,
                    arg: Some(RowExpr::Col("xi".into())),
                },
                AggItem {
                    name: "md".into(),
                    op: AggOp::Mean,
                    arg: Some(RowExpr::Col("xd".into())),
                },
                AggItem {
                    name: "med_d".into(),
                    op: AggOp::Median,
                    arg: Some(RowExpr::Col("xd".into())),
                },
                AggItem {
                    name: "med_f".into(),
                    op: AggOp::Median,
                    arg: Some(RowExpr::Col("xf".into())),
                },
                AggItem {
                    name: "var".into(),
                    op: AggOp::Variance,
                    arg: Some(RowExpr::Col("xf".into())),
                },
                AggItem {
                    name: "std".into(),
                    op: AggOp::Stddev,
                    arg: Some(RowExpr::Col("xf".into())),
                },
                AggItem {
                    name: "p25".into(),
                    op: AggOp::Percentile(Float64::from_f64(0.25)),
                    arg: Some(RowExpr::Col("xf".into())),
                },
                AggItem {
                    name: "mn".into(),
                    op: AggOp::Min,
                    arg: Some(RowExpr::Col("xi".into())),
                },
                AggItem {
                    name: "mx".into(),
                    op: AggOp::Max,
                    arg: Some(RowExpr::Col("xi".into())),
                },
                AggItem {
                    name: "fst".into(),
                    op: AggOp::First,
                    arg: Some(RowExpr::Col("xi".into())),
                },
                AggItem {
                    name: "lst".into(),
                    op: AggOp::Last,
                    arg: Some(RowExpr::Col("xi".into())),
                },
            ],
            distinct_key: None,
        };
        add!(
            "32_summarize_all_12_agg_ops",
            mk_console_prog(print_table(plan)),
        );

        // 33. Ungrouped summarize on empty table (1 row) vs grouped on empty table (0 rows)
        let empty_tbl = Expr::TableLit {
            schema: m_schema,
            rows: vec![],
        };
        add!(
            "33_summarize_empty_ungrouped_and_grouped",
            mk_console_prog(let_seq(
                "u",
                LTy::public(Ty::Unit),
                print_table(Plan::Summarize {
                    input: Box::new(Plan::SourceExpr(Box::new(empty_tbl.clone()))),
                    aggs: vec![
                        AggItem {
                            name: "n".into(),
                            op: AggOp::Count,
                            arg: None,
                        },
                        AggItem {
                            name: "m".into(),
                            op: AggOp::Mean,
                            arg: Some(RowExpr::Col("xf".into())),
                        },
                    ],
                    distinct_key: None,
                }),
                print_table(Plan::Summarize {
                    input: Box::new(Plan::GroupBy {
                        input: Box::new(Plan::SourceExpr(Box::new(empty_tbl))),
                        keys: vec!["g".into()],
                    }),
                    aggs: vec![AggItem {
                        name: "n".into(),
                        op: AggOp::Count,
                        arg: None,
                    }],
                    distinct_key: None,
                }),
            )),
        );
    }

    // 34. Right-to-left integer sum overflow order subtlety (`sumSortedInts`!)
    {
        let s = TableTy {
            cols: vec![col("x", ScalarTy::Int, TagSet::empty())],
            ..TableTy::default()
        };
        let tbl = Expr::TableLit {
            schema: s,
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
        add!(
            "34_sum_sorted_ints_right_fold_overflow",
            mk_console_prog(print_table(Plan::Summarize {
                input: Box::new(Plan::SourceExpr(Box::new(tbl))),
                aggs: vec![AggItem {
                    name: "s".into(),
                    op: AggOp::Sum,
                    arg: Some(RowExpr::Col("x".into())),
                }],
                distinct_key: None,
            })),
        );
    }

    // 35. Window functions (all 6: rowNumber, rank, lag, lead, runningSum, rollingMean)
    {
        let w_schema = TableTy {
            cols: vec![
                col("p", ScalarTy::Text, TagSet::empty()),
                col("v", ScalarTy::Int, TagSet::empty()),
            ],
            ..TableTy::default()
        };
        let w_tbl = Expr::TableLit {
            schema: w_schema,
            rows: vec![
                RowLit {
                    cells: vec![Literal::Text("A".into()), Literal::int(30)],
                },
                RowLit {
                    cells: vec![Literal::Text("A".into()), Literal::int(10)],
                },
                RowLit {
                    cells: vec![Literal::Text("A".into()), Literal::int(10)],
                },
                RowLit {
                    cells: vec![Literal::Text("B".into()), Literal::int(5)],
                },
                RowLit {
                    cells: vec![Literal::Text("B".into()), Literal::int(15)],
                },
            ],
        };
        let plan = Plan::Window {
            input: Box::new(Plan::SourceExpr(Box::new(w_tbl))),
            items: vec![
                WindowItem {
                    name: "rn".into(),
                    win_fn: WindowFn::RowNumber,
                    over: vec!["p".into()],
                    order: vec![("v".into(), SortDir::Asc)],
                },
                WindowItem {
                    name: "rk".into(),
                    win_fn: WindowFn::Rank { col: "v".into() },
                    over: vec!["p".into()],
                    order: vec![("v".into(), SortDir::Asc)],
                },
                WindowItem {
                    name: "prev".into(),
                    win_fn: WindowFn::Lag {
                        col: "v".into(),
                        offset: BigInt::from(1u64),
                    },
                    over: vec!["p".into()],
                    order: vec![("v".into(), SortDir::Asc)],
                },
                WindowItem {
                    name: "nxt".into(),
                    win_fn: WindowFn::Lead {
                        col: "v".into(),
                        offset: BigInt::from(1u64),
                    },
                    over: vec!["p".into()],
                    order: vec![("v".into(), SortDir::Asc)],
                },
                WindowItem {
                    name: "rsum".into(),
                    win_fn: WindowFn::RunningSum { col: "v".into() },
                    over: vec!["p".into()],
                    order: vec![("v".into(), SortDir::Asc)],
                },
                WindowItem {
                    name: "rmean".into(),
                    win_fn: WindowFn::RollingMean {
                        col: "v".into(),
                        window_size: BigInt::from(2u64),
                    },
                    over: vec!["p".into()],
                    order: vec![("v".into(), SortDir::Asc)],
                },
            ],
        };
        add!("35_window_all_6_fns", mk_console_prog(print_table(plan)));
    }

    // 36. FillGaps, PivotWider, Crosstab
    {
        let fg_schema = TableTy {
            cols: vec![
                col("grp", ScalarTy::Text, TagSet::empty()),
                col("t", ScalarTy::Int, TagSet::empty()),
                col("val", ScalarTy::Int, TagSet::empty()),
            ],
            ..TableTy::default()
        };
        let fg_tbl = Expr::TableLit {
            schema: fg_schema,
            rows: vec![
                RowLit {
                    cells: vec![Literal::Text("B".into()), Literal::int(2), Literal::int(20)],
                },
                RowLit {
                    cells: vec![Literal::Text("A".into()), Literal::int(3), Literal::int(30)],
                },
                RowLit {
                    cells: vec![Literal::Text("A".into()), Literal::int(1), Literal::int(10)],
                },
            ],
        };
        add!(
            "36_fill_gaps",
            mk_console_prog(print_table(Plan::FillGaps {
                input: Box::new(Plan::SourceExpr(Box::new(fg_tbl))),
                col: "t".into(),
                step_micros: BigInt::from(1),
                over: vec!["grp".into()],
                fill: vec![("val".into(), Literal::int(0))],
            })),
        );

        let piv_schema = TableTy {
            cols: vec![
                col("id", ScalarTy::Text, TagSet::empty()),
                col("k", ScalarTy::Text, TagSet::empty()),
                col("v", ScalarTy::Int, TagSet::empty()),
            ],
            ..TableTy::default()
        };
        let piv_tbl = Expr::TableLit {
            schema: piv_schema,
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
        add!(
            "37_pivot_wider",
            mk_console_prog(print_table(Plan::PivotWider {
                input: Box::new(Plan::SourceExpr(Box::new(piv_tbl.clone()))),
                names_from: "k".into(),
                values_from: "v".into(),
                static_cols: vec!["q1".into(), "q2".into(), "q3".into()],
                fill: Literal::int(0),
            })),
        );
        add!(
            "38_crosstab",
            Program {
                funs: vec![FunDecl {
                    name: "main".into(),
                    kind: FunKind::Function,
                    is_pure: false,
                    params: vec![],
                    pc: TagSet::empty(),
                    ret: LTy::public(Ty::DynamicTable(TagSet::empty())),
                    body: Expr::Rel(Box::new(Plan::Crosstab {
                        input: Box::new(Plan::SourceExpr(Box::new(piv_tbl))),
                        rows_col: "id".into(),
                        cols_col: "k".into(),
                        values_col: "v".into(),
                        fill: Literal::int(0),
                    })),
                }],
                entry: Some("main".into()),
                ..Program::default()
            },
        );
    }

    // 39-44. Float & Stats edge cases (NaN payload, Inf, -0.0/+0.0, 1e80, 1e-82, 1e-170, 1e308, degenerate linreg, ttest)
    {
        let xy_schema = TableTy {
            cols: vec![
                col("x", ScalarTy::Float, TagSet::empty()),
                col("y", ScalarTy::Float, TagSet::empty()),
            ],
            ..TableTy::default()
        };
        let mk_xy = |pts: &[(Float64, Float64)]| Expr::TableLit {
            schema: xy_schema.clone(),
            rows: pts
                .iter()
                .map(|&(x, y)| RowLit {
                    cells: vec![Literal::Float(x), Literal::Float(y)],
                })
                .collect(),
        };

        // 39. Canonical NaN + -0.0/+0.0 + Inf in float aggregates & sort
        let special_tbl = mk_xy(&[
            (
                Float64::from_bits(0x7ff8_0000_0000_0001),
                Float64::from_f64(1.0),
            ),
            (
                Float64::from_bits(0x8000_0000_0000_0000),
                Float64::from_f64(2.0),
            ),
            (
                Float64::from_bits(0x0000_0000_0000_0000),
                Float64::from_f64(3.0),
            ),
            (
                Float64::from_bits(f64::INFINITY.to_bits()),
                Float64::from_f64(4.0),
            ),
        ]);
        add!(
            "39_float_nan_negzero_inf_aggs_and_sort",
            mk_console_prog(let_seq(
                "s",
                LTy::public(Ty::Unit),
                print_table(Plan::Sort {
                    input: Box::new(Plan::SourceExpr(Box::new(special_tbl.clone()))),
                    keys: vec![("x".into(), SortDir::Asc)],
                }),
                print_table(Plan::Summarize {
                    input: Box::new(Plan::SourceExpr(Box::new(special_tbl))),
                    aggs: vec![
                        AggItem {
                            name: "sum_x".into(),
                            op: AggOp::Sum,
                            arg: Some(RowExpr::Col("x".into())),
                        },
                        AggItem {
                            name: "mean_x".into(),
                            op: AggOp::Mean,
                            arg: Some(RowExpr::Col("x".into())),
                        },
                        AggItem {
                            name: "sd_x".into(),
                            op: AggOp::Stddev,
                            arg: Some(RowExpr::Col("x".into())),
                        },
                        AggItem {
                            name: "med_x".into(),
                            op: AggOp::Median,
                            arg: Some(RowExpr::Col("x".into())),
                        },
                    ],
                    distinct_key: None,
                }),
            )),
        );

        // 40. Extreme magnitude float aggregates (1e308, 1.7e308, 2e200, 2e-170, percentile lerp)
        let ext_tbl = mk_xy(&[
            (Float64::from_f64(-1.7e308), Float64::from_f64(0.0)),
            (Float64::from_f64(1.7e308), Float64::from_f64(2e-170)),
        ]);
        let ext_tbl2 = mk_xy(&[
            (Float64::from_f64(1e308), Float64::from_f64(0.0)),
            (Float64::from_f64(1.7e308), Float64::from_f64(2e200)),
        ]);
        add!(
            "40_float_extreme_magnitudes",
            mk_console_prog(let_seq(
                "a",
                LTy::public(Ty::Unit),
                print_table(Plan::Summarize {
                    input: Box::new(Plan::SourceExpr(Box::new(ext_tbl))),
                    aggs: vec![
                        AggItem {
                            name: "p50".into(),
                            op: AggOp::Percentile(Float64::from_f64(0.5)),
                            arg: Some(RowExpr::Col("x".into())),
                        },
                        AggItem {
                            name: "sd_small".into(),
                            op: AggOp::Stddev,
                            arg: Some(RowExpr::Col("y".into())),
                        },
                    ],
                    distinct_key: None,
                }),
                print_table(Plan::Summarize {
                    input: Box::new(Plan::SourceExpr(Box::new(ext_tbl2))),
                    aggs: vec![
                        AggItem {
                            name: "med_big".into(),
                            op: AggOp::Median,
                            arg: Some(RowExpr::Col("x".into())),
                        },
                        AggItem {
                            name: "mean_big".into(),
                            op: AggOp::Mean,
                            arg: Some(RowExpr::Col("x".into())),
                        },
                        AggItem {
                            name: "sd_big".into(),
                            op: AggOp::Stddev,
                            arg: Some(RowExpr::Col("y".into())),
                        },
                    ],
                    distinct_key: None,
                }),
            )),
        );

        // 41. statsCorr on 1e80 and 1e-82 + NaN rejection (verifying EXACT float64 bits via stop!)
        let t_1e80 = mk_xy(&[
            (Float64::from_f64(1e80), Float64::from_f64(2e80)),
            (Float64::from_f64(2e80), Float64::from_f64(4e80)),
            (Float64::from_f64(3e80), Float64::from_f64(6e80)),
        ]);
        let t_1e_82 = mk_xy(&[
            (Float64::from_f64(1e-82), Float64::from_f64(2e-82)),
            (Float64::from_f64(2e-82), Float64::from_f64(4e-82)),
            (Float64::from_f64(3e-82), Float64::from_f64(6e-82)),
        ]);
        let t_nan = mk_xy(&[
            (Float64::from_f64(1.0), Float64::from_f64(1.0)),
            (Float64::from_f64(2.0), Float64::CANONICAL_NAN),
            (Float64::from_f64(3.0), Float64::from_f64(3.0)),
        ]);
        add!(
            "41_stats_corr_scales_and_nan",
            mk_console_prog(let_seq(
                "r1",
                LTy::public(Ty::Unit),
                print_bool(Expr::Prim {
                    op: PrimOp::IsSome,
                    args: vec![Expr::Prim {
                        op: PrimOp::StatsCorr {
                            col_x: "x".into(),
                            col_y: "y".into(),
                        },
                        args: vec![t_1e80.clone()],
                    }],
                }),
                let_seq(
                    "r2",
                    LTy::public(Ty::Unit),
                    print_bool(Expr::Prim {
                        op: PrimOp::IsSome,
                        args: vec![Expr::Prim {
                            op: PrimOp::StatsCorr {
                                col_x: "x".into(),
                                col_y: "y".into(),
                            },
                            args: vec![t_1e_82.clone()],
                        }],
                    }),
                    print_bool(Expr::Prim {
                        op: PrimOp::IsNone,
                        args: vec![Expr::Prim {
                            op: PrimOp::StatsCorr {
                                col_x: "x".into(),
                                col_y: "y".into(),
                            },
                            args: vec![t_nan.clone()],
                        }],
                    }),
                ),
            )),
        );
        // 41b. Exact 64-bit IEEE-754 output of statsCorr on non-trivial correlation via public stop detail
        let t_nontriv_corr = mk_xy(&[
            (Float64::from_f64(1.0), Float64::from_f64(2.0)),
            (Float64::from_f64(2.0), Float64::from_f64(5.0)),
            (Float64::from_f64(3.0), Float64::from_f64(4.0)),
            (Float64::from_f64(4.0), Float64::from_f64(9.0)),
        ]);
        add!(
            "41b_stats_corr_exact_bits",
            Program {
                funs: vec![FunDecl {
                    name: "main".into(),
                    kind: FunKind::Function,
                    is_pure: false,
                    params: vec![],
                    pc: TagSet::empty(),
                    ret: LTy::public(Ty::Unit),
                    body: Expr::Stop {
                        kind: BugKind::UserStop,
                        detail: Some(Box::new(Expr::Tuple(vec![
                            Expr::Prim {
                                op: PrimOp::StatsCorr {
                                    col_x: "x".into(),
                                    col_y: "y".into(),
                                },
                                args: vec![t_nontriv_corr],
                            },
                            Expr::Prim {
                                op: PrimOp::StatsCorr {
                                    col_x: "x".into(),
                                    col_y: "y".into(),
                                },
                                args: vec![t_1e80],
                            },
                            Expr::Prim {
                                op: PrimOp::StatsCorr {
                                    col_x: "x".into(),
                                    col_y: "y".into(),
                                },
                                args: vec![t_1e_82],
                            },
                        ]))),
                    },
                }],
                entry: Some("main".into()),
                ..Program::default()
            },
        );

        // 42. statsLinReg on 1e-170 + constant y + print via stop detail (public!) to verify exact bits!
        let t_1e_170 = mk_xy(&[
            (Float64::from_f64(1e-170), Float64::from_f64(2e-170)),
            (Float64::from_f64(2e-170), Float64::from_f64(4e-170)),
            (Float64::from_f64(3e-170), Float64::from_f64(6e-170)),
        ]);
        let t_const_y = mk_xy(&[
            (Float64::from_f64(1.0), Float64::from_f64(5.0)),
            (Float64::from_f64(2.0), Float64::from_f64(5.0)),
        ]);
        add!(
            "42_stats_linreg_1e_170_and_const_y",
            mk_console_prog(let_seq(
                "m1",
                LTy::public(Ty::LinearModel),
                Expr::Prim {
                    op: PrimOp::StatsLinReg {
                        col_x: "x".into(),
                        col_y: "y".into(),
                    },
                    args: vec![t_1e_170],
                },
                let_seq(
                    "m2",
                    LTy::public(Ty::LinearModel),
                    Expr::Prim {
                        op: PrimOp::StatsLinReg {
                            col_x: "x".into(),
                            col_y: "y".into(),
                        },
                        args: vec![t_const_y],
                    },
                    print_bool(Expr::Prim {
                        op: PrimOp::Ne,
                        args: vec![Expr::Var("m1".into()), Expr::Var("m2".into())],
                    }),
                ),
            )),
        );

        // 43. Degenerate statsLinReg (zero x-variance & NaN) -> divByZero stop
        let t_zero_x = mk_xy(&[
            (Float64::from_f64(5.0), Float64::from_f64(1.0)),
            (Float64::from_f64(5.0), Float64::from_f64(2.0)),
        ]);
        add!(
            "43_stats_linreg_degenerate_zero_x",
            Program {
                funs: vec![FunDecl {
                    name: "main".into(),
                    kind: FunKind::Function,
                    is_pure: false,
                    params: vec![],
                    pc: TagSet::empty(),
                    ret: LTy::public(Ty::LinearModel),
                    body: Expr::Prim {
                        op: PrimOp::StatsLinReg {
                            col_x: "x".into(),
                            col_y: "y".into(),
                        },
                        args: vec![t_zero_x],
                    },
                }],
                entry: Some("main".into()),
                ..Program::default()
            },
        );
        add!(
            "44_stats_linreg_degenerate_nan",
            Program {
                funs: vec![FunDecl {
                    name: "main".into(),
                    kind: FunKind::Function,
                    is_pure: false,
                    params: vec![],
                    pc: TagSet::empty(),
                    ret: LTy::public(Ty::LinearModel),
                    body: Expr::Prim {
                        op: PrimOp::StatsLinReg {
                            col_x: "x".into(),
                            col_y: "y".into(),
                        },
                        args: vec![t_nan],
                    },
                }],
                entry: Some("main".into()),
                ..Program::default()
            },
        );

        // 45. statsTTest outside boundary stop
        add!(
            "45_stats_ttest_outside_boundary",
            Program {
                funs: vec![FunDecl {
                    name: "main".into(),
                    kind: FunKind::Function,
                    is_pure: false,
                    params: vec![],
                    pc: TagSet::empty(),
                    ret: LTy::public(Ty::StatTest),
                    body: Expr::Prim {
                        op: PrimOp::StatsTTest {
                            col_x: "x".into(),
                            col_y: "y".into(),
                        },
                        args: vec![mk_xy(&[(Float64::from_f64(1.0), Float64::from_f64(2.0))])],
                    },
                }],
                entry: Some("main".into()),
                ..Program::default()
            },
        );

        // 46. Out-of-range & NaN percentile static rejections
        for (lbl, p) in [
            ("46_bad_percentile_gt1", Float64::from_f64(1.5)),
            ("47_bad_percentile_lt0", Float64::from_f64(-0.1)),
            ("48_bad_percentile_nan", Float64::CANONICAL_NAN),
        ] {
            add!(
                lbl,
                mk_console_prog(print_table(Plan::Summarize {
                    input: Box::new(Plan::SourceExpr(Box::new(mk_xy(&[(
                        Float64::from_f64(1.0),
                        Float64::from_f64(2.0),
                    )])))),
                    aggs: vec![AggItem {
                        name: "p".into(),
                        op: AggOp::Percentile(p),
                        arg: Some(RowExpr::Col("x".into())),
                    }],
                    distinct_key: None,
                })),
            );
        }
    }

    // 49. Chart + Report + WriteReportHtml + TableProfile
    {
        let s = TableTy {
            cols: vec![
                col("cat", ScalarTy::Text, TagSet::empty()),
                col("val", ScalarTy::Int, TagSet::empty()),
            ],
            ..TableTy::default()
        };
        let t = Expr::TableLit {
            schema: s,
            rows: vec![
                RowLit {
                    cells: vec![Literal::Text("A".into()), Literal::int(10)],
                },
                RowLit {
                    cells: vec![Literal::Text("B".into()), Literal::int(20)],
                },
            ],
        };
        add!(
            "49_chart_report_write_html_profile",
            Program {
                funs: vec![FunDecl {
                    name: "main".into(),
                    kind: FunKind::Function,
                    is_pure: false,
                    params: vec![(
                        "out".into(),
                        LTy::public(Ty::WriteFiles {
                            root: "reports/".into(),
                            allows: TagSet::empty(),
                        }),
                    )],
                    pc: TagSet::empty(),
                    ret: LTy::public(Ty::Result {
                        ok_ty: Box::new(Ty::Unit),
                        err_ty: Box::new(Ty::Text),
                    }),
                    body: let_seq(
                        "prof",
                        LTy::public(Ty::Profile(TagSet::empty())),
                        Expr::Prim {
                            op: PrimOp::TableProfile,
                            args: vec![t.clone()],
                        },
                        let_seq(
                            "ch",
                            LTy::public(Ty::Chart(TagSet::empty())),
                            Expr::Prim {
                                op: PrimOp::ChartMake {
                                    kind: ChartKind::Bar,
                                    cols: vec!["cat".into(), "val".into()],
                                    title: "Sales".into(),
                                },
                                args: vec![t.clone()],
                            },
                            let_seq(
                                "r0",
                                LTy::public(Ty::Report(TagSet::empty())),
                                Expr::Prim {
                                    op: PrimOp::ReportNew,
                                    args: vec![Expr::Lit(Literal::Text("Q1".into()))],
                                },
                                let_seq(
                                    "r1",
                                    LTy::public(Ty::Report(TagSet::empty())),
                                    Expr::Prim {
                                        op: PrimOp::ReportAddSummary,
                                        args: vec![
                                            Expr::Var("r0".into()),
                                            Expr::Lit(Literal::Text("All good".into())),
                                        ],
                                    },
                                    let_seq(
                                        "r2",
                                        LTy::public(Ty::Report(TagSet::empty())),
                                        Expr::Prim {
                                            op: PrimOp::ReportAddChart,
                                            args: vec![
                                                Expr::Var("r1".into()),
                                                Expr::Var("ch".into()),
                                            ],
                                        },
                                        let_seq(
                                            "r3",
                                            LTy::public(Ty::Report(TagSet::empty())),
                                            Expr::Prim {
                                                op: PrimOp::ReportAddTable,
                                                args: vec![Expr::Var("r2".into()), t],
                                            },
                                            Expr::Host {
                                                op: HostOp::WriteReportHtml,
                                                args: vec![
                                                    Expr::Var("out".into()),
                                                    Expr::Lit(Literal::Text("q1.html".into())),
                                                    Expr::Var("r3".into()),
                                                ],
                                            },
                                        ),
                                    ),
                                ),
                            ),
                        ),
                    ),
                }],
                entry: Some("main".into()),
                ..Program::default()
            },
        );
    }

    // 50-56. Privacy: bucket + suppress_small_groups (Drop & MaskComplementary tie-break),
    // redact, pseudonymize (including Unicode!), blending vs non-blending, implicit flow leak
    {
        let priv_schema = TableTy {
            cols: vec![
                col("id", ScalarTy::Int, ts(&["pii"])),
                col("email", ScalarTy::Text, ts(&["pii"])),
                col("dept", ScalarTy::Text, TagSet::empty()),
                col("score", ScalarTy::Int, ts(&["ferpa"])),
            ],
            ..TableTy::default()
        };
        let mut rows = vec![
            // Dept A: 1 row (<5)
            RowLit {
                cells: vec![
                    Literal::int(1),
                    Literal::Text("a@u.edu".into()),
                    Literal::Text("A".into()),
                    Literal::int(90),
                ],
            },
            // Dept B: 1 row (<5) -> small_sum = 2 < 5 -> triggers complementary masking!
            RowLit {
                cells: vec![
                    Literal::int(2),
                    Literal::Text("b@u.edu".into()),
                    Literal::Text("B".into()),
                    Literal::int(80),
                ],
            },
        ];
        // Dept C1 and C2 both have 5 rows -> tie-break by group key picks "C1"!
        for i in 0..5 {
            rows.push(RowLit {
                cells: vec![
                    Literal::int(10 + i),
                    Literal::Text("c1@u.edu".into()),
                    Literal::Text("C1".into()),
                    Literal::int(70 + i),
                ],
            });
            rows.push(RowLit {
                cells: vec![
                    Literal::int(20 + i),
                    Literal::Text("c2@u.edu".into()),
                    Literal::Text("C2".into()),
                    Literal::int(60 + i),
                ],
            });
        }
        let priv_tbl = Expr::TableLit {
            schema: priv_schema.clone(),
            rows,
        };

        // 50. MaskComplementary with tie-breaking on group key
        add!(
            "50_suppress_mask_complementary_tiebreak",
            mk_console_prog(print_table(Plan::SuppressSmallGroups {
                input: Box::new(Plan::Summarize {
                    input: Box::new(Plan::GroupBy {
                        input: Box::new(Plan::SourceExpr(Box::new(priv_tbl.clone()))),
                        keys: vec!["dept".into()],
                    }),
                    aggs: vec![
                        AggItem {
                            name: "n".into(),
                            op: AggOp::Count,
                            arg: None,
                        },
                        AggItem {
                            name: "sd".into(),
                            op: AggOp::Stddev,
                            arg: Some(RowExpr::Col("score".into())),
                        },
                    ],
                    distinct_key: Some("id".into()),
                }),
                min_k: BigInt::from(5u64),
                distinct_by: Some("id".into()),
                mode: SuppressMode::MaskComplementary,
            })),
        );

        // 51. Bucket + Drop with distinct_by
        add!(
            "51_bucket_suppress_drop",
            mk_console_prog(print_table(Plan::SuppressSmallGroups {
                input: Box::new(Plan::Summarize {
                    input: Box::new(Plan::GroupBy {
                        input: Box::new(Plan::Derive {
                            input: Box::new(Plan::SourceExpr(Box::new(priv_tbl.clone()))),
                            items: vec![DeriveItem::BucketCol {
                                name: "band".into(),
                                source: "score".into(),
                                cuts: vec![Literal::int(75)],
                                labels: vec!["low".into(), "high".into()],
                            }],
                        }),
                        keys: vec!["band".into()],
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
                    distinct_key: Some("id".into()),
                }),
                min_k: BigInt::from(5u64),
                distinct_by: Some("id".into()),
                mode: SuppressMode::Drop,
            })),
        );

        // 52. Redact + Pseudonymize (including non-ASCII Unicode email!)
        let uni_tbl = Expr::TableLit {
            schema: priv_schema.clone(),
            rows: vec![RowLit {
                cells: vec![
                    Literal::int(1),
                    Literal::Text("josé@uni.edu".into()),
                    Literal::Text("CS".into()),
                    Literal::int(95),
                ],
            }],
        };
        add!(
            "52_redact_and_pseudonymize_unicode",
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
                        print_table(Plan::Select {
                            input: Box::new(Plan::Redact {
                                input: Box::new(Plan::SourceExpr(Box::new(uni_tbl.clone()))),
                                col: "email".into(),
                                replacement: "[MASKED]".into(),
                            }),
                            cols: vec!["dept".into(), "email".into()],
                        }),
                        print_table(Plan::Select {
                            input: Box::new(Plan::Pseudonymize {
                                input: Box::new(Plan::SourceExpr(Box::new(uni_tbl))),
                                col: "email".into(),
                                secret: Box::new(Expr::Var("salt".into())),
                            }),
                            cols: vec!["dept".into(), "email".into()],
                        }),
                    ),
                }],
                entry: Some("main".into()),
                ..Program::default()
            },
        );

        // 53. Rejected: Implicit-flow filter/count leak
        add!(
            "53_reject_implicit_flow_filter_count",
            mk_console_prog(print_table(Plan::Summarize {
                input: Box::new(Plan::GroupBy {
                    input: Box::new(Plan::Select {
                        input: Box::new(Plan::Filter {
                            input: Box::new(Plan::SourceExpr(Box::new(priv_tbl.clone()))),
                            pred: RowExpr::Prim {
                                op: PrimOp::Lt,
                                args: vec![
                                    RowExpr::Col("score".into()),
                                    RowExpr::Lit(Literal::int(70)),
                                ],
                            },
                        }),
                        cols: vec!["dept".into()],
                    }),
                    keys: vec!["dept".into()],
                }),
                aggs: vec![AggItem {
                    name: "n".into(),
                    op: AggOp::Count,
                    arg: None,
                }],
                distinct_key: None,
            })),
        );

        // 54. Rejected: Non-blending median stays tagged after suppress_small_groups
        add!(
            "54_reject_median_after_suppress",
            mk_console_prog(print_table(Plan::SuppressSmallGroups {
                input: Box::new(Plan::Summarize {
                    input: Box::new(Plan::GroupBy {
                        input: Box::new(Plan::SourceExpr(Box::new(priv_tbl.clone()))),
                        keys: vec!["dept".into()],
                    }),
                    aggs: vec![AggItem {
                        name: "med".into(),
                        op: AggOp::Median,
                        arg: Some(RowExpr::Col("score".into())),
                    }],
                    distinct_key: None,
                }),
                min_k: BigInt::from(5u64),
                distinct_by: None,
                mode: SuppressMode::Drop,
            })),
        );

        // 55. Rejected: Raw non-bucketed [pii] group key stays tagged after suppress_small_groups
        add!(
            "55_reject_raw_pii_groupkey",
            mk_console_prog(print_table(Plan::SuppressSmallGroups {
                input: Box::new(Plan::Summarize {
                    input: Box::new(Plan::GroupBy {
                        input: Box::new(Plan::SourceExpr(Box::new(priv_tbl))),
                        keys: vec!["email".into()],
                    }),
                    aggs: vec![AggItem {
                        name: "n".into(),
                        op: AggOp::Count,
                        arg: None,
                    }],
                    distinct_key: None,
                }),
                min_k: BigInt::from(5u64),
                distinct_by: None,
                mode: SuppressMode::Drop,
            })),
        );
    }

    // 56-57. WriteTable valid + Probe P2 row-tag taint rejection
    {
        let pub_cols = vec![
            col("dept", ScalarTy::Text, TagSet::empty()),
            col("n", ScalarTy::Int, TagSet::empty()),
        ];
        let src = Expr::TableLit {
            schema: TableTy {
                cols: pub_cols.clone(),
                ..TableTy::default()
            },
            rows: vec![RowLit {
                cells: vec![Literal::Text("CS".into()), Literal::int(42)],
            }],
        };
        add!(
            "56_write_table_ok",
            Program {
                funs: vec![FunDecl {
                    name: "main".into(),
                    kind: FunKind::Function,
                    is_pure: false,
                    params: vec![(
                        "wt".into(),
                        LTy::public(Ty::WriteTable {
                            db: "wh".into(),
                            table_name: "counts".into(),
                            dest_cols: pub_cols,
                            dest_row_tags: TagSet::empty(),
                            allows: TagSet::empty(),
                        }),
                    )],
                    pc: TagSet::empty(),
                    ret: LTy::public(Ty::Result {
                        ok_ty: Box::new(Ty::Int),
                        err_ty: Box::new(Ty::Text),
                    }),
                    body: Expr::Host {
                        op: HostOp::WriteTable,
                        args: vec![Expr::Var("wt".into()), src],
                    },
                }],
                entry: Some("main".into()),
                ..Program::default()
            },
        );

        let leak_src = Expr::TableLit {
            schema: TableTy {
                cols: vec![
                    col("dept", ScalarTy::Text, TagSet::empty()),
                    col("n", ScalarTy::Int, ts(&["ferpa"])),
                ],
                row_tags: ts(&["ferpa"]),
                ..TableTy::default()
            },
            rows: vec![],
        };
        add!(
            "57_reject_write_table_row_tag_leak",
            Program {
                funs: vec![FunDecl {
                    name: "main".into(),
                    kind: FunKind::Function,
                    is_pure: false,
                    params: vec![(
                        "wt".into(),
                        LTy::public(Ty::WriteTable {
                            db: "wh".into(),
                            table_name: "counts".into(),
                            dest_cols: vec![
                                col("dept", ScalarTy::Text, TagSet::empty()),
                                col("n", ScalarTy::Int, ts(&["ferpa"])),
                            ],
                            dest_row_tags: TagSet::empty(),
                            allows: ts(&["ferpa"]),
                        }),
                    )],
                    pc: TagSet::empty(),
                    ret: LTy::new(
                        Ty::Result {
                            ok_ty: Box::new(Ty::Int),
                            err_ty: Box::new(Ty::Text),
                        },
                        ts(&["ferpa"]),
                    ),
                    body: Expr::Host {
                        op: HostOp::WriteTable,
                        args: vec![Expr::Var("wt".into()), leak_src],
                    },
                }],
                entry: Some("main".into()),
                ..Program::default()
            },
        );
    }

    // 58-61. dana.policy checks (minGroupSize, forbidManualDeclassify, export prefix/traversal)
    {
        let strict_pol = Policy {
            min_group_size: BigInt::from(10u64),
            forbid_manual_declassify: true,
            forbid_repl_sensitive: true,
            allow_console: TagSet::empty(),
            allow_export: vec![("reports/".into(), ts(&["ferpa"]))],
            allow_https: vec![],
            allow_write: vec![],
            ..Policy::default()
        };
        add!(
            "58_policy_subpath_ok",
            Program {
                policy: Some(strict_pol.clone()),
                funs: vec![FunDecl {
                    name: "main".into(),
                    kind: FunKind::Function,
                    is_pure: false,
                    params: vec![(
                        "out".into(),
                        LTy::public(Ty::WriteFiles {
                            root: "reports/q1/".into(),
                            allows: ts(&["ferpa"]),
                        }),
                    )],
                    pc: TagSet::empty(),
                    ret: LTy::public(Ty::Unit),
                    body: Expr::Lit(Literal::Unit),
                }],
                entry: Some("main".into()),
                ..Program::default()
            },
        );
        add!(
            "59_policy_reject_traversal",
            Program {
                policy: Some(strict_pol.clone()),
                funs: vec![FunDecl {
                    name: "main".into(),
                    kind: FunKind::Function,
                    is_pure: false,
                    params: vec![(
                        "out".into(),
                        LTy::public(Ty::WriteFiles {
                            root: "reports/../tmp/".into(),
                            allows: ts(&["ferpa"]),
                        }),
                    )],
                    pc: TagSet::empty(),
                    ret: LTy::public(Ty::Unit),
                    body: Expr::Lit(Literal::Unit),
                }],
                entry: Some("main".into()),
                ..Program::default()
            },
        );
        add!(
            "60_policy_reject_manual_declassify",
            Program {
                policy: Some(strict_pol),
                funs: vec![FunDecl {
                    name: "main".into(),
                    kind: FunKind::Function,
                    is_pure: false,
                    params: vec![("d".into(), LTy::public(Ty::Declassify(ts(&["ferpa"]))))],
                    pc: TagSet::empty(),
                    ret: LTy::public(Ty::Unit),
                    body: Expr::Lit(Literal::Unit),
                }],
                entry: Some("main".into()),
                ..Program::default()
            },
        );
        // 61. Allowed manual DeclassifyApprove
        add!(
            "61_manual_declassify_approve_ok",
            Program {
                funs: vec![FunDecl {
                    name: "main".into(),
                    kind: FunKind::Function,
                    is_pure: false,
                    params: vec![
                        ("d".into(), LTy::public(Ty::Declassify(ts(&["ferpa"])))),
                        ("c".into(), LTy::public(Ty::Console(TagSet::empty()))),
                    ],
                    pc: TagSet::empty(),
                    ret: LTy::public(Ty::Unit),
                    body: let_seq(
                        "s",
                        LTy::new(Ty::Text, ts(&["ferpa"])),
                        Expr::Lit(Literal::Text("band-A".into())),
                        print_str(Expr::Host {
                            op: HostOp::DeclassifyApprove(ts(&["ferpa"])),
                            args: vec![
                                Expr::Var("d".into()),
                                Expr::Var("s".into()),
                                Expr::Lit(Literal::Text("registrar approved".into())),
                            ],
                        }),
                    ),
                }],
                entry: Some("main".into()),
                ..Program::default()
            },
        );
    }

    // 62-63. Runtime --allow-export gate (denied upfront with zero partial stdout vs granted!)
    {
        let gate_prog = Program {
            funs: vec![FunDecl {
                name: "main".into(),
                kind: FunKind::Function,
                is_pure: false,
                params: vec![
                    ("c".into(), LTy::public(Ty::Console(TagSet::empty()))),
                    (
                        "out".into(),
                        LTy::public(Ty::WriteFiles {
                            root: "exports/".into(),
                            allows: ts(&["pii"]),
                        }),
                    ),
                ],
                pc: TagSet::empty(),
                ret: LTy::public(Ty::Unit),
                body: print_str(Expr::Lit(Literal::Text(
                    "should_only_appear_when_allowed".into(),
                ))),
            }],
            entry: Some("main".into()),
            ..Program::default()
        };
        cases.push(CorpusCase {
            name: "62_export_gate_denied_upfront",
            prog: gate_prog.clone(),
            fuel: None,
            allow_export: None,
        });
        cases.push(CorpusCase {
            name: "63_export_gate_authorized",
            prog: gate_prog,
            fuel: None,
            allow_export: Some("pii"),
        });
    }

    // 64-67. Runtime path confinement (traversal, absolute, backslash, safe root join)
    for (lbl, root, rel) in [
        ("64_path_reject_traversal", "reports/", "../leak.csv"),
        ("65_path_reject_absolute", "reports/", "/etc/passwd"),
        ("66_path_reject_backslash", "reports/", "sub\\..\\leak.csv"),
        ("67_path_safe_join_no_slash", "out", "_evil/x.csv"),
    ] {
        add!(
            lbl,
            Program {
                funs: vec![FunDecl {
                    name: "main".into(),
                    kind: FunKind::Function,
                    is_pure: false,
                    params: vec![(
                        "out".into(),
                        LTy::public(Ty::WriteFiles {
                            root: root.into(),
                            allows: TagSet::empty(),
                        }),
                    )],
                    pc: TagSet::empty(),
                    ret: LTy::public(Ty::Result {
                        ok_ty: Box::new(Ty::Unit),
                        err_ty: Box::new(Ty::Text),
                    }),
                    body: Expr::Host {
                        op: HostOp::WriteFile,
                        args: vec![
                            Expr::Var("out".into()),
                            Expr::Lit(Literal::Text(rel.into())),
                            Expr::Lit(Literal::Text("payload".into())),
                        ],
                    },
                }],
                entry: Some("main".into()),
                ..Program::default()
            },
        );
    }

    // 68-70. Explicit `.stop` (none, public detail, sensitive `[pii]` detail redacted)
    add!(
        "68_stop_no_detail",
        Program {
            funs: vec![FunDecl {
                name: "main".into(),
                kind: FunKind::Function,
                is_pure: false,
                params: vec![],
                pc: TagSet::empty(),
                ret: LTy::public(Ty::Unit),
                body: Expr::Stop {
                    kind: BugKind::UserStop,
                    detail: None,
                },
            }],
            entry: Some("main".into()),
            ..Program::default()
        },
    );
    add!(
        "69_stop_public_detail",
        Program {
            funs: vec![FunDecl {
                name: "main".into(),
                kind: FunKind::Function,
                is_pure: false,
                params: vec![],
                pc: TagSet::empty(),
                ret: LTy::public(Ty::Unit),
                body: Expr::Stop {
                    kind: BugKind::PromiseViolation,
                    detail: Some(Box::new(Expr::Lit(Literal::Text("bad count".into())))),
                },
            }],
            entry: Some("main".into()),
            ..Program::default()
        },
    );
    add!(
        "70_stop_redacted_pii_detail",
        Program {
            funs: vec![FunDecl {
                name: "main".into(),
                kind: FunKind::Function,
                is_pure: false,
                params: vec![],
                pc: TagSet::empty(),
                ret: LTy::public(Ty::Unit),
                body: let_seq(
                    "ssn",
                    LTy::new(Ty::Text, ts(&["pii"])),
                    Expr::Lit(Literal::Text("999-99-9999".into())),
                    Expr::Stop {
                        kind: BugKind::UserStop,
                        detail: Some(Box::new(Expr::Var("ssn".into()))),
                    },
                ),
            }],
            entry: Some("main".into()),
            ..Program::default()
        },
    );

    // 71-74. Host ops: argsGet, clockNow, consoleError, readCsv empty, outside-boundary ops
    add!(
        "71_args_clock_stderr_readcsv",
        Program {
            schemas: vec![SchemaDecl {
                name: "Row".into(),
                schema: TableTy {
                    cols: vec![col("x", ScalarTy::Int, TagSet::empty())],
                    ..TableTy::default()
                },
            }],
            funs: vec![FunDecl {
                name: "main".into(),
                kind: FunKind::Function,
                is_pure: false,
                params: vec![
                    ("a".into(), LTy::public(Ty::Args)),
                    ("clk".into(), LTy::public(Ty::Clock)),
                    ("rf".into(), LTy::public(Ty::ReadFiles)),
                    ("c".into(), LTy::public(Ty::Console(TagSet::empty()))),
                ],
                pc: TagSet::empty(),
                ret: LTy::public(Ty::Unit),
                body: let_seq(
                    "n",
                    LTy::public(Ty::Int),
                    Expr::Prim {
                        op: PrimOp::ListLen,
                        args: vec![Expr::Host {
                            op: HostOp::ArgsGet,
                            args: vec![Expr::Var("a".into())],
                        }],
                    },
                    let_seq(
                        "_t",
                        LTy::public(Ty::Timestamp),
                        Expr::Host {
                            op: HostOp::ClockNow,
                            args: vec![Expr::Var("clk".into())],
                        },
                        let_seq(
                            "_e",
                            LTy::public(Ty::Unit),
                            Expr::Host {
                                op: HostOp::ConsoleError,
                                args: vec![
                                    Expr::Var("c".into()),
                                    Expr::Lit(Literal::Text("warn".into())),
                                ],
                            },
                            let_seq(
                                "_csv",
                                LTy::public(Ty::Result {
                                    ok_ty: Box::new(Ty::Tuple(vec![
                                        LTy::public(Ty::Table(TableTy {
                                            cols: vec![col("x", ScalarTy::Int, TagSet::empty())],
                                            ..TableTy::default()
                                        })),
                                        LTy::public(Ty::Table(
                                            dana::core::check::quarantine_bad_row_table_ty(
                                                &TableTy {
                                                    cols: vec![col(
                                                        "x",
                                                        ScalarTy::Int,
                                                        TagSet::empty(),
                                                    )],
                                                    ..TableTy::default()
                                                },
                                            ),
                                        )),
                                    ])),
                                    err_ty: Box::new(Ty::Text),
                                }),
                                Expr::Host {
                                    op: HostOp::ReadCsv("Row".into()),
                                    args: vec![
                                        Expr::Var("rf".into()),
                                        Expr::Lit(Literal::Text("missing.csv".into())),
                                    ],
                                },
                                print_int(Expr::Var("n".into())),
                            ),
                        ),
                    ),
                ),
            }],
            entry: Some("main".into()),
            ..Program::default()
        },
    );

    add!(
        "72_outside_boundary_raw_sql",
        Program {
            funs: vec![FunDecl {
                name: "main".into(),
                kind: FunKind::Function,
                is_pure: false,
                params: vec![("db".into(), LTy::public(Ty::RawReadDB("main".into())))],
                pc: TagSet::empty(),
                ret: LTy::public(Ty::Result {
                    ok_ty: Box::new(Ty::Table(TableTy {
                        cols: vec![col("x", ScalarTy::Int, TagSet::empty())],
                        ..TableTy::default()
                    })),
                    err_ty: Box::new(Ty::Text),
                }),
                body: Expr::Host {
                    op: HostOp::RawSqlQuery {
                        db: "main".into(),
                        out_schema: TableTy {
                            cols: vec![col("x", ScalarTy::Int, TagSet::empty())],
                            ..TableTy::default()
                        },
                    },
                    args: vec![
                        Expr::Var("db".into()),
                        Expr::Lit(Literal::Text("SELECT 1".into())),
                    ],
                },
            }],
            entry: Some("main".into()),
            ..Program::default()
        },
    );

    add!(
        "73_outside_boundary_https_get",
        Program {
            funs: vec![FunDecl {
                name: "main".into(),
                kind: FunKind::Function,
                is_pure: false,
                params: vec![(
                    "h".into(),
                    LTy::public(Ty::HttpsAllow {
                        host: "example.org".into(),
                        allows: TagSet::empty(),
                    }),
                )],
                pc: TagSet::empty(),
                ret: LTy::public(Ty::Result {
                    ok_ty: Box::new(Ty::Text),
                    err_ty: Box::new(Ty::Text),
                }),
                body: Expr::Host {
                    op: HostOp::HttpsGetJson,
                    args: vec![
                        Expr::Var("h".into()),
                        Expr::Lit(Literal::Text("https://example.org/data.json".into())),
                    ],
                },
            }],
            entry: Some("main".into()),
            ..Program::default()
        },
    );

    add!(
        "74_outside_boundary_write_parquet",
        Program {
            funs: vec![FunDecl {
                name: "main".into(),
                kind: FunKind::Function,
                is_pure: false,
                params: vec![(
                    "out".into(),
                    LTy::public(Ty::WriteFiles {
                        root: "out/".into(),
                        allows: TagSet::empty(),
                    }),
                )],
                pc: TagSet::empty(),
                ret: LTy::public(Ty::Result {
                    ok_ty: Box::new(Ty::Unit),
                    err_ty: Box::new(Ty::Text),
                }),
                body: Expr::Host {
                    op: HostOp::WriteParquet,
                    args: vec![
                        Expr::Var("out".into()),
                        Expr::Lit(Literal::Text("t.parquet".into())),
                        Expr::TableLit {
                            schema: TableTy {
                                cols: vec![col("x", ScalarTy::Int, TagSet::empty())],
                                ..TableTy::default()
                            },
                            rows: vec![],
                        },
                    ],
                },
            }],
            entry: Some("main".into()),
            ..Program::default()
        },
    );

    // 75. Custom tag + metadata with C0/C1/DEL escapes + spec helper function
    add!(
        "75_custom_tag_metadata_and_spec_helper",
        Program {
            version: CoreVersion { major: 0, minor: 1 },
            tags: vec!["donor".into()],
            funs: vec![
                FunDecl {
                    name: "main".into(),
                    kind: FunKind::Function,
                    is_pure: false,
                    params: vec![("c".into(), LTy::public(Ty::Console(TagSet::empty())))],
                    pc: TagSet::empty(),
                    ret: LTy::public(Ty::Unit),
                    body: print_str(Expr::Lit(Literal::Text("ok\u{07}\u{85}".into()))),
                },
                FunDecl {
                    name: "spec_helper".into(),
                    kind: FunKind::Test,
                    is_pure: false,
                    params: vec![],
                    pc: TagSet::empty(),
                    ret: LTy::public(Ty::Unit),
                    body: let_seq(
                        "fc",
                        LTy::public(Ty::Console(ts(&["donor"]))),
                        Expr::Host {
                            op: HostOp::FakeConsole(ts(&["donor"])),
                            args: vec![],
                        },
                        Expr::Host {
                            op: HostOp::ConsolePrint,
                            args: vec![
                                Expr::Var("fc".into()),
                                Expr::Lit(Literal::Text("spec".into())),
                            ],
                        },
                    ),
                },
            ],
            entry: Some("main".into()),
            metadata: CompilerMetadata {
                entries: vec![MetaEntry {
                    node_id: "m1".into(),
                    orig_name: Some("donor\t\"meta\"\u{85}".into()),
                    span: Some(SourceSpan {
                        file: "donor.dana".into(),
                        start_line: BigInt::from(1u64),
                        start_col: BigInt::from(1u64),
                        end_line: BigInt::from(1u64),
                        end_col: BigInt::from(12u64),
                    }),
                }],
            },
            ..Program::default()
        },
    );

    // 76. Window RunningSum overflow fallback (falls back to 0 matching Eval.lean:1475-1477!)
    {
        let s = TableTy {
            cols: vec![col("v", ScalarTy::Int, TagSet::empty())],
            ..TableTy::default()
        };
        let t = Expr::TableLit {
            schema: s,
            rows: vec![
                RowLit {
                    cells: vec![Literal::int(i64::MAX)],
                },
                RowLit {
                    cells: vec![Literal::int(1)],
                },
            ],
        };
        add!(
            "76_window_running_sum_overflow_fallback",
            mk_console_prog(print_table(Plan::Window {
                input: Box::new(Plan::SourceExpr(Box::new(t))),
                items: vec![WindowItem {
                    name: "rs".into(),
                    win_fn: WindowFn::RunningSum { col: "v".into() },
                    over: vec![],
                    order: vec![],
                }],
            })),
        );
    }

    // 77. Nested Join points + sensitive pc widening re-check
    add!(
        "77_nested_join_and_pc_widening",
        Program {
            funs: vec![FunDecl {
                name: "main".into(),
                kind: FunKind::Function,
                is_pure: false,
                params: vec![("c".into(), LTy::public(Ty::Console(ts(&["pii"]))))],
                pc: TagSet::empty(),
                ret: LTy::public(Ty::Unit),
                body: let_seq(
                    "flag",
                    LTy::new(Ty::Bool, ts(&["pii"])),
                    Expr::Lit(Literal::Bool(true)),
                    let_seq(
                        "res",
                        LTy::new(Ty::Int, ts(&["pii"])),
                        Expr::Join {
                            label: "outer".into(),
                            params: vec![("x".into(), LTy::new(Ty::Int, ts(&["pii"])))],
                            rhs: Box::new(Expr::Var("x".into())),
                            body: Box::new(Expr::Join {
                                label: "inner".into(),
                                params: vec![("y".into(), LTy::new(Ty::Int, ts(&["pii"])))],
                                rhs: Box::new(Expr::Jump {
                                    label: "outer".into(),
                                    args: vec![Expr::Prim {
                                        op: PrimOp::AddInt,
                                        args: vec![
                                            Expr::Var("y".into()),
                                            Expr::Lit(Literal::int(5))
                                        ],
                                    }],
                                }),
                                body: Box::new(Expr::IfE {
                                    cond: Box::new(Expr::Var("flag".into())),
                                    then_br: Box::new(Expr::Jump {
                                        label: "inner".into(),
                                        args: vec![Expr::Lit(Literal::int(37))],
                                    }),
                                    else_br: Box::new(Expr::Lit(Literal::int(0))),
                                }),
                            }),
                        },
                        print_int(Expr::Var("res".into())),
                    ),
                ),
            }],
            entry: Some("main".into()),
            ..Program::default()
        },
    );
    if let Some(last) = cases.last_mut() {
        last.allow_export = Some("pii");
    }

    // 78. Bytes literal comparison & table rendering
    {
        let bs = TableTy {
            cols: vec![col("b", ScalarTy::Bytes, TagSet::empty())],
            ..TableTy::default()
        };
        let tbl = Expr::TableLit {
            schema: bs,
            rows: vec![
                RowLit {
                    cells: vec![Literal::Bytes(vec![0, 1, 255])],
                },
                RowLit {
                    cells: vec![Literal::Bytes(vec![])],
                },
            ],
        };
        add!(
            "78_bytes_literal_eq_and_table",
            mk_console_prog(let_seq(
                "e",
                LTy::public(Ty::Unit),
                print_bool(Expr::Prim {
                    op: PrimOp::Eq,
                    args: vec![
                        Expr::Lit(Literal::Bytes(vec![1, 2])),
                        Expr::Lit(Literal::Bytes(vec![1, 2])),
                    ],
                }),
                print_table(Plan::Distinct {
                    input: Box::new(Plan::SourceExpr(Box::new(tbl))),
                    cols: vec![],
                }),
            )),
        );
    }

    // 79. Sort on sensitive column -> Limit folds orderTags into rowTags (rejected at public console!)
    {
        let s = TableTy {
            cols: vec![
                col("pub_name", ScalarTy::Text, TagSet::empty()),
                col("sec_gpa", ScalarTy::Int, ts(&["ferpa"])),
            ],
            ..TableTy::default()
        };
        let t = Expr::TableLit {
            schema: s,
            rows: vec![
                RowLit {
                    cells: vec![Literal::Text("A".into()), Literal::int(4)],
                },
                RowLit {
                    cells: vec![Literal::Text("B".into()), Literal::int(2)],
                },
            ],
        };
        add!(
            "79_reject_sort_limit_order_channel_leak",
            mk_console_prog(print_table(Plan::Select {
                input: Box::new(Plan::Limit {
                    input: Box::new(Plan::Sort {
                        input: Box::new(Plan::SourceExpr(Box::new(t))),
                        keys: vec![("sec_gpa".into(), SortDir::Desc)],
                    }),
                    n: BigInt::from(1u64),
                }),
                cols: vec!["pub_name".into()],
            })),
        );
    }

    // 80. MaskComplementary when smallSum >= minK (does NOT mask smallest valid group!)
    {
        let s = TableTy {
            cols: vec![
                col("dept", ScalarTy::Text, TagSet::empty()),
                col("v", ScalarTy::Int, ts(&["ferpa"])),
            ],
            ..TableTy::default()
        };
        let mut rows = vec![
            // Dept A: 3 rows (<5)
            RowLit {
                cells: vec![Literal::Text("A".into()), Literal::int(1)],
            },
            RowLit {
                cells: vec![Literal::Text("A".into()), Literal::int(2)],
            },
            RowLit {
                cells: vec![Literal::Text("A".into()), Literal::int(3)],
            },
            // Dept B: 3 rows (<5) -> smallSum = 6 >= 5 -> NO complementary mask!
            RowLit {
                cells: vec![Literal::Text("B".into()), Literal::int(4)],
            },
            RowLit {
                cells: vec![Literal::Text("B".into()), Literal::int(5)],
            },
            RowLit {
                cells: vec![Literal::Text("B".into()), Literal::int(6)],
            },
        ];
        // Dept C: 5 rows (>=5) -> stays UNMASKED!
        for i in 0..5 {
            rows.push(RowLit {
                cells: vec![Literal::Text("C".into()), Literal::int(i)],
            });
        }
        add!(
            "80_mask_complementary_no_extra_mask_when_sum_ge_k",
            mk_console_prog(print_table(Plan::SuppressSmallGroups {
                input: Box::new(Plan::Summarize {
                    input: Box::new(Plan::GroupBy {
                        input: Box::new(Plan::SourceExpr(Box::new(Expr::TableLit {
                            schema: s,
                            rows,
                        }))),
                        keys: vec!["dept".into()],
                    }),
                    aggs: vec![AggItem {
                        name: "n".into(),
                        op: AggOp::Count,
                        arg: None,
                    }],
                    distinct_key: None,
                }),
                min_k: BigInt::from(5u64),
                distinct_by: None,
                mode: SuppressMode::MaskComplementary,
            })),
        );
    }

    // 81. WriteTable with diverse scalar types (Decimal, Float, Option, Date, Bool)
    {
        let cols = vec![
            col("b", ScalarTy::Bool, TagSet::empty()),
            col("d", ScalarTy::Decimal, TagSet::empty()),
            col("f", ScalarTy::Float, TagSet::empty()),
            col("dt", ScalarTy::Date, TagSet::empty()),
            col(
                "opt",
                ScalarTy::Option(Box::new(ScalarTy::Int)),
                TagSet::empty(),
            ),
        ];
        let src = Expr::TableLit {
            schema: TableTy {
                cols: cols.clone(),
                ..TableTy::default()
            },
            rows: vec![RowLit {
                cells: vec![
                    Literal::Bool(true),
                    Literal::decimal(-DEC_SCALE / 2),
                    f64_lit(3.5),
                    Literal::date(19782),
                    Literal::NoneLit(Ty::Int),
                ],
            }],
        };
        add!(
            "81_write_table_diverse_types",
            Program {
                funs: vec![FunDecl {
                    name: "main".into(),
                    kind: FunKind::Function,
                    is_pure: false,
                    params: vec![(
                        "wt".into(),
                        LTy::public(Ty::WriteTable {
                            db: "analytics".into(),
                            table_name: "metrics".into(),
                            dest_cols: cols,
                            dest_row_tags: TagSet::empty(),
                            allows: TagSet::empty(),
                        }),
                    )],
                    pc: TagSet::empty(),
                    ret: LTy::public(Ty::Result {
                        ok_ty: Box::new(Ty::Int),
                        err_ty: Box::new(Ty::Text),
                    }),
                    body: Expr::Host {
                        op: HostOp::WriteTable,
                        args: vec![Expr::Var("wt".into()), src],
                    },
                }],
                entry: Some("main".into()),
                ..Program::default()
            },
        );
    }

    // 82. SourceDB empty fallback (realDBTables = [] on CLI run)
    {
        let s = TableTy {
            cols: vec![col("id", ScalarTy::Int, TagSet::empty())],
            ..TableTy::default()
        };
        add!(
            "82_source_db_empty_fallback",
            Program {
                funs: vec![FunDecl {
                    name: "main".into(),
                    kind: FunKind::Function,
                    is_pure: false,
                    params: vec![
                        ("db".into(), LTy::public(Ty::ReadDB("reg".into()))),
                        ("c".into(), LTy::public(Ty::Console(TagSet::empty()))),
                    ],
                    pc: TagSet::empty(),
                    ret: LTy::public(Ty::Unit),
                    body: print_table(Plan::SourceDB {
                        cap: Box::new(Expr::Var("db".into())),
                        table_name: "students".into(),
                        schema: s,
                    }),
                }],
                entry: Some("main".into()),
                ..Program::default()
            },
        );
    }

    // 83. Stop under sensitive pc redacts even public detail!
    add!(
        "83_stop_sensitive_pc_redacts_public_detail",
        Program {
            funs: vec![FunDecl {
                name: "main".into(),
                kind: FunKind::Function,
                is_pure: false,
                params: vec![],
                pc: TagSet::empty(),
                ret: LTy::public(Ty::Unit),
                body: let_seq(
                    "flag",
                    LTy::new(Ty::Bool, ts(&["ferpa"])),
                    Expr::Lit(Literal::Bool(true)),
                    Expr::IfE {
                        cond: Box::new(Expr::Var("flag".into())),
                        then_br: Box::new(Expr::Stop {
                            kind: BugKind::UserStop,
                            detail: Some(Box::new(Expr::Lit(Literal::int(42)))),
                        }),
                        else_br: Box::new(Expr::Lit(Literal::Unit)),
                    },
                ),
            }],
            entry: Some("main".into()),
            ..Program::default()
        },
    );

    // 84. RowExpr CallPure trapping with divByZero inside Filter
    add!(
        "84_rowexpr_callpure_trap_in_filter",
        Program {
            funs: vec![
                FunDecl {
                    name: "inv_pos".into(),
                    kind: FunKind::Function,
                    is_pure: true,
                    params: vec![("x".into(), LTy::public(Ty::Int))],
                    pc: TagSet::empty(),
                    ret: LTy::public(Ty::Bool),
                    body: Expr::Prim {
                        op: PrimOp::Gt,
                        args: vec![
                            Expr::Prim {
                                op: PrimOp::DivInt,
                                args: vec![Expr::Lit(Literal::int(100)), Expr::Var("x".into())],
                            },
                            Expr::Lit(Literal::int(0)),
                        ],
                    },
                },
                FunDecl {
                    name: "main".into(),
                    kind: FunKind::Function,
                    is_pure: false,
                    params: vec![("c".into(), LTy::public(Ty::Console(TagSet::empty())))],
                    pc: TagSet::empty(),
                    ret: LTy::public(Ty::Unit),
                    body: print_table(Plan::Filter {
                        input: Box::new(Plan::SourceExpr(Box::new(Expr::TableLit {
                            schema: TableTy {
                                cols: vec![col("x", ScalarTy::Int, TagSet::empty())],
                                ..TableTy::default()
                            },
                            rows: vec![
                                RowLit {
                                    cells: vec![Literal::int(5)]
                                },
                                RowLit {
                                    cells: vec![Literal::int(0)]
                                },
                            ],
                        }))),
                        pred: RowExpr::CallPure {
                            fn_name: "inv_pos".into(),
                            args: vec![RowExpr::Col("x".into())],
                        },
                    }),
                },
            ],
            entry: Some("main".into()),
            ..Program::default()
        },
    );

    // 86. ReadParquet outside-boundary parity
    {
        let s = TableTy {
            cols: vec![col("x", ScalarTy::Int, TagSet::empty())],
            ..TableTy::default()
        };
        add!(
            "86_read_parquet_outside_boundary",
            Program {
                funs: vec![FunDecl {
                    name: "main".into(),
                    kind: FunKind::Function,
                    is_pure: false,
                    params: vec![("rf".into(), LTy::public(Ty::ReadFiles))],
                    pc: TagSet::empty(),
                    ret: LTy::public(Ty::Result {
                        ok_ty: Box::new(Ty::Table(s.clone())),
                        err_ty: Box::new(Ty::Text),
                    }),
                    body: Expr::Host {
                        op: HostOp::ReadParquet(s),
                        args: vec![
                            Expr::Var("rf".into()),
                            Expr::Lit(Literal::Text("data.parquet".into())),
                        ],
                    },
                }],
                entry: Some("main".into()),
                ..Program::default()
            },
        );
    }

    // 87. WriteXlsx outside-boundary parity
    {
        let s = TableTy {
            cols: vec![col("x", ScalarTy::Int, TagSet::empty())],
            ..TableTy::default()
        };
        add!(
            "87_write_xlsx_outside_boundary",
            Program {
                funs: vec![FunDecl {
                    name: "main".into(),
                    kind: FunKind::Function,
                    is_pure: false,
                    params: vec![(
                        "wf".into(),
                        LTy::public(Ty::WriteFiles {
                            root: "out/".into(),
                            allows: TagSet::empty(),
                        }),
                    )],
                    pc: TagSet::empty(),
                    ret: LTy::public(Ty::Result {
                        ok_ty: Box::new(Ty::Unit),
                        err_ty: Box::new(Ty::Text),
                    }),
                    body: Expr::Host {
                        op: HostOp::WriteXlsx,
                        args: vec![
                            Expr::Var("wf".into()),
                            Expr::Lit(Literal::Text("report.xlsx".into())),
                            Expr::TableLit {
                                schema: s,
                                rows: vec![RowLit {
                                    cells: vec![Literal::int(1)],
                                }],
                            },
                        ],
                    },
                }],
                entry: Some("main".into()),
                ..Program::default()
            },
        );
    }

    cases
}

#[test]
fn differential_curated_corpus_matches_lean_byte_for_byte() {
    let corpus = build_curated_corpus();
    assert!(
        corpus.len() >= 70,
        "expected >= 70 curated corpus cases, got {}",
        corpus.len()
    );
    // Run across worker threads for fast execution
    let threads = std::thread::available_parallelism()
        .map(std::num::NonZeroUsize::get)
        .unwrap_or(4)
        .min(8);
    let chunk_size = corpus.len().div_ceil(threads);
    std::thread::scope(|scope| {
        for chunk in corpus.chunks(chunk_size) {
            scope.spawn(move || {
                for case in chunk {
                    let wire = print_program(&case.prog);
                    assert_diff_program(case.name, &wire, case.fuel, case.allow_export);
                }
            });
        }
    });
}

#[test]
fn differential_non_canonical_wire_and_cli_errors_match_lean() {
    let lean = lean_danacore_bin();
    let rust = rust_oracle_bin();

    // Non-canonical wire rejections must be rejected identically by both binaries.
    let bad_wires = [
        "(dana-core 0.2 (custom-tags) (none) (datas) (schemas) (consts) (funs) (none) (meta))\n",
        "(dana-core 0.1 (custom-tags) (none) (datas) (schemas) (consts) (funs) (none) (meta))",
        "(dana-core 0.1 (custom-tags) (none) (datas) (schemas) (consts) (funs) (some main) (meta))\n",
        "(dana-core 0.1 (custom-tags) (none) (datas) (schemas) (consts) (funs (fun-decl \"main\" fn false () (tags) (lty (int) (tags)) (lit (lit-int 007)))) (some \"main\") (meta))\n",
        "(dana-core 0.1 (custom-tags) (none) (datas) (schemas) (consts) (funs (fun-decl \"main\" fn false () (tags) (lty (int) (tags)) (lit (lit-int -0)))) (some \"main\") (meta))\n",
        "(dana-core 0.1 (custom-tags) (none) (datas) (schemas) (consts) (funs (fun-decl \"main\" fn false () (tags) (lty (int) (tags)) (lit (lit-int 1_000)))) (some \"main\") (meta))\n",
        "(dana-core 0.1 (custom-tags) (none) (datas) (schemas) (consts) (funs (fun-decl \"main\" fn false () (tags) (lty (float) (tags)) (lit (lit-float 18446744073709551616)))) (some \"main\") (meta))\n",
        "(dana-core 0.1 (custom-tags) (none) (datas) (schemas) (consts) (funs) (some \"\\u{d800}\") (meta))\n",
        "(dana-core 0.1 (custom-tags) (none) (datas) (schemas) (consts) (funs) (some \"\\u{41}\") (meta))\n",
        "(dana-core 0.1 (custom-tags) (none) (datas) (schemas) (consts) (funs) (some \"\\u{0A}\") (meta))\n",
        "(dana-core 0.1 (custom-tags) (none) (datas) (schemas) (consts) (funs) (some \"\\u{01}\") (meta))\n",
        "(dana-core 0.1 (custom-tags) (none) (datas) (schemas) (consts) (funs) (none) (meta (meta-entry \"n1\" (none) (some (span \"a.dana\" 0 1 1 1)))))\n",
        "(dana-core 0.1 (custom-tags) (none) (datas) (schemas) (consts) (funs) (none) (meta (meta-entry \"n1\" (none) (some (span \"a.dana\" 5 1 4 1)))))\n",
        "(dana-core 0.1 (custom-tags) (none) (datas) (schemas) (consts) (funs (fun-decl \"main\" fn false () (tags \"pii\" \"ferpa\") (lty (unit) (tags)) (lit (lit-unit)))) (some \"main\") (meta))\n",
    ];
    for (idx, bad) in bad_wires.iter().enumerate() {
        assert_diff_program(&format!("bad_wire_{idx}"), bad, None, None);
    }

    // CLI error parity (all must return exit code 2 with empty stdout)
    let valid_wire = "(dana-core 0.1 (custom-tags) (none) (datas) (schemas) (consts) (funs (fun-decl \"main\" fn false ((\"c\" (lty (console (tags)) (tags)))) (tags) (lty (unit) (tags)) (host console-print ((var \"c\") (lit (lit-text \"ok\")))))) (some \"main\") (meta))\n";
    let tmp = TempWireFile::new("cli", valid_wire);
    let p = tmp.as_str();

    let cli_cases: Vec<Vec<&str>> = vec![
        vec![],
        vec![p, "check"],
        vec!["run", "check", p],
        vec!["run", p, p],
        vec!["run", p, "--fuel"],
        vec!["run", p, "--fuel", "10", "--fuel", "20"],
        vec!["run", p, "--fuel", "--allow-export"],
        vec!["run", p, "--fuel", "1_0"],
        vec!["run", p, "--fuel", "-1"],
        vec!["run", p, "--allow-export"],
        vec!["run", p, "--allow-export", "pii", "--allow-export", "ferpa"],
        vec!["run", p, "--allow-export", "--fuel"],
        vec!["run", p, "--allow-export", "pii,,ferpa"],
        vec!["run", p, "--allow-export", "-pii"],
        vec!["run", p, "--allow-export", "pii,pii"],
        vec!["run", p, "--unknown-flag"],
        vec!["run", "/nonexistent/dana/path/missing.core"],
        // Valid shorthand without explicit `run`
        vec![p],
    ];
    for args in &cli_cases {
        let l = run_bin(lean, args);
        let r = run_bin(rust, args);
        assert_eq!(
            l.code, r.code,
            "CLI exit code mismatch for {args:?}: lean={} ({}) rust={} ({})",
            l.code, l.stderr, r.code, r.stderr
        );
        assert_eq!(l.stdout, r.stdout, "CLI stdout mismatch for {args:?}");
    }
}

// ---------------------------------------------------------------------------
// Deterministic Seeded SplitMix64 PRNG Differential Fuzzer (300 Programs!)
// ---------------------------------------------------------------------------

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

    fn gen_range(&mut self, upper: usize) -> usize {
        if upper <= 1 {
            0
        } else {
            (self.next_u64() as usize) % upper
        }
    }

    fn gen_bool(&mut self, num: usize, den: usize) -> bool {
        self.gen_range(den) < num
    }

    fn pick_int(&mut self) -> i64 {
        const POOL: &[i64] = &[
            0,
            1,
            -1,
            2,
            -2,
            3,
            -3,
            5,
            -7,
            10,
            -13,
            42,
            -100,
            1000,
            i64::MAX,
            i64::MIN,
            i64::MAX - 1,
            i64::MIN + 1,
            5_000_000_000_000_000_000,
        ];
        if self.gen_bool(3, 4) {
            POOL[self.gen_range(POOL.len())]
        } else {
            (self.next_u64() as i64) % 500
        }
    }

    fn pick_dec(&mut self) -> i128 {
        const POOL: &[i128] = &[
            0,
            1,
            -1,
            -3,
            DEC_SCALE,
            -DEC_SCALE,
            DEC_SCALE / 2,
            -(DEC_SCALE / 2),
            3 * DEC_SCALE,
            -7 * DEC_SCALE,
            DEC_MAX,
            -DEC_MAX,
        ];
        if self.gen_bool(3, 4) {
            POOL[self.gen_range(POOL.len())]
        } else {
            i128::from(self.pick_int() % 50) * (DEC_SCALE / 10)
        }
    }

    fn pick_float(&mut self) -> Float64 {
        const POOL: &[u64] = &[
            0x0000_0000_0000_0000, // +0.0
            0x8000_0000_0000_0000, // -0.0
            0x3ff0_0000_0000_0000, // 1.0
            0xbff0_0000_0000_0000, // -1.0
            0x4000_0000_0000_0000, // 2.0
            0x4024_0000_0000_0000, // 10.0
            0xc024_0000_0000_0000, // -10.0
            0x403e_0000_0000_0000, // 30.0
            0x7ff0_0000_0000_0000, // +Inf
            0xfff0_0000_0000_0000, // -Inf
            0x7ff8_0000_0000_0000, // canon NaN
            0x7ff8_0000_0000_0001, // payload NaN
            0xfff8_0000_0000_0000, // -NaN
        ];
        match self.gen_range(16) {
            i if i < POOL.len() => Float64::from_bits(POOL[i]),
            13 => Float64::from_f64(1e80),
            14 => Float64::from_f64(1e-82),
            _ => Float64::from_f64(1.7e308),
        }
    }

    fn pick_tag_set(&mut self) -> TagSet {
        const TAGS: &[&str] = &["pii", "ferpa", "financial", "health"];
        let mut out = Vec::new();
        for &t in TAGS {
            if self.gen_bool(1, 4) {
                out.push(t.to_string());
            }
        }
        TagSet::of_list(out)
    }

    fn pick_text(&mut self) -> String {
        const POOL: &[&str] = &[
            "",
            "A",
            "B",
            "C",
            "Eng",
            "Sales",
            "  Hi\t",
            "café",
            "a\"b\\c\n",
            "x\u{01}\u{85}",
        ];
        POOL[self.gen_range(POOL.len())].to_string()
    }
}

fn gen_scalar_int_expr(rng: &mut SplitMix64, depth: usize) -> Expr {
    if depth == 0 || rng.gen_bool(1, 3) {
        return Expr::Lit(Literal::int(rng.pick_int()));
    }
    match rng.gen_range(8) {
        0 => Expr::Prim {
            op: PrimOp::AddInt,
            args: vec![
                gen_scalar_int_expr(rng, depth - 1),
                gen_scalar_int_expr(rng, depth - 1),
            ],
        },
        1 => Expr::Prim {
            op: PrimOp::SubInt,
            args: vec![
                gen_scalar_int_expr(rng, depth - 1),
                gen_scalar_int_expr(rng, depth - 1),
            ],
        },
        2 => Expr::Prim {
            op: PrimOp::MulInt,
            args: vec![
                gen_scalar_int_expr(rng, depth - 1),
                gen_scalar_int_expr(rng, depth - 1),
            ],
        },
        3 => Expr::Prim {
            op: PrimOp::DivInt,
            args: vec![
                gen_scalar_int_expr(rng, depth - 1),
                gen_scalar_int_expr(rng, depth - 1),
            ],
        },
        4 => Expr::Prim {
            op: PrimOp::ModInt,
            args: vec![
                gen_scalar_int_expr(rng, depth - 1),
                gen_scalar_int_expr(rng, depth - 1),
            ],
        },
        5 => Expr::Prim {
            op: PrimOp::NegInt,
            args: vec![gen_scalar_int_expr(rng, depth - 1)],
        },
        6 => Expr::IfE {
            cond: Box::new(Expr::Prim {
                op: match rng.gen_range(6) {
                    0 => PrimOp::Eq,
                    1 => PrimOp::Ne,
                    2 => PrimOp::Lt,
                    3 => PrimOp::Le,
                    4 => PrimOp::Gt,
                    _ => PrimOp::Ge,
                },
                args: vec![
                    gen_scalar_int_expr(rng, depth - 1),
                    gen_scalar_int_expr(rng, depth - 1),
                ],
            }),
            then_br: Box::new(gen_scalar_int_expr(rng, depth - 1)),
            else_br: Box::new(gen_scalar_int_expr(rng, depth - 1)),
        },
        _ => {
            let some_or_none = if rng.gen_bool(2, 3) {
                Expr::Prim {
                    op: PrimOp::SomeVal(Ty::Int),
                    args: vec![gen_scalar_int_expr(rng, depth - 1)],
                }
            } else {
                Expr::Lit(Literal::NoneLit(Ty::Int))
            };
            if rng.gen_bool(2, 3) {
                Expr::Prim {
                    op: PrimOp::UnwrapOr,
                    args: vec![some_or_none, gen_scalar_int_expr(rng, depth - 1)],
                }
            } else {
                Expr::Prim {
                    op: PrimOp::UnwrapBang,
                    args: vec![some_or_none],
                }
            }
        }
    }
}

fn gen_scalar_dec_expr(rng: &mut SplitMix64, depth: usize) -> Expr {
    if depth == 0 || rng.gen_bool(1, 3) {
        return Expr::Lit(Literal::decimal(rng.pick_dec()));
    }
    match rng.gen_range(6) {
        0 => Expr::Prim {
            op: PrimOp::AddDec,
            args: vec![
                gen_scalar_dec_expr(rng, depth - 1),
                gen_scalar_dec_expr(rng, depth - 1),
            ],
        },
        1 => Expr::Prim {
            op: PrimOp::SubDec,
            args: vec![
                gen_scalar_dec_expr(rng, depth - 1),
                gen_scalar_dec_expr(rng, depth - 1),
            ],
        },
        2 => Expr::Prim {
            op: PrimOp::MulDec,
            args: vec![
                gen_scalar_dec_expr(rng, depth - 1),
                gen_scalar_dec_expr(rng, depth - 1),
            ],
        },
        3 => Expr::Prim {
            op: PrimOp::DivDec,
            args: vec![
                gen_scalar_dec_expr(rng, depth - 1),
                gen_scalar_dec_expr(rng, depth - 1),
            ],
        },
        4 => Expr::Prim {
            op: PrimOp::NegDec,
            args: vec![gen_scalar_dec_expr(rng, depth - 1)],
        },
        _ => Expr::Prim {
            op: PrimOp::IntToDec,
            args: vec![Expr::Lit(Literal::int(rng.pick_int() % 1000))],
        },
    }
}

fn gen_fuzz_program(rng: &mut SplitMix64, idx: usize) -> (Program, Option<usize>, Option<String>) {
    match idx % 6 {
        // Family 0: Scalar Int / Decimal / Text / Join-loop / Closures
        0 => {
            let body = match rng.gen_range(4) {
                0 => print_int(gen_scalar_int_expr(rng, 3)),
                1 => print_dec(gen_scalar_dec_expr(rng, 3)),
                2 => {
                    let s1 = rng.pick_text();
                    let s2 = rng.pick_text();
                    print_str(Expr::Prim {
                        op: PrimOp::ConcatText,
                        args: vec![
                            Expr::Prim {
                                op: PrimOp::LowerAsciiText,
                                args: vec![Expr::Prim {
                                    op: PrimOp::TrimText,
                                    args: vec![Expr::Lit(Literal::Text(s1))],
                                }],
                            },
                            Expr::Lit(Literal::Text(s2)),
                        ],
                    })
                }
                _ => {
                    let limit = (rng.gen_range(7) as i64) + 1;
                    let step = (rng.gen_range(3) as i64) + 1;
                    print_int(Expr::Join {
                        label: "loop".into(),
                        params: vec![
                            ("i".into(), LTy::public(Ty::Int)),
                            ("acc".into(), LTy::public(Ty::Int)),
                        ],
                        rhs: Box::new(Expr::IfE {
                            cond: Box::new(Expr::Prim {
                                op: PrimOp::Lt,
                                args: vec![Expr::Var("i".into()), Expr::Lit(Literal::int(limit))],
                            }),
                            then_br: Box::new(Expr::Jump {
                                label: "loop".into(),
                                args: vec![
                                    Expr::Prim {
                                        op: PrimOp::AddInt,
                                        args: vec![
                                            Expr::Var("i".into()),
                                            Expr::Lit(Literal::int(step)),
                                        ],
                                    },
                                    Expr::Prim {
                                        op: PrimOp::AddInt,
                                        args: vec![Expr::Var("acc".into()), Expr::Var("i".into())],
                                    },
                                ],
                            }),
                            else_br: Box::new(Expr::Var("acc".into())),
                        }),
                        body: Box::new(Expr::Jump {
                            label: "loop".into(),
                            args: vec![Expr::Lit(Literal::int(0)), Expr::Lit(Literal::int(0))],
                        }),
                    })
                }
            };
            let fuel = if rng.gen_bool(1, 5) {
                Some(rng.gen_range(25) + 1)
            } else {
                None
            };
            (mk_console_prog(body), fuel, None)
        }

        // Family 1: Pure relational pipeline chains (filter, derive, bucket, distinct, sort, limit, window, pivot)
        1 => {
            let schema = TableTy {
                cols: vec![
                    col("g", ScalarTy::Text, TagSet::empty()),
                    col("k", ScalarTy::Int, TagSet::empty()),
                    col("f", ScalarTy::Float, TagSet::empty()),
                ],
                ..TableTy::default()
            };
            let n_rows = rng.gen_range(8);
            let mut rows = Vec::with_capacity(n_rows);
            let groups = ["A", "B", "C"];
            for _ in 0..n_rows {
                rows.push(RowLit {
                    cells: vec![
                        Literal::Text(groups[rng.gen_range(groups.len())].into()),
                        Literal::int((rng.pick_int() % 20) - 5),
                        Literal::Float(rng.pick_float()),
                    ],
                });
            }
            let mut plan = Plan::SourceExpr(Box::new(Expr::TableLit { schema, rows }));
            let stages = rng.gen_range(4) + 1;
            for _ in 0..stages {
                plan = match rng.gen_range(7) {
                    0 => Plan::Filter {
                        input: Box::new(plan),
                        pred: RowExpr::Prim {
                            op: if rng.gen_bool(1, 2) {
                                PrimOp::Ge
                            } else {
                                PrimOp::Ne
                            },
                            args: vec![RowExpr::Col("k".into()), RowExpr::Lit(Literal::int(0))],
                        },
                    },
                    1 => Plan::Derive {
                        input: Box::new(plan),
                        items: vec![DeriveItem::BucketCol {
                            name: "b".into(),
                            source: "k".into(),
                            cuts: vec![Literal::int(0), Literal::int(5)],
                            labels: vec!["neg".into(), "small".into(), "big".into()],
                        }],
                    },
                    2 => Plan::Distinct {
                        input: Box::new(plan),
                        cols: if rng.gen_bool(1, 2) {
                            vec!["g".into()]
                        } else {
                            vec![]
                        },
                    },
                    3 => Plan::Sort {
                        input: Box::new(plan),
                        keys: vec![
                            (
                                "g".into(),
                                if rng.gen_bool(1, 2) {
                                    SortDir::Asc
                                } else {
                                    SortDir::Desc
                                },
                            ),
                            (
                                "f".into(),
                                if rng.gen_bool(1, 2) {
                                    SortDir::Asc
                                } else {
                                    SortDir::Desc
                                },
                            ),
                        ],
                    },
                    4 => Plan::Limit {
                        input: Box::new(plan),
                        n: BigInt::from(rng.gen_range(6) as u64),
                    },
                    5 => Plan::Window {
                        input: Box::new(plan),
                        items: vec![WindowItem {
                            name: "w".into(),
                            win_fn: match rng.gen_range(6) {
                                0 => WindowFn::RowNumber,
                                1 => WindowFn::Rank { col: "k".into() },
                                2 => WindowFn::Lag {
                                    col: "k".into(),
                                    offset: BigInt::from(1u64),
                                },
                                3 => WindowFn::Lead {
                                    col: "k".into(),
                                    offset: BigInt::from(1u64),
                                },
                                4 => WindowFn::RunningSum { col: "k".into() },
                                _ => WindowFn::RollingMean {
                                    col: "f".into(),
                                    window_size: BigInt::from(2u64),
                                },
                            },
                            over: vec!["g".into()],
                            order: vec![("k".into(), SortDir::Asc)],
                        }],
                    },
                    _ => Plan::FillGaps {
                        input: Box::new(plan),
                        col: "k".into(),
                        step_micros: BigInt::from(1),
                        over: vec!["g".into()],
                        fill: vec![("f".into(), f64_lit(0.0))],
                    },
                };
            }
            (mk_console_prog(print_table(plan)), None, None)
        }

        // Family 2: Multi-table joins & unions (public + tagged, duplicates & non-duplicates)
        2 => {
            let key_tags = if rng.gen_bool(1, 3) {
                ts(&["pii"])
            } else {
                TagSet::empty()
            };
            let l_schema = TableTy {
                cols: vec![
                    col("id", ScalarTy::Int, key_tags.clone()),
                    col("lv", ScalarTy::Text, TagSet::empty()),
                ],
                ..TableTy::default()
            };
            let r_schema = TableTy {
                cols: vec![
                    col("id", ScalarTy::Int, key_tags.clone()),
                    col("rv", ScalarTy::Int, TagSet::empty()),
                ],
                ..TableTy::default()
            };
            let ln = rng.gen_range(5);
            let rn = rng.gen_range(5);
            let l_rows = (0..ln)
                .map(|_| RowLit {
                    cells: vec![
                        Literal::int(rng.gen_range(4) as i64),
                        Literal::Text(rng.pick_text()),
                    ],
                })
                .collect();
            let r_rows = (0..rn)
                .map(|_| RowLit {
                    cells: vec![
                        Literal::int(rng.gen_range(4) as i64),
                        Literal::int(rng.pick_int() % 50),
                    ],
                })
                .collect();
            let kind = match rng.gen_range(7) {
                0 => JoinKind::InnerOne,
                1 => JoinKind::InnerManyToOne,
                2 => JoinKind::InnerMany,
                3 => JoinKind::LeftOne,
                4 => JoinKind::LeftManyToOne,
                5 => JoinKind::Semi,
                _ => JoinKind::Anti,
            };
            let plan = Plan::Join {
                kind,
                left: Box::new(Plan::SourceExpr(Box::new(Expr::TableLit {
                    schema: l_schema,
                    rows: l_rows,
                }))),
                right: Box::new(Plan::SourceExpr(Box::new(Expr::TableLit {
                    schema: r_schema,
                    rows: r_rows,
                }))),
                on: if rng.gen_bool(2, 3) {
                    JoinOn::SameKeys(vec!["id".into()])
                } else {
                    JoinOn::Pairs(vec![("id".into(), "id".into())])
                },
                suffixes: Some(("_l".into(), "_r".into())),
            };
            let allows = key_tags.clone();
            let allow_export = if allows.is_empty() || rng.gen_bool(1, 2) {
                if allows.is_empty() {
                    None
                } else {
                    Some(allows.elems().join(","))
                }
            } else {
                None
            };
            let prog = Program {
                funs: vec![FunDecl {
                    name: "main".into(),
                    kind: FunKind::Function,
                    is_pure: false,
                    params: vec![("c".into(), LTy::public(Ty::Console(allows)))],
                    pc: TagSet::empty(),
                    ret: LTy::public(Ty::Unit),
                    body: print_table(plan),
                }],
                entry: Some("main".into()),
                ..Program::default()
            };
            (prog, None, allow_export)
        }

        // Family 3: Aggregations, float/decimal stats, & SuppressSmallGroups (`Drop` & `MaskComplementary`)
        3 => {
            let val_tags = if rng.gen_bool(1, 2) {
                ts(&["ferpa"])
            } else {
                TagSet::empty()
            };
            let schema = TableTy {
                cols: vec![
                    col("id", ScalarTy::Int, ts(&["pii"])),
                    col("g", ScalarTy::Text, TagSet::empty()),
                    col("xi", ScalarTy::Int, val_tags.clone()),
                    col("xd", ScalarTy::Decimal, val_tags.clone()),
                    col("xf", ScalarTy::Float, val_tags),
                ],
                ..TableTy::default()
            };
            let n_rows = rng.gen_range(16);
            let groups = ["A", "B", "C"];
            let rows = (0..n_rows)
                .map(|i| RowLit {
                    cells: vec![
                        Literal::int((i % 7) as i64),
                        Literal::Text(groups[rng.gen_range(groups.len())].into()),
                        Literal::int(rng.pick_int() % 100),
                        Literal::decimal(rng.pick_dec() / 10),
                        Literal::Float(rng.pick_float()),
                    ],
                })
                .collect();
            let agg_ops = [
                AggOp::Count,
                AggOp::CountDistinct,
                AggOp::Sum,
                AggOp::Mean,
                AggOp::Median,
                AggOp::Variance,
                AggOp::Stddev,
                AggOp::Percentile(Float64::from_f64(
                    [0.0, 0.25, 0.5, 0.75, 1.0][rng.gen_range(5)],
                )),
                AggOp::Min,
                AggOp::Max,
                AggOp::First,
                AggOp::Last,
            ];
            let mut aggs = Vec::new();
            let n_aggs = rng.gen_range(4) + 1;
            for a_i in 0..n_aggs {
                let op = agg_ops[rng.gen_range(agg_ops.len())];
                let arg = match op {
                    AggOp::Count => None,
                    _ => Some(RowExpr::Col(
                        ["xi", "xd", "xf"][rng.gen_range(3)].to_string(),
                    )),
                };
                aggs.push(AggItem {
                    name: format!("a{a_i}"),
                    op,
                    arg,
                });
            }
            let base = Plan::Summarize {
                input: Box::new(Plan::GroupBy {
                    input: Box::new(Plan::SourceExpr(Box::new(Expr::TableLit { schema, rows }))),
                    keys: vec!["g".into()],
                }),
                aggs,
                distinct_key: if rng.gen_bool(1, 2) {
                    Some("id".into())
                } else {
                    None
                },
            };
            let plan = if rng.gen_bool(2, 3) {
                let mode = if rng.gen_bool(1, 2) {
                    SuppressMode::Drop
                } else {
                    SuppressMode::MaskComplementary
                };
                let min_k = (rng.gen_range(5) + 4) as u64; // 4..=8 (intentionally tests < 5 rejection too!)
                Plan::SuppressSmallGroups {
                    input: Box::new(base),
                    min_k: BigInt::from(min_k),
                    distinct_by: if rng.gen_bool(1, 2) {
                        Some("id".into())
                    } else {
                        None
                    },
                    mode,
                }
            } else {
                base
            };
            (mk_console_prog(print_table(plan)), None, None)
        }

        // Family 4: Privacy, Policy, Path Confinement, Redact/Pseudonymize, Explicit Stop
        4 => {
            let tag_set = rng.pick_tag_set();
            match rng.gen_range(4) {
                0 => {
                    // Explicit stop with tagged or public value
                    let prog = Program {
                        funs: vec![FunDecl {
                            name: "main".into(),
                            kind: FunKind::Function,
                            is_pure: false,
                            params: vec![],
                            pc: TagSet::empty(),
                            ret: LTy::public(Ty::Unit),
                            body: let_seq(
                                "x",
                                LTy::new(Ty::Text, tag_set),
                                Expr::Lit(Literal::Text(rng.pick_text())),
                                Expr::Stop {
                                    kind: match rng.gen_range(3) {
                                        0 => BugKind::UserStop,
                                        1 => BugKind::PromiseViolation,
                                        _ => BugKind::SchemaConstraint,
                                    },
                                    detail: if rng.gen_bool(3, 4) {
                                        Some(Box::new(Expr::Var("x".into())))
                                    } else {
                                        None
                                    },
                                },
                            ),
                        }],
                        entry: Some("main".into()),
                        ..Program::default()
                    };
                    (prog, None, None)
                }
                1 => {
                    // WriteFiles with random root & relPath + optional policy & export gate
                    let roots = ["out/", "out", "reports/q1/", "reports/../bad/"];
                    let rels = ["a.txt", "sub/b.txt", "../escape", "/abs", "a\\b", ""];
                    let root = roots[rng.gen_range(roots.len())].to_string();
                    let rel = rels[rng.gen_range(rels.len())].to_string();
                    let pol = if rng.gen_bool(1, 2) {
                        Some(Policy {
                            min_group_size: BigInt::from(5u64),
                            allow_export: vec![("reports/".into(), ts(&["ferpa", "pii"]))],
                            ..Policy::default()
                        })
                    } else {
                        None
                    };
                    let allow_export = if !tag_set.is_empty() && rng.gen_bool(1, 2) {
                        Some(tag_set.elems().join(","))
                    } else {
                        None
                    };
                    let prog = Program {
                        policy: pol,
                        funs: vec![FunDecl {
                            name: "main".into(),
                            kind: FunKind::Function,
                            is_pure: false,
                            params: vec![(
                                "wf".into(),
                                LTy::public(Ty::WriteFiles {
                                    root,
                                    allows: tag_set.clone(),
                                }),
                            )],
                            pc: TagSet::empty(),
                            ret: LTy::new(
                                Ty::Result {
                                    ok_ty: Box::new(Ty::Unit),
                                    err_ty: Box::new(Ty::Text),
                                },
                                tag_set,
                            ),
                            body: Expr::Host {
                                op: HostOp::WriteFile,
                                args: vec![
                                    Expr::Var("wf".into()),
                                    Expr::Lit(Literal::Text(rel)),
                                    Expr::Lit(Literal::Text(rng.pick_text())),
                                ],
                            },
                        }],
                        entry: Some("main".into()),
                        ..Program::default()
                    };
                    (prog, None, allow_export)
                }
                2 => {
                    // Redact & Pseudonymize
                    let s = TableTy {
                        cols: vec![
                            col("email", ScalarTy::Text, ts(&["pii"])),
                            col("v", ScalarTy::Int, TagSet::empty()),
                        ],
                        ..TableTy::default()
                    };
                    let t = Expr::TableLit {
                        schema: s,
                        rows: vec![
                            RowLit {
                                cells: vec![Literal::Text(rng.pick_text()), Literal::int(1)],
                            },
                            RowLit {
                                cells: vec![Literal::Text("u2@test.edu".into()), Literal::int(2)],
                            },
                        ],
                    };
                    let plan = if rng.gen_bool(1, 2) {
                        Plan::Redact {
                            input: Box::new(Plan::SourceExpr(Box::new(t))),
                            col: "email".into(),
                            replacement: "[X]".into(),
                        }
                    } else {
                        Plan::Pseudonymize {
                            input: Box::new(Plan::SourceExpr(Box::new(t))),
                            col: "email".into(),
                            secret: Box::new(Expr::Var("sec".into())),
                        }
                    };
                    let prog = Program {
                        funs: vec![FunDecl {
                            name: "main".into(),
                            kind: FunKind::Function,
                            is_pure: false,
                            params: vec![
                                (
                                    "sec".into(),
                                    LTy::new(Ty::Secret("k".into()), ts(&["secret"])),
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
                    (prog, None, None)
                }
                _ => {
                    // StatsCorr & StatsLinReg on random float pairs
                    let s = TableTy {
                        cols: vec![
                            col("x", ScalarTy::Float, TagSet::empty()),
                            col("y", ScalarTy::Float, TagSet::empty()),
                        ],
                        ..TableTy::default()
                    };
                    let n = rng.gen_range(5);
                    let rows = (0..n)
                        .map(|_| RowLit {
                            cells: vec![
                                Literal::Float(rng.pick_float()),
                                Literal::Float(rng.pick_float()),
                            ],
                        })
                        .collect();
                    let tbl = Expr::TableLit { schema: s, rows };
                    let prog = if rng.gen_bool(1, 2) {
                        mk_console_prog(print_bool(Expr::Prim {
                            op: PrimOp::IsSome,
                            args: vec![Expr::Prim {
                                op: PrimOp::StatsCorr {
                                    col_x: "x".into(),
                                    col_y: "y".into(),
                                },
                                args: vec![tbl],
                            }],
                        }))
                    } else {
                        Program {
                            funs: vec![FunDecl {
                                name: "main".into(),
                                kind: FunKind::Function,
                                is_pure: false,
                                params: vec![],
                                pc: TagSet::empty(),
                                ret: LTy::public(Ty::LinearModel),
                                body: Expr::Prim {
                                    op: PrimOp::StatsLinReg {
                                        col_x: "x".into(),
                                        col_y: "y".into(),
                                    },
                                    args: vec![tbl],
                                },
                            }],
                            entry: Some("main".into()),
                            ..Program::default()
                        }
                    };
                    (prog, None, None)
                }
            }
        }

        // Family 5: Deliberate static-checker edge cases & negative mutations
        _ => {
            let prog = match rng.gen_range(6) {
                0 => {
                    // Undeclared custom tag
                    Program {
                        funs: vec![FunDecl {
                            name: "main".into(),
                            kind: FunKind::Function,
                            is_pure: false,
                            params: vec![("c".into(), LTy::public(Ty::Console(ts(&["typo_tag"]))))],
                            pc: TagSet::empty(),
                            ret: LTy::public(Ty::Unit),
                            body: Expr::Lit(Literal::Unit),
                        }],
                        entry: Some("main".into()),
                        ..Program::default()
                    }
                }
                1 => {
                    // Non-tail jump inside let bound
                    Program {
                        funs: vec![FunDecl {
                            name: "main".into(),
                            kind: FunKind::Function,
                            is_pure: false,
                            params: vec![],
                            pc: TagSet::empty(),
                            ret: LTy::public(Ty::Int),
                            body: Expr::Join {
                                label: "j".into(),
                                params: vec![],
                                rhs: Box::new(Expr::Lit(Literal::int(1))),
                                body: Box::new(let_seq(
                                    "x",
                                    LTy::public(Ty::Int),
                                    Expr::Jump {
                                        label: "j".into(),
                                        args: vec![],
                                    },
                                    Expr::Var("x".into()),
                                )),
                            },
                        }],
                        entry: Some("main".into()),
                        ..Program::default()
                    }
                }
                2 => {
                    // Nested Option(Option(Int)) rejected
                    Program {
                        funs: vec![FunDecl {
                            name: "main".into(),
                            kind: FunKind::Function,
                            is_pure: false,
                            params: vec![],
                            pc: TagSet::empty(),
                            ret: LTy::public(Ty::Option(Box::new(Ty::Option(Box::new(Ty::Int))))),
                            body: Expr::Lit(Literal::NoneLit(Ty::Option(Box::new(Ty::Int)))),
                        }],
                        entry: Some("main".into()),
                        ..Program::default()
                    }
                }
                3 => {
                    // Entry function marked as spec Test -> rejected
                    Program {
                        funs: vec![FunDecl {
                            name: "main".into(),
                            kind: FunKind::Test,
                            is_pure: false,
                            params: vec![],
                            pc: TagSet::empty(),
                            ret: LTy::public(Ty::Unit),
                            body: Expr::Lit(Literal::Unit),
                        }],
                        entry: Some("main".into()),
                        ..Program::default()
                    }
                }
                4 => {
                    // Pure function containing HostOp -> rejected
                    Program {
                        funs: vec![FunDecl {
                            name: "bad_pure".into(),
                            kind: FunKind::Function,
                            is_pure: true,
                            params: vec![("c".into(), LTy::public(Ty::Console(TagSet::empty())))],
                            pc: TagSet::empty(),
                            ret: LTy::public(Ty::Unit),
                            body: print_str(Expr::Lit(Literal::Text("x".into()))),
                        }],
                        ..Program::default()
                    }
                }
                _ => {
                    // Scalar implicit flow `if tagged_bool then print("leak") else ()`
                    Program {
                        funs: vec![FunDecl {
                            name: "leak".into(),
                            kind: FunKind::Function,
                            is_pure: false,
                            params: vec![
                                ("b".into(), LTy::new(Ty::Bool, ts(&["ferpa"]))),
                                ("c".into(), LTy::public(Ty::Console(TagSet::empty()))),
                            ],
                            pc: TagSet::empty(),
                            ret: LTy::public(Ty::Unit),
                            body: Expr::IfE {
                                cond: Box::new(Expr::Var("b".into())),
                                then_br: Box::new(print_str(Expr::Lit(Literal::Text(
                                    "leak".into(),
                                )))),
                                else_br: Box::new(Expr::Lit(Literal::Unit)),
                            },
                        }],
                        ..Program::default()
                    }
                }
            };
            (prog, None, None)
        }
    }
}

#[test]
fn differential_prng_fuzzer_300_programs_match_lean_byte_for_byte() {
    use std::sync::atomic::AtomicUsize;

    const FUZZ_COUNT: usize = 300;
    const SEED: u64 = 0xDA4A_2026_1B01_CAFE;

    let mut rng = SplitMix64::new(SEED);
    let generated: Vec<(String, String, Option<usize>, Option<String>)> = (0..FUZZ_COUNT)
        .map(|i| {
            let (prog, fuel, allow_export) = gen_fuzz_program(&mut rng, i);
            let wire = print_program(&prog);
            (format!("fuzz_{i:03}"), wire, fuel, allow_export)
        })
        .collect();

    let check_ok_count = AtomicUsize::new(0);
    let check_err_count = AtomicUsize::new(0);
    let run_ok_count = AtomicUsize::new(0);
    let run_stopped_count = AtomicUsize::new(0);

    let threads = std::thread::available_parallelism()
        .map(std::num::NonZeroUsize::get)
        .unwrap_or(4)
        .min(8);
    let chunk_size = generated.len().div_ceil(threads);
    std::thread::scope(|scope| {
        for chunk in generated.chunks(chunk_size) {
            let check_ok_ref = &check_ok_count;
            let check_err_ref = &check_err_count;
            let run_ok_ref = &run_ok_count;
            let run_stopped_ref = &run_stopped_count;
            scope.spawn(move || {
                for (label, wire, fuel, allow_export) in chunk {
                    assert_diff_program(label, wire, *fuel, allow_export.as_deref());
                    if let Ok(p) = parse_program(wire) {
                        if check_program(&p).is_ok() {
                            check_ok_ref.fetch_add(1, Ordering::Relaxed);
                            let mut w = World::default();
                            if let Some(ae) = allow_export {
                                w.runtime_allow_export =
                                    TagSet::of_list(ae.split(',').map(String::from).collect());
                            }
                            if let Ok(rep) = run_program(fuel.unwrap_or(4096), &p, w) {
                                match rep.status {
                                    ExitStatus::Ok => {
                                        run_ok_ref.fetch_add(1, Ordering::Relaxed);
                                    }
                                    ExitStatus::Stopped | ExitStatus::Failed => {
                                        run_stopped_ref.fetch_add(1, Ordering::Relaxed);
                                    }
                                }
                            }
                        } else {
                            check_err_ref.fetch_add(1, Ordering::Relaxed);
                        }
                    }
                }
            });
        }
    });

    let c_ok = check_ok_count.load(Ordering::Relaxed);
    let c_err = check_err_count.load(Ordering::Relaxed);
    let r_ok = run_ok_count.load(Ordering::Relaxed);
    let r_stop = run_stopped_count.load(Ordering::Relaxed);
    assert_eq!(c_ok + c_err, FUZZ_COUNT);
    assert!(c_ok >= 150, "fuzzer check-ok coverage too low: {c_ok}");
    assert!(c_err >= 50, "fuzzer check-err coverage too low: {c_err}");
    assert!(r_ok >= 80, "fuzzer run-ok coverage too low: {r_ok}");
    assert!(
        r_stop >= 20,
        "fuzzer run-stopped coverage too low: {r_stop}"
    );
    eprintln!(
        "PRNG differential fuzzer summary ({FUZZ_COUNT} programs): check_ok={c_ok}, check_err={c_err}, run_ok={r_ok}, run_stopped={r_stop}"
    );
}

#[test]
fn differential_unbounded_nat_b1_matches_lean_byte_for_byte() {
    const TWO_POW_64: &str = "18446744073709551616";
    const TEN_POW_30: &str = "1000000000000000000000000000000";

    // 1. Policy.min_group_size & SuppressSmallGroups.min_k >= 2^64 (equal, below, and 10^30)
    for (label, mg, mk) in [
        ("b1_policy_eq_2p64", TWO_POW_64, TWO_POW_64),
        ("b1_policy_below_2p64", TEN_POW_30, TWO_POW_64),
        ("b1_policy_eq_1e30", TEN_POW_30, TEN_POW_30),
    ] {
        let wire = format!(
            "(dana-core 0.1 (custom-tags) (some (policy {mg} false false (tags) () () ())) \
             (datas) (schemas) (consts) (funs (fun-decl \"main\" fn false () (tags) \
             (lty (table (table-ty ((col \"g\" (text) (tags) false raw) (col \"n\" (int) (tags) false raw)) (tags) (tags) (none) false (none))) (tags)) \
             (rel (suppress-small-groups (summarize (group-by (source-expr (table-lit \
             (table-ty ((col \"g\" (text) (tags) false raw)) (tags) (tags) (none) false (none)) \
             (((lit-text \"a\")) ((lit-text \"a\"))))) (\"g\")) ((agg \"n\" count (none))) (none)) {mk} (none) drop)))) \
             (some \"main\") (meta))\n"
        );
        assert_diff_program(label, &wire, None, None);
    }

    // 2. SuppressSmallGroups MaskComplementary with min_k = 2^64
    let mask_wire = format!(
        "(dana-core 0.1 (custom-tags) (none) (datas) (schemas) (consts) (funs (fun-decl \"main\" fn false \
         ((\"c\" (lty (console (tags)) (tags)))) (tags) (lty (unit) (tags)) \
         (host console-print-table ((var \"c\") (rel (suppress-small-groups (summarize (group-by (source-expr (table-lit \
         (table-ty ((col \"g\" (text) (tags) false raw)) (tags) (tags) (none) false (none)) \
         (((lit-text \"a\")) ((lit-text \"b\"))))) (\"g\")) ((agg \"n\" count (none))) (none)) {TWO_POW_64} (none) mask-complementary)))))) \
         (some \"main\") (meta))\n"
    );
    assert_diff_program("b1_suppress_mask_2p64", &mask_wire, None, None);

    // 3. Plan::Limit.n >= 2^64
    let limit_wire = format!(
        "(dana-core 0.1 (custom-tags) (none) (datas) (schemas) (consts) (funs (fun-decl \"main\" fn false \
         ((\"c\" (lty (console (tags)) (tags)))) (tags) (lty (unit) (tags)) \
         (host console-print-table ((var \"c\") (rel (limit (source-expr (table-lit \
         (table-ty ((col \"x\" (int) (tags) false raw)) (tags) (tags) (none) false (none)) \
         (((lit-int 1)) ((lit-int 2))))) {TEN_POW_30})))))) (some \"main\") (meta))\n"
    );
    assert_diff_program("b1_limit_1e30", &limit_wire, None, None);

    // 4. WindowFn::Lag, Lead, RollingMean >= 2^64
    let win_wire = format!(
        "(dana-core 0.1 (custom-tags) (none) (datas) (schemas) (consts) (funs (fun-decl \"main\" fn false \
         ((\"c\" (lty (console (tags)) (tags)))) (tags) (lty (unit) (tags)) \
         (host console-print-table ((var \"c\") (rel (window (source-expr (table-lit \
         (table-ty ((col \"x\" (int) (tags) false raw)) (tags) (tags) (none) false (none)) \
         (((lit-int 10)) ((lit-int 20))))) \
         ((win-item \"lg\" (lag \"x\" {TWO_POW_64}) () ((\"x\" asc))) \
         (win-item \"ld\" (lead \"x\" {TEN_POW_30}) () ((\"x\" asc))) \
         (win-item \"rm\" (rolling-mean \"x\" {TWO_POW_64}) () ((\"x\" asc)))))))))) \
         (some \"main\") (meta))\n"
    );
    assert_diff_program("b1_window_big_nat", &win_wire, None, None);

    // 5. SourceSpan start_line, start_col, end_line, end_col >= 2^64
    let span_wire = format!(
        "(dana-core 0.1 (custom-tags) (none) (datas) (schemas) (consts) (funs) (none) \
         (meta (meta-entry \"n1\" (none) (some (span \"a.dana\" {TWO_POW_64} {TWO_POW_64} {TEN_POW_30} {TEN_POW_30})))))\n"
    );
    assert_diff_program("b1_span_big_nat", &span_wire, None, None);

    // 6. Expr::Proj.idx >= 2^64 (valid wire, cleanly rejected at type-check)
    let proj_wire = format!(
        "(dana-core 0.1 (custom-tags) (none) (datas) (schemas) (consts) (funs (fun-decl \"main\" fn false () (tags) \
         (lty (int) (tags)) (proj (tuple-val ((lit (lit-int 1)))) {TWO_POW_64}))) (some \"main\") (meta))\n"
    );
    assert_diff_program("b1_proj_big_nat", &proj_wire, None, None);
}

#[test]
fn differential_deep_nesting_b2_matches_lean_byte_for_byte() {
    fn wrap_prog(body: &str, ret: &str) -> String {
        format!(
            "(dana-core 0.1 (custom-tags) (none) (datas) (schemas) (consts) \
             (funs (fun-decl \"main\" fn false () (tags) (lty {ret} (tags)) {body})) (some \"main\") (meta))\n"
        )
    }

    const D: usize = 3_000;
    let tbl_ty =
        "(table-ty ((col \"x\" (int) (tags) false raw)) (tags) (tags) (none) false (none))";
    let tbl_ret = format!("(table {tbl_ty})");
    let src_tbl = format!("(source-expr (table-lit {tbl_ty} (((lit-int 1)))))");

    // 1. Deep let chain (depth 3,000)
    let mut let_body = "(lit (lit-int 1))".to_string();
    for _ in 0..D {
        let_body = format!("(let \"x\" (lty (int) (tags)) (lit (lit-int 1)) {let_body})");
    }
    let let_wire = wrap_prog(&let_body, "(int)");
    assert_diff_program("b2_let_3000", &let_wire, Some(D + 50), None);
    // Also exercise in-process parse/print/check/run/drop directly on default 2 MiB test thread!
    let p_let = parse_program(&let_wire).expect("parse deep let");
    assert_eq!(print_program(&p_let), let_wire);
    assert!(check_program(&p_let).is_ok());
    assert_eq!(
        run_program(D + 50, &p_let, World::default())
            .unwrap()
            .status,
        ExitStatus::Ok
    );
    drop(p_let);

    // 2. Deep unary prim chain (depth 3,000)
    let mut prim_body = "(lit (lit-int 1))".to_string();
    for _ in 0..D {
        prim_body = format!("(prim neg-int ({prim_body}))");
    }
    let prim_wire = wrap_prog(&prim_body, "(int)");
    assert_diff_program("b2_unary_prim_3000", &prim_wire, Some(D + 50), None);

    // 3. Deep nested limit plan (depth 3,000)
    let mut plan_body = src_tbl.clone();
    for _ in 0..D {
        plan_body = format!("(limit {plan_body} 1)");
    }
    let plan_wire = wrap_prog(&format!("(rel {plan_body})"), &tbl_ret);
    assert_diff_program("b2_nested_limit_3000", &plan_wire, Some(D + 50), None);

    // 4. Deep row-expr chain (depth 3,000)
    let mut re = "(re-lit (lit-int 1))".to_string();
    for _ in 0..D {
        re = format!("(re-prim neg-int ({re}))");
    }
    let filter_plan = format!("(filter {src_tbl} (re-prim eq ({re} (re-lit (lit-int 1)))))");
    let re_wire = wrap_prog(&format!("(rel {filter_plan})"), &tbl_ret);
    assert_diff_program("b2_row_expr_3000", &re_wire, Some(2 * D + 50), None);

    // 5. Deep option type nest (depth 3,000 — rejected cleanly without SIGABRT)
    let mut opt_ty = "(int)".to_string();
    for _ in 0..D {
        opt_ty = format!("(option {opt_ty})");
    }
    let opt_wire = format!(
        "(dana-core 0.1 (custom-tags) (none) (datas) (schemas) (consts) \
         (funs (fun-decl \"f\" fn false ((\"x\" (lty {opt_ty} (tags)))) (tags) (lty (int) (tags)) (lit (lit-int 1)))) (none) (meta))\n"
    );
    assert_diff_program("b2_option_ty_3000", &opt_wire, None, None);

    // 6. Deep list type nest (depth 3,000 — valid!)
    let mut list_ty = "(int)".to_string();
    for _ in 0..D {
        list_ty = format!("(list (lty {list_ty} (tags)))");
    }
    let list_wire = format!(
        "(dana-core 0.1 (custom-tags) (none) (datas) (schemas) (consts) \
         (funs (fun-decl \"f\" fn false ((\"x\" (lty {list_ty} (tags)))) (tags) (lty (int) (tags)) (lit (lit-int 1)))) (none) (meta))\n"
    );
    assert_diff_program("b2_list_ty_3000", &list_wire, None, None);

    // 7. Deep bare parens (depth 15,000)
    let parens_wire = format!("{}a{}\n", "(".repeat(15_000), ")".repeat(15_000));
    assert_diff_program("b2_bare_parens_15000", &parens_wire, None, None);

    // 8. Deep if chain (depth 1,500) & binary prim chain (depth 1,000)
    let mut if_body = "(lit (lit-int 1))".to_string();
    for _ in 0..1_500 {
        if_body = format!("(if (lit (lit-bool true)) {if_body} (lit (lit-int 0)))");
    }
    let if_wire = wrap_prog(&if_body, "(int)");
    assert_diff_program("b2_if_chain_1500", &if_wire, Some(2_000), None);

    let mut add_body = "(lit (lit-int 0))".to_string();
    for _ in 0..1_000 {
        add_body = format!("(prim add-int ((lit (lit-int 1)) {add_body}))");
    }
    let add_wire = wrap_prog(&add_body, "(int)");
    assert_diff_program("b2_bin_add_1000", &add_wire, Some(2_000), None);
}

#[test]
fn differential_closure_chains_and_non_peeled_deep_shapes_match_lean() {
    fn wrap_prog(body: &str, ret: &str) -> String {
        format!(
            "(dana-core 0.1 (custom-tags) (none) (datas) (schemas) (consts) \
             (funs (fun-decl \"main\" fn false () (tags) (lty {ret} (tags)) {body})) (some \"main\") (meta))\n"
        )
    }

    // 1. Closure chain O(2^N) OOM regression: N=500 (old Vec-cloned Env OOM'd at N=25).
    {
        const N: usize = 500;
        let fn_ty = "(lty (fn-ty () (tags) (lty (unit) (tags))) (tags))";
        let lam = "(lam () (tags) (lty (unit) (tags)) (lit (lit-unit)))";
        let mut body = String::new();
        for i in 0..N {
            use std::fmt::Write as _;
            let _ = write!(body, "(let \"f{i}\" {fn_ty} {lam} ");
        }
        body.push_str("(app (var \"f0\") ())");
        for _ in 0..N {
            body.push(')');
        }
        let wire = wrap_prog(&body, "(unit)");
        assert_diff_program("closure_chain_500", &wire, Some(N * 4 + 50), None);
    }

    // 2. Chained lexical closure calls: f0(x)=x; f1(x)=f0(x); ...; f200(42).
    {
        const N: usize = 200;
        let int_lty = "(lty (int) (tags))";
        let fn_ty = format!("(lty (fn-ty ({int_lty}) (tags) {int_lty}) (tags))");
        let mut body =
            format!("(let \"f0\" {fn_ty} (lam ((\"x\" {int_lty})) (tags) {int_lty} (var \"x\")) ");
        for i in 1..N {
            use std::fmt::Write as _;
            let _ = write!(
                body,
                "(let \"f{i}\" {fn_ty} (lam ((\"x\" {int_lty})) (tags) {int_lty} (app (var \"f{}\") ((var \"x\")))) ",
                i - 1
            );
        }
        use std::fmt::Write as _;
        let _ = write!(body, "(app (var \"f{}\") ((lit (lit-int 42))))", N - 1);
        for _ in 0..N {
            body.push(')');
        }
        let wire = wrap_prog(&body, "(int)");
        assert_diff_program("chained_closure_calls_200", &wire, Some(N * 6 + 50), None);
    }

    // 3. Previously debug-overflowing shapes at depth 6,000 (beyond ~5.7k old debug crash point).
    const D: usize = 6_000;
    let let_bound = wrap_prog(
        &format!(
            "{}(lit (lit-int 7)){}",
            "(let \"x\" (lty (int) (tags)) ".repeat(D),
            " (var \"x\"))".repeat(D)
        ),
        "(int)",
    );
    assert_diff_program("deep_let_bound_6000", &let_bound, Some(D * 4 + 50), None);

    let add_left = wrap_prog(
        &format!(
            "{}(lit (lit-int 0)){}",
            "(prim add-int (".repeat(D),
            " (lit (lit-int 1))))".repeat(D)
        ),
        "(int)",
    );
    assert_diff_program("deep_add_left_6000", &add_left, Some(D * 4 + 50), None);

    let add_right = wrap_prog(
        &format!(
            "{}(lit (lit-int 0)){}",
            "(prim add-int ((lit (lit-int 1)) ".repeat(D),
            "))".repeat(D)
        ),
        "(int)",
    );
    assert_diff_program("deep_add_right_6000", &add_right, Some(D * 4 + 50), None);

    let if_then = wrap_prog(
        &format!(
            "{}(lit (lit-int 1)){}",
            "(if (lit (lit-bool true)) ".repeat(D),
            " (lit (lit-int 0)))".repeat(D)
        ),
        "(int)",
    );
    assert_diff_program("deep_if_then_6000", &if_then, Some(D * 4 + 50), None);

    let if_else = wrap_prog(
        &format!(
            "{}(lit (lit-int 1)){}",
            "(if (lit (lit-bool false)) (lit (lit-int 0)) ".repeat(D),
            ")".repeat(D)
        ),
        "(int)",
    );
    assert_diff_program("deep_if_else_6000", &if_else, Some(D * 4 + 50), None);

    let tbl_ty =
        "(table-ty ((col \"a\" (int) (tags) false raw)) (tags) (tags) (none) false (none))";
    let empty_src = format!("(source-expr (table-lit {tbl_ty} ()))");
    let one_row_src = format!("(source-expr (table-lit {tbl_ty} (((lit-int 0)))))");

    let union_6k = wrap_prog(
        &format!(
            "(prim table-count ((rel {}{empty_src}{})))",
            "(union ".repeat(D),
            format!(" {empty_src})").repeat(D)
        ),
        "(int)",
    );
    assert_diff_program("deep_union_6000", &union_6k, Some(D * 4 + 50), None);

    let row_bin_6k = wrap_prog(
        &format!(
            "(prim table-count ((rel (filter {one_row_src} (re-prim eq ({}(re-col \"a\"){} (re-lit (lit-int {D}))))))))",
            "(re-prim add-int (".repeat(D),
            " (re-lit (lit-int 1))))".repeat(D)
        ),
        "(int)",
    );
    assert_diff_program(
        "deep_row_expr_bin_6000",
        &row_bin_6k,
        Some(D * 6 + 50),
        None,
    );

    let deep_case_6k = wrap_prog(
        &format!(
            "{}(lit (lit-int 9)){}",
            "(case (lit (lit-bool true)) ((arm \"true\" () ".repeat(D),
            ") (arm \"false\" () (lit (lit-int 0)))))".repeat(D)
        ),
        "(int)",
    );
    assert_diff_program("deep_case_6000", &deep_case_6k, Some(D * 4 + 50), None);

    let mut res_ty = "(int)".to_string();
    for _ in 0..D {
        res_ty = format!("(result {res_ty} (int))");
    }
    let result_ty_6k = wrap_prog(
        &format!("(lit (lit-none {res_ty}))"),
        &format!("(option {res_ty})"),
    );
    assert_diff_program("deep_result_ty_6000", &result_ty_6k, Some(100), None);

    // 4. Nested if-in-cond (depth 300) + fuel boundary sweep across core constructs.
    let if_cond_300 = wrap_prog(
        &format!(
            "{}(lit (lit-bool true)){}",
            "(if ".repeat(300),
            " (lit (lit-bool true)) (lit (lit-bool false)))".repeat(300)
        ),
        "(bool)",
    );
    assert_diff_program("deep_if_cond_300", &if_cond_300, Some(2_000), None);

    let join_loop_wire = wrap_prog(
        "(join-pt \"lp\" ((\"i\" (lty (int) (tags)))) \
         (if (prim lt ((var \"i\") (lit (lit-int 3)))) \
         (jump \"lp\" ((prim add-int ((var \"i\") (lit (lit-int 1)))))) \
         (var \"i\")) \
         (jump \"lp\" ((lit (lit-int 0)))))",
        "(int)",
    );
    for fuel in 0..=14 {
        assert_diff_program(
            &format!("fuel_join_loop_{fuel}"),
            &join_loop_wire,
            Some(fuel),
            None,
        );
    }
}
