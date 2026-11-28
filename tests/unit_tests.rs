//! Unit tests covering Dana Core IR AST, BigInt Euclidean arithmetic,
//! canonical wire codec, static verifier, naive oracle (real & fake World), and CLI parser.

use std::str::FromStr;

use dana::core::{
    AggItem, AggKind, AggOp, BigInt, BugKind, ChartKind, ColSpec, CompilerMetadata, ConstDecl,
    CoreVersion, CtorDecl, DEC_MAX, DEC_MIN, DEC_SCALE, DataDecl, DeriveItem, Expr, Float64,
    FunDecl, FunKind, HostOp, JoinKind, JoinOn, LTy, Literal, MetaEntry, Plan, Policy,
    PolicyWriteRule, PrimOp, Program, RowExpr, RowLit, ScalarTy, SchemaDecl, SortDir, SourceSpan,
    SuppressMode, TableTy, TagSet, Ty, WindowFn, WindowItem, check_program, is_safe_relative_path,
    join_confined_path, parse_canonical_sexp, parse_program, print_program, print_report,
};
use dana::oracle::{
    CliMode, ExitStatus, FakeDBState, StoredTable, TableRow, TableVal, Val, World, eval,
    float_order_key, fnv1a64, parse_cli_args, parse_comma_tags, pseudonymize_token, render_decimal,
    run_program, val_cmp, val_eq,
};

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

#[test]
fn bigint_euclidean_div_mod_matches_lean() {
    let cases = [
        (-7i64, 2i64, -4i64, 1i64),
        (7, -2, -3, 1),
        (-7, -2, 4, 1),
        (-6, 2, -3, 0),
        (-1, 2, -1, 1),
        (1, -2, 0, 1),
        (-1, -2, 1, 1),
        (0, 5, 0, 0),
        (0, -5, 0, 0),
    ];
    for (a, b, exp_q, exp_r) in cases {
        let ba = BigInt::from(a);
        let bb = BigInt::from(b);
        let (q, r) = ba.div_rem_euclid(&bb).expect("non-zero divisor");
        assert_eq!(q, BigInt::from(exp_q), "div_euclid({a}, {b})");
        assert_eq!(r, BigInt::from(exp_r), "rem_euclid({a}, {b})");
        assert_eq!(&bb * &q + r, ba);
    }
    assert!(BigInt::from(1).div_rem_euclid(&BigInt::ZERO).is_none());

    // Multi-limb 256-bit Decimal multiplication and division
    let max_dec = BigInt::from(DEC_MAX);
    let scale = BigInt::from(DEC_SCALE);
    let prod = &max_dec * &max_dec;
    let q = prod.div_euclid(&scale).unwrap();
    assert!(!q.in_decimal_range());

    // Negative multi-limb division
    let neg_num = -(&max_dec * &scale) - BigInt::one();
    let (nq, nr) = neg_num.div_rem_euclid(&scale).unwrap();
    assert_eq!(nq, -&max_dec - BigInt::one());
    assert_eq!(nr, &scale - &BigInt::one());

    // Range boundaries
    assert!(BigInt::from(i64::MIN).in_int64_range());
    assert!(BigInt::from(i64::MAX).in_int64_range());
    assert!(!(BigInt::from(i64::MIN) - BigInt::one()).in_int64_range());
    assert!(!(BigInt::from(i64::MAX) + BigInt::one()).in_int64_range());

    assert!(BigInt::from(DEC_MAX).in_decimal_range());
    assert!(BigInt::from(DEC_MIN).in_decimal_range());
    assert!(!BigInt::from(i128::MIN).in_decimal_range()); // -2^127 is outside [-(2^127-1), 2^127-1]

    // Parse & display roundtrip for huge integers
    let huge = "12345678901234567890123456789012345678901234567890";
    let parsed = BigInt::from_str(huge).unwrap();
    assert_eq!(parsed.to_string(), huge);
    let neg_huge = format!("-{huge}");
    assert_eq!(BigInt::from_str(&neg_huge).unwrap().to_string(), neg_huge);

    // Exact Float.ofInt bit parity with Lean 4.36.0 probe
    assert_eq!(
        BigInt::from(i64::MIN).to_f64().to_bits(),
        14_114_281_232_179_134_464
    );
    assert_eq!(
        BigInt::from(i64::MAX).to_f64().to_bits(),
        4_890_909_195_324_358_656
    );
    assert_eq!(
        BigInt::from(DEC_SCALE).to_f64().to_bits(),
        4_876_203_697_187_506_176
    );
    assert_eq!(
        BigInt::from(DEC_MAX).to_f64().to_bits(),
        5_179_139_571_476_070_400
    );
    assert_eq!(
        (BigInt::from(DEC_MAX).to_f64() / (DEC_SCALE as f64)).to_bits(),
        4_909_612_291_065_004_972
    );
}

#[test]
fn tag_set_semilattice_and_ordering() {
    let a = ts(&["pii", "ferpa", "pii"]);
    assert_eq!(a.elems(), &["ferpa", "pii"]);
    assert!(TagSet::from_canonical_elems(vec!["a".into(), "b".into()]).is_some());
    assert!(TagSet::from_canonical_elems(vec!["b".into(), "a".into()]).is_none());
    assert!(TagSet::from_canonical_elems(vec!["a".into(), "a".into()]).is_none());

    let b = ts(&["health", "pii"]);
    let c = ts(&["secret"]);
    assert_eq!(a.union(&b), b.union(&a));
    assert_eq!(a.union(&b).union(&c), a.union(&b.union(&c)));
    assert_eq!(a.union(&a), a);
    assert_eq!(a.union(&TagSet::empty()), a);
    assert!(a.is_subset(&a.union(&b)));
    assert_eq!(a.inter(&b), ts(&["pii"]));
    assert_eq!(a.diff(&b), ts(&["ferpa"]));
    assert_eq!(a.remove("pii"), ts(&["ferpa"]));
}

#[test]
fn float_order_key_and_canonical_nan() {
    let neg_nan = Float64::from_bits(0xffff_ffff_ffff_ffff);
    let neg_inf = Float64::from_bits(f64::NEG_INFINITY.to_bits());
    let neg_one = Float64::from_f64(-1.0);
    let neg_zero = Float64::from_bits((-0.0_f64).to_bits());
    let pos_zero = Float64::from_bits(0.0_f64.to_bits());
    let pos_one = Float64::from_f64(1.0);
    let pos_inf = Float64::from_bits(f64::INFINITY.to_bits());
    let canon_nan = Float64::CANONICAL_NAN;
    let payload_nan = Float64::from_bits(0x7ff8_0000_0000_0001);

    let ordered = [
        neg_nan,
        neg_inf,
        neg_one,
        neg_zero,
        pos_zero,
        pos_one,
        pos_inf,
        canon_nan,
        payload_nan,
    ];
    for w in ordered.windows(2) {
        assert!(float_order_key(w[0]) < float_order_key(w[1]));
        assert_eq!(
            val_cmp(&Val::Float(w[0]), &Val::Float(w[1])),
            std::cmp::Ordering::Less
        );
    }
    assert!(!val_eq(&Val::Float(neg_zero), &Val::Float(pos_zero)));
    assert!(val_eq(&Val::Float(canon_nan), &Val::Float(canon_nan)));
    assert!(!val_eq(&Val::Float(canon_nan), &Val::Float(payload_nan)));
    assert_eq!(
        Float64::from_f64(f64::from_bits(0x7ff8_0000_0000_0001)).bits,
        0x7ff8_0000_0000_0000
    );
    assert_eq!(
        Float64::from_f64(f64::from_bits(0xfff8_0000_0000_0000)).bits,
        0x7ff8_0000_0000_0000
    );
}

#[test]
fn wire_roundtrip_and_strict_rejections() {
    let rich = Program {
        version: CoreVersion { major: 0, minor: 1 },
        tags: vec!["hipaa_custom".to_string()],
        policy: Some(Policy {
            min_group_size: BigInt::from(5u64),
            forbid_manual_declassify: false,
            forbid_repl_sensitive: true,
            allow_console: TagSet::empty(),
            allow_export: vec![("exports/".to_string(), ts(&["hipaa_custom"]))],
            allow_https: vec![("api.example.org".to_string(), ts(&["pii"]))],
            allow_write: vec![PolicyWriteRule {
                db: "warehouse".to_string(),
                table: "cohorts".to_string(),
                tags: ts(&["ferpa"]),
            }],
            ..Policy::default()
        }),
        datas: vec![DataDecl {
            name: "Status".to_string(),
            ctors: vec![
                CtorDecl {
                    name: "Active".to_string(),
                    fields: vec![LTy::public(Ty::Int)],
                },
                CtorDecl {
                    name: "Inactive".to_string(),
                    fields: vec![],
                },
            ],
        }],
        schemas: vec![SchemaDecl {
            name: "S".to_string(),
            schema: TableTy {
                cols: vec![col("id", ScalarTy::Int, ts(&["pii"]))],
                ..TableTy::default()
            },
        }],
        consts: vec![ConstDecl {
            name: "K".to_string(),
            lty: LTy::public(Ty::Int),
            value: Literal::int(42),
        }],
        funs: vec![FunDecl {
            name: "main".to_string(),
            kind: FunKind::Function,
            is_pure: false,
            params: vec![("c".to_string(), LTy::public(Ty::Console(TagSet::empty())))],
            pc: TagSet::empty(),
            ret: LTy::public(Ty::Unit),
            body: Expr::Host {
                op: HostOp::ConsolePrint,
                args: vec![
                    Expr::Var("c".to_string()),
                    Expr::Lit(Literal::Text(
                        "line1\n\t\r\"\\\u{01}\u{7f}\u{85}".to_string(),
                    )),
                ],
            },
        }],
        entry: Some("main".to_string()),
        metadata: CompilerMetadata {
            entries: vec![MetaEntry {
                node_id: "n0".to_string(),
                orig_name: Some("nel:\u{85}".to_string()),
                span: Some(SourceSpan {
                    file: "src/app.dana".to_string(),
                    start_line: BigInt::from(1u64),
                    start_col: BigInt::from(1u64),
                    end_line: BigInt::from(10u64),
                    end_col: BigInt::from(5u64),
                }),
            }],
        },
    };
    assert!(check_program(&rich).is_ok());
    let wire = print_program(&rich);
    assert!(wire.contains("\\u{1}"));
    assert!(wire.contains("\\u{7f}"));
    assert!(wire.contains("\\u{85}"));
    assert_eq!(parse_program(&wire).unwrap(), rich);

    // Rejections
    let bad_wires: &[(&str, &str)] = &[
        (
            "(dana-core 0.2 (custom-tags) (none) (datas) (schemas) (consts) (funs) (none) (meta))\n",
            "unsupported dana-core wire version",
        ),
        (
            "(dana-core 0.1 (custom-tags) (none) (datas) (schemas) (consts) (funs) (none) (meta))",
            "single trailing LF",
        ),
        (
            "(dana-core 0.1 (custom-tags) (none) (datas) (schemas) (consts) (funs) (none) (meta))\n\n",
            "internal line breaks",
        ),
        (
            "(dana-core  0.1 (custom-tags) (none) (datas) (schemas) (consts) (funs) (none) (meta))\n",
            "duplicate space",
        ),
        (
            "( dana-core 0.1 (custom-tags) (none) (datas) (schemas) (consts) (funs) (none) (meta))\n",
            "leading space",
        ),
        (
            "(dana-core 0.1 (custom-tags) (none) (datas) (schemas) (consts) (funs) (none) (meta) )\n",
            "trailing space",
        ),
        (
            "(dana-core 0.1 (custom-tags) (none) (datas) (schemas) (consts) (funs) (some \"\\u{d800}\") (meta))\n",
            "surrogate",
        ),
        (
            "(dana-core 0.1 (custom-tags) (none) (datas) (schemas) (consts) (funs) (some \"\\u{41}\") (meta))\n",
            "non-canonical",
        ),
        (
            "(dana-core 0.1 (custom-tags) (none) (datas) (schemas) (consts) (funs) (some \"\\u{0A}\") (meta))\n",
            "non-lowercase",
        ),
        (
            "(dana-core 0.1 (custom-tags) (none) (datas) (schemas) (consts) (funs) (some \"\\u{01}\") (meta))\n",
            "non-canonical",
        ),
        (
            "(dana-core 0.1 (custom-tags) (none) (datas) (schemas) (consts) (funs) (some \"\\u{a}\") (meta))\n",
            "non-canonical",
        ),
        (
            "(dana-core 0.1 (custom-tags) (none) (datas) (schemas) (consts) (funs) (some main) (meta))\n",
            "non-canonical",
        ),
        (
            "(dana-core 0.1 (custom-tags) (none) (datas) (schemas) (consts) (funs (fun-decl \"main\" fn false () (tags) (lty (int) (tags)) (lit (lit-int 007)))) (some \"main\") (meta))\n",
            "non-canonical",
        ),
        (
            "(dana-core 0.1 (custom-tags) (none) (datas) (schemas) (consts) (funs (fun-decl \"main\" fn false () (tags) (lty (int) (tags)) (lit (lit-int -0)))) (some \"main\") (meta))\n",
            "non-canonical",
        ),
        (
            "(dana-core 0.1 (custom-tags) (none) (datas) (schemas) (consts) (funs (fun-decl \"main\" fn false () (tags) (lty (float) (tags)) (lit (lit-float 18446744073709551616)))) (some \"main\") (meta))\n",
            "non-canonical",
        ),
        (
            "(dana-core 0.1 (custom-tags) (none) (datas) (schemas) (consts) (funs) (none) (meta (meta-entry \"n1\" (none) (some (span \"a.dana\" 0 1 1 1)))))\n",
            "invalid SourceSpan",
        ),
        (
            "(dana-core 0.1 (custom-tags) (none) (datas) (schemas) (consts) (funs) (none) (meta (meta-entry \"\" (none) (none))))\n",
            "empty nodeId",
        ),
    ];
    for (bad, expected_sub) in bad_wires {
        let err = parse_program(bad).expect_err(&format!("expected failure for: {bad}"));
        assert!(
            err.message.contains(expected_sub),
            "expected '{expected_sub}' in '{}'",
            err.message
        );
    }
    assert!(parse_canonical_sexp("(a \u{01})\n").is_err());
    assert!(parse_canonical_sexp("(a \"\u{85}\")\n").is_err());
}

#[test]
fn path_confinement_and_decimal_rendering() {
    assert!(!is_safe_relative_path(""));
    assert!(!is_safe_relative_path("/etc/passwd"));
    assert!(!is_safe_relative_path("../leak.csv"));
    assert!(!is_safe_relative_path("a/../b"));
    assert!(!is_safe_relative_path("a\\b"));
    assert!(is_safe_relative_path("reports/q1.csv"));
    assert_eq!(join_confined_path("out", "_evil/x"), "out/_evil/x");
    assert_eq!(join_confined_path("out/", "a.csv"), "out/a.csv");
    assert_eq!(join_confined_path("", "a.csv"), "a.csv");

    assert_eq!(render_decimal(&BigInt::ZERO), "0.0");
    assert_eq!(render_decimal(&BigInt::from(DEC_SCALE)), "1.0");
    assert_eq!(render_decimal(&BigInt::from(-DEC_SCALE)), "-1.0");
    assert_eq!(
        render_decimal(&BigInt::from(-500_000_000_000_000_000i128)),
        "-0.5"
    );
    assert_eq!(render_decimal(&BigInt::from(1i64)), "0.000000000000000001");
}

#[test]
fn world_fixtures_real_db_csv_and_fake_handles() {
    let student_schema = TableTy {
        cols: vec![
            col("id", ScalarTy::Int, ts(&["pii"])),
            col("email", ScalarTy::Text, ts(&["pii"])),
            col("program", ScalarTy::Text, TagSet::empty()),
            col("credits", ScalarTy::Int, ts(&["ferpa"])),
            col("gpa", ScalarTy::Decimal, ts(&["ferpa"])),
        ],
        ..TableTy::default()
    };

    // Real DB + bucket + suppress_small_groups(distinct_by: .id)
    let k_anon_prog = Program {
        schemas: vec![SchemaDecl {
            name: "Students".to_string(),
            schema: student_schema.clone(),
        }],
        funs: vec![FunDecl {
            name: "main".to_string(),
            kind: FunKind::Function,
            is_pure: false,
            params: vec![
                (
                    "db".to_string(),
                    LTy::public(Ty::ReadDB("registrar".into())),
                ),
                (
                    "console".to_string(),
                    LTy::public(Ty::Console(TagSet::empty())),
                ),
            ],
            pc: TagSet::empty(),
            ret: LTy::public(Ty::Unit),
            body: Expr::Host {
                op: HostOp::ConsolePrintTable,
                args: vec![
                    Expr::Var("console".into()),
                    Expr::Rel(Box::new(Plan::SuppressSmallGroups {
                        input: Box::new(Plan::Summarize {
                            input: Box::new(Plan::GroupBy {
                                input: Box::new(Plan::Derive {
                                    input: Box::new(Plan::SourceDB {
                                        cap: Box::new(Expr::Var("db".into())),
                                        table_name: "students".into(),
                                        schema: student_schema.clone(),
                                    }),
                                    items: vec![DeriveItem::BucketCol {
                                        name: "gpa_band".into(),
                                        source: "gpa".into(),
                                        cuts: vec![
                                            Literal::decimal(2 * DEC_SCALE),
                                            Literal::decimal(3 * DEC_SCALE),
                                        ],
                                        labels: vec![
                                            "<2.0".into(),
                                            "2.0-3.0".into(),
                                            ">=3.0".into(),
                                        ],
                                    }],
                                }),
                                keys: vec!["program".into(), "gpa_band".into()],
                            }),
                            aggs: vec![
                                AggItem {
                                    name: "n".into(),
                                    op: AggOp::Count,
                                    arg: None,
                                },
                                AggItem {
                                    name: "total_credits".into(),
                                    op: AggOp::Sum,
                                    arg: Some(RowExpr::Col("credits".into())),
                                },
                            ],
                            distinct_key: Some("id".into()),
                        }),
                        min_k: BigInt::from(5u64),
                        distinct_by: Some("id".into()),
                        mode: SuppressMode::Drop,
                    })),
                ],
            },
        }],
        entry: Some("main".into()),
        ..Program::default()
    };

    let tenth = DEC_SCALE / 10;
    let world = World {
        real_db_tables: vec![StoredTable {
            db: "registrar".into(),
            table_name: "students".into(),
            schema: student_schema.clone(),
            rows: vec![
                vec![
                    Val::Int(1.into()),
                    Val::Text("s1@u.edu".into()),
                    Val::Text("CS".into()),
                    Val::Int(15.into()),
                    Val::Decimal((35 * tenth).into()),
                ],
                vec![
                    Val::Int(2.into()),
                    Val::Text("s2@u.edu".into()),
                    Val::Text("CS".into()),
                    Val::Int(15.into()),
                    Val::Decimal((36 * tenth).into()),
                ],
                vec![
                    Val::Int(3.into()),
                    Val::Text("s3@u.edu".into()),
                    Val::Text("CS".into()),
                    Val::Int(15.into()),
                    Val::Decimal((37 * tenth).into()),
                ],
                vec![
                    Val::Int(4.into()),
                    Val::Text("s4@u.edu".into()),
                    Val::Text("CS".into()),
                    Val::Int(15.into()),
                    Val::Decimal((38 * tenth).into()),
                ],
                vec![
                    Val::Int(5.into()),
                    Val::Text("s5@u.edu".into()),
                    Val::Text("CS".into()),
                    Val::Int(15.into()),
                    Val::Decimal((39 * tenth).into()),
                ],
                // 6 Math rows with only 3 distinct IDs -> suppressed!
                vec![
                    Val::Int(10.into()),
                    Val::Text("m1@u.edu".into()),
                    Val::Text("Math".into()),
                    Val::Int(12.into()),
                    Val::Decimal((35 * tenth).into()),
                ],
                vec![
                    Val::Int(10.into()),
                    Val::Text("m1@u.edu".into()),
                    Val::Text("Math".into()),
                    Val::Int(12.into()),
                    Val::Decimal((35 * tenth).into()),
                ],
                vec![
                    Val::Int(11.into()),
                    Val::Text("m2@u.edu".into()),
                    Val::Text("Math".into()),
                    Val::Int(12.into()),
                    Val::Decimal((36 * tenth).into()),
                ],
                vec![
                    Val::Int(11.into()),
                    Val::Text("m2@u.edu".into()),
                    Val::Text("Math".into()),
                    Val::Int(12.into()),
                    Val::Decimal((36 * tenth).into()),
                ],
                vec![
                    Val::Int(12.into()),
                    Val::Text("m3@u.edu".into()),
                    Val::Text("Math".into()),
                    Val::Int(12.into()),
                    Val::Decimal((37 * tenth).into()),
                ],
                vec![
                    Val::Int(12.into()),
                    Val::Text("m3@u.edu".into()),
                    Val::Text("Math".into()),
                    Val::Int(12.into()),
                    Val::Decimal((37 * tenth).into()),
                ],
            ],
        }],
        ..World::default()
    };
    let rep = run_program(64, &k_anon_prog, world).unwrap();
    assert_eq!(rep.status, ExitStatus::Ok);
    assert_eq!(
        rep.stdout,
        vec!["program | gpa_band | n | total_credits\nCS | >=3.0 | 5 | 75"]
    );
    assert!(print_report(&rep).starts_with("(dana-report 0.1 (status ok)"));

    // Pseudonymize with real secret & Unicode value
    let tok1 = pseudonymize_token("k_secret_42", &Val::Text("alice@u.edu".into()));
    assert!(tok1.starts_with("ps_"));
    assert_eq!(tok1.len(), 19);
    let unicode_hash = fnv1a64("k:é");
    assert_ne!(unicode_hash, 0);

    // Spec test using fakeConsole + fakeFiles + fakeDB + fakeSecret + fail
    let spec_prog = Program {
        funs: vec![FunDecl {
            name: "spec_check".into(),
            kind: FunKind::Test,
            is_pure: false,
            params: vec![],
            pc: TagSet::empty(),
            ret: LTy::public(Ty::Unit),
            body: Expr::LetE {
                name: "fc".into(),
                lty: LTy::public(Ty::Console(ts(&["pii"]))),
                bound: Box::new(Expr::Host {
                    op: HostOp::FakeConsole(ts(&["pii"])),
                    args: vec![],
                }),
                body: Box::new(Expr::LetE {
                    name: "_p".into(),
                    lty: LTy::public(Ty::Unit),
                    bound: Box::new(Expr::Host {
                        op: HostOp::ConsolePrint,
                        args: vec![
                            Expr::Var("fc".into()),
                            Expr::Lit(Literal::Text("hi".into())),
                        ],
                    }),
                    body: Box::new(Expr::Fail(Box::new(Expr::Lit(Literal::Text(
                        "assertion failed".into(),
                    ))))),
                }),
            },
        }],
        ..Program::default()
    };
    assert!(check_program(&spec_prog).is_ok());
    let spec_out = eval(
        64,
        &spec_prog,
        &[],
        &TagSet::empty(),
        World {
            fake_dbs: vec![FakeDBState {
                db: "d".into(),
                tables: vec![],
            }],
            ..World::default()
        },
        &spec_prog.funs[0].body,
    );
    let spec_rep = dana::oracle::extract_report(spec_out).unwrap();
    assert_eq!(spec_rep.status, ExitStatus::Failed);
    assert_eq!(spec_rep.diagnostic.as_deref(), Some("assertion failed"));
    assert_eq!(spec_rep.fake_consoles.len(), 1);
    assert_eq!(spec_rep.fake_consoles[0].stdout, vec!["hi"]);

    // TableProfile redacts tagged columns
    let tv = TableVal {
        cols: vec![
            col("pub_x", ScalarTy::Int, TagSet::empty()),
            col("sec_y", ScalarTy::Text, ts(&["pii"])),
        ],
        rows: vec![
            TableRow {
                cells: vec![Val::Int(10.into()), Val::Text("secret1".into())],
                group_meta: None,
            },
            TableRow {
                cells: vec![Val::Int(20.into()), Val::Text("secret2".into())],
                group_meta: None,
            },
        ],
    };
    let pv = match dana::oracle::eval_prim_op(&PrimOp::TableProfile, &[Val::Table(tv)]) {
        dana::oracle::eval::PrimResult::Ok(Val::Profile(ref pv)) => Some(pv.clone()),
        _ => None,
    }
    .expect("expected ProfileVal");
    assert_eq!(pv.cols[0].min_display.as_deref(), Some("10"));
    assert_eq!(pv.cols[0].max_display.as_deref(), Some("20"));
    assert_eq!(pv.cols[1].min_display.as_deref(), Some("[REDACTED:pii]"));
    assert_eq!(pv.cols[1].max_display.as_deref(), Some("[REDACTED:pii]"));

    // Window & Join types smoke check
    let _unused = (
        ChartKind::Bar,
        JoinKind::InnerOne,
        JoinOn::SameKeys(vec!["id".into()]),
        SortDir::Asc,
        WindowItem {
            name: "rn".into(),
            win_fn: WindowFn::RowNumber,
            over: vec![],
            order: vec![],
        },
        RowLit { cells: vec![] },
        BugKind::UserStop,
    );
}

#[test]
fn cli_arg_parser_strictness() {
    let args = |xs: &[&str]| xs.iter().map(|s| (*s).to_string()).collect::<Vec<_>>();

    let o1 = parse_cli_args(&args(&["foo.core"])).unwrap();
    assert_eq!(o1.mode, CliMode::Run);
    assert_eq!(o1.path, "foo.core");
    assert_eq!(o1.fuel, 4096);
    assert!(o1.allow_export.is_empty());

    let o2 = parse_cli_args(&args(&[
        "run",
        "a.core",
        "--fuel",
        "123",
        "--allow-export",
        "ferpa,pii",
    ]))
    .unwrap();
    assert_eq!(o2.mode, CliMode::Run);
    assert_eq!(o2.fuel, 123);
    assert_eq!(o2.allow_export, ts(&["ferpa", "pii"]));

    assert_eq!(
        parse_cli_args(&args(&["check", "a.core"])).unwrap().mode,
        CliMode::Check
    );
    assert_eq!(
        parse_cli_args(&args(&["fmt", "a.core"])).unwrap().mode,
        CliMode::Fmt
    );

    // Every invalid CLI case matching Makefile smoke checks & Main.lean
    let bad_cli: &[&[&str]] = &[
        &[],
        &["a.core", "check"],
        &["run", "check", "a.core"],
        &["run", "a.core", "b.core"],
        &["run", "a.core", "--fuel"],
        &["run", "a.core", "--fuel", "10", "--fuel", "20"],
        &["run", "a.core", "--fuel", "--allow-export"],
        &["run", "a.core", "--fuel", "1_0"],
        &["run", "a.core", "--fuel", "-5"],
        &["run", "a.core", "--fuel", "abc"],
        &["run", "a.core", "--allow-export"],
        &[
            "run",
            "a.core",
            "--allow-export",
            "pii",
            "--allow-export",
            "ferpa",
        ],
        &["run", "a.core", "--allow-export", "--fuel"],
        &["run", "a.core", "--allow-export", ""],
        &["run", "a.core", "--allow-export", "pii,,ferpa"],
        &["run", "a.core", "--allow-export", "-pii"],
        &["run", "a.core", "--allow-export", "pii,pii"],
        &["run", "a.core", "--unknown"],
    ];
    for case in bad_cli {
        assert!(
            parse_cli_args(&args(case)).is_err(),
            "expected CLI error for: {case:?}"
        );
    }
    assert_eq!(
        parse_comma_tags("pii,custom_1-a").unwrap(),
        ts(&["custom_1-a", "pii"])
    );
}

#[test]
fn deep_nesting_and_linear_let_env_on_default_2mib_test_thread() {
    // Runs directly on the default 2 MiB `cargo test` thread without spawning a larger test thread.
    const D: usize = 5_000;
    let tbl_schema = TableTy {
        cols: vec![col("x", ScalarTy::Int, TagSet::empty())],
        ..TableTy::default()
    };
    let big_tbl = Expr::TableLit {
        schema: tbl_schema.clone(),
        rows: (0..10)
            .map(|i| RowLit {
                cells: vec![Literal::int(i)],
            })
            .collect(),
    };
    // 5,000 nested `let`s after binding a table — exercises O(1) persistent EnvList (linear, not quadratic!)
    let mut body = Expr::Prim {
        op: PrimOp::TableCount,
        args: vec![Expr::Var("tbl".into())],
    };
    for _ in 0..D {
        body = Expr::LetE {
            name: "n".into(),
            lty: LTy::public(Ty::Int),
            bound: Box::new(Expr::Lit(Literal::int(1))),
            body: Box::new(body),
        };
    }
    body = Expr::LetE {
        name: "tbl".into(),
        lty: LTy::public(Ty::Table(tbl_schema.clone())),
        bound: Box::new(big_tbl),
        body: Box::new(body),
    };
    let prog = Program {
        funs: vec![FunDecl {
            name: "main".into(),
            kind: FunKind::Function,
            is_pure: false,
            params: vec![],
            pc: TagSet::empty(),
            ret: LTy::public(Ty::Int),
            body,
        }],
        entry: Some("main".into()),
        ..Program::default()
    };
    let wire = print_program(&prog);
    let parsed = parse_program(&wire).expect("parse 5000-deep let");
    assert_eq!(print_program(&parsed), wire);
    dana::core::with_large_stack(|| assert_eq!(parsed, prog));
    assert!(check_program(&parsed).is_ok());
    let rep = run_program(D + 100, &parsed, World::default()).expect("run 5000-deep let");
    assert_eq!(rep.status, ExitStatus::Ok);
    drop(parsed);
    drop(prog);

    // 5,000 nested Ty::Option and Ty::List drop safely on 2 MiB stack
    let mut opt_ty = Ty::Int;
    let mut list_ty = Ty::Int;
    for _ in 0..D {
        opt_ty = Ty::Option(Box::new(opt_ty));
        list_ty = Ty::List(Box::new(LTy::public(list_ty)));
    }
    assert!(!dana::core::check::valid_ty(&Program::default(), &opt_ty));
    assert!(dana::core::check::valid_ty(&Program::default(), &list_ty));
    drop(opt_ty);
    drop(list_ty);

    // 15,000 nested bare parens parse/drop safely on 2 MiB stack
    let parens = format!("{}a{}\n", "(".repeat(15_000), ")".repeat(15_000));
    assert!(parse_canonical_sexp(&parens).is_ok());
    assert!(parse_program(&parens).is_err());

    // 2,000 let-bound closure chain (O(2^N) OOM regression: must stay linear in RAM & O(1) stack)
    let fn_ty = "(lty (fn-ty () (tags) (lty (unit) (tags))) (tags))";
    let lam = "(lam () (tags) (lty (unit) (tags)) (lit (lit-unit)))";
    let mut clo_body = String::new();
    for i in 0..2_000 {
        use std::fmt::Write as _;
        let _ = write!(clo_body, "(let \"f{i}\" {fn_ty} {lam} ");
    }
    clo_body.push_str("(app (var \"f0\") ())");
    for _ in 0..2_000 {
        clo_body.push(')');
    }
    let clo_wire = format!(
        "(dana-core 0.1 (custom-tags) (none) (datas) (schemas) (consts) \
         (funs (fun-decl \"main\" fn false () (tags) (lty (unit) (tags)) {clo_body})) \
         (some \"main\") (meta))\n"
    );
    let clo_prog = parse_program(&clo_wire).expect("parse 2000-closure chain");
    assert_eq!(print_program(&clo_prog), clo_wire);
    assert!(check_program(&clo_prog).is_ok());
    let clo_rep = run_program(10_000, &clo_prog, World::default()).expect("run 2000-closure chain");
    assert_eq!(clo_rep.status, ExitStatus::Ok);
    drop(clo_prog);

    // 6,000-deep non-peeled shapes on default 2 MiB test thread (parse, print, check, run, drop)
    const D6: usize = 6_000;
    let deep_wires = [
        (
            "let_bound_6k",
            format!(
                "(dana-core 0.1 (custom-tags) (none) (datas) (schemas) (consts) \
                 (funs (fun-decl \"main\" fn false () (tags) (lty (int) (tags)) {}(lit (lit-int 7)){})) \
                 (some \"main\") (meta))\n",
                "(let \"x\" (lty (int) (tags)) ".repeat(D6),
                " (var \"x\"))".repeat(D6),
            ),
        ),
        (
            "add_left_6k",
            format!(
                "(dana-core 0.1 (custom-tags) (none) (datas) (schemas) (consts) \
                 (funs (fun-decl \"main\" fn false () (tags) (lty (int) (tags)) {}(lit (lit-int 0)){})) \
                 (some \"main\") (meta))\n",
                "(prim add-int (".repeat(D6),
                " (lit (lit-int 1))))".repeat(D6),
            ),
        ),
        (
            "if_else_6k",
            format!(
                "(dana-core 0.1 (custom-tags) (none) (datas) (schemas) (consts) \
                 (funs (fun-decl \"main\" fn false () (tags) (lty (int) (tags)) {}(lit (lit-int 1)){})) \
                 (some \"main\") (meta))\n",
                "(if (lit (lit-bool false)) (lit (lit-int 0)) ".repeat(D6),
                ")".repeat(D6),
            ),
        ),
    ];
    for (name, wire) in deep_wires {
        let p = parse_program(&wire).expect(name);
        assert_eq!(print_program(&p), wire, "{name} print roundtrip");
        assert!(check_program(&p).is_ok(), "{name} check");
        let rep = run_program(D6 * 4 + 50, &p, World::default()).expect(name);
        assert_eq!(rep.status, ExitStatus::Ok, "{name} run");
        drop(p);
    }
}

#[test]
fn unbounded_nat_wire_roundtrip_and_check_eval() {
    let two_pow_64: BigInt = "18446744073709551616".parse().unwrap();
    let ten_pow_30: BigInt = "1000000000000000000000000000000".parse().unwrap();
    let prog = Program {
        policy: Some(Policy {
            min_group_size: two_pow_64.clone(),
            ..Policy::default()
        }),
        funs: vec![FunDecl {
            name: "main".into(),
            kind: FunKind::Function,
            is_pure: false,
            params: vec![],
            pc: TagSet::empty(),
            ret: LTy::public(Ty::Table(TableTy {
                cols: vec![
                    col("g", ScalarTy::Text, TagSet::empty()),
                    col("n", ScalarTy::Int, TagSet::empty()),
                ],
                ..TableTy::default()
            })),
            body: Expr::Rel(Box::new(Plan::Limit {
                input: Box::new(Plan::SuppressSmallGroups {
                    input: Box::new(Plan::Summarize {
                        input: Box::new(Plan::GroupBy {
                            input: Box::new(Plan::SourceExpr(Box::new(Expr::TableLit {
                                schema: TableTy {
                                    cols: vec![col("g", ScalarTy::Text, TagSet::empty())],
                                    ..TableTy::default()
                                },
                                rows: vec![RowLit {
                                    cells: vec![Literal::Text("a".into())],
                                }],
                            }))),
                            keys: vec!["g".into()],
                        }),
                        aggs: vec![AggItem {
                            name: "n".into(),
                            op: AggOp::Count,
                            arg: None,
                        }],
                        distinct_key: None,
                    }),
                    min_k: ten_pow_30.clone(),
                    distinct_by: None,
                    mode: SuppressMode::Drop,
                }),
                n: ten_pow_30.clone(),
            })),
        }],
        entry: Some("main".into()),
        metadata: CompilerMetadata {
            entries: vec![MetaEntry {
                node_id: "m0".into(),
                orig_name: None,
                span: Some(SourceSpan {
                    file: "big.dana".into(),
                    start_line: two_pow_64.clone(),
                    start_col: two_pow_64.clone(),
                    end_line: ten_pow_30.clone(),
                    end_col: ten_pow_30,
                }),
            }],
        },
        ..Program::default()
    };
    let wire = print_program(&prog);
    assert!(wire.contains("18446744073709551616"));
    assert!(wire.contains("1000000000000000000000000000000"));
    let parsed = parse_program(&wire).unwrap();
    assert_eq!(parsed, prog);
    assert!(check_program(&parsed).is_ok());
    let rep = run_program(4096, &parsed, World::default()).unwrap();
    assert_eq!(rep.status, ExitStatus::Ok);
}
