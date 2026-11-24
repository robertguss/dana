//! Phase 2C Wave 5 — 1,000,000-Row Columnar Throughput & Parallel Scaling Smoke Benchmark.
//!
//! Benchmarks:
//! 1. **1,000,000-row columnar pipeline** (`Filter(.qty > 0) |> Derive(tax: net_tax(.amount, .rate))
//!    |> GroupBy(.region) |> Summarize(total_tax: sum(.tax), row_count: count()) |> Sort(.region)`)
//!    with a non-recursive pure Dana UDF (`net_tax` using `IfE`, `MulDec`, `SubDec`) inlined into
//!    register bytecode — sequential vs. parallel cell-for-cell parity and throughput metrics.
//! 2. **100,000-row `HashJoin` + `GroupBy` + `HashAggregate` + `Sort`** sequential vs. parallel
//!    parity and throughput metrics.

use std::time::Instant;

use dana::core::{
    AggItem, AggKind, AggOp, ColSpec, DEC_SCALE, DeriveItem, Expr, FunDecl, FunKind, JoinKind,
    JoinOn, LTy, Literal, Plan, PrimOp, Program, RowExpr, ScalarTy, SortDir, TagSet, Ty,
};
use dana::oracle::Val;
use dana::oracle::value::val_list_eq;
use dana::runtime::ir::PseudonymizeMode;
use dana::vm::expr::{RowEvalErr, RowEvalHost, compile_core_row_expr};
use dana::vm::ops::agg::{CompiledAgg, op_hash_aggregate};
use dana::vm::ops::join::op_hash_join;
use dana::vm::ops::sort_win::op_sort;
use dana::vm::ops::{OpExecConfig, VmMode, op_group_by};
use dana::vm::{BATCH_SIZE, Batch, Column, ColumnData, VmConfig, VmTable, eval_core_plan_batches};

fn pub_col(name: &str, ty: ScalarTy) -> ColSpec {
    ColSpec {
        name: name.to_string(),
        ty,
        tags: TagSet::empty(),
        bucketed: false,
        agg_kind: AggKind::Raw,
    }
}

/// Build a 1,000,000-row columnar [`VmTable`] directly in 2,048-row batches (zero row-boxing).
fn build_sales_1m_table(n_rows: usize) -> VmTable {
    let specs = vec![
        pub_col("region", ScalarTy::Text),
        pub_col("amount", ScalarTy::Decimal),
        pub_col("rate", ScalarTy::Decimal),
        pub_col("qty", ScalarTy::Int),
    ];
    let regions: Vec<String> = (0..16).map(|r| format!("region_{r:02}")).collect();
    let n_batches = n_rows.div_ceil(BATCH_SIZE);
    let mut batches = Vec::with_capacity(n_batches);

    let mut remaining = n_rows;
    let mut base_row = 0usize;
    while remaining > 0 {
        let len = remaining.min(BATCH_SIZE);
        let mut r_offsets = Vec::with_capacity(len + 1);
        let mut r_data = Vec::with_capacity(len * 9);
        let mut amounts = Vec::with_capacity(len);
        let mut rates = Vec::with_capacity(len);
        let mut qtys = Vec::with_capacity(len);
        r_offsets.push(0);

        for j in 0..len {
            let idx = base_row + j;
            let reg = regions[idx & 15].as_bytes();
            r_data.extend_from_slice(reg);
            r_offsets.push(r_data.len());

            // Deterministic positive decimals: $10.00 .. $259.00
            let amt_dollars = ((idx % 250) as i128) + 10;
            amounts.push(amt_dollars * DEC_SCALE);

            // Deterministic rates: 0.05 .. 0.12
            let rate_bps = ((idx % 8) as i128) + 5;
            rates.push(rate_bps * (DEC_SCALE / 100));

            // ~10% qty == 0
            let qty = if idx.is_multiple_of(10) {
                0
            } else {
                ((idx % 7) as i64) + 1
            };
            qtys.push(qty);
        }

        batches.push(Batch {
            cols: vec![
                Column {
                    spec: specs[0].clone(),
                    data: ColumnData::Text {
                        offsets: r_offsets,
                        data: r_data,
                    },
                    validity: None,
                },
                Column {
                    spec: specs[1].clone(),
                    data: ColumnData::Decimal(amounts),
                    validity: None,
                },
                Column {
                    spec: specs[2].clone(),
                    data: ColumnData::Decimal(rates),
                    validity: None,
                },
                Column {
                    spec: specs[3].clone(),
                    data: ColumnData::Int(qtys),
                    validity: None,
                },
            ],
            len,
            selection: None,
            group_meta: None,
        });
        base_row += len;
        remaining -= len;
    }

    VmTable {
        cols: specs,
        batches,
    }
}

#[test]
fn bench_1m_rows_filter_inlined_udf_agg_seq_vs_parallel() -> Result<(), String> {
    const N_ROWS: usize = 1_000_000;
    let source_tbl = build_sales_1m_table(N_ROWS);
    assert_eq!(source_tbl.total_rows(), N_ROWS);

    // Non-recursive pure Dana UDF `net_tax(amount: Decimal, rate: Decimal) : Decimal`:
    //   if amount > 100.00 then (amount * rate) - 1.50 else (amount * rate)
    let prog = Program {
        funs: vec![FunDecl {
            name: "net_tax".into(),
            kind: FunKind::Function,
            is_pure: true,
            params: vec![
                ("amount".into(), LTy::public(Ty::Decimal)),
                ("rate".into(), LTy::public(Ty::Decimal)),
            ],
            pc: TagSet::empty(),
            ret: LTy::public(Ty::Decimal),
            body: Expr::IfE {
                cond: Box::new(Expr::Prim {
                    op: PrimOp::Gt,
                    args: vec![
                        Expr::Var("amount".into()),
                        Expr::Lit(Literal::decimal(100 * DEC_SCALE)),
                    ],
                }),
                then_br: Box::new(Expr::Prim {
                    op: PrimOp::SubDec,
                    args: vec![
                        Expr::Prim {
                            op: PrimOp::MulDec,
                            args: vec![Expr::Var("amount".into()), Expr::Var("rate".into())],
                        },
                        Expr::Lit(Literal::decimal(DEC_SCALE + DEC_SCALE / 2)),
                    ],
                }),
                else_br: Box::new(Expr::Prim {
                    op: PrimOp::MulDec,
                    args: vec![Expr::Var("amount".into()), Expr::Var("rate".into())],
                }),
            },
        }],
        ..Program::default()
    };

    let plan = Plan::Sort {
        input: Box::new(Plan::Summarize {
            input: Box::new(Plan::GroupBy {
                input: Box::new(Plan::Derive {
                    input: Box::new(Plan::Filter {
                        input: Box::new(Plan::SourceExpr(Box::new(Expr::Var("sales".into())))),
                        pred: RowExpr::Prim {
                            op: PrimOp::Gt,
                            args: vec![RowExpr::Col("qty".into()), RowExpr::Lit(Literal::int(0))],
                        },
                    }),
                    items: vec![DeriveItem::ColExpr {
                        name: "tax".into(),
                        expr: Box::new(RowExpr::CallPure {
                            fn_name: "net_tax".into(),
                            args: vec![RowExpr::Col("amount".into()), RowExpr::Col("rate".into())],
                        }),
                    }],
                }),
                keys: vec!["region".into()],
            }),
            aggs: vec![
                AggItem {
                    name: "total_tax".into(),
                    op: AggOp::Sum,
                    arg: Some(RowExpr::Col("tax".into())),
                },
                AggItem {
                    name: "row_count".into(),
                    op: AggOp::Count,
                    arg: None,
                },
            ],
            distinct_key: None,
        }),
        keys: vec![("region".into(), SortDir::Asc)],
    };

    let seq_cfg = VmConfig {
        batch_size: BATCH_SIZE,
        parallel_threshold_rows: usize::MAX,
        max_threads: Some(1),
        optimize: true,
        pseudonymize_mode: PseudonymizeMode::CoreV01Fnv1a,
    };
    let par_cfg = VmConfig {
        batch_size: BATCH_SIZE,
        parallel_threshold_rows: 8_192,
        max_threads: None,
        optimize: true,
        pseudonymize_mode: PseudonymizeMode::CoreV01Fnv1a,
    };

    let t0 = Instant::now();
    let seq_out = eval_core_plan_batches(&prog, "sales", source_tbl.clone(), &plan, &seq_cfg)
        .map_err(|e| format!("seq 1M failed: {e:?}"))?;
    let seq_ms = t0.elapsed().as_secs_f64() * 1_000.0;

    let t1 = Instant::now();
    let par_out = eval_core_plan_batches(&prog, "sales", source_tbl, &plan, &par_cfg)
        .map_err(|e| format!("par 1M failed: {e:?}"))?;
    let par_ms = t1.elapsed().as_secs_f64() * 1_000.0;

    let seq_tv = seq_out.into_table_val();
    let par_tv = par_out.into_table_val();

    assert_eq!(seq_tv.cols, par_tv.cols, "1M output schema mismatch");
    assert_eq!(seq_tv.rows.len(), 16, "expected 16 regions");
    assert_eq!(seq_tv.rows.len(), par_tv.rows.len());

    let mut total_filtered_rows = 0i64;
    for (ri, (sr, pr)) in seq_tv.rows.iter().zip(&par_tv.rows).enumerate() {
        assert!(
            val_list_eq(&sr.cells, &pr.cells),
            "1M cell mismatch at group row {ri}: seq={:?} par={:?}",
            sr.cells,
            pr.cells
        );
        if let Some(Val::Int(cnt)) = sr.cells.get(2)
            && let Some(c) = cnt.to_i64()
        {
            total_filtered_rows += c;
        }
    }
    assert_eq!(
        total_filtered_rows, 900_000,
        "expected exactly 900,000 filtered rows (90% of 1M)"
    );

    let seq_mrows_s = (N_ROWS as f64) / (seq_ms * 1_000.0);
    let par_mrows_s = (N_ROWS as f64) / (par_ms * 1_000.0);
    eprintln!(
        "[vm_bench_smoke] 1M Filter+InlinedUDF+GroupBy+Summarize+Sort | seq: {seq_ms:.2} ms ({seq_mrows_s:.2} M rows/s) | par: {par_ms:.2} ms ({par_mrows_s:.2} M rows/s)"
    );
    Ok(())
}

struct EmptyHost;

impl RowEvalHost for EmptyHost {
    fn lookup_outer(&self, _name: &str) -> Option<Val> {
        None
    }

    fn lookup_const(&self, _name: &str) -> Option<Val> {
        None
    }

    fn call_pure_fallback(&self, fn_name: &str, _args: Vec<Val>) -> Result<Val, RowEvalErr> {
        Err(RowEvalErr::Failed(format!("unexpected call `{fn_name}`")))
    }
}

fn build_fact_100k_and_dim(n_rows: usize) -> (VmTable, VmTable) {
    let f_specs = vec![
        pub_col("id", ScalarTy::Int),
        pub_col("dept_id", ScalarTy::Int),
        pub_col("amount", ScalarTy::Decimal),
    ];
    let mut batches = Vec::with_capacity(n_rows.div_ceil(BATCH_SIZE));
    let mut rem = n_rows;
    let mut base = 0usize;
    while rem > 0 {
        let len = rem.min(BATCH_SIZE);
        let mut ids = Vec::with_capacity(len);
        let mut depts = Vec::with_capacity(len);
        let mut amts = Vec::with_capacity(len);
        for j in 0..len {
            let i = base + j;
            ids.push(i as i64);
            depts.push((i & 63) as i64);
            amts.push((((i % 500) as i128) + 1) * DEC_SCALE);
        }
        batches.push(Batch {
            cols: vec![
                Column {
                    spec: f_specs[0].clone(),
                    data: ColumnData::Int(ids),
                    validity: None,
                },
                Column {
                    spec: f_specs[1].clone(),
                    data: ColumnData::Int(depts),
                    validity: None,
                },
                Column {
                    spec: f_specs[2].clone(),
                    data: ColumnData::Decimal(amts),
                    validity: None,
                },
            ],
            len,
            selection: None,
            group_meta: None,
        });
        base += len;
        rem -= len;
    }
    let fact = VmTable {
        cols: f_specs,
        batches,
    };

    let d_specs = vec![
        pub_col("dept_id", ScalarTy::Int),
        pub_col("region", ScalarTy::Text),
    ];
    let mut d_ids = Vec::with_capacity(64);
    let mut r_offsets = Vec::with_capacity(65);
    let mut r_data = Vec::new();
    r_offsets.push(0);
    for d in 0..64i64 {
        d_ids.push(d);
        let reg = format!("reg_{:02}", d % 8);
        r_data.extend_from_slice(reg.as_bytes());
        r_offsets.push(r_data.len());
    }
    let dim = VmTable {
        cols: d_specs.clone(),
        batches: vec![Batch {
            cols: vec![
                Column {
                    spec: d_specs[0].clone(),
                    data: ColumnData::Int(d_ids),
                    validity: None,
                },
                Column {
                    spec: d_specs[1].clone(),
                    data: ColumnData::Text {
                        offsets: r_offsets,
                        data: r_data,
                    },
                    validity: None,
                },
            ],
            len: 64,
            selection: None,
            group_meta: None,
        }],
    };
    (fact, dim)
}

#[test]
fn bench_100k_rows_hash_join_agg_seq_vs_parallel() -> Result<(), String> {
    const N_ROWS: usize = 100_000;
    let (fact, dim) = build_fact_100k_and_dim(N_ROWS);

    let prog = Program::default();
    let compiled_aggs = vec![
        CompiledAgg {
            name: "total_amount".into(),
            op: AggOp::Sum,
            out_spec: ColSpec {
                name: "total_amount".into(),
                ty: ScalarTy::Decimal,
                tags: TagSet::empty(),
                bucketed: false,
                agg_kind: AggKind::Blending,
            },
            arg_prog: Some(compile_core_row_expr(&RowExpr::Col("amount".into()), &prog)),
        },
        CompiledAgg {
            name: "row_count".into(),
            op: AggOp::Count,
            out_spec: ColSpec {
                name: "row_count".into(),
                ty: ScalarTy::Int,
                tags: TagSet::empty(),
                bucketed: false,
                agg_kind: AggKind::Blending,
            },
            arg_prog: None,
        },
    ];
    let out_cols = vec![
        ColSpec {
            name: "region".into(),
            ty: ScalarTy::Text,
            tags: TagSet::empty(),
            bucketed: false,
            agg_kind: AggKind::GroupKey,
        },
        compiled_aggs[0].out_spec.clone(),
        compiled_aggs[1].out_spec.clone(),
    ];

    let run_pipeline = |cfg: &OpExecConfig, f: VmTable, d: VmTable| -> Result<VmTable, String> {
        let joined = op_hash_join(
            JoinKind::InnerManyToOne,
            f,
            d,
            &JoinOn::SameKeys(vec!["dept_id".into()]),
            &None,
            &TagSet::empty(),
            cfg,
        )
        .map_err(|e| format!("join: {e:?}"))?;
        let grouped = op_group_by(joined, &["region".into()], cfg.mode);
        let agg = op_hash_aggregate(
            grouped,
            &["region".into()],
            &compiled_aggs,
            None,
            out_cols.clone(),
            &EmptyHost,
            cfg,
        )
        .map_err(|e| format!("agg: {e:?}"))?;
        Ok(op_sort(agg, &[("region".into(), SortDir::Asc)], cfg))
    };

    let seq_cfg = OpExecConfig {
        batch_size: BATCH_SIZE,
        parallel_threshold_rows: usize::MAX,
        max_threads: Some(1),
        mode: VmMode::CoreV01,
        pseudonymize_mode: PseudonymizeMode::CoreV01Fnv1a,
    };
    let par_cfg = OpExecConfig {
        batch_size: BATCH_SIZE,
        parallel_threshold_rows: 8_192,
        max_threads: None,
        mode: VmMode::CoreV01,
        pseudonymize_mode: PseudonymizeMode::CoreV01Fnv1a,
    };

    let t0 = Instant::now();
    let seq_out = run_pipeline(&seq_cfg, fact.clone(), dim.clone())?;
    let seq_ms = t0.elapsed().as_secs_f64() * 1_000.0;

    let t1 = Instant::now();
    let par_out = run_pipeline(&par_cfg, fact, dim)?;
    let par_ms = t1.elapsed().as_secs_f64() * 1_000.0;

    let seq_tv = seq_out.into_table_val();
    let par_tv = par_out.into_table_val();

    assert_eq!(seq_tv.cols, par_tv.cols);
    assert_eq!(seq_tv.rows.len(), 8);
    let mut sum_cnt = 0i64;
    for (ri, (sr, pr)) in seq_tv.rows.iter().zip(&par_tv.rows).enumerate() {
        assert!(
            val_list_eq(&sr.cells, &pr.cells),
            "100k join+agg mismatch at row {ri}: seq={:?} par={:?}",
            sr.cells,
            pr.cells
        );
        if let Some(Val::Int(c)) = sr.cells.get(2)
            && let Some(n) = c.to_i64()
        {
            sum_cnt += n;
        }
    }
    assert_eq!(sum_cnt, N_ROWS as i64);

    let seq_mrows_s = (N_ROWS as f64) / (seq_ms * 1_000.0);
    let par_mrows_s = (N_ROWS as f64) / (par_ms * 1_000.0);
    eprintln!(
        "[vm_bench_smoke] 100k HashJoin+GroupBy+Summarize+Sort | seq: {seq_ms:.2} ms ({seq_mrows_s:.2} M rows/s) | par: {par_ms:.2} ms ({par_mrows_s:.2} M rows/s)"
    );
    Ok(())
}
