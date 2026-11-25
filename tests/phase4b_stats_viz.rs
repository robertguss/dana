#![forbid(unsafe_code)]

//! Phase 4B comprehensive test suite:
//! - Statistical accuracy (`Stats.corr` Pearson & tied-rank Spearman, `Stats.linear_regression` +
//!   `model.predict(x)`, exact Welch two-sample t-test, `Stats.chi_square` independence &
//!   goodness-of-fit, `Stats.outliers` `:zscore` & `:iqr` with privacy tag propagation)
//! - Relational `pivot_longer` (VM == reference evaluator parity, `Option` & numeric widening,
//!   privacy tag propagation, SQL pushdown barrier & `explain`)
//! - Privacy-safe dataset profiler (`table.profile()` & `console.print_profile` with full stats,
//!   8-bin Unicode sparklines for public columns and strict `[REDACTED:...]` for tagged columns)
//! - Zero-dependency SVG & Unicode terminal charts (all 5 `ChartKind`s, dynamic interpolated
//!   titles, OLS trendline overlay, XSS escaping, empty/single-row/constant NaN-free SVG)
//! - Self-contained HTML5 & GitHub-flavored Markdown reports + `out.write_html`,
//!   `out.write_markdown`, `out.write_svg` (privacy, `--allow-export`, confinement, `dry_run`)
//! - Live E2E executions of 4 real examples (`course-outcomes-stats.dana`,
//!   `saas-cohort-retention.dana`, `hipaa-clinic-outcomes.dana`, `log-anomaly-triage.dana`).

use std::collections::HashMap;
use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

use dana::base::{DiagCode, SourceMap, render_diagnostic};
use dana::check::{check_module, check_resolved, parse_policy, resolve_path};
use dana::core::bigint::BigInt;
use dana::core::syntax::{AggKind, BugKind, ChartKind, ColSpec, Float64, ScalarTy, TagSet};
use dana::db::{SqlDialect, SqlParam, open_connection};
use dana::ffi::GzipWriter;
use dana::formats::parquet::{ParquetCompression, write_parquet_table};
use dana::formats::time::parse_decimal_bigint_strict;
use dana::lower::lower_program;
use dana::oracle::value::{ChartVal, ReportVal, TableRow, TableVal, Val};
use dana::plan::{SplitPlan, split_exec_plan_pushdown};
use dana::runtime::{RunConfig, RunResult, run_exec_program, run_program_tests};
use dana::stats::profile::{profile_table, render_profile_terminal};
use dana::stats::{
    OutlierMethod, chi_square_contingency, chi_square_gof, chi_square_p_value,
    detect_outliers_table, linear_regression, pearson_corr, spearman_corr, welch_t_test,
};
use dana::syntax::parse_module;
use dana::viz::report::{render_html_report, render_markdown_report};
use dana::viz::svg::render_chart_svg;
use dana::viz::terminal::render_chart_terminal;
use dana::vm::{VmConfig, run_exec_program_vm, run_program_tests_vm};

type TestResult<T = ()> = Result<T, Box<dyn std::error::Error>>;

static TMP_SEQ: AtomicU64 = AtomicU64::new(1);

struct TempDir {
    path: PathBuf,
}

impl TempDir {
    fn new(prefix: &str) -> TestResult<Self> {
        let n = TMP_SEQ.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "dana_phase4b_{prefix}_{}_{}",
            std::process::id(),
            n
        ));
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

fn repo_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

fn col(name: &str, ty: ScalarTy, tags: &[&str]) -> ColSpec {
    ColSpec {
        name: name.to_string(),
        ty,
        tags: TagSet::of_list(tags.iter().map(|s| (*s).to_string()).collect()),
        bucketed: false,
        agg_kind: AggKind::Raw,
    }
}

fn compile_source(
    src: &str,
    policy: Option<dana::core::syntax::Policy>,
) -> Result<dana::runtime::ExecProgram, String> {
    let mut sm = SourceMap::new();
    let fid = sm.add_file("test.dana".to_string(), src.to_string());
    let ast = parse_module(fid, src).map_err(|d| render_diagnostic(&d, &sm))?;
    let checked = check_module(fid, ast, policy, &sm).map_err(|ds| {
        ds.iter()
            .map(|d| render_diagnostic(d, &sm))
            .collect::<String>()
    })?;
    let lowered = lower_program(checked).map_err(|d| render_diagnostic(&d, &sm))?;
    Ok(lowered.exec)
}

fn check_fails_with(src: &str, expected: DiagCode) -> TestResult {
    let mut sm = SourceMap::new();
    let fid = sm.add_file("neg.dana".to_string(), src.to_string());
    let ast = parse_module(fid, src).map_err(|d| render_diagnostic(&d, &sm))?;
    match check_module(fid, ast, None, &sm) {
        Ok(_) => Err("expected type/privacy error, but source compiled cleanly".into()),
        Err(diags) => {
            assert!(
                diags.iter().any(|d| d.code() == expected),
                "expected {expected:?}, got {:?}",
                diags
                    .iter()
                    .map(|d| (d.code(), d.message()))
                    .collect::<Vec<_>>()
            );
            Ok(())
        }
    }
}

fn compile_example(
    rel_path: &str,
    with_policy: bool,
) -> Result<dana::runtime::ExecProgram, String> {
    let root = repo_root();
    let mut sm = SourceMap::new();
    let policy = if with_policy {
        let ppath = root.join("examples/dana.policy");
        let psrc = fs::read_to_string(&ppath).map_err(|e| format!("read policy: {e}"))?;
        let pfid = sm.add_file(ppath.display().to_string(), psrc.clone());
        Some(parse_policy(pfid, &psrc).map_err(|d| render_diagnostic(&d, &sm))?)
    } else {
        None
    };
    let path = root.join(rel_path);
    let resolved = resolve_path(&path, policy, &mut sm).map_err(|ds| {
        ds.iter()
            .map(|d| render_diagnostic(d, &sm))
            .collect::<String>()
    })?;
    let checked = check_resolved(&resolved, &sm).map_err(|ds| {
        ds.iter()
            .map(|d| render_diagnostic(d, &sm))
            .collect::<String>()
    })?;
    let lowered = lower_program(checked).map_err(|d| render_diagnostic(&d, &sm))?;
    Ok(lowered.exec)
}

fn run_both_specs(src: &str) -> TestResult {
    let prog = compile_source(src, None).map_err(|e| format!("compile failed:\n{e}"))?;
    let cfg = RunConfig::default();
    let vm_small = VmConfig {
        batch_size: 2,
        parallel_threshold_rows: 2,
        max_threads: Some(2),
        optimize: true,
        ..VmConfig::default()
    };
    let oracle_res = run_program_tests(&prog, None, &cfg);
    let vm_res = run_program_tests_vm(&prog, None, &cfg, &vm_small);
    assert!(!oracle_res.is_empty(), "expected at least one test block");
    assert_eq!(oracle_res.len(), vm_res.len());
    for (o, v) in oracle_res.iter().zip(&vm_res) {
        assert!(o.passed, "oracle test `{}` failed: {:?}", o.name, o.message);
        assert!(v.passed, "vm test `{}` failed: {:?}", v.name, v.message);
    }
    Ok(())
}

fn assert_svg_well_formed(svg: &str, label: &str) {
    assert!(
        svg.starts_with("<svg xmlns=\"http://www.w3.org/2000/svg\""),
        "{label}: missing <svg> root: {svg}"
    );
    assert!(
        svg.trim_end().ends_with("</svg>"),
        "{label}: missing closing </svg>: {svg}"
    );
    assert!(!svg.contains("NaN"), "{label}: SVG contains NaN!\n{svg}");
    assert!(
        !svg.contains("inf\"") && !svg.contains("Infinity"),
        "{label}: SVG contains inf!\n{svg}"
    );
}

// ===========================================================================
// 1. Statistical Engine Numerical Accuracy Tests
// ===========================================================================

#[test]
fn stats_corr_pearson_and_spearman_tied_ranks() -> TestResult {
    // Exact tied-rank Spearman test:
    // x = [10, 20, 20, 30, 40] -> avg ranks [1.0, 2.5, 2.5, 4.0, 5.0]
    // y = [ 2,  5,  3,  5,  9] -> avg ranks [1.0, 3.5, 2.0, 3.5, 5.0]
    // Exact Spearman rho = 8.75 / 9.5 = 35/38 = 0.9210526315789473
    // (Note: naive untied formula 1 - 6*sum(d^2)/(n*(n^2-1)) gives 0.925, which is WRONG!)
    let xs = [10.0, 20.0, 20.0, 30.0, 40.0];
    let ys = [2.0, 5.0, 3.0, 5.0, 9.0];
    let rho = spearman_corr(&xs, &ys).ok_or("expected spearman_corr")?;
    let expected_rho = 35.0 / 38.0;
    assert!(
        (rho - expected_rho).abs() < 1e-12,
        "spearman tied ranks: got {rho}, expected {expected_rho}"
    );

    // Strictly monotonic non-linear: Spearman = 1.0, Pearson < 1.0
    let mx = [1.0, 2.0, 3.0, 4.0, 5.0];
    let my = [1.0, 8.0, 27.0, 64.0, 125.0];
    let r = pearson_corr(&mx, &my).ok_or("expected pearson_corr")?;
    let s = spearman_corr(&mx, &my).ok_or("expected spearman_corr")?;
    assert!((s - 1.0).abs() < 1e-12, "monotonic spearman={s}");
    let expected_cubic_r = 304.0 / 103_900.0_f64.sqrt();
    assert!(
        (r - expected_cubic_r).abs() < 1e-12,
        "cubic pearson={r}, expected={expected_cubic_r}"
    );

    // Language-level Dana test for both :pearson, default, and :spearman
    run_both_specs(
        r#"
module CorrTest
use Stats

test "pearson and spearman with tied ranks match exact references"
  t = table
    | x    | y   |
    | 10.0 | 2.0 |
    | 20.0 | 5.0 |
    | 20.0 | 3.0 |
    | 30.0 | 5.0 |
    | 40.0 | 9.0 |
  end
  rp_default = Stats.corr(t, x: .x, y: .y)
  rp_explicit = Stats.corr(t, x: .x, y: .y, method: :pearson)
  rs = Stats.corr(t, x: .x, y: .y, method: :spearman)
  assert (rp_default - rp_explicit).abs < 1e-12
  assert (rs - 0.921052631579).abs < 1e-9

  mono = table
    | x   | y     |
    | 1.0 | 1.0   |
    | 2.0 | 8.0   |
    | 3.0 | 27.0  |
    | 4.0 | 64.0  |
    | 5.0 | 125.0 |
  end
  assert (Stats.corr(mono, x: .x, y: .y, method: :spearman) - 1.0).abs < 1e-12
  assert (Stats.corr(mono, x: .x, y: .y, method: :pearson) - 0.9431175).abs < 0.00001
end
"#,
    )
}

#[test]
fn stats_linear_regression_predict_and_privacy() -> TestResult {
    let fit = linear_regression(&[1.0, 2.0, 3.0, 4.0], &[3.0, 5.0, 7.0, 9.0])
        .ok_or("expected linear_regression")?;
    assert!((fit.slope - 2.0).abs() < 1e-12);
    assert!((fit.intercept - 1.0).abs() < 1e-12);
    assert!((fit.r_squared - 1.0).abs() < 1e-12);
    assert!((fit.predict(10.0) - 21.0).abs() < 1e-12);

    // Language-level scalar + row-expression `model.predict(x)` accepting Int/Float/Decimal
    run_both_specs(
        r#"
module LinRegPredictTest
use Stats

test "model.predict supports Int, Float, Decimal and row derive"
  pts = table
    | x   | y   |
    | 1.0 | 3.0 |
    | 2.0 | 5.0 |
    | 3.0 | 7.0 |
    | 4.0 | 9.0 |
  end
  model = Stats.linear_regression(pts, x: .x, y: .y)
  assert (model.predict(10) - 21.0).abs < 1e-9
  assert (model.predict(2.5) - 6.0).abs < 1e-9
  var d: Decimal = 5.0
  assert (model.predict(d) - 11.0).abs < 1e-9

  scored = pts |> derive(y_hat: model.predict(.x))
  assert (scored.first!.y_hat - 3.0).abs < 1e-9
end
"#,
    )?;

    // Privacy: sensitive model OR sensitive x taints model.predict(x)
    check_fails_with(
        r##"
module PredictModelTaint
use Stats

schema SecretPts
  x: Float [pii]
  y: Float
end

fn main(t: Table(SecretPts), console: Console) : Int
  m = Stats.linear_regression(t, x: .x, y: .y)
  y_hat = m.predict(5.0)
  console.print("#{y_hat}")
  0
end
"##,
        DiagCode::PrivacyError,
    )?;

    check_fails_with(
        r##"
module PredictInputTaint
use Stats

schema PubPts
  x: Float
  y: Float
end

fn main(t: Table(PubPts), secret_x: Float [pii], console: Console) : Int
  m = Stats.linear_regression(t, x: .x, y: .y)
  y_hat = m.predict(secret_x)
  console.print("#{y_hat}")
  0
end
"##,
        DiagCode::PrivacyError,
    )
}

#[test]
fn stats_welch_t_test_accuracy() -> TestResult {
    // Case 1: Exact closed-form df = 2 Student-t:
    // a = [1, 3] (mean=2, var=2), b = [4, 6] (mean=5, var=2)
    // t = -3 / sqrt(2) = -2.1213203435596424, df = 2
    // exact p = 1 - 3 / sqrt(13) = 0.16794970566215628
    let r1 = welch_t_test(&[1.0, 3.0], &[4.0, 6.0]).ok_or("expected welch_t_test")?;
    let expected_t1 = -3.0 / 2.0_f64.sqrt();
    let expected_p1 = 1.0 - 3.0 / 13.0_f64.sqrt();
    assert!((r1.t_stat - expected_t1).abs() < 1e-10);
    assert!((r1.df - 2.0).abs() < 1e-10);
    assert!(
        (r1.p_value - expected_p1).abs() < 1e-9,
        "welch df=2 p={}, expected={expected_p1}",
        r1.p_value
    );

    // Case 2: Unequal sizes & unequal variances (exact numerical integration & SciPy reference):
    // a = [10, 12, 14, 16, 18], b = [20, 21, 22, 23]
    // t = -4.824506406770075, df = 5.520787746170678, two-tailed p = 0.0036685383123840924
    let r2 = welch_t_test(&[10.0, 12.0, 14.0, 16.0, 18.0], &[20.0, 21.0, 22.0, 23.0])
        .ok_or("expected welch_t_test")?;
    assert!((r2.t_stat - (-4.824_506_406_770_075)).abs() < 1e-9);
    assert!((r2.df - 5.520_787_746_170_678).abs() < 1e-9);
    assert!(
        (r2.p_value - 0.003_668_538_312_384).abs() < 1e-9,
        "welch unequal var p={}",
        r2.p_value
    );

    run_both_specs(
        r#"
module WelchTest
use Stats

test "Stats.t_test matches Welch t-statistic and p-value"
  a = table
    | v    |
    | 10.0 |
    | 12.0 |
    | 14.0 |
    | 16.0 |
    | 18.0 |
  end
  b = table
    | v    |
    | 20.0 |
    | 21.0 |
    | 22.0 |
    | 23.0 |
  end
  res = Stats.t_test(a, b, column: .v)
  assert (res.t_stat - (-4.8245064)).abs < 0.0001
  assert (res.p_value - 0.0036685).abs < 0.00001
end
"#,
    )
}

#[test]
fn stats_chi_square_independence_gof_and_privacy() -> TestResult {
    // Exact gamma-series & Lentz CF reference values:
    // df=1, chi2=3.841458820694124 -> p = 0.05
    assert!((chi_square_p_value(3.841_458_820_694_124, 1.0) - 0.05).abs() < 1e-7);
    // df=2, chi2=8.4 -> Q(1, 4.2) = exp(-4.2) (exercises Lentz CF: x=4.2 >= a+1=2)
    assert!((chi_square_p_value(8.4, 2.0) - (-4.2_f64).exp()).abs() < 1e-12);
    // df=4, chi2=6.8 -> Q(2, 3.4) = (1 + 3.4)*exp(-3.4)
    assert!((chi_square_p_value(6.8, 4.0) - 4.4 * (-3.4_f64).exp()).abs() < 1e-12);
    // df=10, chi2=3.9402991361190605 -> p = 0.95 (exercises series branch: x=1.97 < a+1=6)
    assert!((chi_square_p_value(3.940_299_136_119_060_5, 10.0) - 0.95).abs() < 1e-7);

    // 2x2 contingency table [[20, 30], [30, 20]] -> chi2 = 4.0, df = 1, p = 0.045500263896
    let c1 = chi_square_contingency(&[vec![20, 30], vec![30, 20]])
        .ok_or("expected chi_square_contingency")?;
    assert!((c1.stat - 4.0).abs() < 1e-12);
    assert!((c1.df - 1.0).abs() < 1e-12);
    assert!(
        (c1.p_value - 0.045_500_263_896).abs() < 1e-6,
        "2x2 p={}",
        c1.p_value
    );

    // GOF [30, 14, 6] vs [20, 20, 10] -> chi2 = 8.4, df = 2, p = exp(-4.2)
    let g1 =
        chi_square_gof(&[30.0, 14.0, 6.0], &[20.0, 20.0, 10.0]).ok_or("expected chi_square_gof")?;
    assert!((g1.stat - 8.4).abs() < 1e-12);
    assert!((g1.p_value - (-4.2_f64).exp()).abs() < 1e-12);

    // Language-level Dana tests for BOTH independence and GOF modes
    run_both_specs(
        r#"
module ChiSquareTest
use Stats

test "chi_square independence and goodness-of-fit"
  # 2x2 table: (A,Y)=4, (A,N)=1, (B,Y)=1, (B,N)=4 -> chi2 = 3.6, df = 1, p = 0.05777957
  ind = table
    | grp | out |
    | "A" | "Y" |
    | "A" | "Y" |
    | "A" | "Y" |
    | "A" | "Y" |
    | "A" | "N" |
    | "B" | "Y" |
    | "B" | "N" |
    | "B" | "N" |
    | "B" | "N" |
    | "B" | "N" |
  end
  r_ind = Stats.chi_square(ind, x: .grp, y: .out)
  assert (r_ind.stat - 3.6).abs < 0.0001
  assert (r_ind.p_value - 0.0577796).abs < 0.00001

  gof = table
    | obs  | exp  |
    | 30.0 | 20.0 |
    | 14.0 | 20.0 |
    | 6.0  | 10.0 |
  end
  r_gof = Stats.chi_square(gof, observed: .obs, expected: .exp)
  assert (r_gof.stat - 8.4).abs < 0.0001
  assert (r_gof.p_value - 0.0149956).abs < 0.00001
end
"#,
    )?;

    // Privacy: chi_square on sensitive column propagates tag and blocks Console output
    check_fails_with(
        r##"
module ChiSquarePrivacy
use Stats

schema Patient
  treatment: Text
  diagnosis: Text [health]
end

fn main(t: Table(Patient), console: Console) : Int
  res = Stats.chi_square(t, x: .treatment, y: .diagnosis)
  console.print("#{res.p_value}")
  0
end
"##,
        DiagCode::PrivacyError,
    )
}

#[test]
fn stats_outliers_zscore_iqr_and_privacy() -> TestResult {
    // Direct Rust API test (including nulls & degenerate constant table)
    let tv_const = TableVal {
        cols: vec![col("v", ScalarTy::Float, &[])],
        rows: vec![
            TableRow {
                cells: vec![Val::Float(Float64::from_f64(5.0))],
                group_meta: None,
            },
            TableRow {
                cells: vec![Val::Float(Float64::from_f64(5.0))],
                group_meta: None,
            },
            TableRow {
                cells: vec![Val::Float(Float64::from_f64(5.0))],
                group_meta: None,
            },
        ],
    };
    let out_const = detect_outliers_table(
        &tv_const,
        "v",
        OutlierMethod::ZScore,
        2.0,
        "outlier?",
        &TagSet::empty(),
    )?;
    assert!(
        out_const
            .rows
            .iter()
            .all(|r| matches!(r.cells[1], Val::Bool(false)))
    );

    // Dana language tests for :zscore and :iqr with nulls and custom flag column
    run_both_specs(
        r#"
module OutliersTest
use Stats

schema Reading
  id: Int
  val: Float?
end

test "zscore and iqr outlier flagging handle spikes and nulls"
  rows = table
    | id | val   |
    | 1  | 10.0  |
    | 2  | 10.5  |
    | 3  | 11.0  |
    | 4  | 9.5   |
    | 5  | 10.2  |
    | 6  | 9.8   |
    | 7  | 10.1  |
    | 8  | 10.3  |
    | 9  | 100.0 |
    | 10 | none  |
  end

  z = Stats.outliers(rows, column: .val, method: :zscore, threshold: 2.0)
  flagged_z = z |> where(.outlier?)
  assert flagged_z.count() == 1
  assert flagged_z.first!.id == 9

  # Null row must never be flagged
  null_row = z |> where(.id == 10)
  assert null_row.first!.outlier? == false

  iq = Stats.outliers(rows, column: .val, method: :iqr, threshold: 1.5, flag: "is_spike")
  flagged_iq = iq |> where(.is_spike)
  assert flagged_iq.count() == 1
  assert flagged_iq.first!.id == 9
end
"#,
    )?;

    // Privacy propagation: flagging outliers on [pii] column tags `outlier?` as [pii],
    // blocking console.print_table even after selecting only (.id, .outlier?).
    check_fails_with(
        r#"
module OutliersPrivacy
use Stats

schema Payroll
  id: Int
  salary: Float [pii]
end

fn main(t: Table(Payroll), console: Console) : Int
  flagged = Stats.outliers(t, column: .salary, method: :iqr)
    |> select(.id, .outlier?)
  console.print_table(flagged)
  0
end
"#,
        DiagCode::PrivacyError,
    )
}

// ===========================================================================
// 2. Relational `pivot_longer` Tests (VM == Oracle Parity, Widening, Privacy)
// ===========================================================================

#[test]
fn pivot_longer_parity_widening_privacy_and_pushdown() -> TestResult {
    run_both_specs(
        r#"
module PivotLongerTest

schema QuarterlySales
  region: Text
  q1: Int
  q2: Int?
  q3: Float
end

test "pivot_longer unpivots columns with Option + numeric widening identically on VM and oracle"
  wide = table
    | region | q1  | q2   | q3    |
    | "East" | 100 | 120  | 150.5 |
    | "West" | 80  | none | 95.0  |
  end

  long = wide
    |> pivot_longer(cols: [.q1, .q2, .q3], names_to: "quarter", values_to: "revenue")

  assert long.count() == 6
  east_q1 = long |> where(.region == "East" and .quarter == "q1")
  assert east_q1.count() == 1
  assert east_q1.first!.revenue == 100.0

  west_q2 = long |> where(.region == "West" and .quarter == "q2")
  assert west_q2.count() == 1
  assert west_q2.first!.revenue.none?

  west_q3 = long |> where(.region == "West" and .quarter == "q3")
  assert west_q3.count() == 1
  assert west_q3.first!.revenue == 95.0
end
"#,
    )?;

    // Privacy: melting a [pii] column taints `values_to`, blocking console.print_table!
    check_fails_with(
        r#"
module PivotLongerPrivacy

schema PatientScores
  dept: Text
  public_score: Float
  private_score: Float [pii]
end

fn main(t: Table(PatientScores), console: Console) : Int
  long = t |> pivot_longer(
    cols: [.public_score, .private_score],
    names_to: "metric",
    values_to: "score"
  )
  console.print_table(long)
  0
end
"#,
        DiagCode::PrivacyError,
    )?;

    // Verify `names_to` remains public when selecting only (.dept, .metric) after pivot_longer!
    compile_source(
        r#"
module PivotLongerNamesPublic

schema PatientScores
  dept: Text
  public_score: Float
  private_score: Float [pii]
end

fn print_names(t: Table(PatientScores), console: Console) : Int
  names_only = t
    |> pivot_longer(
      cols: [.public_score, .private_score],
      names_to: "metric",
      values_to: "score"
    )
    |> select(.dept, .metric)
  console.print_table(names_only)
  0
end
"#,
        None,
    )
    .map_err(|e| format!("names_to should stay public: {e}"))?;

    // Verify pushdown splitter treats PivotLonger as a local VM barrier cleanly.
    let db_prog = compile_source(
        r#"
module PivotLongerDb

schema MetricWide
  id: Int
  m1: Float
  m2: Float
end

fn main(db: ReadDB(Metrics)) : Int
  _ = db.table(MetricWide)
    |> where(.id > 0)
    |> pivot_longer(cols: [.m1, .m2], names_to: "m", values_to: "v")
  0
end
"#,
        None,
    )
    .map_err(|e| format!("compile db pivot_longer: {e}"))?;
    let main_fn = db_prog.find_fun("main").ok_or("missing main")?;
    if let dana::runtime::ExecExpr::LetE { bound, .. } = &main_fn.body
        && let dana::runtime::ExecExpr::Rel(plan) = bound.as_ref()
    {
        let split = split_exec_plan_pushdown(plan, &db_prog, "Metrics", SqlDialect::Sqlite, None);
        match split {
            SplitPlan::Hybrid {
                pushdown,
                local_suffix,
                ..
            } => {
                assert!(
                    pushdown.sql.contains("WHERE"),
                    "expected WHERE pushed to SQL: {}",
                    pushdown.sql
                );
                assert!(
                    matches!(local_suffix, dana::runtime::ExecPlan::PivotLonger { .. }),
                    "expected PivotLonger in local suffix, got {local_suffix:?}"
                );
            }
            other => {
                return Err(
                    format!("expected Hybrid pushdown for pivot_longer, got {other:?}").into(),
                );
            }
        }
    }

    Ok(())
}

// ===========================================================================
// 3. Privacy-Safe Dataset Profiler Tests
// ===========================================================================

#[test]
fn profile_public_stats_sparklines_and_strict_redaction() -> TestResult {
    let tv = TableVal {
        cols: vec![
            col("score", ScalarTy::Float, &[]),
            col("dept", ScalarTy::Text, &[]),
            col("ssn", ScalarTy::Text, &["pii"]),
            col("diagnosis", ScalarTy::Text, &["health"]),
            col("combined", ScalarTy::Int, &["pii", "health"]),
        ],
        rows: vec![
            TableRow {
                cells: vec![
                    Val::Float(Float64::from_f64(10.0)),
                    Val::Text("Math".into()),
                    Val::Text("111-11-1111".into()),
                    Val::Text("Asthma".into()),
                    Val::Int(BigInt::from(42)),
                ],
                group_meta: None,
            },
            TableRow {
                cells: vec![
                    Val::Float(Float64::from_f64(20.0)),
                    Val::Text("Math".into()),
                    Val::Text("222-22-2222".into()),
                    Val::Text("Diabetes".into()),
                    Val::Int(BigInt::from(99)),
                ],
                group_meta: None,
            },
            TableRow {
                cells: vec![
                    Val::Float(Float64::from_f64(30.0)),
                    Val::Text("Bio".into()),
                    Val::Text("333-33-3333".into()),
                    Val::Text("Asthma".into()),
                    Val::Int(BigInt::from(77)),
                ],
                group_meta: None,
            },
            TableRow {
                cells: vec![
                    Val::OptNone,
                    Val::Text("Math".into()),
                    Val::OptNone,
                    Val::Text("Flu".into()),
                    Val::Int(BigInt::from(88)),
                ],
                group_meta: None,
            },
        ],
    };

    let prof = profile_table(&tv, &TagSet::empty(), &[]);
    assert_eq!(prof.cols.len(), 5);

    // Public numeric column `score`
    let c_score = &prof.cols[0];
    assert!(!c_score.is_redacted());
    assert_eq!(c_score.row_count, 4);
    assert_eq!(c_score.null_count, 1);
    assert!((c_score.null_pct.to_f64() - 25.0).abs() < 1e-9);
    assert_eq!(c_score.distinct_count, 3);
    assert!((c_score.mean.ok_or("mean")?.to_f64() - 20.0).abs() < 1e-9);
    assert!((c_score.stddev.ok_or("stddev")?.to_f64() - 10.0).abs() < 1e-9);
    assert!((c_score.min.ok_or("min")?.to_f64() - 10.0).abs() < 1e-9);
    assert!((c_score.p25.ok_or("p25")?.to_f64() - 15.0).abs() < 1e-9);
    assert!((c_score.median.ok_or("median")?.to_f64() - 20.0).abs() < 1e-9);
    assert!((c_score.p75.ok_or("p75")?.to_f64() - 25.0).abs() < 1e-9);
    assert!((c_score.max.ok_or("max")?.to_f64() - 30.0).abs() < 1e-9);
    let spark = c_score.sparkline.as_deref().ok_or("expected sparkline")?;
    assert_eq!(spark.chars().count(), 8);
    assert!(spark.chars().all(|ch| "▁▂▃▄▅▆▇█".contains(ch)));

    // Public categorical column `dept`
    let c_dept = &prof.cols[1];
    assert!(!c_dept.is_redacted());
    assert_eq!(
        c_dept.top_values,
        vec![("Math".to_string(), 3), ("Bio".to_string(), 1)]
    );

    // Strictly redacted columns: ssn [pii], diagnosis [health], combined [health,pii]
    for (col_idx, expected_marker) in [
        (2, "[REDACTED:pii]"),
        (3, "[REDACTED:health]"),
        (4, "[REDACTED:health,pii]"),
    ] {
        let c = &prof.cols[col_idx];
        assert!(c.is_redacted());
        assert_eq!(c.min_display.as_deref(), Some(expected_marker));
        assert_eq!(c.max_display.as_deref(), Some(expected_marker));
        assert!(c.mean.is_none());
        assert!(c.stddev.is_none());
        assert!(c.min.is_none());
        assert!(c.p25.is_none());
        assert!(c.median.is_none());
        assert!(c.p75.is_none());
        assert!(c.max.is_none());
        assert!(c.sparkline.is_none());
        assert!(c.top_values.is_empty());
    }

    let term = render_profile_terminal(&prof);
    assert!(term.contains("[REDACTED:pii]"));
    assert!(term.contains("[REDACTED:health]"));
    assert!(term.contains("[REDACTED:health,pii]"));
    assert!(term.contains(spark));
    for secret in ["111-11-1111", "222-22-2222", "Asthma", "Diabetes", "Flu"] {
        assert!(
            !term.contains(secret),
            "secret `{secret}` leaked in profile:\n{term}"
        );
    }

    // Table-level `row_tags` redacts EVERY column (even public ones!)
    let row_redacted = profile_table(&tv, &TagSet::of_list(vec!["pii".to_string()]), &[]);
    assert!(
        row_redacted
            .cols
            .iter()
            .all(|c| c.is_redacted() && c.mean.is_none() && c.sparkline.is_none())
    );

    // Language-level: `console.print_profile(rows.profile())` works cleanly on column-tagged table
    // and redacts PII values, while row-tagged filtered table STILL fails static PrivacyError!
    let prog = compile_source(
        r#"
module ProfilePrintSafe

schema Patient
  dept: Text
  ssn: Text [pii]
  age: Int [health]
end

fn show_patient_profile(rows: Table(Patient), console: Console) : Int
  console.print_profile(rows.profile())
  0
end

fn main(console: Console) : Int
  rows = table
    | dept         | ssn           | age |
    | "Cardiology" | "123-45-6789" | 54  |
    | "Cardiology" | "987-65-4321" | 61  |
  end
  show_patient_profile(rows, console)
end
"#,
        None,
    )
    .map_err(|e| format!("compile ProfilePrintSafe: {e}"))?;
    match run_exec_program(&prog, &RunConfig::default()) {
        RunResult::Ok {
            exit_code, stdout, ..
        } => {
            assert_eq!(exit_code, 0);
            let joined = stdout.join("\n");
            assert!(joined.contains("Cardiology"), "stdout={joined}");
            assert!(joined.contains("[REDACTED:pii]"), "stdout={joined}");
            assert!(joined.contains("[REDACTED:health]"), "stdout={joined}");
            assert!(!joined.contains("123-45-6789"), "PII leaked: {joined}");
            assert!(!joined.contains("987-65-4321"), "PII leaked: {joined}");
        }
        other => return Err(format!("unexpected run result: {other:?}").into()),
    }

    check_fails_with(
        r#"
module ProfileRowTagsBlocked

schema Patient
  dept: Text
  ssn: Text [pii]
end

fn main(p: Table(Patient), console: Console) : Int
  filtered = p |> where(.ssn == "123")
  console.print_profile(filtered.profile())
  0
end
"#,
        DiagCode::PrivacyError,
    )
}

// ===========================================================================
// 4. Zero-Dependency SVG, Terminal Charts, XSS & Edge Cases, HTML/MD Exports
// ===========================================================================

#[test]
fn viz_all_five_chart_kinds_svg_terminal_xss_and_degenerate_inputs() -> TestResult {
    // 1. Grouped Bar
    let bar = ChartVal {
        kind: ChartKind::Bar,
        title: "Sales <script>alert(1)</script> & \"Quotes\"".to_string(),
        col_names: vec!["dept".into(), "rate".into(), "band".into()],
        series: vec![
            vec![
                Val::Text("A & B".into()),
                Val::Text("A & B".into()),
                Val::Text("C".into()),
            ],
            vec![
                Val::Float(Float64::from_f64(0.12)),
                Val::Float(Float64::from_f64(0.25)),
                Val::Float(Float64::from_f64(0.18)),
            ],
            vec![
                Val::Text("18-44".into()),
                Val::Text("45-64".into()),
                Val::Text("18-44".into()),
            ],
        ],
        x_col: Some("dept".into()),
        y_col: Some("rate".into()),
        color_col: Some("band".into()),
        ..ChartVal::default()
    };
    let bar_svg = render_chart_svg(&bar);
    assert_svg_well_formed(&bar_svg, "bar");
    assert!(bar_svg.contains("<rect "));
    assert!(bar_svg.contains("&lt;script&gt;alert(1)&lt;/script&gt;"));
    assert!(!bar_svg.contains("<script>"));
    let bar_term = render_chart_terminal(&bar);
    assert!(bar_term.contains("[Bar]") && bar_term.contains("A & B"));

    // 2. Multi-series Line
    let line = ChartVal {
        kind: ChartKind::Line,
        title: "Latency Trend".to_string(),
        col_names: vec!["t".into(), "ms".into(), "ep".into()],
        series: vec![
            vec![
                Val::Int(1.into()),
                Val::Int(2.into()),
                Val::Int(1.into()),
                Val::Int(2.into()),
            ],
            vec![
                Val::Float(Float64::from_f64(20.0)),
                Val::Float(Float64::from_f64(45.0)),
                Val::Float(Float64::from_f64(15.0)),
                Val::Float(Float64::from_f64(30.0)),
            ],
            vec![
                Val::Text("/pay".into()),
                Val::Text("/pay".into()),
                Val::Text("/search".into()),
                Val::Text("/search".into()),
            ],
        ],
        x_col: Some("t".into()),
        y_col: Some("ms".into()),
        color_col: Some("ep".into()),
        ..ChartVal::default()
    };
    let line_svg = render_chart_svg(&line);
    assert_svg_well_formed(&line_svg, "line");
    assert!(line_svg.contains("<polyline "));
    assert!(line_svg.contains("/pay") && line_svg.contains("/search"));
    assert!(render_chart_terminal(&line).contains("[Line]"));

    // 3. Scatter with OLS Trendline
    let scatter = ChartVal {
        kind: ChartKind::Scatter,
        title: "Hours vs Completion".to_string(),
        col_names: vec!["hours".into(), "rate".into(), "mod".into()],
        series: vec![
            vec![
                Val::Float(Float64::from_f64(2.0)),
                Val::Float(Float64::from_f64(4.0)),
                Val::Float(Float64::from_f64(6.0)),
                Val::Float(Float64::from_f64(8.0)),
            ],
            vec![
                Val::Float(Float64::from_f64(0.60)),
                Val::Float(Float64::from_f64(0.70)),
                Val::Float(Float64::from_f64(0.80)),
                Val::Float(Float64::from_f64(0.90)),
            ],
            vec![
                Val::Text("online".into()),
                Val::Text("online".into()),
                Val::Text("in-person".into()),
                Val::Text("in-person".into()),
            ],
        ],
        x_col: Some("hours".into()),
        y_col: Some("rate".into()),
        color_col: Some("mod".into()),
        trendline: Some((0.05, 0.50, 1.0)),
        ..ChartVal::default()
    };
    let scatter_svg = render_chart_svg(&scatter);
    assert_svg_well_formed(&scatter_svg, "scatter");
    assert!(scatter_svg.contains("<circle "));
    assert!(scatter_svg.contains("class=\"trendline\""));
    assert!(scatter_svg.contains("R² = 1.000"));
    assert!(render_chart_terminal(&scatter).contains("OLS:"));

    // 4. Histogram (explicit bins + constant data)
    let hist = ChartVal {
        kind: ChartKind::Histogram,
        title: "Score Distribution".to_string(),
        col_names: vec!["score".into()],
        series: vec![vec![
            Val::Float(Float64::from_f64(10.0)),
            Val::Float(Float64::from_f64(15.0)),
            Val::Float(Float64::from_f64(22.0)),
            Val::Float(Float64::from_f64(35.0)),
            Val::Float(Float64::from_f64(48.0)),
            Val::Float(Float64::from_f64(50.0)),
        ]],
        x_col: Some("score".into()),
        bins: Some(4),
        ..ChartVal::default()
    };
    let hist_svg = render_chart_svg(&hist);
    assert_svg_well_formed(&hist_svg, "histogram");
    assert!(hist_svg.contains("<rect "));
    assert!(render_chart_terminal(&hist).contains("[Histogram]"));

    // 5. Heatmap
    let heat = ChartVal {
        kind: ChartKind::Heatmap,
        title: "Retention Grid".to_string(),
        col_names: vec!["m".into(), "cohort".into(), "pct".into()],
        series: vec![
            vec![
                Val::Int(0.into()),
                Val::Int(1.into()),
                Val::Int(0.into()),
                Val::Int(1.into()),
            ],
            vec![
                Val::Text("2026-01".into()),
                Val::Text("2026-01".into()),
                Val::Text("2026-02".into()),
                Val::Text("2026-02".into()),
            ],
            vec![
                Val::Float(Float64::from_f64(100.0)),
                Val::Float(Float64::from_f64(75.0)),
                Val::Float(Float64::from_f64(100.0)),
                Val::Float(Float64::from_f64(82.0)),
            ],
        ],
        x_col: Some("m".into()),
        y_col: Some("cohort".into()),
        value_col: Some("pct".into()),
        ..ChartVal::default()
    };
    let heat_svg = render_chart_svg(&heat);
    assert_svg_well_formed(&heat_svg, "heatmap");
    assert!(heat_svg.contains("100") && heat_svg.contains("75") && heat_svg.contains("82"));
    assert!(render_chart_terminal(&heat).contains("[Heatmap]"));

    // Degenerate inputs (empty, single-row, constant-value) across ALL 5 ChartKinds -> zero NaNs!
    for kind in [
        ChartKind::Bar,
        ChartKind::Line,
        ChartKind::Scatter,
        ChartKind::Histogram,
        ChartKind::Heatmap,
    ] {
        let empty = ChartVal {
            kind,
            title: "Empty".to_string(),
            ..ChartVal::default()
        };
        assert_svg_well_formed(&render_chart_svg(&empty), "empty");

        let constant = ChartVal {
            kind,
            title: "Constant".to_string(),
            col_names: vec!["x".into(), "y".into(), "v".into()],
            series: vec![
                vec![
                    Val::Float(Float64::from_f64(5.0)),
                    Val::Float(Float64::from_f64(5.0)),
                ],
                vec![
                    Val::Float(Float64::from_f64(5.0)),
                    Val::Float(Float64::from_f64(5.0)),
                ],
                vec![
                    Val::Float(Float64::from_f64(5.0)),
                    Val::Float(Float64::from_f64(5.0)),
                ],
            ],
            x_col: Some("x".into()),
            y_col: Some("y".into()),
            value_col: Some("v".into()),
            trendline: Some((0.0, 5.0, 1.0)),
            ..ChartVal::default()
        };
        assert_svg_well_formed(&render_chart_svg(&constant), "constant");
    }

    // HTML & Markdown report XSS & self-contained verification
    let rep = ReportVal {
        title: "Audit <script>evil()</script>".to_string(),
        summaries: vec!["Summary with <b>tags</b> & quotes \"ok\"".to_string()],
        charts: vec![scatter],
        tables: vec![(
            vec!["col|a".into(), "val".into()],
            vec![vec![Val::Text("<img src=x>".into()), Val::Int(42.into())]],
        )],
    };
    let html = render_html_report(&rep);
    assert!(html.contains("<!doctype html>"));
    assert!(!html.contains("<script>"));
    assert!(!html.contains("<img src=x>"));
    assert!(html.contains("&lt;script&gt;evil()&lt;/script&gt;"));
    assert!(html.contains("<svg xmlns=\"http://www.w3.org/2000/svg\""));
    let html_no_xmlns = html.replace("http://www.w3.org/2000/svg", "");
    assert!(
        !html_no_xmlns.contains("https://") && !html_no_xmlns.contains("http://"),
        "HTML report must contain zero external URLs"
    );

    let md = render_markdown_report(&rep);
    assert!(md.contains("# Audit <script>evil()</script>"));
    assert!(md.contains("| col\\|a | val |"));
    assert!(md.contains("OLS Trendline:"));
    Ok(())
}

#[test]
fn write_html_markdown_svg_exports_privacy_confinement_and_dry_run() -> TestResult {
    let tmp = TempDir::new("exports")?;
    let src = r##"
module ExportSuite
use Stats

fn main(out: WriteFiles("reports/"), console: Console) : Int
  pts = table
    | x   | y    | grp |
    | 1.0 | 2.0  | "A" |
    | 2.0 | 4.0  | "A" |
    | 3.0 | 6.0  | "B" |
    | 4.0 | 8.0  | "B" |
  end
  r = Stats.corr(pts, x: .x, y: .y)
  model = Stats.linear_regression(pts, x: .x, y: .y)

  chart = pts
    |> chart_scatter(
         x: .x,
         y: .y,
         color: .grp,
         trendline: model,
         title: "Dynamic Title (r = #{r.round(3)})"
       )

  hist = pts |> chart_histogram(x: .y, bins: 3, title: "Y Histogram")

  report = Report.new("Export Verification")
    |> add_summary("Slope = #{model.slope.round(2)}")
    |> add_chart(chart)
    |> add_chart(hist)
    |> add_table(pts)

  try out.write_html("out.html", report)
  try out.write_markdown("out.md", report)
  try out.write_svg("scatter.svg", chart)
  console.print("done")
  0
end
"##;
    let prog = compile_source(src, None).map_err(|e| format!("compile ExportSuite: {e}"))?;

    // Dry-run must NOT write files
    let dry_cfg = RunConfig {
        work_dir: Some(tmp.path().to_path_buf()),
        live_io: true,
        dry_run: true,
        ..RunConfig::default()
    };
    match run_exec_program(&prog, &dry_cfg) {
        RunResult::Ok {
            exit_code, stdout, ..
        } => {
            assert_eq!(exit_code, 0);
            let joined = stdout.join("\n");
            assert!(joined.contains("[DRY-RUN]"), "stdout={joined}");
            assert!(!tmp.path().join("reports/out.html").exists());
            assert!(!tmp.path().join("reports/out.md").exists());
            assert!(!tmp.path().join("reports/scatter.svg").exists());
        }
        other => return Err(format!("dry_run failed: {other:?}").into()),
    }

    // Live write
    let live_cfg = RunConfig {
        work_dir: Some(tmp.path().to_path_buf()),
        live_io: true,
        ..RunConfig::default()
    };
    match run_exec_program_vm(&prog, &live_cfg, &VmConfig::default()) {
        RunResult::Ok { exit_code, .. } => assert_eq!(exit_code, 0),
        other => return Err(format!("live export failed: {other:?}").into()),
    }
    let html = fs::read_to_string(tmp.path().join("reports/out.html"))?;
    let md = fs::read_to_string(tmp.path().join("reports/out.md"))?;
    let svg = fs::read_to_string(tmp.path().join("reports/scatter.svg"))?;

    assert!(html.contains("Dynamic Title (r = 1)"));
    assert!(html.contains("class=\"trendline\""));
    assert!(html.contains("Y Histogram"));
    assert!(md.contains("# Export Verification"));
    assert!(md.contains("Dynamic Title (r = 1)"));
    assert!(md.contains("| x | y | grp |"));
    assert_svg_well_formed(&svg, "scatter.svg");
    assert!(svg.contains("Dynamic Title (r = 1)"));

    // Privacy check: write_svg & write_markdown MUST reject [pii] charts/reports to public WriteFiles
    check_fails_with(
        r#"
module RejectSvgPii
schema Sec
  x: Float [pii]
  y: Float
end
fn main(t: Table(Sec), out: WriteFiles("reports/")) : Int
  c = t |> chart_scatter(x: .x, y: .y, title: "Secret")
  try out.write_svg("leak.svg", c)
  0
end
"#,
        DiagCode::PrivacyError,
    )?;

    check_fails_with(
        r#"
module RejectMdPii
schema Sec
  x: Float [pii]
  y: Float
end
fn main(t: Table(Sec), out: WriteFiles("reports/")) : Int
  c = t |> chart_scatter(x: .x, y: .y, title: "Secret")
  rep = Report.new("Leak") |> add_chart(c)
  try out.write_markdown("leak.md", rep)
  0
end
"#,
        DiagCode::PrivacyError,
    )?;

    // Confinement check: path traversal rejected statically
    check_fails_with(
        r#"
module RejectTraversal
fn main(out: WriteFiles("reports/")) : Int
  rep = Report.new("Ok")
  try out.write_markdown("../escape.md", rep)
  0
end
"#,
        DiagCode::CapabilityError,
    )?;

    // Runtime --allow-export gate enforcement for write_svg with [pii]
    let gated_prog = compile_source(
        r#"
module GatedSvg
schema Sec
  x: Float [pii]
  y: Float
end
fn main(out: WriteFiles("reports/", allows: [pii])) : Int
  t = table
    | x   | y   |
    | 1.0 | 2.0 |
    | 2.0 | 4.0 |
  end
  c = t |> chart_scatter(x: .x, y: .y, title: "Allowed")
  try out.write_svg("ok.svg", c)
  0
end
"#,
        None,
    )
    .map_err(|e| format!("compile GatedSvg: {e}"))?;
    let denied_cfg = RunConfig {
        work_dir: Some(tmp.path().to_path_buf()),
        live_io: true,
        allow_export: TagSet::empty(),
        ..RunConfig::default()
    };
    match run_exec_program(&gated_prog, &denied_cfg) {
        RunResult::Stopped { bug, .. } => assert_eq!(bug.kind, BugKind::ExportGateDenied),
        other => return Err(format!("expected ExportGateDenied, got {other:?}").into()),
    }

    Ok(())
}

// ===========================================================================
// 5. Live E2E Executions of 4 Real Examples
// ===========================================================================

#[test]
fn e2e_live_course_outcomes_stats_with_parquet() -> TestResult {
    let tmp = TempDir::new("course_outcomes")?;
    let data_dir = tmp.path().join("data");
    fs::create_dir_all(&data_dir)?;

    let tv = TableVal {
        cols: vec![
            col("section_id", ScalarTy::Text, &[]),
            col("modality", ScalarTy::Text, &[]),
            col("enrolled", ScalarTy::Int, &[]),
            col(
                "avg_weekly_hours",
                ScalarTy::Option(Box::new(ScalarTy::Float)),
                &[],
            ),
            col("completion_rate", ScalarTy::Float, &[]),
        ],
        rows: vec![
            ("S1", "online", 24, Some(2.0), 0.62),
            ("S2", "online", 22, Some(3.0), 0.68),
            ("S3", "online", 20, Some(4.0), 0.72),
            ("S4", "online", 25, Some(5.0), 0.76),
            ("S5", "in-person", 18, Some(6.0), 0.82),
            ("S6", "in-person", 21, Some(7.0), 0.87),
            ("S7", "in-person", 23, Some(8.0), 0.91),
            ("S8", "in-person", 19, Some(9.0), 0.95),
            ("S9", "online", 17, Some(1.5), 0.12), // clear outlier!
            ("S10", "online", 15, None, 0.75),     // missing avg_weekly_hours
        ]
        .into_iter()
        .map(|(sid, m, enr, hrs, rate)| TableRow {
            cells: vec![
                Val::Text(sid.to_string()),
                Val::Text(m.to_string()),
                Val::Int(BigInt::from(enr)),
                match hrs {
                    Some(h) => Val::OptSome(Box::new(Val::Float(Float64::from_f64(h)))),
                    None => Val::OptNone,
                },
                Val::Float(Float64::from_f64(rate)),
            ],
            group_meta: None,
        })
        .collect(),
    };
    write_parquet_table(
        &data_dir.join("section-outcomes.parquet"),
        &tv,
        ParquetCompression::Zstd,
    )?;

    let prog = compile_example("examples/course-outcomes-stats.dana", true)
        .map_err(|e| format!("compile course-outcomes-stats: {e}"))?;
    let cfg = RunConfig {
        work_dir: Some(tmp.path().to_path_buf()),
        live_io: true,
        ..RunConfig::default()
    };

    for (engine, res) in [
        ("oracle", run_exec_program(&prog, &cfg)),
        ("vm", run_exec_program_vm(&prog, &cfg, &VmConfig::default())),
    ] {
        match res {
            RunResult::Ok {
                exit_code, stdout, ..
            } => {
                assert_eq!(exit_code, 0, "{engine} exit_code");
                let out_s = stdout.join("\n");
                assert!(
                    out_s.contains("Dataset Profile"),
                    "{engine} missing profile:\n{out_s}"
                );
                assert!(
                    out_s.chars().any(|c| "▁▂▃▄▅▆▇█".contains(c)),
                    "{engine} missing sparkline:\n{out_s}"
                );
                assert!(out_s.contains("Pearson r="), "{engine} stdout:\n{out_s}");
                assert!(!out_s.contains("NaN"), "{engine} stdout NaN:\n{out_s}");
            }
            other => return Err(format!("{engine} failed: {other:?}").into()),
        }
    }

    let html = fs::read_to_string(tmp.path().join("reports/course-outcomes.html"))?;
    assert!(html.contains("Course Section Outcomes Study"));
    assert!(html.contains("Weekly Engagement vs. Section Completion (r = "));
    assert!(html.contains("<svg xmlns=\"http://www.w3.org/2000/svg\""));
    assert!(html.contains("class=\"trendline\""));
    assert!(
        html.contains("S9"),
        "expected outlier section S9 in HTML table"
    );
    assert!(!html.contains("NaN"), "HTML report contains NaN");
    Ok(())
}

#[test]
fn e2e_live_saas_cohort_retention_with_sqlite() -> TestResult {
    let tmp = TempDir::new("saas_cohort")?;
    let db_path = tmp.path().join("billing.sqlite");
    let db_uri = format!("sqlite://{}", db_path.display());

    {
        let mut conn = open_connection(&db_uri)?;
        conn.execute(
            r#"CREATE TABLE "Subscription" (
                "account_id" INTEGER NOT NULL,
                "plan" TEXT NOT NULL,
                "signup_date" TEXT NOT NULL
            )"#,
            &[],
        )?;
        conn.execute(
            r#"CREATE TABLE "MonthlyInvoice" (
                "account_id" INTEGER NOT NULL,
                "bill_month" TEXT NOT NULL,
                "mrr" TEXT NOT NULL,
                "paid?" INTEGER NOT NULL
            )"#,
            &[],
        )?;

        for (aid, plan, dt) in [
            (1, "pro", "2026-01-05"),
            (2, "pro", "2026-01-14"),
            (3, "team", "2026-02-03"),
            (4, "team", "2026-02-20"),
            (5, "pro", "2026-03-08"),
        ] {
            conn.execute(
                r#"INSERT INTO "Subscription" ("account_id", "plan", "signup_date") VALUES (?1, ?2, ?3)"#,
                &[
                    SqlParam::Int(aid),
                    SqlParam::Text(plan.to_string()),
                    SqlParam::Text(dt.to_string()),
                ],
            )?;
        }

        for (aid, bm, mrr, paid) in [
            (1, "2026-01-01", "100.00", true),
            (2, "2026-01-01", "100.00", true),
            (1, "2026-02-01", "100.00", true),
            (2, "2026-02-01", "100.00", false),
            (1, "2026-03-01", "100.00", true),
            (3, "2026-02-01", "200.00", true),
            (4, "2026-02-01", "200.00", true),
            (3, "2026-03-01", "200.00", true),
            (4, "2026-03-01", "200.00", true),
            (5, "2026-03-01", "150.00", true),
        ] {
            conn.execute(
                r#"INSERT INTO "MonthlyInvoice" ("account_id", "bill_month", "mrr", "paid?") VALUES (?1, ?2, ?3, ?4)"#,
                &[
                    SqlParam::Int(aid),
                    SqlParam::Text(bm.to_string()),
                    SqlParam::Decimal(parse_decimal_bigint_strict(mrr)?),
                    SqlParam::Bool(paid),
                ],
            )?;
        }
    }

    let prog = compile_example("examples/saas-cohort-retention.dana", true)
        .map_err(|e| format!("compile saas-cohort-retention: {e}"))?;
    let mut db_bindings = HashMap::new();
    db_bindings.insert("Billing".to_string(), db_uri);
    let cfg = RunConfig {
        work_dir: Some(tmp.path().to_path_buf()),
        db_bindings,
        live_io: true,
        ..RunConfig::default()
    };

    for (engine, res) in [
        ("oracle", run_exec_program(&prog, &cfg)),
        ("vm", run_exec_program_vm(&prog, &cfg, &VmConfig::default())),
    ] {
        match res {
            RunResult::Ok {
                exit_code, stdout, ..
            } => {
                assert_eq!(exit_code, 0, "{engine} exit_code");
                let out_s = stdout.join("\n");
                assert!(
                    out_s.contains("2026-01-01") && out_s.contains("M0"),
                    "{engine} stdout:\n{out_s}"
                );
            }
            other => return Err(format!("{engine} failed: {other:?}").into()),
        }
    }

    let html = fs::read_to_string(tmp.path().join("reports/saas-retention.html"))?;
    assert!(html.contains("SaaS Cohort Retention &amp; MRR"));
    assert!(html.contains("Monthly Account Retention (%)"));
    assert!(html.contains("3-Month Rolling Cohort LTV"));
    let svg_count = html
        .matches("<svg xmlns=\"http://www.w3.org/2000/svg\"")
        .count();
    assert_eq!(
        svg_count, 2,
        "expected heatmap + rolling line SVGs, got {svg_count}"
    );
    assert!(
        html.contains("<polyline "),
        "expected rolling-mean line polyline"
    );
    assert!(!html.contains("NaN"));
    Ok(())
}

#[test]
fn e2e_live_hipaa_clinic_outcomes_with_sqlite() -> TestResult {
    let tmp = TempDir::new("hipaa_clinic")?;
    let db_path = tmp.path().join("clinic.sqlite");
    let db_uri = format!("sqlite://{}", db_path.display());

    {
        let mut conn = open_connection(&db_uri)?;
        conn.execute(
            r#"CREATE TABLE "PatientEncounter" (
                "patient_id" INTEGER NOT NULL,
                "full_name" TEXT NOT NULL,
                "department" TEXT NOT NULL,
                "age_years" INTEGER NOT NULL,
                "length_of_stay_days" TEXT NOT NULL,
                "readmitted_30d?" INTEGER NOT NULL
            )"#,
            &[],
        )?;

        // 11 distinct Cardiology patients in 45-64 (SURVIVES k >= 10)
        for i in 1..=11i64 {
            conn.execute(
                r#"INSERT INTO "PatientEncounter" ("patient_id", "full_name", "department", "age_years", "length_of_stay_days", "readmitted_30d?") VALUES (?1, ?2, ?3, ?4, ?5, ?6)"#,
                &[
                    SqlParam::Int(i),
                    SqlParam::Text(format!("SecretCardioPatient_{i}")),
                    SqlParam::Text("Cardiology".to_string()),
                    SqlParam::Int(50 + (i % 10)),
                    SqlParam::Decimal(parse_decimal_bigint_strict("4.0")?),
                    SqlParam::Bool(i % 4 == 0),
                ],
            )?;
        }
        // 10 distinct Oncology patients in 18-44 (SURVIVES k >= 10)
        for i in 101..=110i64 {
            conn.execute(
                r#"INSERT INTO "PatientEncounter" ("patient_id", "full_name", "department", "age_years", "length_of_stay_days", "readmitted_30d?") VALUES (?1, ?2, ?3, ?4, ?5, ?6)"#,
                &[
                    SqlParam::Int(i),
                    SqlParam::Text(format!("SecretOncoPatient_{i}")),
                    SqlParam::Text("Oncology".to_string()),
                    SqlParam::Int(28 + (i % 10)),
                    SqlParam::Decimal(parse_decimal_bigint_strict("6.5")?),
                    SqlParam::Bool(i % 2 == 0),
                ],
            )?;
        }
        // 3 distinct Genetics patients in 18-44 (SUPPRESSED < 10!)
        for i in 201..=203i64 {
            conn.execute(
                r#"INSERT INTO "PatientEncounter" ("patient_id", "full_name", "department", "age_years", "length_of_stay_days", "readmitted_30d?") VALUES (?1, ?2, ?3, ?4, ?5, ?6)"#,
                &[
                    SqlParam::Int(i),
                    SqlParam::Text(format!("SecretGeneticsPatient_{i}")),
                    SqlParam::Text("Genetics".to_string()),
                    SqlParam::Int(31),
                    SqlParam::Decimal(parse_decimal_bigint_strict("2.0")?),
                    SqlParam::Bool(false),
                ],
            )?;
        }
    }

    let prog = compile_example("examples/hipaa-clinic-outcomes.dana", true)
        .map_err(|e| format!("compile hipaa-clinic-outcomes: {e}"))?;
    let mut db_bindings = HashMap::new();
    db_bindings.insert("Clinic".to_string(), db_uri);
    let cfg = RunConfig {
        work_dir: Some(tmp.path().to_path_buf()),
        db_bindings,
        live_io: true,
        ..RunConfig::default()
    };

    for (engine, res) in [
        ("oracle", run_exec_program(&prog, &cfg)),
        ("vm", run_exec_program_vm(&prog, &cfg, &VmConfig::default())),
    ] {
        match res {
            RunResult::Ok {
                exit_code, stdout, ..
            } => {
                assert_eq!(exit_code, 0, "{engine} exit_code");
                let out_s = stdout.join("\n");
                assert!(
                    out_s.contains("Cardiology") && out_s.contains("Oncology"),
                    "{engine} stdout:\n{out_s}"
                );
                assert!(
                    !out_s.contains("Genetics"),
                    "{engine} leaked suppressed Genetics group:\n{out_s}"
                );
                assert!(
                    !out_s.contains("SecretCardioPatient"),
                    "{engine} leaked patient name"
                );
            }
            other => return Err(format!("{engine} failed: {other:?}").into()),
        }
    }

    let html = fs::read_to_string(tmp.path().join("reports/clinical-outcomes.html"))?;
    assert!(html.contains("Quarterly Clinical Outcomes (HIPAA De-Identified)"));
    assert!(html.contains("<svg xmlns=\"http://www.w3.org/2000/svg\""));
    assert!(html.contains("Cardiology") && html.contains("Oncology"));
    assert!(
        !html.contains("Genetics"),
        "suppressed small group leaked into HTML"
    );
    assert!(
        !html.contains("SecretCardioPatient"),
        "PII leaked into HTML"
    );
    assert!(!html.contains("NaN"));
    Ok(())
}

#[test]
fn e2e_live_log_anomaly_triage_with_jsonl_gz() -> TestResult {
    let tmp = TempDir::new("log_triage")?;
    let gz_path = tmp.path().join("access.jsonl.gz");

    // Build 12 five-minute buckets for `/api/pay` (11 normal ~25ms + 1 massive 950ms spike -> z > 3.0)
    // and 4 normal buckets for `/api/search`, plus 1 malformed JSON line.
    let mut raw_jsonl = String::new();
    for m in 0..11u32 {
        let total_min = m * 5;
        let hr = 12 + (total_min / 60);
        let mn = total_min % 60;
        raw_jsonl.push_str(&format!(
            "{{\"ts\":\"2026-10-01T{hr:02}:{mn:02}:10Z\",\"client_ip\":\"198.51.100.{}\",\"endpoint\":\"/api/pay\",\"status\":200,\"latency_ms\":{:.1}}}\n",
            m + 1,
            24.0 + f64::from(m % 3)
        ));
    }
    // Spike bucket (55 minutes in): 502 error with 950ms latency
    raw_jsonl.push_str(
        "{\"ts\":\"2026-10-01T12:55:15Z\",\"client_ip\":\"203.0.113.77\",\"endpoint\":\"/api/pay\",\"status\":502,\"latency_ms\":950.0}\n",
    );
    for m in 0..4u32 {
        let mn = m * 5;
        raw_jsonl.push_str(&format!(
            "{{\"ts\":\"2026-10-01T12:{mn:02}:20Z\",\"client_ip\":\"192.0.2.{}\",\"endpoint\":\"/api/search\",\"status\":200,\"latency_ms\":18.5}}\n",
            m + 1
        ));
    }
    raw_jsonl.push_str("{broken json line\n");

    {
        let f = fs::File::create(&gz_path)?;
        let mut gz = GzipWriter::new(f)?;
        gz.write_all(raw_jsonl.as_bytes())?;
        gz.finish()?;
    }

    let prog = compile_example("examples/log-anomaly-triage.dana", true)
        .map_err(|e| format!("compile log-anomaly-triage: {e}"))?;
    let cfg = RunConfig {
        args: vec![gz_path.display().to_string()],
        work_dir: Some(tmp.path().to_path_buf()),
        live_io: true,
        ..RunConfig::default()
    };

    for (engine, res) in [
        ("oracle", run_exec_program(&prog, &cfg)),
        ("vm", run_exec_program_vm(&prog, &cfg, &VmConfig::default())),
    ] {
        match res {
            RunResult::Ok {
                exit_code,
                stdout,
                stderr,
            } => {
                assert_eq!(
                    exit_code, 1,
                    "{engine} expected exit code 1 with latency spike"
                );
                assert_eq!(stderr.len(), 1, "{engine} stderr={stderr:?}");
                assert!(stderr[0].contains("Skipped 1 malformed JSON log lines"));
                let out_s = stdout.join("\n");
                assert!(
                    out_s.contains("p95 Latency (5m Buckets)"),
                    "{engine} missing terminal chart:\n{out_s}"
                );
                assert!(out_s.contains("/api/pay"), "{engine} stdout:\n{out_s}");
                assert!(
                    !out_s.contains("203.0.113.77"),
                    "{engine} leaked client_ip PII"
                );
            }
            other => return Err(format!("{engine} failed: {other:?}").into()),
        }
    }

    let html = fs::read_to_string(tmp.path().join("reports/incident-triage.html"))?;
    assert!(html.contains("HTTP Latency &amp; 5xx Triage"));
    assert!(html.contains("<svg xmlns=\"http://www.w3.org/2000/svg\""));
    assert!(html.contains("<polyline "));
    assert!(
        html.contains("[REDACTED]"),
        "expected redacted client_ip in error samples table"
    );
    assert!(
        !html.contains("203.0.113.77"),
        "client_ip PII leaked into HTML report"
    );
    assert!(
        !html.contains("198.51.100."),
        "client_ip PII leaked into HTML report"
    );
    assert!(!html.contains("NaN"));
    Ok(())
}
