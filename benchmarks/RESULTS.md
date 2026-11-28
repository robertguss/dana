# Dana v0.7.2 End-to-End Benchmarks vs. Python

Reproducible end-to-end pipeline benchmarks comparing **Dana v0.7.2 (pre-1.0, Zero-Crate Rust)** against **Python stdlib / `sqlite3`**, **Pandas**, and **Polars** across four realistic data-engineering, SQL-pushdown privacy, and statistical-reporting workloads.

## Methodology & Environment

- **CPU:** AMD EPYC 9554P 64-Core Processor (8 logical cores)
- **Memory:** 31.3 GiB
- **OS:** Linux 6.12.115 (x86_64)
- **Toolchain:** `rustc 1.100.0 (0ef1bc386 2026-11-09)` (`target/release/dana`, zero external Rust crates)
- **Python baselines:** Python `3.15.2`, Pandas `3.1.1`, Polars `2.2.0`, PyArrow `26.0.1` (installed solely in ephemeral `/tmp/dana-bench-venv`)
- **Timing protocol:** 1 warmup run + 5 timed runs per engine, each in a **fresh child subprocess** timed end-to-end with wall-clock `perf_counter` and isolated per-process kernel peak RSS (`/usr/bin/time -f %M`, falling back to `os.wait4`), capturing full cold-start CLI / interpreter startup, parsing/compilation, I/O, execution, and output writing.
- **Output parity:** Every Python baseline is verified cell-for-cell against Dana's outputs after execution (exact keys, counts, FERPA suppressions, exact `Decimal` against Python `Decimal`, and strict floating-point tolerances).

### Reproduce

```sh
cargo build --release
python3 benchmarks/run_benchmarks.py
```

## Headline Results (Median End-to-End Wall-Clock)

| Workload | Rows | Dana v0.7.2 (ms) | Python stdlib (ms) | Pandas (ms) | Polars (ms) | Dana vs. stdlib | Dana vs. Pandas | Dana vs. Polars |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| W1: CSV + UDF ETL | 500,500 | **368.3** | 1366.3 | 1856.7 | 322.2 | **3.71× faster** | **5.04× faster** | 1.14× slower |
| W2: 500k×50k Join + UDF | 500,000 | **152.8** | 992.3 | 522.0 | 280.2 | **6.49× faster** | **3.42× faster** | **1.83× faster** |
| W3: SQLite + FERPA Privacy | 250,000 | **107.8** | 160.3 | 595.0 | 360.6 | **1.49× faster** | **5.52× faster** | **3.35× faster** |
| W4: Parquet + Stats + HTML | 200,000 | **125.1** | 645.5 | 519.6 | 243.4 | **5.16× faster** | **4.15× faster** | **1.95× faster** |

## Dana v0.3.0 -> v0.7.2 Speedup & Peak-RSS Improvement

| Workload | v0.3.0 Median (ms) | v0.7.2 Median (ms) | Latency Speedup | v0.3.0 Peak RSS (MiB) | v0.7.2 Peak RSS (MiB) | Peak-RSS Reduction |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| W1: CSV + UDF ETL | 3602.9 | **368.3** | **9.78× faster** | 1325.1 | **116.9** | **11.34× smaller (−91.2%)** |
| W2: 500k×50k Join + UDF | 1504.0 | **152.8** | **9.84× faster** | 781.8 | **99.2** | **7.88× smaller (−87.3%)** |
| W3: SQLite + FERPA Privacy | 127.1 | **107.8** | **1.18× faster** | 29.0 | **22.2** | **1.31× smaller (−23.5%)** |
| W4: Parquet + Stats + HTML | 1110.2 | **125.1** | **8.88× faster** | 350.1 | **53.2** | **6.58× smaller (−84.8%)** |

## W1: 500,000-Row CSV Quarantine + Pure Dana UDF + GroupBy/Sort

`benchmarks/w1_csv_udf_etl.dana` ingests 500,000 valid + 500 malformed CSV rows (quarantining invalid decimals and negative quantities), filters `qty > 0`, evaluates a multi-branch pure `net_price` UDF in exact `Decimal` arithmetic (inlined into Dana's vectorized register bytecode), aggregates across 32 `(region, category)` groups, and sorts descending by `total_net`.

| Engine | Median (ms) | Min (ms) | Max (ms) | Throughput (rows/s) | Peak RSS (MiB) |
| --- | ---: | ---: | ---: | ---: | ---: |
| Dana v0.7.2 (exact `Decimal`, columnar CSV + inlined UDF) | 368.3 | 350.4 | 393.9 | 1,358,996 | 116.9 |
| Python stdlib (`csv` + `decimal.Decimal`) | 1366.3 | 1317.5 | 1435.5 | 366,321 | 21.6 |
| Pandas (`float64` + Python UDF loop) | 1856.7 | 1661.9 | 2009.7 | 269,558 | 311.9 |
| Polars (native `pl.when/then` `Float64` expr) | 322.2 | 283.5 | 332.9 | 1,553,259 | 273.5 |

## W2: 500,000-Row Fact × 50,000-Row Dim Parquet `join_many_to_one` + UDF + Agg

`benchmarks/w2_columnar_join_analytics.dana` reads 500,000 fact rows and 50,000 dimension rows from Zstd Parquet (Python stdlib reads equivalent CSV mirrors since stdlib has no Parquet codec), performs a checked N:1 hash join enforcing dimension uniqueness, runs an inlined `effective_margin` UDF, aggregates across 40 `(department, channel)` groups, and sorts deterministically.

| Engine | Median (ms) | Min (ms) | Max (ms) | Throughput (rows/s) | Peak RSS (MiB) |
| --- | ---: | ---: | ---: | ---: | ---: |
| Dana v0.7.2 (columnar Zstd Parquet + zero-copy N:1 join + inlined UDF) | 152.8 | 120.4 | 168.9 | 3,271,762 | 99.2 |
| Python stdlib (CSV mirror + `dict` join) | 992.3 | 979.2 | 1008.8 | 503,892 | 35.1 |
| Pandas (`read_parquet` + `merge(validate='many_to_one')`) | 522.0 | 506.2 | 578.6 | 957,815 | 252.9 |
| Polars (`read_parquet` + `join(validate='m:1')`) | 280.2 | 255.4 | 312.8 | 1,784,689 | 212.4 |

## W3: 250,000-Row SQLite Pushdown + `[pii]`/`[ferpa]` Suppression + Rolling Window

`benchmarks/w3_sqlite_pushdown_privacy.dana` scans a 250,000-row SQLite database via `ReadDB`, pushes `where(.active? and .term_year >= 2024)` and column projection down into parameterized SQL, buckets `[ferpa]` ages, aggregates distinct students & mean GPA, declassifies via `suppress_small_groups(min: 5, distinct_by: .student_id)` (suppressing `RareStudies`), and computes a partitioned 3-term `rolling_mean` window. Python baselines execute the identical pushed-down SQL query.

| Engine | Median (ms) | Min (ms) | Max (ms) | Throughput (rows/s) | Peak RSS (MiB) |
| --- | ---: | ---: | ---: | ---: | ---: |
| Dana v0.7.2 (SQLite pushdown + compile-time `[pii]`/`[ferpa]` + VM window) | 107.8 | 85.0 | 111.4 | 2,319,986 | 22.2 |
| Python stdlib (`sqlite3` + pure Python aggregation/window) | 160.3 | 154.9 | 180.1 | 1,559,487 | 24.6 |
| Pandas (`read_sql_query` + `pd.cut` + `groupby` + `rolling`) | 595.0 | 582.2 | 608.4 | 420,199 | 153.0 |
| Polars (`read_database` + `group_by` + `rolling_mean.over`) | 360.6 | 355.8 | 397.3 | 693,375 | 98.5 |

## W4: 200,000-Row Native Zstd Parquet Round-Trip + Stats + Profile + HTML Report

`benchmarks/w4_parquet_stats_report.dana` reads 200,000 Zstd Parquet rows, filters healthy readings, writes a filtered Zstd Parquet file, computes a full dataset `profile()`, Pearson `Stats.corr`, `Stats.linear_regression`, grouped zone metrics, an inline SVG scatter plot with OLS trendline, and a self-contained HTML5 report.

| Engine | Median (ms) | Min (ms) | Max (ms) | Throughput (rows/s) | Peak RSS (MiB) |
| --- | ---: | ---: | ---: | ---: | ---: |
| Dana v0.7.2 (columnar Zstd Parquet + `Stats` + `profile()` + SVG/HTML5) | 125.1 | 101.4 | 148.5 | 1,599,134 | 53.2 |
| Python (`pyarrow` Parquet I/O + pure Python stats/HTML) | 645.5 | 611.3 | 662.3 | 309,838 | 240.2 |
| Pandas (`read_parquet`/`to_parquet` + NumPy OLS + HTML) | 519.6 | 496.2 | 559.6 | 384,897 | 208.1 |
| Polars (`read_parquet`/`write_parquet` + `corr`/`cov` + HTML) | 243.4 | 241.0 | 250.9 | 821,664 | 125.4 |

## Exact Output Parity Checks

- **W1 (`w1_summary.csv`):** 32/32 groups matched across all engines — exact 0-ulp `Decimal` equality between Dana and Python `decimal.Decimal` (`valid=500,000`, `bad=500`), and `< 1e-9` relative parity against Pandas (`float64` UDF) and Polars (`Float64` expression).
- **W2 (`w2_summary.csv`):** 40/40 `(department, channel)` groups matched across Dana, Python stdlib, Pandas, and Polars — exact integer `total_units` & `txn_count`, and `< 1e-9` relative parity on `total_revenue` & `total_margin`.
- **W3 (`w3_summary.csv`):** 24/24 published `(department, age_band, term_seq)` cells matched identically (`< 1e-9` on `avg_gpa` and `rolling_3t_gpa`); all 75 `RareStudies` rows (3 distinct students) were suppressed and zero `[pii]` emails appeared in output.
- **W4 (`w4_stats.csv`, `w4_zones.csv`, `w4_report.html`, `w4_clean.parquet`):** Exact `clean_rows=180,000`, 6/6 zone aggregates, and `< 1e-9` parity on Pearson `r`, OLS `slope`, `intercept`, and `r_squared` across all engines, plus verified Zstd Parquet round-trip and inline `<svg>` HTML5 report output.

## W3 Parameterized SQLite Pushdown Verification (`dana explain`)

```text
== fn department_term_summary ==
-- plan #0 (dialect: sqlite) --
[LOGICAL PLAN]
  Window([rolling_3t_gpa])
    Sort([department:Asc, age_band:Asc, term_seq:Asc])
      SuppressSmallGroups(min=5, mode=Drop)
        HashAggregate([students:CountDistinct, enrollments:Count, avg_gpa:Mean])
          GroupBy([department, age_band, term_seq])
            Derive([age_band])
              Select([student_id, department, term_seq, age_years, grade_points])
                Filter
                  SourceDB(StudentEnrollment)
[OPTIMIZED PLAN] (fused=0, pushed=0, pruned=0, dead=0, limits=0)
  Window([rolling_3t_gpa])
    Sort([department:Asc, age_band:Asc, term_seq:Asc])
      SuppressSmallGroups(min=5, mode=Drop)
        HashAggregate([students:CountDistinct, enrollments:Count, avg_gpa:Mean])
          GroupBy([department, age_band, term_seq])
            Derive([age_band])
              Select([student_id, department, term_seq, age_years, grade_points])
                Filter
                  SourceDB(StudentEnrollment)
[SQL PUSHDOWN -> sqlite] (db=Registrar, bind=__dana_pushdown_0, ops=[SourceDB(StudentEnrollment) -> Filter -> Select([student_id, department, term_seq, age_years, grade_points]) -> Derive([age_band])])
  SELECT "student_id" AS "student_id", "department" AS "department", "term_seq" AS "term_seq", "age_years" AS "age_years", "grade_points" AS "grade_points", (CASE WHEN ("age_years" < ?) THEN ? WHEN ("age_years" < ?) THEN ? WHEN ("age_years" < ?) THEN ? ELSE ? END) AS "age_band" FROM "StudentEnrollment" WHERE ("active?" AND ("term_year" >= ?))
[PARAMETERS]
  ?1 = Int(22)
  ?2 = Text("under_22")
  ?3 = Int(30)
  ?4 = Text("22_to_29")
  ?5 = Int(45)
  ?6 = Text("30_to_44")
  ?7 = Text("45_plus")
  ?8 = Int(2024)
[PUSHDOWN BOUNDARY: aggregate `Mean` requires local VM]
[LOCAL VM SUFFIX]
  Window([rolling_3t_gpa])
    Sort([department:Asc, age_band:Asc, term_seq:Asc])
      SuppressSmallGroups(min=5, mode=Drop)
        HashAggregate([students:CountDistinct, enrollments:Count, avg_gpa:Mean])
          GroupBy([department, age_band, term_seq])
            SourceExpr
[SENSITIVITY PROVENANCE]
  ENTER SourceDB(StudentEnrollment): tags=[ferpa, pii], cols=[student_id:[pii], student_email:[pii], age_years:[ferpa], grade_points:[ferpa]], row_tags=[]
  DROP_COL Select([student_id, department, term_seq, age_years, grade_points]): removed tagged cols [student_email:[pii]]
  BUCKET Derive(age_band <- age_years): tags=[ferpa], bucketed=true (eligible for clearance under suppress_small_groups)
  PROPAGATE GroupBy([department, age_band, term_seq]): key tags [ferpa] -> row_tags=[ferpa]
  PROPAGATE Summarize: row_tags=[ferpa, pii], aggs=[students(CountDistinct,Blending)=[ferpa, pii], enrollments(Count,Blending)=[ferpa], avg_gpa(Mean,Blending)=[ferpa]]
  CLEAR SuppressSmallGroups(min=5, mode=Drop): cleared [ferpa, pii] (remaining=[])
  OUTPUT: PUBLIC (no sensitivity tags remaining)
```

## Honest Engineering Analysis

1. **Direct streaming-columnar CSV ingestion + exact `Decimal` UDF (W1):** Streaming CSV directly into 2,048-row `VmTable` batches (`Val::Columnar(Arc<VmTable>)`) with zero-allocation `parse_decimal_i128` and unboxed `FastColConstraint` validation cut Dana from `3602.9 ms / 1325.1 MiB` (v0.3.0) down to **`368.3 ms / 116.9 MiB`** (**9.78× faster**, **11.34× lower peak RSS**). Dana v0.7.2 is **3.71× faster** than Python `csv` + `decimal.Decimal` (1366.3 ms), **5.04× faster** than Pandas (`float64` + Python UDF loop) (1856.7 ms, 311.9 MiB RSS), and **1.14× slower** than Polars (native `pl.when/then` `Float64` expr) (322.2 ms, 273.5 MiB RSS) — while preserving exact 128-bit 18-digit fixed-point `Decimal` arithmetic (0-ulp parity with Python `Decimal`) and full `bad_rows` quarantine.
2. **Direct columnar Parquet + zero-copy N:1 hash join + unboxed aggregation (W2):** Decoding Zstd Parquet directly into `VmTable` batches, borrowing `Val::Columnar` join inputs without cloning, specializing single non-null `Int` keys + columnar gather in `op_hash_join`, and streaming unboxed `ExecSurface` aggregates cut Dana from `1504.0 ms / 781.8 MiB` (v0.3.0) to **`152.8 ms / 99.2 MiB`** (**9.84× faster**, **7.88× lower peak RSS**). Dana v0.7.2 is **6.49× faster** than Python stdlib (CSV + `dict` join) (992.3 ms), **3.42× faster** than Pandas (522.0 ms, 252.9 MiB RSS), and **1.83× faster** than Polars (280.2 ms, 212.4 MiB RSS) in a zero-crate Rust binary with checked N:1 uniqueness verification.
3. **SQLite pushdown + compile-time FERPA privacy (W3):** Dana v0.7.2 (**107.8 ms, 22.2 MiB peak RSS**; v0.3.0 was `127.1 ms / 29.0 MiB`) preserves and extends its decisive lead: **1.49× faster** than Python `sqlite3` stdlib (160.3 ms), **3.35× faster** than Polars (360.6 ms, 98.5 MiB RSS), and **5.52× faster** than Pandas (595.0 ms, 153.0 MiB RSS) — while statically proving `[pii]`/`[ferpa]` declassification (`suppress_small_groups(min: 5, distinct_by: .student_id)` -> `OUTPUT: PUBLIC`).
4. **Direct columnar Parquet round-trip + columnar `Stats` / `profile()` + HTML5 report (W4):** Eliminating `TableVal` boxing across `read_parquet`, `write_parquet`, `profile()`, `Stats.corr`, `Stats.linear_regression`, and grouped zone aggregation cut Dana from `1110.2 ms / 350.1 MiB` (v0.3.0) to **`125.1 ms / 53.2 MiB`** (**8.88× faster**, **6.58× lower peak RSS**). Dana v0.7.2 is **5.16× faster** than Python (`pyarrow` + pure Python stats/HTML) (645.5 ms), **4.15× faster** than Pandas + NumPy (519.6 ms, 208.1 MiB RSS), and **1.95× faster** than Polars (243.4 ms, 125.4 MiB RSS) with zero external Rust crates and full cell-for-cell parity.
