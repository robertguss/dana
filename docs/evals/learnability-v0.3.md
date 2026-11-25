# Dana v0.3 Prospective AI Learnability Evaluation Protocol

> **Status:** Prospective Pre-Registration (Pre-Execution)
> **Target Release:** Dana **v0.3** (pre-1.0 — holding `v1.0` for a later GA milestone)
> **Reference Specification Baseline:** `docs/reference/README.md` at commit `2a7ba5e` (embedded verbatim in `dana guide`)
> **Deterministic Grading Harness:** [`tests/learnability_harness.rs`](../../tests/learnability_harness.rs)
> **Results Report (Post-Execution):** `docs/evals/learnability-v0.3-results.md` *(to be written ONLY after live multi-family model runs complete; zero placeholder results appear in this protocol document)*

---

## 1. Objective

Verify prospectively that fresh, zero-history AI coding agents from multiple independent model families can write correct, idiomatic, privacy-compliant, canonically formatted **Dana v0.3** data pipelines on **6 unseen real-world tasks** using **only** the embedded `dana guide` language reference and Dana's compiler/test/format diagnostics—with zero access to the Dana repository, examples, or grading harness.

This protocol is committed **before** any candidate model executes any task so that the task specifications, model matrix, scoring rubric, and acceptance gates are locked prospectively without hindsight selection.

---

## 2. Information Boundary & Isolation Rules

Every candidate model runs as a fresh, zero-history agent inside an isolated temporary directory:

```text
/tmp/dana-eval/<model>/
```

### Permitted Inputs (Exclusive)

Each candidate agent has access **only** to:

1. A standalone release binary copy of `dana` at `/tmp/dana-eval/dana`, reading the Dana v0.3 specification **exclusively** via `/tmp/dana-eval/dana guide` (and `/tmp/dana-eval/dana guide <section>`), which embeds `docs/reference/README.md` from commit `2a7ba5e`.
2. The standalone 6-task specification packet (`tasks.md`, exact text in Section 6 below) and Task 2's institutional policy file (`t2_dana.policy`, exact text in Section 6.1 below).
3. Compiler, test, formatter, and runtime feedback from `/tmp/dana-eval/dana` (`check`, `test`, `format`, `explain`, `run`) on the agent's own files inside `/tmp/dana-eval/<model>/`, **only after** freezing Stage 1 (`t<N>.attempt1.dana`).

### Explicit Prohibitions

Candidate agents **must not**:

- Read, list, search, or inspect `/home/exedev/code/dana` or any git worktree of the Dana repository (`examples/`, `src/`, `tests/`, `benchmarks/`, `docs/`, `grammar/`, `formal/`).
- Read `tests/learnability_harness.rs`, any hidden fixtures, or any other model's `/tmp/dana-eval/<other-model>/` workspace.
- Search the web or fetch external documentation or source code for Dana.
- Modify `t2_dana.policy`, `tasks.md`, or `/tmp/dana-eval/dana`.

---

## 3. Model Matrix (4 Models Across 2 Families)

| Family | Provider Driver | Model Identifier | Tier |
| --- | --- | --- | --- |
| Anthropic Claude | `claudeAgent` | `claude-sonnet-5-5` | Frontier balanced |
| Anthropic Claude | `claudeAgent` | `claude-haiku-5-5` | Fast / compact |
| Google Gemini | `antigravity` | `gemini-4-neon` | Frontier reasoning |
| Google Gemini | `antigravity` | `gemini-4-argon` | Fast / compact |

Running both flagship and compact tiers across two distinct vendor families tests whether learnability stems from Dana's syntax, type/privacy model, and `dana guide` clarity rather than vendor-specific quirks.

---

## 4. Two-Stage Scoring Protocol

For each task `N ∈ {1, 2, 3, 4, 5, 6}`:

### Stage 1 — First-Shot Pass Rate (`t<N>.attempt1.dana`)

1. The model reads `/tmp/dana-eval/dana guide` and `tasks.md` (plus `t2_dana.policy` for Task 2).
2. **Before** invoking `dana check`, `dana test`, `dana format`, or `dana run` on task `N`, the model writes its complete initial solution to:
   ```text
   /tmp/dana-eval/<model>/t<N>.attempt1.dana
   ```
3. `t<N>.attempt1.dana` is frozen immediately once written and never overwritten.
4. The deterministic harness grades `t<N>.attempt1.dana` across all 5 automated checks, reporting both:
   - **First-Shot Functional Pass:** static check + author tests + hidden functional E2E + hidden privacy audit (independent of whitespace formatting), and
   - **First-Shot Strict Pass:** all 5 gates including `dana format --check`.

### Stage 2 — Compiler-Assisted Pass Rate (`t<N>.dana`, `<= 3` Repair Iterations)

1. Starting from `t<N>.attempt1.dana`, the model copies/edits into `t<N>.dana` and may execute up to **3 repair iterations** using **only** diagnostics from:
   - `/tmp/dana-eval/dana check` (passing `--policy t2_dana.policy` for Task 2),
   - `/tmp/dana-eval/dana test` (passing `--policy t2_dana.policy` for Task 2),
   - `/tmp/dana-eval/dana format --check` / `/tmp/dana-eval/dana format`.
2. Each repair iteration counts as one diagnostic-to-edit cycle (max `3` cycles; iteration `0` means `t<N>.attempt1.dana` already passed all local checks and formatting cleanly).
3. Final submissions `t1.dana` .. `t6.dana` are graded offline by `tests/learnability_harness.rs` (invoked via `DANA_EVAL_SUBMISSION_DIR=/tmp/dana-eval/<model> cargo test --test learnability_harness grade_external_submission_dir_if_set -- --nocapture`).

### Automated Five-Gate Grading Rubric (Per Submission)

Every submission is evaluated deterministically by `tests/learnability_harness.rs` on five gates:

1. **Canonical Formatting (`formatted_cleanly`):** `parse_module` succeeds and `format_module(&module) == source` (identical to `dana format --check`).
2. **Static Type, Privacy & Policy Check (`check_passed`):** Correct module header, `resolve_path` + `check_resolved` (enforcing `t2_dana.policy` for Task 2) + `lower_program` succeed with `0` diagnostics.
3. **Author Unit Tests (`author_tests_passed`):** At least one `test` block exists, and every `test`/`examples` block passes on **both** the vectorized columnar VM (`run_program_tests_vm`) and the naive reference oracle (`run_program_tests`).
4. **Hidden Functional E2E Grading (`hidden_e2e_passed`):**
   - Direct execution of every required pure function via `eval_exec_entry_vm` on hidden typed fixtures, verifying exact schema/columns, row ordering, numeric accuracy, and edge cases.
   - Live execution of `main(...)` across **both** the vectorized VM and the reference oracle on hidden disk/SQLite/Parquet fixtures, verifying exit codes, console output, and generated output artifacts (`.csv`, `.html`, `.md`).
5. **Hidden Privacy & Policy Audit (`privacy_audit_passed`):**
   - **T2:** Verifies `t2_dana.policy` compliance, public `Console` signature, declassified return type (zero `[pii]`/`[ferpa]` tags), suppression of both `< 5`-row cohorts AND multi-row cohorts with `< 5` distinct `student_id`s, and zero raw PII/suppressed cohort names in stdout/stderr.
   - **T5:** Verifies `[pii]` cleared and `[health]` preserved on `prepare_research_export`, exact keyed HMAC-SHA256 pseudonymization using `Secret("CLINIC_HMAC_KEY")` (verified live via subprocess `CLINIC_HMAC_KEY` env var), `"[REDACTED]"` notes, zero raw patient IDs/notes in `exports/clinic-export.csv` or stdout/stderr, and hard runtime denial (`ExportGateDenied`) when `--allow-export health` is omitted.

---

## 5. Pre-Declared v0.3 Acceptance Gate Criteria

To pass the **Dana v0.3** AI Learnability Gate, live multi-family results must satisfy ALL of the following:

1. **Compiler-Assisted Pass Rate:** `>= 85%` per model family (`>= 10/12` per family, or `>= 5/6` per individual model) on Stage 2 final submissions (`t1.dana`..`t6.dana`), where a pass requires all 5 grading gates to succeed.
2. **Zero Privacy / Policy Leaks:** `0` privacy or policy leaks across all passing submissions (100% pass on hidden negative privacy probes for T2 and T5).
3. **100% Canonical Formatting Compliance:** `100%` `dana format --check` compliance across all passing Stage 2 final submissions.
4. **Full Transparency Reporting:** `docs/evals/learnability-v0.3-results.md` must report:
   - Exact Stage 1 (first-shot) vs. Stage 2 (compiler-assisted) pass rates per model and per family,
   - Exact per-task pass/fail breakdown (`T1`–`T6`),
   - Exact repair iteration counts (`0..=3`) per task and model,
   - Exact Dana diagnostic codes encountered during first-shot failures, and
   - Every compiler, diagnostic, or `dana guide` ergonomics gap discovered during the live runs.

---

## 6. Standalone Evaluation Packet (`t2_dana.policy` & `tasks.md`)

The two artifacts below are placed verbatim into each candidate agent's isolated `/tmp/dana-eval/<model>/` directory.

### 6.1 `t2_dana.policy`

<!-- BEGIN T2_DANA_POLICY -->
```text
version 1

min_group_size 5
forbid manual_declassify
forbid repl_show_sensitive

allow console tags []
```
<!-- END T2_DANA_POLICY -->

### 6.2 `tasks.md`

<!-- BEGIN STANDALONE TASKS.MD -->
# Dana v0.3 Unseen Task Suite (T1–T6)

Implement all 6 standalone Dana modules in your current working directory (`t1.dana` through `t6.dana`).

## Rules

1. Read the Dana language reference exclusively via `/tmp/dana-eval/dana guide`. Do not access any external Dana repository or examples.
2. For each task `N` (`1..=6`):
   - **First**, write your complete initial solution to `t<N>.attempt1.dana` **before** running `dana check`, `dana test`, `dana format`, or `dana run` on task `N`. Do not edit `t<N>.attempt1.dana` afterward.
   - **Next**, copy `t<N>.attempt1.dana` to `t<N>.dana` and use only `/tmp/dana-eval/dana check` (with `--policy t2_dana.policy` for Task 2), `/tmp/dana-eval/dana test`, and `/tmp/dana-eval/dana format` to repair any errors in up to **3 repair iterations**.
   - Ensure every final `t<N>.dana` passes `dana format --check`, `dana check`, and `dana test`.
3. Follow every module name, schema name, column name/type/tag/constraint, pure function name/signature, `main` signature, and output file path **exactly** as specified below; an automated hidden test suite imports/invokes both your pure functions and `main`.

---

## Task 1 (`t1.dana`, `module LedgerEtl`) — Zero-Friction Public CSV Quarantine ETL

- **Module:** `module LedgerEtl`
- **Schema:** `schema LedgerRow`
  - `txn_id: Int`
  - `date: Date`
  - `category: Text where not .empty?`
  - `amount: Decimal where . > 0`
- **Pure Function:**
  - Signature: `fn summarize_ledger(rows: Table(LedgerRow)) : Table(category: Text, txn_count: Int, total_amount: Decimal)`
  - Postcondition: `promise unique(.category)`
  - Behavior: Group `rows` by `.category`, summarize `txn_count: count()` and `total_amount: sum(.amount)`, and sort descending by `.total_amount` (breaking any ties ascending by `.category`).
- **Entry Point:**
  - Signature: `fn main(args: Args, files: ReadFiles, console: Console) : Int`
  - Behavior:
    1. Obtain the CSV path via `args.first.or_return(2)`.
    2. Load `(rows, bad_rows) = try files.read_csv(path, as: LedgerRow)`.
    3. Print `summarize_ledger(rows)` via `console.print_table(...)`.
    4. Return `0` if `bad_rows.empty?`, else `1`.
- **Tests:** Include at least one `test` block exercising `Files.in_memory` and `summarize_ledger`.

---

## Task 2 (`t2.dana`, `module FerpaSummary`) — FERPA Institutional Privacy & `dana.policy`

- **Module:** `module FerpaSummary`
- **Policy:** Must pass `dana check --policy t2_dana.policy t2.dana` and `dana test --policy t2_dana.policy t2.dana` against `t2_dana.policy`.
- **Schema:** `schema StudentRecord`
  - `student_id: Int [pii]`
  - `email: Text [pii]`
  - `gpa: Decimal [ferpa] where . >= 0.0 and . <= 4.0`
  - `age: Int [ferpa] where . >= 14 and . <= 120`
  - `program: Text`
- **Pure Function:**
  - Signature: `fn program_outcomes(students: Table(StudentRecord)) : Table(program: Text, age_band: Text, student_count: Int, avg_gpa: Decimal?)` *(return type may be written explicitly or inferred with these exact columns and types)*
  - Postconditions:
    - `promise unique(.program, .age_band)`
    - `promise all(.student_count >= 5)`
  - Behavior:
    1. Derive `age_band: bucket(.age, cuts: [22, 30], labels: ["under_22", "22_to_29", "30_plus"])`.
    2. Group by `.program, .age_band`.
    3. Summarize `student_count: count_distinct(.student_id)` and `avg_gpa: mean(.gpa)`.
    4. Apply `suppress_small_groups(min: 5, distinct_by: .student_id)`.
    5. Sort ascending by `.program, .age_band`.
- **Entry Point:**
  - Signature: `fn main(files: ReadFiles, console: Console) : Int` *(plain public `Console` with NO `allows:` clause, because `suppress_small_groups` declassifies `[pii]` and `[ferpa]`)*
  - Behavior:
    1. Read `"students.csv"` via `files.read_csv("students.csv", as: StudentRecord)`.
    2. Print `program_outcomes(students)` via `console.print_table(...)`.
    3. Return `0`.
- **Tests:** Include at least one `test` block proving that groups with `< 5` distinct students are suppressed while groups with `>= 5` distinct students survive.

---

## Task 3 (`t3.dana`, `module OrdersAnalytics`) — SQLite `ReadDB` Pushdown, Explicit-Cardinality Joins & Windows

- **Module:** `module OrdersAnalytics`
- **Schemas:**
  - `schema Customer`
    - `customer_id: Int`
    - `tier: Text`
    - `active?: Bool`
  - `schema OrderRow`
    - `order_id: Int`
    - `customer_id: Int`
    - `order_date: Date`
    - `total: Decimal where . > 0`
- **Pure Function 1:**
  - Signature: `fn active_tier_daily_revenue(customers: Table(Customer), orders: Table(OrderRow)) : Table(tier: Text, order_date: Date, daily_revenue: Decimal, order_count: Int, rolling_2d_avg: Float?)` *(return type may be explicit or inferred with these exact columns and types)*
  - Behavior:
    1. Filter `customers` to active rows (`where(.active?)`).
    2. Join `orders` with active customers using `join_many_to_one(..., on: .customer_id)`.
    3. Group by `.tier, .order_date`.
    4. Summarize `daily_revenue: sum(.total)` and `order_count: count()`.
    5. Apply `window(rolling_2d_avg: rolling_mean(.daily_revenue, rows: 2), over: [.tier], order: .order_date)`.
    6. Sort ascending by `.tier, .order_date`.
- **Pure Function 2:**
  - Signature: `fn customers_without_orders(customers: Table(Customer), orders: Table(OrderRow)) : Table(customer_id: Int, tier: Text)` *(return type may be explicit or inferred with these exact columns and types)*
  - Behavior:
    1. Apply `anti_join(orders, on: .customer_id)` on `customers`.
    2. Select `.customer_id, .tier`.
    3. Sort ascending by `.customer_id`.
- **Entry Point:**
  - Signature: `fn main(db: ReadDB(Store), console: Console) : Int`
  - Behavior:
    1. Read `db.table(Customer)` and `db.table(OrderRow)`.
    2. Print `active_tier_daily_revenue(...)` via `console.print_table(...)`.
    3. Return `0`.
- **Tests:** Include at least one `test` block using `DB.in_memory(Store, ...)` or table literals exercising both pure functions.

---

## Task 4 (`t4.dana`, `module MetricStats`) — Reshaping (`pivot_longer`) & Practical Statistics (`use Stats`)

- **Module:** `module MetricStats` (must declare `use Stats`)
- **Schema:** `schema WideMetric`
  - `entity: Text`
  - `group_name: Text`
  - `q1: Float`
  - `q2: Float`
  - `q3: Float`
- **Pure Function 1:**
  - Signature: `fn melt_quarters(rows: Table(WideMetric)) : Table(entity: Text, group_name: Text, quarter: Text, score: Float)` *(return type may be explicit or inferred with these exact columns and types)*
  - Behavior:
    1. Unpivot `rows` via `pivot_longer(cols: [.q1, .q2, .q3], names_to: "quarter", values_to: "score")`.
    2. Sort ascending by `.entity, .quarter`.
- **Pure Function 2:**
  - Signature: `fn quarter_stats(rows: Table(WideMetric)) : Table(r_spearman: Float, slope: Float, pred_10: Float, p_value: Float)`
  - Behavior:
    1. Compute `r_spearman = Stats.corr(rows, x: .q1, y: .q3, method: :spearman)`.
    2. Compute `model = Stats.linear_regression(rows, x: .q1, y: .q3)`.
    3. Compute `pred_10 = model.predict(10.0)`.
    4. Compute two-sample Welch t-test `ab = Stats.t_test(rows |> where(.group_name == "A"), rows |> where(.group_name == "B"), column: .q3)`.
    5. Return a 1-row `Table(r_spearman: Float, slope: Float, pred_10: Float, p_value: Float)` containing `(r_spearman, model.slope, pred_10, ab.p_value)`.
- **Entry Point:**
  - Signature: `fn main(files: ReadFiles, console: Console) : Int`
  - Behavior:
    1. Read `"metrics.csv"` via `files.read_csv("metrics.csv", as: WideMetric)`.
    2. Print `quarter_stats(...)` via `console.print_table(...)`.
    3. Return `0`.
- **Tests:** Include at least one `test` block verifying `melt_quarters` row count and `quarter_stats` values.

---

## Task 5 (`t5.dana`, `module ClinicExport`) — Keyed Pseudonymization, Redaction & Authorized Export

- **Module:** `module ClinicExport`
- **Schema:** `schema ClinicVisit`
  - `patient_id: Text [pii]`
  - `notes: Text [pii]`
  - `clinic_code: Text`
  - `systolic_bp: Int [health] where . > 0`
- **Pure Function:**
  - Signature: `fn prepare_research_export(visits: Table(ClinicVisit), key: Secret("CLINIC_HMAC_KEY"))` *(returns columns `patient_id: Text, notes: Text, clinic_code: Text, systolic_bp: Int [health]`; return type annotation may be omitted so Dana infers column and order sensitivity tags)*
  - Behavior:
    1. Run `pseudonymize(.patient_id, key: key)` and `redact(.notes)`.
    2. Keep `.patient_id, .notes, .clinic_code, .systolic_bp`.
    3. Sort ascending by `.clinic_code, .systolic_bp`.
    4. Result clears `[pii]` while preserving `[health]` on `.systolic_bp`.
- **Entry Point:**
  - Signature: `fn main(files: ReadFiles, key: Secret("CLINIC_HMAC_KEY"), out: WriteFiles("exports/", allows: [health]), console: Console) : Int`
  - Behavior:
    1. Read `"visits.csv"` via `files.read_csv("visits.csv", as: ClinicVisit)`.
    2. Compute `prepared = prepare_research_export(visits, key)`.
    3. Write `"clinic-export.csv"` via `try out.write_csv("clinic-export.csv", prepared)`.
    4. Print `"exported #{prepared.count()}"` via `console.print(...)`.
    5. Return `0`.
- **Tests:** Include at least one `test` block using `Secret.fake("test-key")` verifying deterministic pseudonymization and `"[REDACTED]"` notes.

---

## Task 6 (`t6.dana`, `module SensorReport`) — Multi-Format Parquet, `Stats.outliers`, Trendline SVG Chart & HTML/Markdown Report

- **Module:** `module SensorReport` (must declare `use Stats`)
- **Schema:** `schema SensorPoint`
  - `sensor_id: Text`
  - `zone: Text`
  - `temp_c: Float`
  - `power_w: Float where . >= 0.0`
- **Pure Function:**
  - Signature: `fn flag_power_outliers(points: Table(SensorPoint)) : Table(sensor_id: Text, zone: Text, temp_c: Float, power_w: Float, outlier?: Bool)` *(return type may be explicit or inferred with these exact columns and types)*
  - Behavior:
    1. Call `Stats.outliers(points, column: .power_w, method: :zscore, threshold: 2.0)`.
    2. Sort ascending by `.sensor_id`.
- **Entry Point:**
  - Signature: `fn main(files: ReadFiles, out: WriteFiles("reports/"), console: Console) : Int`
  - Behavior:
    1. Read `"sensors.parquet"` via `points = try files.read_parquet("sensors.parquet", as: SensorPoint)`.
    2. Compute `flagged = flag_power_outliers(points)`.
    3. Compute `r = Stats.corr(points, x: .temp_c, y: .power_w, method: :pearson)`.
    4. Compute `model = Stats.linear_regression(points, x: .temp_c, y: .power_w)`.
    5. Build scatter chart:
       ```dana
       chart = points
         |> chart_scatter(
              x: .temp_c,
              y: .power_w,
              color: .zone,
              trendline: model,
              title: "Temp vs Power (r = #{r.round(3)})"
            )
       ```
    6. Build report:
       ```dana
       report = Report.new("Sensor Diagnostics")
         |> add_summary("Slope=#{model.slope.round(3)}, R2=#{model.r_squared.round(3)}")
         |> add_chart(chart)
         |> add_table(flagged |> where(.outlier?))
       ```
    7. Write **both** `try out.write_html("sensors.html", report)` and `try out.write_markdown("sensors.md", report)`.
    8. Print a summary line to `console`.
    9. Return `0`.
- **Tests:** Include at least one `test` block verifying `flag_power_outliers` flags an injected high-power spike.
<!-- END STANDALONE TASKS.MD -->
