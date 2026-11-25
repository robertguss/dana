# Dana v0.3 Prospective AI Learnability Evaluation — Results

> **Status:** Completed — **ALL PRE-DECLARED ACCEPTANCE GATES PASSED**
> **Execution Date:** 2026-11-25
> **Target Release:** Dana **v0.3** (pre-1.0 — holding `v1.0` GA for streaming-columnar file I/O, pre-1.0 ergonomics polish, and production soak)
> **Prospective Protocol:** [`docs/evals/learnability-v0.3.md`](learnability-v0.3.md) (locked at commit `642401c` prior to running any candidate model)
> **Tested Binary Baseline:** Standalone release copy of `dana` built from commit `2a7ba5e` / `642401c`, embedding `docs/reference/README.md` v0.3 verbatim in `dana guide`
> **Deterministic Grader:** [`tests/learnability_harness.rs`](../../tests/learnability_harness.rs) (`DANA_EVAL_SUBMISSION_DIR=/tmp/dana-eval/<model> cargo test --test learnability_harness grade_external_submission_dir_if_set -- --nocapture`)

---

## 1. Pre-Declared Acceptance Gate Outcome: **PASSED**

All four pre-registered v0.3 acceptance criteria in Section 5 of [`docs/evals/learnability-v0.3.md`](learnability-v0.3.md) passed across all 4 models and both vendor families (`24` blind task runs total):

| Acceptance Criterion | Pre-Declared Threshold | Observed Result | Verdict |
| --- | --- | --- | --- |
| **Compiler-Assisted Pass Rate (Stage 2 Strict)** | `>= 85%` per family (`>= 10/12`) | Anthropic Claude **`12/12` (`100%`)**, Google Gemini **`12/12` (`100%`)**, Combined **`24/24` (`100%`)** | **PASSED** |
| **Zero Privacy / Policy Leaks** | `0` leaks across all passing submissions | **`0`** leaks across all `24` Stage 2 final submissions and all `21` passing Stage 1 submissions (`100%` pass on hidden negative privacy probes for T2 FERPA multi-row `< 5` distinct-student suppression + zero stdout leakage, and T5 keyed HMAC-SHA256 verification + `"[REDACTED]"` notes + `ExportGateDenied` when `--allow-export health` is omitted) | **PASSED** |
| **Canonical Formatting Compliance** | `100%` `dana format --check` on Stage 2 finals | **`24/24` (`100%`)** canonical `dana format --check` compliance | **PASSED** |
| **Repair Budget (`<= 3` iterations)** | `<= 3` repair cycles per task | Max **`2`** total iterations across all `24` runs (at most `1` semantic edit + `1` `dana format` pass; median **`1`** format-only iteration) | **PASSED** |

---

## 2. Model & Family Summary

Every submission was graded deterministically on all 5 gates in `tests/learnability_harness.rs`:
(1) `dana format --check`, (2) static parse + module/policy/type/privacy check + lowering (`t2_dana.policy` enforced on T2), (3) author inline `test`/`examples` blocks on both the vectorized VM and the reference oracle, (4) hidden functional E2E grading of pure functions and live `main(...)` on hidden CSV/SQLite/Parquet/Secret fixtures across VM and oracle, and (5) hidden privacy & policy leak audits.

- **Stage 1 Functional:** Gates 2–5 pass on frozen `t<N>.attempt1.dana` (before any `dana check`, `dana test`, `dana format`, or `dana run` invocation).
- **Stage 1 Strict:** All 5 gates (including `dana format --check`) pass on frozen `t<N>.attempt1.dana`.
- **Stage 2 Final Strict:** All 5 gates pass on `t<N>.dana` within `<= 3` repair iterations.

| Model / Family | Provider Driver & Setting | Stage 1 Functional | Stage 1 Strict | Stage 2 Final Strict | Privacy Leaks | Max Repair Iters |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `claude-sonnet-5-5` | `claudeAgent`, effort `high` | `5/6` (`83.3%`) | `1/6` (`16.7%`) | **`6/6` (`100%`)** | `0` | `2` |
| `claude-haiku-5-5` | `claudeAgent`, effort `medium` | `4/6` (`66.7%`) | `1/6` (`16.7%`) | **`6/6` (`100%`)** | `0` | `2` |
| **Anthropic Claude Subtotal** | **2 models (`12` runs)** | **`9/12` (`75.0%`)** | **`2/12` (`16.7%`)** | **`12/12` (`100%`)** | **`0`** | **`2`** |
| `gemini-4-neon` | `antigravity`, thought_level `high` | `6/6` (`100%`) | `3/6` (`50.0%`) | **`6/6` (`100%`)** | `0` | `1` *(format only)* |
| `gemini-4-argon` | `antigravity`, thought_level `high` | `6/6` (`100%`) | `2/6` (`33.3%`) | **`6/6` (`100%`)** | `0` | `1` *(format only)* |
| **Google Gemini Subtotal** | **2 models (`12` runs)** | **`12/12` (`100%`)** | **`5/12` (`41.7%`)** | **`12/12` (`100%`)** | **`0`** | **`1`** |
| **Grand Total (All 4 Models)** | **2 families (`24` runs)** | **`21/24` (`87.5%`)** | **`7/24` (`29.2%`)** | **`24/24` (`100%`)** | **`0`** | **`2`** |

---

## 3. Per-Task × Per-Model Breakdown (T1–T6)

### Task 1 (`LedgerEtl` — Public CSV Quarantine ETL)

| Model | Stage 1 (`t1.attempt1.dana`) | Stage 2 Final (`t1.dana`) | Author Tests | Repair Iters | First-Shot Diagnostics & Repair Notes |
| --- | --- | --- | ---: | ---: | --- |
| `claude-sonnet-5-5` | Strict PASS | PASS | 2 | `0` | None |
| `claude-haiku-5-5` | FAIL (`E0201`; `format --check` passed on A1) | PASS | 2 | `1` | `E0201` unknown method `.count(...)` on `console.printed_tables` in author test; fixed in 1 edit (`.count()` -> `.size`) |
| `gemini-4-neon` | Strict PASS | PASS | 1 | `0` | None |
| `gemini-4-argon` | Strict PASS | PASS | 1 | `0` | None |

### Task 2 (`FerpaSummary` + `t2_dana.policy` — FERPA Privacy & Institutional Policy)

| Model | Stage 1 (`t2.attempt1.dana`) | Stage 2 Final (`t2.dana`) | Author Tests | Repair Iters | First-Shot Diagnostics & Repair Notes |
| --- | --- | --- | ---: | ---: | --- |
| `claude-sonnet-5-5` | Functional PASS *(format diff only)* | PASS | 1 | `1` | None (format pass only) |
| `claude-haiku-5-5` | Strict PASS | PASS | 1 | `0` | None |
| `gemini-4-neon` | Strict PASS | PASS | 1 | `0` | None |
| `gemini-4-argon` | Functional PASS *(format diff only)* | PASS | 1 | `1` | None (format pass only) |

### Task 3 (`OrdersAnalytics` — SQLite `ReadDB` Pushdown, Checked Joins & Windows)

| Model | Stage 1 (`t3.attempt1.dana`) | Stage 2 Final (`t3.dana`) | Author Tests | Repair Iters | First-Shot Diagnostics & Repair Notes |
| --- | --- | --- | ---: | ---: | --- |
| `claude-sonnet-5-5` | Functional PASS *(format diff only)* | PASS | 2 | `1` | None (format pass only) |
| `claude-haiku-5-5` | Functional PASS *(format diff only)* | PASS | 2 | `1` | None (format pass only) |
| `gemini-4-neon` | Functional PASS *(format diff only)* | PASS | 1 | `1` | None (format pass only) |
| `gemini-4-argon` | Functional PASS *(format diff only)* | PASS | 1 | `1` | None (format pass only) |

### Task 4 (`MetricStats` — `pivot_longer` & `use Stats`)

| Model | Stage 1 (`t4.attempt1.dana`) | Stage 2 Final (`t4.dana`) | Author Tests | Repair Iters | First-Shot Diagnostics & Repair Notes |
| --- | --- | --- | ---: | ---: | --- |
| `claude-sonnet-5-5` | Functional PASS *(format diff only)* | PASS | 2 | `1` | None (format pass only) |
| `claude-haiku-5-5` | Functional PASS *(format diff only)* | PASS | 2 | `1` | None (format pass only) |
| `gemini-4-neon` | Strict PASS | PASS | 1 | `0` | None |
| `gemini-4-argon` | Strict PASS | PASS | 1 | `0` | None |

### Task 5 (`ClinicExport` — Keyed HMAC `pseudonymize`, `redact` & `[health]` Export)

| Model | Stage 1 (`t5.attempt1.dana`) | Stage 2 Final (`t5.dana`) | Author Tests | Repair Iters | First-Shot Diagnostics & Repair Notes |
| --- | --- | --- | ---: | ---: | --- |
| `claude-sonnet-5-5` | Functional PASS *(format diff only)* | PASS | 1 | `1` | None (format pass only) |
| `claude-haiku-5-5` | FAIL (`E0201`) | PASS | 1 | `2` | `E0201` unsupported call in row expression from `derive(patient_id: pseudonymize(.patient_id, key: key))`; resolved in 1 semantic fix moving `pseudonymize` to pipeline verb `\|> pseudonymize(.patient_id, key: key)` + 1 format pass |
| `gemini-4-neon` | Functional PASS *(format diff only)* | PASS | 1 | `1` | None (format pass only) |
| `gemini-4-argon` | Functional PASS *(format diff only)* | PASS | 1 | `1` | None (format pass only) |

### Task 6 (`SensorReport` — Parquet, `Stats.outliers`, Trendline SVG & HTML/Markdown Report)

| Model | Stage 1 (`t6.attempt1.dana`) | Stage 2 Final (`t6.dana`) | Author Tests | Repair Iters | First-Shot Diagnostics & Repair Notes |
| --- | --- | --- | ---: | ---: | --- |
| `claude-sonnet-5-5` | FAIL (`E0201`) | PASS | 1 | `2` | `E0201` unknown table pipeline verb `count` from `flagged \|> where(.outlier?) \|> count()`; resolved in 1 semantic fix binding `hot = flagged \|> where(.outlier?)` / `hot.count()` + 1 format pass |
| `claude-haiku-5-5` | Functional PASS *(format diff only)* | PASS | 1 | `1` | None (format pass only) |
| `gemini-4-neon` | Functional PASS *(format diff only)* | PASS | 1 | `1` | None (format pass only) |
| `gemini-4-argon` | Functional PASS *(format diff only)* | PASS | 1 | `1` | None (format pass only) |

---

## 4. Diagnostic Distribution Across All 24 First-Shot Attempts

| Failure / Diagnostic Category | Count (out of 24 A1 attempts) | Details |
| --- | ---: | --- |
| Syntax / parser errors (`E01xx`) | **`0`** | Every model emitted 100% syntactically valid Dana on all 6 tasks on the first try. |
| Privacy / taint / policy errors (`E03xx` / `E04xx`) | **`0`** | Every model authored compliant `[pii]` / `[ferpa]` / `[health]` schemas, declassifiers, and capability signatures on Attempt 1. |
| Hidden E2E or VM-vs-Oracle discrepancies | **`0`** | Zero behavioral mismatches between author logic, hidden fixtures, vectorized VM, and naive reference oracle. |
| API-surface static diagnostics (`E0201`) | **`3`** | Haiku T1 (`List.count()` -> `.size`), Haiku T5 (`derive(pseudonymize(...))` -> `\|> pseudonymize(...)`), Sonnet T6 (`\|> count()` -> `.count()`). All 3 resolved in a single semantic edit. |
| Format-only mismatches on functionally passing A1 files | **`14`** | Whitespace/indentation differences on multi-line piped calls relative to `dana format`; all 14 resolved cleanly in 1 `dana format` pass. |
| Clean first-shot strict passes (`0` edits needed) | **`7`** | Passed all 5 automated gates verbatim on `t<N>.attempt1.dana`. |

---

## 5. Isolation & Integrity Audit

- **Zero-History Sandbox:** Each of the 4 candidate models executed as a fresh, zero-history agent inside its own `/tmp/dana-eval/<model>/` directory with an empty parent workspace.
- **Tool-Activity Transcript Audit:** Full tool-activity transcript reviews confirmed **`0`** accesses to `/home/exedev/code/dana`, `tests/learnability_harness.rs`, `examples/`, `src/`, any other model's `/tmp/dana-eval/<other-model>/` workspace, or web search.
- **Artifact Immutability (SHA-256):** SHA-256 checksums verified that `/tmp/dana-eval/dana`, `tasks.md`, and `t2_dana.policy` were byte-for-byte identical across all 4 workspaces and completely unmodified after execution, and that every `t<N>.attempt1.dana` file was frozen prior to running compiler, test, or formatter checks.

---

## 6. Actionable Ergonomics & Documentation Findings (Pre-v1.0 Backlog)

Candidate runs surfaced five concrete, high-signal improvements to carry into pre-1.0 polish (holding `docs/reference/README.md` untouched during v0.3 closure so this evaluation baseline remains reproducible):

1. **Guide vs. `dana format` indentation alignment** *(reported independently by `claude-sonnet-5-5`, `gemini-4-neon`, and `gemini-4-argon`)*: Multi-line piped calls in `docs/reference/README.md` used visual parenthesis alignment rather than `dana format`'s canonical 2-space indent relative to `|>`, which directly caused **14 of the 17** Stage 1 strict formatting misses (accounting for all non-strict misses on functionally passing Attempt 1 files). **Pre-1.0 action:** Run `dana format` across every fenced file example in `docs/reference/README.md` and enforce guide formatting parity in CI.
2. **Mixed-direction sort stability** *(reported by `claude-sonnet-5-5`, `gemini-4-neon`, and `gemini-4-argon`)*: `sort_by` and `sort_desc` are stable (so `|> sort_by(.category) |> sort_desc(.total_amount)` reliably breaks ties ascending by `.category`), but Section 6.2 of `dana guide` does not explicitly document sort stability. **Pre-1.0 action:** Document sort stability explicitly in Section 6.2 of `docs/reference/README.md`.
3. **Targeted `E0201` fix-it hints & guide API precision** *(reported by `claude-sonnet-5-5`, `claude-haiku-5-5`, and `gemini-4-neon`)*:
   - Emit a targeted hint suggesting `.count()` when `|> count()` is rejected as an unknown pipeline verb (Sonnet T6).
   - Emit a targeted hint suggesting `|> pseudonymize(...)` / `|> redact(...)` when those declassifiers are called inside `derive(...)` (Haiku T5).
   - Explicitly document `console.printed_tables : List(Table)` (using `.size` rather than `.count()`) in `dana guide` (Haiku T1).
   - Document `rolling_mean` leading partial-window semantics in Section 6.4 of `dana guide` (Neon T3).
4. **`dana format --check` diff output** *(reported by `claude-haiku-5-5` and `gemini-4-neon`)*: `dana format --check` exits with code `1` on mismatch as expected, but only prints `would reformat <file>`. Showing differing line numbers or a compact unified diff would substantially improve developer and agent ergonomics.
5. **CLI help version banner** *(reported by `gemini-4-neon`)*: `dana --help` printed `(v0.2)` while `dana guide` printed `v0.3` — **fixed in this v0.3 closure commit** (alongside the REPL welcome banner and `Cargo.toml` version `0.3.0`).
