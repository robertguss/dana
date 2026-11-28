# Dana v0.7 Prospective AI Learnability Evaluation — Results

> **Status:** Completed — **ALL PRE-DECLARED ACCEPTANCE GATES PASSED**
> **Execution Date:** 2026-11-28
> **Target Release:** Dana **v0.7.2** (pre-1.0 — holding `v1.0` GA for sustained production soak)
> **Prospective Protocol:** [`docs/evals/learnability-v0.7.md`](learnability-v0.7.md)
> **Tested Binary Baseline:** Standalone release copy of `dana v0.7.2` (`/tmp/dana-eval-v07/dana`), embedding `docs/reference/README.md` (`v0.7`) verbatim in `dana guide`
> **Deterministic Grader:** Standalone 5-gate verifier (`grade_v07.py`) testing canonical formatting, static + policy checks, VM & Oracle inline tests, live SQLite `--attach` / local HTTP / UDS / CSV / Parquet / `WriteTable` E2E parity, and `maskkeel` + `dry-run` privacy audits

---

## 1. Pre-Declared Acceptance Gate Outcome: **PASSED**

All four pre-registered v0.7 acceptance criteria in Section 5 of [`docs/evals/learnability-v0.7.md`](learnability-v0.7.md) passed across all 4 models and both vendor families (`16` blind task runs total covering `v0.5–v0.7.2` features):

| Acceptance Criterion | Pre-Declared Threshold | Observed Result | Verdict |
| --- | --- | --- | --- |
| **Compiler-Assisted Pass Rate (Stage 2 Strict)** | `>= 85%` per family (`>= 7/8`) | Anthropic Claude **`8/8` (`100%`)**, Google Gemini **`8/8` (`100%`)**, Combined **`16/16` (`100%`)** | **PASSED** |
| **Zero Privacy / Policy / Secret Leaks** | `0` leaks across all passing submissions | **`0`** leaks across all `16` Stage 2 final submissions and all `15` passing Attempt-1 hidden E2E runs (`100%` pass on T1 `dry-run` secret/network suppression, T2 `0700`/`0600` modes + formula sanitization + `< 5` cell suppression + `maskkeel scan` `pii_columns_found == 0`, and T4 missing-SQLite `dry-run` zero-mutation + `operator_email` stripping) | **PASSED** |
| **Canonical Formatting Compliance** | `100%` `dana format --check` on Stage 2 finals | **`16/16` (`100%`)** canonical `dana format --check` compliance | **PASSED** |
| **Repair Budget (`<= 3` iterations)** | `<= 3` repair cycles per task | Max **`3`** iterations across all `16` runs (all `3`-iteration runs were bisecting T3's `Console.fake().printed_tables` vs. `DynamicTable` assertion in tests; every T1/T2/T4 semantic & formatting fix took `0` or `1` iteration) | **PASSED** |

---

## 2. Model & Family Summary

Every submission was graded deterministically on all 5 gates defined in the protocol:
(1) `dana format --check`, (2) `dana check` + `t2_dana.policy`/`t4_dana.policy`, (3) author inline `test` blocks on **both** `dana test` (VM) and `dana test --oracle`, (4) live hidden E2E parity (`VM == --oracle`) across local HTTP/UDS sockets, CSV/Parquet, `--attach`ed SQLite, and `WriteTable` idempotency, and (5) Gate 5 privacy, policy, and `dry-run` audits.

- **Stage 1 Hidden E2E + Privacy (Gates 2, 4, 5):** Compiles, passes hidden E2E `VM == --oracle`, and passes all Gate 5 privacy/dry-run checks on frozen `t<N>.attempt1.dana` (shown alongside Stage 1 Functional so the T3 `Console.fake().printed_tables` vs. `DynamicTable` spec discrepancy is transparent).
- **Stage 1 Functional (Gates 2–5):** Static check, author tests (VM & Oracle), hidden E2E, and privacy audit on frozen `t<N>.attempt1.dana`.
- **Stage 1 Strict (Gates 1–5):** All 5 gates including `dana format --check` on frozen `t<N>.attempt1.dana`.
- **Stage 2 Final Strict (Gates 1–5):** All 5 gates on `t<N>.dana` within `<= 3` repair iterations.

| Model / Family | Provider Driver & Setting | Stage 1 Hidden E2E | Stage 1 Functional | Stage 1 Strict | Stage 2 Final Strict | Privacy Leaks | Max Repair Iters |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `claude-sonnet-5-5` | `claudeAgent`, effort `high` | `4/4` (`100%`) | `3/4` (`75.0%`) | `1/4` (`25.0%`) | **`4/4` (`100%`)** | `0` | `1` |
| `claude-haiku-5-5` | `claudeAgent`, effort `medium` | `3/4` (`75.0%`) | `2/4` (`50.0%`) | `0/4` (`0.0%`) | **`4/4` (`100%`)** | `0` | `1` *(excl. 3 probe runs)* |
| **Anthropic Claude Subtotal** | **2 models (`8` runs)** | **`7/8` (`87.5%`)** | **`5/8` (`62.5%`)** | **`1/8` (`12.5%`)** | **`8/8` (`100%`)** | **`0`** | **`1`** |
| `gemini-4-neon` | `antigravity`, thought_level `high` | `4/4` (`100%`) | `3/4` (`75.0%`) | `0/4` (`0.0%`) | **`4/4` (`100%`)** | `0` | `3` *(T3 test only)* |
| `gemini-4-argon` | `antigravity`, thought_level `high` | `4/4` (`100%`) | `3/4` (`75.0%`) | `0/4` (`0.0%`) | **`4/4` (`100%`)** | `0` | `3` *(T3 test only)* |
| **Google Gemini Subtotal** | **2 models (`8` runs)** | **`8/8` (`100%`)** | **`6/8` (`75.0%`)** | **`0/8` (`0.0%`)** | **`8/8` (`100%`)** | **`0`** | **`3`** |
| **Grand Total (All 4 Models)** | **2 families (`16` runs)** | **`15/16` (`93.8%`)** | **`11/16` (`68.8%`)** | **`1/16` (`6.25%`)** | **`16/16` (`100%`)** | **`0`** | **`3`** |

---

## 3. Per-Task × Per-Model Breakdown (T1–T4)

### Task 1 (`ModbCatalogBridge` — `LocalHttpAllow`, `LocalSocketAllow`, Typed JSON `struct`, `List.join`, `JsonResponse.has?`)

| Model | Stage 1 (`t1.attempt1.dana`) | Stage 2 Final (`t1.dana`) | Repair Iters | First-Shot Diagnostics & Repair Notes |
| --- | --- | --- | ---: | --- |
| `claude-sonnet-5-5` | Functional PASS *(format diff only)* | PASS | `1` | Format diff on single-line `items \|> where(...) \|> sort_by(...)`; 1 `dana format` pass |
| `claude-haiku-5-5` | Functional PASS *(format diff only)* | PASS | `1` | Format diff on long `sync_catalog(...)` signature line; 1 `dana format` pass |
| `gemini-4-neon` | Functional PASS *(format diff only)* | PASS | `1` | Format diff on wrapped `CatalogItemBody(...)` constructor; 1 `dana format` pass |
| `gemini-4-argon` | Functional PASS *(format diff only)* | PASS | `1` | Format diff on wrapped `CatalogItemBody(...)` constructor; 1 `dana format` pass |

### Task 2 (`FerpaSafeCohort` + `t2_dana.policy` — `pseudonymize`, `dedupe_by`, `coarsen`, `:half_even`, `suppress_small_cells`, Private CSV/Parquet)

| Model | Stage 1 (`t2.attempt1.dana`) | Stage 2 Final (`t2.dana`) | Repair Iters | First-Shot Diagnostics & Repair Notes |
| --- | --- | --- | ---: | --- |
| `claude-sonnet-5-5` | **Strict PASS** | PASS | `0` | Passed all 5 gates verbatim on Attempt 1 (`0` edits needed) |
| `claude-haiku-5-5` | Functional PASS *(format diff only)* | PASS | `1` | Format diff on long `main(...)` signature line; 1 `dana format` pass |
| `gemini-4-neon` | Functional PASS *(format diff only)* | PASS | `1` | Format diff on wrapped `files.read_csv(...)` call; 1 `dana format` pass |
| `gemini-4-argon` | Functional PASS *(format diff only)* | PASS | `1` | Format diff on wrapped `files.read_csv(...)` call; 1 `dana format` pass |

### Task 3 (`SqlitePushdownRollup` — SQLite `--attach`, `try_parse_date` Pushdown, `:half_even`, Mixed Sort, `crosstab`)

Note: All 4 models' `t3.attempt1.dana` production functions (`region_channel_summary` and `main`) passed `dana check`, `dana explain --dialect sqlite`, and hidden E2E execution (`VM == --oracle`) verbatim on Attempt 1. All 4 models' Attempt-1 author tests hit `PromiseViolation: assertion failed` on `console.printed_tables.size == 2` because `Console.fake().printed_tables` captures plain `Table` prints (`summary`) while omitting `DynamicTable` (`ct` from `crosstab`), even though `console.print_table(ct)` renders `ct` into `console.printed_lines`. All 4 models independently diagnosed the discrepancy and adjusted their Stage 2 test assertion to `console.printed_tables.size == 1` + `console.printed_lines` checks while leaving `main` and `region_channel_summary` faithful to the spec.

| Model | Stage 1 (`t3.attempt1.dana`) | Stage 2 Final (`t3.dana`) | Repair Iters | First-Shot Diagnostics & Repair Notes |
| --- | --- | --- | ---: | --- |
| `claude-sonnet-5-5` | Hidden E2E PASS; author `test` FAIL (`PromiseViolation`) | PASS | `1` | Formatted cleanly on A1; bisected `printed_tables.size == 2` -> `== 1` + `printed_lines.size == 3` in 1 edit |
| `claude-haiku-5-5` | Hidden E2E PASS; author `test` FAIL (`PromiseViolation`, format diff) | PASS | `1` | Bisected via 3 excluded probe files (`t3_probe*.tmp.dana`), updated `== 2` -> `== 1` + `dana format` |
| `gemini-4-neon` | Hidden E2E PASS; author `test` FAIL (`PromiseViolation`) | PASS | `3` | Formatted cleanly on A1; 3 test-assertion bisection iterations (`== 2` -> `== 1` + `printed_lines`) |
| `gemini-4-argon` | Hidden E2E PASS; author `test` FAIL (`PromiseViolation`) | PASS | `3` | Formatted cleanly on A1; 3 test-assertion bisection iterations (`== 2` -> `== 1` + `printed_lines`) |

### Task 4 (`JsonBodyAndDryRunGuard` + `t4_dana.policy` — Policy-Gated `LocalHttpAllow`, Nested `fields:`, `WriteTable`, `Json.encode`, `has?`)

| Model | Stage 1 (`t4.attempt1.dana`) | Stage 2 Final (`t4.dana`) | Repair Iters | First-Shot Diagnostics & Repair Notes |
| --- | --- | --- | ---: | --- |
| `claude-sonnet-5-5` | Functional PASS *(format diff only)* | PASS | `1` | Format diff on long `main(...)` signature line; 1 `dana format` pass |
| `claude-haiku-5-5` | FAIL (`E0201` ×2 + format diff) | PASS | `1` | `E0201` in author test (`clean \|> where(...) \|> count()` instead of `.count()`); fixed + `dana format` in 1 cycle |
| `gemini-4-neon` | Functional PASS *(format diff only)* | PASS | `1` | Format diff on wrapped `responses: { ... }` map literal; 1 `dana format` pass |
| `gemini-4-argon` | Functional PASS *(format diff only)* | PASS | `1` | Format diff on wrapped `responses: { ... }` map literal; 1 `dana format` pass |

---

## 4. Diagnostic Distribution Across All 16 First-Shot Attempts

| Failure / Diagnostic Category | Count (out of 16 A1 attempts) | Details |
| --- | ---: | --- |
| Syntax / parser errors (`E01xx`) | **`0`** | Every model emitted 100% syntactically valid Dana on all 4 tasks on Attempt 1. |
| Privacy / taint / policy errors (`E0202` / `E03xx` / `E04xx`) | **`0`** | Every model handled `pseudonymize`-before-`dedupe_by`, `coarsen`, `.round_to`, `suppress_small_cells`, `shuffle`, `[pii]` stripping, and `t2_dana.policy` / `t4_dana.policy` ceilings cleanly on Attempt 1. |
| Hidden E2E or VM-vs-Oracle discrepancies | **`0`** | Zero behavioral mismatches between any passing Attempt-1/Stage-2 module, hidden fixtures, vectorized VM, SQLite `--attach` pushdown, and reference oracle. |
| Static API-surface diagnostics (`E0201`) | **`1`** | `claude-haiku-5-5` T4 author test (`\|> count()` instead of `.count()`), resolved cleanly in 1 edit. |
| Spec/runtime `Console.fake` discrepancy in author T3 tests | **`4`** | All 4 models hit `PromiseViolation: assertion failed` on `console.printed_tables.size == 2` because `DynamicTable` (`crosstab`) writes to `printed_lines` but not `printed_tables`. |
| Format-only mismatches on passing Attempt-1 code | **`11`** | Line-wrapping / `\|>` collapse differences relative to `dana format` (including T1/T2/T4 across Haiku/Neon/Argon, T1/T4 on Sonnet, and Haiku T3 table alignment); all resolved cleanly via `dana format`. |
| Clean first-shot strict passes (`0` edits needed) | **`1`** | `claude-sonnet-5-5` T2 (`FerpaSafeCohort`). |

---

## 5. Isolation, Integrity & Grader Transparency Audit

- **Zero-History Sandbox:** Each of the 4 candidate models ran as a fresh, zero-history delegated agent inside its own `/tmp/dana-eval-v07/<model>/` directory.
- **Artifact Immutability (SHA-256):** `sha256sum -c /tmp/dana-eval-v07/baseline.sha256` passed `16/16` (`OK`) after all runs finished, confirming `/tmp/dana-eval-v07/dana`, `tasks.md`, `t2_dana.policy`, and `t4_dana.policy` were untouched across all workspaces, and all `t<N>.attempt1.dana` files remained frozen prior to running compiler checks.
- **Child Thread Tool-Activity Audit:** Full activity transcript audits across all 4 threads confirmed **`0`** accesses to `/home/exedev/code/dana`, `grade_v07.py`, any sibling model workspace, or web search. *(Transparency note: `claude-sonnet-5-5` initially began copying `t3.dana` into its runtime scratchpad during T3 assertion bisection, immediately recognized its isolation boundary, deleted the scratchpad copy, and bisected in-place within `/tmp/dana-eval-v07/claude-sonnet-5-5/`.)*
- **Grader Fixes After Run Completion (Untouched Submissions):** Initial execution of `grade_v07.py` surfaced two bugs strictly inside the Python test harness (`grade_t2` passed an unquoted comma `=SUM(1,2)` in the hidden CSV fixture and asserted `len(tok) == 64` whereas Dana's `src/formats/crypto.rs` produces 35-char `ps_<32-hex>` HMAC tokens). Both grader assertions were corrected in `grade_v07.py` and re-run against the completely unmodified model files.

---

## 6. Actionable Pre-`v1.0` Ergonomics & Documentation Findings (Queued for `v0.7.3`)

Holding `v0.7.2` frozen to the tested binary and guide, all 4 models surfaced clear, convergent ergonomics improvements to address in `v0.7.3` before `v1.0` GA:

1. **`Console.fake().printed_tables` omits `DynamicTable` (`crosstab`)** *(reported independently by all 4 models)*:
   Passing a `DynamicTable` to `console.print_table(ct)` formats it to `console.printed_lines` without recording an entry in `console.printed_tables`. Either populate `printed_tables` (or add a dedicated accessor) or document this explicitly in `dana guide` §6.5 & §10.
2. **Line numbers & evaluated diffs on `PromiseViolation: assertion failed` in `dana test`** *(reported independently by all 4 models)*:
   Failed `assert` statements currently report only `PromiseViolation: assertion failed` without file:line location, expression text, or LHS/RHS values, forcing models to bisect assertions with temporary probe files (accounting for every `> 1`-iteration run in this eval).
3. **In-memory test fakes for `WriteFiles` and `WriteTable`** *(reported independently by all 4 models)*:
   Because `WriteFiles` and `WriteTable` have no `in_memory` / `.fake(...)` constructors yet, models cannot call `main(...)` directly inside `dana test` for file/database write pipelines (T2 and T4).
4. **Document formatter wrapping / pipeline layout & Decimal interpolation formatting in `dana guide`** *(reported by `claude-sonnet-5-5`, `claude-haiku-5-5`, and `gemini-4-neon`)*:
   Brief examples in `dana guide` of when `dana format` collapses calls vs. wraps pipelines onto one `|>` stage per line — plus noting trailing-zero trimming on interpolated `Decimal` values (`320.00` -> `320`) — would eliminate the remaining format-only Stage 1 misses and string-check surprises.
