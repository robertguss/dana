# Dana v0.7 Prospective AI Learnability Evaluation Protocol

> **Status:** Prospective Pre-Registration (Pre-Execution)
> **Target Release:** Dana **v0.7.2** (pre-1.0 — holding `v1.0` GA for sustained production soak)
> **Reference Specification Baseline:** `docs/reference/README.md` (`v0.7`, embedded verbatim in `dana guide` for `v0.7.2`)
> **Deterministic Grading Script:** Standalone `grade_v07.py` executing offline + hidden E2E VM/Oracle/SQLite/TCP/UDS/maskkeel suites
> **Results Report (Post-Execution):** `docs/evals/learnability-v0.7-results.md` *(to be written ONLY after live multi-family model runs complete; zero placeholder results appear in this protocol document)*

---

## 1. Objective

Verify prospectively that fresh, zero-history AI coding agents from two independent model families can write correct, idiomatic, privacy-compliant, canonically formatted **Dana v0.7 (`v0.7.2`)** data pipelines covering the **v0.5–v0.7.2** feature surface on **4 unseen real-world tasks** using **only** the embedded `dana guide` language reference and Dana's compiler/test/format diagnostics—with zero access to the Dana repository, examples, or grading scripts.

Whereas [`docs/evals/learnability-v0.3.md`](learnability-v0.3.md) evaluated Dana's `v0.3` core surface, this `v0.7` evaluation specifically targets features introduced in `v0.5` through `v0.7.2`:
- **T1 (`ModbCatalogBridge`):** `LocalHttpAllow(MoCatalog)`, `LocalSocketAllow(MoAudit)`, `Secret(...)`, typed `struct` JSON bodies (`Decimal` exact string encoding), `List(Text).join(",")`, `JsonResponse.has?("result.batch_id")`, and `LocalHttp.fake`/`LocalSocket.fake`.
- **T2 (`FerpaSafeCohort` + `t2_dana.policy`):** `dana.policy`, `read_csv(..., on_bad_rows: :quarantine, coerce_integral_floats: true)`, `pseudonymize` before `dedupe_by`, `coarsen`, `bucket`, `.round_to(0.5, mode: :half_even)`, row-level k-anonymity `suppress_small_cells`, `shuffle(seed: 42)`, atomic private `write_csv(..., private: true, sanitize_formulas: true)`, and `write_parquet(..., private: true)`.
- **T3 (`SqlitePushdownRollup`):** SQLite `--attach` (`from: "sales.ticket"` + `from: "store"`), exact proleptic Gregorian `.try_parse_date` SQL pushdown, `join_many_to_one`, post-aggregate `summarize` with `count_if` and `.round(2, mode: :half_even)`, mixed-direction `sort_by(desc(...), asc(...))`, and `crosstab` printed via `console.print_table`.
- **T4 (`JsonBodyAndDryRunGuard` + `t4_dana.policy`):** `dana.policy` with named `LocalHttpAllow(FeedApi)`, nested JSON `fields:` path+index mapping (`"geo.coords.0"`), `[pii]` stripping, `WriteTable(OpsDb, "events")` idempotent upsert + zero-mutation `dry-run` on missing SQLite files, `Json.encode`, and `JsonResponse.has?("ack.id")` guarding `dry-run`.

---

## 2. Information Boundary & Isolation Rules

Every candidate model runs as a fresh, zero-history agent inside an isolated temporary directory:

```text
/tmp/dana-eval-v07/<model>/
```

### Permitted Inputs (Exclusive)

Each candidate agent has access **only** to:

1. A standalone release binary copy of `dana v0.7.2` at `/tmp/dana-eval-v07/dana`, reading the Dana specification **exclusively** via `/tmp/dana-eval-v07/dana guide` (and `/tmp/dana-eval-v07/dana guide <section>`).
2. The standalone 4-task specification packet (`tasks.md`, Section 6.3 below) and the two institutional policy files (`t2_dana.policy` in Section 6.1 and `t4_dana.policy` in Section 6.2).
3. Compiler, test, formatter, and runtime feedback from `/tmp/dana-eval-v07/dana` (`check`, `test`, `format`) on the agent's own files inside `/tmp/dana-eval-v07/<model>/`, **only after** freezing Stage 1 (`t<N>.attempt1.dana`).

### Explicit Prohibitions

Candidate agents **must not**:

- Read, list, search, or inspect `/home/exedev/code/dana` or any other directory outside `/tmp/dana-eval-v07/<model>/`.
- Read any hidden grading script or any other model's `/tmp/dana-eval-v07/<other-model>/` workspace.
- Search the web or fetch external documentation or source code for Dana.
- Modify `tasks.md`, `t2_dana.policy`, `t4_dana.policy`, or `/tmp/dana-eval-v07/dana`.

---

## 3. Model Matrix (4 Models Across 2 Families)

| Family | Provider Driver | Model Identifier | Options / Tier |
| --- | --- | --- | --- |
| Anthropic Claude | `claudeAgent` | `claude-sonnet-5-5` | `effort: "high"` (Frontier balanced) |
| Anthropic Claude | `claudeAgent` | `claude-haiku-5-5` | `effort: "medium"` (Fast / compact) |
| Google Gemini | `antigravity` | `gemini-4-neon` | `thought_level: "high"` (Frontier reasoning) |
| Google Gemini | `antigravity` | `gemini-4-argon` | `thought_level: "high"` (Fast / compact) |

---

## 4. Two-Stage Scoring Protocol

For each task `N ∈ {1, 2, 3, 4}`:

### Stage 1 — First-Shot Pass Rate (`t<N>.attempt1.dana`)

1. The model reads `/tmp/dana-eval-v07/dana guide`, `tasks.md`, `t2_dana.policy`, and `t4_dana.policy`.
2. **Before** invoking `dana check`, `dana test`, `dana format`, or `dana run` on task `N`, the model writes its complete initial solution to:
   ```text
   /tmp/dana-eval-v07/<model>/t<N>.attempt1.dana
   ```
3. `t<N>.attempt1.dana` is frozen immediately once written and never overwritten.
4. The deterministic grader (`grade_v07.py`) grades `t<N>.attempt1.dana` across all 5 automated gates, reporting both **Stage 1 Functional** (Gates 2–5 independent of whitespace) and **Stage 1 Strict** (Gates 1–5 including `dana format --check`).

### Stage 2 — Compiler-Assisted Pass Rate (`t<N>.dana`, `<= 3` Repair Iterations)

1. Starting from `t<N>.attempt1.dana`, the model copies/edits into `t<N>.dana` and may execute up to **3 repair iterations** using **only** diagnostics from `/tmp/dana-eval-v07/dana check`, `test`, and `format --check` / `format` (passing `--policy t2_dana.policy` on T2 and `--policy t4_dana.policy` on T4).
2. Each repair iteration counts as one diagnostic-to-edit cycle (max `3` cycles; iteration `0` means `t<N>.attempt1.dana` already passed all local checks and formatting cleanly).
3. Final submissions `t1.dana` .. `t4.dana` and frozen Stage 1 files `t1.attempt1.dana` .. `t4.attempt1.dana` are graded offline and end-to-end by `grade_v07.py`.

### Automated Five-Gate Grading Rubric (Per Submission)

1. **Canonical Formatting (`format --check`):** `dana format --check` exits `0`.
2. **Static Check & Policy (`check`):** `dana check` succeeds with `0` diagnostics (enforcing `--policy t2_dana.policy` on T2 and `--policy t4_dana.policy` on T4), and verifies required module/schema/struct/function definitions.
3. **Author Unit Tests (`test` & `test --oracle`):** At least one `test` block exists, and `dana test` passes on **both** the vectorized VM and `--oracle` (enforcing policy on T2/T4).
4. **Hidden Functional E2E (`VM == Oracle`):** Live execution against hidden fixtures across **both** the vectorized VM (`dana run`) and reference oracle (`dana run --oracle`):
   - **T1:** Live local HTTP server (`--local-http MoCatalog=...`) + live local Unix domain socket server (`--local-socket MoAudit=...`) + `CATALOG_TOKEN=...` verifying filtered/sorted item order, exact `"price":"19.5"` Decimal string JSON body, `Authorization: Bearer ...` header, `skus_csv`, `has_batch_id`, and exact stdout `PUSHED=... SKUS=... HAS_BATCH=...`.
   - **T2:** Live hidden `cohort.csv` containing integral float `25.0` in `age_years`, formula injection `=SUM(1,2)` in `notes`, negative value `-5` in `notes`, duplicate `student_id` rows (keeping higher `credits_earned`), a `< 5` equivalence cell (dropped), and a bad row (`bad == 1`), verifying `KEPT=... BAD=1`, sanitized `'=SUM(1,2)` and preserved `-5`, rounded `:half_even` `.gpa_band`, and valid `cohort.parquet` + `cohort.csv` output.
   - **T3:** Live hidden SQLite `main.db` (`store`) + `--attach sales=sales.db` (`ticket`) with invalid date `"2026-02-29"` (dropped), exact `:half_even` tie rounding (`0.625 -> 0.62`, `0.375 -> 0.38`), mixed-direction sorting, `crosstab` matrix printed cleanly, `dana explain --dialect sqlite` verifying SQL pushdown (`TRY_PARSE_DATE` / `SUBSTR` / `JOIN`), and byte-identical `VM == --oracle` stdout.
   - **T4:** Live Pass 1 (insert) and Pass 2 (idempotency unchanged) against local HTTP `FeedApi` + SQLite `OpsDb`, verifying nested `"geo.coords.0"` / `"geo.coords.1"` extraction, `AckPayload` JSON body on `/ack`, `UPSERT=3/0/0 ACK=true` -> `UPSERT=0/0/3 ACK=true`, and `VM == --oracle` parity.
5. **Hidden Privacy, Policy & Dry-Run Audit:**
   - **T1:** `dana dry-run` executes `POST` suppression without calling `/items` or `/audit/catalog`, exits `0`, prints `HAS_BATCH=false`, and leaks `0` occurrences of the `CATALOG_TOKEN` secret value.
   - **T2:** `private_out/` has `0700` mode, `cohort.csv` and `cohort.parquet` have `0600` mode, `0` raw `student_id` or `email` values or rare-cohort records appear in `cohort.csv`/`cohort.parquet`/stdout, and `maskkeel scan` reports `pii_columns_found == 0`.
   - **T4:** `dana dry-run` on a non-existent `fresh_dir/store.sqlite` leaves `fresh_dir` completely uncreated (`!exists`), emits `0` internal `float64(`/`date(` wrappers, intercepts `POST /ack` (`ACK=false`), and `0` `operator_email` values appear in stdout or SQLite.

---

## 5. Pre-Declared v0.7 Acceptance Gate Criteria

To pass the **Dana v0.7.2** AI Learnability Gate, live multi-family results must satisfy ALL of the following:

1. **Compiler-Assisted Pass Rate:** `>= 85%` per model family (`>= 7/8` per family across `4` tasks × `2` models) on Stage 2 final submissions (`t1.dana`..`t4.dana`), where a pass requires all 5 grading gates to succeed.
2. **Zero Privacy / Policy Leaks:** `0` privacy, policy, or secret leaks across all passing submissions (`100%` pass on Gate 5 across T1, T2, and T4).
3. **100% Canonical Formatting Compliance:** `100%` `dana format --check` compliance across all passing Stage 2 final submissions.
4. **Full Transparency Reporting:** `docs/evals/learnability-v0.7-results.md` must report exact Stage 1 vs. Stage 2 pass rates per model and family, per-task diagnostics, repair iteration counts (`0..=3`), isolation/SHA-256 verification, and any newly surfaced pre-`v1.0` ergonomics findings.

---

## 6. Standalone Evaluation Packet (`t2_dana.policy`, `t4_dana.policy`, `tasks.md`)

### 6.1 `t2_dana.policy`

<!-- BEGIN T2_DANA_POLICY -->
```text
version 1
min_group_size 5
forbid manual_declassify
forbid repl_show_sensitive
allow console tags []
allow export "private_out/" tags []
```
<!-- END T2_DANA_POLICY -->

### 6.2 `t4_dana.policy`

<!-- BEGIN T4_DANA_POLICY -->
```text
version 1
forbid manual_declassify
allow console tags []
allow local_http FeedApi tags []
allow write OpsDb.events tags []
```
<!-- END T4_DANA_POLICY -->

### 6.3 `tasks.md`

<!-- BEGIN STANDALONE TASKS.MD -->
# Dana v0.7 Unseen Task Suite (T1–T4)

Implement all 4 standalone Dana modules in your current working directory (`t1.dana` through `t4.dana`).

## Rules

1. Read the Dana language reference **exclusively** via `/tmp/dana-eval-v07/dana guide` (and `/tmp/dana-eval-v07/dana guide <section>`). Do not access `/home/exedev/code/dana`, any other directory, or web search.
2. For each task `N` (`1..=4`):
   - **First**, write your complete initial solution to `t<N>.attempt1.dana` **before** running `/tmp/dana-eval-v07/dana` (`check`, `test`, `format`, or `run`) on task `N`. **Never overwrite `t<N>.attempt1.dana` afterward.**
   - **Next**, copy `t<N>.attempt1.dana` to `t<N>.dana` and use only `/tmp/dana-eval-v07/dana check` (passing `--policy t2_dana.policy` for T2 and `--policy t4_dana.policy` for T4), `/tmp/dana-eval-v07/dana test`, and `/tmp/dana-eval-v07/dana format` to repair any errors in up to **3 repair iterations**.
   - Ensure every final `t<N>.dana` passes `dana format --check`, `dana check`, and `dana test`.
3. Follow every module name, schema name, struct name, field/column name, type, sensitivity tag, constraint, function signature, `main` signature, and printed output format **exactly** as specified below; an automated hidden test suite grades both your frozen `.attempt1.dana` files and your final `t<N>.dana` files.
4. Record your exact repair iteration count (`0..=3`), diagnostic codes encountered, and any `dana guide` / compiler friction in `notes.md`.

---

## Task 1 (`t1.dana`, `module ModbCatalogBridge`) — Local HTTP + UDS Bridge, Typed JSON Bodies, `List.join`, and `JsonResponse.has?`

- **Module:** `module ModbCatalogBridge`
- **Schema:** `schema RawProduct`
  - `sku: Text where not .empty?`
  - `name: Text where not .empty?`
  - `price: Decimal where . > 0.00`
  - `stock: Int where . >= 0`
- **Structs:**
  - `struct CatalogItemBody`
    - `sku: Text`
    - `name: Text`
    - `price: Decimal`
    - `stock: Int`
  - `struct AuditReceipt`
    - `pushed_count: Int`
    - `skus_csv: Text`
    - `has_batch_id: Bool`
- **Function:**
  - Exact signature:
    `fn sync_catalog(files: ReadFiles, mo: LocalHttpAllow(MoCatalog), audit: LocalSocketAllow(MoAudit), token: Secret("catalog_token"), path: Text) : Result(AuditReceipt, Text)`
  - Behavior:
    1. Load `(items, _bad) = try files.read_csv(path, as: RawProduct)`.
    2. Keep rows with `.stock > 0` and sort ascending by `.sku`.
    3. Initialize `var skus = []` and `var last_has_batch = false`.
    4. For each row in the filtered, sorted table (`for item in ...`):
       - Construct `CatalogItemBody(sku: item.sku, name: item.name, price: item.price, stock: item.stock)`.
       - POST it via `resp = try mo.post_json("/items", body: body, headers: {"Authorization": "Bearer #{token}"})`.
       - Update `last_has_batch = resp.has?("result.batch_id")`.
       - Append `item.sku` via `skus = skus.append(item.sku)`.
    5. Construct `receipt = AuditReceipt(pushed_count: skus.size, skus_csv: skus.join(","), has_batch_id: last_has_batch)`.
    6. POST `receipt` via `_ack = try audit.post_json("/audit/catalog", body: receipt)`.
    7. Return `Ok(receipt)`.
- **Entry Point:**
  - Exact signature:
    `fn main(args: Args, files: ReadFiles, mo: LocalHttpAllow(MoCatalog), audit: LocalSocketAllow(MoAudit), token: Secret("catalog_token"), console: Console) : Int`
  - Behavior:
    1. Obtain CSV path via `path = args.first.or_return(2)`.
    2. Run `receipt = try sync_catalog(files, mo, audit, token, path)`.
    3. Print exact single line:
       `console.print("PUSHED=#{receipt.pushed_count} SKUS=#{receipt.skus_csv} HAS_BATCH=#{receipt.has_batch_id}")`
    4. Return `0`.
- **Tests:** Include at least one `test` block exercising `sync_catalog` / `main` with `Files.in_memory`, `LocalHttp.fake(MoCatalog, ...)`, `LocalSocket.fake(MoAudit, ...)`, `Secret.fake(...)`, and `Console.fake()`.

---

## Task 2 (`t2.dana`, `module FerpaSafeCohort`) — Policy-Gated FERPA `suppress_small_cells`, `coarsen`, `:half_even`, and Private Sanitized Exports

- **Module:** `module FerpaSafeCohort`
- **Policy:** Must pass `dana check --policy t2_dana.policy t2.dana` and `dana test --policy t2_dana.policy t2.dana` against `t2_dana.policy`.
- **Schema:** `schema RawEnrollment`
  - `student_id: Int [pii]`
  - `email: Text [pii] where .contains?("@")`
  - `major: Text [ferpa]`
  - `age_years: Int [ferpa] where . >= 16`
  - `gpa: Float [ferpa] where . >= 0.0 and . <= 4.0`
  - `credits_earned: Int where . >= 0`
  - `notes: Text`
- **Pure Function:**
  - Signature:
    `fn prepare_cohort(rows: Table(RawEnrollment), salt: Secret("cohort_salt"))` *(let Dana infer the declassified return table type)*
  - Exact pipeline behavior (in privacy-safe order):
    1. `|> pseudonymize(.student_id, key: salt)`
    2. `|> rename(student_token: .student_id)`
    3. `|> drop(.email)`
    4. `|> dedupe_by(.student_token, order_by: [desc(.credits_earned)], keep: :first)`
    5. `|> derive(major_group: coarsen(.major, allow: ["MDiv", "MATS"], other: "Other"), age_band: bucket(.age_years, cuts: [25, 35], labels: ["under_25", "25_34", "35_plus"]), gpa_band: .gpa.round_to(0.5, mode: :half_even))`
    6. `|> select(.student_token, .major_group, .age_band, .gpa_band, .credits_earned, .notes)`
    7. `|> suppress_small_cells(by: [.major_group, .age_band], min: 5, distinct_by: .student_token)`
    8. `|> shuffle(seed: 42)`
- **Entry Point:**
  - Exact signature:
    `fn main(args: Args, files: ReadFiles, salt: Secret("cohort_salt"), out: WriteFiles("private_out/"), console: Console) : Int`
  - Behavior:
    1. Obtain CSV path via `path = args.first.or_return(2)`.
    2. Load `(rows, bad) = try files.read_csv(path, as: RawEnrollment, on_bad_rows: :quarantine, coerce_integral_floats: true)`.
    3. Compute `safe = prepare_cohort(rows, salt)`.
    4. Write `try out.write_csv("cohort.csv", safe, private: true, sanitize_formulas: true)`.
    5. Write `try out.write_parquet("cohort.parquet", safe, private: true)`.
    6. Print `console.print("KEPT=#{safe.count()} BAD=#{bad.count()}")`.
    7. Return `0`.
- **Tests:** Include at least one `test` block using `Secret.fake(...)` verifying deduplication (keeping highest `credits_earned`), `coarsen`, `:half_even` `.round_to(0.5, mode: :half_even)`, and suppression of `< 5`-student cells.

---

## Task 3 (`t3.dana`, `module SqlitePushdownRollup`) — Attached SQLite, `try_parse_date` Pushdown, Post-Agg `:half_even`, Mixed Sort, and `crosstab`

- **Module:** `module SqlitePushdownRollup`
- **Schemas:**
  - `schema Store`
    - `store_id: Int`
    - `region: Text`
  - `schema SalesTicket`
    - `ticket_id: Int`
    - `store_id: Int`
    - `channel: Text`
    - `raw_date: Text`
    - `amount: Decimal where . > 0.00`
    - `paid: Bool`
- **Function:**
  - Signature: `fn region_channel_summary(db: ReadDB(Retail))` *(keep the pipeline rooted at `db.table(...)` so SQL pushdown activates cleanly)*
  - Behavior:
    1. Read `db.table(SalesTicket, from: "sales.ticket")` and `db.table(Store, from: "store")`. *(Hint for tests: `DB.in_memory(Retail, {"store": stores_tbl, "sales.ticket": tickets_tbl})` matches `from:` table names directly.)*
    2. Derive `parsed_date: .raw_date.try_parse_date` and filter `where(.parsed_date.some?)`.
    3. Join stores via `|> join_many_to_one(db.table(Store, from: "store"), on: .store_id)`.
    4. Group by `.region, .channel`.
    5. Summarize:
       - `orders: count()`
       - `paid_orders: count_if(.paid)`
       - `total_amount: sum(.amount)`
       - `paid_rate: (count_if(.paid).to_decimal / count().to_decimal).round(2, mode: :half_even)`
    6. Sort via `|> sort_by(desc(.total_amount), asc(.region), asc(.channel))`.
- **Entry Point:**
  - Exact signature: `fn main(db: ReadDB(Retail), console: Console) : Int`
  - Behavior:
    1. Compute `summary = region_channel_summary(db)`.
    2. Print `console.print_table(summary)`.
    3. Compute `ct = summary |> crosstab(rows: .region, cols: .channel, values: .orders, fill: 0)` and print `console.print_table(ct)`.
    4. Print exact summary line `console.print("GROUPS=#{summary.count()} TOTAL=#{summary.sum(.total_amount)}")`.
    5. Return `0`.
- **Tests:** Include at least one `test` block using `DB.in_memory(Retail, {"store": ..., "sales.ticket": ...})` and `Console.fake()` verifying invalid date `"2026-02-29"` is excluded, `:half_even` tie rounding (`5/8 -> 0.62`, `3/8 -> 0.38`), ordering, and `console.printed_tables.size == 2`.

---

## Task 4 (`t4.dana`, `module JsonBodyAndDryRunGuard`) — Policy-Gated `LocalHttpAllow`, Nested JSON Mapping, `WriteTable`, `Json.encode`, and `dry-run` Guard

- **Module:** `module JsonBodyAndDryRunGuard`
- **Policy:** Must pass `dana check --policy t4_dana.policy t4.dana` and `dana test --policy t4_dana.policy t4.dana` against `t4_dana.policy`.
- **Schema:** `schema FeedEvent`
  - `event_id: Text where not .empty?`
  - `event_date: Date`
  - `score: Float`
  - `lon: Float`
  - `lat: Float`
  - `operator_email: Text [pii] where .contains?("@")`
- **Struct:** `struct AckPayload`
  - `event_count: Int`
  - `inserted: Int`
  - `updated: Int`
  - `unchanged: Int`
- **Entry Point:**
  - Exact signature:
    `fn main(feed: LocalHttpAllow(FeedApi), events_out: WriteTable(OpsDb, "events"), console: Console) : Int`
  - Behavior:
    1. Fetch `resp = try feed.get_json("/events")`.
    2. Parse `(raw_events, _bad) = resp.parse_table("events", as: FeedEvent, fields: {"lon": "geo.coords.0", "lat": "geo.coords.1"})`.
    3. Strip `[pii]` and sort deterministically: `clean = raw_events |> select(.event_id, .event_date, .score, .lon, .lat) |> sort_by(.event_id)`.
    4. Upsert into SQLite: `stats = try events_out.upsert(clean, key: .event_id)`.
    5. Encode `payload = AckPayload(event_count: clean.count(), inserted: stats.inserted, updated: stats.updated, unchanged: stats.unchanged)` via `ack_json = Json.encode(payload)`.
    6. POST `ack_resp = try feed.post_json("/ack", body: ack_json)`.
    7. Probe `acked = ack_resp.has?("ack.id")` (safe under both live responses and `dry-run` `null` stubs).
    8. Print `console.print("UPSERT=#{stats.inserted}/#{stats.updated}/#{stats.unchanged} ACK=#{acked}")`.
    9. Return `0`.
- **Tests:** Include at least one `test` block exercising nested `"geo.coords"` `parse_table`, stripping `operator_email: [pii]`, and `Json.encode(AckPayload(...))` with `LocalHttp.fake(FeedApi, ...)`.
<!-- END STANDALONE TASKS.MD -->
