# Dana Privacy & Declassification Model (v0.1)

**Status:** Approved Phase 0 design specification. This document defines how Dana tracks,
propagates, declassifies, authorizes, redacts, and formally verifies sensitive data (such as
PII, FERPA student records, financial data, and custom institutional categories).

## First Principle

> **Zero friction on public data; serious, intentional friction on sensitive data.**

If a `schema` declares no sensitivity tags, every column tag set is `[]` and every table's
`row_tags` is `[]`. Non-sensitive scripts never mention `allows:`, `suppress_small_groups`,
`Declassify`, `--allow-export`, or `dana.policy`—the entire privacy layer stays invisible.

The moment a column or schema carries a sensitivity tag (`[pii]`, `[ferpa]`, `[donor]`, …),
Dana enforces strict compile-time, runtime, and optional policy-file guardrails so neither a
human nor an AI agent can accidentally leak protected records.

---

## 1. Sensitivity Tag Model

Sensitivity labels form a **flat bounded join-semilattice** `(Set(Tag), ∅, ∪, ⊆)`:

- **Public:** the empty set `[]` (`∅`).
- **Built-in standard tags:** `pii`, `ferpa`, `financial`, `health`, `secret`.
- **Custom project/module tags:** declared in one line so typos (e.g. `[ferppa]`) are
  rejected at compile time:
  ```ruby
  tag donor
  tag counseling
  ```
- **Composition:** combining values or contexts takes the **set union** (`[pii] ∪ [ferpa] =
  [pii, ferpa]`). There are no hidden tag hierarchies or external policy graphs required to
  read a function signature.

### Attaching Tags to Schemas

Tags may be attached to individual columns, or to an entire `schema` when the **existence of
a row itself** is sensitive:

```ruby
schema Student
  id: Int [pii]
  email: Text [pii]
  gpa: Decimal? [ferpa]
  program: Text
  enrolled_year: Int
  active?: Bool
end

## Every row indicates a counseling visit, so row presence itself is [counseling].
schema CounselingVisit [counseling]
  student_id: Int [pii]
  visit_date: Date
  duration_min: Int
end
```

When a table is loaded with schema `S`:
- Each column `c` starts with its declared tag set `col_tags(c)`.
- Table `row_tags` starts with `schema_tags(S)` (`[]` for `Student`, `[counseling]` for
  `CounselingVisit`).

---

## 2. Direct & Implicit Information Flow

Every `Table` type carries two compile-time sensitivity components:
1. **`col_tags: Map(ColumnName, Set(Tag))`** — sensitivity of each column's values.
2. **`row_tags: Set(Tag)`** — sensitivity of **row presence, cardinality, grouping, and row
   order**.

The effective sensitivity of emitting a column `c` from table `T` is always
`col_tags(T, c) ∪ row_tags(T)`.

### Scalar Expressions & Control Flow

- Literals and pure constants have tag set `[]`.
- Any scalar operation `op(e1, ..., en)` has tag set `tags(e1) ∪ ... ∪ tags(en)`.
- Outside table pipelines, branching on a tagged condition (`if`, `case`, `while`) elevates
  the block's **program-counter label** `pc := pc ∪ tags(cond)`. Every value produced or
  effect invoked inside that branch inherits `pc`.

### Relational Pipeline Propagation Rules

| Operator | Effect on `col_tags` | Effect on `row_tags` | Notes |
| --- | --- | --- | --- |
| `select(c1, ...)` | Keeps only selected columns' tags | Unchanged | Selecting public columns from `Student` keeps `row_tags = []` (zero false alarms). |
| `drop(c1, ...)` | Removes dropped columns | Unchanged | Dropping `.gpa` after `where(.gpa < 2.0)` does **not** clear `row_tags`. |
| `rename(a: b)` | Moves tags from `b` to `a` | Unchanged | |
| `derive(x: expr)` | `col_tags(x) = tags(expr)` | Unchanged | `tags(expr)` is union of tags of columns referenced in `expr`. |
| `where(pred)` | Unchanged | `row_tags ∪ tags(pred)` | Prevents filter-then-drop/count implicit leaks. |
| `distinct(cols...)` | Unchanged | `row_tags ∪ tags(cols)` | Row count depends on distinctness of `cols`. |
| `sort_by(cols...)` | Unchanged | `order_tags := tags(cols)` (folded into `row_tags` unless re-sorted publicly or aggregated) | Prevents order-channel leaks like `sort_desc(.gpa) \|> select(.program)`. |
| `limit(n)` | Unchanged | `row_tags ∪ order_tags` | Which rows survive `limit` depends on ordering. |
| `join_*(R, on: pred)` | Left & right column tags preserved | `L.row_tags ∪ R.row_tags ∪ tags(pred)` | Matching keys on `[pii]` adds `[pii]` to `row_tags`. |
| `semi_join` / `anti_join` | Left column tags preserved | `L.row_tags ∪ R.row_tags ∪ tags(pred)` | Row survival depends on right table match. |
| `union(R)` | Per-column `L.col_tags(c) ∪ R.col_tags(c)` | `L.row_tags ∪ R.row_tags` | |
| `group_by(keys...)` | Grouping key columns retain their tags | `row_tags ∪ tags(keys)` | Records grouping keys for `summarize` and `suppress_small_groups`. |
| `summarize(a: agg(e), ...)` | `col_tags(a) = tags(e) ∪ row_tags`; each output col records whether it is a **blending aggregate** (`count`, `sum`, `mean`, `median`, `stddev`, `variance`, `percentile`) or **non-blending** (`min`, `max`, `first`, `last`, `collect`) | Preserves `row_tags`; tracks exact hidden group size (and distinct entity count if specified) | Re-sorting/grouping clears prior `order_tags`. |
| `window(x: wfn(e), over: part, order: ord)` | `col_tags(x) = tags(e) ∪ tags(part) ∪ tags(ord)` | Unchanged | |
| `pivot_wider(names_from: n, values_from: v, columns: [...])` | Static output columns each inherit `tags(n) ∪ tags(v)` | `row_tags ∪ tags(n)` | Output column names are compile-time constants, so headers cannot leak tagged data. |
| `crosstab(rows: r, cols: c, values: v)` | Returns `DynamicTable` tagged `row_tags ∪ tags(r) ∪ tags(c) ∪ tags(v)` | Folded into `DynamicTable` tags | Display-only matrix; cannot be statically dot-indexed and cannot leak sensitive headers to public sinks. |

### Concrete Example: Zero False Alarms vs. Caught Implicit Leak

```ruby
# 1. Public columns only -> 100% public (row_tags = [], col_tags = [])
db.table(Student)
  |> select(.program, .enrolled_year)
  |> group_by(.program, .enrolled_year)
  |> summarize(headcount: count())
# Compiles directly to Console or public WriteFiles with ZERO privacy annotations.

# 2. Implicit FERPA leak -> caught statically!
db.table(Student)
  |> where(.gpa < 2.0)                  # row_tags += [ferpa]
  |> select(.program)                   # .gpa dropped, but row_tags is still [ferpa]
  |> group_by(.program)
  |> summarize(probation_n: count())    # probation_n carries [ferpa] via row_tags
# Cannot be written publicly without `suppress_small_groups(min: 5)` or an authorized sink.
```

---

## 3. Audited Declassifiers & Safe Aggregations

Dana has **no free `declassify(...)` function**. A helper function—or an AI agent trying to
resolve a compiler error—cannot silently strip sensitivity tags. Tags are cleared **only**
through two auditable mechanisms:

### 3.1 Built-In Audited Privacy Primitives

1. **`redact(.col)`** (or `redact(.col, with: "[REDACTED]")`)
   - Replaces every value in `.col` with a fixed public constant.
   - Clears `col_tags(.col)` to `[]`. Does not clear `row_tags`.

2. **`pseudonymize(.col, key: secret)`**
   - Computes a keyed cryptographic HMAC-SHA256 deterministic token (e.g. `ps_<hex>`) using an
     explicit `Secret` capability (`secret: Secret("student_pseudo_key")`).
   - Clears `[pii]` on `.col` (or the tag set authorized for that pseudonymization key),
     preserving equality/joinability across tables without exposing raw identity.
   - Fails to compile if given a hardcoded string literal instead of a `Secret` capability.

3. **`bucket(.col, cuts: [...], labels: [...])`**
   - Maps a sensitive numeric or date column into a **compile-time-constant finite set of
     public labels** (e.g. `cuts: [18, 45, 65], labels: ["0-17", "18-44", "45-64", "65+"]`).
   - On individual rows, the bucketed column **retains its original sensitivity tags** (so
     row-level bands cannot leak publicly), *but* carries a static `bucketed` flag.
   - Because labels are compile-time constants, no raw sensitive string (such as an email or
     free-text note) can ever escape through a bucket label.

4. **`suppress_small_groups(min: k)`** (and **`suppress_small_groups(min: k, distinct_by: .id)`**)
   - Valid only immediately on a `summarize`d table (where the engine tracks exact source row
     counts—and when `distinct_by` is supplied, exact distinct entity counts, preventing one
     student with 5 course rows from masquerading as 5 students).
   - Enforces `k >= min_group_size` (default floor `5`; may be raised by `dana.policy`).
   - Drops groups smaller than `k` (or, with `mode: :mask`, masks suppressed aggregate cells
     while enforcing complementary suppression so suppressed counts cannot be recovered by
     subtraction from a grand total).
   - **What it clears:**
     - Clears `row_tags` to `[]` (except tags present on any remaining non-bucketed group-by
       key column).
     - Clears sensitivity tags on **blending aggregates** (`count`, `sum`, `mean`, `median`,
       `stddev`, `variance`, `percentile`).
     - Clears sensitivity tags on **`bucketed` group-by key columns** created via
       `bucket(...)` (since each surviving bucket represents `>= k` distinct entities and its
       label is a compile-time constant).
   - **What it NEVER clears:**
     - **Non-bucketed group-by key columns** keep their tags (`group_by(.email)` keeps
       `.email` as `[pii]`; `group_by(.clinical_notes)` keeps `[health]`).
     - **Single-record extremes** (`min`, `max`, `first`, `last`, `collect`) keep their tags
       because a single individual's exact value can surface even in a large group.

```ruby
students
  |> group_by(.program)
  |> summarize(n: count(), avg_gpa: mean(.gpa), top_gpa: max(.gpa))
  |> suppress_small_groups(min: 5, distinct_by: .id)
# Resulting column tags:
#   program : Text     []       (already public)
#   n       : Int      []       (cleared: blending aggregate, k >= 5 distinct students)
#   avg_gpa : Decimal? []       (cleared: blending aggregate, k >= 5 distinct students)
#   top_gpa : Decimal? [ferpa]  (STILL TAGGED: max exposes one student's exact GPA)
```

### 3.2 Capability-Gated Manual Escape Hatch (`Declassify`)

For rare, institution-approved exceptions (such as `mask_last4` or custom coarsened buckets
not covered by the built-in audited primitives), `main` may explicitly pass a `Declassify`
capability:

```ruby
fn main(db: ReadDB(Seminary), declass: Declassify([ferpa]), console: Console)
  ...
  # Explicit, auditable call requiring the capability token:
  safe_label = declass.approve(masked_value, reason: "Registrar-approved cohort band")
end
```

- Every `Declassify` usage is visible right in `main`'s signature, listed in `dana explain`,
  and can be globally forbidden in `dana.policy` (`forbid manual_declassify`).

---

## 4. Authorized Sinks, DB Writes & Optional `dana.policy`

### 4.1 Default Mode: Capability Allowlists + Column-Matched DB Writes

Every output capability defaults to `allows: []` (public data only):

- **External sinks (`Console`, `WriteFiles`, `HttpsAllow`, `Report`):**
  - Accepting a value/table with effective tags `T` requires `T ⊆ sink.allows`.
  - Any chart added to a `Report` (`chart_bar`, `chart_line`, etc.) checks tags on all axis,
    label, color, and tooltip columns against the report's allowed tags.
  - **Runtime export gate:** When a program declares any external sink with non-empty
    `allows`, `dana run` refuses to execute unless the operator passes matching runtime
    authorization (e.g., `dana run registrar_export.dana --allow-export=pii,ferpa`). This
    gives humans an explicit kill-switch whenever an AI agent or scheduled script runs.

- **Database table writes (`WriteTable(Db, "table_name", allows: [...])`):**
  - Enforces **both**:
    1. **Capability check:** every written column's effective tags and `row_tags` must be a
       subset of the capability's `allows` set.
    2. **Column-by-column schema match:** writing expression `e` into destination column `d`
       requires `tags(e) ⊆ dest_schema.col_tags(d)` (and `row_tags ⊆ dest_schema.row_tags ∪
       dest_schema.col_tags(d)` for table-level compatibility). You can never accidentally
       downgrade a `[ferpa]` column into a public `notes: Text` column in Postgres.

### 4.2 Opt-In Institutional Policy File (`dana.policy`)

Any project or organization may optionally check a human-readable `dana.policy` file into
the repository root (or pass `--policy path/to/dana.policy`). When absent, default capability
rules apply with zero friction. When present, `dana.policy` acts as an **immutable upper
bound** enforced by both `dana check` and `dana run`:

```text
# dana.policy — human-readable upper bound on all scripts in this repository
version 1

min_group_size 5
forbid manual_declassify
forbid repl_show_sensitive

allow export "registrar/"         tags [pii, ferpa]
allow https  "api.populiweb.com"  tags [pii]
allow write  Seminary.students    tags [pii, ferpa]
allow write  Seminary.audit_log   tags []
```

- A `.dana` script may request **fewer** permissions than `dana.policy`, never **more**.
- If an AI agent edits a script to add `WriteFiles("tmp/", allows: [pii])` or
  `Declassify([ferpa])`, compilation fails immediately against `dana.policy`.
- A human reviewer (or Registrar/IT security auditor) can audit every sensitive boundary in
  the entire repository by reading one short file.

---

## 5. Runtime Redaction, Quarantine, `dry-run`, `profile()`, REPL & `fake`

Compile-time checks alone do not stop diagnostics from leaking sensitive values into terminal
logs or an AI agent's context window. Dana enforces **safe-by-default runtime redaction**:

| Surface | On Public Schemas (`[]`) | On Tagged Schemas (`[pii]`, `[ferpa]`, …) |
| --- | --- | --- |
| **Quarantine `bad_rows`** | `line`, `column`, `error_kind`, `raw_value`, and `raw_line` are all public `[]`. | `line: Int`, `column: Text`, and `error_kind: ParseError` stay **public `[]`** (`"line 42, col gpa: BadDecimal"`). `raw_value` inherits that column's tags; `raw_line` inherits the union of all schema tags. |
| **Runtime failures** (`join_one` duplicates, `promise` failures, asserts) | Prints the concrete failing value and row indices. | Prints `[REDACTED:tag]` plus row indices/counts (e.g., `duplicate key [REDACTED:pii] (2 rows: 42, 109)`). |
| **`dana dry-run`** | Prints insert/update/delete counts and concrete sample row diffs. | Prints exact insert/update/delete counts and changed column names; tagged cell values render as `[REDACTED:tag]` unless `--allow-export` is granted (and permitted by `dana.policy`). |
| **`profile()`** | Prints type, count, null %, distinct count, min/max, mean/median, top values, sparkline. | Prints safe metadata only (type, count, null %, distinct count); omits sample strings, top values, and `min`/`max` unless authorized. |
| **`dana repl`** | Prints tables directly. | Auto-redacts tagged columns (`[REDACTED:pii]`) by default. Local interactive display requires explicit `--show-sensitive=pii,ferpa` (blocked if `dana.policy` sets `forbid repl_show_sensitive`). |
| **`dana explain`** | Prints query plan & SQL pushdown split. | Also prints the exact **sensitivity provenance trace**: every line where tags enter, propagate into `row_tags`, get cleared by an audited declassifier, or exit an authorized sink. |
| **`dana fake`** | Generates deterministic typed fixture tables. | Generates deterministic, realistic synthetic fixtures matching types, `where` constraints, and format hints (e.g., `user_001@example.invalid`) so AI agents can develop and test with **zero real records**. |

---

## 6. Formal Verification Contract (Lean Core)

In `formal/` (Phase 1), Dana Core IR models:
- Types, structural table schemas, and unified `T?` missing values;
- Tag sets (`Set(Tag)`), per-column tags, table `row_tags`, and scalar `pc`;
- Pure relational operators, audited declassifiers, and capability-gated sinks.

### What Lean Proves

1. **Schema & Type Soundness:** Every well-typed Core IR program evaluates without missing
   column errors, type errors, or untagged null crashes.
2. **Termination-Insensitive Non-Interference (up to Audited Declassifiers & Authorized Sinks):**
   For any tag `t`, any program `P` that does **not** hold a sink allowing `t`, a `Declassify`
   capability for `t`, or an audited declassifier clearing `t` along a path to output:
   running `P` on any two inputs `I1` and `I2` that agree on all data not tagged with `t`
   produces **byte-for-byte identical** outputs (and identical redacted diagnostics).

### Explicit Trust Boundary (What Lies Outside the Proof)

Being honest about boundaries matters as much as the proof itself:
- **Timing & memory side channels** are out of scope (Dana targets accidental and
  agent-induced disclosure in data pipelines, not cryptographic constant-time execution).
- **Differential privacy / composition attacks across multiple independent runs** (e.g.,
  running two slightly different `suppress_small_groups(min: 5)` reports and differencing
  them by hand) are outside the static proof; `suppress_small_groups` is modeled as a
  trusted audited declassification boundary whose minimum `k` and blending-aggregate rules
  are statically enforced.
- **Native parsers and DB wire protocols** are verified by Zero-Crate Rust memory safety,
  the differential reference oracle, and continuous fuzzing rather than Lean.
