# Dana v1 Design Charter

This document records the foundational design decisions for **Dana v1**—the data sibling to
[Mo](https://github.com/robertguss/mo). Every later specification (`docs/reference/`,
`docs/design/`, `formal/`) builds on these commitments.

## 1. Mission & Core Scope

Dana is a dedicated, self-contained programming language and runtime for everyday data work:

- **Tier 1 (v1 Core):**
  - **Database & ETL pipelines:** ingesting, validating, cleaning, reconciling, deduplicating,
    joining across sources, and upserting into databases cleanly.
  - **Operational, product & financial analytics:** group-bys, window functions, rolling
    aggregations, cohorts, pivots, exact `Decimal` financial math, and repeatable reporting.
  - **Practical exploratory analysis, statistics & visualization:** table profiling,
    descriptive stats, correlations, significance checks, linear regression, outlier flags,
    and zero-dependency SVG and terminal charts embedded in self-contained HTML/Markdown
    reports.
- **Explicit v1 Non-Goals (deferred to v2+):**
  - Deep learning, GPU tensors, automatic differentiation, and large-scale distributed
    cluster compute.
  - Heavy R/SciPy statistical modeling suites (GLMs, ARIMA, full probability distribution
    libraries, dense/sparse linear algebra)—added later only as real workloads require them.
  - A central third-party package registry or transitive package manager.
  - Web-based `.ipynb` notebook files (replaced by plain-text executable report scripts and
    a safe terminal REPL).

## 2. Signature Pillar: Native PII & FERPA Privacy (Level 3)

Sensitive data handling is a first-class property of Dana's type system, capability system,
and runtime—not an optional lint pass or external wrapper:

1. **Schema-tagged sensitivity (opt-in friction):** Columns in a `schema` may carry
   sensitivity tags such as `[pii]`, `[ferpa]`, or domain-specific tags (e.g. `[financial]`).
   Scripts working on non-sensitive data pay zero syntactic tax.
2. **Compiler-enforced propagation:** Sensitivity tags propagate automatically through
   derived columns, expressions, filters, joins, and aggregations (including implicit flows;
   the exact information-flow and declassification rules are specified in Phase 0,
   `docs/design/privacy.md`).
3. **Capability-gated sinks:** Writing, printing, charting, or transmitting sensitive columns
   to any output (`Console`, `WriteFiles`, `WriteTable`, `HttpsAllow`, `Report`) is a compile
   error unless the data is explicitly declassified via an audited primitive (`drop`,
   `redact`, `mask`, `pseudonymize`, `suppress_small_groups`, etc.) **or** the caller holds
   an explicit capability authorizing that sensitivity tag.
4. **AI-safe runtime inspection:** Error messages, crash diagnostics, malformed-row
   quarantine diagnostics, `dana dry-run` diffs, and REPL previews automatically redact
   tagged fields by default so AI agents debugging real pipelines never see raw student or
   personal records.
5. **Higher-ed & institutional reporting primitives:** Built-in small-cell suppression
   (`suppress_small_groups(min: k)`) and keyed consistent pseudonymization across tables.
6. **Schema-driven synthetic data (`dana fake`):** Deterministic generation of realistic,
   safe fixture tables from any `schema` so humans and AI agents can develop and verify
   pipelines completely offline.

## 3. Language Feel: Mo's Data Sibling

Dana shares Mo's aesthetic and AI-first discipline:

- **Readable, unambiguous syntax:** Ruby/Elixir warmth—`module`, `fn ... end`, `case ... end`,
  `?` boolean predicates (`empty?`, `active?`), no semicolons, non-significant indentation
  with an opinionated formatter (`dana format`).
- **Data-native surface:**
  - `|>` left-to-right pipeline operator.
  - `schema ... end` declarations with column types, value constraints (`where`), and
    sensitivity tags (`[pii]`, `[ferpa]`).
  - `.column` selector shorthand inside table pipeline verbs.
  - Markdown-style `table ... end` literals for inline `examples` and `test` blocks.
- **Pure pipelines, practical glue:** Code inside table pipelines is strictly pure so the
  query planner can freely fuse, parallelize, and push stages down to SQL. Outside
  pipelines, Mo-style `fn`, `case`, `if`, and `for` handle CLI arguments, API pagination,
  error handling, and multi-step orchestration.
- **One canonical way:** Avoid Pandas-style overlapping APIs. There is one clean, algebraic,
  pipeable way to filter, derive, join, group, reshape, and aggregate tables.

## 4. Type System & Missing Values

- **Boundary schemas + inferred structural table types:** Declare named `schema`s at inputs,
  outputs, and public function boundaries (assisted by `dana infer-schema` on raw files).
  Inside `|>` pipelines, the compiler tracks every column's name, type, nullability, and
  sensitivity tags structurally with zero throwaway intermediate structs.
- **One unified missing-value model (`T?`):** SQL `NULL`, empty CSV cells, JSON `null`, and
  Parquet nulls all map to a single optional type (`Decimal?`, `Text?`). There is no
  `None`/`NaN`/`pd.NA`/`NaT` split.
- **Exact money & real time:** `Decimal` is a built-in first-class type alongside `Int` and
  `Float`. `Date`, `Timestamp` (explicit timezone/UTC + IANA zones), and `Duration` are
  first-class primitives.
- **Quarantine-first parsing:** Reading messy CSV/JSON/XLSX files into a `schema` splits
  cleanly into `(valid_rows, bad_rows)` rather than silently coercing invalid inputs or
  aborting mid-file.

## 5. Workflow Modes

- **Pipeline-first modules (primary):** Checked, formatted, tested `.dana` modules with
  explicit capabilities.
- **Built-in safe REPL & CLI one-liners (`dana repl`):** Fast interactive exploration on the
  same engine, defaulting to read-only capabilities and automatic PII redaction, with an
  explicit `untyped` reader when first inspecting unknown files.
- **Executable reports:** Scripts generate clean, self-contained HTML and Markdown reports
  embedding formatted tables and native SVG charts—plain text in git and trivial for AI
  agents to edit and diff.

## 6. Databases & SQL Pushdown

- **One pipeline API everywhere:** Local files, in-memory tables, SQLite, and Postgres expose
  the exact same typed `Table` interface.
- **Automatic parameterized SQL pushdown:** Filter, projection, join, and aggregation stages
  on database tables compile down into parameterized SQL (making SQL injection structurally
  impossible), pulling only reduced results locally and seamlessly joining DB tables with
  local files.
- **Offline schema snapshots (`schema.lock`):** Introspect database schemas into a checked-in
  lockfile so the compiler and AI agents verify columns, types, and drift completely offline.
- **Scoped SQL escape hatch:** A `raw_sql` escape hatch requires an explicit capability
  (`RawReadDB`) and a declared output `schema`, and remains parameterized-only.

## 7. Built-In v1 Standard Library (Batteries Included)

Everything required for daily data work ships inside one self-contained binary:

- **Databases:** Embedded SQLite, native PostgreSQL wire-protocol client (TLS-capable).
  *(MSSQL and MySQL/MariaDB are planned for v1.5/v2 if real workloads call for them.)*
- **Files & Streams:** CSV/TSV (quarantine mode), JSON/JSONL (streaming), Parquet, Excel
  (`.xlsx` read/write), transparent gzip/zstd compression, capability-gated HTTPS client with
  explicit host allowlists.
- **Relational & Time Series:** `where`, `select`, `drop`, `rename`, `derive`, `sort`,
  `distinct`, `limit`, `group_by`, `summarize`, explicit-cardinality joins (`join_one`,
  `join_many_to_one`, `join_many`), `semi_join`, `anti_join`, `union`, `pivot_wider` /
  `pivot_longer`, window functions (`lag`/`lead`, `rank`, `row_number`, rolling windows),
  `date_trunc`, `fill_gaps`.
- **Profiling, Stats & Charts:** One-line redacted `profile()`, `mean`, `median`,
  `percentile`, `stddev`, `variance`, `corr` (Pearson/Spearman), t-test, chi-square, linear
  regression, z-score/IQR outlier flags, and declarative zero-dep SVG + terminal charts
  (`chart_bar`, `chart_line`, `chart_scatter`, `chart_histogram`, `chart_heatmap`).

## 8. AI-First & Data-Safety Guardrails

- **Embedded version-matched docs:** `dana guide` (mirroring `mo guide`) embeds the reference
  and agent guide straight into the binary.
- **Inline intent:** Markdown-table `examples` and table-level `promise` contracts checked
  automatically in `dana test` and at pipeline boundaries.
- **Explicit join cardinalities:** Prevent silent fan-out bugs that duplicate rows and distort
  metrics.
- **Redacted `dana dry-run`:** Executes DB write pipelines read-only and prints a redacted
  insert/update/delete diff before granting `WriteTable`/`WriteDB`.
- **Plan & privacy inspection (`dana explain`):** Shows exactly which stages push down to
  SQL vs. execute locally, and traces where sensitivity tags enter and get declassified.
- **Offline fake testing:** `DB.in_memory`, `Files.in_memory`, `Console.fake`, and
  `dana fake` make every pipeline 100% unit-testable with zero live credentials or real PII.

## 9. Supply-Chain & Implementation Discipline

- **No central package registry:** 95% of scripts use only the built-in stdlib. Repo-local
  `vendor/` modules are hash-pinned, checked in full into git, and **pure by default**—unable
  to touch files, env vars, databases, or the network unless explicitly passed a capability.
- **Own vectorized columnar VM:** ~2,048-row contiguous typed column batches with null
  bitmaps, streaming execution, multi-threaded partitions, and compiled vectorized user
  functions (no UDF cliff).
- **Zero-Crate Rust host stack:** Built strictly on Rust `std` (`Cargo.toml` contains **zero**
  third-party crates) plus minimal audited `extern "C"` shims to a tiny C allowlist:
  1. SQLite single-file amalgamation
  2. System TLS / OpenSSL
  3. `zlib` / `zstd`
- **Full verification rigor:**
  1. **Lean Formal Core:** Machine-checked proofs of **schema/type soundness** and
     **PII/FERPA non-interference** over Dana Core IR.
  2. **Differential Reference Oracle:** A compact, naive row-by-row Rust evaluator verified
     against both the vectorized VM and SQL pushdown on randomized pipelines.
  3. **Parser Fuzzing:** Continuous fuzzing on CSV, JSON, Parquet, XLSX, HTTP, and Postgres
     wire parsers.
  4. **AI Learnability Gates:** Fresh models from multiple families writing Dana solely from
     `dana guide`, scored on objective pass rates before releases.
