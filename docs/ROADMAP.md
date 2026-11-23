# Roadmap

Progress is tracked by phase and verifiable gates, not by calendar dates. Each phase begins
with a written design step for anything a Dana user or agent will observe, and closes only
when its declared checks pass.

| Phase | Goal | Release |
| --- | --- | --- |
| 0. Design & Spec | Charter, privacy model, sample programs, reference & executable grammar | |
| 1. Formal Core & Oracle | Dana Core IR, Lean soundness + non-interference proofs, naive Rust oracle | |
| 2. Core Toolchain & Vectorized VM | Zero-Crate Rust compiler, structural table checker, 2,048-row batch VM, CSV/JSON/gzip | Internal milestone |
| 3. Databases & SQL Pushdown | Embedded SQLite, native Postgres wire + TLS, `schema.lock`, SQL pushdown, `dry-run`, `explain` | **v0.1** |
| 4. Formats, Analytics, Charts & REPL | Native Parquet & `.xlsx`, HTTPS allowlist, windows/pivots/stats, SVG/HTML reports, `dana repl` | **v0.2** |
| 5. Hardening & Learnability Gate | Full parser fuzzing, differential soak tests, real-world pipelines, multi-model AI learnability gate | **v1.0** |

## Now: Phase 0 — Design & Spec

Phase 0 establishes the exact language specification before compiler implementation starts:

- [x] **Design Charter & Architecture Overview** (`docs/CHARTER.md`, `docs/design/architecture.md`, `docs/ROADMAP.md`)
- [x] **Privacy & Declassification Model** (`docs/design/privacy.md`): sensitivity tag algebra, direct and implicit flows (filters/group-bys/counts), audited declassifiers (`redact`, `pseudonymize`, `suppress_small_groups`), capability sink rules, optional `dana.policy`, and runtime redaction rules.
- [x] **Real-World Sample Programs** (`examples/`): 10 realistic `.dana` scripts (plus `examples/dana.policy`) covering general CSV, higher-ed/FERPA, SaaS, fintech/e-commerce, DevOps streaming logs, healthcare/HIPAA, and exploratory statistics.
- [ ] **Dana Language Reference v0.1** (`docs/reference/README.md`) & **Executable Grammar** (`grammar/`): complete readable reference (later embedded via `dana guide`) with every example parsed cleanly by the grammar.
- [ ] **Dana Core IR Specification** (`docs/design/core-ir.md`): exact syntax, typing, sensitivity rules, and text serialization shared between Rust and Lean.

## Upcoming Phases

### Phase 1 — Formal Core & Differential Oracle
- Formalize Dana Core IR in Lean (`formal/`): syntax, static schema/type rules, sensitivity/taint rules, capability boundary rules, and operational semantics.
- Prove **schema/type soundness** and **PII/FERPA non-interference** in Lean.
- Implement the ~300-line naive row-by-row reference evaluator in Zero-Crate Rust (`src/oracle/`) and verify agreement with the Lean Core evaluator via shared Core IR text format.

### Phase 2 — Core Toolchain & Vectorized Columnar VM
- Implement the Zero-Crate Rust CLI (`dana check`, `dana run`, `dana test`, `dana format`, `dana fake`, `dana infer-schema`, `dana guide`).
- Front end: lexer, parser, name/module resolver, boundary schema + inferred structural table type checker, sensitivity/capability checker, `examples` and `promise` lowering.
- Back end: relational plan builder + 2,048-row contiguous columnar batch VM (streaming, multi-threaded partitions, compiled vectorized expressions with zero UDF cliff).
- Built-in types & codecs: `Int`, `Float`, `Decimal`, `Bool`, `Text`, `Bytes`, `Date`, `Timestamp` (IANA TZ), `Duration`, unified `T?`, CSV/TSV (quarantine mode), JSON/JSONL, transparent gzip/zstd.
- Gate: differential fuzzing asserts `naive oracle == vectorized VM` across thousands of generated pipelines (values, nulls, join cardinality errors, and sensitivity tags).

### Phase 3 — Databases & SQL Pushdown (**v0.1**)
- Minimal audited `extern "C"` shims for embedded SQLite amalgamation and system TLS.
- Native PostgreSQL wire-protocol client (TLS, SCRAM-SHA-256 auth, typed binary/text decoding, parameterized queries only).
- `dana schema-sync` / `schema.lock` offline database schema snapshots.
- Query planner pushdown splitter: lowers pushable pipeline stages into parameterized SQL (SQLite & Postgres dialects) and seamlessly streams results into local vectorized stages for cross-source joins and custom functions.
- `dana dry-run` (redacted insert/update/delete diffs), `dana explain` (SQL pushdown + PII flow map), and capability-gated `raw_sql`.
- Gate: differential testing asserts `naive oracle == vectorized VM == SQLite pushdown == Postgres pushdown`.

### Phase 4 — Formats, Analytics, Charts & Safe REPL (**v0.2**)
- Native in-tree Parquet reader/writer and Excel (`.xlsx`) reader/writer (reusing the audited zlib/zstd shim).
- Capability-gated HTTPS client with explicit domain allowlists and PII-egress blocking.
- Full analytics stdlib: window functions (`lag`/`lead`, `rank`, `row_number`, rolling windows), `pivot_wider`/`pivot_longer`, `fill_gaps`, redacted `profile()`, practical stats (`median`, `percentile`, `stddev`, `corr`, t-test, chi-square, linear regression, outlier flags).
- Zero-dependency SVG & terminal charts (`chart_bar`, `chart_line`, `chart_scatter`, `chart_histogram`, `chart_heatmap`) and self-contained HTML/Markdown `Report` builder.
- `dana repl` (interactive safe mode: read-only + PII-redacted defaults, `untyped` exploration) and `vendor/` hash-pinned pure-by-default modules.

### Phase 5 — Hardening & AI Learnability Gate (**v1.0**)
- Continuous fuzzing across every external parser (CSV, JSON, Parquet, XLSX, HTTP, Postgres wire).
- Real-world end-to-end data pipelines benchmarked against Python (Pandas/Polars) and audited for privacy guarantees.
- Prospectively declared multi-model AI learnability evaluation: fresh models from multiple families writing working, privacy-compliant Dana pipelines solely from `dana guide`.

## Alongside every phase

Five tracks run alongside every phase:

1. **Formal verification** of Dana Core IR in Lean (soundness + privacy non-interference);
2. **Differential testing & fuzzing** (`naive oracle == vectorized VM == SQL pushdown`, parser fuzzers);
3. **Zero-crate supply-chain audit** (verifying `Cargo.toml` stays at zero external crates and C shims stay minimal);
4. **AI learnability evaluations** (verifying humans and agents write idiomatic Dana cleanly from `dana guide`);
5. **Documentation** kept in lockstep with the compiler and embedded into `dana guide`.
