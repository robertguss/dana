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

## Now: Phase 1 Complete — Ready for Phase 2 (Core Toolchain & Vectorized Columnar VM)

Phase 0 and Phase 1 established, formally proved, and differentially verified the language specification, Core IR, Lean 4 proofs, and Zero-Crate Rust reference oracle:

- [x] **Design Charter & Architecture Overview** (`docs/CHARTER.md`, `docs/design/architecture.md`, `docs/ROADMAP.md`)
- [x] **Privacy & Declassification Model** (`docs/design/privacy.md`): sensitivity tag algebra, direct and implicit flows (filters/group-bys/counts), audited declassifiers (`redact`, `pseudonymize`, `bucket`, `suppress_small_groups`), capability sink rules, optional `dana.policy`, and runtime redaction rules.
- [x] **Real-World Sample Programs** (`examples/`): 10 realistic `.dana` scripts (plus `examples/dana.policy`) covering general CSV, higher-ed/FERPA, SaaS, fintech/e-commerce, DevOps streaming logs, healthcare/HIPAA, and exploratory statistics.
- [x] **Dana Core IR Specification** (`docs/design/core-ir.md`): exact typed Core IR, pure relational `Plan` sub-calculus, sensitivity algebra, canonical S-expression text protocol `(dana-core 0.1 ...)`, and Lean theorem statements.
- [x] **Dana Language Reference v0.1** (`docs/reference/README.md`) & **Executable Grammar** (`grammar/`): 0-conflict Bison IELR(1) grammar (`%expect 0`, no precedence declarations) passing all 10 `examples/*.dana`, every fenced snippet in `docs/reference/README.md` and `README.md`, and positive/negative syntax tests (`make grammar`).
- [x] **Phase 1A — Lean 4 Formal Core & Non-Interference Proofs** (`formal/`): zero-dependency Lean 4 (`v4.36.0`) formalization of Dana Core IR, decidable static checker, deterministic evaluator, canonical `(dana-core 0.1 ...)` wire codec, `danacore` CLI oracle, and machine-checked proofs of Schema & Type Soundness (Theorems 1A–1D) and Termination-/Error-Insensitive Non-Interference + Redacted Explicit-Stop Diagnostics (Theorems 2A–2E), zero `sorry`/custom axioms (`make formal`).
- [x] **Phase 1B — Zero-Crate Rust Core IR & Naive Differential Oracle** (`Cargo.toml`, `src/core/`, `src/oracle/`, `src/bin/dana-oracle.rs`, `tests/`): zero-dependency Rust (`std` only, `#![forbid(unsafe_code)]`, strict clippy denies) Core IR AST, arbitrary-precision `BigInt`, iterative $O(1)$-stack canonical `(dana-core 0.1 ...)` parser/printer, static verifier, persistent `Arc`-environment reference evaluator, and `dana-oracle` CLI (`make oracle`), differentially verified byte-for-byte against the Lean `danacore` CLI across curated corpora, privacy/policy rejections, unbounded `Nat >= 2^64` wire payloads, deep AST/type/value shapes, closure chains, fuel boundaries, and 300 PRNG-generated programs.

## Upcoming Phases

### Phase 2 — Core Toolchain & Vectorized Columnar VM (Next)
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
