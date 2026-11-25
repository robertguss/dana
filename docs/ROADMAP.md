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

## Now: Phase 4 Complete (**v0.2**) — Ready for Phase 5 (Hardening & AI Learnability Gate)

Phases 0, 1, 2, 3, and 4 established, formally proved, implemented, and differentially verified the language specification, Core IR, Lean 4 proofs, naive Rust reference oracle, Zero-Crate Rust compiler/CLI, streaming formats/FFI codecs, 2,048-row vectorized columnar VM, embedded SQLite + native PostgreSQL v3.0 database pushdown runtime (**v0.1**), and native Parquet/XLSX/HTTPS, statistical analytics, SVG/terminal charts, HTML/Markdown reports, safe interactive REPL, and SHA-256 hash-pinned `vendor/` modules (**v0.2**):

- [x] **Design Charter & Architecture Overview** (`docs/CHARTER.md`, `docs/design/architecture.md`, `docs/ROADMAP.md`)
- [x] **Privacy & Declassification Model** (`docs/design/privacy.md`): sensitivity tag algebra, direct and implicit flows (filters/group-bys/counts), audited declassifiers (`redact`, `pseudonymize`, `bucket`, `suppress_small_groups`), capability sink rules, optional `dana.policy`, and runtime redaction rules.
- [x] **Real-World Sample Programs** (`examples/`): 10 realistic `.dana` scripts (plus `examples/dana.policy`) covering general CSV, higher-ed/FERPA, SaaS, fintech/e-commerce, DevOps streaming logs, healthcare/HIPAA, and exploratory statistics.
- [x] **Dana Core IR Specification** (`docs/design/core-ir.md`): exact typed Core IR, pure relational `Plan` sub-calculus, sensitivity algebra, canonical S-expression text protocol `(dana-core 0.1 ...)`, and Lean theorem statements.
- [x] **Dana Language Reference v0.1** (`docs/reference/README.md`) & **Executable Grammar** (`grammar/`): 0-conflict Bison IELR(1) grammar (`%expect 0`, no precedence declarations) passing all 10 `examples/*.dana`, every fenced snippet in `docs/reference/README.md` and `README.md`, and positive/negative syntax tests (`make grammar`).
- [x] **Phase 1A — Lean 4 Formal Core & Non-Interference Proofs** (`formal/`): zero-dependency Lean 4 (`v4.36.0`) formalization of Dana Core IR, decidable static checker, deterministic evaluator, canonical `(dana-core 0.1 ...)` wire codec, `danacore` CLI oracle, and machine-checked proofs of Schema & Type Soundness (Theorems 1A–1D) and Termination-/Error-Insensitive Non-Interference + Redacted Explicit-Stop Diagnostics (Theorems 2A–2E), zero `sorry`/custom axioms (`make formal`).
- [x] **Phase 1B — Zero-Crate Rust Core IR & Naive Differential Oracle** (`Cargo.toml`, `src/core/`, `src/oracle/`, `src/bin/dana-oracle.rs`, `tests/`): zero-dependency Rust (`std` only, `#![forbid(unsafe_code)]`, strict clippy denies) Core IR AST, arbitrary-precision `BigInt`, iterative $O(1)$-stack canonical `(dana-core 0.1 ...)` parser/printer, static verifier, persistent `Arc`-environment reference evaluator, and `dana-oracle` CLI (`make oracle`), differentially verified byte-for-byte against the Lean `danacore` CLI across curated corpora, privacy/policy rejections, unbounded `Nat >= 2^64` wire payloads, deep AST/type/value shapes, closure chains, fuel boundaries, and 300 PRNG-generated programs.
- [x] **Phase 2A — Zero-Crate Compiler Front End & Core IR Bridge** (`src/base/`, `src/syntax/`, `src/check/`, `src/lower/`, `src/runtime/`, `src/cli/`): 100% Bison IELR(1) parity parser and canonical formatter, module & `dana.policy` resolver, structural table/privacy/capability/implicit-flow checker, iterative stack-safe lowering with `verified_core` extraction, and `dana` CLI (`check`, `run`, `test`, `format`, `guide`).
- [x] **Phase 2B — Audited FFI Codecs & Streaming Formats** (`src/ffi/`, `src/formats/`): minimal audited RAII FFI wrappers for system `zlib` and `libzstd` (only `unsafe` in the repo), IANA TZif timezone calendar math, HMAC-SHA256 pseudonymization, streaming CSV/TSV quarantine parser & JSON/JSONL codecs, `dana infer-schema`, and deterministic constraint-satisfying `dana fake`.
- [x] **Phase 2C — Relational Query Optimizer & 2,048-Row Vectorized Columnar VM** (`src/plan/`, `src/vm/`): stop-, tag-, and cardinality-preserving relational optimizer (filter fusion, predicate pushdown, dead-derive pruning, limit folding) with `dana explain`, 2,048-row contiguous columnar batch engine with bit-packed null bitmaps, compiled register-based row bytecode with automatic pure UDF inlining (zero UDF cliff), vectorized physical operators (`HashJoin`, radix-partitioned `HashAggregate`, `SuppressSmallGroups`, `Window`, `Sort`, `Distinct`, `FillGaps`, `PivotWider`, `Crosstab`, `Redact`, `Pseudonymize`), deterministic `std::thread::scope` multi-core execution, 1M-row throughput smoke benchmark, and 5,000+ generated-pipeline differential verification (`Lean danacore == naive oracle == vectorized VM`).
- [x] **Phase 3 — Databases & SQL Pushdown (**v0.1**)** (`src/ffi/{sqlite,tls}.rs`, `src/db/`, `src/plan/{pushdown,explain}.rs`, `src/check/`, `src/runtime/`, `src/vm/`, `src/cli/`): minimal audited SQLite 3 & OpenSSL 3 TLS FFI shims, embedded SQLite driver & native PostgreSQL v3.0 wire-protocol client (TLS + SCRAM-SHA-256 auth, parameterized queries only, direct 2,048-row columnar batch streaming), deterministic tag-preserving `dana schema-sync` & offline `schema.lock` verification (including column-by-column `WriteTable` sensitivity compatibility), 100% parameterized SQL pushdown splitter (SQLite & Postgres dialects) verified across 1,125+ differential cases (`Oracle == VM == SQLite Pushdown == Postgres Pushdown`), live `ReadDB`/`WriteTable.upsert`/`RawReadDB.raw_sql` execution, strictly read-only redacted `dana dry-run`, and sensitivity-provenance `dana explain`.
- [x] **Phase 4 — Formats, Analytics, Charts & Safe REPL (**v0.2**)** (`src/formats/{zip,parquet,xlsx}.rs`, `src/net/https.rs`, `src/stats/`, `src/viz/`, `src/check/vendor.rs`, `src/repl/`, `src/cli/`):
  - **Phase 4A:** native zero-crate PKZIP/raw DEFLATE, Apache Parquet reader/writer (`PLAIN` + `RLE_DICTIONARY`, `UNCOMPRESSED`/`SNAPPY`/`GZIP`/`ZSTD`, exact 18-digit `Decimal`), OOXML Excel `.xlsx` single/multi-sheet reader/writer with quarantine `bad_rows` and strict XXE/DTD/zip-bomb protection, and capability-gated OpenSSL TLS HTTPS client (`HttpsAllow`) with exact host allowlisting and `--allow-export` PII-egress gating.
  - **Phase 4B:** practical statistical analytics stdlib (`Stats.corr` Pearson & tied-rank Spearman, `Stats.linear_regression` + `model.predict`, Welch `Stats.t_test`, `Stats.chi_square`, `Stats.outliers` `:zscore`/`:iqr`), relational `pivot_longer`, privacy-redacted `table.profile()` with 8-bin Unicode sparklines, zero-dependency standalone SVG & Unicode terminal charts (`bar`, `line`, `scatter` + OLS trendline, `histogram`, `heatmap`), and self-contained HTML5 & Markdown `Report` exports.
  - **Phase 4C:** SHA-256 hash-pinned pure-by-default `vendor/` modules (`vendor/vendor.lock`, `dana vendor pin|verify`, automatic resolver verification on `ModuleOrigin::Vendor` imports), safe read-only & privacy-redacted interactive `dana repl` (line-buffered `BufRead`, `--eval`, `--db`, `--policy` `forbid repl_show_sensitive` hard-fail, `--show-sensitive`, meta-commands `:help`/`:type`/`:profile`/`:explain`/`:infer-schema`/`:vars`/`:reset`/`:quit`, and REPL-only `untyped.read_{csv,jsonl,parquet,xlsx}` explorer), and live end-to-end verification across all 10 `examples/*.dana`.

## Upcoming Phases

### Phase 5 — Hardening & AI Learnability Gate (**v1.0**, Next)
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
