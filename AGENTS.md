# AGENTS.md

Guidance for coding agents (Claude Code, Codex, Antigravity, Cursor, and others) working in
this repository. `CLAUDE.md` imports this file.

## What this is

**Dana** is a pre-release, AI-first programming language and vectorized columnar runtime for
fast, private, database-native data work—the data sibling to
[Mo](https://github.com/robertguss/mo).

Phases 0, 1, 2, 3, 4, 5, 6 (Slices 4.1 & 4.2), and 7 (Slices 5.1 & 5.2) — Design, Executable
Grammar, Lean 4 Formal Core, Naive Rust Oracle, Zero-Crate Toolchain, Streaming Formats/FFI,
Relational Optimizer & 2,048-Row Vectorized Columnar VM, Databases & SQL Pushdown (**v0.1**),
Formats, Analytics, Charts, Safe REPL & Hash-Pinned Vendor Modules (**v0.2**), 12-Parser Fuzzing,
Differential Soak, Privacy Red-Team, End-to-End Python Benchmarks & 24/24 Multi-Model AI
Learnability Gate (**v0.3**), Direct Streaming-Columnar CSV/Parquet Ingestion into `VmTable` +
Zero-Copy Columnar Analytics & Writers (**v0.4, pre-1.0**), and WTS-Readiness: Multi-Schema
PostgreSQL Interop, Row/Aggregate Stdlib, Atomic `0700`/`0600` Private Exports, CSV Formula
Sanitization, Deterministic `shuffle`, Row-Level `suppress_small_cells` & `examples/wts/`
Pilots (**v0.5, pre-1.0**) — are complete. **`v1.0` GA is intentionally held** for sustained
production soak and final hardening sign-off. Run `make check-all` (or `make check-v05`) after
changes to `grammar/`, `examples/`, `formal/`, `src/`, or `docs/reference/README.md`.

## Documents in Order of Authority

1. `docs/CHARTER.md` — locked-in v1 pillars, non-goals, and constraints.
2. `docs/reference/README.md` — the Dana Language Reference v0.5 (embedded into `dana guide`).
   Wins over design docs on user-observable rules.
3. `docs/design/privacy.md` — PII/FERPA taint, implicit-flow, and declassification semantics.
4. `docs/design/core-ir.md` — Dana Core IR, canonical text wire protocol, and Lean theorems.
5. `docs/design/architecture.md` — compiler pipeline, vectorized VM, and module boundaries.
6. `docs/ROADMAP.md` — phase gates, active work, and status.

## Checks

```sh
make grammar               # build 0-conflict Bison IELR(1) grammar and verify examples/ & Reference
make grammar CC=clang      # verify clean build under clang too
make formal                # build & verify Lean 4 formal core, proofs, and danacore CLI
make oracle                # fmt, clippy (-D warnings), doc, unit & differential test suites
make test-parser-parity    # run Rust parser vs. Bison IELR(1) parity suite
make test-examples         # run end-to-end tests across all 10 examples/*.dana (VM & oracle)
make test-db               # run SQLite/Postgres driver, schema.lock, pushdown & CLI DB e2e tests
make test-phase4           # run Phase 4A/4B/4C suites (Parquet, XLSX, HTTPS, stats, charts, REPL, vendor, all 10 live e2e)
make test-v04              # run v0.4 Slice 4.2 streaming-columnar CSV/Parquet/Stats/profile/REPL parity suite
make test-v05              # run v0.5 WTS-readiness suite (Postgres multi-schema, stdlib, FERPA exports, pilots)
make test-diff             # run Lean/oracle/VM/SQL-pushdown differential verification suites (6,000+ cases)
make fuzz-parsers          # run 12-parser zero-crate fuzzer (--release)
make fuzz-soak             # run extended differential soak & 47-probe adversarial privacy suite (--release)
make soak                  # run 10,000-case extended differential soak (DANA_SOAK_CASES=10000)
make learnability          # run Phase 5C deterministic AI learnability grading harness
make bench                 # build release binary and run Dana vs. Python/Pandas/Polars benchmarks
make check-all             # run grammar, formal, and oracle checks end-to-end
make check-v04             # run full v0.4 verification (grammar, formal, oracle, fuzz-parsers, fuzz-soak, learnability)
make check-v05             # run full v0.5 verification (grammar, formal, oracle, fuzz-parsers, fuzz-soak, learnability)
```

## Non-Negotiable Engineering Rules

1. **Zero-Crate Rust:** `Cargo.toml` must contain **zero** external Rust crates
   (`dependencies = {}`, `dev-dependencies = {}`). Never add a crate without explicit
   approval from Robert.
2. **Audited C Allowlist Only:** External native code is strictly limited to SQLite
   (single-file amalgamation), system TLS/OpenSSL, and `zlib`/`zstd`, isolated behind
   minimal `extern "C"` shims in `src/ffi/`.
3. **Contain `unsafe`:** Every Rust module outside `src/ffi/` (and explicitly justified,
   benchmarked inner batch loops if ever needed) uses `#![forbid(unsafe_code)]`.
4. **Privacy by Construction:** Never bypass sensitivity checks in diagnostics, error
   messages, `bad_rows`, `dry-run` diffs, or REPL output. Sensitive fields must redact by
   default.
5. **Prove & Differentially Verify:** Core type/schema soundness and PII/FERPA
   non-interference belong in the Lean Core (`formal/`). Fast execution paths (vectorized VM
   and SQL pushdown) must match the naive reference oracle (`src/oracle/`).
6. **Honest Evidence:** A skipped check is not a pass. Report exact commands run and exact
   outcomes.

## Tooling on This Host

- Rust (`rustc` / `cargo`) for the zero-crate toolchain and runtime.
- Lean 4 (`/opt/elan/bin/lean`) for `formal/` proofs.
