# AGENTS.md

Guidance for coding agents (Claude Code, Codex, Antigravity, Cursor, and others) working in
this repository. `CLAUDE.md` imports this file.

## What this is

**Dana** is a pre-release, AI-first programming language and vectorized columnar runtime for
fast, private, database-native data work—the data sibling to
[Mo](https://github.com/robertguss/mo).

Phases 0, 1, and 2 (Design, Executable Grammar, Lean 4 Formal Core, Naive Rust Oracle,
Zero-Crate Toolchain, Streaming Formats/FFI, Relational Optimizer & 2,048-Row Vectorized
Columnar VM) are complete. Phase 3 (Databases & SQL Pushdown) is next. Run
`make check-all` after changes to `grammar/`, `examples/`, `formal/`, `src/`, or
`docs/reference/README.md`.

## Documents in Order of Authority

1. `docs/CHARTER.md` — locked-in v1 pillars, non-goals, and constraints.
2. `docs/reference/README.md` — the Dana Language Reference v0.1 (embedded into `dana guide`).
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
make test-diff             # run Lean/oracle/VM differential verification suites (5,000+ cases)
make check-all             # run grammar, formal, and oracle checks end-to-end
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
