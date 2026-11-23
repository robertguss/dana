# Dana Architecture Overview (v0.1 Draft)

**Status:** Phase 0 design blueprint. This document defines the planned compiler pipeline,
core contracts, execution engine, Zero-Crate Rust boundaries, and Lean verification split.
Where the future Language Reference (`docs/reference/README.md`) and this document disagree,
the Language Reference wins on user-observable semantics.

## 1. The Shape of the System

Dana ships as one self-contained executable, `dana`, with subcommands:
`check`, `run`, `test`, `format`, `repl`, `explain`, `dry-run`, `fake`, `infer-schema`,
`schema-sync`, and `guide`.

```text
┌────────┐  ┌────────┐  ┌─────────────────────────┐  ┌──────────────────┐
│ source ├─►│ parser ├─►│ names, structural table ├─►│ lowering to      │
│(.dana) │  │(syntax)│  │ types, taint & caps     │  │ Dana Core IR     │
└────────┘  └────────┘  │ (check)                 │  │ (lower)          │
                        └─────────────────────────┘  └────────┬─────────┘
                                                              │ Core IR (text/AST)
                                     ┌────────────────────────┼────────────────────────┐
                                     ▼                        ▼                        ▼
                            ┌────────────────┐     ┌────────────────────┐    ┌──────────────────┐
                            │ Lean formal    │◄───►│ Naive Rust oracle  │◄──►│ Query Planner &  │
                            │ model & proofs │     │ (row-by-row ref)   │    │ Pushdown Split   │
                            └────────────────┘     └────────────────────┘    └────────┬─────────┘
                                                                                      │
                                                       ┌──────────────────────────────┴──────────────┐
                                                       ▼                                             ▼
                                            ┌─────────────────────┐                     ┌───────────────────────┐
                                            │ SQL Pushdown Backend│                     │ Vectorized Columnar VM│
                                            │ (SQLite / Postgres) │───typed stream─────►│ (2,048-row batches,   │
                                            │ parameterized only  │                     │  parallel, streaming) │
                                            └─────────────────────┘                     └───────────┬───────────┘
                                                                                                    ▼
                                                                                        ┌───────────────────────┐
                                                                                        │ Capability Host Ops   │
                                                                                        │ (FS, DB, HTTPS, SVG,  │
                                                                                        │  redacted diagnostics)│
                                                                                        └───────────────────────┘
```

### Stage Responsibilities

1. **Front End (`syntax`, `check`):**
   - Parses `.dana` modules into an AST (no significant whitespace).
   - Resolves module imports (stdlib, project-local modules, and hash-pinned pure-by-default
     `vendor/` modules).
   - Checks boundary `schema` definitions, infers structural table types across every `|>`
     stage, checks unified `T?` missing-value handling, and checks sensitivity tags and
     capability requirements.
2. **Lowering & Dana Core IR (`lower`, `core`):**
   - Desugars surface constructs (`|>`, `.col` selectors, `examples`, `promise`, `schema`
     constraints) into **Dana Core IR**: a small, explicitly typed calculus combining scalar
     expressions, relational operators, sensitivity labels, and capability operations.
   - Dana Core IR has a canonical, deterministic text representation so the Rust toolchain
     and the Lean formalization exchange identical programs.
3. **Verification Oracles (`formal/`, `src/oracle/`):**
   - **Lean (`formal/`):** Formalizes Dana Core IR's typing, sensitivity-propagation,
     declassification, and operational semantics, proving **schema/type soundness** and
     **PII/FERPA non-interference**.
   - **Naive Rust Oracle (`src/oracle/`):** A tiny (~300-line) straightforward row-by-row
     evaluator over Dana Core IR used for high-volume differential fuzzing against both the
     vectorized VM and SQL pushdown backends.
4. **Query Planner & Pushdown Splitter (`plan`):**
   - Optimizes the pure relational plan (projection pruning, predicate pushdown, filter
     fusion, join reordering only when semantics/cardinality checks are preserved).
   - Splits database-backed subplans into a **pushdown prefix** (compiled to parameterized
     SQLite or Postgres SQL) and a **local suffix** executed by the vectorized VM.
   - Powers `dana explain` (printing SQL pushdown boundaries and sensitivity flow) and
     `dana dry-run` (executing write pipelines read-only to compute redacted diffs).
5. **Vectorized Columnar VM (`vm`):**
   - Stores tables in memory as streams of **column batches** (`Batch`, default 2,048 rows):
     each column is a contiguous typed array (`Vec<i64>`, `Vec<i128>` scaled `Decimal`,
     `Vec<f64>`, string/bytes offset buffers) paired with a bit-packed validity bitmap for
     `T?` nulls and compile-time sensitivity metadata.
   - Evaluates built-in ops *and* custom user scalar functions directly over column vectors
     in tight, cache-friendly, SIMD-amenable loops—eliminating Python's UDF cliff.
   - Streams batches out-of-core so files larger than RAM process with bounded memory, and
     parallelizes independent batch partitions safely across CPU cores using Rust's
     ownership/Send+Sync guarantees.
6. **Capability Host Operations (`host`):**
   - All external effects go through explicit capability tokens (`ReadFiles`, `WriteFiles`,
     `ReadDB`, `WriteTable`, `RawReadDB`, `HttpsAllow`, `Console`, `Clock`).
   - Every capability has a deterministic in-memory test double (`DB.in_memory`,
     `Files.in_memory`, `Console.fake`, `Https.fake`).
   - Runtime error formatting and `bad_rows` quarantine records consult sensitivity metadata
     to auto-redact tagged values unless explicitly authorized.

## 2. Four Core Contracts

Following Mo's discipline, four explicit contracts bind the subsystems together so no layer
silently drifts from another:

| Contract | Location (planned) | Connects |
| --- | --- | --- |
| **Dana Core IR** | `formal/` (Lean) & `src/core/` (Rust) + canonical text form | Front end, Lean proofs, naive oracle, planner |
| **Relational Plan & Batch ABI** | `src/plan/` & `src/vm/batch.rs` | Query planner, SQL pushdown, vectorized VM |
| **Built-in Primitives & Declassifiers** | `src/base/prims.rs` (single table of truth) | Checker, Core IR, Lean model, oracle, SQL pushdown, VM |
| **Capabilities & Host Ops** | `src/base/hostops.rs` | Checker, verifier, VM, host adapters, test fakes |

## 3. Zero-Crate Rust & Audited C Allowlist

To keep Dana's own supply chain as small and auditable as the user programs it runs:

- **Zero Rust crates:** `Cargo.toml` MUST have **zero** external crate dependencies
  (`dependencies = {}` and `dev-dependencies = {}`). All compiler, VM, parser, codec,
  statistics, SVG charting, and Postgres wire-protocol code is written in-tree against Rust
  `std`.
- **Audited C allowlist (maximum 3 external C components):** Only three battle-tested C
  foundations are linked via minimal, strictly audited `extern "C"` shims under `src/ffi/`:
  1. **SQLite** (single-file public-domain C amalgamation vendored in `third_party/sqlite/`)
  2. **System TLS / OpenSSL** (`libssl` / `libcrypto`) for Postgres TLS and capability-gated HTTPS
  3. **`zlib` / `zstd`** for gzip/zstd streaming, Parquet page compression, and `.xlsx` (ZIP)
- **No `unsafe` sprawl:** `unsafe` is strictly forbidden outside `src/ffi/` and explicitly
  documented SIMD/batch inner loops (if needed after profiling), enforced by `#![forbid(unsafe_code)]`
  in every other module.

## 4. Planned Repository Layout

```text
dana/
├── Cargo.toml                 # Zero third-party crates; workspace/binary definition
├── AGENTS.md                  # Guidance for coding agents (imported by CLAUDE.md)
├── docs/
│   ├── CHARTER.md             # Locked-in v1 pillars and non-goals
│   ├── ROADMAP.md             # Phase-gated build plan and status
│   ├── reference/             # Dana Language Reference (embedded into `dana guide`)
│   └── design/                # Architecture, privacy model, Core IR, formats, SQL pushdown
├── examples/                  # Realistic `.dana` programs validated by grammar & tests
├── grammar/                   # Executable reference grammar + parse corpus
├── formal/                    # Lean 4 specification & proofs of Dana Core IR
├── src/
│   ├── base/                  # Source spans, diagnostics, prims & hostops contracts
│   ├── syntax/                # Lexer, parser, AST, canonical formatter
│   ├── check/                 # Structural table types, taint/privacy & capability checker
│   ├── lower/                 # Desugaring to Dana Core IR
│   ├── core/                  # Core IR definitions, verifier, canonical text codec
│   ├── oracle/                # Compact naive row-by-row differential reference evaluator
│   ├── plan/                  # Relational optimizer, SQL pushdown splitter, explain, dry-run
│   ├── vm/                    # Vectorized 2,048-row columnar batch engine & parallel runner
│   ├── formats/               # CSV, JSON/JSONL, Parquet, XLSX, compression streams
│   ├── db/                    # SQLite adapter, native Postgres wire client, schema.lock
│   ├── stats/                 # Profile, descriptive stats, regressions, tests
│   ├── viz/                   # Zero-dependency SVG/terminal charts & HTML/Markdown reports
│   ├── repl/                  # Safe interactive REPL & one-liner runner
│   ├── ffi/                   # Minimal audited C shims (SQLite, TLS, zlib/zstd)
│   └── cli/                   # `dana` binary entrypoints & embedded `guide`
├── third_party/               # Vendored SQLite amalgamation (pinned & checksummed)
├── tests/                     # Unit, golden CLI, differential, and database integration tests
├── fuzz/                      # Parser and differential fuzz targets
├── learnability/              # Multi-model AI learnability benchmarks & protocols
└── ci/                        # Local & nightly verification scripts
```

## 5. Active Phase 0 Design Work

Before writing Phase 1/2 code, the remaining Phase 0 design deliverable must be completed and
approved:

1. ~~**Privacy & Declassification Semantics**~~ — completed in [`docs/design/privacy.md`](privacy.md).
2. ~~**Sample Programs**~~ — completed in [`examples/`](../../examples/README.md) (10 programs + `dana.policy`).
3. ~~**Dana Core IR Specification**~~ — completed in [`docs/design/core-ir.md`](core-ir.md).
4. **Dana Language Reference v0.1 & Executable Grammar (`docs/reference/README.md`, `grammar/`):**
   Complete readable reference (destined for `dana guide`) backed by an executable grammar
   that parses all 10 `examples/*.dana` files and every reference snippet cleanly.
