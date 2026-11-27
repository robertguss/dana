# Dana

**An open-source, AI-first programming language for fast, private, database-native data work.**

Dana is the data sibling to [Mo](https://github.com/robertguss/mo). Where Mo is built for
long-running systems and living services, Dana is built for databases, ETL pipelines,
operational and financial analytics, practical statistics, and clean reporting—fast by
default, batteries included, and safe around sensitive data like PII and FERPA records.

> **Status: Dana v0.6 (`v0.6.8`, pre-1.0) — Exact Numerics, CSV Quarantine/Coercion, `coarsen`, SQLite `--attach`, PostgreSQL `TryParseIsoDate`/`TryParseDecimal`/DST Pushdown, PG Arrays, Covariant `ReadDB` `schema.lock`, & `dedupe_by` Complete (`v1.0` GA held for production soak).**
> Dana's 0-conflict Bison IELR(1) executable grammar (`make grammar`), Lean 4 formal core with
> soundness & non-interference proofs (`make formal`), **Zero-Crate Rust** compiler, 2,048-row
> vectorized columnar VM with pure-UDF bytecode inlining, direct streaming-columnar CSV/TSV &
> Apache Parquet I/O into `Val::Columnar(Arc<VmTable>)` (6.0×–11.4× faster and 6.7×–11.4× lower
> peak RSS than `v0.3.0`, outperforming Pandas by 3.9×–6.9× across all 4 workloads and beating
> Polars on W2 500k×50k Parquet join, W3 SQLite pushdown, and W4 Zstd Parquet + Stats + HTML5
> report), embedded SQLite (with `--attach` / `?attach=`) + native PostgreSQL v3.0 SQL pushdown
> runtime (`dedupe_by`, `coarsen`, `try_parse_date`, `try_parse_decimal`, calendar/DST ops,
> `known_not_null` join simplification, materialized parse/timezone CTEs, PG array decoding, and
> covariant `ReadDB` `schema.lock`), native Excel (`.xlsx`), capability-gated HTTPS, columnar
> `Stats` & `profile()`, standalone SVG/HTML/Markdown reporting, safe read-only `dana repl`,
> SHA-256 hash-pinned `vendor/` modules, 12-parser zero-crate fuzzer + adversarial privacy
> hardening suite, and prospective 4-model / 2-family AI learnability gate (`24/24` strict pass,
> `0` privacy leaks) are complete and verified. `v1.0` GA is intentionally held for production soak.

## Why Dana

Python's data ecosystem is remarkable, but it carries four structural headaches:

1. **The UDF cliff & runtime overhead:** Python is slow row-by-row, and stepping outside
   built-in C/Rust dataframe primitives drops speed by orders of magnitude.
2. **Supply-chain sprawl:** Doing real data work in Python usually pulls dozens or hundreds
   of transitive packages from PyPI.
3. **The SQL / ORM / DataFrame split:** Moving between raw SQL strings, ORMs, local files,
   and in-memory tables duplicates schemas, invites SQL injection, and copies data repeatedly.
4. **No native concept of sensitive data:** One stray `print(df.head())`, unmasked CSV export,
   or AI agent reading a crash traceback can leak PII or FERPA-protected student records.

Dana addresses all four at the language, compiler, and runtime level:

- **Native PII & FERPA sensitivity tracking:** Columns carry schema-level sensitivity tags
  (`[pii]`, `[ferpa]`, `[financial]`, `[health]`, `[secret]`, or custom `tag`s) that propagate
  automatically through expressions, filters, joins, windows, stats, and charts. Unauthorized
  sinks fail at compile time; crash reports, `dana dry-run` diffs, `profile()`, and `dana repl`
  auto-redact sensitive fields; FERPA small-cell suppression (`suppress_small_groups`),
  `bucket`, `redact`, and keyed HMAC-SHA256 `pseudonymize` are built in.
- **Unified relational pipelines with SQL pushdown:** Local CSV/TSV/JSONL (`.gz`/`.zst`),
  native Apache Parquet, Excel `.xlsx`, in-memory tables, embedded SQLite, and native
  PostgreSQL share one typed `|>` pipeline API. Eligible DB stages compile automatically into
  100% parameterized SQL, verified against offline `schema.lock` snapshots.
- **Own vectorized columnar VM, zero UDF cliff:** Built in **Zero-Crate Rust** (`std` only
  plus tiny audited C shims for SQLite, system OpenSSL TLS, and `zlib`/`zstd`), executing
  2,048-row contiguous columnar batches in parallel and inlining pure Dana UDFs directly into
  register bytecode.
- **Batteries-included analytics, charts & safe REPL:** Built-in `use Stats` (`corr`,
  `linear_regression`, Welch `t_test`, `chi_square`, `outliers`), `pivot_longer`/`pivot_wider`,
  `table.profile()`, standalone SVG & terminal charts, self-contained HTML5/Markdown reports,
  and a read-only, privacy-redacted `dana repl` with `untyped` exploration.
- **Human-readable, AI-first, formally verified:** Shares Mo's Ruby/Elixir readability
  (`fn ... end`, `?` predicates, `case`, exact `Decimal`, explicit capabilities, `examples`,
  `promise`, `dana guide`) and proves **schema/type soundness** and **PII/FERPA
  non-interference** over Dana Core IR in **Lean 4**.

## A taste of Dana

<!-- dana-example: file -->
```dana
## Summarizes scholarship applicants by program without exposing student PII/FERPA.
module ScholarshipReport

schema Student
  id: Int [pii]
  email: Text [pii]
  gpa: Decimal? [ferpa]
  program: Text
  enrolled_year: Int
  active?: Bool
end

schema Application
  student_id: Int [pii]
  requested: Decimal where . > 0
end

fn by_program(students: Table(Student), apps: Table(Application))
  promise unique(.program)
  promise all(.applicants >= 5)

  # Filter & select push down to SQLite / Postgres SQL; join_one fails loudly on duplicate keys;
  # suppress_small_groups declassifies [pii]/[ferpa] once k >= 5 distinct students.
  students
    |> where(.enrolled_year == 2026 and .active?)
    |> select(.id, .program, .gpa)
    |> join_one(apps, on: left.id == right.student_id)
    |> group_by(.program)
    |> summarize(
      applicants: count_distinct(.id),
      avg_gpa: mean(.gpa),
      total_requested: sum(.requested)
    )
    |> suppress_small_groups(min: 5, distinct_by: .id)
    |> sort_desc(.total_requested)
end
```

## Install

Download prebuilt release archives (`x86_64-linux` / `aarch64-macos`) from
[GitHub Releases](https://github.com/robertguss/dana/releases), or build from source with
Rust 1.90+ and the system C libraries behind `src/ffi/` (`zlib`, `zstd`, `sqlite3`, `openssl`):

```sh
# macOS (Apple Silicon / Intel)
brew install pkg-config openssl@3 zstd
cargo install --git https://github.com/robertguss/dana --tag v0.6.8

# Ubuntu / Debian
sudo apt-get install -y pkg-config libssl-dev libsqlite3-dev libzstd-dev zlib1g-dev
cargo install --git https://github.com/robertguss/dana --tag v0.6.8
```

## Quickstart CLI

Build the zero-crate toolchain (`cargo build --release`) and run Dana directly:

```sh
# Print the embedded Dana v0.6 Language Reference (or a specific section)
dana guide
dana guide Privacy

# Check types, schemas, privacy tags, and dana.policy ceilings offline
dana check examples/expenses.dana examples/enrollment-report.dana

# Execute inline `examples` and `test` blocks on the vectorized VM
dana test examples/

# Run a pipeline over CSV, Parquet, Excel, SQLite, or PostgreSQL
dana run examples/expenses.dana -- data/october.csv
dana run --db Seminary=sqlite:///path/to/seminary.db examples/enrollment-report.dana

# Inspect optimized plans, parameterized SQL pushdown, and sensitivity provenance
dana explain --dialect sqlite examples/enrollment-report.dana

# Preview redacted database/file writes strictly read-only
dana dry-run --db Seminary=sqlite:///path/to/seminary.db examples/registrar-sync.dana

# Launch the safe, read-only, privacy-redacted interactive REPL
dana repl --db Seminary=sqlite:///path/to/seminary.db
```

## Documentation & Benchmarks

- [Dana Language Reference v0.6](docs/reference/README.md): complete language, privacy, I/O,
  stats, charts, REPL, and CLI reference (embedded into `dana guide`), with every example
  parsed by the [0-conflict Bison IELR(1) grammar](grammar/README.md) (`make grammar`) and
  type-checked under `dana check`.
- [End-to-End Benchmarks vs. Python](benchmarks/RESULTS.md): reproducible real-world pipeline
  benchmarks comparing Dana v0.4 against Python stdlib/`sqlite3`, Pandas, and Polars across
  CSV+UDF ETL (`317.0 ms / 116.2 MiB`), 500k×50k columnar Parquet joins (`135.4 ms / 98.4 MiB`,
  **2.26× faster than Polars**), 250k-row SQLite pushdown + FERPA privacy (`96.0 ms / 21.3 MiB`,
  **5.62× faster than Polars**), and 200k-row Zstd Parquet stats & HTML5 reporting
  (`185.1 ms / 52.3 MiB`, **1.67× faster than Polars**), with exact cell-for-cell parity
  assertions and full `v0.3.0 -> v0.4.0` speedup & RSS comparisons.
- [AI Learnability Evaluation v0.3](docs/evals/learnability-v0.3-results.md)
  ([Prospective Protocol](docs/evals/learnability-v0.3.md)): blind 4-model / 2-family
  evaluation (`claude-sonnet-5-5`, `claude-haiku-5-5`, `gemini-4-neon`, `gemini-4-argon`)
  writing 6 unseen pipelines solely from `dana guide` — **24/24 (100%)** Stage 2 strict pass,
  **21/24 (87.5%)** Stage 1 first-shot functional pass, **0** privacy/policy leaks, and
  **100%** canonical formatting compliance.
- [Ten Sample Programs](examples/README.md): realistic `.dana` scripts across higher ed,
  SaaS, fintech, DevOps logs, healthcare, and exploratory statistics.
- [Design Charter v1](docs/CHARTER.md): locked-in design pillars, non-goals, and principles.
- [Privacy & Declassification Model](docs/design/privacy.md): sensitivity tag algebra,
  implicit flows, audited declassifiers, optional `dana.policy`, runtime redaction, and Lean
  non-interference contract.
- [Architecture Overview](docs/design/architecture.md): compiler pipeline, Dana Core IR,
  vectorized columnar VM, Lean verification boundary, and Zero-Crate Rust policy.
- [Dana Core IR Specification](docs/design/core-ir.md): monomorphic Core IR, pure relational
  `Plan` calculus, canonical S-expression wire protocol, and Lean soundness and non-interference
  theorems.
- [Roadmap](docs/ROADMAP.md): phase-gated build plan and verification gates.

## Verification

```sh
make check-all   # 0-conflict Bison grammar + Lean 4 proofs + Rust fmt/clippy/doc/test suite
make test-v06    # run v0.6 dogfood hardening suite (numerics, CSV, coarsen, SQLite attach, date pushdown, dedupe_by)
make check-v06   # full v0.6 gate: check-all + 12-parser fuzzer + differential soak/privacy + learnability harness
```

## License

Licensed under either of [Apache License, Version 2.0](LICENSE-APACHE) or
[MIT license](LICENSE-MIT), at your option.

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in Dana by you, as defined in the Apache-2.0 license, shall be dual
licensed as above, without any additional terms or conditions.
