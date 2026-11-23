# Dana

**An open-source, AI-first programming language for fast, private, database-native data work.**

Dana is the data sibling to [Mo](https://github.com/robertguss/mo). Where Mo is built for
long-running systems and living services, Dana is built for databases, ETL pipelines,
operational and financial analytics, practical statistics, and clean reporting—fast by
default, batteries included, and safe around sensitive data like PII and FERPA records.

> **Status: Phase 0 (Design).** Dana is in its initial design phase before implementation
> begins. Design documents live under `docs/`. Contributions are not yet open.

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
  (`[pii]`, `[ferpa]`, or custom tags) that propagate automatically through expressions,
  filters, joins, and aggregations. Unauthorized sinks fail at compile time; crash reports
  and AI debug views auto-redact sensitive fields; FERPA small-cell suppression and
  consistent pseudonymization are built in.
- **Unified relational pipelines with SQL pushdown:** Local CSV/JSON/Parquet/XLSX files,
  in-memory tables, SQLite, and Postgres share one typed `|>` pipeline API. Database stages
  compile automatically into parameterized SQL, with offline `schema.lock` snapshots and
  redacted `dana dry-run` diffs before writes.
- **Own vectorized columnar VM, zero UDF cliff:** Built in **Zero-Crate Rust** (`std` only
  plus tiny audited C shims for SQLite, system TLS, and zlib/zstd), executing 2,048-row
  contiguous columnar batches in parallel with streaming support.
- **Human-readable, AI-first, formally verified:** Shares Mo's Ruby/Elixir readability
  (`fn ... end`, `?` predicates, `case`, `Decimal`, explicit capabilities, `examples`,
  `promise`, `dana guide`, multi-model learnability gates) and proves **schema/type
  soundness** and **PII/FERPA non-interference** over Dana Core IR in **Lean**.

## A taste of Dana

```ruby
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

  students
    |> where(.enrolled_year == 2026 and .active?)
    |> select(.id, .program, .gpa)               # pushes down to Postgres SQL
    |> join_one(apps, on: .id == .student_id)    # fails loudly on duplicate keys
    |> group_by(.program)
    |> summarize(
         applicants: count(),
         avg_gpa: mean(.gpa),
         total_requested: sum(.requested)
       )
    |> suppress_small_groups(min: 5)             # declassifies [ferpa] once k >= 5
    |> sort_desc(.total_requested)
end
```

## What's here

- [Design Charter v1](docs/CHARTER.md): the locked-in v1 pillars, non-goals, and design
  principles.
- [Privacy & Declassification Model](docs/design/privacy.md): sensitivity tag algebra,
  implicit flows, audited declassifiers, optional `dana.policy`, runtime redaction, and Lean
  non-interference contract.
- [Roadmap](docs/ROADMAP.md): phase-gated build plan from Phase 0 (Design) through Phase 5
  (Learnability & Hardening).
- [Architecture Overview](docs/design/architecture.md): compiler pipeline, Dana Core IR,
  vectorized columnar VM, Lean verification boundary, and Zero-Crate Rust policy.

## License

Licensed under either of [Apache License, Version 2.0](LICENSE-APACHE) or
[MIT license](LICENSE-MIT), at your option.

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in Dana by you, as defined in the Apache-2.0 license, shall be dual
licensed as above, without any additional terms or conditions.
