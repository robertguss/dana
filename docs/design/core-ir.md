# Dana Core IR Specification (v0.1)

**Status:** Phase 0 design specification. Dana Core is the small, explicitly typed internal
language that every surface feature of Dana lowers to. It is the single formal contract
connecting four parts of the toolchain:

1. **The Rust front end** (`src/lower/`, `src/core/`)
2. **The Lean 4 formalization & `danacore` oracle** (`formal/`)
3. **The naive row-by-row Rust differential oracle** (`src/oracle/`)
4. **The relational query planner, SQL pushdown splitter, and vectorized columnar VM** (`src/plan/`, `src/vm/`)

Following [Mo Core](https://github.com/robertguss/mo), Dana Core is a **monomorphic, strict,
explicitly typed functional language**—extended with a **pure relational plan sub-calculus**
and **first-class sensitivity labels**. Generic surface code is monomorphized before
entering Core; there are no type variables in Core.

---

## 1. Design Principles

- **Small enough to prove in Lean:** Every surface convenience (`|>`, `.col` shorthand,
  `for`/`while`/`break`/`continue`/`return`/`try`, `schema` constraints, `examples`,
  `promise`) lowers away into a small, orthogonal set of Core constructors.
- **Explicit relational plans inside Core:** Relational operators (`Filter`, `Project`,
  `Join`, `GroupBy`, `Summarize`, `SuppressSmallGroups`, `Window`, `PivotWider`, …) remain
  first-class pure nodes in Core rather than desugaring into opaque loops. This allows:
  1. Lean to prove **schema soundness** and **PII/FERPA non-interference** directly over
     relational operators;
  2. the naive Rust oracle to evaluate plans directly row-by-row;
  3. the query planner to optimize and push prefixes down to SQLite/Postgres SQL;
  4. differential fuzzing to assert `lean == naive_oracle == vectorized_vm == sql_pushdown`.
- **Single source of truth for sensitivity:** Column tags, table `row_tags`, `order_tags`,
  `bucketed` flags, aggregate kinds, and capability `allows` sets are explicit in Core types
  so typing and privacy checking are one unified, decidable judgment.
- **Honest oracle boundaries:** External wire/codec operations that do not belong inside a
  theorem prover (e.g., real Postgres sockets, TLS, Parquet/XLSX binary decoders, SVG string
  rendering) have explicit typed signatures in Core and stop at a documented `outside`
  boundary in `danacore` while remaining fully checked for typing, capabilities, and
  non-interference.

---

## 2. Sensitivity & Metadata Algebra

```text
Tag      ::= Ident                               -- built-in or declared via `tag`
TagSet   ::= SortedUniqueList(Tag)               -- bounded join-semilattice (∅, ∪, ⊆)
AggKind  ::= Raw | GroupKey | Blending | NonBlending

ColSpec  ::= {
  name     : Ident,
  ty       : ScalarTy,
  tags     : TagSet,
  bucketed : Bool,                               -- true iff produced by `bucket(...)`
  agg_kind : AggKind                             -- tracks blending vs min/max/key
}

TableTy  ::= {
  cols           : List(ColSpec),                -- distinct column names, ordered
  row_tags       : TagSet,                       -- implicit-flow taint on row presence/count
  order_tags     : TagSet,                       -- implicit-flow taint on row order
  grouped_by     : Option(List(Ident)),          -- active grouping keys (if grouped/summarized)
  summarized     : Bool,                         -- true right after `Summarize`
  distinct_by    : Option(Ident)                 -- hidden distinct-entity key tracked for k-suppression
}
```

### Invariants Checked by the Core Verifier

1. Column names within `TableTy.cols` are strictly unique.
2. Every `Tag` in any `TagSet` is either built-in (`pii`, `ferpa`, `financial`, `health`,
   `secret`) or declared in the program's `tags` header.
3. `bucketed = true` is valid only on `Text` columns produced by `RelOp.Bucket` (or preserved
   unchanged through `Select`/`Rename`/`GroupBy`).
4. `SuppressSmallGroups` is valid **only** when the input table has `summarized = true`.

---

## 3. Types (`Ty` and `LTy`)

Every value expression in Core carries a **labeled type** `LTy = { ty: Ty, tags: TagSet }`.
For tables (`Ty.Table(TableTy)`), per-column tags live in `TableTy.cols` and table-level
context tags live in `TableTy.row_tags` / `TableTy.order_tags` (so outer `LTy.tags` is `[]`
for `Table` values and `tags` for `DynamicTable` values).

### 3.1 Scalar & Composite Types (`Ty`)

| Category | Core Constructors | Representation / Semantics |
| --- | --- | --- |
| **Primitives** | `Unit`, `Bool`, `Int`, `Decimal`, `Float`, `Text`, `Bytes` | `Int`: 64-bit signed, **checked** (overflow stops, never wraps). `Decimal`: exact fixed-point integer count of `10⁻¹⁸` within `±(2¹²⁷ − 1)` (matching Mo). `Float`: IEEE-754 binary64 (no silent `NaN` propagation in aggregations). |
| **Time** | `Date`, `Timestamp`, `Duration` | `Date`: proleptic Gregorian days since `1970-01-01`. `Timestamp`: UTC microseconds since epoch (IANA timezone ops explicit). `Duration`: signed whole microseconds. |
| **Missing & Errors** | `Option(Ty)`, `Result(Ty, Ty)` | One unified `Option` (`None`, `Some`) for all missing values (`T?`) across SQL, CSV, JSON, Parquet, XLSX. |
| **Collections & Records** | `Tuple(List(LTy))`, `List(LTy)`, `Map(LTy, LTy)`, `Data(Name)` | `Map` is insertion-ordered; structs and enums share `Data(Name)` looked up in the program's data table. |
| **Tables** | `Table(TableTy)`, `DynamicTable(TagSet)` | `Table` is statically typed; `DynamicTable` is produced only by `Crosstab` or REPL `untyped` readers. |
| **Reporting & Stats** | `Chart(TagSet)`, `Report(TagSet)`, `Profile(TagSet)`, `LinearModel`, `StatTest` | Charts, reports, and profiles carry their effective `TagSet` statically so unauthorized sensitive plots fail at compile time. |
| **Functions** | `Fn(List(LTy), pc: TagSet, LTy)` | Monomorphic function type with explicit caller `pc` bound. |
| **Capabilities** | `Args`, `Clock`, `Console(allows)`, `ReadFiles`, `WriteFiles(root, allows)`, `ReadDB(db)`, `WriteTable(db, table, dest_cols, dest_row_tags, allows)`, `RawReadDB(db)`, `HttpsAllow(host, allows)`, `Secret(name)`, `Declassify(allows)` | Capabilities are first-class values with no ambient authority; `allows: TagSet` is checked statically at every host operation. |

---

## 4. Expressions & Control Flow (`Expr`)

Dana Core keeps Mo Core's clean expression grammar, plus a `Plan` node for pure relational
pipelines:

```text
Expr ::=
  | Lit(Literal)                                 -- typed literal (tags = ∅)
  | Var(Ident)
  | ConstRef(Ident)                              -- read of ordered top-level constant
  | Let(Ident, LTy, Expr, Expr)
  | If(Expr, Expr, Expr)                         -- elevates pc by tags(cond) in branches
  | Case(Expr, List(CaseArm))                    -- exhaustive 1-level constructor match; elevates pc
  | Lam(List((Ident, LTy)), Expr)                -- closure
  | App(Expr, List(Expr))                        -- call closure
  | Call(Ident, List(Expr))                      -- call top-level function
  | Join(Ident, List((Ident, LTy)), Expr, Expr)  -- local tail join point (loops/return/try lower here)
  | Jump(Ident, List(Expr))                      -- tail jump to enclosing join point
  | Tuple(List(Expr)) | Proj(Expr, Nat)
  | Ctor(Name, CtorName, List(Expr))             -- struct / enum constructor
  | TableLit(TableTy, List(RowLit))              -- lowered Markdown `table ... end` literal
  | Prim(PrimOp, List(Expr))                     -- pure scalar / collection / stats primitives
  | Rel(Plan)                                    -- pure relational pipeline
  | Host(HostOp, List(Expr))                     -- capability-gated I/O, DB, HTTPS, Secret, Declassify
  | Stop(BugKind, Option(Expr))                  -- bug stop (redacts tagged detail automatically)
  | Fail(Expr)                                   -- spec-only assertion failure (test/example/promise)
```

### Lowering Surface Constructs to Core

- `for`, `while`, `break`, `continue`, `return`, and `try` lower to `Join` / `Jump` + `Case`
  (identical to Mo Core).
- `x ?? default` lowers to `Case(x, [Some(v) -> v, None -> default])`.
- `a |> f(b)` inside table pipelines lowers into nested `Plan` constructors; outside table
  pipelines, `a |> f(b)` lowers to `Call(f, [a, b])`.
- `schema S` definitions lower to `Data` metadata, schema-constraint validator functions,
  and initial `TableTy` descriptors (`col_tags`, `row_tags`).
- Inline `examples`, `promise`, and `test` blocks lower to top-level `spec` functions (just
  like Mo Core: only `spec` functions may call `Fail` or construct `DB.in_memory`,
  `Files.in_memory`, `Console.fake`, `Https.fake`, `Secret.fake`).

---

## 5. Pure Relational Plan Sub-Calculus (`Plan`)

Every node in `Plan` is **strictly pure** (no I/O, no mutation, no ambient clock/randomness).
This purity invariant guarantees safe query optimization, parallel batch execution, and SQL
pushdown:

```text
Plan ::=
  | SourceExpr(Expr)                             -- materialized/in-memory Table value
  | SourceDB(cap: Expr, table: Ident, ty: TableTy) -- ReadDB table scan (SQL pushdown root)
  | Select(Plan, List(Ident))
  | Drop(Plan, List(Ident))
  | Rename(Plan, List((Ident, Ident)))           -- (new_name, old_name)
  | Derive(Plan, List(DeriveItem))               -- scalar expr or audited `Bucket`
  | Filter(Plan, RowExpr)                        -- adds tags(pred) to row_tags
  | Distinct(Plan, List(Ident))                  -- adds tags(cols) to row_tags
  | Sort(Plan, List((Ident, SortDir)))           -- updates order_tags; public sort clears old order_tags
  | Limit(Plan, Nat)                             -- folds order_tags into row_tags
  | Join(JoinKind, Plan, Plan, JoinOn, Suffixes) -- fails loudly on cardinality violation (redacted)
  | Union(Plan, Plan)
  | GroupBy(Plan, List(Ident))
  | Summarize(Plan, List(AggItem), distinct_key: Option(Ident))
  | SuppressSmallGroups(Plan, min_k: Nat, distinct_by: Option(Ident), mode: SuppressMode)
  | Window(Plan, List(WindowItem))
  | FillGaps(Plan, col: Ident, step: Duration, over: List(Ident), fill: List((Ident, Literal)))
  | PivotWider(Plan, names_from: Ident, values_from: Ident, static_cols: List(Ident), fill: Literal)
  | Crosstab(Plan, rows: Ident, cols: Ident, values: Ident, fill: Literal)  -- yields DynamicTable
  | Redact(Plan, col: Ident, replacement: Text)  -- audited declassifier: clears col_tags(col)
  | Pseudonymize(Plan, col: Ident, secret: Expr) -- audited declassifier: clears [pii] via Secret cap
```

Where:
- `DeriveItem ::= ColExpr(Ident, RowExpr) | BucketCol(Ident, source: Ident, cuts: List(Literal), labels: List(Text))`
- `JoinKind ::= InnerOne | InnerManyToOne | InnerMany | LeftOne | LeftManyToOne | Semi | Anti`
- `JoinOn ::= SameKeys(List(Ident)) | Pairs(List((Ident, Ident)))`
- `AggItem ::= { name: Ident, op: AggOp, arg: Option(RowExpr) }` with `AggOp` partitioned into:
  - **Blending:** `Count`, `CountDistinct`, `Sum`, `Mean`, `Stddev`, `Variance`
  - **Non-blending:** `Median`, `Percentile(Float)`, `Min`, `Max`, `First`, `Last`
- `SuppressMode ::= Drop | MaskComplementary`

### Row Expressions (`RowExpr`)

`RowExpr` is the pure scalar expression language inside `Filter`, `Derive`, `Summarize`, and
`Window`. It may reference input columns (`Col(Ident)`), outer lexical `let` bindings
(`OuterVar(Ident)`), literals, pure `PrimOp`s, `If`/`Case`, and **pure top-level user
functions** (verified effect-free and termination-bounded or fuel-evaluated). Because
`RowExpr` compiles directly into vectorized batch instructions in the VM, user-defined helper
functions execute over 2,048-row chunks with **zero UDF cliff**.

---

## 6. Programs, Policy & Host Effects (`World`)

A Core `Program` consists of:

```text
Program ::= {
  version  : CoreVersion,                        -- 0.1
  tags     : List(Tag),                          -- declared custom tags
  policy   : Option(Policy),                     -- parsed optional `dana.policy` upper bound
  datas    : List(DataDecl),                     -- structs & enums
  schemas  : List(SchemaDecl),                   -- named table schemas & constraints
  consts   : List(ConstDecl),                    -- ordered, acyclic module constants
  funs     : List(FunDecl),                      -- kind ∈ { Function, Test, Example, Promise }
  entry    : Option(Ident),                      -- designated `main`
  metadata : CompilerMetadata                    -- spans/names for diagnostics; never read by semantics
}
```

### Policy Checking (`dana.policy`)

If `Program.policy` is `Some(P)`:
- Every `SuppressSmallGroups(min_k, ...)` must satisfy `min_k >= P.min_group_size`.
- If `P.forbid_manual_declassify`, no `Declassify` capability may appear in `entry` or any
  `HostOp.DeclassifyApprove`.
- Every `WriteFiles(root, allows)`, `HttpsAllow(host, allows)`, `WriteTable(db, tbl, ...,
  allows)`, and `Console(allows)` capability requested by `entry` must be a subset of the
  corresponding `allow` entry in `P`.

### World & Operational Semantics

Just like Mo Core, Dana Core's executable semantics is a deterministic big-step evaluator
indexed by fuel:

```text
eval : Nat -> Program -> Env -> PcLabel -> World -> Expr -> Outcome
```

Where:
- `World` holds real and independent fake states (`Args`, `Console`, `Files`, `DB` tables,
  `Https` mock responses, `Secrets`, `Clock`, and `PolicyRuntimeFlags` such as
  `allow_export: TagSet`).
- `Outcome` is one of:
  - `ok(Val, World)`
  - `stopped(Bug, World)` — runtime stop (integer overflow, division by zero, join
    cardinality violation, `promise` failure, file/DB error). Any sensitive value involved in
    a `Bug` is **redacted at construction** into `[REDACTED:tag]` while preserving public
    row indices, line numbers, column names, and counts.
  - `failed(Text, World)` — spec-only assertion failure.
  - `jumped(Ident, List(Val), World)` — internal tail jump (never escapes a well-typed
    program).
  - `wrong` — stuck state (proven unreachable by Theorem 1).
  - `outOfFuel` — fuel exhausted.

---

## 7. Canonical Wire Format (`(dana-core 0.1 ...)`)

Following Mo Core's `TEXT.md`, Rust and Lean exchange Core programs and execution reports
using a strict, canonical S-expression text protocol:

- **Header:** Every file begins with `(dana-core 0.1 PAYLOAD)` followed by a single LF (`\n`).
  Unknown versions are rejected immediately.
- **Formatting:** Single ASCII space between elements, no internal line breaks, no padding
  inside parentheses, case-sensitive constructor names matching Lean (`(unit)`, `(none)`,
  `(some ...)`, `(table-ty ...)`, `(rel (filter ...))`).
- **Strings:** Escaped with `\"`, `\\`, `\n`, `\r`, `\t`; all other control characters use
  lowercase shortest `\u{hex}`. Surrogates and raw control characters are rejected.
- **Observable Reports (`Report`):** For differential testing, `danacore` (Lean),
  `dana --oracle` (naive Rust), `dana run` (vectorized VM), and SQL pushdown tests all emit
  the same canonical **observable report** containing:
  - exit status (`ok` / `stopped` / `failed`),
  - redacted diagnostic payload (if stopped/failed),
  - real stdout/stderr lines,
  - final written file/DB table contents (canonical structural spelling),
  - fake handle snapshots (for spec runs).
- **Metadata separation:** `CompilerMetadata` (source spans, original parameter names) is
  preserved losslessly on the wire and validated for shape, but never read by typing,
  evaluation, or Lean proofs.

---

## 8. Formal Theorems Proved in Lean (`formal/`)

Phase 1 proves two main theorems over Dana Core IR (with zero `sorry`s and zero external
Lean dependencies beyond Lean's bundled library):

### Theorem 1 — Schema & Type Soundness (Progress & Preservation)

If `checkProgram P = ok` and `eval fuel P env [] world expr = out`, then:
1. `out ≠ Outcome.wrong` (well-typed programs never get stuck on missing columns, mismatched
   column types, unguarded `Option` unwraps, or ill-typed join keys).
2. Whenever `out = Outcome.ok(v, w')`, `v` conforms strictly to the static `LTy` (including
   exact `TableTy` column order, scalar types, nullability, and group-size invariants after
   `SuppressSmallGroups`).

### Theorem 2 — Termination- and Error-Insensitive Non-Interference (Up to Audited Declassifiers & Authorized Sinks)

Fix any observer clearance level `L : TagSet` (the tags the observer is authorized to learn).
Define `L`-equivalence (`≈_L`) on values, tables, and `World`s:
- Two values of type `LTy` with `tags ⊆ L` are `≈_L` iff they are identical.
- Two values with `tags ⊈ L` are always `≈_L` (arbitrary differences allowed).
- Two tables `T1, T2` with `row_tags ⊆ L` are `≈_L` iff they have identical row counts and
  every column `c` with `col_tags(c) ⊆ L` has identical values (modulo row order if
  `order_tags ⊈ L`); if `row_tags ⊈ L`, `T1` and `T2` are always `≈_L`.

**Theorem (2A–2D — Termination- and Error-Insensitive Non-Interference on `ok` runs):**
For any well-typed program `P` whose non-spec functions contain no `Pseudonymize`/
`SuppressSmallGroups`/`DeclassifyApprove` boundary clearing a tag outside `L`, whose output
sinks all satisfy `sink.allows ⊆ L`, whose declared `Data` types satisfy
`progDatasSortableForNI`, and whose stored DB tables satisfy `progRespectsDB`:
if `W1 ≈_L W2`, and both `runProgram fuel P W1` and `runProgram fuel P W2` complete normally
with `status = ok`, then their observable reports satisfy **`rep1 == rep2`** (identical
stdout, stderr, written files/tables, and fake handle snapshots).

**Theorem (2E — Redacted Explicit-Stop Non-Interference):**
Whenever an explicit `.stop kind (some detailExpr)` executes from publicly equivalent states
(`L = []`) and `detailExpr` evaluates normally on both runs, both runs stop with the exact
same `Bug` (sensitive payloads redacted to `[REDACTED:tag]`), preserve `WorldEquiv`, and emit
identical observable `ExecReport`s.

**Explicit Trust Boundary:**
- Timing, memory, termination, and stop/trap position divergence (`ok` vs. `stopped`) lie
  outside the static proof: because `extractReport` retains output emitted before a stop, the
  position of a runtime trap (e.g., `100 / (secret - i)` divide-by-zero or `Int64`/`Decimal`
  overflow) or an explicit `.stop` executed conditionally under a sensitive `pc` is observable
  and can leak an entire small-domain value in one run.
- Stored DB tables are trusted to match their declared `SourceDB` schemas (`progRespectsDB`).
- Audited declassifiers crossing `L` (`DeclassifyApprove`, `Pseudonymize`,
  `SuppressSmallGroups` clearing tags outside `L`) are explicitly excluded from `progSafeForNI`
  as the audited trust boundary.
- Binary wire/file codecs (`rawSqlQuery`, `httpsGetJson`, `readParquet`, `writeParquet`,
  `writeXlsx`) and `statsTTest` (which requires a Student-t CDF / incomplete beta function)
  return `BugKind.outsideBoundary` in the Lean Core oracle and are verified in the Rust
  runtime/oracle.
- Numeric/statistical oracle conventions: `variance`/`stddev` use population denominator (`/ n`,
  giving `some(0.0)` for `n = 1` and `none` for `n = 0`, with scaled deviations in `stddev`);
  `percentile(p)` requires finite `p ∈ [0.0, 1.0]` with linear interpolation; `Decimal`
  `median` uses exact scaled integer midpoint toward zero while `Float`/`Int` `median` uses
  `(lo / 2.0) + (hi / 2.0)`; `statsCorr`/`statsLinReg` reject non-finite inputs and scale
  deviations by `max |d|` to avoid overflow/underflow, with degenerate `statsLinReg` (`n < 2`,
  non-finite inputs, or zero `x`-variance) stopping with `BugKind.divByZero`.
- File-write path confinement: `.writeFile`, `.writeReportHtml`, `.writeParquet`, and
  `.writeXlsx` reject non-safe `relPath` values (empty, leading `/`, `\`, or any `".."`
  segment) by returning `Err(...)` without writing, and join `(root, relPath)` with a single
  `/` (`joinConfinedPath`) so a capability rooted at `"out"` writes `"out/_evil/x"`, never
  `"out_evil/x"`.

*Corollary:* Every direct or implicit flow of a sensitive tag `t ∉ L` into a public normal
output is **structurally guaranteed** to pass through either an explicitly audited
declassifier (`redact`, `pseudonymize`, `bucket` + `suppress_small_groups`) or an explicitly
authorized capability (`allows:` / `Declassify`)—never through an accidental filter, sort,
join, `bad_rows` message, or explicit `.stop` diagnostic payload.

---

## 9. Differential Oracle & SQL Pushdown Equivalence Contract

Alongside the Lean proofs (which operate on Core IR directly), Phases 2 and 3 enforce a
three-way differential invariant over randomized Core programs:

```text
Report(danacore_lean(P)) == Report(rust_naive_oracle(P)) == Report(rust_vectorized_vm(opt(P)))
```

And for database-backed plans (Phase 3):

```text
Report(rust_naive_oracle(P)) == Report(sqlite_pushdown(P)) == Report(postgres_pushdown(P))
```

Any disagreement—on values, `Option` nulls, `Decimal` rounding, join cardinality stops, or
redacted diagnostics—is treated as a compiler/optimizer bug and fails CI.
