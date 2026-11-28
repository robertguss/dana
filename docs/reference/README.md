# Dana Language Reference, v0.7

**Version 0.7 (pre-1.0).** This is the complete, authoritative language reference for Dana,
embedded directly into `dana guide` for human authors and AI coding agents.

Every rule is illustrated with real syntax checked by Dana's 0-conflict IELR(1) grammar
(`make grammar`), and every complete module example (`<!-- dana-example: file -->`) compiles
cleanly under `dana check`. "An error" means the compiler rejects the program statically.
"Stops" means a running program traps on a runtime invariant (integer overflow, duplicate
join key, `.first!` on an empty table, failed `assert`/`promise`, or unauthorized runtime
export) and halts with a redacted report.

---

## 1. First Program & Execution Model

<!-- dana-example: file -->
```dana
## Totals a CSV file of expenses by category, largest first.
module Expenses

schema Expense
  date: Date
  category: Text where not .empty?
  amount: Decimal
end

fn summarize_by_category(expenses: Table(Expense)) : Table(category: Text, total: Decimal)
  promise unique(.category)
  promise sum(.total) == expenses.sum(.amount)

  expenses
    |> group_by(.category)
    |> summarize(total: sum(.amount))
    |> sort_desc(.total)
end

fn main(args: Args, files: ReadFiles, console: Console) : Int
  path = args.first.or_return(2)
  (expenses, bad_rows) = try files.read_csv(path, as: Expense)

  totals = summarize_by_category(expenses)
  console.print_table(totals)
  if bad_rows.empty?: 0 else: 1
end
```

Key design rules:

- **One file = one module.** The first code line is `module Name` (optional `##` doc comments
  may precede it).
- **Explicit capabilities, zero ambient authority.** `main` receives every I/O capability as a
  typed parameter (`Args`, `ReadFiles`, `WriteFiles(...)`, `ReadDB(...)`, `WriteTable(...)`,
  `RawReadDB(...)`, `HttpsAllow(...)`, `LocalHttpAllow(...)`, `LocalSocketAllow(...)`, `Console`,
  `Secret(...)`). Functions without capability parameters are **pure** and can run inside
  vectorized table pipelines.
- **Keyword-delimited blocks.** Blocks open with `schema`, `struct`, `enum`, `fn`, `if`
  (block form), `case`, `for`, `while`, `table`, `examples`, or `test`, and close with `end`.
  Indentation is purely stylistic (`dana format` uses 2 spaces).
- **Zero friction on public data.** Schemas with no `[tag]` annotations carry empty tag sets
  and require no privacy boilerplate anywhere.
- **Direct streaming-columnar I/O & vectorized VM.** By default (`dana run`), CSV/TSV
  (`read_csv`, `read_tsv`) and Apache Parquet (`read_parquet`, `write_parquet`) stream directly
  into and out of 2,048-row contiguous columnar batches (`VmTable`) — feeding relational
  pipelines, inlined pure UDFs, `Stats.*`, `table.profile()`, and CSV/JSONL/Parquet writers
  without row-oriented boxing while preserving 100% parity with `dana run --oracle`.
- **Vectorized VM & SQL pushdown.** `dana run` compiles pipelines to Dana's 2,048-row
  vectorized columnar VM with automatic SQLite/PostgreSQL SQL pushdown and pure-UDF bytecode
  inlining (`dana run --oracle` executes the naive row-by-row reference oracle).

---

## 2. Source Text & Syntax

### 2.1 Files, Modules & Imports

Module `Seminary.Enrollment` maps to `seminary/enrollment.dana` (`CapCase` segments become
lowercase hyphenated paths; `CourseOutcomes` -> `course-outcomes.dana`).

```text
module MyApp
expose public_fn, MySchema, MyEnum(..)
use Stats
use Helpers
use Helpers { helper_a, HelperType }
```

- Built-in stdlib namespaces (`Stats`, `Report`, `Table`, `Json`, `Args`, `Files`, `DB`, `Console`,
  `Https`, `LocalHttp`, `LocalSocket`, `Secret`) require no disk files; declare `use Stats` when calling `Stats.*`.
- Source files are UTF-8. Invisible formatting/bidi/zero-width control characters are a lexing
  error anywhere in source, including comments and strings; write `"\u{200B}"` instead.

### 2.2 Comments

- `#` starts a line comment through end of line.
- `##` starts a doc comment for the module header or the declaration immediately below it.

### 2.3 Naming Conventions, Atoms & Keywords

- `snake_case`: variables, parameters, functions, columns, schema fields (`student_id`, `net_price`).
- `?` suffix: boolean values and predicates (`active?`, `empty?`, `some?`, `none?`, `contains?`).
- `!` suffix: trapping operations (`first!`).
- `CapCase`: modules, schemas, structs, enums, enum constructors, capability types (`Student`,
  `Ok`, `Error`, `ReadFiles`).
- `_` discards a value; `_name` marks an intentionally unused binding.
- **Atoms:** `:snake_case` symbolic options (`:month`, `:year`, `:day`, `:hour`, `:minute`,
  `:pearson`, `:spearman`, `:zscore`, `:iqr`, `:drop`, `:mask`).

Reserved keywords:

```text
and assert break case const continue else end enum examples expose false fn
for if in is module none not or promise return schema stop struct table
test true try use var while
```

Contextual words:

- `where` introduces column constraints in `schema` and filters rows in `|> where(...)`.
- `tag` declares custom sensitivity tags (`tag donor`) and remains usable as a variable/column
  name (`.tag`).
- After `.`, `table`, `where`, `tag`, and capitalized column names (`.M0`, `.Q1`) are valid
  member names (e.g., `db.table(Student)`, `.M0 - .M3`).
- Named-argument labels (`as`, `on`, `from`, `left`, `right`, `allows`, `over`, `order`, `cuts`,
  `labels`, `columns`, `cols`, `names_from`, `values_from`, `names_to`, `values_to`, `fill`,
  `key`, `sheet`, `sheets`, `method`, `threshold`, `flag`, `bins`, `trendline`, `title`,
  `params`, `headers`, `fields`, `responses`, `every`, `rows`, `by`, `min`, `distinct_by`,
  `mode`, `seed`, `private`, `sanitize_formulas`, `sub`, `prefix`, `suffix`, `start`, `len`,
  `list`, `lo`, `hi`, `step`, `suffixes`) are ordinary identifiers.

### 2.4 Line Breaks & Continuations

Newlines terminate statements (no semicolons). Newlines are ignored inside `(...)`, `[...]`,
and `{...}`, after an opening delimiter, `,`, `.`, `=`, `|>`, or any binary operator, and
immediately before a closing delimiter, `.`, `|>`, or any binary operator other than unary `-`.

---

## 3. Values, Literals & Types

### 3.1 Built-In Scalar & Time Types

| Type | Literals / Construction | Exact Semantics |
| --- | --- | --- |
| `Bool` | `true`, `false` | Logical truth values |
| `Int` | `0`, `42`, `1_000_000`, `-7` | Checked 64-bit signed integer; overflow stops |
| `Decimal` | `12.50`, `0.00`, `100.0` | Exact fixed-point (`10⁻¹⁸` scale, `±(2¹²⁷ − 1)`) |
| `Float` | `1.5e-4`, `1e-9`, `0.95` (in `Float` context) | IEEE-754 binary64 for statistical/scientific math |
| `Text` | `"hello"`, `"""..."""`, `"x=#{v}"` | UTF-8 string; triple-quoted blocks auto-dedent and process standard backslash escapes (`\"`, `\\`, `\n`) |
| `Bytes` | Binary payloads (Parquet / SQLite `BLOB`) | Raw byte sequence |
| `Date` | `2026-10-01` | Proleptic Gregorian calendar date (`YYYY-MM-DD`) |
| `Timestamp` | `2026-10-01T14:30:00Z` | UTC instant (microsecond precision) |
| `Duration` | `5.seconds`, `5.minutes`, `2.hours`, `30.days` | Exact signed elapsed time (microseconds) |
| `Unit` | `Unit` | Empty value |

### 3.2 Exact `Decimal` vs. `Float` Rules (Important!)

1. **Literal default:** A bare decimal literal such as `12.50` or `0.0` defaults to **`Decimal`**.
   It becomes **`Float`** automatically when:
   - it uses scientific notation (`1.5e-4`, `1e-9`), **or**
   - the surrounding expected type is `Float` or `Float?` (a `Float` schema column, `Float`
     function parameter, `var x: Float = 0.0`, or binary operation against a `Float` value).
2. **No implicit mixed-type variable arithmetic:** Adding/multiplying/dividing non-literal
   values of different numeric types (`Int + Decimal`, `Decimal + Float`, `Int / Float`) is a
   **compile error**. Convert explicitly:
   - On `Int`: `.to_decimal` -> `Decimal`, `.to_float` -> `Float`, `.abs` -> `Int`.
   - On `Decimal`: `.to_float` -> `Float`, `.abs` -> `Decimal`, `.round(n, [mode: :half_away | :half_even])` -> `Decimal`, `.ceil` / `.floor` / `.trunc` / `.to_int` -> `Int` (traps on `DomainError` if out of 64-bit `Int` range).
   - On `Float`: `.abs` -> `Float`, `.round(n, [mode: :half_away | :half_even])` -> `Float`, `.ceil` / `.floor` / `.trunc` / `.to_int` -> `Int` (traps on `DomainError` on `NaN`, infinite, or out-of-range inputs).
   - There is intentionally **no** `.to_decimal` on `Float` (keep exact money/financial values
     as `Decimal` from the schema boundary).
3. **Scalar text, numeric, parsing & time helpers** (available both in normal expressions and
   inside row expressions `where`/`derive`):
   - `Text`: `a + b` (concatenation), `#{expr}` (interpolation), `.len : Int` (UTF-8 character
     count; pushes down to SQL `LENGTH(...)`), `.empty?`, `.trim`, `.ascii_lowercase`, `.lower`,
     `.upper`, `.slice(start, len)` (UTF-8 char slicing; negative `start` counts from end,
     `len <= 0` returns `""`), `.contains?("sub")`, `.starts_with?("prefix")`,
     `.ends_with?("suffix")`.
   - **Safe parsing on `Text`** (trims ASCII whitespace, returns `T?`, never traps):
     `.try_parse_date : Date?`, `.try_parse_int : Int?`, `.try_parse_decimal : Decimal?`,
     `.try_parse_float : Float?`.
   - **Numeric bounding & quantization:** `.clamp(lo, hi)` (on `Int`/`Decimal`/`Float`;
     traps on `DomainError` if `lo > hi` or `NaN` bounds) and `.round_to(step, [mode: :half_away | :half_even])`
     (on `Float`; quantizes to multiples of `step > 0` with `:half_away` [default] or
     `:half_even` banker's rounding; traps on `step <= 0` or non-finite inputs). Inside `derive(...)`,
     `.round_to(...)` marks the resulting column as coarsened (`bucketed = true`).
   - **List membership:** `val.in?(list) : Bool` works across `Bool`, `Int`, `Decimal`, `Float`,
     `Text`, `Date`, `Timestamp`, `Duration`, and `Option(T)` (returning `false` when `none`).
   - `Date` / `Timestamp`: `.year : Int`, `.add_days(n: Int) : Date` (or `add_days(d, n)`),
     `days_between(.d1, .d2) : Int`, `months_between(.d1, .d2) : Int`,
     `date_trunc(.d, :month)` (also `:year`, `:day`, `:hour`, `:minute`),
     `date_trunc(.ts, 5.minutes)`, `.d.at_midnight_in_tz("America/New_York") : Timestamp`
     (or `at_midnight_in_tz(d, tz)`), `.ts.in_tz("America/Chicago") : Text`,
     `.ts.date_in_tz("America/Chicago") : Date`, `ts + dur : Timestamp`, `ts1 - ts2 : Duration`.

<!-- dana-example: fragment -->
```dana
pct = ((active.to_decimal / total.to_decimal) * 100).round(1)
ratio = (count.to_float / 100.0).round(4)
local_day = ts.date_in_tz("America/New_York")
msg = "Retention: #{pct}% on #{local_day}"
```

### 3.3 Missing Values (`T?`) & Errors (`Result`)

Dana unifies SQL `NULL`, empty CSV cells, JSON `null`, Parquet nulls, and Excel blanks into
`Option(T)`, written `T?` (`Decimal?`, `Float?`, `Text?`), with literal `none`.

- Coalesce with `??` (`opt_val ?? 0.0`); right-hand side is short-circuited.
- Test presence with `.some?` and `.none?`.
- Compare directly with `==` / `!=` against `T` or `none`.
- Recoverable I/O errors return `Result(T, E)` (`Ok(v)` / `Error(e)`). Prefix `try expr`
  unwraps `Ok(v)` and propagates `Error(e)` (returning early in functions returning `Result`,
  or failing cleanly in `main`).
- On `Option(T)` (such as `args.first`), `.or_return(fallback_return_value)` unwraps `Some(v)`
  or returns `fallback_return_value` from the enclosing function.

### 3.4 Collections, Tuples, Structs & Enums

- **Tuples:** `(A, B)`, destructured via `(rows, bad_rows) = ...`.
- **Lists:** `[1, 2, 3] : List(Int)` with `.size` (or `.len`), `.empty?`, `.first : T?`,
  `.first! : T`, and immutable `.append(x)`.
- **Maps:** `{"Authorization": "Bearer #{token}"}` or `{requests: 0}` (`Map(K, V)`), indexed
  via `m[key] : V?`.
- **Named records (`struct`) & tagged unions (`enum`):**

<!-- dana-example: file -->
```dana
module TypesDemo

struct MetricSummary
  matched_count: Int
  matched_total: Decimal
end

enum Status
  Balanced
  Variance(delta: Decimal)
end

fn describe(s: Status) : Text
  case s
    Balanced: "ok"
    Variance(d): "off by #{d}"
  end
end

test "struct and enum work cleanly"
  m = MetricSummary(matched_count: 2, matched_total: 150.00)
  assert m.matched_count == 2
  assert describe(Variance(-5.25)) == "off by -5.25"
end
```

---

## 4. Schemas, Constraints & Sensitivity Tags

Named `schema` declarations sit at data boundaries (files, databases, public APIs). Inside
pipelines, Dana infers structural table types `Table(col1: T1, col2: T2, ...)` automatically.

- Column constraints use `where` with `.` referring to the column value (`. > 0`,
  `. >= 0.00 and . <= 4.00`, `not .empty?`, `.contains?("@")`). Rows violating a constraint
  during `read_csv`/`read_jsonl`/`read_xlsx` are routed to `bad_rows` with
  `error_kind == "ConstraintFailed"`.
- Built-in sensitivity tags: `pii`, `ferpa`, `financial`, `health`, `secret`.
- Custom sensitivity tags: declare `tag name` at module level (e.g., `tag donor`,
  `tag counseling`).
- Attach tags to individual columns (`email: Text [pii]`) or to an entire schema when row
  existence itself is sensitive (`schema CounselingVisit [counseling]`).

<!-- dana-example: fragment -->
```dana
tag counseling

schema Student
  student_id: Int [pii]
  email: Text [pii] where .contains?("@")
  gpa: Decimal? [ferpa] where . >= 0.00 and . <= 4.00
  program: Text where not .empty?
  active?: Bool
end

schema CounselingVisit [counseling]
  student_id: Int [pii]
  visit_date: Date
  duration_min: Int where . > 0
end
```

---

## 5. Expressions, Operators & Control Flow

### 5.1 Operator Precedence (Lowest to Highest)

1. Pipe: `|>` (left-associative)
2. Logical OR: `or` (short-circuiting)
3. Logical AND: `and` (short-circuiting)
4. Logical NOT: `not` (prefix)
5. Comparisons & type test: `==`, `!=`, `<`, `<=`, `>`, `>=`, `is` (non-associative)
6. Missing-value coalesce: `??` (right-associative, short-circuiting)
7. Additive: `+`, `-`
8. Multiplicative: `*`, `/`, `%`
9. Unary prefix: `-`, `try`
10. Postfix: `.member`, `.method(args)`, `(args)`, `[index]`

### 5.2 Bindings & Control Flow

- Immutable binding: `x = expr`. Mutable variable (required before reassigning): `var x = 0`
  (optionally typed: `var d: Decimal = 5.0`).
- **Inline `if` expression** (uses `:` and **no `end`**; valid across multiple lines and inside `derive`/`where`):
  `if cond:\n  a\nelse if cond2:\n  b\nelse:\n  c`.
- **Block `if` statement/expression** (no `:`, closed by `end`): `if cond \n ... \n else \n ... \n end`.
- **Pattern matching `case ... end`:** matches constructors (`Ok(v)`, `Error(e)`, `Some(x)`,
  `None`), literals, lists (`[]`, `[p]`, `[a, b]`), tuples, and wildcard `_`.
- **Loops:** `for x in items ... end` (iterates lists or table rows), `while cond ... end`,
  with `break`, `continue`, and `return` supporting optional trailing guards
  (`break if not more`, `return 2 if bad`).
- **Constants & Lambdas:** `const MAX_ROWS = 1000`, `fn(x) x + 1 end`.

<!-- dana-example: fragment -->
```dana
grade = if score >= 90: "A"
  else if score >= 80: "B"
  else: "C"

var total = 0
for row in rows
  total = total + row.qty
end

val = case res
  Ok(n): n
  Error(_): 0
end
```

---

## 6. Tables & Relational Pipelines (`|>`)

Every `Table(...)` carries a compile-time schema: ordered columns `(name, ScalarTy, col_tags)`
plus table-level context tags (`row_tags`, `order_tags`). Table pipelines are **strictly pure**
so Dana can optimize them, push eligible prefixes down into parameterized SQL, and execute
local stages in parallel 2,048-row columnar batches.

### 6.1 Markdown Table Literals

Literal tables use Markdown pipe syntax with normal Dana expressions in cells (including
`none`, which automatically widens that column to `T?`; columns containing only `none`
adopt the target `T?` type from a surrounding parameter, return, or binding annotation):

<!-- dana-example: fragment -->
```dana
sample = table
  | section_id | enrolled | avg_hours | completion |
  | "S1"       | 20       | 4.0       | 0.75       |
  | "S2"       | 15       | none      | 0.60       |
end
```

### 6.2 Complete Pipeline Verbs Reference

| Verb | Exact Signature & Semantics |
| --- | --- |
| `where` | `where(pred)` — Filter rows (`Bool` row expr). Adds referenced column tags to `row_tags`. |
| `select` | `select(.a, alias: .old_b)` — Keep/reorder/alias columns (at least one). Does NOT taint `row_tags`. |
| `drop` | `drop(.a, .b)` — Remove columns (cannot drop all columns). |
| `rename` | `rename(new_name: .old_name, ...)` — Rename columns in place. |
| `derive` | `derive(x: expr, y: bucket(...), z: coarsen(...))` — Add or replace computed columns (pure row exprs, audited coarseners, & pure UDFs). |
| `sort_by` | `sort_by(.a, desc(.b), asc(.c))` — Deterministic **stable** multi-key sort (`asc(.col)` or bare `.col` ascending with `none` first; `desc(.col)` descending with `none` last; trailing `:asc`/`:desc` also accepted). Adds key tags to `order_tags`. |
| `sort_desc` | `sort_desc(.a, .b)` — Deterministic **stable** descending sort (`none` sorts last). Adds key tags to `order_tags`. |
| `distinct` | `distinct(.a, .b)` or `distinct()` — Deduplicate rows. Adds key tags to `row_tags`. |
| `dedupe_by` | `dedupe_by(.k1, ..., [order_by: [asc/desc(.col)], keep: :first | :last])` — Deterministic keyed deduplication keeping `:first` (default) or `:last` row per key tuple (`order_by:` defaults to input order). Adds key and `order_by` tags to `row_tags`. |
| `limit` | `limit(n)` — Keep first `n` rows (constant non-negative integer). Folds `order_tags` into `row_tags`. |
| `group_by` | `group_by(.a, .b)` — Set grouping keys for `summarize`. Adds key tags to `row_tags`. |
| `summarize` | `summarize(n: count(), avg: mean(.x), ...)` — Aggregate per group (or whole table if ungrouped). |
| `suppress_small_groups` | `suppress_small_groups(min: k, distinct_by: .id)` (opt. `mode: :drop \| :mask`) — Audited k-anonymity declassifier immediately after `summarize`. |
| `suppress_small_cells` | `suppress_small_cells(by: [.c1, ...], min: k)` (opt. `distinct_by: .id`) — Audited row-level k-anonymity suppression keeping rows in classes with `>= k` rows (or distinct values); requires zero `[pii]`/`[secret]` columns. |
| `shuffle` | `shuffle(seed: Int)` — Deterministic SplitMix64 Fisher-Yates row permutation clearing `order_tags`. |
| `window` | `window(c: win_fn, ..., over: [.g], order: .t)` — Partitioned/ordered window computations (`over: []` for whole table). |
| `fill_gaps` | `fill_gaps(.t, every: 5.minutes, over: [.g], fill: {col: 0})` — Fill missing time buckets; unfilled non-key columns become `T?`. |
| `pivot_wider` | `pivot_wider(names_from: .k, values_from: .v, columns: ["M0", "M3"], fill: 0.0)` — Statically typed wide table with compile-time column list. |
| `pivot_longer` | `pivot_longer(cols: [.a, .b], names_to: "metric", values_to: "val")` — Unpivot columns into `(names_to: Text, values_to: unified_ty)`. |
| `crosstab` | `crosstab(rows: .r, cols: .c, values: .v, fill: 0)` — Dynamic display matrix returning `DynamicTable`. |
| `union` | `union(other)` — Concatenate two tables with identical column names and types (unions tags). |
| `redact` | `redact(.col)` — Replace column with `"[REDACTED]"` (`Text`), clearing `col_tags(.col)`. |
| `pseudonymize` | `pseudonymize(.col, key: secret)` — Keyed HMAC-SHA256 `Text` token, clearing `[pii]`. |

`sort_by` supports single-call mixed directions via `asc(.col)` / `desc(.col)` (for example,
`|> sort_by(desc(.total_amount), asc(.category))`). Both `sort_by` and `sort_desc` are
deterministic **stable** sorts, so chaining them produces equivalent tie-breaks:
`|> sort_by(.category) |> sort_desc(.total_amount)` sorts descending by `.total_amount` with ties
broken ascending by `.category`.

### 6.3 Aggregates Inside `summarize(...)`

| Aggregate | Return Type | Blending? (Clears under `suppress_small_groups`) |
| --- | --- | --- |
| `count()` | `Int` | Yes (blending) |
| `count_distinct(.col)` | `Int` | Yes (blending; enables `distinct_by: .col`) |
| `count_if(cond)` | `Int` | Yes (blending; pushes SQL `SUM(CASE WHEN cond THEN 1 ELSE 0 END)`) |
| `sum(.col)` | `Int` / `Decimal` / `Float` | Yes (blending; `0` on empty) |
| `mean(.col)` | `Decimal?` (if `Decimal`) or `Float?` | Yes (blending) |
| `stddev(.col)`, `variance(.col)` | `Float?` | Yes (blending) |
| `median(.col)` | `Decimal?` or `Float?` | **No** (stays tagged — order statistic) |
| `percentile(.col, 0.95)` | `Float?` | **No** (stays tagged — order statistic) |
| `min(.col)`, `max(.col)`, `first(.col)`, `last(.col)` | `T?` | **No** (stays tagged — extreme/single-row) |

Post-aggregate expressions (including coalescing and arithmetic over aggregates) work directly
inside `summarize`:
`summarize(base_mean: mean(.latency_ms) ?? 0.0, active_rate: count_if(.active).to_decimal / count().to_decimal)`.

### 6.4 Window Functions Inside `window(...)`

Supported window calls in `window(out_col: ..., over: [.g1, ...], order: .t)` (also accepts
`over: []`, `over: .g`, or `order: [.a, .b]`):

- `row_number() : Int` — 1-based row index within partition.
- `rank(.col) : Int` — Competition rank within partition.
- `lag(.col, n) : T?` and `lead(.col, n) : T?` — Value `n` rows before/after (offset defaults to `1`).
- `running_sum(.col) : Int | Decimal | Float` — Cumulative sum up to current row.
- `rolling_mean(.col, rows: k) : Float?` (or `rolling_mean(.col, k)`) — Trailing `k`-row moving
  average within each partition (inclusive of the current row). On leading partial windows
  (`< k` rows), averages the available leading rows (e.g., for `rows: 3`, row 1 averages row 1
  and row 2 averages rows 1–2) rather than returning `none`. `none` values inside the window are
  skipped (excluded from numerator and denominator); returns `none` only when all rows in the
  window are `none`.
- Compound delta subtraction: `delta: .students - lag(.students, 1) : Int? | Decimal? | Float?`.

### 6.5 `pivot_longer`, `pivot_wider`, `fill_gaps` & `crosstab`

<!-- dana-example: file -->
```dana
module ReshapeDemo

schema QuarterlySales
  region: Text
  q1: Decimal
  q2: Decimal
  q3: Decimal
end

fn to_long(wide: Table(QuarterlySales))
  wide
    |> pivot_longer(cols: [.q1, .q2, .q3], names_to: "quarter", values_to: "revenue")
    |> sort_by(.region, .quarter)
end

test "pivot_longer and pivot_wider round-trip cleanly"
  wide = table
    | region  | q1     | q2     | q3     |
    | "North" | 100.00 | 120.00 | 150.00 |
  end
  long = to_long(wide)
  assert long.count() == 3
  assert long.first!.quarter == "q1"
  assert long.first!.revenue == 100.00

  back = long
    |> pivot_wider(
      names_from: .quarter,
      values_from: .revenue,
      columns: ["q1", "q2", "q3"],
      fill: 0.00
    )
  assert back.first!.q2 == 120.00
end
```

- `pivot_longer` automatically widens numeric/optional column types (`Int` + `Decimal` ->
  `Decimal`, `T` + `T?` -> `T?`) and unions sensitivity tags of all melted columns onto
  `values_to`.
- `pivot_wider` requires compile-time string literals in `columns: [...]` so downstream code
  can reference `.M0`, `.q2`, etc. safely at compile time.
- `crosstab(rows: .r, cols: .c, values: .v, fill: 0)` handles data-dependent columns and
  returns a display-only `DynamicTable` (printable via `console.print_table`).

### 6.6 Explicit-Cardinality Joins

Joins declare expected cardinality so unexpected duplicate keys **stop loudly at runtime**
instead of silently multiplying rows:

- `join_one(other, on: ...)` — 1:1 inner join (both sides must have unique keys).
- `join_many_to_one(other, on: ...)` — N:1 inner join (right side must have unique keys).
- `join_many(other, on: ...)` — N:M inner join (duplicates allowed on both sides).
- `left_join_one(other, on: ...)` — 1:1 left outer join (right columns widen to `T?`).
- `left_join_many_to_one(other, on: ...)` — N:1 left outer join (right columns widen to `T?`).
- `semi_join(other, on: ...)` — Keep left rows with a match in `other` (left schema unchanged).
- `anti_join(other, on: ...)` — Keep left rows with NO match in `other` (left schema unchanged).

Key syntax & collision rules:

- Same key name(s): `on: .order_id` or `on: [.tenant_id, .order_id]`.
- Different key names: `on: left.cust_id == right.id` (keeps both key columns).
- Overlapping non-key column names are a **compile error** unless you `select`/`drop` first or
  pass `suffixes: ("_left", "_right")`.

<!-- dana-example: fragment -->
```dana
enriched = orders
  |> left_join_one(paid_by_order, on: .order_id)
  |> join_many_to_one(customers, on: left.cust_id == right.id, suffixes: ("_order", "_cust"))
```

### 6.7 Table Scalar Helpers & Pure UDFs (Zero UDF Cliff)

Scalar helpers on any `Table(...)`:

- `tbl.count() : Int` — Row count (inherits `row_tags`).
- `tbl.empty? : Bool` — True when 0 rows (inherits `row_tags`).
- `tbl.first! : Row` — First row record (stops if table is empty; inherits `row_tags` + `order_tags`).
- `tbl.sum(.col) : Int | Decimal | Float` — Non-optional column sum (`0` on empty table).
- `tbl.mean(.col) : Decimal? | Float?` — Returns **`Option`** (`none` on empty/all-null) — coalesce with `?? 0.0` (or `?? 0.00`).
- `tbl.stddev(.col) : Float?` — Returns **`Option`** (`none` when `< 2` non-null values) — coalesce with `?? 1.0`.
- `tbl.profile() : Profile` — Privacy-redacted dataset profile.
- `Table.concat(list_of_tables)` — Concatenates a `List(Table(S))`.

**Pure UDFs inside pipelines:** Any top-level pure `fn` (no capability parameters) may be
called directly inside `where(...)`, `derive(...)`, or `summarize(...)`. Non-recursive pure
UDFs without early `return` are automatically inlined into flat vectorized register bytecode on
Dana's 2,048-row columnar VM:

<!-- dana-example: file -->
```dana
module UdfDemo

schema Item
  sku: Text
  unit_price: Decimal
  qty: Int
end

fn discounted_total(price: Decimal, qty: Int) : Decimal
  gross = price * qty.to_decimal
  if qty >= 10: gross * 0.90 else: gross
end

fn price_items(items: Table(Item))
  items |> derive(net: discounted_total(.unit_price, .qty))
end

test "pure UDF runs inside derive"
  items = table
    | sku  | unit_price | qty |
    | "A1" | 10.00      | 10  |
    | "B2" | 10.00      | 2   |
  end
  out = price_items(items)
  assert out.sum(.net) == 110.00
end
```

---

## 7. Privacy, Sensitivity & Declassification

Dana tracks sensitivity tags statically in the type system (proved non-interferent in Lean 4
over Dana Core IR) and enforces runtime redaction everywhere.

### 7.1 Propagation Rules

1. **Direct column flow:** Any expression referencing a column tagged `[t]` produces a value
   tagged `[t]`. Selecting only public columns from a table with other tagged columns stays
   completely public (`row_tags = []`).
2. **Implicit row-existence flow (`row_tags`):** Filtering (`where`), deduplicating (`distinct`),
   grouping (`group_by`), or joining (`join_*`) on a column tagged `[t]` adds `[t]` to the
   table's `row_tags`. Consequently, `filtered.count()`, `filtered.empty?`, and downstream
   aggregates inherit `[t]` until safely declassified.
3. **Ordering flow (`order_tags`):** `sort_by`/`sort_desc` on a column tagged `[t]` adds `[t]`
   to `order_tags`, which flows into `limit`, `.first!`, and order-sensitive aggregates.
4. **Control-flow taint (`pc`):** Inside `if sensitive_cond ... end`, impure capability calls
   (printing, writing files/DBs, HTTPS) are forbidden unless the sink allows the condition's
   tags, and any returned/assigned values inherit the condition's tags.

### 7.2 Audited Built-In Declassifiers

There is no unguarded manual `declassify` escape hatch. Use Dana's audited declassifiers:

1. **`redact(.col)`** — Replaces every value in `.col` with `"[REDACTED]"` (`Text`) and clears
   `col_tags(.col)` to `[]`.
2. **`pseudonymize(.col, key: secret)`** — Replaces `.col` with a deterministic keyed
   HMAC-SHA256 hex token (`Text`), requiring a `Secret(...)` capability. Clears **`[pii]`**
   only (non-PII tags like `[health]` or `[counseling]` remain tracked). Identical keys produce
   identical tokens, so downstream joins on pseudonymized IDs still match 100%.
3. **`bucket(.col, cuts: [c1, c2, ...], labels: ["l0", "l1", "l2", ...])`**, **`coarsen(.col, allow: ["a", "b"], other: "Other")`** (`Text`/`Text?`), and **`.round_to(step, [mode:])`**
   (inside `derive`) — Coarsen sensitive values into intervals, an allowlisted category + fallback label,
   or step multiples (`bucketed = true`). All three stay tagged on individual rows and clear
   `[ferpa]` / group tags only once protected by `suppress_small_groups` or `suppress_small_cells`.
4. **`suppress_small_groups(min: k, distinct_by: .id)`** (optional `mode: :drop` [default] or
   `mode: :mask`):
   - Must immediately follow `summarize(...)`.
   - `min: k` must be a compile-time constant `>= 5` (and `>= policy.min_group_size`).
   - `distinct_by: .id` requires a matching `count_distinct(.id)` inside `summarize(...)` so
     one person with 5 rows cannot satisfy `k = 5`.
   - **Clears:** `row_tags`, `order_tags`, **blending** aggregates (`count`, `count_distinct`,
     `count_if`, `sum`, `mean`, `stddev`, `variance`), and **`bucketed`** group keys.
   - **Keeps tagged:** non-bucketed sensitive group keys AND **order statistics / extremes**
     (`min`, `max`, `median`, `percentile`, `first`, `last`) — preventing single-record outlier
     re-identification!
   - With `mode: :mask`, suppressed cells (and complementary suppression cells) become `none`
     and aggregate columns widen to `T?`.
5. **`suppress_small_cells(by: [.c1, ...], min: k, [distinct_by: .id])`** (row-level
   `k`-anonymity) & **`shuffle(seed: Int)`**:
   - Retains individual rows whose quasi-identifier equivalence class (`by:`) has `>= k` rows
     (or `>= k` distinct non-null `distinct_by` values), dropping rows from smaller classes;
     `min: k` must be a literal integer `>= 2` and `>= policy.min_group_size`.
   - Statically rejects with **`E0202`** if `[pii]` or `[secret]` remains tagged on any column
     (`.drop`, `.select`, `redact`, or `pseudonymize` direct identifiers first).
   - **Clears:** `row_tags` and `[ferpa]` on `by:` columns and coarsened (`bucket` / `.round_to`)
     columns; **keeps `[ferpa]`** on un-coarsened columns. Logs `K_ANON` in `dana explain`.
   - Pair with `|> shuffle(seed: Int)` to deterministically permute row order and clear
     `order_tags`.

<!-- dana-example: file -->
```dana
module PrivacyDeclassifyDemo

schema Encounter
  patient_id: Int [pii]
  department: Text
  age_years: Int [health]
  stay_days: Decimal [health]
end

fn safe_summary(encounters: Table(Encounter))
  promise all(.patients >= 10)

  encounters
    |> select(.patient_id, .department, .age_years, .stay_days)
    |> derive(
      age_band: bucket(.age_years, cuts: [18, 45, 65], labels: ["0-17", "18-44", "45-64", "65+"])
    )
    |> group_by(.department, .age_band)
    |> summarize(patients: count_distinct(.patient_id), avg_stay: mean(.stay_days))
    |> suppress_small_groups(min: 10, distinct_by: .patient_id)
    |> sort_desc(.patients)
end

fn main(db: ReadDB(Clinic), console: Console) : Int
  console.print_table(safe_summary(db.table(Encounter)))
  0
end
```

### 7.3 Capability Annotations & `dana.policy`

All output capabilities default to `allows: []` (public data only). Authorized sinks declare
explicit tag allowlists:

| Capability Type in Dana | Purpose & Privacy Rules |
| --- | --- |
| `Args` | CLI arguments (`args.first : Text?`, `args.list : List(Text)`) |
| `Console` / `Console(allows: [...])` | Terminal output (`print`, `error`, `print_table`, `print_chart`, `print_profile`) |
| `ReadFiles` | Read local files (`read_csv`, `read_jsonl`, `read_xlsx`, `read_parquet`) |
| `WriteFiles("prefix/", allows: [...])` | Confined directory writer (`0700` dirs / `0600` atomic temp+rename when `private: true` or non-empty `allows:`; sensitive tags require runtime `--allow-export=...`) |
| `ReadDB(DbName)` | Typed read-only DB access (`db.table(Schema)`) with automatic SQL pushdown |
| `WriteTable(DbName, "table_name", allows: [...])` | Typed DB upsert (`try w.upsert(tbl, key: .id)`) with column-by-column `schema.lock` tag verification |
| `RawReadDB(DbName)` | Capability-gated parameterized raw SQL (`try raw.raw_sql("...", params: [...], as: Schema)`) |
| `HttpsAllow("host", allows: [...])` | Exact-host HTTPS JSON client (no redirects to other hosts; sensitive egress requires `--allow-export=...`) |
| `LocalHttpAllow("host:port" \| Name, allows: [...])` | Capability-gated plaintext HTTP/1.1 client strictly confined to loopback hosts (`127.0.0.1:PORT`, `localhost:PORT`, `[::1]:PORT`) or CLI/env-bound service names (`--local-http Name=URL\|ready:FILE` / `DANA_LOCAL_HTTP_<NAME>`) |
| `LocalSocketAllow("/path.sock" \| Name, allows: [...])` | Capability-gated HTTP/1.1 client over a non-symlinked Unix domain socket (`"/path.sock"` or `--local-socket Name=PATH` / `DANA_LOCAL_SOCKET_<NAME>`) |
| `Secret("env_name")` | Key material from uppercase env var `ENV_NAME` (e.g. `FERPA_SALT=...` for `Secret("ferpa_salt")`; no CLI `--secret` flag; allowed in `pseudonymize`, `HttpsAllow`, `LocalHttpAllow`, and `LocalSocketAllow` `headers:`) |

**Optional `dana.policy` ceiling:** When `dana.policy` sits beside a `.dana` file (or is passed
via `--policy FILE`), Dana enforces it as a hard upper bound during both `dana check` and
`dana run`. Exact syntax:

```text
version 1

min_group_size 5
forbid manual_declassify
forbid repl_show_sensitive
forbid local_http
forbid local_socket

allow console tags []
allow export       "reports/"          tags []
allow export       "ir-exports/"       tags [counseling]
allow https        "api.populiweb.com" tags [pii]
allow local_http   "127.0.0.1:8091"    tags []
allow local_socket "/run/mo.sock"      tags []
allow write        Seminary.students   tags [pii, ferpa]
```

> **Note:** In Dana code, `WriteTable` takes two arguments: `WriteTable(Seminary, "students", allows: [pii, ferpa])`.
> In `dana.policy`, the matching rule uses dot syntax: `allow write Seminary.students tags [pii, ferpa]`.

### 7.4 Safe-by-Default Runtime Redaction

- On tagged schemas, `BadRow(S)` keeps `line: Int`, `column: Text`, and `error_kind: Text`
  public while tagging `raw_value: Text` and `raw_line: Text` with the schema's tags.
- Runtime errors, `dana dry-run` diffs, `table.profile()`, and `dana repl` automatically render
  unauthorized sensitive values as `[REDACTED:<sorted,tags>]`.
- Exporting sensitive data to `WriteFiles`, `HttpsAllow`, `LocalHttpAllow`, or `LocalSocketAllow`
  requires **both** compile-time `allows: [...]` (permitted by `dana.policy`) **and** runtime
  `--allow-export=tag1,tag2`.

---

## 8. Databases, Files, HTTPS & SQL Pushdown

### 8.1 File I/O Signatures (`ReadFiles` & `WriteFiles`)

**Quarantine readers** return `Result((Table(S), Table(BadRow(S))), Text)` — unwrap with `try`
and destructure the 2-tuple:

```text
(rows, bad) = try files.read_csv("data/in.csv", as: MySchema)          # .csv/.tsv, auto .gz/.zst
rows        = try files.read_csv("data/in.csv", as: MySchema, on_bad_rows: :error, coerce_integral_floats: true)
(rows, bad) = try files.read_jsonl("data/in.jsonl.gz", as: MySchema)   # auto .gz/.zst
(rows, bad) = try files.read_xlsx("data/book.xlsx", sheet: "Gifts", as: MySchema)
```

`read_csv` accepts `on_bad_rows: :quarantine` (default, returning `(rows, bad_rows)` and warning
when a non-`_` `bad_rows` binding is left uninspected) or `:error` (returning `Result(Table(S), Text)`
directly with privacy-redacted row diagnostics), plus `coerce_integral_floats: true|false` (default
`false`; `true` accepts integral tokens like `"1"` for `Float` columns).

**Direct Parquet reader** returns `Result(Table(S), Text)` (no quarantine tuple — binary typed
Parquet enforces schema types directly; supports `UNCOMPRESSED`, `SNAPPY`, `GZIP`, `ZSTD`,
`PLAIN`, and `RLE_DICTIONARY`):

```text
rows = try files.read_parquet("data/orders.parquet", as: Order)
```

**Confined writers** on `out: WriteFiles("reports/")` all return `Result(Unit, Text)` and write
under the capability's prefix (creating subdirectories automatically). Every `WriteFiles`
writer accepts optional `private: Bool` (default `false`); whenever `private: true` **or**
`WriteFiles` carries non-empty `allows:` tags, missing parent directories are created with mode
`0700` and payloads are flushed, synced, and atomically renamed from a `0600` temp file:

| Method | Payload | Notes |
| --- | --- | --- |
| `try out.write_csv("out.csv", tbl, private: false, sanitize_formulas: false)` | `Table` | `.tsv` uses tabs; `.gz`/`.zst` auto-compress; `sanitize_formulas: true` prefixes `'`, preserving negative decimals (also via `format_csv(tbl, sanitize_formulas: true)`) |
| `try out.write_jsonl("out.jsonl.zst", tbl, private: false)` | `Table` | Auto `.gz`/`.zst` compression |
| `try out.write_parquet("out.parquet", tbl, private: false)` | `Table` | Native Zstd-compressed Apache Parquet |
| `try out.write_xlsx("out.xlsx", sheets: {"S1": t1, "S2": t2}, private: false)` | `Map(Text, Table)` or `Table` | Single- or multi-sheet OOXML `.xlsx` |
| `try out.write_html("report.html", report, private: false)` | `Report` | Self-contained HTML5 with inline SVGs |
| `try out.write_markdown("report.md", report, private: false)` | `Report` | GitHub-flavored Markdown report |
| `try out.write_svg("chart.svg", chart, private: false)` | `Chart` | Standalone `<svg>` file |
| `try out.write_file("notes.txt", text, private: false)` | `Text` | Plain UTF-8 text (alias: `write_text`) |

### 8.2 Databases, `schema.lock` & SQL Pushdown

Bind databases at runtime with `--db Name=URI` (e.g., `--db Seminary=sqlite:///path/to/db.sqlite?attach=populi:/path/to/populi.db`
or `--db Seminary=postgres://user:pass@host:5432/db`) plus `--attach [DB:]schema=PATH` for SQLite
secondary databases, or env var `DANA_DB_<NAME>`.

- **Typed scan with automatic SQL pushdown:** `db.table(Schema)` (or schema-qualified
  `db.table(Schema, from: "populi.enrollments")` for PostgreSQL schemas, `--attach`ed SQLite
  databases, or multi-schema `WriteTable(Db, "schema.table")`) returns `Table(Schema)` directly
  (not a `Result`). Unattached SQLite databases also fall back from `"schema.table"` to literal
  `"schema.table"` then flattened `"schema_table"` in `main`. Eligible `where`, `select`, `drop`,
  `rename`, `derive` (including `bucket`, `coarsen`, `.lower`/`.upper`/`.slice`, `.in?`,
  `Int`/`Decimal` `.clamp`, exact proleptic Gregorian `.try_parse_date`, plus PostgreSQL
  `.try_parse_decimal` [`_dana_dec_*` `AS MATERIALIZED` CTE with 25-char Unicode `White_Space` trim
  and nested `CASE`] and calendar/DST primitives `Date.year`, `add_days`, `days_between`,
  `at_midnight_in_tz`), `join_*`, `distinct`, `dedupe_by` (`ROW_NUMBER()` on SQLite; `DISTINCT ON`
  on PostgreSQL when key/order uniquely identifies rows), `group_by`/`summarize` (including
  `count_if`), `sort_by`, and `limit` prefixes compile automatically into 100% parameterized SQL
  (`?` on SQLite, `$1..$n` on PostgreSQL) and stream 2,048-row batches into the columnar VM
  (`shuffle`, `pseudonymize`, and `suppress_small_cells` act as local VM boundaries). On PostgreSQL,
  Dana also tracks `known_not_null` to eliminate redundant `COALESCE` / simplify non-null join keys
  from `IS NOT DISTINCT FROM` to `=`, materializes `SELECT` CTEs evaluating `TryParseIsoDate`,
  `TryParseDecimal`, or `AtTimeZone` (`AS MATERIALIZED`) to prevent inline re-expansion across
  multi-million-row joins, and decodes PostgreSQL `TEXT[]`/`VARCHAR[]` array columns cleanly into
  `Text` literals. To get live runtime SQL pushdown inside a helper function, pass
  `db: ReadDB(MyDb)` and start the pipeline with `db.table(Schema) |> ...` (passing `db.table(Schema)`
  into a `Table(Schema)` parameter materializes the scan before the call). Inspect pushdown
  boundaries with `dana explain --dialect sqlite|postgres FILE`.
- **Offline `schema.lock` (covariant `ReadDB`, strict `WriteTable`):** Run `dana schema-sync --db Seminary=... [--attach [DB:]schema=PATH]... [--schemas s1,s2,...] --out schema.lock` to
  snapshot table schemas while preserving human-authored `[pii]`/`[ferpa]` annotations. `dana check`
  verifies every `db.table(Schema)` and `WriteTable.upsert(...)` offline against `schema.lock`:
  `ReadDB` checks column nullability covariantly (`T?` schema fields may read `NOT NULL` DB columns
  cleanly), whereas `WriteTable.upsert` remains strict.
- **Typed upsert & `dana dry-run`:** `stats = try db_write.upsert(rows, key: .student_id)`
  returns `Result(UpsertStats, Text)` with `stats.inserted`, `stats.updated`, `stats.unchanged`.
  Running under `dana dry-run` executes strictly read-only and prints redacted insert/update
  diffs without modifying disk or database state.
- **Parameterized raw SQL (`RawReadDB`):**

<!-- dana-example: file -->
```dana
module RawSqlDemo

schema ActiveCount
  program: Text
  n: Int
end

fn main(raw_db: RawReadDB(Seminary), console: Console) : Int
  rows = try raw_db.raw_sql(
    "SELECT program, COUNT(*) AS n FROM students WHERE cohort_year >= ? GROUP BY program",
    params: [2024],
    as: ActiveCount
  )
  console.print_table(rows)
  0
end
```

The first argument to `raw_sql` **must** be a compile-time constant string literal (string
interpolation `#{...}` is a compile error); pass dynamic values strictly via `params: [...]`.

### 8.3 Capability-Gated HTTPS JSON Client (`HttpsAllow`)

<!-- dana-example: file -->
```dana
module ApiFetchDemo

schema ApiUser
  id: Int [pii]
  email: Text [pii] where .contains?("@")
end

fn fetch_page(
  api: HttpsAllow("api.example.com", allows: [pii]),
  token: Secret("api_token"),
  page: Int
) : Result((Table(ApiUser), Table(BadRow(ApiUser)), Bool), Text)
  resp = try api.get_json(
    "https://api.example.com/v1/users?page=#{page}",
    headers: {"Authorization": "Bearer #{token}"}
  )
  (rows, bad) = resp.parse_table("items", as: ApiUser)
  has_more = resp.bool_at("has_more")
  Ok((rows, bad, has_more))
end
```

`JsonResponse` helpers and `HttpsAllow` write methods:

- `resp.parse_table("items", as: Schema, [fields: {"col": "nested.path.0"}]) : (Table(Schema), Table(BadRow(Schema)))`
  (direct tuple, not `Result`; optional `fields:` maps schema columns to dotted object paths and
  0-based JSON array indices — e.g. `"lon": "geometry.coordinates.0"`). Pass `""` as the
  container key when the JSON root itself is an array (`[...]`).
- `resp.bool_at("field") : Bool`, `resp.text_at("field") : Text`, `resp.int_at("field") : Int`.
- `api.post_json(url, body, [headers: {...}])` and `api.put_json(url, body, [headers: {...}])`
  return `Result(JsonResponse, Text)`. `body` may be `Text` (sent verbatim with
  `Content-Type: application/json`), `Table(...)` (serialized as a compact JSON array `[...]`), or
  any typed JSON-encodable value (`struct`, table row from `for row in tbl`, `Map(Text, ...)`,
  `List`, `Option`, or scalar — encoded automatically via `Json.encode(...)` with `Decimal`
  represented as an exact JSON string). Empty `2xx` / `204 No Content` responses succeed with a null
  JSON body. Use `Json.encode(value) : Text` directly whenever explicit JSON serialization (with
  privacy-tag propagation) is needed. Sensitive bodies or headers require **both** compile-time
  `allows: [...]` and runtime `--allow-export`. Running under `dana dry-run` intercepts writes
  cleanly and prints `[DRY-RUN] would POST/PUT ...` with headers/sensitive payloads redacted.

<!-- dana-example: file -->
```dana
module HttpsPostAndNestedDemo

schema Quake
  id: Text
  place: Text
  lon: Float
end

fn sync_quakes(api: HttpsAllow("api.example.com")) : Result(Int, Text)
  resp = try api.get_json("https://api.example.com/quakes")
  (rows, _bad) = resp.parse_table(
    "features",
    as: Quake,
    fields: {"place": "properties.place", "lon": "geometry.coordinates.0"}
  )
  _ack = try api.post_json("https://api.example.com/ingest", rows)
  Ok(rows.count())
end

test "nested fields mapping and table post_json work with Https.fake"
  payload = """{"features": [{"id": "q1", "properties": {"place": "OR"}, "geometry": {"coordinates": [-122.7, 45.5]}}]}"""
  api = Https.fake(
    "api.example.com",
    responses: {"https://api.example.com/quakes": payload, "https://api.example.com/ingest": "{}"}
  )
  assert (try sync_quakes(api)) == 1
  assert api.requests.size == 2
  assert api.request_bodies.first!.contains?("\"place\":\"OR\"")
end
```

### 8.4 Capability-Gated Local HTTP (`LocalHttpAllow`) & Unix Domain Sockets (`LocalSocketAllow`)

`LocalHttpAllow` and `LocalSocketAllow` enable strict plaintext HTTP/1.1 integration with local
co-resident services (for example `mo serve` or local Unix admin sockets) **without** weakening
`HttpsAllow` TLS enforcement:

- **Pinned vs. named endpoints:**
  - `LocalHttpAllow("127.0.0.1:8091", [allows: [...]])` pins an explicit loopback authority
    (`127.0.0.0/8`, `localhost`, or `[::1]`) **with an explicit non-zero `:port`** (wildcard
    portless loopback authorities, non-loopback IPs, hostnames, schemes, userinfo, and paths are
    rejected at compile time).
  - `LocalHttpAllow(MoShop, [allows: [...]])` binds dynamically at runtime via
    `--local-http MoShop=http://127.0.0.1:8091` or `--local-http MoShop=ready:/path/ready.json`
    (reads `{"url": ...}` or `{"port": ...}` such as `mo serve --ready-file`) or env var
    `DANA_LOCAL_HTTP_MOSHOP`.
  - `LocalSocketAllow("/run/mo.sock", [allows: [...]])` or `LocalSocketAllow(MoAdmin)` binds via
    `--local-socket MoAdmin=/run/mo.sock` or `DANA_LOCAL_SOCKET_MOADMIN`. Paths with `..` or URL
    schemes are rejected at compile time; live connects canonicalize parent directories and reject
    symlinks or non-socket files via `lstat`.
- **Methods & URL rules:** Both capabilities provide `.get_json(target, [headers: {...}])`,
  `.post_json(target, body, [headers: {...}])`, `.put_json(target, body, [headers: {...}])`, and
  `.delete_json(target, [headers: {...}])` returning `Result(JsonResponse, Text)`.
  `LocalHttpAllow` accepts relative `/path[?query]` or exact `http://<same-authority>/path` URLs
  and forbids `https://`; `LocalSocketAllow` requires relative `/path[?query]`.
- **Security & `dry-run` invariants:**
  - `HttpsAllow` continues to reject `http://` URLs unconditionally.
  - `LocalHttpAllow` verifies every post-DNS `SocketAddr::ip().is_loopback()` before TCP connect,
    forbids `Host`/`Content-Length`/`Transfer-Encoding` overrides and CR/LF/NUL headers, and never
    follows 3xx redirects.
  - Sensitive data requires both compile-time `allows: [...]` (within `dana.policy`) and runtime
    `--allow-export=...`. `Secret("name")` headers remain permitted for bearer auth.
  - Under `dana dry-run`, `GET` executes read-only while `POST`/`PUT`/`DELETE` are suppressed cleanly
    and print `[DRY-RUN] would POST/PUT/DELETE ... (headers: [...])` with header values and
    sensitive bodies redacted.

<!-- dana-example: file -->
```dana
module LocalHttpAndSocketDemo

struct ProductIn
  sku: Text
  title: Text
  category: Text
  price: Decimal
  stock: Int
end

schema ProductOut
  sku: Text
  stock: Int
end

fn sync_local_mo(
  mo: LocalHttpAllow(MoShop),
  admin: LocalSocketAllow(MoAdmin),
  token: Secret("shop_token")
) : Result(Int, Text)
  _ = try mo.get_json("/health")
  auth = {"Authorization": "Bearer #{token}"}
  item = ProductIn(sku: "blend-1", title: "House \"Roast\"", category: "beans", price: 16.50, stock: 12)
  _ = try mo.post_json("/products", body: item, headers: auth)
  _ = try admin.post_json("/admin/verify", body: {"check": true})
  resp = try mo.get_json("/products", headers: auth)
  (rows, _bad) = resp.parse_table("", as: ProductOut)
  Ok(rows.count())
end

test "LocalHttp.fake and LocalSocket.fake run offline cleanly"
  mo = LocalHttp.fake(
    MoShop,
    responses: {
      "GET /health": "{\"status\":\"ok\"}",
      "POST /products": "{\"ok\":true}",
      "GET /products": "[{\"sku\":\"blend-1\",\"stock\":12}]"
    }
  )
  admin = LocalSocket.fake(MoAdmin, responses: {"POST /admin/verify": "{\"ok\":true}"})
  assert (try sync_local_mo(mo, admin, Secret.fake("dev"))) == 1
  assert mo.requests.size == 3
  assert mo.request_bodies.first!.contains?("\"price\":\"16.5\"")
  assert admin.requests.size == 1
end
```

---

## 9. Statistics, Charts & Reports

Import `use Stats` at the top of the module to access statistical primitives. All statistical
functions and charts propagate sensitivity tags from referenced columns and `row_tags`.

### 9.1 Profiling & `Stats` Functions

| Call | Return Type & Fields / Behavior |
| --- | --- |
| `tbl.profile()` | `Profile` — Per-column type, null %, min/mean/p50/max + 8-bin Unicode sparklines (tagged cols auto-redact). Print via `console.print_profile(tbl.profile())`. |
| `Stats.corr(tbl, x: .a, y: .b, method: :pearson \| :spearman)` | `Float` — Default `:pearson`; `:spearman` uses exact tied-rank averaging. |
| `Stats.linear_regression(tbl, x: .a, y: .b)` | `LinearModel` — `.slope : Float`, `.intercept : Float`, `.r_squared : Float`, and `model.predict(x) : Float` (accepts `Int`/`Float`/`Decimal`, works as scalar or inside `derive(y_hat: model.predict(.x))`). |
| `Stats.t_test(tbl_a, tbl_b, column: .c)` | `StatTest` — Two-sample Welch t-test: `.t_stat : Float`, `.p_value : Float`, `.df : Float`. |
| `Stats.chi_square(tbl, x: .a, y: .b)` | `StatTest` — Contingency independence test: `.stat` (or `.chi2`), `.p_value`, `.df`. |
| `Stats.chi_square(tbl, observed: .o, expected: .e)` | `StatTest` — Goodness-of-fit test: `.stat` (or `.chi2`), `.p_value`, `.df`. |
| `Stats.outliers(tbl, column: .c, method: :zscore \| :iqr, threshold: 2.0, flag: "outlier?")` | `Table(...)` — Appends a `Bool` flag column (defaults: `method: :zscore`, `threshold: 3.0` for `:zscore` / `1.5` for `:iqr`, `flag: "outlier?"`). |

### 9.2 Charts & Reports

All five chart verbs are piped from a `Table(...)`, support dynamic interpolated `title:`
strings, render in the terminal via `console.print_chart(c)`, save standalone SVG via
`try out.write_svg("c.svg", c)`, and embed directly inside `Report`:

| Chart Verb | Arguments |
| --- | --- |
| `chart_bar` | `x: .cat, y: .val` (optional `color: .grp, title: "..."`) |
| `chart_line` | `x: .t, y: .val` (optional `color: .grp, title: "..."`) |
| `chart_scatter` | `x: .a, y: .b` (optional `color: .grp, trendline: model, title: "..."`) |
| `chart_histogram` | `x: .val` (or `column: .val`, optional `bins: 20, title: "..."`) |
| `chart_heatmap` | `x: .c1, y: .c2, value: .v` (optional `title: "..."`) |

Build self-contained HTML5 or Markdown reports with `Report.new("Title")`:

<!-- dana-example: file -->
```dana
module StatsChartReportDemo
use Stats

schema Reading
  group: Text
  hours: Float
  score: Float
end

fn main(files: ReadFiles, out: WriteFiles("reports/"), console: Console) : Int
  rows = try files.read_parquet("data/readings.parquet", as: Reading)
  console.print_profile(rows.profile())

  r = Stats.corr(rows, x: .hours, y: .score, method: :pearson)
  rho = Stats.corr(rows, x: .hours, y: .score, method: :spearman)
  model = Stats.linear_regression(rows, x: .hours, y: .score)
  scored = rows |> derive(predicted: model.predict(.hours))
  flagged = Stats.outliers(scored, column: .score, method: :iqr, threshold: 1.5)

  a = rows |> where(.group == "A")
  b = rows |> where(.group == "B")
  ab = Stats.t_test(a, b, column: .score)

  scatter = rows
    |> chart_scatter(
      x: .hours,
      y: .score,
      color: .group,
      trendline: model,
      title: "Hours vs. Score (r = #{r.round(3)}, rho = #{rho.round(3)})"
    )
  hist = rows |> chart_histogram(x: .score, bins: 12, title: "Score Distribution")

  console.print_chart(hist)

  report = Report.new("Study Summary")
    |> add_summary(
      "Slope=#{model.slope.round(4)}, R^2=#{model.r_squared.round(3)}, Welch p=#{ab.p_value.round(4)}"
    )
    |> add_chart(scatter)
    |> add_chart(hist)
    |> add_table(flagged |> where(.outlier?))

  try out.write_html("study.html", report)
  try out.write_markdown("study.md", report)
  try out.write_svg("scatter.svg", scatter)
  0
end
```

---

## 10. Tests, Intent & Fake Capabilities

Functions may embed executable `examples ... end` (bare boolean expressions, no `assert`
keyword) and runtime-checked `promise ...` postconditions (`promise unique(.a, .b)`,
`promise all(row_pred)`, `promise sum(.x) == input.sum(.y)`, `promise . >= 0.00`). Top-level
`test "description" ... end` blocks use `assert cond`.

**In-memory test fakes** are strictly scoped to `test` and `examples` blocks (using them in
production code is a compile error):

| Fake Constructor | Returns | Inspection Helpers |
| --- | --- | --- |
| `Files.in_memory({"a.csv": "..."}).read_only` | `ReadFiles` | Serves in-memory CSV/TSV/JSONL fixtures |
| `DB.in_memory(DbName, {Schema1: tbl1, ...})` | `ReadDB(DbName)` | Serves typed in-memory tables |
| `Console.fake()` | `Console` | `.printed_lines : List(Text)`, `.printed_errors : List(Text)`, `.printed_tables : List(Table)` |
| `Https.fake("host", responses: {"https://host/...": "{...}"}, allows: [pii])` | `HttpsAllow` | Stubbed JSON responses (`allows:` optional); `.requests : List(Text)` & `.request_bodies : List(Text)` |
| `LocalHttp.fake(Name \| "127.0.0.1:8091", responses: {"GET /p": "{...}"}, allows: [pii])` | `LocalHttpAllow` | Stubbed local HTTP JSON (`allows:` optional); `.requests : List(Text)` & `.request_bodies : List(Text)` |
| `LocalSocket.fake(Name \| "/run/mo.sock", responses: {"POST /p": "{...}"}, allows: [pii])` | `LocalSocketAllow` | Stubbed local UDS JSON (`allows:` optional); `.requests : List(Text)` & `.request_bodies : List(Text)` |
| `Secret.fake("test-key")` | `Secret` | Deterministic test secret for `pseudonymize` / HTTPS |
| `Args.of(["a.csv", "b.csv"])` | `Args` | Supplies CLI args to `main(...)` in tests |

`Console.fake()` inspection fields are `List(...)` values (`console.printed_lines : List(Text)`
captures stdout from `print`, `print_table`, `print_chart`, and `print_profile`;
`console.printed_errors : List(Text)` captures `error`; `console.printed_tables : List(Table)`
captures tables passed to `print_table`). Use `List` properties `.size` (or `.len`), `.empty?`,
`.first`, and `.first!` — **not** `.count()` (`.count()` is a `Table` method).

<!-- dana-example: file -->
```dana
module FakeCapsDemo

schema Row
  k: Text
  v: Int
end

fn main(args: Args, files: ReadFiles, console: Console) : Int
  path = args.first.or_return(2)
  (rows, bad) = try files.read_csv(path, as: Row)
  console.print("total=#{rows.sum(.v)}, bad=#{bad.count()}")
  if bad.empty?: 0 else: 1
end

test "in-memory files, args, and fake console test main end-to-end"
  csv = """
    k,v
    a,10
    b,oops
    c,5
  """
  files = Files.in_memory({"in.csv": csv}).read_only
  console = Console.fake()

  assert main(Args.of(["in.csv"]), files, console) == 1
  assert console.printed_lines.first! == "total=15, bad=1"
end
```

---

## 11. Modules, Vendoring, REPL & CLI

### 11.1 Hash-Pinned `vendor/` Modules (Pure by Default)

Dana has **no central package registry**. Shared third-party `.dana` files live under `vendor/`
and are pinned by exact SHA-256 hash in `vendor/vendor.lock`:

```sh
dana vendor pin               # scans vendor/**/*.dana and writes vendor/vendor.lock
dana vendor verify            # verifies every vendored file offline (rejects tampering/unpinned/symlinks)
```

Every `use` resolved from `vendor/` is automatically hash-verified by the compiler against
`vendor/vendor.lock`, and vendored modules are **pure by default** (cannot mint ambient I/O).
`dana vendor pin` warns on stderr if a vendored file path does not match the kebab-case relative
path expected by `use ModuleName`.

### 11.2 Safe Interactive REPL (`dana repl`)

`dana repl` runs the real compiler and 2,048-row vectorized VM in a **read-only, privacy-redacted**
interactive session:

- **Pre-bound read-only capabilities:** `files: ReadFiles`, `console: Console`, and every
  `--db Name=URI` as `Name: ReadDB(Name)`. Write, export, secret, and raw-SQL capabilities are
  never exposed in the REPL.
- **Privacy-redacted by default:** Tagged columns, `row_tags`-tainted tables, scalars, profiles,
  and charts automatically display `[REDACTED:<tags>]`. Pass `--show-sensitive tag1,tag2` to
  view specific tags locally; if `dana.policy` sets `forbid repl_show_sensitive`, startup
  hard-fails with `E0202`.
- **Flags:** `--eval EXPR` (one-liner), `--db Name=URI`, `--policy FILE`, `--schema-lock FILE`,
  `--show-sensitive TAGS`.
- **Zero-boilerplate `--schema-lock` tables:** When `--schema-lock` is active (or a sibling
  `schema.lock` is auto-discovered), locked tables are pre-declared as `CapCase` schemas (e.g.
  `Db.table(GhRepos)`) and also support direct string shorthand `Db.table("gh_repos")` without
  typing `schema ... end` first — preserving all locked `[pii]`/`[ferpa]` tags and full SQL
  pushdown (`:explain` and `--eval`). User-defined `schema` declarations override auto-generated ones.
- **REPL-only `untyped` data explorer** (for inspecting files before writing a `schema`):
  `untyped.read_csv("path.csv")`, `untyped.read_jsonl("path.jsonl")`,
  `untyped.read_parquet("path.parquet")`, `untyped.read_xlsx("path.xlsx", sheet: "Sheet1")`.
- **All 8 `:meta` commands:**
  - `:help` (`:h`) — Show REPL help and active privacy display mode
  - `:type <expr>` — Print inferred Dana type and sensitivity tags
  - `:profile <expr>` — Print privacy-redacted dataset profile
  - `:explain <expr>` — Show optimized plan, SQL pushdown, and sensitivity provenance
  - `:infer-schema <var|path>` — Emit ready-to-paste `schema ... end` declaration
  - `:vars` — List capabilities, locked `schema.lock` tables, session definitions, and bound variables
  - `:reset` — Clear all session declarations and variables
  - `:quit` (`:q`, `:exit`) — Exit the REPL

### 11.3 CLI Reference

Every `dana <subcommand>` accepts `-h` or `--help` to print its usage summary.

```sh
dana check [--db Name=URI]... [--attach [DB:]schema=PATH]... [--schema-lock FILE] [--policy FILE] [--json] <FILE...>
dana run [--oracle] [--oracle-steps N] [--db Name=URI]... [--attach [DB:]schema=PATH]... [--local-http Name=URL|ready:FILE]... [--local-socket Name=PATH]... [--schema-lock FILE] [--policy FILE] [--allow-export TAGS] [--emit-core] <FILE> [-- ARGS...]
dana dry-run [--oracle] [--oracle-steps N] [--db Name=URI]... [--attach [DB:]schema=PATH]... [--local-http Name=URL|ready:FILE]... [--local-socket Name=PATH]... [--schema-lock FILE] [--policy FILE] [--allow-export TAGS] <FILE> [-- ARGS...]
dana test [--oracle] [--oracle-steps N] [--policy FILE] [--filter SUBSTR] [PATH...]
dana explain [--dialect sqlite|postgres] [--schema-lock FILE] [--policy FILE] <FILE>
dana schema-sync --db Name=URI [--db Name2=URI2 ...] [--attach [DB:]schema=PATH]... [--schemas s1,s2,...] [--out schema.lock]
dana repl [--policy FILE] [--db Name=URI]... [--attach [DB:]schema=PATH]... [--schema-lock FILE] [--show-sensitive TAGS] [--eval EXPR]
dana vendor pin|verify [--dir PATH]
dana format [--check] <PATH...>
dana infer-schema <DATA_FILE> [--name Schema] [--sample-rows N] [--format csv|tsv|jsonl|parquet|xlsx]
dana fake <FILE.dana> [--schema Name] [--rows N] [--seed S] [--format csv|tsv|jsonl] [--out PATH]
dana guide [SECTION]
dana --version | -V
```

---

## 12. Common Pitfalls & Quick Idioms for Authors and AI Agents

1. **Quarantine tuple vs. direct Parquet:** `read_csv`, `read_jsonl`, and `read_xlsx` return
   `Result((Table(S), Table(BadRow(S))), Text)` -> `(rows, bad) = try files.read_csv(...)`.
   `read_parquet` returns `Result(Table(S), Text)` -> `rows = try files.read_parquet(...)`
   (no `bad_rows` tuple!).
2. **Optional aggregates (`??` required):** `table.mean(.c)`, `table.stddev(.c)`, and
   `summarize` `mean`/`median`/`stddev`/`variance`/`percentile`/`min`/`max` plus `lag`/`lead`/
   `rolling_mean` all return `Option(T)` (`T?`). Coalesce with `?? 0.0` (for `Float?`) or
   `?? 0.00` (for `Decimal?`). By contrast, `count()`, `count_distinct(.c)`, and `sum(.c)` are
   non-optional.
3. **`Decimal` vs. `Float` conversions:** Never mix non-literal `Int`, `Decimal`, and `Float`
   in `+ - * /`. Use `.to_decimal` (on `Int`) or `.to_float` (on `Int` or `Decimal`). Bare
   `10.50` is `Decimal`; scientific `1e-4` is `Float`. Watch out for unannotated local bindings
   like `x = if flag: 2.5 else: 0.5` (inferred as `Decimal`!): annotate `var x: Float = ...`,
   use scientific notation (`2.5e0`), or convert with `x.to_float` before combining with `Float`.
4. **`WriteTable` vs. `dana.policy` syntax:** In Dana function signatures write
   `WriteTable(Seminary, "students", allows: [pii, ferpa])` (two arguments). In `dana.policy`
   write `allow write Seminary.students tags [pii, ferpa]` (dot syntax).
5. **FERPA/HIPAA `suppress_small_groups` & `suppress_small_cells` rules:**
   - `suppress_small_groups` must immediately follow `summarize(...)` (`distinct_by: .student_id`
     requires `count_distinct(.student_id)` inside `summarize(...)`; `min:` >= 5 and
     `>= dana.policy`'s `min_group_size`). Only **blending** aggregates (`count`, `count_distinct`,
     `count_if`, `sum`, `mean`, `stddev`, `variance`) and **`bucket`**-ed group keys clear
     tags; `min`, `max`, `median`, and `percentile` remain tagged!
   - `suppress_small_cells(by: [...], min: k, [distinct_by: .id])` preserves individual rows
     (`min:` >= 2 and `>= dana.policy`'s `min_group_size`), rejects any remaining
     `[pii]`/`[secret]` column with `E0202`, clears `[ferpa]` only on `by:` columns and
     coarsened (`bucket` / `.round_to`) columns, and pairs cleanly with `shuffle(seed:)`,
     `private: true`, and `sanitize_formulas: true`.
6. **Implicit `row_tags` on `.count()`:** Filtering (`where`) on a tagged column taints
   `row_tags`, so `filtered.count()` carries that tag and cannot print to plain public
   `Console`. Select public columns only, aggregate + `suppress_small_groups`, or use an
   authorized sink (`WriteFiles(..., allows: [...])` / `Console(allows: [...])`).
7. **Join key & collision rules:** Use `on: .id` when column names match, and
   `on: left.a == right.b` (never `on: .a == .b`) when they differ. Overlapping non-key columns
   require `select`/`drop` first or `suffixes: ("_left", "_right")`.
8. **Mutable bindings need `var`:** Plain `x = 1` is immutable. Write `var x = 1` before
   reassigning `x = x + 1` in `for`/`while` loops.
9. **Inline `if` vs. block `if`:** Inline `if c: a else: b` uses colons and has NO `end` (use
   this inside `derive`/`where` expressions). Block `if c \n ... \n end` has no colons and
   requires `end`.
10. **Constant SQL in `raw_sql`:** `raw_db.raw_sql("SELECT ... WHERE id = ?", params: [id], as: S)`
    rejects string interpolation (`#{...}`); always pass parameters in `params: [...]`.
11. **`use Stats` & `Console.print`:** Declare `use Stats` before calling `Stats.corr`,
    `Stats.linear_regression`, `Stats.t_test`, `Stats.chi_square`, or `Stats.outliers`.
    `console.print(...)` takes `Text` (interpolate scalars with `"#{x}"`); use
    `console.print_table(t)`, `console.print_chart(c)`, and `console.print_profile(p)` for
    structured values.
12. **Sibling `dana.policy` auto-discovery:** `dana check` and `dana run` automatically load a
    `dana.policy` in the same directory as the `.dana` file unless overridden with `--policy`.
13. **`Table` methods/properties vs. `|>` pipeline verbs:** `.count()`, `.empty?`, `.first!`,
    `.profile()`, `.sum(.col)`, `.mean(.col)`, and `.stddev(.col)` are `Table` methods/properties,
    not `|>` pipeline verbs — call `tbl.count()` (or bind the pipeline first, e.g.,
    `hot = tbl |> where(.outlier?)` then `hot.count()`), not `tbl |> count()`. On `List` values
    (such as `console.printed_tables`), use `.size`, `.empty?`, `.first`, or `.first!` — not `.count()`.
14. **`pseudonymize` and `redact` are `|>` table pipeline verbs (not row functions):** Pipe them
    directly (`tbl |> pseudonymize(.col, key: secret) |> redact(.notes)`) instead of calling them
    inside `derive(...)`. Only `bucket(.col, cuts: [...], labels: [...])` is called inside `derive(...)`.
15. **Row-level `k`-anonymity from `ReadDB` with `[pii]` join keys:** `suppress_small_cells`
    rejects tables carrying `[pii]` in columns OR `row_tags` (`where`/`group_by`/`join_*` on a
    `[pii]` column adds `[pii]` to `row_tags`). Push non-PII `where(...)` filters down to SQL first,
    then run `|> pseudonymize(.id, key: secret)` *before* filtering/joining/grouping on `.id` (compute
    sentinel tokens for `none` / `""` via `pseudonymize` so null/blank filtering compares public tokens).

---

## 13. Grammar Authority

The complete context-free grammar is specified and verified for **zero LR(1) conflicts**
(`%define lr.type ielr`, `%expect 0`, no operator precedence declarations) in `grammar/dana.y`.
Run `make grammar` to validate all `examples/*.dana`, every fenced `dana` block in this
reference and `README.md`, and the positive/negative grammar test suites.
