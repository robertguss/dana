# Dana Language Reference, v0.1

**Version 0.1 (Phase 0 approved draft).** This is the complete language reference for core
Dana, written to be read in full by people and by AI agents (embedded into the `dana guide`
command once the toolchain is built).

Every rule has an example, and every code example in this document parses with Dana's
executable IELR(1) grammar (`grammar/` in this repository) with zero grammar conflicts.
"An error" below means the compiler rejects the program. "Stops" means a running program
hits a runtime bug and halts with a redacted report.

---

## 1. A First Program

<!-- dana-example: file -->
```dana
## Totals a CSV file of expenses by category, largest first.
module Expenses

schema Expense
  date: Date
  category: Text where not .empty?
  amount: Decimal
end

fn main(args: Args, files: ReadFiles, console: Console) : Int
  path = args.first.or_return(2)
  (expenses, bad_rows) = try files.read_csv(path, as: Expense)

  totals = expenses
    |> group_by(.category)
    |> summarize(total: sum(.amount))
    |> sort_desc(.total)

  console.print_table(totals)
  if bad_rows.empty?: 0 else: 1
end
```

- Every file is one module, named on its first line of code (`module Name`). `##` doc
  comments may appear before it.
- `main` declares every capability the program needs (`Args`, `ReadFiles`, `Console`). A
  program has no ambient authority: it cannot write files, query a database, read secrets,
  or make HTTPS requests unless handed those capabilities.
- Blocks open with a keyword (`module`, `schema`, `struct`, `enum`, `fn`, `if`, `case`,
  `for`, `while`, `table`, `examples`, `test`) and close with `end`. Indentation has no
  semantic meaning; `dana format` formats code with two spaces per level.
- Because `Expense` declares no sensitivity tags, Dana's privacy system stays invisible
  (**zero friction on public data**).

---

## 2. Source Text

### 2.1 Files & Module Names

A program is a tree of `.dana` modules under a root folder. The module `Seminary.Enrollment`
lives in `seminary/enrollment.dana`: each CapCase segment maps to a lowercase hyphenated
folder or file name.

Source files are UTF-8. Invisible formatting characters—direction overrides, zero-width
characters, and control characters other than tab, CR, and LF—are a lexing error anywhere
in source, including comments and strings. Write them as Unicode escapes (`"\u{200B}"`).

### 2.2 Comments

`#` begins a line comment through the end of the line. `##` documents the declaration
immediately below it, or the module when placed before `module`.

### 2.3 Names & Keywords

- Values, variables, functions, columns, and parameters use `snake_case`: ASCII lowercase
  letters, digits, and `_`, starting with a letter or `_`.
- A name ending in `?` denotes a boolean value or predicate (`empty?`, `active?`,
  `some?`, `none?`).
- A name ending in `!` denotes a stopping unwrap or assertion helper (`first!`).
- Types, schemas, structs, enum constructors, and modules use `CapCase` (`Student`,
  `CourseEnrollment`, `Ok`, `Error`).
- `_` alone discards a value; names starting with `_` mark intentionally unused bindings.
- Atoms (symbolic option labels) start with `:` followed immediately by a `snake_case` name
  (`:month`, `:pearson`, `:mask`).

Reserved keywords:

```text
and assert break case const continue else end enum examples expose false fn
for if in is module none not or promise return schema stop struct table
test true try use var while
```

`where` and `tag` are contextual: `where` introduces column constraints in `schema`
declarations and serves as the table-filtering pipeline verb `where(...)`; `tag` declares
custom sensitivity tags at module level (`tag donor`) and remains usable as a column or
variable name (`.tag`, `derive(tag: ...)`). `table` is allowed as a member name after `.`
(as in `db.table(Student)`), and capitalized column names such as `.M0` or `.Q1` are
allowed after `.`. Words such as `as`, `on`, `left`, `right`, `allows`, `over`, `order`,
`cuts`, `labels`, `columns`, `fill`, `key`, `sheet`, and `sheets` are ordinary identifiers.

### 2.4 Lines & Continuations

A newline ends a statement; Dana has no semicolons. Newlines are ignored:

- inside parentheses `(...)`, brackets `[...]`, and braces `{...}`;
- after an opening delimiter, comma `,`, `.`, `=`, `|>`, or any binary operator;
- immediately before a closing delimiter, `.`, `|>`, or any binary operator other than
  unary `-` (and an inline `if cond: a` may continue onto `else` on the next line).

<!-- dana-example: fragment -->
```dana
summary = students
  |> where(.active? and
       .enrolled_year >= 2025)
  |> group_by(.program)
  |> summarize(headcount: count())
```

---

## 3. Values, Literals & Types

### 3.1 Built-In Scalar & Time Types

| Type | Literals / Examples | Semantics |
| --- | --- | --- |
| `Bool` | `true`, `false` | Logical truth values |
| `Int` | `0`, `42`, `-7` | Checked 64-bit signed integer; overflow stops |
| `Decimal` | `12.50`, `0.00` | Exact fixed-point (`10⁻¹⁸` scale, `±(2¹²⁷ − 1)`) for money & exact metrics |
| `Float` | `0.95`, `1.5e-4` | IEEE-754 binary64 for statistical/scientific math |
| `Text` | `"hello"`, `"""..."""` | UTF-8 text; supports `#{expr}` interpolation |
| `Bytes` | `b"..."` (via encoding) | Raw byte sequences |
| `Date` | `2026-10-01` | Proleptic Gregorian calendar date (`YYYY-MM-DD`) |
| `Timestamp` | `2026-10-01T14:30:00Z` | UTC instant with explicit IANA timezone conversions |
| `Duration` | `5.minutes`, `30.days` | Exact signed elapsed time (microseconds) |
| `Unit` | `Unit` | Empty return value |

### 3.2 Missing Values (`T?`) & Errors (`Result`)

Dana has **one** unified missing-value representation across SQL `NULL`, empty CSV cells,
JSON `null`, Parquet nulls, and Excel blanks: `Option(T)`, written shorthand as `T?`
(`Decimal?`, `Text?`, `Float?`), with literal `none`.

- Coalesce missing values with `??` (`mean(.gpa) ?? 0.00`).
- Test presence with `.some?` and `.none?`.
- Recoverable I/O and parsing failures return `Result(T, E)` (`Ok(v)` / `Error(e)`),
  propagated cleanly with `try expr`.

<!-- dana-example: fragment -->
```dana
clean = rows
  |> where(.avg_weekly_hours.some?)
  |> derive(hours: .avg_weekly_hours ?? 0.0)
```

### 3.3 Collections, Tuples, Structs & Enums

- Tuples: `(A, B)`, destructured as `(valid, bad_rows) = ...`.
- Lists: `[1, 2, 3]`, type `List(T)`.
- Insertion-ordered maps: `{"Authorization": "Bearer #{token}"}` or `{requests: 0}`, type
  `Map(K, V)`.
- Named records (`struct`) and tagged unions (`enum`):

<!-- dana-example: fragment -->
```dana
struct MetricSummary
  matched_count: Int
  matched_total: Decimal
end

enum ParseError
  BadDecimal
  MissingRequired
  ConstraintFailed
end
```

---

## 4. Schemas, Constraints & Sensitivity Tags

Named `schema` declarations sit at **data boundaries** (files, database tables, public
functions). Inside pipelines, Dana infers structural table types automatically so you never
write throwaway intermediate structs.

- Column constraints use `where` with `.` referring to the column's value (or `.pred?` for
  a method predicate).
- Built-in sensitivity tags: `pii`, `ferpa`, `financial`, `health`, `secret`.
- Custom sensitivity tags are declared at module level with `tag name`.
- Tags may be attached to columns (`email: Text [pii]`) or to the whole schema when row
  presence itself is sensitive (`schema CounselingVisit [counseling]`).

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
2. Logical OR: `or`
3. Logical AND: `and`
4. Logical NOT: `not` (prefix)
5. Comparisons & type test: `==`, `!=`, `<`, `<=`, `>`, `>=`, `is` (non-associative)
6. Missing-value coalesce: `??` (right-associative)
7. Additive: `+`, `-`
8. Multiplicative: `*`, `/`, `%`
9. Unary prefix: `-`, `try`
10. Postfix: `.member`, `.method(args)`, `(args)`, `[index]`

### 5.2 Control Flow

Dana supports both **inline `if` expressions** (with `:`) and **block `if` statements**
(closed by `end`), exhaustive `case ... end`, `for ... in ... end`, `while ... end`, and
early exits (`return`, `break`, `continue`) with optional trailing `if cond`.

<!-- dana-example: fragment -->
```dana
label = if score >= 90: "A"
  else if score >= 80: "B"
  else: "C"

if not bad_rows.empty?
  for bad in bad_rows
    console.error("line #{bad.line}: #{bad.error_kind}")
  end
end

status = case result
  Ok(n): n
  Error(_): 0
end
```

---

## 6. Tables & Relational Pipelines (`|>`)

Every `Table(...)` has a compile-time known schema: ordered column names, scalar types,
nullability (`T?`), sensitivity tags (`col_tags`), and table-level context tags (`row_tags`,
`order_tags`). Table pipelines are **strictly pure**, enabling automatic SQL pushdown,
vectorized batch execution, and parallel partitioning.

### 6.1 Markdown Table Literals

Literal tables use Markdown pipe syntax (normal Dana literals inside cells) and are ideal
for `examples` and `test` blocks:

<!-- dana-example: fragment -->
```dana
sample = table
  | date       | category | amount |
  | 2026-10-01 | "food"   |  12.50 |
  | 2026-10-02 | "rent"   | 900.00 |
end
```

### 6.2 Core Pipeline Verbs (One Canonical Way)

| Verb | Purpose |
| --- | --- |
| `where(pred)` | Filter rows using `.col` expressions |
| `select(.a, b: .old_b)` | Keep (and optionally alias) columns |
| `drop(.a, .b)` | Remove columns |
| `rename(new_name: .old_name)` | Rename columns |
| `derive(x: expr, ...)` | Add or replace computed columns |
| `sort_by(.a, .b)` / `sort_desc(.a)` | Deterministic sort |
| `distinct(.a)` / `distinct()` | Deduplicate rows |
| `limit(n)` | Take first `n` rows |
| `group_by(.a, .b)` | Set grouping keys |
| `summarize(n: count(), avg: mean(.x))` | Aggregate (`count`, `count_distinct`, `sum`, `mean`, `median`, `stddev`, `variance`, `percentile`, `min`, `max`) |
| `window(d: .x - lag(.x, 1), over: [.g], order: .t)` | Window functions (`lag`, `lead`, `row_number`, `rank`, `running_sum`, `rolling_mean`) |
| `fill_gaps(.t, every: 5.minutes, over: [.g], fill: {...})` | Fill missing time-series buckets |
| `pivot_wider(names_from: .k, values_from: .v, columns: [...], fill: 0)` | Statically typed pivot with compile-time column names |
| `crosstab(rows: .r, cols: .c, values: .v, fill: 0)` | Dynamic display matrix returning `DynamicTable` |
| `union(other)` | Concatenate tables with matching schemas |

### 6.3 Explicit-Cardinality Joins

Joins declare their expected cardinality so duplicate lookup keys **stop loudly** instead
of silently multiplying rows:

- `join_one` (1:1), `join_many_to_one` (N:1), `join_many` (N:M)
- `left_join_one`, `left_join_many_to_one` (unmatched right columns become `T?`)
- `semi_join`, `anti_join`
- **Keys:** use `on: .key` (or `on: [.a, .b]`) when both sides share key names, and explicit
  `on: left.id == right.student_id` when key names differ.
- **Collisions:** overlapping non-key column names are a compile error unless you `select`/
  `drop` first or pass explicit `suffixes: ("_left", "_right")`.

<!-- dana-example: fragment -->
```dana
merged = orders
  |> left_join_one(paid_by_order, on: .order_id)
  |> join_many_to_one(customers, on: left.cust_id == right.id)
```

---

## 7. Privacy, Sensitivity & Declassification

Full rules live in `docs/design/privacy.md`. Summary for authors and agents:

1. **Zero friction on public data:** untagged schemas have `col_tags = []` and
   `row_tags = []`; no privacy annotations are needed anywhere.
2. **Direct & implicit propagation:** selecting public columns from a table containing
   tagged columns stays public (`row_tags = []`), while `where`, `sort_by`, `distinct`,
   `join_*`, and `group_by` over tagged columns add those tags to `row_tags`.
3. **Four audited built-in declassifiers** (there is no unguarded free `declassify`):
   - `redact(.col)` — replaces values with `"[REDACTED]"`, clearing `col_tags(.col)`.
   - `pseudonymize(.col, key: secret)` — keyed HMAC-SHA256 deterministic token (requires a
     `Secret` capability), clearing `[pii]`.
   - `bucket(.col, cuts: [...], labels: [...])` — maps sensitive values into
     compile-time-constant public labels; stays tagged on individual rows and clears under
     `suppress_small_groups`.
   - `suppress_small_groups(min: k, distinct_by: .id)` — enforces `>= k` distinct entities
     (default floor `5`); clears `row_tags`, blending aggregates (`count`, `sum`, `mean`,
     `median`, `stddev`, `variance`, `percentile`), and `bucketed` group keys, while
     keeping non-bucketed group keys and `min`/`max` tagged.
4. **Authorized sinks & optional `dana.policy`:** output capabilities default to
   `allows: []`; authorized sinks list `allows: [...]`, `WriteTable` checks column-by-column
   schema tag compatibility, external sensitive exports require runtime `--allow-export=...`,
   and an optional repository `dana.policy` file enforces a hard human-readable ceiling.
5. **Safe-by-default runtime redaction:** on tagged schemas, `bad_rows` keeps `line`,
   `column`, and `error_kind` public while tagging `raw_value`/`raw_line`; runtime errors,
   `dana dry-run`, `profile()`, and `dana repl` automatically redact tagged values.

<!-- dana-example: fragment -->
```dana
safe = encounters
  |> derive(age_group: bucket(.age_years, cuts: [18, 45, 65], labels: ["0-17", "18-44", "45-64", "65+"]))
  |> group_by(.department, .age_group)
  |> summarize(patients: count_distinct(.patient_id), avg_los: mean(.length_of_stay_days))
  |> suppress_small_groups(min: 10, distinct_by: .patient_id)
```

---

## 8. Databases, Files, Analytics & Reports

- **Databases:** `db.table(Schema)` scans SQLite or Postgres and automatically pushes
  eligible filter, select, join, and aggregate stages into parameterized SQL (verified
  against offline `schema.lock`). `WriteTable.upsert(rows, key: .id)` previews redacted
  diffs under `dana dry-run`. Rare dialect-specific queries use capability-gated `RawReadDB`.
- **Files & HTTPS:** `files.read_csv`, `files.read_jsonl` (transparent `.gz`/`.zst`),
  `files.read_xlsx` return `Result((Table(S), Table(BadRow(S))), FileError)`;
  `files.read_parquet` returns `Result(Table(S), FileError)`. `HttpsAllow("host")` restricts
  outbound HTTP to an explicit host and tag allowlist.
- **Stats & Charts:** `table.profile()`, `Stats.corr`, `Stats.linear_regression`,
  `Stats.t_test`, `Stats.chi_square`, and zero-dependency charts (`chart_bar`, `chart_line`,
  `chart_scatter`, `chart_histogram`, `chart_heatmap`) rendered as standalone SVG in
  `Report` HTML/Markdown outputs or Unicode charts in the terminal.

---

## 9. Intent, Tests & Fake Capabilities

Functions may carry inline `examples ... end` and `promise ...` checks alongside top-level
`test "name" ... end` blocks. Every capability has an in-memory test double usable only in
spec code (`Files.in_memory`, `DB.in_memory`, `Console.fake`, `Https.fake`, `Secret.fake`):

<!-- dana-example: fragment -->
```dana
fn double_total(expenses: Table(Expense)) : Decimal
  examples
    sample = table
      | date       | category | amount |
      | 2026-10-01 | "food"   |  10.00 |
    end
    double_total(sample) == 20.00
  end

  promise . >= 0.00

  expenses.sum(.amount) * 2
end

test "empty table totals zero"
  empty = table
    | date | category | amount |
  end
  assert double_total(empty) == 0.00
end
```

---

## 10. Modules, Vendoring & CLI

- **No central package registry.** Modules import from the built-in stdlib, local project
  files, or hash-pinned `vendor/` files. Vendored modules are **pure by default** and
  cannot perform I/O unless passed a capability from `main`.
- **CLI commands:** `dana check`, `dana run`, `dana test`, `dana format`, `dana repl`,
  `dana explain`, `dana dry-run`, `dana fake`, `dana infer-schema`, `dana schema-sync`, and
  `dana guide`.

---

## 11. Grammar Authority

The complete context-free grammar is specified and checked for **zero LR(1) conflicts**
(`%define lr.type ielr`, `%expect 0`, no precedence declarations) in `grammar/dana.y`. Run
`make grammar` to validate `examples/*.dana`, every `dana` block in this reference, and the
positive/negative grammar test suite.
