# Dana Formal Core (`formal/`)

Lean 4 formalization, machine-checked proofs, canonical wire codec, and reference CLI oracle
(`danacore`) for **Dana Core IR v0.1**.

- **Toolchain:** `leanprover/lean4:v4.36.0` (bundled Lean 4 library only; **zero** external Lean packages).
- **Proofs:** 100% complete machine-checked proofs with **zero unproved goals** and **zero custom axioms** (`#print axioms` checked in `DanaCore/Tests.lean`).

## Layout

| File | Purpose |
| --- | --- |
| `lean-toolchain` | Pins `leanprover/lean4:v4.36.0` |
| `lakefile.toml` | Lake package defining library `DanaCore` and executable `danacore` |
| `DanaCore/Syntax.lean` | Sensitivity semilattice (`Tag`, canonical `TagSet` + proved algebraic laws), `ColSpec`, `TableTy`, monomorphic `Ty`/`LTy`, `RowExpr`, `Expr`, 21-operator pure relational `Plan`, `Policy`, `Program`, and lossless `CompilerMetadata` |
| `DanaCore/Check.lean` | Decidable static schema, type, sensitivity-taint, `bucketed`, `SuppressSmallGroups`, capability `allows`, column-matched `WriteTable`, `dana.policy`, and spec-code (`test`/`example`/`promise`) verifier |
| `DanaCore/Eval.lean` | Deterministic fuel-indexed big-step evaluator (`eval` / `evalPlan` / `evalRowExpr`), real + isolated fake `World` state, automatic `[REDACTED:tag]` runtime stop redaction, and canonical `ExecReport` extraction |
| `DanaCore/Soundness.lean` | **Theorem 1:** Schema & Type Soundness (well-typed programs/plans never evaluate to `Outcome.wrong`, never leak uncaught `Outcome.jumped`, and preserve `ValWf` / `TableValWf` / `WorldWf`) |
| `DanaCore/NonInterference.lean` | **Theorem 2:** Termination- and Error-Insensitive Non-Interference up to audited declassifiers & authorized sinks (`≈_L` on values, tables with `col_tags`/`row_tags`/`order_tags`, environments, and worlds; Confinement, TEINI on `ok` runs, and redacted explicit-`.stop` diagnostic non-interference) |
| `DanaCore/Text.lean` | Canonical `(dana-core 0.1 ...)` S-expression parser & printer + `(dana-report 0.1 ...)` report serializer |
| `DanaCore/Tests.lean` | Compiled-evaluator `#guard` tests across public pipelines, implicit-flow leaks, `bucket` + `suppress_small_groups`, `dana.policy` upper bounds, redacted duplicate-key diagnostics, S-expression round-trips, and `#print axioms` checks |
| `Main.lean` | `danacore` CLI oracle (`run`, `check`, `fmt`) |

## Build & Verification Commands

From the repository root:

```sh
make formal
```

Or directly inside `formal/`:

```sh
lake build
.lake/build/bin/danacore check <file.core>
.lake/build/bin/danacore run <file.core>
```

## Proved Theorems

1. **Theorem 1 — Schema & Type Soundness (`DanaCore/Soundness.lean`):**
   - Well-typed `Expr`s and `Plan`s never get stuck (`out ≠ Outcome.wrong`), closed evaluations never escape with `Outcome.jumped`, and every produced value satisfies `ValWf` (exact column count, column types, unique column names, unified `Option`, and `SuppressSmallGroups` tracked group-size floor invariants).
2. **Theorem 2 — Termination- and Error-Insensitive Non-Interference (`DanaCore/NonInterference.lean`):**
   - Fixes any observer clearance `L : TagSet` and defines `L`-indistinguishability (`ValEquiv`, `TableEquiv` accounting for `col_tags`, `row_tags`, and `order_tags` permutations, `EnvEquiv`, `WorldEquiv`).
   - Theorems 2A–2D prove that any well-typed program/expression/plan whose non-spec functions contain no declassifiers clearing tags outside `L`, whose sinks satisfy `allows ⊆ L`, whose declared algebraic `Data` types satisfy `progDatasSortableForNI`, and whose stored DB tables satisfy `progRespectsDB` maps `L`-equivalent worlds to `L`-equivalent values and byte-for-byte identical observable `ExecReport`s whenever both runs finish normally (`status = ok`).
   - Theorem 2E proves that when an explicit `.stop kind (some detailExpr)` executes from publicly equivalent states (`L = []`) and `detailExpr` evaluates normally on both runs, both executions stop with the exact same `[REDACTED:tag]` diagnostic and observable `ExecReport` regardless of the sensitive payload.

## Explicit Trust Boundary

- **Timing, memory, termination, and stop/trap position divergence (`ok` vs. `stopped`)**: Theorems 2A–2D assume both runs terminate with `status = ok`. Because `extractReport` retains stdout/stderr/writes emitted prior to a stop, the *position* of a runtime trap (such as `100 / (secret - i)` divide-by-zero or `Int64`/`Decimal` overflow) or an explicit `.stop` executed conditionally under a sensitive `pc` is observable and can leak an entire small-domain sensitive value in a single run (for example via a loop printing public indices before trapping).
- **Database schema fidelity (`progRespectsDB`)**: stored DB tables read via `SourceDB` are trusted to match their declared schemas and sensitivity tags.
- **Audited declassifiers crossing `L`**: `DeclassifyApprove`, `Pseudonymize`, and `SuppressSmallGroups` clearing tags outside `L` are excluded from `progSafeForNI` as the audited declassification trust boundary.
- **Outside-boundary operations**: live wire/binary codecs (`rawSqlQuery`, `httpsGetJson`, `readParquet`, `writeParquet`, `writeXlsx`) and `statsTTest` (which requires a Student-t CDF / incomplete beta function) return `BugKind.outsideBoundary` in the Lean Core oracle.

## Numeric, Statistical & Path-Confinement Conventions

- **`variance` / `stddev`:** Population denominator (`/ n`), returning `some(0.0)` for `n = 1` and `none` for `n = 0` (`stddev` scales deviations by `max |x - mean|`).
- **`percentile(p)`:** Requires finite `p ∈ [0.0, 1.0]` (validated statically by `checkProgram`) and uses overflow-safe linear interpolation on sorted non-null values.
- **`median`:** On `Decimal` columns uses exact scaled integer midpoint (`(lo + hi) / 2` toward zero); on `Float`/`Int` columns returns `Float` using `(lo / 2.0) + (hi / 2.0)`.
- **`statsCorr` / `statsLinReg`:** Non-finite (`NaN`/`±Inf`) inputs are rejected up front, and deviations are scaled by `max |x - mean|` before squaring. `statsCorr` returns `none` for `< 2` points, non-finite inputs, or zero variance in `x` or `y`; `statsLinReg` stops with `BugKind.divByZero` on degenerate inputs (`< 2` points, non-finite inputs, or zero variance in `x`).
- **Write-path confinement:** `.writeFile`, `.writeReportHtml`, `.writeParquet`, and `.writeXlsx` reject unsafe `relPath` values (empty, leading `/`, `\`, or `".."` segment) with `Err(...)` without mutating `World`, and join `(root, relPath)` with a single `/` (`joinConfinedPath`).

## Canonical Wire Format

Programs serialize as single-line canonical S-expressions terminated by LF (`\n`):

```lisp
(dana-core 0.1 (custom-tags ...) (none) (datas ...) (schemas ...) (consts ...) (funs ...) (some "main") (meta ...))
```

Execution reports serialize as:

```lisp
(dana-report 0.1 (status ok) (diagnostic (none)) (stdout ...) (stderr ...) (written-files ...) (written-tables ...) (fake-consoles ...) (fake-files ...))
```
