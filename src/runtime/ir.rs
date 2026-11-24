//! Execution IR (`ExecProgram`) wrapping Dana Core IR v0.1 plus Phase 2 surface runtime
//! extensions, with lossless `try_to_core_program` conversion for pure Core IR v0.1 programs.

use std::collections::HashMap;
use std::sync::Arc;

use crate::core::bigint::BigInt;
use crate::core::syntax::*;

/// Selects whether `pseudonymize` uses the Lean Core IR v0.1 deterministic token (`fnv1a64`)
/// or the production keyed HMAC-SHA256 construction.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub enum PseudonymizeMode {
    #[default]
    CoreV01Fnv1a,
    HmacSha256,
}

/// Struct field-name layout metadata used for field projection on `Val::Ctor`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StructLayout {
    pub name: Ident,
    pub field_names: Vec<Ident>,
    pub field_ltys: Vec<LTy>,
}

/// Schema with optional compiled per-column `where` constraint predicates.
#[derive(Clone, Debug)]
pub struct CompiledSchema {
    pub decl: SchemaDecl,
    /// Parallel to `decl.schema.cols`; each `Some(re)` evaluates against a single-column row
    /// binding `.` (column name `"__self"`) to the non-null cell value and returns `Bool`.
    pub constraints: Vec<Option<ExecRowExpr>>,
}

/// Primitive operations: either a pure Core IR v0.1 [`PrimOp`] or a Phase 2 runtime extension.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExecPrimOp {
    Core(PrimOp),
    // Float scalar arithmetic & math
    AddFloat,
    SubFloat,
    MulFloat,
    DivFloat,
    NegFloat,
    AbsFloat,
    AbsDecimal,
    AbsInt,
    RoundFloat,
    RoundDecimal,
    IntToFloat,
    DecToFloat,
    // Formatting / string interpolation conversions
    ValToText,
    // Temporal ops
    DateTruncUnit(String),
    DateTruncDuration,
    MonthsBetween,
    InTz,
    DateInTz,
    // Collection & Table surface helpers
    ListFirst,
    ListFirstBang,
    TableEmpty,
    TableFirstBang,
    TableRowsToList,
    TableColSum(Ident),
    TableColMean(Ident),
    TableColStddev(Ident),
    TableBuildDynamic(TableTy),
    /// Coerce a table literal/value into a target `TableTy` (promoting `T` -> `Option(T)` and tags).
    TableCoerce(TableTy),
    /// Access named field on `Val::Ctor`, `Val::LinearModel`, `Val::StatTest`, or `TableRow` map/tuple.
    RecordField {
        type_name: Ident,
        field_name: Ident,
        field_idx: usize,
    },
    /// Two-sample Welch t-test across two tables (`Stats.t_test(a, b, column: .col)`).
    StatsWelchTTest {
        col: Ident,
    },
    /// Optional binary numeric promotion (`Int - Option(Int)` -> `Option(Int)` for window diffs).
    OptSubInt,
    OptSubDec,
    OptSubFloat,
    /// `Table` structural value equality (compares rows and cells ignoring hidden `group_meta`).
    TableEq,
    /// Promise helpers evaluated on a table value.
    PromiseUnique(Vec<Ident>),
    /// Check `all(pred)` over every row of a table.
    PromiseAll,
}

/// Host I/O and spec fake-capability operations.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExecHostOp {
    Core(HostOp),
    /// `Args.of(list)` (spec-only synthetic Args value).
    FakeArgsOf,
    /// `args.first` -> `Option(Text)`.
    ArgsFirst,
    /// `Files.in_memory(map)` -> fake `ReadFiles` seeded with inline file contents.
    FakeFilesInMemory,
    /// `DB.in_memory(db, map)` -> fake `ReadDB` seeded with inline tables.
    FakeDbInMemory {
        db: Ident,
        table_names: Vec<Ident>,
    },
    /// `console.printed_lines` / `printed_errors` / `printed_tables` (fake Console inspection).
    FakeConsoleLines,
    FakeConsoleErrors,
    FakeConsoleTables,
    /// `console.print_chart(c)` / `console.print_profile(p)`.
    ConsolePrintChart,
    ConsolePrintProfile,
    /// `files.read_jsonl(path, as: Schema)` -> `Result((Table(S), Table(BadRow(S))), Text)`.
    ReadJsonl(Ident),
    /// `files.read_xlsx(path, sheet: ..., as: Schema)` (Phase 4 boundary).
    ReadXlsx(Ident),
    /// `out.write_csv(path, table)` / `out.write_jsonl(path, table)`.
    WriteCsv,
    WriteJsonl,
    /// `db_write.upsert(table, key: .k)` (Phase 3 boundary on real handle).
    WriteTableUpsert {
        key_col: Ident,
    },
    /// `response.parse_table(field, as: S)` / `response.bool_at(field)` (Phase 4 HTTPS JSON).
    JsonParseTable(Ident),
    JsonBoolAt,
}

/// Row-level pure expression inside `where`, `derive`, `summarize`, and `schema where`.
#[derive(Debug, PartialEq, Eq)]
pub enum ExecRowExpr {
    Lit(Literal),
    Col(Ident),
    OuterVar(Ident),
    ConstRef(Ident),
    Prim {
        op: ExecPrimOp,
        args: Vec<ExecRowExpr>,
    },
    IfE {
        cond: Box<ExecRowExpr>,
        then_br: Box<ExecRowExpr>,
        else_br: Box<ExecRowExpr>,
    },
    Coalesce {
        opt_expr: Box<ExecRowExpr>,
        default_expr: Box<ExecRowExpr>,
    },
    CallPure {
        fn_name: Ident,
        args: Vec<ExecRowExpr>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExecAggItem {
    pub name: Ident,
    pub op: AggOp,
    pub arg: Option<ExecRowExpr>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExecDeriveItem {
    ColExpr {
        name: Ident,
        expr: Box<ExecRowExpr>,
    },
    BucketCol {
        name: Ident,
        source: Ident,
        cuts: Vec<Literal>,
        labels: Vec<String>,
    },
}

#[derive(Debug, PartialEq, Eq)]
pub enum ExecPlan {
    SourceExpr(Box<ExecExpr>),
    SourceDB {
        cap: Box<ExecExpr>,
        table_name: Ident,
        schema: TableTy,
    },
    Select {
        input: Box<ExecPlan>,
        cols: Vec<Ident>,
    },
    Drop {
        input: Box<ExecPlan>,
        cols: Vec<Ident>,
    },
    Rename {
        input: Box<ExecPlan>,
        pairs: Vec<(Ident, Ident)>,
    },
    Derive {
        input: Box<ExecPlan>,
        items: Vec<ExecDeriveItem>,
    },
    Filter {
        input: Box<ExecPlan>,
        pred: ExecRowExpr,
    },
    Distinct {
        input: Box<ExecPlan>,
        cols: Vec<Ident>,
    },
    Sort {
        input: Box<ExecPlan>,
        keys: Vec<(Ident, SortDir)>,
    },
    Limit {
        input: Box<ExecPlan>,
        n: BigInt,
    },
    Join {
        kind: JoinKind,
        left: Box<ExecPlan>,
        right: Box<ExecPlan>,
        on: JoinOn,
        suffixes: Suffixes,
    },
    Union {
        left: Box<ExecPlan>,
        right: Box<ExecPlan>,
    },
    GroupBy {
        input: Box<ExecPlan>,
        keys: Vec<Ident>,
    },
    Summarize {
        input: Box<ExecPlan>,
        aggs: Vec<ExecAggItem>,
        distinct_key: Option<Ident>,
    },
    SuppressSmallGroups {
        input: Box<ExecPlan>,
        min_k: BigInt,
        distinct_by: Option<Ident>,
        mode: SuppressMode,
    },
    Window {
        input: Box<ExecPlan>,
        items: Vec<WindowItem>,
    },
    FillGaps {
        input: Box<ExecPlan>,
        col: Ident,
        step_micros: BigInt,
        over: Vec<Ident>,
        fill: Vec<(Ident, Literal)>,
    },
    PivotWider {
        input: Box<ExecPlan>,
        names_from: Ident,
        values_from: Ident,
        static_cols: Vec<Ident>,
        fill: Literal,
    },
    Crosstab {
        input: Box<ExecPlan>,
        rows_col: Ident,
        cols_col: Ident,
        values_col: Ident,
        fill: Literal,
    },
    Redact {
        input: Box<ExecPlan>,
        col: Ident,
        replacement: String,
    },
    Pseudonymize {
        input: Box<ExecPlan>,
        col: Ident,
        secret: Box<ExecExpr>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExecCaseArm {
    pub pattern: ExecPattern,
    pub body: ExecExpr,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExecPattern {
    Wildcard,
    Bind(Ident),
    Ctor { ctor: Ident, binders: Vec<Ident> },
    Lit(Literal),
    ListExact(Vec<Ident>),
}

#[derive(Debug, PartialEq, Eq)]
pub enum ExecExpr {
    Lit(Literal),
    Var(Ident),
    ConstRef(Ident),
    LetE {
        name: Ident,
        lty: LTy,
        bound: Box<ExecExpr>,
        body: Box<ExecExpr>,
    },
    IfE {
        cond: Box<ExecExpr>,
        then_br: Box<ExecExpr>,
        else_br: Box<ExecExpr>,
    },
    CaseE {
        scrut: Box<ExecExpr>,
        arms: Vec<ExecCaseArm>,
    },
    Lam {
        params: Vec<(Ident, LTy)>,
        pc: TagSet,
        ret: LTy,
        body: Arc<ExecExpr>,
    },
    App {
        fn_expr: Box<ExecExpr>,
        args: Vec<ExecExpr>,
    },
    Call {
        fn_name: Ident,
        args: Vec<ExecExpr>,
    },
    Join {
        label: Ident,
        params: Vec<(Ident, LTy)>,
        rhs: Box<ExecExpr>,
        body: Box<ExecExpr>,
    },
    Jump {
        label: Ident,
        args: Vec<ExecExpr>,
    },
    /// Iterative `for` loop lowered cleanly (handles mutable loop-carried state + `break`/`continue`).
    ForLoop {
        item_var: Ident,
        iter_expr: Box<ExecExpr>,
        state_vars: Vec<(Ident, LTy)>,
        body: Box<ExecExpr>,
        after: Box<ExecExpr>,
    },
    /// Iterative `while` loop with loop-carried state variables.
    WhileLoop {
        cond: Box<ExecExpr>,
        state_vars: Vec<(Ident, LTy)>,
        body: Box<ExecExpr>,
        after: Box<ExecExpr>,
    },
    Tuple(Vec<ExecExpr>),
    Proj {
        tup: Box<ExecExpr>,
        idx: BigInt,
    },
    Ctor {
        type_name: Ident,
        ctor_name: Ident,
        args: Vec<ExecExpr>,
    },
    TableLit {
        schema: TableTy,
        rows: Vec<RowLit>,
    },
    Prim {
        op: ExecPrimOp,
        args: Vec<ExecExpr>,
    },
    Rel(Box<ExecPlan>),
    Host {
        op: ExecHostOp,
        args: Vec<ExecExpr>,
    },
    /// Assert boolean expression (stops with `BugKind::PromiseViolation` / `UserStop` when false).
    Assert {
        cond: Box<ExecExpr>,
        message: String,
    },
    /// Evaluate `promise` predicate against table or return value.
    CheckPromise {
        ret_var: Ident,
        promise: ExecPromise,
    },
    Stop {
        kind: BugKind,
        detail: Option<Box<ExecExpr>>,
        detail_tags: TagSet,
    },
    Fail(Box<ExecExpr>),
}

impl ExecExpr {
    /// Extract the inner [`Literal`] without moving out of a custom-`Drop` enum.
    #[must_use]
    pub fn into_lit(mut self) -> Option<Literal> {
        match &mut self {
            Self::Lit(l) => Some(std::mem::replace(l, Literal::Unit)),
            _ => None,
        }
    }

    /// Unwrap `ExecExpr::Rel(plan)` or wrap as `ExecPlan::SourceExpr(self)` without moving out
    /// of a custom-`Drop` enum.
    #[must_use]
    pub fn into_plan(mut self) -> ExecPlan {
        if let Self::Rel(plan) = &mut self {
            std::mem::replace(
                plan.as_mut(),
                ExecPlan::SourceExpr(Box::new(Self::Lit(Literal::Unit))),
            )
        } else {
            ExecPlan::SourceExpr(Box::new(self))
        }
    }
}

// ---------------------------------------------------------------------------
// Iterative Clone for ExecExpr / ExecPlan / ExecRowExpr (O(1) Call Stack)
// ---------------------------------------------------------------------------

enum ExecCloneTask<'a> {
    Expr(&'a ExecExpr),
    Plan(&'a ExecPlan),
    Row(&'a ExecRowExpr),
    BuildExpr(CloneBuildExpr<'a>),
    BuildPlan(CloneBuildPlan<'a>),
    BuildRow(CloneBuildRow<'a>),
}

enum CloneBuildRow<'a> {
    Prim(&'a ExecPrimOp, usize),
    IfE,
    Coalesce,
    CallPure(&'a Ident, usize),
}

enum CloneBuildPlan<'a> {
    SourceExpr,
    SourceDB(&'a Ident, &'a TableTy),
    Select(&'a [Ident]),
    Drop(&'a [Ident]),
    Rename(&'a [(Ident, Ident)]),
    Derive(&'a [ExecDeriveItem]),
    Filter,
    Distinct(&'a [Ident]),
    Sort(&'a [(Ident, SortDir)]),
    Limit(&'a BigInt),
    Join(JoinKind, &'a JoinOn, &'a Suffixes),
    Union,
    GroupBy(&'a [Ident]),
    Summarize(&'a [ExecAggItem], &'a Option<Ident>),
    SuppressSmallGroups(&'a BigInt, &'a Option<Ident>, SuppressMode),
    Window(&'a [WindowItem]),
    FillGaps(&'a Ident, &'a BigInt, &'a [Ident], &'a [(Ident, Literal)]),
    PivotWider(&'a Ident, &'a Ident, &'a [Ident], &'a Literal),
    Crosstab(&'a Ident, &'a Ident, &'a Ident, &'a Literal),
    Redact(&'a Ident, &'a str),
    Pseudonymize(&'a Ident),
}

enum CloneBuildExpr<'a> {
    LetE(&'a Ident, &'a LTy),
    IfE,
    CaseE(&'a [ExecCaseArm]),
    App(usize),
    Call(&'a Ident, usize),
    Join(&'a Ident, &'a [(Ident, LTy)]),
    Jump(&'a Ident, usize),
    ForLoop(&'a Ident, &'a [(Ident, LTy)]),
    WhileLoop(&'a [(Ident, LTy)]),
    Tuple(usize),
    Proj(&'a BigInt),
    Ctor(&'a Ident, &'a Ident, usize),
    Prim(&'a ExecPrimOp, usize),
    Rel,
    Host(&'a ExecHostOp, usize),
    Assert(&'a str),
    CheckPromiseAll(&'a Ident),
    CheckPromiseBool(&'a Ident),
    Stop(BugKind, &'a TagSet, bool),
    Fail,
}

fn run_exec_clone(initial: ExecCloneTask<'_>) -> (Vec<ExecExpr>, Vec<ExecPlan>, Vec<ExecRowExpr>) {
    let mut tasks = vec![initial];
    let mut exprs: Vec<ExecExpr> = Vec::new();
    let mut plans: Vec<ExecPlan> = Vec::new();
    let mut rows: Vec<ExecRowExpr> = Vec::new();

    while let Some(task) = tasks.pop() {
        match task {
            ExecCloneTask::Row(re) => match re {
                ExecRowExpr::Lit(l) => rows.push(ExecRowExpr::Lit(l.clone())),
                ExecRowExpr::Col(c) => rows.push(ExecRowExpr::Col(c.clone())),
                ExecRowExpr::OuterVar(v) => rows.push(ExecRowExpr::OuterVar(v.clone())),
                ExecRowExpr::ConstRef(c) => rows.push(ExecRowExpr::ConstRef(c.clone())),
                ExecRowExpr::Prim { op, args } => {
                    tasks.push(ExecCloneTask::BuildRow(CloneBuildRow::Prim(op, args.len())));
                    for a in args.iter().rev() {
                        tasks.push(ExecCloneTask::Row(a));
                    }
                }
                ExecRowExpr::IfE {
                    cond,
                    then_br,
                    else_br,
                } => {
                    tasks.push(ExecCloneTask::BuildRow(CloneBuildRow::IfE));
                    tasks.push(ExecCloneTask::Row(else_br));
                    tasks.push(ExecCloneTask::Row(then_br));
                    tasks.push(ExecCloneTask::Row(cond));
                }
                ExecRowExpr::Coalesce {
                    opt_expr,
                    default_expr,
                } => {
                    tasks.push(ExecCloneTask::BuildRow(CloneBuildRow::Coalesce));
                    tasks.push(ExecCloneTask::Row(default_expr));
                    tasks.push(ExecCloneTask::Row(opt_expr));
                }
                ExecRowExpr::CallPure { fn_name, args } => {
                    tasks.push(ExecCloneTask::BuildRow(CloneBuildRow::CallPure(
                        fn_name,
                        args.len(),
                    )));
                    for a in args.iter().rev() {
                        tasks.push(ExecCloneTask::Row(a));
                    }
                }
            },
            ExecCloneTask::BuildRow(op) => match op {
                CloneBuildRow::Prim(pop, n) => {
                    let start = rows.len().saturating_sub(n);
                    let args = rows.split_off(start);
                    rows.push(ExecRowExpr::Prim {
                        op: pop.clone(),
                        args,
                    });
                }
                CloneBuildRow::IfE => {
                    if let (Some(e), Some(t), Some(c)) = (rows.pop(), rows.pop(), rows.pop()) {
                        rows.push(ExecRowExpr::IfE {
                            cond: Box::new(c),
                            then_br: Box::new(t),
                            else_br: Box::new(e),
                        });
                    }
                }
                CloneBuildRow::Coalesce => {
                    if let (Some(d), Some(o)) = (rows.pop(), rows.pop()) {
                        rows.push(ExecRowExpr::Coalesce {
                            opt_expr: Box::new(o),
                            default_expr: Box::new(d),
                        });
                    }
                }
                CloneBuildRow::CallPure(fn_name, n) => {
                    let start = rows.len().saturating_sub(n);
                    let args = rows.split_off(start);
                    rows.push(ExecRowExpr::CallPure {
                        fn_name: fn_name.clone(),
                        args,
                    });
                }
            },
            ExecCloneTask::Plan(plan) => match plan {
                ExecPlan::SourceExpr(e) => {
                    tasks.push(ExecCloneTask::BuildPlan(CloneBuildPlan::SourceExpr));
                    tasks.push(ExecCloneTask::Expr(e));
                }
                ExecPlan::SourceDB {
                    cap,
                    table_name,
                    schema,
                } => {
                    tasks.push(ExecCloneTask::BuildPlan(CloneBuildPlan::SourceDB(
                        table_name, schema,
                    )));
                    tasks.push(ExecCloneTask::Expr(cap));
                }
                ExecPlan::Select { input, cols } => {
                    tasks.push(ExecCloneTask::BuildPlan(CloneBuildPlan::Select(cols)));
                    tasks.push(ExecCloneTask::Plan(input));
                }
                ExecPlan::Drop { input, cols } => {
                    tasks.push(ExecCloneTask::BuildPlan(CloneBuildPlan::Drop(cols)));
                    tasks.push(ExecCloneTask::Plan(input));
                }
                ExecPlan::Rename { input, pairs } => {
                    tasks.push(ExecCloneTask::BuildPlan(CloneBuildPlan::Rename(pairs)));
                    tasks.push(ExecCloneTask::Plan(input));
                }
                ExecPlan::Derive { input, items } => {
                    tasks.push(ExecCloneTask::BuildPlan(CloneBuildPlan::Derive(items)));
                    for it in items.iter().rev() {
                        if let ExecDeriveItem::ColExpr { expr, .. } = it {
                            tasks.push(ExecCloneTask::Row(expr));
                        }
                    }
                    tasks.push(ExecCloneTask::Plan(input));
                }
                ExecPlan::Filter { input, pred } => {
                    tasks.push(ExecCloneTask::BuildPlan(CloneBuildPlan::Filter));
                    tasks.push(ExecCloneTask::Row(pred));
                    tasks.push(ExecCloneTask::Plan(input));
                }
                ExecPlan::Distinct { input, cols } => {
                    tasks.push(ExecCloneTask::BuildPlan(CloneBuildPlan::Distinct(cols)));
                    tasks.push(ExecCloneTask::Plan(input));
                }
                ExecPlan::Sort { input, keys } => {
                    tasks.push(ExecCloneTask::BuildPlan(CloneBuildPlan::Sort(keys)));
                    tasks.push(ExecCloneTask::Plan(input));
                }
                ExecPlan::Limit { input, n } => {
                    tasks.push(ExecCloneTask::BuildPlan(CloneBuildPlan::Limit(n)));
                    tasks.push(ExecCloneTask::Plan(input));
                }
                ExecPlan::Join {
                    kind,
                    left,
                    right,
                    on,
                    suffixes,
                } => {
                    tasks.push(ExecCloneTask::BuildPlan(CloneBuildPlan::Join(
                        *kind, on, suffixes,
                    )));
                    tasks.push(ExecCloneTask::Plan(right));
                    tasks.push(ExecCloneTask::Plan(left));
                }
                ExecPlan::Union { left, right } => {
                    tasks.push(ExecCloneTask::BuildPlan(CloneBuildPlan::Union));
                    tasks.push(ExecCloneTask::Plan(right));
                    tasks.push(ExecCloneTask::Plan(left));
                }
                ExecPlan::GroupBy { input, keys } => {
                    tasks.push(ExecCloneTask::BuildPlan(CloneBuildPlan::GroupBy(keys)));
                    tasks.push(ExecCloneTask::Plan(input));
                }
                ExecPlan::Summarize {
                    input,
                    aggs,
                    distinct_key,
                } => {
                    tasks.push(ExecCloneTask::BuildPlan(CloneBuildPlan::Summarize(
                        aggs,
                        distinct_key,
                    )));
                    for a in aggs.iter().rev() {
                        if let Some(re) = &a.arg {
                            tasks.push(ExecCloneTask::Row(re));
                        }
                    }
                    tasks.push(ExecCloneTask::Plan(input));
                }
                ExecPlan::SuppressSmallGroups {
                    input,
                    min_k,
                    distinct_by,
                    mode,
                } => {
                    tasks.push(ExecCloneTask::BuildPlan(
                        CloneBuildPlan::SuppressSmallGroups(min_k, distinct_by, *mode),
                    ));
                    tasks.push(ExecCloneTask::Plan(input));
                }
                ExecPlan::Window { input, items } => {
                    tasks.push(ExecCloneTask::BuildPlan(CloneBuildPlan::Window(items)));
                    tasks.push(ExecCloneTask::Plan(input));
                }
                ExecPlan::FillGaps {
                    input,
                    col,
                    step_micros,
                    over,
                    fill,
                } => {
                    tasks.push(ExecCloneTask::BuildPlan(CloneBuildPlan::FillGaps(
                        col,
                        step_micros,
                        over,
                        fill,
                    )));
                    tasks.push(ExecCloneTask::Plan(input));
                }
                ExecPlan::PivotWider {
                    input,
                    names_from,
                    values_from,
                    static_cols,
                    fill,
                } => {
                    tasks.push(ExecCloneTask::BuildPlan(CloneBuildPlan::PivotWider(
                        names_from,
                        values_from,
                        static_cols,
                        fill,
                    )));
                    tasks.push(ExecCloneTask::Plan(input));
                }
                ExecPlan::Crosstab {
                    input,
                    rows_col,
                    cols_col,
                    values_col,
                    fill,
                } => {
                    tasks.push(ExecCloneTask::BuildPlan(CloneBuildPlan::Crosstab(
                        rows_col, cols_col, values_col, fill,
                    )));
                    tasks.push(ExecCloneTask::Plan(input));
                }
                ExecPlan::Redact {
                    input,
                    col,
                    replacement,
                } => {
                    tasks.push(ExecCloneTask::BuildPlan(CloneBuildPlan::Redact(
                        col,
                        replacement,
                    )));
                    tasks.push(ExecCloneTask::Plan(input));
                }
                ExecPlan::Pseudonymize { input, col, secret } => {
                    tasks.push(ExecCloneTask::BuildPlan(CloneBuildPlan::Pseudonymize(col)));
                    tasks.push(ExecCloneTask::Expr(secret));
                    tasks.push(ExecCloneTask::Plan(input));
                }
            },
            ExecCloneTask::BuildPlan(op) => match op {
                CloneBuildPlan::SourceExpr => {
                    if let Some(e) = exprs.pop() {
                        plans.push(ExecPlan::SourceExpr(Box::new(e)));
                    }
                }
                CloneBuildPlan::SourceDB(table_name, schema) => {
                    if let Some(cap) = exprs.pop() {
                        plans.push(ExecPlan::SourceDB {
                            cap: Box::new(cap),
                            table_name: table_name.clone(),
                            schema: schema.clone(),
                        });
                    }
                }
                CloneBuildPlan::Select(cols) => {
                    if let Some(input) = plans.pop() {
                        plans.push(ExecPlan::Select {
                            input: Box::new(input),
                            cols: cols.to_vec(),
                        });
                    }
                }
                CloneBuildPlan::Drop(cols) => {
                    if let Some(input) = plans.pop() {
                        plans.push(ExecPlan::Drop {
                            input: Box::new(input),
                            cols: cols.to_vec(),
                        });
                    }
                }
                CloneBuildPlan::Rename(pairs) => {
                    if let Some(input) = plans.pop() {
                        plans.push(ExecPlan::Rename {
                            input: Box::new(input),
                            pairs: pairs.to_vec(),
                        });
                    }
                }
                CloneBuildPlan::Derive(items) => {
                    let row_count = items
                        .iter()
                        .filter(|it| matches!(it, ExecDeriveItem::ColExpr { .. }))
                        .count();
                    let start = rows.len().saturating_sub(row_count);
                    let mut row_vals = rows.split_off(start).into_iter();
                    if let Some(input) = plans.pop() {
                        let mut citems = Vec::with_capacity(items.len());
                        for item in items {
                            match item {
                                ExecDeriveItem::ColExpr { name, .. } => {
                                    if let Some(re) = row_vals.next() {
                                        citems.push(ExecDeriveItem::ColExpr {
                                            name: name.clone(),
                                            expr: Box::new(re),
                                        });
                                    }
                                }
                                ExecDeriveItem::BucketCol {
                                    name,
                                    source,
                                    cuts,
                                    labels,
                                } => citems.push(ExecDeriveItem::BucketCol {
                                    name: name.clone(),
                                    source: source.clone(),
                                    cuts: cuts.clone(),
                                    labels: labels.clone(),
                                }),
                            }
                        }
                        plans.push(ExecPlan::Derive {
                            input: Box::new(input),
                            items: citems,
                        });
                    }
                }
                CloneBuildPlan::Filter => {
                    if let (Some(pred), Some(input)) = (rows.pop(), plans.pop()) {
                        plans.push(ExecPlan::Filter {
                            input: Box::new(input),
                            pred,
                        });
                    }
                }
                CloneBuildPlan::Distinct(cols) => {
                    if let Some(input) = plans.pop() {
                        plans.push(ExecPlan::Distinct {
                            input: Box::new(input),
                            cols: cols.to_vec(),
                        });
                    }
                }
                CloneBuildPlan::Sort(keys) => {
                    if let Some(input) = plans.pop() {
                        plans.push(ExecPlan::Sort {
                            input: Box::new(input),
                            keys: keys.to_vec(),
                        });
                    }
                }
                CloneBuildPlan::Limit(n) => {
                    if let Some(input) = plans.pop() {
                        plans.push(ExecPlan::Limit {
                            input: Box::new(input),
                            n: n.clone(),
                        });
                    }
                }
                CloneBuildPlan::Join(kind, on, suffixes) => {
                    if let (Some(right), Some(left)) = (plans.pop(), plans.pop()) {
                        plans.push(ExecPlan::Join {
                            kind,
                            left: Box::new(left),
                            right: Box::new(right),
                            on: on.clone(),
                            suffixes: suffixes.clone(),
                        });
                    }
                }
                CloneBuildPlan::Union => {
                    if let (Some(right), Some(left)) = (plans.pop(), plans.pop()) {
                        plans.push(ExecPlan::Union {
                            left: Box::new(left),
                            right: Box::new(right),
                        });
                    }
                }
                CloneBuildPlan::GroupBy(keys) => {
                    if let Some(input) = plans.pop() {
                        plans.push(ExecPlan::GroupBy {
                            input: Box::new(input),
                            keys: keys.to_vec(),
                        });
                    }
                }
                CloneBuildPlan::Summarize(aggs, distinct_key) => {
                    let arg_count = aggs.iter().filter(|a| a.arg.is_some()).count();
                    let start = rows.len().saturating_sub(arg_count);
                    let mut arg_vals = rows.split_off(start).into_iter();
                    if let Some(input) = plans.pop() {
                        let mut caggs = Vec::with_capacity(aggs.len());
                        for a in aggs {
                            caggs.push(ExecAggItem {
                                name: a.name.clone(),
                                op: a.op,
                                arg: if a.arg.is_some() {
                                    arg_vals.next()
                                } else {
                                    None
                                },
                            });
                        }
                        plans.push(ExecPlan::Summarize {
                            input: Box::new(input),
                            aggs: caggs,
                            distinct_key: distinct_key.clone(),
                        });
                    }
                }
                CloneBuildPlan::SuppressSmallGroups(min_k, distinct_by, mode) => {
                    if let Some(input) = plans.pop() {
                        plans.push(ExecPlan::SuppressSmallGroups {
                            input: Box::new(input),
                            min_k: min_k.clone(),
                            distinct_by: distinct_by.clone(),
                            mode,
                        });
                    }
                }
                CloneBuildPlan::Window(items) => {
                    if let Some(input) = plans.pop() {
                        plans.push(ExecPlan::Window {
                            input: Box::new(input),
                            items: items.to_vec(),
                        });
                    }
                }
                CloneBuildPlan::FillGaps(col, step_micros, over, fill) => {
                    if let Some(input) = plans.pop() {
                        plans.push(ExecPlan::FillGaps {
                            input: Box::new(input),
                            col: col.clone(),
                            step_micros: step_micros.clone(),
                            over: over.to_vec(),
                            fill: fill.to_vec(),
                        });
                    }
                }
                CloneBuildPlan::PivotWider(names_from, values_from, static_cols, fill) => {
                    if let Some(input) = plans.pop() {
                        plans.push(ExecPlan::PivotWider {
                            input: Box::new(input),
                            names_from: names_from.clone(),
                            values_from: values_from.clone(),
                            static_cols: static_cols.to_vec(),
                            fill: fill.clone(),
                        });
                    }
                }
                CloneBuildPlan::Crosstab(rows_col, cols_col, values_col, fill) => {
                    if let Some(input) = plans.pop() {
                        plans.push(ExecPlan::Crosstab {
                            input: Box::new(input),
                            rows_col: rows_col.clone(),
                            cols_col: cols_col.clone(),
                            values_col: values_col.clone(),
                            fill: fill.clone(),
                        });
                    }
                }
                CloneBuildPlan::Redact(col, replacement) => {
                    if let Some(input) = plans.pop() {
                        plans.push(ExecPlan::Redact {
                            input: Box::new(input),
                            col: col.clone(),
                            replacement: replacement.to_string(),
                        });
                    }
                }
                CloneBuildPlan::Pseudonymize(col) => {
                    if let (Some(secret), Some(input)) = (exprs.pop(), plans.pop()) {
                        plans.push(ExecPlan::Pseudonymize {
                            input: Box::new(input),
                            col: col.clone(),
                            secret: Box::new(secret),
                        });
                    }
                }
            },
            ExecCloneTask::Expr(expr) => match expr {
                ExecExpr::Lit(l) => exprs.push(ExecExpr::Lit(l.clone())),
                ExecExpr::Var(v) => exprs.push(ExecExpr::Var(v.clone())),
                ExecExpr::ConstRef(c) => exprs.push(ExecExpr::ConstRef(c.clone())),
                ExecExpr::TableLit { schema, rows: rs } => exprs.push(ExecExpr::TableLit {
                    schema: schema.clone(),
                    rows: rs.clone(),
                }),
                ExecExpr::Lam {
                    params,
                    pc,
                    ret,
                    body,
                } => exprs.push(ExecExpr::Lam {
                    params: params.clone(),
                    pc: pc.clone(),
                    ret: ret.clone(),
                    body: Arc::clone(body),
                }),
                ExecExpr::LetE {
                    name,
                    lty,
                    bound,
                    body,
                } => {
                    tasks.push(ExecCloneTask::BuildExpr(CloneBuildExpr::LetE(name, lty)));
                    tasks.push(ExecCloneTask::Expr(body));
                    tasks.push(ExecCloneTask::Expr(bound));
                }
                ExecExpr::IfE {
                    cond,
                    then_br,
                    else_br,
                } => {
                    tasks.push(ExecCloneTask::BuildExpr(CloneBuildExpr::IfE));
                    tasks.push(ExecCloneTask::Expr(else_br));
                    tasks.push(ExecCloneTask::Expr(then_br));
                    tasks.push(ExecCloneTask::Expr(cond));
                }
                ExecExpr::CaseE { scrut, arms } => {
                    tasks.push(ExecCloneTask::BuildExpr(CloneBuildExpr::CaseE(arms)));
                    for a in arms.iter().rev() {
                        tasks.push(ExecCloneTask::Expr(&a.body));
                    }
                    tasks.push(ExecCloneTask::Expr(scrut));
                }
                ExecExpr::App { fn_expr, args } => {
                    tasks.push(ExecCloneTask::BuildExpr(CloneBuildExpr::App(args.len())));
                    for a in args.iter().rev() {
                        tasks.push(ExecCloneTask::Expr(a));
                    }
                    tasks.push(ExecCloneTask::Expr(fn_expr));
                }
                ExecExpr::Call { fn_name, args } => {
                    tasks.push(ExecCloneTask::BuildExpr(CloneBuildExpr::Call(
                        fn_name,
                        args.len(),
                    )));
                    for a in args.iter().rev() {
                        tasks.push(ExecCloneTask::Expr(a));
                    }
                }
                ExecExpr::Join {
                    label,
                    params,
                    rhs,
                    body,
                } => {
                    tasks.push(ExecCloneTask::BuildExpr(CloneBuildExpr::Join(
                        label, params,
                    )));
                    tasks.push(ExecCloneTask::Expr(body));
                    tasks.push(ExecCloneTask::Expr(rhs));
                }
                ExecExpr::Jump { label, args } => {
                    tasks.push(ExecCloneTask::BuildExpr(CloneBuildExpr::Jump(
                        label,
                        args.len(),
                    )));
                    for a in args.iter().rev() {
                        tasks.push(ExecCloneTask::Expr(a));
                    }
                }
                ExecExpr::ForLoop {
                    item_var,
                    iter_expr,
                    state_vars,
                    body,
                    after,
                } => {
                    tasks.push(ExecCloneTask::BuildExpr(CloneBuildExpr::ForLoop(
                        item_var, state_vars,
                    )));
                    tasks.push(ExecCloneTask::Expr(after));
                    tasks.push(ExecCloneTask::Expr(body));
                    tasks.push(ExecCloneTask::Expr(iter_expr));
                }
                ExecExpr::WhileLoop {
                    cond,
                    state_vars,
                    body,
                    after,
                } => {
                    tasks.push(ExecCloneTask::BuildExpr(CloneBuildExpr::WhileLoop(
                        state_vars,
                    )));
                    tasks.push(ExecCloneTask::Expr(after));
                    tasks.push(ExecCloneTask::Expr(body));
                    tasks.push(ExecCloneTask::Expr(cond));
                }
                ExecExpr::Tuple(xs) => {
                    tasks.push(ExecCloneTask::BuildExpr(CloneBuildExpr::Tuple(xs.len())));
                    for x in xs.iter().rev() {
                        tasks.push(ExecCloneTask::Expr(x));
                    }
                }
                ExecExpr::Proj { tup, idx } => {
                    tasks.push(ExecCloneTask::BuildExpr(CloneBuildExpr::Proj(idx)));
                    tasks.push(ExecCloneTask::Expr(tup));
                }
                ExecExpr::Ctor {
                    type_name,
                    ctor_name,
                    args,
                } => {
                    tasks.push(ExecCloneTask::BuildExpr(CloneBuildExpr::Ctor(
                        type_name,
                        ctor_name,
                        args.len(),
                    )));
                    for a in args.iter().rev() {
                        tasks.push(ExecCloneTask::Expr(a));
                    }
                }
                ExecExpr::Prim { op, args } => {
                    tasks.push(ExecCloneTask::BuildExpr(CloneBuildExpr::Prim(
                        op,
                        args.len(),
                    )));
                    for a in args.iter().rev() {
                        tasks.push(ExecCloneTask::Expr(a));
                    }
                }
                ExecExpr::Rel(plan) => {
                    tasks.push(ExecCloneTask::BuildExpr(CloneBuildExpr::Rel));
                    tasks.push(ExecCloneTask::Plan(plan));
                }
                ExecExpr::Host { op, args } => {
                    tasks.push(ExecCloneTask::BuildExpr(CloneBuildExpr::Host(
                        op,
                        args.len(),
                    )));
                    for a in args.iter().rev() {
                        tasks.push(ExecCloneTask::Expr(a));
                    }
                }
                ExecExpr::Assert { cond, message } => {
                    tasks.push(ExecCloneTask::BuildExpr(CloneBuildExpr::Assert(message)));
                    tasks.push(ExecCloneTask::Expr(cond));
                }
                ExecExpr::CheckPromise { ret_var, promise } => match promise {
                    ExecPromise::UniqueCols(cols) => exprs.push(ExecExpr::CheckPromise {
                        ret_var: ret_var.clone(),
                        promise: ExecPromise::UniqueCols(cols.clone()),
                    }),
                    ExecPromise::AllRows(re) => {
                        tasks.push(ExecCloneTask::BuildExpr(CloneBuildExpr::CheckPromiseAll(
                            ret_var,
                        )));
                        tasks.push(ExecCloneTask::Row(re));
                    }
                    ExecPromise::BoolExpr(e) => {
                        tasks.push(ExecCloneTask::BuildExpr(CloneBuildExpr::CheckPromiseBool(
                            ret_var,
                        )));
                        tasks.push(ExecCloneTask::Expr(e));
                    }
                },
                ExecExpr::Stop {
                    kind,
                    detail,
                    detail_tags,
                } => {
                    tasks.push(ExecCloneTask::BuildExpr(CloneBuildExpr::Stop(
                        *kind,
                        detail_tags,
                        detail.is_some(),
                    )));
                    if let Some(d) = detail {
                        tasks.push(ExecCloneTask::Expr(d));
                    }
                }
                ExecExpr::Fail(e) => {
                    tasks.push(ExecCloneTask::BuildExpr(CloneBuildExpr::Fail));
                    tasks.push(ExecCloneTask::Expr(e));
                }
            },
            ExecCloneTask::BuildExpr(op) => match op {
                CloneBuildExpr::LetE(name, lty) => {
                    if let (Some(body), Some(bound)) = (exprs.pop(), exprs.pop()) {
                        exprs.push(ExecExpr::LetE {
                            name: name.clone(),
                            lty: lty.clone(),
                            bound: Box::new(bound),
                            body: Box::new(body),
                        });
                    }
                }
                CloneBuildExpr::IfE => {
                    if let (Some(e), Some(t), Some(c)) = (exprs.pop(), exprs.pop(), exprs.pop()) {
                        exprs.push(ExecExpr::IfE {
                            cond: Box::new(c),
                            then_br: Box::new(t),
                            else_br: Box::new(e),
                        });
                    }
                }
                CloneBuildExpr::CaseE(orig_arms) => {
                    let start = exprs.len().saturating_sub(orig_arms.len());
                    let bodies = exprs.split_off(start);
                    if let Some(scrut) = exprs.pop() {
                        let arms = orig_arms
                            .iter()
                            .zip(bodies)
                            .map(|(a, body)| ExecCaseArm {
                                pattern: a.pattern.clone(),
                                body,
                            })
                            .collect();
                        exprs.push(ExecExpr::CaseE {
                            scrut: Box::new(scrut),
                            arms,
                        });
                    }
                }
                CloneBuildExpr::App(n) => {
                    let start = exprs.len().saturating_sub(n);
                    let args = exprs.split_off(start);
                    if let Some(fn_expr) = exprs.pop() {
                        exprs.push(ExecExpr::App {
                            fn_expr: Box::new(fn_expr),
                            args,
                        });
                    }
                }
                CloneBuildExpr::Call(fn_name, n) => {
                    let start = exprs.len().saturating_sub(n);
                    let args = exprs.split_off(start);
                    exprs.push(ExecExpr::Call {
                        fn_name: fn_name.clone(),
                        args,
                    });
                }
                CloneBuildExpr::Join(label, params) => {
                    if let (Some(body), Some(rhs)) = (exprs.pop(), exprs.pop()) {
                        exprs.push(ExecExpr::Join {
                            label: label.clone(),
                            params: params.to_vec(),
                            rhs: Box::new(rhs),
                            body: Box::new(body),
                        });
                    }
                }
                CloneBuildExpr::Jump(label, n) => {
                    let start = exprs.len().saturating_sub(n);
                    let args = exprs.split_off(start);
                    exprs.push(ExecExpr::Jump {
                        label: label.clone(),
                        args,
                    });
                }
                CloneBuildExpr::ForLoop(item_var, state_vars) => {
                    if let (Some(after), Some(body), Some(iter_expr)) =
                        (exprs.pop(), exprs.pop(), exprs.pop())
                    {
                        exprs.push(ExecExpr::ForLoop {
                            item_var: item_var.clone(),
                            iter_expr: Box::new(iter_expr),
                            state_vars: state_vars.to_vec(),
                            body: Box::new(body),
                            after: Box::new(after),
                        });
                    }
                }
                CloneBuildExpr::WhileLoop(state_vars) => {
                    if let (Some(after), Some(body), Some(cond)) =
                        (exprs.pop(), exprs.pop(), exprs.pop())
                    {
                        exprs.push(ExecExpr::WhileLoop {
                            cond: Box::new(cond),
                            state_vars: state_vars.to_vec(),
                            body: Box::new(body),
                            after: Box::new(after),
                        });
                    }
                }
                CloneBuildExpr::Tuple(n) => {
                    let start = exprs.len().saturating_sub(n);
                    let xs = exprs.split_off(start);
                    exprs.push(ExecExpr::Tuple(xs));
                }
                CloneBuildExpr::Proj(idx) => {
                    if let Some(tup) = exprs.pop() {
                        exprs.push(ExecExpr::Proj {
                            tup: Box::new(tup),
                            idx: idx.clone(),
                        });
                    }
                }
                CloneBuildExpr::Ctor(type_name, ctor_name, n) => {
                    let start = exprs.len().saturating_sub(n);
                    let args = exprs.split_off(start);
                    exprs.push(ExecExpr::Ctor {
                        type_name: type_name.clone(),
                        ctor_name: ctor_name.clone(),
                        args,
                    });
                }
                CloneBuildExpr::Prim(pop, n) => {
                    let start = exprs.len().saturating_sub(n);
                    let args = exprs.split_off(start);
                    exprs.push(ExecExpr::Prim {
                        op: pop.clone(),
                        args,
                    });
                }
                CloneBuildExpr::Rel => {
                    if let Some(p) = plans.pop() {
                        exprs.push(ExecExpr::Rel(Box::new(p)));
                    }
                }
                CloneBuildExpr::Host(hop, n) => {
                    let start = exprs.len().saturating_sub(n);
                    let args = exprs.split_off(start);
                    exprs.push(ExecExpr::Host {
                        op: hop.clone(),
                        args,
                    });
                }
                CloneBuildExpr::Assert(msg) => {
                    if let Some(cond) = exprs.pop() {
                        exprs.push(ExecExpr::Assert {
                            cond: Box::new(cond),
                            message: msg.to_string(),
                        });
                    }
                }
                CloneBuildExpr::CheckPromiseAll(ret_var) => {
                    if let Some(re) = rows.pop() {
                        exprs.push(ExecExpr::CheckPromise {
                            ret_var: ret_var.clone(),
                            promise: ExecPromise::AllRows(Box::new(re)),
                        });
                    }
                }
                CloneBuildExpr::CheckPromiseBool(ret_var) => {
                    if let Some(e) = exprs.pop() {
                        exprs.push(ExecExpr::CheckPromise {
                            ret_var: ret_var.clone(),
                            promise: ExecPromise::BoolExpr(Box::new(e)),
                        });
                    }
                }
                CloneBuildExpr::Stop(kind, detail_tags, has_detail) => {
                    let detail = if has_detail {
                        exprs.pop().map(Box::new)
                    } else {
                        None
                    };
                    exprs.push(ExecExpr::Stop {
                        kind,
                        detail,
                        detail_tags: detail_tags.clone(),
                    });
                }
                CloneBuildExpr::Fail => {
                    if let Some(e) = exprs.pop() {
                        exprs.push(ExecExpr::Fail(Box::new(e)));
                    }
                }
            },
        }
    }
    (exprs, plans, rows)
}

impl Clone for ExecExpr {
    fn clone(&self) -> Self {
        let (mut exprs, _, _) = run_exec_clone(ExecCloneTask::Expr(self));
        exprs.pop().unwrap_or(Self::Lit(Literal::Unit))
    }
}

impl Clone for ExecPlan {
    fn clone(&self) -> Self {
        let (_, mut plans, _) = run_exec_clone(ExecCloneTask::Plan(self));
        plans
            .pop()
            .unwrap_or_else(|| Self::SourceExpr(Box::new(ExecExpr::Lit(Literal::Unit))))
    }
}

impl Clone for ExecRowExpr {
    fn clone(&self) -> Self {
        let (_, _, mut rows) = run_exec_clone(ExecCloneTask::Row(self));
        rows.pop().unwrap_or(Self::Lit(Literal::Unit))
    }
}

// ---------------------------------------------------------------------------
// Iterative Drop for ExecExpr / ExecPlan / ExecRowExpr (O(1) Call Stack)
// ---------------------------------------------------------------------------

enum ExecDropNode {
    Expr(ExecExpr),
    Plan(ExecPlan),
    Row(ExecRowExpr),
}

fn push_exec_row_children(re: &mut ExecRowExpr, stack: &mut Vec<ExecDropNode>) {
    match re {
        ExecRowExpr::Lit(_)
        | ExecRowExpr::Col(_)
        | ExecRowExpr::OuterVar(_)
        | ExecRowExpr::ConstRef(_) => {}
        ExecRowExpr::Prim { args, .. } | ExecRowExpr::CallPure { args, .. } => {
            for a in std::mem::take(args) {
                stack.push(ExecDropNode::Row(a));
            }
        }
        ExecRowExpr::IfE {
            cond,
            then_br,
            else_br,
        } => {
            stack.push(ExecDropNode::Row(std::mem::replace(
                cond.as_mut(),
                ExecRowExpr::Lit(Literal::Unit),
            )));
            stack.push(ExecDropNode::Row(std::mem::replace(
                then_br.as_mut(),
                ExecRowExpr::Lit(Literal::Unit),
            )));
            stack.push(ExecDropNode::Row(std::mem::replace(
                else_br.as_mut(),
                ExecRowExpr::Lit(Literal::Unit),
            )));
        }
        ExecRowExpr::Coalesce {
            opt_expr,
            default_expr,
        } => {
            stack.push(ExecDropNode::Row(std::mem::replace(
                opt_expr.as_mut(),
                ExecRowExpr::Lit(Literal::Unit),
            )));
            stack.push(ExecDropNode::Row(std::mem::replace(
                default_expr.as_mut(),
                ExecRowExpr::Lit(Literal::Unit),
            )));
        }
    }
}

fn push_exec_plan_children(plan: &mut ExecPlan, stack: &mut Vec<ExecDropNode>) {
    let dummy_plan = || ExecPlan::SourceExpr(Box::new(ExecExpr::Lit(Literal::Unit)));
    match plan {
        ExecPlan::SourceExpr(e) | ExecPlan::SourceDB { cap: e, .. } => {
            stack.push(ExecDropNode::Expr(std::mem::replace(
                e.as_mut(),
                ExecExpr::Lit(Literal::Unit),
            )));
        }
        ExecPlan::Select { input, .. }
        | ExecPlan::Drop { input, .. }
        | ExecPlan::Rename { input, .. }
        | ExecPlan::Distinct { input, .. }
        | ExecPlan::Sort { input, .. }
        | ExecPlan::Limit { input, .. }
        | ExecPlan::GroupBy { input, .. }
        | ExecPlan::SuppressSmallGroups { input, .. }
        | ExecPlan::Window { input, .. }
        | ExecPlan::FillGaps { input, .. }
        | ExecPlan::PivotWider { input, .. }
        | ExecPlan::Crosstab { input, .. }
        | ExecPlan::Redact { input, .. } => {
            stack.push(ExecDropNode::Plan(std::mem::replace(
                input.as_mut(),
                dummy_plan(),
            )));
        }
        ExecPlan::Derive { input, items } => {
            stack.push(ExecDropNode::Plan(std::mem::replace(
                input.as_mut(),
                dummy_plan(),
            )));
            for it in std::mem::take(items) {
                if let ExecDeriveItem::ColExpr { mut expr, .. } = it {
                    stack.push(ExecDropNode::Row(std::mem::replace(
                        expr.as_mut(),
                        ExecRowExpr::Lit(Literal::Unit),
                    )));
                }
            }
        }
        ExecPlan::Filter { input, pred } => {
            stack.push(ExecDropNode::Plan(std::mem::replace(
                input.as_mut(),
                dummy_plan(),
            )));
            stack.push(ExecDropNode::Row(std::mem::replace(
                pred,
                ExecRowExpr::Lit(Literal::Unit),
            )));
        }
        ExecPlan::Summarize { input, aggs, .. } => {
            stack.push(ExecDropNode::Plan(std::mem::replace(
                input.as_mut(),
                dummy_plan(),
            )));
            for a in std::mem::take(aggs) {
                if let Some(arg) = a.arg {
                    stack.push(ExecDropNode::Row(arg));
                }
            }
        }
        ExecPlan::Join { left, right, .. } | ExecPlan::Union { left, right } => {
            stack.push(ExecDropNode::Plan(std::mem::replace(
                left.as_mut(),
                dummy_plan(),
            )));
            stack.push(ExecDropNode::Plan(std::mem::replace(
                right.as_mut(),
                dummy_plan(),
            )));
        }
        ExecPlan::Pseudonymize { input, secret, .. } => {
            stack.push(ExecDropNode::Plan(std::mem::replace(
                input.as_mut(),
                dummy_plan(),
            )));
            stack.push(ExecDropNode::Expr(std::mem::replace(
                secret.as_mut(),
                ExecExpr::Lit(Literal::Unit),
            )));
        }
    }
}

fn push_exec_expr_children(expr: &mut ExecExpr, stack: &mut Vec<ExecDropNode>) {
    match expr {
        ExecExpr::Lit(_) | ExecExpr::Var(_) | ExecExpr::ConstRef(_) | ExecExpr::TableLit { .. } => {
        }
        ExecExpr::LetE { bound, body, .. }
        | ExecExpr::Join {
            rhs: bound, body, ..
        } => {
            stack.push(ExecDropNode::Expr(std::mem::replace(
                bound.as_mut(),
                ExecExpr::Lit(Literal::Unit),
            )));
            stack.push(ExecDropNode::Expr(std::mem::replace(
                body.as_mut(),
                ExecExpr::Lit(Literal::Unit),
            )));
        }
        ExecExpr::IfE {
            cond,
            then_br,
            else_br,
        } => {
            stack.push(ExecDropNode::Expr(std::mem::replace(
                cond.as_mut(),
                ExecExpr::Lit(Literal::Unit),
            )));
            stack.push(ExecDropNode::Expr(std::mem::replace(
                then_br.as_mut(),
                ExecExpr::Lit(Literal::Unit),
            )));
            stack.push(ExecDropNode::Expr(std::mem::replace(
                else_br.as_mut(),
                ExecExpr::Lit(Literal::Unit),
            )));
        }
        ExecExpr::CaseE { scrut, arms } => {
            stack.push(ExecDropNode::Expr(std::mem::replace(
                scrut.as_mut(),
                ExecExpr::Lit(Literal::Unit),
            )));
            for a in std::mem::take(arms) {
                stack.push(ExecDropNode::Expr(a.body));
            }
        }
        ExecExpr::Lam { body, .. } => {
            let taken = std::mem::replace(body, Arc::new(ExecExpr::Lit(Literal::Unit)));
            if let Ok(inner) = Arc::try_unwrap(taken) {
                stack.push(ExecDropNode::Expr(inner));
            }
        }
        ExecExpr::App { fn_expr, args } => {
            stack.push(ExecDropNode::Expr(std::mem::replace(
                fn_expr.as_mut(),
                ExecExpr::Lit(Literal::Unit),
            )));
            for a in std::mem::take(args) {
                stack.push(ExecDropNode::Expr(a));
            }
        }
        ExecExpr::Call { args, .. }
        | ExecExpr::Jump { args, .. }
        | ExecExpr::Tuple(args)
        | ExecExpr::Ctor { args, .. }
        | ExecExpr::Prim { args, .. }
        | ExecExpr::Host { args, .. } => {
            for a in std::mem::take(args) {
                stack.push(ExecDropNode::Expr(a));
            }
        }
        ExecExpr::ForLoop {
            iter_expr,
            body,
            after,
            ..
        } => {
            stack.push(ExecDropNode::Expr(std::mem::replace(
                iter_expr.as_mut(),
                ExecExpr::Lit(Literal::Unit),
            )));
            stack.push(ExecDropNode::Expr(std::mem::replace(
                body.as_mut(),
                ExecExpr::Lit(Literal::Unit),
            )));
            stack.push(ExecDropNode::Expr(std::mem::replace(
                after.as_mut(),
                ExecExpr::Lit(Literal::Unit),
            )));
        }
        ExecExpr::WhileLoop {
            cond, body, after, ..
        } => {
            stack.push(ExecDropNode::Expr(std::mem::replace(
                cond.as_mut(),
                ExecExpr::Lit(Literal::Unit),
            )));
            stack.push(ExecDropNode::Expr(std::mem::replace(
                body.as_mut(),
                ExecExpr::Lit(Literal::Unit),
            )));
            stack.push(ExecDropNode::Expr(std::mem::replace(
                after.as_mut(),
                ExecExpr::Lit(Literal::Unit),
            )));
        }
        ExecExpr::Proj { tup: e, .. } | ExecExpr::Assert { cond: e, .. } | ExecExpr::Fail(e) => {
            stack.push(ExecDropNode::Expr(std::mem::replace(
                e.as_mut(),
                ExecExpr::Lit(Literal::Unit),
            )));
        }
        ExecExpr::Rel(plan) => {
            stack.push(ExecDropNode::Plan(std::mem::replace(
                plan.as_mut(),
                ExecPlan::SourceExpr(Box::new(ExecExpr::Lit(Literal::Unit))),
            )));
        }
        ExecExpr::CheckPromise { promise, .. } => match promise {
            ExecPromise::UniqueCols(_) => {}
            ExecPromise::AllRows(re) => {
                stack.push(ExecDropNode::Row(std::mem::replace(
                    re.as_mut(),
                    ExecRowExpr::Lit(Literal::Unit),
                )));
            }
            ExecPromise::BoolExpr(e) => {
                stack.push(ExecDropNode::Expr(std::mem::replace(
                    e.as_mut(),
                    ExecExpr::Lit(Literal::Unit),
                )));
            }
        },
        ExecExpr::Stop { detail, .. } => {
            if let Some(d) = detail.take() {
                stack.push(ExecDropNode::Expr(*d));
            }
        }
    }
}

fn drain_exec_drop(mut stack: Vec<ExecDropNode>) {
    while let Some(mut node) = stack.pop() {
        match &mut node {
            ExecDropNode::Expr(e) => push_exec_expr_children(e, &mut stack),
            ExecDropNode::Plan(p) => push_exec_plan_children(p, &mut stack),
            ExecDropNode::Row(r) => push_exec_row_children(r, &mut stack),
        }
    }
}

impl Drop for ExecExpr {
    fn drop(&mut self) {
        let mut stack = Vec::new();
        push_exec_expr_children(self, &mut stack);
        drain_exec_drop(stack);
    }
}

impl Drop for ExecPlan {
    fn drop(&mut self) {
        let mut stack = Vec::new();
        push_exec_plan_children(self, &mut stack);
        drain_exec_drop(stack);
    }
}

impl Drop for ExecRowExpr {
    fn drop(&mut self) {
        let mut stack = Vec::new();
        push_exec_row_children(self, &mut stack);
        drain_exec_drop(stack);
    }
}

/// Compiled `promise` postcondition attached to a function.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExecPromise {
    UniqueCols(Vec<Ident>),
    AllRows(Box<ExecRowExpr>),
    BoolExpr(Box<ExecExpr>),
}

#[derive(Clone, Debug)]
pub struct ExecFun {
    pub name: Ident,
    pub kind: FunKind,
    pub is_pure: bool,
    pub params: Vec<(Ident, LTy)>,
    pub pc: TagSet,
    pub ret: LTy,
    pub body: ExecExpr,
}

/// Complete lowered Phase 2 executable program.
#[derive(Clone, Debug, Default)]
pub struct ExecProgram {
    pub version: CoreVersion,
    pub tags: Vec<Tag>,
    pub policy: Option<Policy>,
    pub datas: Vec<DataDecl>,
    pub struct_layouts: HashMap<Ident, StructLayout>,
    pub schemas: Vec<CompiledSchema>,
    pub consts: Vec<ConstDecl>,
    pub funs: Vec<ExecFun>,
    pub entry: Option<Ident>,
    pub metadata: CompilerMetadata,
}

impl ExecProgram {
    #[must_use]
    pub fn find_schema(&self, name: &str) -> Option<&CompiledSchema> {
        self.schemas.iter().find(|s| s.decl.name == name)
    }

    #[must_use]
    pub fn find_fun(&self, name: &str) -> Option<&ExecFun> {
        self.funs.iter().find(|f| f.name == name)
    }

    #[must_use]
    pub fn find_const(&self, name: &str) -> Option<&ConstDecl> {
        self.consts.iter().find(|c| c.name == name)
    }

    #[must_use]
    pub fn min_group_floor(&self) -> BigInt {
        let default_floor = BigInt::from(5u64);
        match &self.policy {
            None => default_floor,
            Some(p) => p.min_group_size.clone().max(default_floor),
        }
    }

    /// Extract a pure Core IR v0.1 [`Program`] if every construct in `self` lies within
    /// the Lean-verified Core IR v0.1 subset. Returns `None` if Phase 2 runtime extensions are used.
    #[must_use]
    pub fn try_to_core_program(&self) -> Option<Program> {
        let mut funs = Vec::with_capacity(self.funs.len());
        for f in &self.funs {
            let body = try_exec_expr_to_core(&f.body)?;
            funs.push(FunDecl {
                name: f.name.clone(),
                kind: f.kind,
                is_pure: f.is_pure,
                params: f.params.clone(),
                pc: f.pc.clone(),
                ret: f.ret.clone(),
                body,
            });
        }
        Some(Program {
            version: self.version,
            tags: self.tags.clone(),
            policy: self.policy.clone(),
            datas: self.datas.clone(),
            schemas: self.schemas.iter().map(|s| s.decl.clone()).collect(),
            consts: self.consts.clone(),
            funs,
            entry: self.entry.clone(),
            metadata: self.metadata.clone(),
        })
    }
}

enum ConvTask<'a> {
    Expr(&'a ExecExpr),
    Plan(&'a ExecPlan),
    Row(&'a ExecRowExpr),
    BuildExpr(BuildExprOp<'a>),
    BuildPlan(BuildPlanOp<'a>),
    BuildRow(BuildRowOp<'a>),
}

enum BuildRowOp<'a> {
    Prim(&'a PrimOp, usize),
    IfE,
    Coalesce,
    CallPure(&'a Ident, usize),
}

enum BuildPlanOp<'a> {
    SourceExpr,
    SourceDB(&'a Ident, &'a TableTy),
    Select(&'a [Ident]),
    Drop(&'a [Ident]),
    Rename(&'a [(Ident, Ident)]),
    Derive(&'a [ExecDeriveItem]),
    Filter,
    Distinct(&'a [Ident]),
    Sort(&'a [(Ident, SortDir)]),
    Limit(&'a BigInt),
    Join(JoinKind, &'a JoinOn, &'a Suffixes),
    Union,
    GroupBy(&'a [Ident]),
    Summarize(&'a [ExecAggItem], &'a Option<Ident>),
    SuppressSmallGroups(&'a BigInt, &'a Option<Ident>, SuppressMode),
    Window(&'a [WindowItem]),
    FillGaps(&'a Ident, &'a BigInt, &'a [Ident], &'a [(Ident, Literal)]),
    PivotWider(&'a Ident, &'a Ident, &'a [Ident], &'a Literal),
    Crosstab(&'a Ident, &'a Ident, &'a Ident, &'a Literal),
    Redact(&'a Ident, &'a str),
    Pseudonymize(&'a Ident),
}

enum BuildExprOp<'a> {
    LetE(&'a Ident, &'a LTy),
    IfE,
    CaseE(Vec<(Ident, Vec<Ident>)>),
    Lam(&'a [(Ident, LTy)], &'a TagSet, &'a LTy),
    App(usize),
    Call(&'a Ident, usize),
    Join(&'a Ident, &'a [(Ident, LTy)]),
    Jump(&'a Ident, usize),
    Tuple(usize),
    Proj(&'a BigInt),
    Ctor(&'a Ident, &'a Ident, usize),
    Prim(&'a PrimOp, usize),
    Rel,
    Host(&'a HostOp, usize),
    Stop(BugKind, bool),
    Fail,
}

fn pop_n<T>(v: &mut Vec<T>, n: usize) -> Option<Vec<T>> {
    let start = v.len().checked_sub(n)?;
    Some(v.split_off(start))
}

/// Iterative O(1)-stack conversion from [`ExecExpr`] to Core IR v0.1 [`Expr`].
fn try_exec_expr_to_core(root: &ExecExpr) -> Option<Expr> {
    let mut tasks = vec![ConvTask::Expr(root)];
    let mut exprs: Vec<Expr> = Vec::new();
    let mut plans: Vec<Plan> = Vec::new();
    let mut rows: Vec<RowExpr> = Vec::new();

    while let Some(task) = tasks.pop() {
        match task {
            ConvTask::Row(re) => match re {
                ExecRowExpr::Lit(l) => rows.push(RowExpr::Lit(l.clone())),
                ExecRowExpr::Col(c) => rows.push(RowExpr::Col(c.clone())),
                ExecRowExpr::OuterVar(v) => rows.push(RowExpr::OuterVar(v.clone())),
                ExecRowExpr::ConstRef(c) => rows.push(RowExpr::ConstRef(c.clone())),
                ExecRowExpr::Prim { op, args } => {
                    let ExecPrimOp::Core(cop) = op else {
                        return None;
                    };
                    tasks.push(ConvTask::BuildRow(BuildRowOp::Prim(cop, args.len())));
                    for a in args.iter().rev() {
                        tasks.push(ConvTask::Row(a));
                    }
                }
                ExecRowExpr::IfE {
                    cond,
                    then_br,
                    else_br,
                } => {
                    tasks.push(ConvTask::BuildRow(BuildRowOp::IfE));
                    tasks.push(ConvTask::Row(else_br));
                    tasks.push(ConvTask::Row(then_br));
                    tasks.push(ConvTask::Row(cond));
                }
                ExecRowExpr::Coalesce {
                    opt_expr,
                    default_expr,
                } => {
                    tasks.push(ConvTask::BuildRow(BuildRowOp::Coalesce));
                    tasks.push(ConvTask::Row(default_expr));
                    tasks.push(ConvTask::Row(opt_expr));
                }
                ExecRowExpr::CallPure { fn_name, args } => {
                    tasks.push(ConvTask::BuildRow(BuildRowOp::CallPure(
                        fn_name,
                        args.len(),
                    )));
                    for a in args.iter().rev() {
                        tasks.push(ConvTask::Row(a));
                    }
                }
            },
            ConvTask::BuildRow(op) => match op {
                BuildRowOp::Prim(cop, n) => {
                    let args = pop_n(&mut rows, n)?;
                    rows.push(RowExpr::Prim {
                        op: cop.clone(),
                        args,
                    });
                }
                BuildRowOp::IfE => {
                    let else_br = Box::new(rows.pop()?);
                    let then_br = Box::new(rows.pop()?);
                    let cond = Box::new(rows.pop()?);
                    rows.push(RowExpr::IfE {
                        cond,
                        then_br,
                        else_br,
                    });
                }
                BuildRowOp::Coalesce => {
                    let default_expr = Box::new(rows.pop()?);
                    let opt_expr = Box::new(rows.pop()?);
                    rows.push(RowExpr::Coalesce {
                        opt_expr,
                        default_expr,
                    });
                }
                BuildRowOp::CallPure(fn_name, n) => {
                    let args = pop_n(&mut rows, n)?;
                    rows.push(RowExpr::CallPure {
                        fn_name: fn_name.clone(),
                        args,
                    });
                }
            },
            ConvTask::Plan(plan) => match plan {
                ExecPlan::SourceExpr(e) => {
                    tasks.push(ConvTask::BuildPlan(BuildPlanOp::SourceExpr));
                    tasks.push(ConvTask::Expr(e));
                }
                ExecPlan::SourceDB {
                    cap,
                    table_name,
                    schema,
                } => {
                    tasks.push(ConvTask::BuildPlan(BuildPlanOp::SourceDB(
                        table_name, schema,
                    )));
                    tasks.push(ConvTask::Expr(cap));
                }
                ExecPlan::Select { input, cols } => {
                    tasks.push(ConvTask::BuildPlan(BuildPlanOp::Select(cols)));
                    tasks.push(ConvTask::Plan(input));
                }
                ExecPlan::Drop { input, cols } => {
                    tasks.push(ConvTask::BuildPlan(BuildPlanOp::Drop(cols)));
                    tasks.push(ConvTask::Plan(input));
                }
                ExecPlan::Rename { input, pairs } => {
                    tasks.push(ConvTask::BuildPlan(BuildPlanOp::Rename(pairs)));
                    tasks.push(ConvTask::Plan(input));
                }
                ExecPlan::Derive { input, items } => {
                    tasks.push(ConvTask::BuildPlan(BuildPlanOp::Derive(items)));
                    for it in items.iter().rev() {
                        if let ExecDeriveItem::ColExpr { expr, .. } = it {
                            tasks.push(ConvTask::Row(expr));
                        }
                    }
                    tasks.push(ConvTask::Plan(input));
                }
                ExecPlan::Filter { input, pred } => {
                    tasks.push(ConvTask::BuildPlan(BuildPlanOp::Filter));
                    tasks.push(ConvTask::Row(pred));
                    tasks.push(ConvTask::Plan(input));
                }
                ExecPlan::Distinct { input, cols } => {
                    tasks.push(ConvTask::BuildPlan(BuildPlanOp::Distinct(cols)));
                    tasks.push(ConvTask::Plan(input));
                }
                ExecPlan::Sort { input, keys } => {
                    tasks.push(ConvTask::BuildPlan(BuildPlanOp::Sort(keys)));
                    tasks.push(ConvTask::Plan(input));
                }
                ExecPlan::Limit { input, n } => {
                    tasks.push(ConvTask::BuildPlan(BuildPlanOp::Limit(n)));
                    tasks.push(ConvTask::Plan(input));
                }
                ExecPlan::Join {
                    kind,
                    left,
                    right,
                    on,
                    suffixes,
                } => {
                    tasks.push(ConvTask::BuildPlan(BuildPlanOp::Join(*kind, on, suffixes)));
                    tasks.push(ConvTask::Plan(right));
                    tasks.push(ConvTask::Plan(left));
                }
                ExecPlan::Union { left, right } => {
                    tasks.push(ConvTask::BuildPlan(BuildPlanOp::Union));
                    tasks.push(ConvTask::Plan(right));
                    tasks.push(ConvTask::Plan(left));
                }
                ExecPlan::GroupBy { input, keys } => {
                    tasks.push(ConvTask::BuildPlan(BuildPlanOp::GroupBy(keys)));
                    tasks.push(ConvTask::Plan(input));
                }
                ExecPlan::Summarize {
                    input,
                    aggs,
                    distinct_key,
                } => {
                    tasks.push(ConvTask::BuildPlan(BuildPlanOp::Summarize(
                        aggs,
                        distinct_key,
                    )));
                    for a in aggs.iter().rev() {
                        if let Some(re) = &a.arg {
                            tasks.push(ConvTask::Row(re));
                        }
                    }
                    tasks.push(ConvTask::Plan(input));
                }
                ExecPlan::SuppressSmallGroups {
                    input,
                    min_k,
                    distinct_by,
                    mode,
                } => {
                    tasks.push(ConvTask::BuildPlan(BuildPlanOp::SuppressSmallGroups(
                        min_k,
                        distinct_by,
                        *mode,
                    )));
                    tasks.push(ConvTask::Plan(input));
                }
                ExecPlan::Window { input, items } => {
                    tasks.push(ConvTask::BuildPlan(BuildPlanOp::Window(items)));
                    tasks.push(ConvTask::Plan(input));
                }
                ExecPlan::FillGaps {
                    input,
                    col,
                    step_micros,
                    over,
                    fill,
                } => {
                    tasks.push(ConvTask::BuildPlan(BuildPlanOp::FillGaps(
                        col,
                        step_micros,
                        over,
                        fill,
                    )));
                    tasks.push(ConvTask::Plan(input));
                }
                ExecPlan::PivotWider {
                    input,
                    names_from,
                    values_from,
                    static_cols,
                    fill,
                } => {
                    tasks.push(ConvTask::BuildPlan(BuildPlanOp::PivotWider(
                        names_from,
                        values_from,
                        static_cols,
                        fill,
                    )));
                    tasks.push(ConvTask::Plan(input));
                }
                ExecPlan::Crosstab {
                    input,
                    rows_col,
                    cols_col,
                    values_col,
                    fill,
                } => {
                    tasks.push(ConvTask::BuildPlan(BuildPlanOp::Crosstab(
                        rows_col, cols_col, values_col, fill,
                    )));
                    tasks.push(ConvTask::Plan(input));
                }
                ExecPlan::Redact {
                    input,
                    col,
                    replacement,
                } => {
                    tasks.push(ConvTask::BuildPlan(BuildPlanOp::Redact(col, replacement)));
                    tasks.push(ConvTask::Plan(input));
                }
                ExecPlan::Pseudonymize { input, col, secret } => {
                    tasks.push(ConvTask::BuildPlan(BuildPlanOp::Pseudonymize(col)));
                    tasks.push(ConvTask::Expr(secret));
                    tasks.push(ConvTask::Plan(input));
                }
            },
            ConvTask::BuildPlan(op) => match op {
                BuildPlanOp::SourceExpr => {
                    plans.push(Plan::SourceExpr(Box::new(exprs.pop()?)));
                }
                BuildPlanOp::SourceDB(table_name, schema) => {
                    plans.push(Plan::SourceDB {
                        cap: Box::new(exprs.pop()?),
                        table_name: table_name.clone(),
                        schema: schema.clone(),
                    });
                }
                BuildPlanOp::Select(cols) => {
                    let input = Box::new(plans.pop()?);
                    plans.push(Plan::Select {
                        input,
                        cols: cols.to_vec(),
                    });
                }
                BuildPlanOp::Drop(cols) => {
                    let input = Box::new(plans.pop()?);
                    plans.push(Plan::Drop {
                        input,
                        cols: cols.to_vec(),
                    });
                }
                BuildPlanOp::Rename(pairs) => {
                    let input = Box::new(plans.pop()?);
                    plans.push(Plan::Rename {
                        input,
                        // `ExecPlan::Rename` stores `(old_name, new_name)`, while Core IR
                        // `Plan::Rename` stores `(new_name, old_name)`.
                        pairs: pairs
                            .iter()
                            .map(|(old_n, new_n)| (new_n.clone(), old_n.clone()))
                            .collect(),
                    });
                }
                BuildPlanOp::Derive(items) => {
                    let row_count = items
                        .iter()
                        .filter(|it| matches!(it, ExecDeriveItem::ColExpr { .. }))
                        .count();
                    let mut row_vals = pop_n(&mut rows, row_count)?.into_iter();
                    let input = Box::new(plans.pop()?);
                    let mut citems = Vec::with_capacity(items.len());
                    for item in items {
                        match item {
                            ExecDeriveItem::ColExpr { name, .. } => {
                                citems.push(DeriveItem::ColExpr {
                                    name: name.clone(),
                                    expr: Box::new(row_vals.next()?),
                                })
                            }
                            ExecDeriveItem::BucketCol {
                                name,
                                source,
                                cuts,
                                labels,
                            } => citems.push(DeriveItem::BucketCol {
                                name: name.clone(),
                                source: source.clone(),
                                cuts: cuts.clone(),
                                labels: labels.clone(),
                            }),
                        }
                    }
                    plans.push(Plan::Derive {
                        input,
                        items: citems,
                    });
                }
                BuildPlanOp::Filter => {
                    let pred = rows.pop()?;
                    let input = Box::new(plans.pop()?);
                    plans.push(Plan::Filter { input, pred });
                }
                BuildPlanOp::Distinct(cols) => {
                    let input = Box::new(plans.pop()?);
                    plans.push(Plan::Distinct {
                        input,
                        cols: cols.to_vec(),
                    });
                }
                BuildPlanOp::Sort(keys) => {
                    let input = Box::new(plans.pop()?);
                    plans.push(Plan::Sort {
                        input,
                        keys: keys.to_vec(),
                    });
                }
                BuildPlanOp::Limit(n) => {
                    let input = Box::new(plans.pop()?);
                    plans.push(Plan::Limit {
                        input,
                        n: n.clone(),
                    });
                }
                BuildPlanOp::Join(kind, on, suffixes) => {
                    let right = Box::new(plans.pop()?);
                    let left = Box::new(plans.pop()?);
                    plans.push(Plan::Join {
                        kind,
                        left,
                        right,
                        on: on.clone(),
                        suffixes: suffixes.clone(),
                    });
                }
                BuildPlanOp::Union => {
                    let right = Box::new(plans.pop()?);
                    let left = Box::new(plans.pop()?);
                    plans.push(Plan::Union { left, right });
                }
                BuildPlanOp::GroupBy(keys) => {
                    let input = Box::new(plans.pop()?);
                    plans.push(Plan::GroupBy {
                        input,
                        keys: keys.to_vec(),
                    });
                }
                BuildPlanOp::Summarize(aggs, distinct_key) => {
                    let arg_count = aggs.iter().filter(|a| a.arg.is_some()).count();
                    let mut arg_vals = pop_n(&mut rows, arg_count)?.into_iter();
                    let input = Box::new(plans.pop()?);
                    let mut caggs = Vec::with_capacity(aggs.len());
                    for a in aggs {
                        let arg = if a.arg.is_some() {
                            Some(arg_vals.next()?)
                        } else {
                            None
                        };
                        caggs.push(AggItem {
                            name: a.name.clone(),
                            op: a.op,
                            arg,
                        });
                    }
                    plans.push(Plan::Summarize {
                        input,
                        aggs: caggs,
                        distinct_key: distinct_key.clone(),
                    });
                }
                BuildPlanOp::SuppressSmallGroups(min_k, distinct_by, mode) => {
                    let input = Box::new(plans.pop()?);
                    plans.push(Plan::SuppressSmallGroups {
                        input,
                        min_k: min_k.clone(),
                        distinct_by: distinct_by.clone(),
                        mode,
                    });
                }
                BuildPlanOp::Window(items) => {
                    let input = Box::new(plans.pop()?);
                    plans.push(Plan::Window {
                        input,
                        items: items.to_vec(),
                    });
                }
                BuildPlanOp::FillGaps(col, step_micros, over, fill) => {
                    let input = Box::new(plans.pop()?);
                    plans.push(Plan::FillGaps {
                        input,
                        col: col.clone(),
                        step_micros: step_micros.clone(),
                        over: over.to_vec(),
                        fill: fill.to_vec(),
                    });
                }
                BuildPlanOp::PivotWider(names_from, values_from, static_cols, fill) => {
                    let input = Box::new(plans.pop()?);
                    plans.push(Plan::PivotWider {
                        input,
                        names_from: names_from.clone(),
                        values_from: values_from.clone(),
                        static_cols: static_cols.to_vec(),
                        fill: fill.clone(),
                    });
                }
                BuildPlanOp::Crosstab(rows_col, cols_col, values_col, fill) => {
                    let input = Box::new(plans.pop()?);
                    plans.push(Plan::Crosstab {
                        input,
                        rows_col: rows_col.clone(),
                        cols_col: cols_col.clone(),
                        values_col: values_col.clone(),
                        fill: fill.clone(),
                    });
                }
                BuildPlanOp::Redact(col, replacement) => {
                    let input = Box::new(plans.pop()?);
                    plans.push(Plan::Redact {
                        input,
                        col: col.clone(),
                        replacement: replacement.to_string(),
                    });
                }
                BuildPlanOp::Pseudonymize(col) => {
                    let secret = Box::new(exprs.pop()?);
                    let input = Box::new(plans.pop()?);
                    plans.push(Plan::Pseudonymize {
                        input,
                        col: col.clone(),
                        secret,
                    });
                }
            },
            ConvTask::Expr(expr) => match expr {
                ExecExpr::Lit(l) => exprs.push(Expr::Lit(l.clone())),
                ExecExpr::Var(v) => exprs.push(Expr::Var(v.clone())),
                ExecExpr::ConstRef(c) => exprs.push(Expr::ConstRef(c.clone())),
                ExecExpr::TableLit { schema, rows: rs } => exprs.push(Expr::TableLit {
                    schema: schema.clone(),
                    rows: rs.clone(),
                }),
                ExecExpr::LetE {
                    name,
                    lty,
                    bound,
                    body,
                } => {
                    tasks.push(ConvTask::BuildExpr(BuildExprOp::LetE(name, lty)));
                    tasks.push(ConvTask::Expr(body));
                    tasks.push(ConvTask::Expr(bound));
                }
                ExecExpr::IfE {
                    cond,
                    then_br,
                    else_br,
                } => {
                    tasks.push(ConvTask::BuildExpr(BuildExprOp::IfE));
                    tasks.push(ConvTask::Expr(else_br));
                    tasks.push(ConvTask::Expr(then_br));
                    tasks.push(ConvTask::Expr(cond));
                }
                ExecExpr::CaseE { scrut, arms } => {
                    let mut arm_meta = Vec::with_capacity(arms.len());
                    for a in arms {
                        let pair = match &a.pattern {
                            ExecPattern::Ctor { ctor, binders } => (ctor.clone(), binders.clone()),
                            ExecPattern::Wildcard => ("_".to_string(), Vec::new()),
                            _ => return None,
                        };
                        arm_meta.push(pair);
                    }
                    tasks.push(ConvTask::BuildExpr(BuildExprOp::CaseE(arm_meta)));
                    for a in arms.iter().rev() {
                        tasks.push(ConvTask::Expr(&a.body));
                    }
                    tasks.push(ConvTask::Expr(scrut));
                }
                ExecExpr::Lam {
                    params,
                    pc,
                    ret,
                    body,
                } => {
                    tasks.push(ConvTask::BuildExpr(BuildExprOp::Lam(params, pc, ret)));
                    tasks.push(ConvTask::Expr(body));
                }
                ExecExpr::App { fn_expr, args } => {
                    tasks.push(ConvTask::BuildExpr(BuildExprOp::App(args.len())));
                    for a in args.iter().rev() {
                        tasks.push(ConvTask::Expr(a));
                    }
                    tasks.push(ConvTask::Expr(fn_expr));
                }
                ExecExpr::Call { fn_name, args } => {
                    tasks.push(ConvTask::BuildExpr(BuildExprOp::Call(fn_name, args.len())));
                    for a in args.iter().rev() {
                        tasks.push(ConvTask::Expr(a));
                    }
                }
                ExecExpr::Join {
                    label,
                    params,
                    rhs,
                    body,
                } => {
                    tasks.push(ConvTask::BuildExpr(BuildExprOp::Join(label, params)));
                    tasks.push(ConvTask::Expr(body));
                    tasks.push(ConvTask::Expr(rhs));
                }
                ExecExpr::Jump { label, args } => {
                    tasks.push(ConvTask::BuildExpr(BuildExprOp::Jump(label, args.len())));
                    for a in args.iter().rev() {
                        tasks.push(ConvTask::Expr(a));
                    }
                }
                ExecExpr::Tuple(xs) => {
                    tasks.push(ConvTask::BuildExpr(BuildExprOp::Tuple(xs.len())));
                    for x in xs.iter().rev() {
                        tasks.push(ConvTask::Expr(x));
                    }
                }
                ExecExpr::Proj { tup, idx } => {
                    tasks.push(ConvTask::BuildExpr(BuildExprOp::Proj(idx)));
                    tasks.push(ConvTask::Expr(tup));
                }
                ExecExpr::Ctor {
                    type_name,
                    ctor_name,
                    args,
                } => {
                    tasks.push(ConvTask::BuildExpr(BuildExprOp::Ctor(
                        type_name,
                        ctor_name,
                        args.len(),
                    )));
                    for a in args.iter().rev() {
                        tasks.push(ConvTask::Expr(a));
                    }
                }
                ExecExpr::Prim { op, args } => {
                    let ExecPrimOp::Core(cop) = op else {
                        return None;
                    };
                    tasks.push(ConvTask::BuildExpr(BuildExprOp::Prim(cop, args.len())));
                    for a in args.iter().rev() {
                        tasks.push(ConvTask::Expr(a));
                    }
                }
                ExecExpr::Rel(plan) => {
                    tasks.push(ConvTask::BuildExpr(BuildExprOp::Rel));
                    tasks.push(ConvTask::Plan(plan));
                }
                ExecExpr::Host { op, args } => {
                    let ExecHostOp::Core(cop) = op else {
                        return None;
                    };
                    tasks.push(ConvTask::BuildExpr(BuildExprOp::Host(cop, args.len())));
                    for a in args.iter().rev() {
                        tasks.push(ConvTask::Expr(a));
                    }
                }
                ExecExpr::Stop { kind, detail, .. } => {
                    tasks.push(ConvTask::BuildExpr(BuildExprOp::Stop(
                        *kind,
                        detail.is_some(),
                    )));
                    if let Some(d) = detail {
                        tasks.push(ConvTask::Expr(d));
                    }
                }
                ExecExpr::Fail(e) => {
                    tasks.push(ConvTask::BuildExpr(BuildExprOp::Fail));
                    tasks.push(ConvTask::Expr(e));
                }
                ExecExpr::ForLoop { .. }
                | ExecExpr::WhileLoop { .. }
                | ExecExpr::Assert { .. }
                | ExecExpr::CheckPromise { .. } => return None,
            },
            ConvTask::BuildExpr(op) => match op {
                BuildExprOp::LetE(name, lty) => {
                    let body = Box::new(exprs.pop()?);
                    let bound = Box::new(exprs.pop()?);
                    exprs.push(Expr::LetE {
                        name: name.clone(),
                        lty: lty.clone(),
                        bound,
                        body,
                    });
                }
                BuildExprOp::IfE => {
                    let else_br = Box::new(exprs.pop()?);
                    let then_br = Box::new(exprs.pop()?);
                    let cond = Box::new(exprs.pop()?);
                    exprs.push(Expr::IfE {
                        cond,
                        then_br,
                        else_br,
                    });
                }
                BuildExprOp::CaseE(meta) => {
                    let bodies = pop_n(&mut exprs, meta.len())?;
                    let scrut = Box::new(exprs.pop()?);
                    let arms = meta
                        .into_iter()
                        .zip(bodies)
                        .map(|((ctor, binders), body)| CaseArm {
                            ctor,
                            binders,
                            body,
                        })
                        .collect();
                    exprs.push(Expr::CaseE { scrut, arms });
                }
                BuildExprOp::Lam(params, pc, ret) => {
                    let body = Arc::new(exprs.pop()?);
                    exprs.push(Expr::Lam {
                        params: params.to_vec(),
                        pc: pc.clone(),
                        ret: ret.clone(),
                        body,
                    });
                }
                BuildExprOp::App(n) => {
                    let args = pop_n(&mut exprs, n)?;
                    let fn_expr = Box::new(exprs.pop()?);
                    exprs.push(Expr::App { fn_expr, args });
                }
                BuildExprOp::Call(fn_name, n) => {
                    let args = pop_n(&mut exprs, n)?;
                    exprs.push(Expr::Call {
                        fn_name: fn_name.clone(),
                        args,
                    });
                }
                BuildExprOp::Join(label, params) => {
                    let body = Box::new(exprs.pop()?);
                    let rhs = Box::new(exprs.pop()?);
                    exprs.push(Expr::Join {
                        label: label.clone(),
                        params: params.to_vec(),
                        rhs,
                        body,
                    });
                }
                BuildExprOp::Jump(label, n) => {
                    let args = pop_n(&mut exprs, n)?;
                    exprs.push(Expr::Jump {
                        label: label.clone(),
                        args,
                    });
                }
                BuildExprOp::Tuple(n) => {
                    let xs = pop_n(&mut exprs, n)?;
                    exprs.push(Expr::Tuple(xs));
                }
                BuildExprOp::Proj(idx) => {
                    let tup = Box::new(exprs.pop()?);
                    exprs.push(Expr::Proj {
                        tup,
                        idx: idx.clone(),
                    });
                }
                BuildExprOp::Ctor(type_name, ctor_name, n) => {
                    let args = pop_n(&mut exprs, n)?;
                    exprs.push(Expr::Ctor {
                        type_name: type_name.clone(),
                        ctor_name: ctor_name.clone(),
                        args,
                    });
                }
                BuildExprOp::Prim(cop, n) => {
                    let args = pop_n(&mut exprs, n)?;
                    exprs.push(Expr::Prim {
                        op: cop.clone(),
                        args,
                    });
                }
                BuildExprOp::Rel => {
                    exprs.push(Expr::Rel(Box::new(plans.pop()?)));
                }
                BuildExprOp::Host(cop, n) => {
                    let args = pop_n(&mut exprs, n)?;
                    exprs.push(Expr::Host {
                        op: cop.clone(),
                        args,
                    });
                }
                BuildExprOp::Stop(kind, has_detail) => {
                    let detail = if has_detail {
                        Some(Box::new(exprs.pop()?))
                    } else {
                        None
                    };
                    exprs.push(Expr::Stop { kind, detail });
                }
                BuildExprOp::Fail => {
                    let inner = Box::new(exprs.pop()?);
                    exprs.push(Expr::Fail(inner));
                }
            },
        }
    }
    exprs.pop()
}
