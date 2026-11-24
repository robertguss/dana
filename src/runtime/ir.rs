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
#[derive(Clone, Debug, PartialEq, Eq)]
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

#[derive(Clone, Debug, PartialEq, Eq)]
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

#[derive(Clone, Debug, PartialEq, Eq)]
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

fn try_exec_row_to_core(re: &ExecRowExpr) -> Option<RowExpr> {
    match re {
        ExecRowExpr::Lit(l) => Some(RowExpr::Lit(l.clone())),
        ExecRowExpr::Col(c) => Some(RowExpr::Col(c.clone())),
        ExecRowExpr::OuterVar(v) => Some(RowExpr::OuterVar(v.clone())),
        ExecRowExpr::ConstRef(c) => Some(RowExpr::ConstRef(c.clone())),
        ExecRowExpr::Prim { op, args } => {
            let ExecPrimOp::Core(cop) = op else {
                return None;
            };
            let mut cargs = Vec::with_capacity(args.len());
            for a in args {
                cargs.push(try_exec_row_to_core(a)?);
            }
            Some(RowExpr::Prim {
                op: cop.clone(),
                args: cargs,
            })
        }
        ExecRowExpr::IfE {
            cond,
            then_br,
            else_br,
        } => Some(RowExpr::IfE {
            cond: Box::new(try_exec_row_to_core(cond)?),
            then_br: Box::new(try_exec_row_to_core(then_br)?),
            else_br: Box::new(try_exec_row_to_core(else_br)?),
        }),
        ExecRowExpr::Coalesce {
            opt_expr,
            default_expr,
        } => Some(RowExpr::Coalesce {
            opt_expr: Box::new(try_exec_row_to_core(opt_expr)?),
            default_expr: Box::new(try_exec_row_to_core(default_expr)?),
        }),
        ExecRowExpr::CallPure { fn_name, args } => {
            let mut cargs = Vec::with_capacity(args.len());
            for a in args {
                cargs.push(try_exec_row_to_core(a)?);
            }
            Some(RowExpr::CallPure {
                fn_name: fn_name.clone(),
                args: cargs,
            })
        }
    }
}

fn try_exec_plan_to_core(plan: &ExecPlan) -> Option<Plan> {
    match plan {
        ExecPlan::SourceExpr(e) => Some(Plan::SourceExpr(Box::new(try_exec_expr_to_core(e)?))),
        ExecPlan::SourceDB {
            cap,
            table_name,
            schema,
        } => Some(Plan::SourceDB {
            cap: Box::new(try_exec_expr_to_core(cap)?),
            table_name: table_name.clone(),
            schema: schema.clone(),
        }),
        ExecPlan::Select { input, cols } => Some(Plan::Select {
            input: Box::new(try_exec_plan_to_core(input)?),
            cols: cols.clone(),
        }),
        ExecPlan::Drop { input, cols } => Some(Plan::Drop {
            input: Box::new(try_exec_plan_to_core(input)?),
            cols: cols.clone(),
        }),
        ExecPlan::Rename { input, pairs } => Some(Plan::Rename {
            input: Box::new(try_exec_plan_to_core(input)?),
            pairs: pairs.clone(),
        }),
        ExecPlan::Derive { input, items } => {
            let mut citems = Vec::with_capacity(items.len());
            for item in items {
                match item {
                    ExecDeriveItem::ColExpr { name, expr } => citems.push(DeriveItem::ColExpr {
                        name: name.clone(),
                        expr: Box::new(try_exec_row_to_core(expr)?),
                    }),
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
            Some(Plan::Derive {
                input: Box::new(try_exec_plan_to_core(input)?),
                items: citems,
            })
        }
        ExecPlan::Filter { input, pred } => Some(Plan::Filter {
            input: Box::new(try_exec_plan_to_core(input)?),
            pred: try_exec_row_to_core(pred)?,
        }),
        ExecPlan::Distinct { input, cols } => Some(Plan::Distinct {
            input: Box::new(try_exec_plan_to_core(input)?),
            cols: cols.clone(),
        }),
        ExecPlan::Sort { input, keys } => Some(Plan::Sort {
            input: Box::new(try_exec_plan_to_core(input)?),
            keys: keys.clone(),
        }),
        ExecPlan::Limit { input, n } => Some(Plan::Limit {
            input: Box::new(try_exec_plan_to_core(input)?),
            n: n.clone(),
        }),
        ExecPlan::Join {
            kind,
            left,
            right,
            on,
            suffixes,
        } => Some(Plan::Join {
            kind: *kind,
            left: Box::new(try_exec_plan_to_core(left)?),
            right: Box::new(try_exec_plan_to_core(right)?),
            on: on.clone(),
            suffixes: suffixes.clone(),
        }),
        ExecPlan::Union { left, right } => Some(Plan::Union {
            left: Box::new(try_exec_plan_to_core(left)?),
            right: Box::new(try_exec_plan_to_core(right)?),
        }),
        ExecPlan::GroupBy { input, keys } => Some(Plan::GroupBy {
            input: Box::new(try_exec_plan_to_core(input)?),
            keys: keys.clone(),
        }),
        ExecPlan::Summarize {
            input,
            aggs,
            distinct_key,
        } => {
            let mut caggs = Vec::with_capacity(aggs.len());
            for a in aggs {
                let arg = match &a.arg {
                    Some(re) => Some(try_exec_row_to_core(re)?),
                    None => None,
                };
                caggs.push(AggItem {
                    name: a.name.clone(),
                    op: a.op,
                    arg,
                });
            }
            Some(Plan::Summarize {
                input: Box::new(try_exec_plan_to_core(input)?),
                aggs: caggs,
                distinct_key: distinct_key.clone(),
            })
        }
        ExecPlan::SuppressSmallGroups {
            input,
            min_k,
            distinct_by,
            mode,
        } => Some(Plan::SuppressSmallGroups {
            input: Box::new(try_exec_plan_to_core(input)?),
            min_k: min_k.clone(),
            distinct_by: distinct_by.clone(),
            mode: *mode,
        }),
        ExecPlan::Window { input, items } => Some(Plan::Window {
            input: Box::new(try_exec_plan_to_core(input)?),
            items: items.clone(),
        }),
        ExecPlan::FillGaps {
            input,
            col,
            step_micros,
            over,
            fill,
        } => Some(Plan::FillGaps {
            input: Box::new(try_exec_plan_to_core(input)?),
            col: col.clone(),
            step_micros: step_micros.clone(),
            over: over.clone(),
            fill: fill.clone(),
        }),
        ExecPlan::PivotWider {
            input,
            names_from,
            values_from,
            static_cols,
            fill,
        } => Some(Plan::PivotWider {
            input: Box::new(try_exec_plan_to_core(input)?),
            names_from: names_from.clone(),
            values_from: values_from.clone(),
            static_cols: static_cols.clone(),
            fill: fill.clone(),
        }),
        ExecPlan::Crosstab {
            input,
            rows_col,
            cols_col,
            values_col,
            fill,
        } => Some(Plan::Crosstab {
            input: Box::new(try_exec_plan_to_core(input)?),
            rows_col: rows_col.clone(),
            cols_col: cols_col.clone(),
            values_col: values_col.clone(),
            fill: fill.clone(),
        }),
        ExecPlan::Redact {
            input,
            col,
            replacement,
        } => Some(Plan::Redact {
            input: Box::new(try_exec_plan_to_core(input)?),
            col: col.clone(),
            replacement: replacement.clone(),
        }),
        ExecPlan::Pseudonymize { input, col, secret } => Some(Plan::Pseudonymize {
            input: Box::new(try_exec_plan_to_core(input)?),
            col: col.clone(),
            secret: Box::new(try_exec_expr_to_core(secret)?),
        }),
    }
}

fn try_exec_expr_to_core(expr: &ExecExpr) -> Option<Expr> {
    match expr {
        ExecExpr::Lit(l) => Some(Expr::Lit(l.clone())),
        ExecExpr::Var(v) => Some(Expr::Var(v.clone())),
        ExecExpr::ConstRef(c) => Some(Expr::ConstRef(c.clone())),
        ExecExpr::LetE {
            name,
            lty,
            bound,
            body,
        } => Some(Expr::LetE {
            name: name.clone(),
            lty: lty.clone(),
            bound: Box::new(try_exec_expr_to_core(bound)?),
            body: Box::new(try_exec_expr_to_core(body)?),
        }),
        ExecExpr::IfE {
            cond,
            then_br,
            else_br,
        } => Some(Expr::IfE {
            cond: Box::new(try_exec_expr_to_core(cond)?),
            then_br: Box::new(try_exec_expr_to_core(then_br)?),
            else_br: Box::new(try_exec_expr_to_core(else_br)?),
        }),
        ExecExpr::CaseE { scrut, arms } => {
            let mut carms = Vec::with_capacity(arms.len());
            for a in arms {
                let (ctor, binders) = match &a.pattern {
                    ExecPattern::Ctor { ctor, binders } => (ctor.clone(), binders.clone()),
                    ExecPattern::Wildcard => ("_".to_string(), Vec::new()),
                    _ => return None,
                };
                carms.push(CaseArm {
                    ctor,
                    binders,
                    body: try_exec_expr_to_core(&a.body)?,
                });
            }
            Some(Expr::CaseE {
                scrut: Box::new(try_exec_expr_to_core(scrut)?),
                arms: carms,
            })
        }
        ExecExpr::Lam {
            params,
            pc,
            ret,
            body,
        } => Some(Expr::Lam {
            params: params.clone(),
            pc: pc.clone(),
            ret: ret.clone(),
            body: Arc::new(try_exec_expr_to_core(body)?),
        }),
        ExecExpr::App { fn_expr, args } => {
            let mut cargs = Vec::with_capacity(args.len());
            for a in args {
                cargs.push(try_exec_expr_to_core(a)?);
            }
            Some(Expr::App {
                fn_expr: Box::new(try_exec_expr_to_core(fn_expr)?),
                args: cargs,
            })
        }
        ExecExpr::Call { fn_name, args } => {
            let mut cargs = Vec::with_capacity(args.len());
            for a in args {
                cargs.push(try_exec_expr_to_core(a)?);
            }
            Some(Expr::Call {
                fn_name: fn_name.clone(),
                args: cargs,
            })
        }
        ExecExpr::Join {
            label,
            params,
            rhs,
            body,
        } => Some(Expr::Join {
            label: label.clone(),
            params: params.clone(),
            rhs: Box::new(try_exec_expr_to_core(rhs)?),
            body: Box::new(try_exec_expr_to_core(body)?),
        }),
        ExecExpr::Jump { label, args } => {
            let mut cargs = Vec::with_capacity(args.len());
            for a in args {
                cargs.push(try_exec_expr_to_core(a)?);
            }
            Some(Expr::Jump {
                label: label.clone(),
                args: cargs,
            })
        }
        ExecExpr::Tuple(xs) => {
            let mut cxs = Vec::with_capacity(xs.len());
            for x in xs {
                cxs.push(try_exec_expr_to_core(x)?);
            }
            Some(Expr::Tuple(cxs))
        }
        ExecExpr::Proj { tup, idx } => Some(Expr::Proj {
            tup: Box::new(try_exec_expr_to_core(tup)?),
            idx: idx.clone(),
        }),
        ExecExpr::Ctor {
            type_name,
            ctor_name,
            args,
        } => {
            let mut cargs = Vec::with_capacity(args.len());
            for a in args {
                cargs.push(try_exec_expr_to_core(a)?);
            }
            Some(Expr::Ctor {
                type_name: type_name.clone(),
                ctor_name: ctor_name.clone(),
                args: cargs,
            })
        }
        ExecExpr::TableLit { schema, rows } => Some(Expr::TableLit {
            schema: schema.clone(),
            rows: rows.clone(),
        }),
        ExecExpr::Prim { op, args } => {
            let ExecPrimOp::Core(cop) = op else {
                return None;
            };
            let mut cargs = Vec::with_capacity(args.len());
            for a in args {
                cargs.push(try_exec_expr_to_core(a)?);
            }
            Some(Expr::Prim {
                op: cop.clone(),
                args: cargs,
            })
        }
        ExecExpr::Rel(plan) => Some(Expr::Rel(Box::new(try_exec_plan_to_core(plan)?))),
        ExecExpr::Host { op, args } => {
            let ExecHostOp::Core(cop) = op else {
                return None;
            };
            let mut cargs = Vec::with_capacity(args.len());
            for a in args {
                cargs.push(try_exec_expr_to_core(a)?);
            }
            Some(Expr::Host {
                op: cop.clone(),
                args: cargs,
            })
        }
        ExecExpr::Stop { kind, detail, .. } => {
            let cdetail = match detail {
                Some(d) => Some(Box::new(try_exec_expr_to_core(d)?)),
                None => None,
            };
            Some(Expr::Stop {
                kind: *kind,
                detail: cdetail,
            })
        }
        ExecExpr::Fail(e) => Some(Expr::Fail(Box::new(try_exec_expr_to_core(e)?))),
        ExecExpr::ForLoop { .. }
        | ExecExpr::WhileLoop { .. }
        | ExecExpr::Assert { .. }
        | ExecExpr::CheckPromise { .. } => None,
    }
}
