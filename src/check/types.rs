//! Structural `Table(...)` type inference, boundary schema & constraint validation,
//! flow-sensitive sensitivity tag tracking, capability/policy verification, and
//! elaborated IR construction.

use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use crate::base::{DiagCode, Diagnostic, SourceMap, Span};
use crate::check::resolve::{ModuleOrigin, ResolvedProgram, check_tag_declared};
use crate::core::bigint::BigInt;
use crate::core::check::{
    ensure_option_scalar, numeric_core_of_scalar, quarantine_bad_row_table_ty,
};
use crate::core::syntax::*;
use crate::db::schema_lock::{LockedCol, SchemaLockFile};
use crate::formats::time::{
    MICROS_PER_DAY, MICROS_PER_HOUR, MICROS_PER_MINUTE, MICROS_PER_SECOND, parse_decimal_bigint,
    parse_iso_date, parse_iso_timestamp,
};
use crate::runtime::ir::*;
use crate::syntax::ast::{self, BinOp, CallArg, Expr, ExprKind, Stmt, StmtKind, TopItem, UnaryOp};

/// Checked and elaborated Dana program ready for final Core IR lowering & sanity verification.
#[derive(Clone, Debug)]
pub struct CheckedProgram {
    pub root_name: String,
    pub exec: ExecProgram,
    /// Metadata source spans for functions, schemas, and tests.
    pub spans: Vec<(Ident, String, Span)>,
    /// Non-fatal compiler warnings (e.g. unused CSV/JSONL/XLSX quarantine tables).
    pub warnings: Vec<Diagnostic>,
}

/// Check an already-resolved multi-module program.
///
/// # Errors
/// Returns one or more privacy-safe [`Diagnostic`]s on type, schema, privacy, policy, or
/// capability violations.
pub fn check_resolved(
    resolved: &ResolvedProgram,
    sm: &SourceMap,
) -> Result<CheckedProgram, Vec<Diagnostic>> {
    check_resolved_with_lock(resolved, sm, None)
}

/// Check an already-resolved multi-module program, optionally verifying all `ReadDB` and
/// `WriteTable` references offline against a [`SchemaLockFile`].
///
/// # Errors
/// Returns one or more privacy-safe [`Diagnostic`]s on type, schema, privacy, policy, or
/// capability violations.
pub fn check_resolved_with_lock(
    resolved: &ResolvedProgram,
    sm: &SourceMap,
    schema_lock: Option<&SchemaLockFile>,
) -> Result<CheckedProgram, Vec<Diagnostic>> {
    let mut checker = Checker::new(resolved, sm, schema_lock);
    checker.check_all()?;
    Ok(checker.finish())
}

/// Convenience helper: resolve and check a single in-memory parsed module.
///
/// # Errors
/// Returns diagnostics on resolution, type, privacy, or policy errors.
pub fn check_module(
    file_id: crate::base::FileId,
    module: ast::Module,
    policy: Option<Policy>,
    sm: &SourceMap,
) -> Result<CheckedProgram, Vec<Diagnostic>> {
    check_module_with_lock(file_id, module, policy, sm, None)
}

/// Convenience helper: resolve and check a single in-memory parsed module with an optional
/// offline [`SchemaLockFile`].
///
/// # Errors
/// Returns diagnostics on resolution, type, schema-lock drift, privacy, or policy errors.
pub fn check_module_with_lock(
    file_id: crate::base::FileId,
    module: ast::Module,
    policy: Option<Policy>,
    sm: &SourceMap,
    schema_lock: Option<&SchemaLockFile>,
) -> Result<CheckedProgram, Vec<Diagnostic>> {
    let resolved = crate::check::resolve::resolve_module(file_id, module, policy)?;
    check_resolved_with_lock(&resolved, sm, schema_lock)
}

#[derive(Clone, Debug)]
struct FnSig<'a> {
    name: Ident,
    params: Vec<(Ident, LTy)>,
    ret: Option<LTy>,
    is_pure: bool,
    module_idx: usize,
    ast_decl: &'a ast::FnDecl,
}

#[derive(Clone, Debug)]
struct VarBinding {
    lty: LTy,
    mutable: bool,
}

#[derive(Clone, Copy, Debug)]
enum LocalScopeKind {
    Normal,
    Spec,
}

#[derive(Clone, Debug, Default)]
struct FlowState {
    /// Union of sensitivity tags of all values returned via `return`, `or_return`, or `try`
    /// (including `pc` / guard sensitivity tags at each early-return site).
    ret_tags: TagSet,
    /// PC sensitivity raised by early returns (`return`, `or_return`, `try`) so statements
    /// after an enclosing `if`/`case`/loop inherit the guard/branch condition taint.
    ret_exit_pc: TagSet,
    /// PC sensitivity raised by `break` statements inside the innermost active loop.
    break_pc: TagSet,
    /// PC sensitivity raised by `continue` statements inside the innermost active loop.
    continue_pc: TagSet,
}

impl FlowState {
    fn merge_from(&mut self, other: &Self) {
        self.ret_tags = self.ret_tags.union(&other.ret_tags);
        self.ret_exit_pc = self.ret_exit_pc.union(&other.ret_exit_pc);
        self.break_pc = self.break_pc.union(&other.break_pc);
        self.continue_pc = self.continue_pc.union(&other.continue_pc);
    }
}

const MAX_LOOP_FIXPOINT_ITERS: usize = 64;

/// Internal sentinel type names for built-in record-like values represented via `Ty::Data(...)`.
const TY_UPSERT_STATS: &str = "__UpsertStats";
const TY_JSON_RESPONSE: &str = "__JsonResponse";
const TY_IN_MEMORY_FILES: &str = "__InMemoryFiles";
const TY_TABLE_ROW_PREFIX: &str = "__TableRow$";
const TY_UNRESOLVED_LIST_ELEM: &str = "__UnresolvedElem";

struct Checker<'a> {
    resolved: &'a ResolvedProgram,
    sm: &'a SourceMap,
    schema_lock: Option<&'a SchemaLockFile>,
    diags: Vec<Diagnostic>,
    committed_diags: Vec<Diagnostic>,
    schemas: HashMap<Ident, CompiledSchema>,
    schema_order: Vec<Ident>,
    structs: HashMap<Ident, StructLayout>,
    enums: HashMap<Ident, DataDecl>,
    ctor_to_enum: HashMap<Ident, (Ident, usize)>,
    consts: HashMap<Ident, ConstDecl>,
    const_order: Vec<Ident>,
    fn_sigs: HashMap<Ident, FnSig<'a>>,
    fn_order: Vec<Ident>,
    checked_funs: HashMap<Ident, ExecFun>,
    in_progress_fns: HashSet<Ident>,
    table_row_schemas: HashMap<Ident, TableTy>,
    temp_counter: usize,
    spans: Vec<(Ident, String, Span)>,
    flow_stack: Vec<FlowState>,
    loop_state_stack: Vec<Vec<Ident>>,
    current_fn_declared_ret: Option<LTy>,
    warnings: Vec<Diagnostic>,
}

impl<'a> Checker<'a> {
    fn new(
        resolved: &'a ResolvedProgram,
        sm: &'a SourceMap,
        schema_lock: Option<&'a SchemaLockFile>,
    ) -> Self {
        let mut structs = HashMap::new();
        structs.insert(
            TY_UPSERT_STATS.to_string(),
            StructLayout {
                name: TY_UPSERT_STATS.to_string(),
                field_names: vec![
                    "inserted".to_string(),
                    "updated".to_string(),
                    "unchanged".to_string(),
                ],
                field_ltys: vec![
                    LTy::public(Ty::Int),
                    LTy::public(Ty::Int),
                    LTy::public(Ty::Int),
                ],
            },
        );
        Self {
            resolved,
            sm,
            schema_lock,
            diags: Vec::new(),
            committed_diags: Vec::new(),
            schemas: HashMap::new(),
            schema_order: Vec::new(),
            structs,
            enums: HashMap::new(),
            ctor_to_enum: HashMap::new(),
            consts: HashMap::new(),
            const_order: Vec::new(),
            fn_sigs: HashMap::new(),
            fn_order: Vec::new(),
            checked_funs: HashMap::new(),
            in_progress_fns: HashSet::new(),
            table_row_schemas: HashMap::new(),
            temp_counter: 0,
            spans: Vec::new(),
            flow_stack: Vec::new(),
            loop_state_stack: Vec::new(),
            current_fn_declared_ret: None,
            warnings: Vec::new(),
        }
    }

    fn record_flow_ret(&mut self, val_tags: &TagSet, ret_pc: &TagSet) {
        if let Some(f) = self.flow_stack.last_mut() {
            f.ret_tags = f.ret_tags.union(val_tags).union(ret_pc);
            f.ret_exit_pc = f.ret_exit_pc.union(ret_pc);
        }
    }

    fn record_flow_break(&mut self, jmp_pc: &TagSet) {
        if let Some(f) = self.flow_stack.last_mut() {
            f.break_pc = f.break_pc.union(jmp_pc);
        }
    }

    fn record_flow_continue(&mut self, jmp_pc: &TagSet) {
        if let Some(f) = self.flow_stack.last_mut() {
            f.continue_pc = f.continue_pc.union(jmp_pc);
        }
    }

    fn fresh(&mut self, prefix: &str) -> String {
        self.temp_counter += 1;
        format!("__{prefix}_{}", self.temp_counter)
    }

    fn check_all(&mut self) -> Result<(), Vec<Diagnostic>> {
        // 1. Collect enums, structs, schemas across all resolved modules.
        for rm in &self.resolved.modules {
            for item in &rm.module.items {
                if let TopItem::Enum(e) = item {
                    self.register_enum(e);
                }
            }
        }
        for rm in &self.resolved.modules {
            for item in &rm.module.items {
                if let TopItem::Schema(s) = item {
                    self.register_schema_header(s);
                }
            }
        }
        for rm in &self.resolved.modules {
            for item in &rm.module.items {
                if let TopItem::Struct(s) = item {
                    self.register_struct(s);
                }
            }
        }
        // Compile schema `where` constraints now that all schemas/types are known.
        for rm in &self.resolved.modules {
            for item in &rm.module.items {
                if let TopItem::Schema(s) = item {
                    self.compile_schema_constraints(s);
                }
            }
        }
        // 2. Register constants.
        for rm in &self.resolved.modules {
            for item in &rm.module.items {
                if let TopItem::Const(c) = item {
                    self.register_const(c);
                }
            }
        }
        // 3. Register function signatures (checking parameter policy ceilings).
        for (mod_idx, rm) in self.resolved.modules.iter().enumerate() {
            for item in &rm.module.items {
                if let TopItem::Fn(f) = item {
                    self.register_fn_sig(mod_idx, rm.origin, f);
                }
            }
        }
        if !self.diags.is_empty() {
            return Err(std::mem::take(&mut self.diags));
        }

        // 4. Type-check & elaborate all functions (inferring omitted return types on demand).
        let fn_names = self.fn_order.clone();
        for fname in fn_names {
            self.ensure_fn_checked(&fname);
        }

        // 5. Type-check & elaborate top-level `test` blocks from the root module.
        let mut test_idx = 0usize;
        for item in &self.resolved.root().module.items {
            if let TopItem::Test(t) = item {
                test_idx += 1;
                let t_name = format!("__test_{test_idx}_{}", sanitize_ident(&t.name));
                self.spans.push((t_name.clone(), t.name.clone(), t.span));
                self.check_test_decl(&t_name, t);
            }
        }

        self.committed_diags.extend(std::mem::take(&mut self.diags));
        if !self.committed_diags.is_empty() {
            return Err(std::mem::take(&mut self.committed_diags));
        }
        Ok(())
    }

    fn finish(mut self) -> CheckedProgram {
        let mut datas: Vec<DataDecl> = self.enums.into_values().collect();
        for (name, layout) in &self.structs {
            if !name.starts_with("__") {
                datas.push(DataDecl {
                    name: name.clone(),
                    ctors: vec![CtorDecl {
                        name: name.clone(),
                        fields: layout.field_ltys.clone(),
                    }],
                });
            }
        }
        datas.sort_by(|a, b| a.name.cmp(&b.name));

        let schemas: Vec<CompiledSchema> = self
            .schema_order
            .iter()
            .filter_map(|n| self.schemas.get(n).cloned())
            .collect();
        let consts: Vec<ConstDecl> = self
            .const_order
            .iter()
            .filter_map(|n| self.consts.get(n).cloned())
            .collect();

        let mut funs = Vec::with_capacity(self.checked_funs.len());
        for name in &self.fn_order {
            if let Some(f) = self.checked_funs.remove(name) {
                funs.push(f);
            }
        }
        // Append spec functions (`examples`, `test`) in deterministic order.
        let mut extra_funs: Vec<ExecFun> = self.checked_funs.into_values().collect();
        extra_funs.sort_by(|a, b| a.name.cmp(&b.name));
        funs.extend(extra_funs);

        let mut tags: Vec<String> = self.resolved.declared_tags.iter().cloned().collect();
        tags.sort();

        let entry = if funs.iter().any(|f| f.name == "main") {
            Some("main".to_string())
        } else {
            None
        };

        let mut metadata = CompilerMetadata::default();
        for (node_id, orig_name, sp) in &self.spans {
            metadata.entries.push(MetaEntry {
                node_id: node_id.clone(),
                orig_name: Some(orig_name.clone()),
                span: Some(self.sm.to_core_span(*sp)),
            });
        }

        CheckedProgram {
            root_name: self.resolved.root_name.clone(),
            exec: ExecProgram {
                version: CoreVersion::default(),
                tags,
                policy: self.resolved.policy.clone(),
                datas,
                struct_layouts: self.structs,
                schemas,
                consts,
                funs,
                entry,
                metadata,
            },
            spans: self.spans,
            warnings: self.warnings,
        }
    }

    // -----------------------------------------------------------------------
    // Tag & Policy Validation
    // -----------------------------------------------------------------------

    fn resolve_tags(&mut self, tags: &[ast::SpannedName]) -> TagSet {
        let mut out = Vec::with_capacity(tags.len());
        for t in tags {
            if let Some(d) = check_tag_declared(self.resolved, &t.name, t.span) {
                self.diags.push(d);
            } else {
                out.push(t.name.clone());
            }
        }
        TagSet::of_list(out)
    }

    fn check_capability_policy(&mut self, ty: &Ty, span: Span) {
        if let Err(err) =
            crate::core::check::check_cap_against_policy(self.resolved.policy.as_ref(), ty)
        {
            self.diags.push(
                Diagnostic::error(DiagCode::PrivacyError, err.message)
                    .with_primary(span, "capability exceeds `dana.policy` ceiling"),
            );
        }
    }

    // -----------------------------------------------------------------------
    // Type Expression Resolution
    // -----------------------------------------------------------------------

    fn resolve_type(&mut self, te: &ast::TypeExpr) -> Ty {
        let base = match &te.kind {
            ast::TypeKind::Tuple(elems) => {
                let ltys = elems
                    .iter()
                    .map(|e| LTy::public(self.resolve_type(e)))
                    .collect();
                Ty::Tuple(ltys)
            }
            ast::TypeKind::Named { name, args } => self.resolve_named_type(name, args, te.span),
        };
        if te.optional {
            Ty::Option(Box::new(base))
        } else {
            base
        }
    }

    fn resolve_named_type(
        &mut self,
        name: &ast::SpannedName,
        args: &[ast::TypeArg],
        span: Span,
    ) -> Ty {
        match name.name.as_str() {
            "Unit" => Ty::Unit,
            "Bool" => Ty::Bool,
            "Int" => Ty::Int,
            "Decimal" => Ty::Decimal,
            "Float" => Ty::Float,
            "Text" => Ty::Text,
            "Bytes" => Ty::Bytes,
            "Date" => Ty::Date,
            "Timestamp" => Ty::Timestamp,
            "Duration" => Ty::Duration,
            "LinearModel" => Ty::LinearModel,
            "StatTest" => Ty::StatTest,
            "Args" => Ty::Args,
            "Clock" => Ty::Clock,
            "ReadFiles" => Ty::ReadFiles,
            "Option" => {
                if let [ast::TypeArg::Type(inner)] = args {
                    Ty::Option(Box::new(self.resolve_type(inner)))
                } else {
                    self.diags.push(
                        Diagnostic::error(DiagCode::TypeError, "`Option` expects 1 type argument")
                            .with_span(span),
                    );
                    Ty::Unit
                }
            }
            "Result" => {
                if let [ast::TypeArg::Type(ok), ast::TypeArg::Type(err)] = args {
                    Ty::Result {
                        ok_ty: Box::new(self.resolve_type(ok)),
                        err_ty: Box::new(self.resolve_type(err)),
                    }
                } else {
                    self.diags.push(
                        Diagnostic::error(DiagCode::TypeError, "`Result` expects 2 type arguments")
                            .with_span(span),
                    );
                    Ty::Unit
                }
            }
            "List" => {
                if let [ast::TypeArg::Type(elem)] = args {
                    Ty::List(Box::new(LTy::public(self.resolve_type(elem))))
                } else {
                    self.diags.push(
                        Diagnostic::error(DiagCode::TypeError, "`List` expects 1 type argument")
                            .with_span(span),
                    );
                    Ty::Unit
                }
            }
            "Map" => {
                if let [ast::TypeArg::Type(k), ast::TypeArg::Type(v)] = args {
                    Ty::Map {
                        key: Box::new(LTy::public(self.resolve_type(k))),
                        val: Box::new(LTy::public(self.resolve_type(v))),
                    }
                } else {
                    self.diags.push(
                        Diagnostic::error(DiagCode::TypeError, "`Map` expects 2 type arguments")
                            .with_span(span),
                    );
                    Ty::Unit
                }
            }
            "Table" => self.resolve_table_type(args, span),
            "BadRow" => {
                if let [
                    ast::TypeArg::Type(ast::TypeExpr {
                        kind: ast::TypeKind::Named { name: sname, .. },
                        optional: false,
                        ..
                    }),
                ] = args
                    && let Some(cs) = self.schemas.get(&sname.name)
                {
                    Ty::Table(quarantine_bad_row_table_ty(&cs.decl.schema))
                } else {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::SchemaError,
                            "`BadRow(Schema)` requires a declared schema name",
                        )
                        .with_span(span),
                    );
                    Ty::Unit
                }
            }
            "DynamicTable" => Ty::DynamicTable(TagSet::empty()),
            "Chart" => Ty::Chart(TagSet::empty()),
            "Report" => Ty::Report(TagSet::empty()),
            "Profile" => Ty::Profile(TagSet::empty()),
            "Console" => {
                let allows = self.extract_allows_arg(args, span);
                Ty::Console(allows)
            }
            "WriteFiles" => {
                let root = match args.first() {
                    Some(ast::TypeArg::Text { value, .. }) => value.clone(),
                    _ => {
                        self.diags.push(
                            Diagnostic::error(
                                DiagCode::CapabilityError,
                                "`WriteFiles` requires a directory prefix string literal",
                            )
                            .with_span(span),
                        );
                        String::new()
                    }
                };
                let allows = self.extract_allows_arg(&args[1.min(args.len())..], span);
                Ty::WriteFiles { root, allows }
            }
            "ReadDB" => {
                let db = self.extract_cap_ident_arg(args.first(), "ReadDB", span);
                Ty::ReadDB(db)
            }
            "RawReadDB" => {
                let db = self.extract_cap_ident_arg(args.first(), "RawReadDB", span);
                Ty::RawReadDB(db)
            }
            "WriteTable" => {
                let db = self.extract_cap_ident_arg(args.first(), "WriteTable", span);
                let table_name = match args.get(1) {
                    Some(ast::TypeArg::Text { value, .. }) => value.clone(),
                    _ => {
                        self.diags.push(
                            Diagnostic::error(
                                DiagCode::CapabilityError,
                                "`WriteTable` requires `(DbName, \"table_name\", ...)`",
                            )
                            .with_span(span),
                        );
                        String::new()
                    }
                };
                let allows = self.extract_allows_arg(&args[2.min(args.len())..], span);
                let mut resolved_table = table_name;
                let mut dest_cols = Vec::new();
                if let Some(locked_db) = self.schema_lock.and_then(|l| l.find_db(&db)) {
                    match locked_db.resolve_table(&resolved_table) {
                        Ok(tbl) => {
                            resolved_table = tbl.name.clone();
                            dest_cols = tbl.cols.iter().map(LockedCol::to_col_spec).collect();
                        }
                        Err(err) => {
                            self.diags.push(
                                Diagnostic::error(DiagCode::SchemaError, err.to_string())
                                    .with_span(span),
                            );
                        }
                    }
                }
                Ty::WriteTable {
                    db,
                    table_name: resolved_table,
                    dest_cols,
                    dest_row_tags: TagSet::empty(),
                    allows,
                }
            }
            "HttpsAllow" => {
                let host = match args.first() {
                    Some(ast::TypeArg::Text { value, .. }) => value.clone(),
                    _ => {
                        self.diags.push(
                            Diagnostic::error(
                                DiagCode::CapabilityError,
                                "`HttpsAllow` requires a hostname string literal",
                            )
                            .with_span(span),
                        );
                        String::new()
                    }
                };
                let allows = self.extract_allows_arg(&args[1.min(args.len())..], span);
                Ty::HttpsAllow { host, allows }
            }
            "Secret" => {
                let sname = match args.first() {
                    Some(ast::TypeArg::Text { value, .. }) => value.clone(),
                    _ => {
                        self.diags.push(
                            Diagnostic::error(
                                DiagCode::CapabilityError,
                                "`Secret` requires a secret name string literal",
                            )
                            .with_span(span),
                        );
                        String::new()
                    }
                };
                Ty::Secret(sname)
            }
            "Declassify" => {
                let allows = self.extract_allows_arg(args, span);
                Ty::Declassify(allows)
            }
            other => {
                if self.structs.contains_key(other) || self.enums.contains_key(other) {
                    Ty::Data(other.to_string())
                } else if self.schemas.contains_key(other) {
                    // Schema name used directly inside `Table(Schema)` is handled by `resolve_table_type`.
                    Ty::Data(other.to_string())
                } else {
                    self.diags.push(
                        Diagnostic::error(DiagCode::TypeError, format!("unknown type `{other}`"))
                            .with_span(span),
                    );
                    Ty::Unit
                }
            }
        }
    }

    fn resolve_table_type(&mut self, args: &[ast::TypeArg], span: Span) -> Ty {
        // Case 1: `Table(SchemaName)` or `Table(BadRow(SchemaName))`
        if let [ast::TypeArg::Type(inner)] = args
            && !inner.optional
            && let ast::TypeKind::Named { name, args: iargs } = &inner.kind
        {
            if name.name == "BadRow" {
                return self.resolve_named_type(name, iargs, inner.span);
            }
            if let Some(cs) = self.schemas.get(&name.name) {
                return Ty::Table(cs.decl.schema.clone());
            }
            self.diags.push(
                Diagnostic::error(
                    DiagCode::SchemaError,
                    format!("unknown schema `{}` in `Table(...)`", name.name),
                )
                .with_span(name.span),
            );
            return Ty::Table(TableTy::default());
        }

        // Case 2: Structural `Table(col: Ty [tags], ...)`
        let mut cols = Vec::with_capacity(args.len());
        let mut seen = HashSet::new();
        for arg in args {
            match arg {
                ast::TypeArg::NamedType {
                    name,
                    ty,
                    tags,
                    span: aspan,
                } => {
                    if !seen.insert(name.name.clone()) {
                        self.diags.push(
                            Diagnostic::error(
                                DiagCode::SchemaError,
                                format!(
                                    "duplicate column `{}` in structural `Table(...)`",
                                    name.name
                                ),
                            )
                            .with_span(name.span),
                        );
                    }
                    let resolved_ty = self.resolve_type(ty);
                    let Some(scalar_ty) = resolved_ty.to_scalar_ty() else {
                        self.diags.push(
                            Diagnostic::error(
                                DiagCode::TypeError,
                                format!("column `{}` must have a scalar type", name.name),
                            )
                            .with_span(*aspan),
                        );
                        continue;
                    };
                    let col_tags = self.resolve_tags(tags);
                    cols.push(ColSpec {
                        name: name.name.clone(),
                        ty: scalar_ty,
                        tags: col_tags,
                        bucketed: false,
                        agg_kind: AggKind::Raw,
                    });
                }
                _ => {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::TypeError,
                            "structural `Table(...)` requires `column: Type` entries or a single Schema name",
                        )
                        .with_span(span),
                    );
                }
            }
        }
        Ty::Table(TableTy {
            cols,
            row_tags: TagSet::empty(),
            order_tags: TagSet::empty(),
            grouped_by: None,
            summarized: false,
            distinct_by: None,
        })
    }

    fn extract_allows_arg(&mut self, args: &[ast::TypeArg], span: Span) -> TagSet {
        for arg in args {
            match arg {
                ast::TypeArg::NamedTags { name, tags, .. } if name.name == "allows" => {
                    return self.resolve_tags(tags);
                }
                _ => {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::CapabilityError,
                            "expected `allows: [tag1, ...]` capability argument",
                        )
                        .with_span(span),
                    );
                }
            }
        }
        TagSet::empty()
    }

    fn extract_cap_ident_arg(
        &mut self,
        arg: Option<&ast::TypeArg>,
        cap_name: &str,
        span: Span,
    ) -> Ident {
        match arg {
            Some(ast::TypeArg::Type(ast::TypeExpr {
                kind: ast::TypeKind::Named { name, args },
                optional: false,
                ..
            })) if args.is_empty() => name.name.clone(),
            _ => {
                self.diags.push(
                    Diagnostic::error(
                        DiagCode::CapabilityError,
                        format!("`{cap_name}` requires a capitalized database name"),
                    )
                    .with_span(span),
                );
                String::new()
            }
        }
    }

    // -----------------------------------------------------------------------
    // Declaration Registration
    // -----------------------------------------------------------------------

    fn register_enum(&mut self, e: &ast::EnumDecl) {
        let mut ctors = Vec::with_capacity(e.variants.len());
        for (idx, v) in e.variants.iter().enumerate() {
            let mut fields = Vec::with_capacity(v.fields.len());
            for vf in &v.fields {
                match vf {
                    ast::VariantField::Positional { ty, .. } => {
                        fields.push(LTy::public(self.resolve_type(ty)));
                    }
                    ast::VariantField::Named { ty, tags, .. } => {
                        let rty = self.resolve_type(ty);
                        let ts = self.resolve_tags(tags);
                        fields.push(LTy::new(rty, ts));
                    }
                }
            }
            self.ctor_to_enum
                .insert(v.name.name.clone(), (e.name.name.clone(), idx));
            ctors.push(CtorDecl {
                name: v.name.name.clone(),
                fields,
            });
        }
        self.enums.insert(
            e.name.name.clone(),
            DataDecl {
                name: e.name.name.clone(),
                ctors,
            },
        );
    }

    fn register_schema_header(&mut self, s: &ast::SchemaDecl) {
        let row_tags = self.resolve_tags(&s.tags);
        let mut cols = Vec::with_capacity(s.fields.len());
        let mut seen = HashSet::new();
        for f in &s.fields {
            if !seen.insert(f.name.name.clone()) {
                self.diags.push(
                    Diagnostic::error(
                        DiagCode::SchemaError,
                        format!(
                            "duplicate column `{}` in schema `{}`",
                            f.name.name, s.name.name
                        ),
                    )
                    .with_span(f.name.span),
                );
            }
            let rty = self.resolve_type(&f.ty);
            let Some(scalar_ty) = rty.to_scalar_ty() else {
                self.diags.push(
                    Diagnostic::error(
                        DiagCode::SchemaError,
                        format!(
                            "schema column `{}.{}` must have a scalar type",
                            s.name.name, f.name.name
                        ),
                    )
                    .with_span(f.ty.span),
                );
                continue;
            };
            let tags = self.resolve_tags(&f.tags);
            cols.push(ColSpec {
                name: f.name.name.clone(),
                ty: scalar_ty,
                tags,
                bucketed: false,
                agg_kind: AggKind::Raw,
            });
        }
        if cols.is_empty() {
            self.diags.push(
                Diagnostic::error(
                    DiagCode::SchemaError,
                    format!("schema `{}` must declare at least one column", s.name.name),
                )
                .with_span(s.span),
            );
        }
        let decl = SchemaDecl {
            name: s.name.name.clone(),
            schema: TableTy {
                cols,
                row_tags,
                order_tags: TagSet::empty(),
                grouped_by: None,
                summarized: false,
                distinct_by: None,
            },
        };
        self.spans
            .push((s.name.name.clone(), s.name.name.clone(), s.span));
        self.schema_order.push(s.name.name.clone());
        self.schemas.insert(
            s.name.name.clone(),
            CompiledSchema {
                decl,
                constraints: vec![None; s.fields.len()],
            },
        );
    }

    fn compile_schema_constraints(&mut self, s: &ast::SchemaDecl) {
        let Some(existing) = self.schemas.get(&s.name.name).cloned() else {
            return;
        };
        let mut compiled = Vec::with_capacity(s.fields.len());
        let empty_env = HashMap::new();
        for (idx, f) in s.fields.iter().enumerate() {
            if let Some(cond) = &f.constraint {
                let col_spec = existing.decl.schema.cols.get(idx).cloned();
                let Some(cs) = col_spec else {
                    compiled.push(None);
                    continue;
                };
                // Constraints check the non-null inner value when the column is `T?`.
                let inner_ty = match &cs.ty {
                    ScalarTy::Option(inner) => inner.as_ref().clone(),
                    other => other.clone(),
                };
                let self_cols = vec![ColSpec {
                    name: "__self".to_string(),
                    ty: inner_ty,
                    tags: TagSet::empty(),
                    bucketed: false,
                    agg_kind: AggKind::Raw,
                }];
                let (re, re_ty, _) =
                    self.check_row_expr(cond, &self_cols, &empty_env, Some(&Ty::Bool), true);
                if re_ty != Ty::Bool {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::SchemaError,
                            format!(
                                "`where` constraint on `{}.{}` must evaluate to `Bool`",
                                s.name.name, f.name.name
                            ),
                        )
                        .with_span(cond.span),
                    );
                }
                compiled.push(Some(re));
            } else {
                compiled.push(None);
            }
        }
        if let Some(entry) = self.schemas.get_mut(&s.name.name) {
            entry.constraints = compiled;
        }
    }

    fn register_struct(&mut self, s: &ast::StructDecl) {
        let mut field_names = Vec::with_capacity(s.fields.len());
        let mut field_ltys = Vec::with_capacity(s.fields.len());
        let mut seen = HashSet::new();
        for f in &s.fields {
            if !seen.insert(f.name.name.clone()) {
                self.diags.push(
                    Diagnostic::error(
                        DiagCode::TypeError,
                        format!(
                            "duplicate field `{}` in struct `{}`",
                            f.name.name, s.name.name
                        ),
                    )
                    .with_span(f.name.span),
                );
            }
            let rty = self.resolve_type(&f.ty);
            let tags = self.resolve_tags(&f.tags);
            field_names.push(f.name.name.clone());
            field_ltys.push(LTy::new(rty, tags));
        }
        self.structs.insert(
            s.name.name.clone(),
            StructLayout {
                name: s.name.name.clone(),
                field_names,
                field_ltys,
            },
        );
    }

    fn register_const(&mut self, c: &ast::ConstDecl) {
        let expected = c.ty.as_ref().map(|t| self.resolve_type(t));
        let empty_env = HashMap::new();
        let (expr, lty) = self.check_expr(
            &c.value,
            &empty_env,
            expected.as_ref(),
            &TagSet::empty(),
            LocalScopeKind::Normal,
            None,
        );
        let lit = if let Some(l) = expr.into_lit() {
            l
        } else {
            self.diags.push(
                Diagnostic::error(
                    DiagCode::TypeError,
                    format!("`const {}` must be a compile-time literal", c.name.name),
                )
                .with_span(c.value.span),
            );
            Literal::Unit
        };
        self.const_order.push(c.name.name.clone());
        self.consts.insert(
            c.name.name.clone(),
            ConstDecl {
                name: c.name.name.clone(),
                lty,
                value: lit,
            },
        );
    }

    fn register_fn_sig(&mut self, mod_idx: usize, origin: ModuleOrigin, f: &'a ast::FnDecl) {
        if origin == ModuleOrigin::Vendor && f.name.name == "main" {
            self.diags.push(
                Diagnostic::error(
                    DiagCode::CapabilityError,
                    "vendored modules cannot define an entry `main` function",
                )
                .with_span(f.name.span),
            );
        }
        let mut params = Vec::with_capacity(f.params.len());
        let mut is_pure = true;
        for p in &f.params {
            let pty = self.resolve_type(&p.ty);
            self.check_capability_policy(&pty, p.span);
            if is_capability_ty(&pty) {
                is_pure = false;
            }
            let ptags = self.resolve_tags(&p.tags);
            params.push((p.name.name.clone(), LTy::new(pty, ptags)));
        }
        let ret = f.ret_ty.as_ref().map(|r| {
            let rty = self.resolve_type(&r.ty);
            let rtags = self.resolve_tags(&r.tags);
            LTy::new(rty, rtags)
        });
        self.spans
            .push((f.name.name.clone(), f.name.name.clone(), f.span));
        self.fn_order.push(f.name.name.clone());
        self.fn_sigs.insert(
            f.name.name.clone(),
            FnSig {
                name: f.name.name.clone(),
                params,
                ret,
                is_pure,
                module_idx: mod_idx,
                ast_decl: f,
            },
        );
    }

    // -----------------------------------------------------------------------
    // Function, Examples, Promise & Test Checking
    // -----------------------------------------------------------------------

    fn ensure_fn_checked(&mut self, name: &str) -> Option<LTy> {
        if let Some(done) = self.checked_funs.get(name) {
            return Some(done.ret.clone());
        }
        let sig = self.fn_sigs.get(name)?.clone();
        if !self.in_progress_fns.insert(name.to_string()) {
            // Recursive call: return declared return type if present.
            return sig.ret.clone();
        }

        // Isolate this function's diagnostics, flow tracking, and active loop stacks so
        // lazily checking a callee during a caller's loop fixpoint pass never loses diagnostics.
        let outer_diags = std::mem::take(&mut self.diags);
        let outer_flow = std::mem::take(&mut self.flow_stack);
        let outer_loops = std::mem::take(&mut self.loop_state_stack);
        let outer_decl_ret = std::mem::replace(&mut self.current_fn_declared_ret, sig.ret.clone());

        let mut env: HashMap<Ident, VarBinding> = HashMap::new();
        for (pname, plty) in &sig.params {
            env.insert(
                pname.clone(),
                VarBinding {
                    lty: plty.clone(),
                    mutable: false,
                },
            );
        }

        let expected_ret = sig.ret.as_ref().map(|r| r.ty.clone());
        let mut regular_stmts: Vec<&'a Stmt> = Vec::new();
        let mut example_blocks: Vec<(&'a [Stmt], Span)> = Vec::new();
        let mut promise_exprs: Vec<(&'a Expr, Span)> = Vec::new();
        for fs in &sig.ast_decl.body {
            match fs {
                ast::FnStmt::Examples { stmts, span } => {
                    example_blocks.push((stmts.as_slice(), *span));
                }
                ast::FnStmt::Promise { expr, span } => {
                    promise_exprs.push((expr, *span));
                }
                ast::FnStmt::Stmt(st) => regular_stmts.push(st),
            }
        }

        let ret_label = self.fresh("ret");
        self.flow_stack.push(FlowState::default());
        let (mut body_expr, mut inferred_ret) = self.check_stmt_refs_block(
            &regular_stmts,
            &mut env,
            expected_ret.as_ref(),
            &TagSet::empty(),
            LocalScopeKind::Normal,
            Some((&ret_label, expected_ret.as_ref())),
        );
        let fn_flow = self.flow_stack.pop().unwrap_or_default();
        inferred_ret.tags = inferred_ret.tags.union(&fn_flow.ret_tags);

        let final_ret = if let Some(declared) = &sig.ret {
            body_expr = self.coerce_expr(
                body_expr,
                &inferred_ret,
                declared,
                sig.ast_decl.span,
                "function return value",
            );
            // If no runtime `TableCoerce` was needed (columns/types already match), preserve
            // the body's exact Core IR `TableTy` metadata (`summarized`, `agg_kind`, `bucketed`)
            // so `core::check_program` validates pure Core IR v0.1 functions directly.
            if !matches!(
                body_expr,
                ExecExpr::Prim {
                    op: ExecPrimOp::TableCoerce(_),
                    ..
                }
            ) && let (Ty::Table(inf_tt), Ty::Table(decl_tt)) = (&inferred_ret.ty, &declared.ty)
                && inf_tt.row_tags == decl_tt.row_tags
                && inf_tt.cols.len() == decl_tt.cols.len()
                && inf_tt
                    .cols
                    .iter()
                    .zip(&decl_tt.cols)
                    .all(|(a, b)| a.name == b.name && a.tags == b.tags)
                && inferred_ret.tags == declared.tags
            {
                inferred_ret
            } else {
                declared.clone()
            }
        } else {
            inferred_ret
        };

        // Wrap `return` jumps with an outer `Join` target only when the body actually jumps to it.
        let mut wrapped_body = if expr_jumps_to(&body_expr, &ret_label) {
            let ret_param = self.fresh("ret_val");
            ExecExpr::Join {
                label: ret_label,
                params: vec![(ret_param.clone(), final_ret.clone())],
                rhs: Box::new(ExecExpr::Var(ret_param)),
                body: Box::new(body_expr),
            }
        } else {
            body_expr
        };

        // Compile and attach `promise` postconditions around the return value!
        if !promise_exprs.is_empty() {
            let res_var = self.fresh("promise_res");
            let mut checks = ExecExpr::Var(res_var.clone());
            for (pexpr, pspan) in promise_exprs.iter().rev() {
                let compiled_promise =
                    self.check_promise_expr(pexpr, *pspan, &res_var, &final_ret, &env);
                checks = ExecExpr::LetE {
                    name: self.fresh("p_ok"),
                    lty: LTy::public(Ty::Unit),
                    bound: Box::new(ExecExpr::CheckPromise {
                        ret_var: res_var.clone(),
                        promise: compiled_promise,
                    }),
                    body: Box::new(checks),
                };
            }
            wrapped_body = ExecExpr::LetE {
                name: res_var,
                lty: final_ret.clone(),
                bound: Box::new(wrapped_body),
                body: Box::new(checks),
            };
        }

        // Update signature return type so subsequent callers and examples see inferred return type.
        if let Some(s_entry) = self.fn_sigs.get_mut(name) {
            s_entry.ret = Some(final_ret.clone());
        }

        let exec_fn = ExecFun {
            name: sig.name.clone(),
            kind: FunKind::Function,
            is_pure: sig.is_pure,
            params: sig.params.clone(),
            pc: TagSet::empty(),
            ret: final_ret.clone(),
            body: wrapped_body,
        };
        self.checked_funs.insert(sig.name.clone(), exec_fn);
        self.in_progress_fns.remove(name);

        // Validate that top-level `main` only declares capability parameters (front-end check
        // matching Core IR v0.1, run after body checking so body privacy diagnostics still fire).
        if sig.name == "main" {
            for (p_ast, (_, plty)) in sig.ast_decl.params.iter().zip(&sig.params) {
                if !is_capability_ty(&plty.ty) {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::CapabilityError,
                            format!(
                                "entry `main` parameter `{}` must be a capability (e.g. `Args`, `Console`, `ReadFiles`, `WriteFiles`, `ReadDB`, `Clock`)",
                                p_ast.name.name
                            ),
                        )
                        .with_span(p_ast.span),
                    );
                }
            }
        }

        // Commit this function's diagnostics and restore caller context before running examples.
        self.committed_diags.extend(std::mem::take(&mut self.diags));
        self.diags = outer_diags;
        self.flow_stack = outer_flow;
        self.loop_state_stack = outer_loops;
        self.current_fn_declared_ret = outer_decl_ret;

        // Now check inline `examples ... end` blocks (in Spec scope, with the function's final sig visible!).
        for (idx, (ex_stmts, ex_span)) in example_blocks.into_iter().enumerate() {
            let ex_name = format!("__example_{}_{}", sig.name, idx + 1);
            self.spans
                .push((ex_name.clone(), format!("{} (example)", sig.name), ex_span));
            self.check_spec_block(&ex_name, FunKind::ExampleDecl, ex_stmts, true);
        }

        let _ = sig.module_idx;
        Some(final_ret)
    }

    fn check_promise_expr(
        &mut self,
        expr: &Expr,
        span: Span,
        res_var: &str,
        ret_lty: &LTy,
        fn_env: &HashMap<Ident, VarBinding>,
    ) -> ExecPromise {
        // Case 1: `promise unique(.a, .b)` on a `Table` return type.
        if let ExprKind::Call { callee, args } = &expr.kind
            && let ExprKind::Ident(fname) = &callee.kind
        {
            if fname == "unique" {
                let mut cols = Vec::new();
                if let Ty::Table(tt) = &ret_lty.ty {
                    for arg in args {
                        if let CallArg::Positional(ae) = arg
                            && let ExprKind::DotField(m) = &ae.kind
                        {
                            if tt.find_col(&m.name).is_none() {
                                self.diags.push(
                                    Diagnostic::error(
                                        DiagCode::TypeError,
                                        format!(
                                            "unknown column `.{}` in `promise unique(...)`",
                                            m.name
                                        ),
                                    )
                                    .with_span(m.span),
                                );
                            }
                            cols.push(m.name.clone());
                        } else {
                            self.diags.push(
                                Diagnostic::error(
                                    DiagCode::TypeError,
                                    "`promise unique(...)` expects `.column` arguments",
                                )
                                .with_span(arg.span()),
                            );
                        }
                    }
                } else {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::TypeError,
                            "`promise unique(...)` is only valid on functions returning a `Table`",
                        )
                        .with_span(span),
                    );
                }
                return ExecPromise::UniqueCols(cols);
            }
            if fname == "all" {
                if let [CallArg::Positional(pred)] = args.as_slice()
                    && let Ty::Table(tt) = &ret_lty.ty
                {
                    let (re, re_ty, _) =
                        self.check_row_expr(pred, &tt.cols, fn_env, Some(&Ty::Bool), false);
                    if re_ty != Ty::Bool {
                        self.diags.push(
                            Diagnostic::error(
                                DiagCode::TypeError,
                                "`promise all(...)` predicate must return `Bool`",
                            )
                            .with_span(pred.span),
                        );
                    }
                    return ExecPromise::AllRows(Box::new(re));
                }
                self.diags.push(
                    Diagnostic::error(
                        DiagCode::TypeError,
                        "`promise all(pred)` requires 1 boolean row predicate on a `Table` return type",
                    )
                    .with_span(span),
                );
                return ExecPromise::AllRows(Box::new(ExecRowExpr::Lit(Literal::Bool(true))));
            }
        }

        // Case 2: General boolean expression where `.` refers to `res_var`, and `sum(.col)` /
        // `count()` / etc. on a Table return type operate on `res_var`.
        let mut p_env = fn_env.clone();
        p_env.insert(
            "__promise_self".to_string(),
            VarBinding {
                lty: ret_lty.clone(),
                mutable: false,
            },
        );
        let rewritten =
            rewrite_promise_self(expr, "__promise_self", matches!(ret_lty.ty, Ty::Table(_)));
        let (ex, lty) = self.check_expr(
            &rewritten,
            &p_env,
            Some(&Ty::Bool),
            &TagSet::empty(),
            LocalScopeKind::Spec,
            None,
        );
        if lty.ty != Ty::Bool {
            self.diags.push(
                Diagnostic::error(
                    DiagCode::TypeError,
                    "`promise` expression must return `Bool`",
                )
                .with_span(span),
            );
        }
        // Substitute `__promise_self` variable ref -> `res_var`.
        let bound = ExecExpr::LetE {
            name: "__promise_self".to_string(),
            lty: ret_lty.clone(),
            bound: Box::new(ExecExpr::Var(res_var.to_string())),
            body: Box::new(ex),
        };
        ExecPromise::BoolExpr(Box::new(bound))
    }

    fn check_test_decl(&mut self, name: &str, t: &ast::TestDecl) {
        self.check_spec_block(name, FunKind::Test, &t.body, false);
    }

    fn check_spec_block(
        &mut self,
        name: &str,
        kind: FunKind,
        stmts: &[Stmt],
        assert_bare_bool_exprs: bool,
    ) {
        let outer_flow = std::mem::take(&mut self.flow_stack);
        let outer_loops = std::mem::take(&mut self.loop_state_stack);
        let outer_decl_ret = self.current_fn_declared_ret.replace(LTy::public(Ty::Unit));

        let mut env = HashMap::new();
        let ret_label = self.fresh("spec_ret");
        let ret_ctx = Some((ret_label.as_str(), Some(&Ty::Unit)));
        self.flow_stack.push(FlowState::default());
        let (body, _) = self.check_block_inner(
            stmts,
            &mut env,
            Some(&Ty::Unit),
            &TagSet::empty(),
            LocalScopeKind::Spec,
            ret_ctx,
            BlockTail::Value,
            Vec::new(),
            assert_bare_bool_exprs,
            name,
        );
        self.flow_stack.pop();

        self.flow_stack = outer_flow;
        self.loop_state_stack = outer_loops;
        self.current_fn_declared_ret = outer_decl_ret;

        let ret_param = self.fresh("spec_done");
        let wrapped = ExecExpr::Join {
            label: ret_label,
            params: vec![(ret_param, LTy::public(Ty::Unit))],
            rhs: Box::new(ExecExpr::Lit(Literal::Unit)),
            body: Box::new(body),
        };
        self.checked_funs.insert(
            name.to_string(),
            ExecFun {
                name: name.to_string(),
                kind,
                is_pure: false,
                params: Vec::new(),
                pc: TagSet::empty(),
                ret: LTy::public(Ty::Unit),
                body: wrapped,
            },
        );
    }

    // -----------------------------------------------------------------------
    // Block & Statement Checking / Lowering
    // -----------------------------------------------------------------------

    fn check_block(
        &mut self,
        stmts: &[Stmt],
        env: &mut HashMap<Ident, VarBinding>,
        expected_ret: Option<&Ty>,
        pc: &TagSet,
        scope: LocalScopeKind,
        ret_ctx: Option<(&str, Option<&Ty>)>,
    ) -> (ExecExpr, LTy) {
        let refs: Vec<&Stmt> = stmts.iter().collect();
        self.check_stmt_refs_inner(
            &refs,
            env,
            expected_ret,
            pc,
            scope,
            ret_ctx,
            BlockTail::Value,
            Vec::new(),
            false,
            "",
        )
    }

    fn check_stmt_refs_block(
        &mut self,
        stmts: &[&Stmt],
        env: &mut HashMap<Ident, VarBinding>,
        expected_ret: Option<&Ty>,
        pc: &TagSet,
        scope: LocalScopeKind,
        ret_ctx: Option<(&str, Option<&Ty>)>,
    ) -> (ExecExpr, LTy) {
        self.check_stmt_refs_inner(
            stmts,
            env,
            expected_ret,
            pc,
            scope,
            ret_ctx,
            BlockTail::Value,
            Vec::new(),
            false,
            "",
        )
    }

    #[expect(
        clippy::too_many_arguments,
        reason = "block checker threads typing env, flow-sensitive pc, loop/branch tail mode, and spec assertion mode"
    )]
    fn check_block_inner(
        &mut self,
        stmts: &[Stmt],
        env: &mut HashMap<Ident, VarBinding>,
        expected_ret: Option<&Ty>,
        pc: &TagSet,
        scope: LocalScopeKind,
        ret_ctx: Option<(&str, Option<&Ty>)>,
        tail: BlockTail<'_>,
        prefix_steps: Vec<BlockStep>,
        assert_bare_bool_exprs: bool,
        spec_name: &str,
    ) -> (ExecExpr, LTy) {
        let refs: Vec<&Stmt> = stmts.iter().collect();
        self.check_stmt_refs_inner(
            &refs,
            env,
            expected_ret,
            pc,
            scope,
            ret_ctx,
            tail,
            prefix_steps,
            assert_bare_bool_exprs,
            spec_name,
        )
    }

    #[expect(
        clippy::too_many_arguments,
        reason = "zero-clone block checker iterates statement references directly"
    )]
    fn check_stmt_refs_inner(
        &mut self,
        stmts: &[&Stmt],
        env: &mut HashMap<Ident, VarBinding>,
        expected_ret: Option<&Ty>,
        pc: &TagSet,
        scope: LocalScopeKind,
        ret_ctx: Option<(&str, Option<&Ty>)>,
        tail: BlockTail<'_>,
        prefix_steps: Vec<BlockStep>,
        assert_bare_bool_exprs: bool,
        spec_name: &str,
    ) -> (ExecExpr, LTy) {
        let mut steps = prefix_steps;
        let mut cur_pc = pc.clone();
        let mut final_lty = LTy::new(Ty::Unit, cur_pc.clone());
        let mut branch_val_var: Option<Ident> = None;

        if stmts.is_empty() {
            match tail {
                BlockTail::Value => {
                    return (
                        if steps.is_empty() {
                            ExecExpr::Lit(Literal::Unit)
                        } else {
                            self.fold_block_steps(steps)
                        },
                        final_lty,
                    );
                }
                BlockTail::StateTuple(names) => {
                    steps.push(BlockStep::Final(build_var_tuple(names)));
                    return (self.fold_block_steps(steps), final_lty);
                }
                BlockTail::ValueAndState(names) => {
                    steps.push(BlockStep::Final(build_val_and_var_tuple(
                        ExecExpr::Lit(Literal::Unit),
                        names,
                    )));
                    return (self.fold_block_steps(steps), final_lty);
                }
            }
        }

        let last_idx = stmts.len() - 1;
        for (idx, st) in stmts.iter().enumerate() {
            let is_last = idx == last_idx;
            let want_val = is_last && !matches!(tail, BlockTail::StateTuple(_));
            let exp_ty = if want_val {
                expected_ret
            } else if matches!(
                st.kind,
                StmtKind::Expr(Expr {
                    kind: ExprKind::IfBlock { .. } | ExprKind::Case { .. },
                    ..
                })
            ) {
                Some(&Ty::Unit)
            } else {
                None
            };
            match &st.kind {
                StmtKind::Var { name, ty, value } => {
                    let ann = ty.as_ref().map(|t| self.resolve_type(t));
                    let (mut rhs, mut rhs_lty) = self.check_expr_in_block(
                        value,
                        env,
                        ann.as_ref(),
                        &mut cur_pc,
                        scope,
                        ret_ctx,
                        &mut steps,
                    );
                    if let Some(a_ty) = ann {
                        let target = LTy::new(a_ty, rhs_lty.tags.union(&cur_pc));
                        rhs = self.coerce_expr(
                            rhs,
                            &rhs_lty,
                            &target,
                            value.span,
                            "`var` initializer",
                        );
                        rhs_lty = target;
                    }
                    rhs_lty.tags = rhs_lty.tags.union(&cur_pc);
                    env.insert(
                        name.name.clone(),
                        VarBinding {
                            lty: rhs_lty.clone(),
                            mutable: true,
                        },
                    );
                    steps.push(BlockStep::Bind(name.name.clone(), rhs_lty, rhs));
                }
                StmtKind::Assign { lhs, rhs } => {
                    let quarantine_candidate = match &lhs.kind {
                        ExprKind::Tuple(elems) if elems.len() == 2 => match &elems[1].kind {
                            ExprKind::Ident(bad_name) if !bad_name.starts_with('_') => {
                                let was_outer_mut = env.get(bad_name).is_some_and(|b| b.mutable);
                                Some((bad_name.clone(), elems[1].span, was_outer_mut))
                            }
                            _ => None,
                        },
                        _ => None,
                    };
                    self.lower_assign_stmt(lhs, rhs, env, &mut cur_pc, scope, ret_ctx, &mut steps);
                    if let Some((bad_name, bad_span, false)) = quarantine_candidate
                        && let Some(binding) = env.get(&bad_name)
                        && let Ty::Table(tt) = &binding.lty.ty
                        && is_quarantine_bad_row_table(tt)
                        && !stmts_reference_ident(&stmts[idx + 1..], &bad_name)
                    {
                        self.warnings.push(
                            Diagnostic::warning(
                                DiagCode::SchemaError,
                                format!(
                                    "unused quarantine table `{bad_name}`: inspect `{bad_name}.count()`, rename to `_{bad_name}` to ignore, or pass `on_bad_rows: :error` to fail on malformed rows"
                                ),
                            )
                            .with_span(bad_span),
                        );
                    }
                    if want_val
                        && !matches!(expected_ret, Some(Ty::Unit))
                        && let ExprKind::Ident(name) = &lhs.kind
                        && let Some(b) = env.get(name)
                    {
                        final_lty = b.lty.clone();
                        match tail {
                            BlockTail::Value => {
                                steps.push(BlockStep::Final(ExecExpr::Var(name.clone())));
                            }
                            BlockTail::ValueAndState(_) => {
                                let tmp = self.fresh("br_val");
                                steps.push(BlockStep::Bind(
                                    tmp.clone(),
                                    final_lty.clone(),
                                    ExecExpr::Var(name.clone()),
                                ));
                                branch_val_var = Some(tmp);
                            }
                            BlockTail::StateTuple(_) => {}
                        }
                    }
                }
                StmtKind::Assert(cond) => {
                    // Note: stopping under sensitive `cur_pc` is a documented 1-bit termination
                    // channel matching Core IR v0.1 Theorems 2B/2C; message carries no cell data.
                    let (cex, clty) = self.check_expr_in_block(
                        cond,
                        env,
                        Some(&Ty::Bool),
                        &mut cur_pc,
                        scope,
                        ret_ctx,
                        &mut steps,
                    );
                    if clty.ty != Ty::Bool {
                        self.diags.push(
                            Diagnostic::error(
                                DiagCode::TypeError,
                                "`assert` requires a `Bool` expression",
                            )
                            .with_span(cond.span),
                        );
                    }
                    steps.push(BlockStep::Effect(
                        LTy::new(Ty::Unit, cur_pc.clone()),
                        ExecExpr::Assert {
                            cond: Box::new(cex),
                            message: "assertion failed".to_string(),
                        },
                    ));
                }
                StmtKind::Return { value, guard } => {
                    let mut ret_pc = cur_pc.clone();
                    let guard_ex = if let Some(g) = guard {
                        let (gex, glty) = self.check_expr_in_block(
                            g,
                            env,
                            Some(&Ty::Bool),
                            &mut cur_pc,
                            scope,
                            ret_ctx,
                            &mut steps,
                        );
                        if glty.ty != Ty::Bool {
                            self.diags.push(
                                Diagnostic::error(
                                    DiagCode::TypeError,
                                    "`return ... if` guard must be `Bool`",
                                )
                                .with_span(g.span),
                            );
                        }
                        let g_tags = glty.effective_tags();
                        ret_pc = ret_pc.union(&g_tags);
                        // Subsequent statements in this block execute only when the guard is false.
                        cur_pc = cur_pc.union(&g_tags);
                        Some(gex)
                    } else {
                        None
                    };

                    let r_exp = ret_ctx.and_then(|(_, t)| t);
                    let mut val_pc = ret_pc.clone();
                    let (val_ex, mut val_lty) = match value {
                        Some(v) => self.check_expr_in_block(
                            v,
                            env,
                            r_exp,
                            &mut val_pc,
                            scope,
                            ret_ctx,
                            &mut steps,
                        ),
                        None => (
                            ExecExpr::Lit(Literal::Unit),
                            LTy::new(Ty::Unit, ret_pc.clone()),
                        ),
                    };
                    ret_pc = ret_pc.union(&val_pc);
                    val_lty.tags = val_lty.tags.union(&ret_pc);
                    let val_ex = if let Some(decl_ret) = self.current_fn_declared_ret.clone() {
                        self.coerce_expr(val_ex, &val_lty, &decl_ret, st.span, "`return` value")
                    } else if let Some(rt) = r_exp {
                        self.coerce_expr(
                            val_ex,
                            &val_lty,
                            &LTy::new(rt.clone(), val_lty.tags.clone()),
                            st.span,
                            "`return` value",
                        )
                    } else {
                        val_ex
                    };
                    self.record_flow_ret(&val_lty.tags, &ret_pc);

                    let jump = if let Some((lbl, _)) = ret_ctx {
                        ExecExpr::Jump {
                            label: lbl.to_string(),
                            args: vec![val_ex],
                        }
                    } else {
                        self.diags.push(
                            Diagnostic::error(
                                DiagCode::TypeError,
                                "`return` used outside a function",
                            )
                            .with_span(st.span),
                        );
                        val_ex
                    };
                    let eff = wrap_guard_expr(jump, guard_ex);
                    if want_val {
                        final_lty = r_exp.cloned().map_or_else(
                            || val_lty.clone(),
                            |rt| LTy::new(rt, val_lty.tags.clone()),
                        );
                    }
                    steps.push(BlockStep::Effect(LTy::new(Ty::Unit, cur_pc.clone()), eff));
                }
                StmtKind::Break { guard } => {
                    let mut jmp_pc = cur_pc.clone();
                    let guard_ex = self.check_loop_guard(
                        guard.as_ref(),
                        env,
                        &mut cur_pc,
                        &mut jmp_pc,
                        scope,
                        ret_ctx,
                        &mut steps,
                    );
                    self.record_flow_break(&jmp_pc);
                    let jmp = ExecExpr::Jump {
                        label: "__break".to_string(),
                        args: self.capture_active_loop_vars(env),
                    };
                    steps.push(BlockStep::Effect(
                        LTy::new(Ty::Unit, cur_pc.clone()),
                        wrap_guard_expr(jmp, guard_ex),
                    ));
                }
                StmtKind::Continue { guard } => {
                    let mut jmp_pc = cur_pc.clone();
                    let guard_ex = self.check_loop_guard(
                        guard.as_ref(),
                        env,
                        &mut cur_pc,
                        &mut jmp_pc,
                        scope,
                        ret_ctx,
                        &mut steps,
                    );
                    self.record_flow_continue(&jmp_pc);
                    let jmp = ExecExpr::Jump {
                        label: "__continue".to_string(),
                        args: self.capture_active_loop_vars(env),
                    };
                    steps.push(BlockStep::Effect(
                        LTy::new(Ty::Unit, cur_pc.clone()),
                        wrap_guard_expr(jmp, guard_ex),
                    ));
                }
                StmtKind::Stop(opt) => {
                    // Termination under sensitive `cur_pc` matches Core IR v0.1 Theorems 2B/2C;
                    // `detail_tags` ensures any sensitive payload is deterministically redacted.
                    let (detail, detail_tags) = match opt.as_ref() {
                        Some(e) => {
                            let (de, dlty) = self.check_expr_in_block(
                                e,
                                env,
                                None,
                                &mut cur_pc,
                                scope,
                                ret_ctx,
                                &mut steps,
                            );
                            (Some(Box::new(de)), dlty.effective_tags().union(&cur_pc))
                        }
                        None => (None, cur_pc.clone()),
                    };
                    steps.push(BlockStep::Effect(
                        LTy::new(Ty::Unit, cur_pc.clone()),
                        ExecExpr::Stop {
                            kind: BugKind::UserStop,
                            detail,
                            detail_tags,
                        },
                    ));
                }
                StmtKind::For { target, iter, body } => {
                    self.lower_for_stmt(
                        target,
                        iter,
                        body,
                        env,
                        &mut cur_pc,
                        scope,
                        ret_ctx,
                        &mut steps,
                    );
                }
                StmtKind::While { cond, body } => {
                    self.lower_while_stmt(cond, body, env, &mut cur_pc, scope, ret_ctx, &mut steps);
                }
                StmtKind::Expr(e) => {
                    let (ex, mut lty) = self.check_expr_in_block(
                        e,
                        env,
                        exp_ty,
                        &mut cur_pc,
                        scope,
                        ret_ctx,
                        &mut steps,
                    );
                    lty.tags = lty.tags.union(&cur_pc);
                    if assert_bare_bool_exprs && lty.ty == Ty::Bool {
                        steps.push(BlockStep::Effect(
                            LTy::new(Ty::Unit, cur_pc.clone()),
                            ExecExpr::Assert {
                                cond: Box::new(ex),
                                message: format!("example assertion failed in `{spec_name}`"),
                            },
                        ));
                    } else if want_val {
                        match tail {
                            BlockTail::Value => {
                                final_lty = lty;
                                steps.push(BlockStep::Final(ex));
                            }
                            BlockTail::ValueAndState(_) => {
                                if matches!(expected_ret, Some(Ty::Unit)) {
                                    final_lty = LTy::new(Ty::Unit, lty.tags.clone());
                                    steps.push(BlockStep::Effect(lty, ex));
                                } else {
                                    final_lty = lty;
                                    let tmp = self.fresh("br_val");
                                    steps.push(BlockStep::Bind(tmp.clone(), final_lty.clone(), ex));
                                    branch_val_var = Some(tmp);
                                }
                            }
                            BlockTail::StateTuple(_) => steps.push(BlockStep::Effect(lty, ex)),
                        }
                    } else {
                        steps.push(BlockStep::Effect(lty, ex));
                    }
                }
            }
        }

        match tail {
            BlockTail::Value => {}
            BlockTail::StateTuple(names) => {
                steps.push(BlockStep::Final(build_var_tuple(names)));
            }
            BlockTail::ValueAndState(names) => {
                let val_ex =
                    branch_val_var.map_or_else(|| ExecExpr::Lit(Literal::Unit), ExecExpr::Var);
                steps.push(BlockStep::Final(build_val_and_var_tuple(val_ex, names)));
            }
        }

        let folded = self.fold_block_steps(steps);
        (folded, final_lty)
    }

    /// Evaluate an expression inside a statement block, propagating:
    /// 1. Mutable `var` assignments made inside `if ... end` and `case ... end` blocks back into
    ///    `env` and `steps` (value + branch-PC sensitivity tags), and
    /// 2. Any early-exit PC taint (`return`, `or_return`, `try`, `break`, `continue`) into `cur_pc`.
    #[expect(
        clippy::too_many_arguments,
        reason = "block-level expression checker merges branch var mutations and control-flow pc"
    )]
    fn check_expr_in_block(
        &mut self,
        expr: &Expr,
        env: &mut HashMap<Ident, VarBinding>,
        expected: Option<&Ty>,
        cur_pc: &mut TagSet,
        scope: LocalScopeKind,
        ret_ctx: Option<(&str, Option<&Ty>)>,
        steps: &mut Vec<BlockStep>,
    ) -> (ExecExpr, LTy) {
        self.flow_stack.push(FlowState::default());
        let (out_ex, out_lty) = match &expr.kind {
            ExprKind::IfBlock {
                cond,
                then_body,
                else_ifs,
                else_body,
            } => {
                let written =
                    collect_mutated_outer_vars_if(then_body, else_ifs, else_body.as_ref(), env);
                let mut branch_envs = Vec::new();
                let (if_ex, if_lty) = self.check_if_block_with_state(
                    cond,
                    then_body,
                    else_ifs,
                    else_body.as_ref(),
                    env,
                    expected,
                    cur_pc,
                    scope,
                    ret_ctx,
                    &written,
                    &mut branch_envs,
                );
                if written.is_empty() {
                    (if_ex, if_lty)
                } else {
                    merge_branch_mut_vars(env, &written, &branch_envs, &if_lty.tags);
                    let res_tmp = self.fresh("if_res");
                    let mut tup_ltys = Vec::with_capacity(1 + written.len());
                    tup_ltys.push(if_lty.clone());
                    for v in &written {
                        tup_ltys.push(
                            env.get(v)
                                .map_or_else(|| LTy::public(Ty::Unit), |b| b.lty.clone()),
                        );
                    }
                    steps.push(BlockStep::Bind(
                        res_tmp.clone(),
                        LTy::new(Ty::Tuple(tup_ltys), if_lty.tags.clone()),
                        if_ex,
                    ));
                    for (i, v) in written.iter().enumerate() {
                        let vlty = env
                            .get(v)
                            .map_or_else(|| LTy::public(Ty::Unit), |b| b.lty.clone());
                        steps.push(BlockStep::Bind(
                            v.clone(),
                            vlty,
                            ExecExpr::Proj {
                                tup: Box::new(ExecExpr::Var(res_tmp.clone())),
                                idx: BigInt::from(i + 1),
                            },
                        ));
                    }
                    (
                        ExecExpr::Proj {
                            tup: Box::new(ExecExpr::Var(res_tmp)),
                            idx: BigInt::ZERO,
                        },
                        if_lty,
                    )
                }
            }
            ExprKind::Case { scrut, lines } => {
                let written = collect_mutated_outer_vars_case(lines, env);
                let mut arm_envs = Vec::new();
                let (case_ex, case_lty) = self.check_case_with_state(
                    scrut,
                    lines,
                    expr.span,
                    env,
                    expected,
                    cur_pc,
                    scope,
                    ret_ctx,
                    &written,
                    &mut arm_envs,
                );
                if written.is_empty() {
                    (case_ex, case_lty)
                } else {
                    merge_branch_mut_vars(env, &written, &arm_envs, &case_lty.tags);
                    let res_tmp = self.fresh("case_res");
                    let mut tup_ltys = Vec::with_capacity(1 + written.len());
                    tup_ltys.push(case_lty.clone());
                    for v in &written {
                        tup_ltys.push(
                            env.get(v)
                                .map_or_else(|| LTy::public(Ty::Unit), |b| b.lty.clone()),
                        );
                    }
                    steps.push(BlockStep::Bind(
                        res_tmp.clone(),
                        LTy::new(Ty::Tuple(tup_ltys), case_lty.tags.clone()),
                        case_ex,
                    ));
                    for (i, v) in written.iter().enumerate() {
                        let vlty = env
                            .get(v)
                            .map_or_else(|| LTy::public(Ty::Unit), |b| b.lty.clone());
                        steps.push(BlockStep::Bind(
                            v.clone(),
                            vlty,
                            ExecExpr::Proj {
                                tup: Box::new(ExecExpr::Var(res_tmp.clone())),
                                idx: BigInt::from(i + 1),
                            },
                        ));
                    }
                    (
                        ExecExpr::Proj {
                            tup: Box::new(ExecExpr::Var(res_tmp)),
                            idx: BigInt::ZERO,
                        },
                        case_lty,
                    )
                }
            }
            _ => self.check_expr(expr, env, expected, cur_pc, scope, ret_ctx),
        };
        let sub_flow = self.flow_stack.pop().unwrap_or_default();
        if let Some(parent) = self.flow_stack.last_mut() {
            parent.merge_from(&sub_flow);
        }
        *cur_pc = cur_pc
            .union(&sub_flow.ret_exit_pc)
            .union(&sub_flow.break_pc)
            .union(&sub_flow.continue_pc);
        (out_ex, out_lty)
    }

    fn capture_active_loop_vars(&self, env: &HashMap<Ident, VarBinding>) -> Vec<ExecExpr> {
        if let Some(active) = self.loop_state_stack.last() {
            return active.iter().map(|n| ExecExpr::Var(n.clone())).collect();
        }
        let mut names: Vec<&String> = env
            .iter()
            .filter(|(_, b)| b.mutable)
            .map(|(k, _)| k)
            .collect();
        names.sort();
        names
            .into_iter()
            .map(|n| ExecExpr::Var(n.clone()))
            .collect()
    }

    #[expect(
        clippy::too_many_arguments,
        reason = "loop guard checking updates both jump pc and post-guard block pc"
    )]
    fn check_loop_guard(
        &mut self,
        guard: Option<&Expr>,
        env: &mut HashMap<Ident, VarBinding>,
        cur_pc: &mut TagSet,
        jmp_pc: &mut TagSet,
        scope: LocalScopeKind,
        ret_ctx: Option<(&str, Option<&Ty>)>,
        steps: &mut Vec<BlockStep>,
    ) -> Option<ExecExpr> {
        let g = guard?;
        let (gex, glty) =
            self.check_expr_in_block(g, env, Some(&Ty::Bool), cur_pc, scope, ret_ctx, steps);
        if glty.ty != Ty::Bool {
            self.diags.push(
                Diagnostic::error(DiagCode::TypeError, "loop guard must evaluate to `Bool`")
                    .with_span(g.span),
            );
        }
        let g_tags = glty.effective_tags();
        *jmp_pc = jmp_pc.union(&g_tags);
        *cur_pc = cur_pc.union(&g_tags);
        Some(gex)
    }

    #[expect(
        clippy::too_many_arguments,
        reason = "assignment lowering carries block state and typing context"
    )]
    fn lower_assign_stmt(
        &mut self,
        lhs: &Expr,
        rhs: &Expr,
        env: &mut HashMap<Ident, VarBinding>,
        cur_pc: &mut TagSet,
        scope: LocalScopeKind,
        ret_ctx: Option<(&str, Option<&Ty>)>,
        steps: &mut Vec<BlockStep>,
    ) {
        let (rhs_ex, mut rhs_lty) =
            self.check_expr_in_block(rhs, env, None, cur_pc, scope, ret_ctx, steps);
        rhs_lty.tags = rhs_lty.tags.union(cur_pc);
        match &lhs.kind {
            ExprKind::Ident(name) => {
                let was_mut = env.get(name).is_some_and(|b| b.mutable);
                if let Some(prev) = env.get_mut(name)
                    && prev.mutable
                {
                    let merged_tags = prev.lty.tags.union(&rhs_lty.tags);
                    if is_unresolved_list(&prev.lty.ty) && matches!(rhs_lty.ty, Ty::List(_)) {
                        prev.lty = LTy::new(rhs_lty.ty.clone(), merged_tags);
                    } else {
                        prev.lty.tags = merged_tags;
                    }
                } else {
                    env.insert(
                        name.clone(),
                        VarBinding {
                            lty: rhs_lty.clone(),
                            mutable: was_mut,
                        },
                    );
                }
                steps.push(BlockStep::Bind(name.clone(), rhs_lty, rhs_ex));
            }
            ExprKind::Underscore => {
                steps.push(BlockStep::Effect(rhs_lty, rhs_ex));
            }
            ExprKind::Tuple(elems) => {
                let tmp = self.fresh("tup");
                let elem_ltys = match &rhs_lty.ty {
                    Ty::Tuple(ts) if ts.len() == elems.len() => ts.clone(),
                    _ => {
                        self.diags.push(
                            Diagnostic::error(
                                DiagCode::TypeError,
                                format!("cannot destructure non-tuple into {}-tuple", elems.len()),
                            )
                            .with_span(lhs.span),
                        );
                        vec![LTy::public(Ty::Unit); elems.len()]
                    }
                };
                steps.push(BlockStep::Bind(tmp.clone(), rhs_lty.clone(), rhs_ex));
                for (i, (el, el_lty)) in elems.iter().zip(elem_ltys).enumerate() {
                    let proj = ExecExpr::Proj {
                        tup: Box::new(ExecExpr::Var(tmp.clone())),
                        idx: BigInt::from(i),
                    };
                    let tagged_el =
                        LTy::new(el_lty.ty, el_lty.tags.union(&rhs_lty.tags).union(cur_pc));
                    match &el.kind {
                        ExprKind::Ident(n) => {
                            let was_mut = env.get(n).is_some_and(|b| b.mutable);
                            if let Some(prev) = env.get_mut(n)
                                && prev.mutable
                            {
                                let merged_tags = prev.lty.tags.union(&tagged_el.tags);
                                if is_unresolved_list(&prev.lty.ty)
                                    && matches!(tagged_el.ty, Ty::List(_))
                                {
                                    prev.lty = LTy::new(tagged_el.ty.clone(), merged_tags);
                                } else {
                                    prev.lty.tags = merged_tags;
                                }
                            } else {
                                env.insert(
                                    n.clone(),
                                    VarBinding {
                                        lty: tagged_el.clone(),
                                        mutable: was_mut,
                                    },
                                );
                            }
                            steps.push(BlockStep::Bind(n.clone(), tagged_el, proj));
                        }
                        ExprKind::Underscore => {}
                        _ => {
                            self.diags.push(
                                Diagnostic::error(
                                    DiagCode::TypeError,
                                    "unsupported tuple destructuring target",
                                )
                                .with_span(el.span),
                            );
                        }
                    }
                }
            }
            _ => {
                self.diags.push(
                    Diagnostic::error(
                        DiagCode::TypeError,
                        "assignment target must be a variable or tuple of variables",
                    )
                    .with_span(lhs.span),
                );
            }
        }
    }

    #[expect(
        clippy::too_many_arguments,
        reason = "for-loop lowering runs monotone fixpoint sensitivity analysis and preserves loop-carried state"
    )]
    fn lower_for_stmt(
        &mut self,
        target: &ast::ForTarget,
        iter: &Expr,
        body: &[Stmt],
        env: &mut HashMap<Ident, VarBinding>,
        cur_pc: &mut TagSet,
        scope: LocalScopeKind,
        ret_ctx: Option<(&str, Option<&Ty>)>,
        steps: &mut Vec<BlockStep>,
    ) {
        let (iter_ex, iter_lty) =
            self.check_expr_in_block(iter, env, None, cur_pc, scope, ret_ctx, steps);
        let loop_pc = cur_pc.union(&iter_lty.tags);
        let (list_ex, elem_lty, base_loop_pc) = match &iter_lty.ty {
            Ty::List(el) => (iter_ex, el.as_ref().clone(), loop_pc),
            Ty::Table(tt) => {
                let row_ty_name = self.register_table_row_type(tt);
                let row_lty = LTy::new(Ty::Data(row_ty_name), tt.row_tags.clone());
                let extra = loop_pc.union(&tt.row_tags);
                (
                    ExecExpr::Prim {
                        op: ExecPrimOp::TableRowsToList,
                        args: vec![iter_ex],
                    },
                    row_lty,
                    extra,
                )
            }
            _ => {
                self.diags.push(
                    Diagnostic::error(
                        DiagCode::TypeError,
                        "`for ... in ...` requires a `List` or `Table`",
                    )
                    .with_span(iter.span),
                );
                (iter_ex, LTy::public(Ty::Unit), loop_pc)
            }
        };

        let item_var = match target {
            ast::ForTarget::Name(n) => n.name.clone(),
            ast::ForTarget::Wildcard(_) => self.fresh("ignored"),
            ast::ForTarget::Tuple(_, _) => self.fresh("for_tup"),
        };

        let mut state_names: Vec<Ident> = env
            .iter()
            .filter(|(_, b)| b.mutable)
            .map(|(k, _)| k.clone())
            .collect();
        state_names.sort();

        // Monotone fixpoint over `(cur_loop_pc, mutable var tags)` so cross-iteration flows
        // (`b = a; a = secret`) and guarded `break if secret` taint all modified loop vars!
        let diag_mark = self.diags.len();
        let warn_mark = self.warnings.len();
        let mut cur_loop_pc = base_loop_pc;
        let mut working_env = env.clone();
        let mut final_body = ExecExpr::Lit(Literal::Unit);
        let mut final_loop_flow = FlowState::default();

        self.loop_state_stack.push(state_names.clone());
        for iter_idx in 0..MAX_LOOP_FIXPOINT_ITERS {
            self.diags.truncate(diag_mark);
            self.warnings.truncate(warn_mark);
            let mut body_env = working_env.clone();
            body_env.insert(
                item_var.clone(),
                VarBinding {
                    lty: elem_lty.clone(),
                    mutable: false,
                },
            );
            let mut prefix_steps = Vec::new();
            if let ast::ForTarget::Tuple(parts, _) = target
                && let Ty::Tuple(ts) = &elem_lty.ty
            {
                for (i, (pt, tlty)) in parts.iter().zip(ts).enumerate() {
                    if let ast::ForTarget::Name(n) = pt {
                        body_env.insert(
                            n.name.clone(),
                            VarBinding {
                                lty: tlty.clone(),
                                mutable: false,
                            },
                        );
                        prefix_steps.push(BlockStep::Bind(
                            n.name.clone(),
                            tlty.clone(),
                            ExecExpr::Proj {
                                tup: Box::new(ExecExpr::Var(item_var.clone())),
                                idx: BigInt::from(i),
                            },
                        ));
                    }
                }
            }

            self.flow_stack.push(FlowState::default());
            let (body_ex, _) = self.check_block_inner(
                body,
                &mut body_env,
                None,
                &cur_loop_pc,
                scope,
                ret_ctx,
                BlockTail::StateTuple(&state_names),
                prefix_steps,
                false,
                "",
            );
            let loop_flow = self.flow_stack.pop().unwrap_or_default();

            let mut changed = false;
            let next_pc = cur_loop_pc
                .union(&loop_flow.break_pc)
                .union(&loop_flow.ret_exit_pc);
            if next_pc != cur_loop_pc {
                cur_loop_pc = next_pc;
                changed = true;
            }
            if merge_loop_mut_vars(&mut working_env, &body_env, &state_names) {
                changed = true;
            }

            final_body = body_ex;
            final_loop_flow = loop_flow;
            if !changed || iter_idx + 1 == MAX_LOOP_FIXPOINT_ITERS {
                break;
            }
        }
        self.loop_state_stack.pop();

        let state_vars = commit_loop_mut_vars(env, &working_env, &state_names);
        if let Some(parent_flow) = self.flow_stack.last_mut() {
            parent_flow.ret_tags = parent_flow.ret_tags.union(&final_loop_flow.ret_tags);
            parent_flow.ret_exit_pc = parent_flow.ret_exit_pc.union(&final_loop_flow.ret_exit_pc);
        }
        *cur_pc = cur_pc.union(&final_loop_flow.ret_exit_pc);

        steps.push(BlockStep::Loop(Box::new(LoopStep::For {
            item_var,
            iter_expr: list_ex,
            state_vars,
            body: final_body,
        })));
    }

    #[expect(
        clippy::too_many_arguments,
        reason = "while-loop lowering runs monotone fixpoint analysis across condition and body"
    )]
    fn lower_while_stmt(
        &mut self,
        cond: &Expr,
        body: &[Stmt],
        env: &mut HashMap<Ident, VarBinding>,
        cur_pc: &mut TagSet,
        scope: LocalScopeKind,
        ret_ctx: Option<(&str, Option<&Ty>)>,
        steps: &mut Vec<BlockStep>,
    ) {
        let mut state_names: Vec<Ident> = env
            .iter()
            .filter(|(_, b)| b.mutable)
            .map(|(k, _)| k.clone())
            .collect();
        state_names.sort();

        let diag_mark = self.diags.len();
        let warn_mark = self.warnings.len();
        let mut cur_loop_pc = cur_pc.clone();
        let mut working_env = env.clone();
        let mut final_cond = ExecExpr::Lit(Literal::Bool(false));
        let mut final_body = ExecExpr::Lit(Literal::Unit);
        let mut final_loop_flow = FlowState::default();

        self.loop_state_stack.push(state_names.clone());
        for iter_idx in 0..MAX_LOOP_FIXPOINT_ITERS {
            self.diags.truncate(diag_mark);
            self.warnings.truncate(warn_mark);
            let (cond_ex, cond_lty) = self.check_expr(
                cond,
                &working_env,
                Some(&Ty::Bool),
                &cur_loop_pc,
                scope,
                ret_ctx,
            );
            if cond_lty.ty != Ty::Bool {
                self.diags.push(
                    Diagnostic::error(DiagCode::TypeError, "`while` condition must be `Bool`")
                        .with_span(cond.span),
                );
            }
            let iter_pc = cur_loop_pc.union(&cond_lty.tags);
            let mut body_env = working_env.clone();

            self.flow_stack.push(FlowState::default());
            let (body_ex, _) = self.check_block_inner(
                body,
                &mut body_env,
                None,
                &iter_pc,
                scope,
                ret_ctx,
                BlockTail::StateTuple(&state_names),
                Vec::new(),
                false,
                "",
            );
            let loop_flow = self.flow_stack.pop().unwrap_or_default();

            let mut changed = false;
            let next_pc = iter_pc
                .union(&loop_flow.break_pc)
                .union(&loop_flow.ret_exit_pc);
            if next_pc != cur_loop_pc {
                cur_loop_pc = next_pc;
                changed = true;
            }
            if merge_loop_mut_vars(&mut working_env, &body_env, &state_names) {
                changed = true;
            }

            final_cond = cond_ex;
            final_body = body_ex;
            final_loop_flow = loop_flow;
            if !changed || iter_idx + 1 == MAX_LOOP_FIXPOINT_ITERS {
                break;
            }
        }
        self.loop_state_stack.pop();

        let state_vars = commit_loop_mut_vars(env, &working_env, &state_names);
        if let Some(parent_flow) = self.flow_stack.last_mut() {
            parent_flow.ret_tags = parent_flow.ret_tags.union(&final_loop_flow.ret_tags);
            parent_flow.ret_exit_pc = parent_flow.ret_exit_pc.union(&final_loop_flow.ret_exit_pc);
        }
        *cur_pc = cur_pc.union(&final_loop_flow.ret_exit_pc);

        steps.push(BlockStep::Loop(Box::new(LoopStep::While {
            cond: final_cond,
            state_vars,
            body: final_body,
        })));
    }

    fn fold_block_steps(&mut self, steps: Vec<BlockStep>) -> ExecExpr {
        let mut acc = ExecExpr::Lit(Literal::Unit);
        for step in steps.into_iter().rev() {
            match step {
                BlockStep::Final(e) => acc = e,
                BlockStep::Bind(name, lty, mut bound) => {
                    if matches!(
                        bound,
                        ExecExpr::Jump { .. } | ExecExpr::Stop { .. } | ExecExpr::Fail(_)
                    ) {
                        // Unconditional control transfer makes `acc` unreachable; keep jump in tail position.
                        acc = bound;
                    } else if expr_has_any_jump(&bound) {
                        // Lower conditional early exits (`if { return }`, `or_return`, `try`, etc.)
                        // via a Core IR tail-position `Join` continuation so `no_free_jumps` holds!
                        let cont_lbl = self.fresh("cont");
                        rewrite_tail_to_jump(&mut bound, &cont_lbl);
                        acc = ExecExpr::Join {
                            label: cont_lbl,
                            params: vec![(name, lty)],
                            rhs: Box::new(acc),
                            body: Box::new(bound),
                        };
                    } else {
                        acc = ExecExpr::LetE {
                            name,
                            lty,
                            bound: Box::new(bound),
                            body: Box::new(acc),
                        };
                    }
                }
                BlockStep::Effect(lty, mut e) => {
                    if matches!(
                        e,
                        ExecExpr::Jump { .. } | ExecExpr::Stop { .. } | ExecExpr::Fail(_)
                    ) || (matches!(acc, ExecExpr::Lit(Literal::Unit)) && lty.ty == Ty::Unit)
                    {
                        acc = e;
                    } else if expr_has_any_jump(&e) {
                        let cont_lbl = self.fresh("cont");
                        let tmp = self.fresh("seq");
                        rewrite_tail_to_jump(&mut e, &cont_lbl);
                        acc = ExecExpr::Join {
                            label: cont_lbl,
                            params: vec![(tmp, lty)],
                            rhs: Box::new(acc),
                            body: Box::new(e),
                        };
                    } else {
                        let tmp = self.fresh("seq");
                        acc = ExecExpr::LetE {
                            name: tmp,
                            lty,
                            bound: Box::new(e),
                            body: Box::new(acc),
                        };
                    }
                }
                BlockStep::Loop(lp) => match *lp {
                    LoopStep::For {
                        item_var,
                        iter_expr,
                        state_vars,
                        body,
                    } => {
                        acc = ExecExpr::ForLoop {
                            item_var,
                            iter_expr: Box::new(iter_expr),
                            state_vars,
                            body: Box::new(body),
                            after: Box::new(acc),
                        };
                    }
                    LoopStep::While {
                        cond,
                        state_vars,
                        body,
                    } => {
                        acc = ExecExpr::WhileLoop {
                            cond: Box::new(cond),
                            state_vars,
                            body: Box::new(body),
                            after: Box::new(acc),
                        };
                    }
                },
            }
        }
        acc
    }

    fn register_table_row_type(&mut self, tt: &TableTy) -> Ident {
        let name = format!("{TY_TABLE_ROW_PREFIX}{}", self.table_row_schemas.len() + 1);
        self.table_row_schemas.insert(name.clone(), tt.clone());
        name
    }

    // -----------------------------------------------------------------------
    // Expression Checking & Lowering
    // -----------------------------------------------------------------------

    fn check_expr(
        &mut self,
        expr: &Expr,
        env: &HashMap<Ident, VarBinding>,
        expected: Option<&Ty>,
        pc: &TagSet,
        scope: LocalScopeKind,
        ret_ctx: Option<(&str, Option<&Ty>)>,
    ) -> (ExecExpr, LTy) {
        match &expr.kind {
            ExprKind::Int(raw) => self.check_int_lit(raw, expected, expr.span),
            ExprKind::Decimal(raw) => self.check_decimal_lit(raw, expected, expr.span),
            ExprKind::Date(raw) => match parse_iso_date(raw) {
                Ok(days) => (ExecExpr::Lit(Literal::date(days)), LTy::public(Ty::Date)),
                Err(e) => {
                    self.diags.push(
                        Diagnostic::error(DiagCode::TypeError, e.message).with_span(expr.span),
                    );
                    (ExecExpr::Lit(Literal::date(0i64)), LTy::public(Ty::Date))
                }
            },
            ExprKind::Timestamp(raw) => match parse_iso_timestamp(raw) {
                Ok(us) => (
                    ExecExpr::Lit(Literal::timestamp(us)),
                    LTy::public(Ty::Timestamp),
                ),
                Err(e) => {
                    self.diags.push(
                        Diagnostic::error(DiagCode::TypeError, e.message).with_span(expr.span),
                    );
                    (
                        ExecExpr::Lit(Literal::timestamp(0i64)),
                        LTy::public(Ty::Timestamp),
                    )
                }
            },
            ExprKind::Text { value, .. } => (
                ExecExpr::Lit(Literal::Text(value.clone())),
                LTy::public(Ty::Text),
            ),
            ExprKind::InterpText { parts, .. } => {
                self.check_interp_text(parts, env, pc, scope, ret_ctx)
            }
            ExprKind::Atom(a) => (
                ExecExpr::Lit(Literal::Text(format!(":{a}"))),
                LTy::public(Ty::Text),
            ),
            ExprKind::Bool(b) => (ExecExpr::Lit(Literal::Bool(*b)), LTy::public(Ty::Bool)),
            ExprKind::None => {
                let inner = match expected {
                    Some(Ty::Option(t)) => t.as_ref().clone(),
                    _ => Ty::Unit,
                };
                (
                    ExecExpr::Lit(Literal::NoneLit(inner.clone())),
                    LTy::public(Ty::Option(Box::new(inner))),
                )
            }
            ExprKind::Ident(name) => {
                if let Some(b) = env.get(name) {
                    (ExecExpr::Var(name.clone()), b.lty.clone())
                } else if let Some(c) = self.consts.get(name) {
                    (ExecExpr::ConstRef(name.clone()), c.lty.clone())
                } else {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::ResolveError,
                            format!("unknown identifier `{name}`"),
                        )
                        .with_span(expr.span),
                    );
                    (ExecExpr::Lit(Literal::Unit), LTy::public(Ty::Unit))
                }
            }
            ExprKind::CapName(name) => {
                if name == "Unit" {
                    return (ExecExpr::Lit(Literal::Unit), LTy::public(Ty::Unit));
                }
                if name == "None" && !self.ctor_to_enum.contains_key("None") {
                    let inner = match expected {
                        Some(Ty::Option(t)) => t.as_ref().clone(),
                        _ => Ty::Unit,
                    };
                    return (
                        ExecExpr::Lit(Literal::NoneLit(inner.clone())),
                        LTy::public(Ty::Option(Box::new(inner))),
                    );
                }
                if let Some((enum_name, idx)) = self.ctor_to_enum.get(name).cloned() {
                    let fields_len = self
                        .enums
                        .get(&enum_name)
                        .and_then(|d| d.ctors.get(idx))
                        .map_or(0, |c| c.fields.len());
                    if fields_len == 0 {
                        return (
                            ExecExpr::Ctor {
                                type_name: enum_name.clone(),
                                ctor_name: name.clone(),
                                args: Vec::new(),
                            },
                            LTy::public(Ty::Data(enum_name)),
                        );
                    }
                }
                // CapNames can also be passed as schema/db/namespace names in specific calls
                // (handled at Call/Field sites); as a standalone expression, treat as label.
                (
                    ExecExpr::Lit(Literal::Text(name.clone())),
                    LTy::public(Ty::Text),
                )
            }
            ExprKind::Underscore | ExprKind::DotField(_) | ExprKind::DotSelf => {
                self.diags.push(
                    Diagnostic::error(
                        DiagCode::TypeError,
                        "column/self shorthand (`.` / `.col`) is only valid inside a table pipeline or `schema`/`promise` clause",
                    )
                    .with_span(expr.span),
                );
                (ExecExpr::Lit(Literal::Unit), LTy::public(Ty::Unit))
            }
            ExprKind::Paren(inner) => self.check_expr(inner, env, expected, pc, scope, ret_ctx),
            ExprKind::Tuple(elems) => {
                let exp_elems = match expected {
                    Some(Ty::Tuple(ts)) if ts.len() == elems.len() => Some(ts),
                    _ => None,
                };
                let mut exs = Vec::with_capacity(elems.len());
                let mut ltys = Vec::with_capacity(elems.len());
                for (i, e) in elems.iter().enumerate() {
                    let e_exp = exp_elems.and_then(|ts| ts.get(i)).map(|l| &l.ty);
                    let (ex, lty) = self.check_expr(e, env, e_exp, pc, scope, ret_ctx);
                    exs.push(ex);
                    ltys.push(lty);
                }
                (ExecExpr::Tuple(exs), LTy::public(Ty::Tuple(ltys)))
            }
            ExprKind::List(elems) => {
                let exp_elem = match expected {
                    Some(Ty::List(el)) => Some(el.as_ref().clone()),
                    _ => None,
                };
                if elems.is_empty() {
                    let elem_lty = exp_elem.unwrap_or_else(|| {
                        LTy::public(Ty::Data(TY_UNRESOLVED_LIST_ELEM.to_string()))
                    });
                    return (
                        ExecExpr::Prim {
                            op: ExecPrimOp::Core(PrimOp::ListLit(elem_lty.clone())),
                            args: Vec::new(),
                        },
                        LTy::public(Ty::List(Box::new(elem_lty))),
                    );
                }
                let mut exs = Vec::with_capacity(elems.len());
                let mut inferred_elem: Option<LTy> = exp_elem;
                for e in elems {
                    let hint = inferred_elem.as_ref().map(|l| &l.ty);
                    let (ex, lty) = self.check_expr(e, env, hint, pc, scope, ret_ctx);
                    inferred_elem = Some(match inferred_elem {
                        None => lty,
                        Some(prev) => LTy::new(prev.ty, prev.tags.union(&lty.tags)),
                    });
                    exs.push(ex);
                }
                let el = inferred_elem.unwrap_or_else(|| LTy::public(Ty::Unit));
                (
                    ExecExpr::Prim {
                        op: ExecPrimOp::Core(PrimOp::ListLit(el.clone())),
                        args: exs,
                    },
                    LTy::public(Ty::List(Box::new(el))),
                )
            }
            ExprKind::Map(entries) => {
                let mut k_lty = LTy::public(Ty::Text);
                let mut v_lty = LTy::public(Ty::Unit);
                let mut args = Vec::with_capacity(entries.len() * 2);
                for (idx, (k, v)) in entries.iter().enumerate() {
                    // Map keys written as bare identifiers (`{requests: 0}`) are Text keys!
                    let (kex, klty) = match &k.kind {
                        ExprKind::Ident(s) | ExprKind::CapName(s) => (
                            ExecExpr::Lit(Literal::Text(s.clone())),
                            LTy::public(Ty::Text),
                        ),
                        _ => self.check_expr(k, env, None, pc, scope, ret_ctx),
                    };
                    let (vex, vlty) = self.check_expr(v, env, None, pc, scope, ret_ctx);
                    if idx == 0 {
                        k_lty = klty;
                        v_lty = vlty;
                    } else {
                        k_lty.tags = k_lty.tags.union(&klty.tags);
                        v_lty.tags = v_lty.tags.union(&vlty.tags);
                    }
                    args.push(kex);
                    args.push(vex);
                }
                (
                    ExecExpr::Prim {
                        op: ExecPrimOp::Core(PrimOp::MapLit {
                            key_lty: k_lty.clone(),
                            val_lty: v_lty.clone(),
                        }),
                        args,
                    },
                    LTy::public(Ty::Map {
                        key: Box::new(k_lty),
                        val: Box::new(v_lty),
                    }),
                )
            }
            ExprKind::Unary { op, expr: inner } => {
                self.check_unary(*op, inner, expr.span, env, expected, pc, scope, ret_ctx)
            }
            ExprKind::Binary { op, lhs, rhs } => {
                self.check_binary(*op, lhs, rhs, expr.span, env, expected, pc, scope, ret_ctx)
            }
            ExprKind::Field { .. } | ExprKind::Call { .. } | ExprKind::Index { .. } => {
                self.check_postfix_chain(expr, env, expected, pc, scope, ret_ctx)
            }
            ExprKind::IfInline {
                cond,
                then_expr,
                else_ifs,
                else_expr,
            } => self.check_if_inline(
                cond, then_expr, else_ifs, else_expr, env, expected, pc, scope, ret_ctx,
            ),
            ExprKind::IfBlock {
                cond,
                then_body,
                else_ifs,
                else_body,
            } => {
                let mut ignored_envs = Vec::new();
                self.check_if_block_with_state(
                    cond,
                    then_body,
                    else_ifs,
                    else_body.as_ref(),
                    env,
                    expected,
                    pc,
                    scope,
                    ret_ctx,
                    &[],
                    &mut ignored_envs,
                )
            }
            ExprKind::Case { scrut, lines } => {
                let mut ignored_envs = Vec::new();
                self.check_case_with_state(
                    scrut,
                    lines,
                    expr.span,
                    env,
                    expected,
                    pc,
                    scope,
                    ret_ctx,
                    &[],
                    &mut ignored_envs,
                )
            }
            ExprKind::Lambda { params, body } => {
                let mut l_env = env.clone();
                let mut param_names: HashSet<Ident> = HashSet::new();
                let mut l_params = Vec::with_capacity(params.len());
                for p in params {
                    let pname = match p {
                        ast::LambdaParam::Name(n) => n.name.clone(),
                        ast::LambdaParam::Wildcard(_) => self.fresh("wild"),
                    };
                    param_names.insert(pname.clone());
                    let plty = LTy::public(Ty::Int);
                    l_env.insert(
                        pname.clone(),
                        VarBinding {
                            lty: plty.clone(),
                            mutable: false,
                        },
                    );
                    l_params.push((pname, plty));
                }
                // Closures cannot capture mutable `var` bindings (prevents stale-snapshot tag
                // laundering and hidden mutation side effects across closure boundaries).
                let mut_captures = collect_captured_mut_vars_lambda(body, env, &param_names);
                if !mut_captures.is_empty() {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::PrivacyError,
                            format!(
                                "closure cannot capture mutable `var` binding(s) {:?}",
                                mut_captures
                            ),
                        )
                        .with_span(expr.span),
                    );
                }
                let (bex, blty) = match body {
                    ast::LambdaBody::Expr(ex) => {
                        self.check_expr(ex, &l_env, None, pc, scope, ret_ctx)
                    }
                    ast::LambdaBody::Block(stmts) => {
                        self.check_block(stmts, &mut l_env, None, pc, scope, ret_ctx)
                    }
                };
                let fn_ty = Ty::Fn {
                    params: l_params.iter().map(|(_, l)| l.clone()).collect(),
                    pc: pc.clone(),
                    ret: Box::new(blty.clone()),
                };
                (
                    ExecExpr::Lam {
                        params: l_params,
                        pc: pc.clone(),
                        ret: blty,
                        body: Arc::new(bex),
                    },
                    LTy::new(fn_ty, pc.clone()),
                )
            }
            ExprKind::TableLit { headers, rows } => {
                self.check_table_lit(headers, rows, expr.span, env, expected, pc, scope, ret_ctx)
            }
        }
    }

    fn check_int_lit(&mut self, raw: &str, expected: Option<&Ty>, span: Span) -> (ExecExpr, LTy) {
        let cleaned: String = raw.chars().filter(|&c| c != '_').collect();
        let val: i64 = match cleaned.parse() {
            Ok(v) => v,
            Err(_) => {
                self.diags.push(
                    Diagnostic::error(
                        DiagCode::TypeError,
                        format!("integer literal `{raw}` out of Int64 range"),
                    )
                    .with_span(span),
                );
                0
            }
        };
        match expected {
            Some(Ty::Decimal) => {
                let scaled = parse_decimal_bigint(&cleaned).unwrap_or(BigInt::ZERO);
                (
                    ExecExpr::Lit(Literal::Decimal(scaled)),
                    LTy::public(Ty::Decimal),
                )
            }
            Some(Ty::Float) => (
                ExecExpr::Lit(Literal::Float(Float64::from_f64(val as f64))),
                LTy::public(Ty::Float),
            ),
            _ => (ExecExpr::Lit(Literal::int(val)), LTy::public(Ty::Int)),
        }
    }

    fn check_decimal_lit(
        &mut self,
        raw: &str,
        expected: Option<&Ty>,
        span: Span,
    ) -> (ExecExpr, LTy) {
        let cleaned: String = raw.chars().filter(|&c| c != '_').collect();
        let has_exp = cleaned.contains('e') || cleaned.contains('E');
        let want_float = has_exp
            || matches!(expected, Some(Ty::Float))
            || matches!(expected, Some(Ty::Option(inner)) if matches!(inner.as_ref(), Ty::Float));
        if want_float {
            match cleaned.parse::<f64>() {
                Ok(f) => (
                    ExecExpr::Lit(Literal::Float(Float64::from_f64(f))),
                    LTy::public(Ty::Float),
                ),
                Err(_) => {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::TypeError,
                            format!("invalid float literal `{raw}`"),
                        )
                        .with_span(span),
                    );
                    (
                        ExecExpr::Lit(Literal::Float(Float64::ZERO)),
                        LTy::public(Ty::Float),
                    )
                }
            }
        } else {
            match parse_decimal_bigint(&cleaned) {
                Ok(d) => (ExecExpr::Lit(Literal::Decimal(d)), LTy::public(Ty::Decimal)),
                Err(e) => {
                    self.diags
                        .push(Diagnostic::error(DiagCode::TypeError, e.message).with_span(span));
                    (
                        ExecExpr::Lit(Literal::Decimal(BigInt::ZERO)),
                        LTy::public(Ty::Decimal),
                    )
                }
            }
        }
    }

    fn check_interp_text(
        &mut self,
        parts: &[ast::InterpPart],
        env: &HashMap<Ident, VarBinding>,
        pc: &TagSet,
        scope: LocalScopeKind,
        ret_ctx: Option<(&str, Option<&Ty>)>,
    ) -> (ExecExpr, LTy) {
        let mut acc: Option<ExecExpr> = None;
        let mut tags = TagSet::empty();
        for part in parts {
            let piece = match part {
                ast::InterpPart::Literal { value, .. } => {
                    if value.is_empty() {
                        continue;
                    }
                    ExecExpr::Lit(Literal::Text(value.clone()))
                }
                ast::InterpPart::Expr(ex) => {
                    let (e, lty) = self.check_expr(ex, env, None, pc, scope, ret_ctx);
                    tags = tags.union(&lty.effective_tags());
                    if lty.ty == Ty::Text {
                        e
                    } else {
                        ExecExpr::Prim {
                            op: ExecPrimOp::ValToText,
                            args: vec![e],
                        }
                    }
                }
            };
            acc = Some(match acc {
                None => piece,
                Some(prev) => ExecExpr::Prim {
                    op: ExecPrimOp::Core(PrimOp::ConcatText),
                    args: vec![prev, piece],
                },
            });
        }
        (
            acc.unwrap_or_else(|| ExecExpr::Lit(Literal::Text(String::new()))),
            LTy::new(Ty::Text, tags),
        )
    }

    #[expect(
        clippy::too_many_arguments,
        reason = "unary expression checker propagates typing context"
    )]
    fn check_unary(
        &mut self,
        op: UnaryOp,
        inner: &Expr,
        span: Span,
        env: &HashMap<Ident, VarBinding>,
        expected: Option<&Ty>,
        pc: &TagSet,
        scope: LocalScopeKind,
        ret_ctx: Option<(&str, Option<&Ty>)>,
    ) -> (ExecExpr, LTy) {
        match op {
            UnaryOp::Not => {
                let (e, lty) = self.check_expr(inner, env, Some(&Ty::Bool), pc, scope, ret_ctx);
                if lty.ty != Ty::Bool {
                    self.diags.push(
                        Diagnostic::error(DiagCode::TypeError, "`not` requires a `Bool` operand")
                            .with_span(span),
                    );
                }
                (
                    ExecExpr::Prim {
                        op: ExecPrimOp::Core(PrimOp::NotBool),
                        args: vec![e],
                    },
                    LTy::new(Ty::Bool, lty.tags),
                )
            }
            UnaryOp::Neg => {
                let (e, lty) = self.check_expr(inner, env, expected, pc, scope, ret_ctx);
                let pop = match lty.ty {
                    Ty::Int => ExecPrimOp::Core(PrimOp::NegInt),
                    Ty::Decimal => ExecPrimOp::Core(PrimOp::NegDec),
                    Ty::Float => ExecPrimOp::NegFloat,
                    _ => {
                        self.diags.push(
                            Diagnostic::error(
                                DiagCode::TypeError,
                                "unary `-` requires a numeric operand",
                            )
                            .with_span(span),
                        );
                        ExecPrimOp::Core(PrimOp::NegInt)
                    }
                };
                (
                    ExecExpr::Prim {
                        op: pop,
                        args: vec![e],
                    },
                    lty,
                )
            }
            UnaryOp::Try => {
                let (e, lty) = self.check_expr(inner, env, None, pc, scope, ret_ctx);
                let (ok_ty, err_ty) = match &lty.ty {
                    Ty::Result { ok_ty, err_ty } => {
                        (ok_ty.as_ref().clone(), err_ty.as_ref().clone())
                    }
                    _ => {
                        self.diags.push(
                            Diagnostic::error(
                                DiagCode::TypeError,
                                "`try` requires a `Result(T, E)` expression",
                            )
                            .with_span(span),
                        );
                        return (e, lty);
                    }
                };
                let ok_var = self.fresh("try_ok");
                let err_var = self.fresh("try_err");
                let err_tags = lty.tags.union(&err_ty.all_tags());
                let ret_pc = pc.union(&lty.tags);
                let ret_ty = ret_ctx.and_then(|(_, t)| t);
                let err_arm_body = match (ret_ctx, ret_ty) {
                    (Some((lbl, _)), Some(Ty::Result { ok_ty: f_ok, .. })) => {
                        self.record_flow_ret(&err_tags, &ret_pc);
                        ExecExpr::Jump {
                            label: lbl.to_string(),
                            args: vec![ExecExpr::Prim {
                                op: ExecPrimOp::Core(PrimOp::ErrVal(f_ok.as_ref().clone())),
                                args: vec![ExecExpr::Var(err_var.clone())],
                            }],
                        }
                    }
                    // In `fn main(...) : Int`, `try` propagates fatal I/O errors cleanly as Fail!
                    // Still propagate `ret_pc` so post-`try` statements cannot launder the Ok/Err
                    // discriminant of a sensitive `Result`, and redact sensitive error payloads.
                    _ => {
                        if !ret_pc.is_empty() {
                            self.record_flow_ret(&TagSet::empty(), &ret_pc);
                        }
                        if !err_tags.is_empty() {
                            ExecExpr::Fail(Box::new(ExecExpr::Lit(Literal::Text(
                                crate::oracle::value::redact_tags(&err_tags),
                            ))))
                        } else {
                            ExecExpr::Fail(Box::new(ExecExpr::Prim {
                                op: ExecPrimOp::ValToText,
                                args: vec![ExecExpr::Var(err_var.clone())],
                            }))
                        }
                    }
                };
                let case_ex = ExecExpr::CaseE {
                    scrut: Box::new(e),
                    arms: vec![
                        ExecCaseArm {
                            pattern: ExecPattern::Ctor {
                                ctor: "Ok".to_string(),
                                binders: vec![ok_var.clone()],
                            },
                            body: ExecExpr::Var(ok_var),
                        },
                        ExecCaseArm {
                            pattern: ExecPattern::Ctor {
                                ctor: "Error".to_string(),
                                binders: vec![err_var],
                            },
                            body: err_arm_body,
                        },
                    ],
                };
                (case_ex, LTy::new(ok_ty, lty.tags))
            }
        }
    }

    #[expect(
        clippy::too_many_arguments,
        reason = "binary expression checker iteratively folds long left-associative chains, pipes, and coalescing"
    )]
    fn check_binary(
        &mut self,
        op: BinOp,
        lhs: &Expr,
        rhs: &Expr,
        span: Span,
        env: &HashMap<Ident, VarBinding>,
        expected: Option<&Ty>,
        pc: &TagSet,
        scope: LocalScopeKind,
        ret_ctx: Option<(&str, Option<&Ty>)>,
    ) -> (ExecExpr, LTy) {
        if op == BinOp::Pipe {
            return self.check_pipe_chain(lhs, rhs, span, env, pc, scope, ret_ctx);
        }

        if op == BinOp::Coalesce {
            let (lex, llty) = self.check_expr(lhs, env, None, pc, scope, ret_ctx);
            let inner_ty = match &llty.ty {
                Ty::Option(t) => t.as_ref().clone(),
                _ => {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::TypeError,
                            "`??` left operand must be `Option(T)` (`T?`)",
                        )
                        .with_span(lhs.span),
                    );
                    llty.ty.clone()
                }
            };
            let rhs_pc = pc.union(&llty.effective_tags());
            let (rex, rlty) = self.check_expr(rhs, env, Some(&inner_ty), &rhs_pc, scope, ret_ctx);
            let tags = llty.tags.union(&rlty.tags);
            // Short-circuit coalesce via CaseE so `rhs` is only evaluated when `lhs` is `none`.
            let some_v = self.fresh("coal_v");
            let case_ex = ExecExpr::CaseE {
                scrut: Box::new(lex),
                arms: vec![
                    ExecCaseArm {
                        pattern: ExecPattern::Ctor {
                            ctor: "Some".to_string(),
                            binders: vec![some_v.clone()],
                        },
                        body: ExecExpr::Var(some_v),
                    },
                    ExecCaseArm {
                        pattern: ExecPattern::Ctor {
                            ctor: "None".to_string(),
                            binders: Vec::new(),
                        },
                        body: rex,
                    },
                ],
            };
            return (case_ex, LTy::new(inner_ty, tags));
        }

        // Iteratively flatten arbitrarily long left-associative binary chains (`1 + 1 + ...`)
        // so 200,000+ term expressions check in O(1) call stack.
        let mut chain: Vec<(BinOp, &Expr, Span)> = Vec::new();
        chain.push((op, rhs, span));
        let mut base = lhs;
        while let ExprKind::Binary {
            op: lop,
            lhs: llhs,
            rhs: lrhs,
        } = &base.kind
        {
            if matches!(lop, BinOp::Pipe | BinOp::Coalesce) {
                break;
            }
            chain.push((*lop, lrhs.as_ref(), base.span));
            base = llhs.as_ref();
        }

        let (mut acc_ex, mut acc_lty) = self.check_expr(base, env, None, pc, scope, ret_ctx);
        let mut lhs_expr_opt: Option<&Expr> = Some(base);
        while let Some((cur_op, cur_rhs, cur_span)) = chain.pop() {
            let (next_ex, next_lty) = self.check_binary_step(
                cur_op,
                acc_ex,
                acc_lty,
                lhs_expr_opt,
                cur_rhs,
                cur_span,
                env,
                expected,
                pc,
                scope,
                ret_ctx,
            );
            acc_ex = next_ex;
            acc_lty = next_lty;
            lhs_expr_opt = None;
        }
        (acc_ex, acc_lty)
    }

    #[expect(
        clippy::too_many_arguments,
        reason = "single binary step combines already-checked LHS with RHS expression"
    )]
    fn check_binary_step(
        &mut self,
        op: BinOp,
        mut lex: ExecExpr,
        mut llty: LTy,
        lhs_lit_expr: Option<&Expr>,
        rhs: &Expr,
        span: Span,
        env: &HashMap<Ident, VarBinding>,
        expected: Option<&Ty>,
        pc: &TagSet,
        scope: LocalScopeKind,
        ret_ctx: Option<(&str, Option<&Ty>)>,
    ) -> (ExecExpr, LTy) {
        let rhs_hint = match &llty.ty {
            Ty::Option(inner)
                if matches!(op, BinOp::Eq | BinOp::Ne) && !matches!(rhs.kind, ExprKind::None) =>
            {
                Some(inner.as_ref())
            }
            t => Some(t),
        };
        let short_circuit_pc;
        let rhs_pc = if matches!(op, BinOp::And | BinOp::Or) {
            short_circuit_pc = pc.union(&llty.effective_tags());
            &short_circuit_pc
        } else {
            pc
        };
        let (mut rex, mut rlty) = self.check_expr(rhs, env, rhs_hint, rhs_pc, scope, ret_ctx);

        // Numeric literal cross-coercion when left side was a literal and right side resolved concretely.
        if llty.ty != rlty.ty {
            if let Some(lhs) = lhs_lit_expr
                && matches!(llty.ty, Ty::Decimal)
                && matches!(rlty.ty, Ty::Float)
                && is_numeric_lit(lhs)
            {
                (lex, llty) = self.check_decimal_from_expr(lhs, &Ty::Float);
            } else if let Some(lhs) = lhs_lit_expr
                && matches!(llty.ty, Ty::Int)
                && matches!(rlty.ty, Ty::Decimal | Ty::Float)
                && is_numeric_lit(lhs)
            {
                (lex, llty) = self.check_decimal_from_expr(lhs, &rlty.ty);
            } else if matches!(rlty.ty, Ty::Int | Ty::Decimal)
                && matches!(llty.ty, Ty::Float)
                && is_numeric_lit(rhs)
            {
                (rex, rlty) = self.check_decimal_from_expr(rhs, &Ty::Float);
            } else if matches!(rlty.ty, Ty::Int)
                && matches!(llty.ty, Ty::Decimal)
                && is_numeric_lit(rhs)
            {
                (rex, rlty) = self.check_decimal_from_expr(rhs, &Ty::Decimal);
            }
        }

        let tags = llty.tags.union(&rlty.tags);
        let _ = expected;

        match op {
            BinOp::And | BinOp::Or => {
                if llty.ty != Ty::Bool || rlty.ty != Ty::Bool {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::TypeError,
                            format!("`{}` requires `Bool` operands", op.as_str()),
                        )
                        .with_span(span),
                    );
                }
                let ex = if op == BinOp::And {
                    ExecExpr::IfE {
                        cond: Box::new(lex),
                        then_br: Box::new(rex),
                        else_br: Box::new(ExecExpr::Lit(Literal::Bool(false))),
                    }
                } else {
                    ExecExpr::IfE {
                        cond: Box::new(lex),
                        then_br: Box::new(ExecExpr::Lit(Literal::Bool(true))),
                        else_br: Box::new(rex),
                    }
                };
                (ex, LTy::new(Ty::Bool, tags))
            }
            BinOp::Eq | BinOp::Ne => {
                // Refine untyped `none` (`Option(Unit)`) against concrete `Option(T)` on either side.
                if matches!(&llty.ty, Ty::Option(li) if matches!(li.as_ref(), Ty::Unit))
                    && matches!(&lex, ExecExpr::Lit(Literal::NoneLit(Ty::Unit)))
                    && let Ty::Option(ri) = &rlty.ty
                    && !matches!(ri.as_ref(), Ty::Unit)
                {
                    lex = ExecExpr::Lit(Literal::NoneLit(ri.as_ref().clone()));
                    llty.ty = rlty.ty.clone();
                } else if matches!(&rlty.ty, Ty::Option(ri) if matches!(ri.as_ref(), Ty::Unit))
                    && matches!(&rex, ExecExpr::Lit(Literal::NoneLit(Ty::Unit)))
                    && let Ty::Option(li) = &llty.ty
                    && !matches!(li.as_ref(), Ty::Unit)
                {
                    rex = ExecExpr::Lit(Literal::NoneLit(li.as_ref().clone()));
                    rlty.ty = llty.ty.clone();
                }

                // Coerce `Option(T) == T` or `T == Option(T)` cleanly.
                if let Ty::Option(inner) = &llty.ty
                    && **inner == rlty.ty
                {
                    rex = ExecExpr::Prim {
                        op: ExecPrimOp::Core(PrimOp::SomeVal(rlty.ty.clone())),
                        args: vec![rex],
                    };
                    rlty.ty = llty.ty.clone();
                } else if let Ty::Option(inner) = &rlty.ty
                    && **inner == llty.ty
                {
                    lex = ExecExpr::Prim {
                        op: ExecPrimOp::Core(PrimOp::SomeVal(llty.ty.clone())),
                        args: vec![lex],
                    };
                    llty.ty = rlty.ty.clone();
                }

                // Table structural equality (ignoring hidden `group_meta`, coercing literal schemas).
                if let (Ty::Table(ltt), Ty::Table(rtt)) = (&llty.ty, &rlty.ty) {
                    if !ltt.cols.is_empty() {
                        let resolved_cols: Vec<ColSpec> = ltt
                            .cols
                            .iter()
                            .map(|lc| {
                                let resolved_ty =
                                    match (&lc.ty, rtt.find_col(&lc.name).map(|rc| &rc.ty)) {
                                        (
                                            ScalarTy::Option(li),
                                            Some(rty @ ScalarTy::Option(ri)),
                                        ) if matches!(li.as_ref(), ScalarTy::Unit)
                                            && !matches!(ri.as_ref(), ScalarTy::Unit) =>
                                        {
                                            rty.clone()
                                        }
                                        _ => lc.ty.clone(),
                                    };
                                ColSpec {
                                    ty: resolved_ty,
                                    ..lc.clone()
                                }
                            })
                            .collect();
                        let target_tt = TableTy {
                            cols: resolved_cols,
                            ..ltt.clone()
                        };
                        if target_tt.cols != ltt.cols {
                            lex = ExecExpr::Prim {
                                op: ExecPrimOp::TableCoerce(target_tt.clone()),
                                args: vec![lex],
                            };
                        }
                        if target_tt.cols != rtt.cols {
                            rex = ExecExpr::Prim {
                                op: ExecPrimOp::TableCoerce(target_tt),
                                args: vec![rex],
                            };
                        }
                    }
                    let eq_ex = ExecExpr::Prim {
                        op: ExecPrimOp::TableEq,
                        args: vec![lex, rex],
                    };
                    let out = if op == BinOp::Ne {
                        ExecExpr::Prim {
                            op: ExecPrimOp::Core(PrimOp::NotBool),
                            args: vec![eq_ex],
                        }
                    } else {
                        eq_ex
                    };
                    return (
                        out,
                        LTy::new(
                            Ty::Bool,
                            llty.effective_tags().union(&rlty.effective_tags()),
                        ),
                    );
                }

                let pop = if op == BinOp::Eq {
                    PrimOp::Eq
                } else {
                    PrimOp::Ne
                };
                (
                    ExecExpr::Prim {
                        op: ExecPrimOp::Core(pop),
                        args: vec![lex, rex],
                    },
                    LTy::new(Ty::Bool, tags),
                )
            }
            BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                let pop = match op {
                    BinOp::Lt => PrimOp::Lt,
                    BinOp::Le => PrimOp::Le,
                    BinOp::Gt => PrimOp::Gt,
                    _ => PrimOp::Ge,
                };
                (
                    ExecExpr::Prim {
                        op: ExecPrimOp::Core(pop),
                        args: vec![lex, rex],
                    },
                    LTy::new(Ty::Bool, tags),
                )
            }
            BinOp::Add => {
                let (pop, rty) = match (&llty.ty, &rlty.ty) {
                    (Ty::Int, Ty::Int) => (ExecPrimOp::Core(PrimOp::AddInt), Ty::Int),
                    (Ty::Decimal, Ty::Decimal) => (ExecPrimOp::Core(PrimOp::AddDec), Ty::Decimal),
                    (Ty::Float, Ty::Float) => (ExecPrimOp::AddFloat, Ty::Float),
                    (Ty::Text, Ty::Text) => (ExecPrimOp::Core(PrimOp::ConcatText), Ty::Text),
                    (Ty::Timestamp, Ty::Duration) => {
                        (ExecPrimOp::Core(PrimOp::AddDuration), Ty::Timestamp)
                    }
                    _ => {
                        self.diags.push(
                            Diagnostic::error(
                                DiagCode::TypeError,
                                "incompatible operand types for `+`",
                            )
                            .with_span(span),
                        );
                        (ExecPrimOp::Core(PrimOp::AddInt), llty.ty.clone())
                    }
                };
                (
                    ExecExpr::Prim {
                        op: pop,
                        args: vec![lex, rex],
                    },
                    LTy::new(rty, tags),
                )
            }
            BinOp::Sub => {
                let (pop, rty) = match (&llty.ty, &rlty.ty) {
                    (Ty::Int, Ty::Int) => (ExecPrimOp::Core(PrimOp::SubInt), Ty::Int),
                    (Ty::Decimal, Ty::Decimal) => (ExecPrimOp::Core(PrimOp::SubDec), Ty::Decimal),
                    (Ty::Float, Ty::Float) => (ExecPrimOp::SubFloat, Ty::Float),
                    (Ty::Timestamp, Ty::Timestamp) => {
                        (ExecPrimOp::Core(PrimOp::DiffTimestamp), Ty::Duration)
                    }
                    _ => {
                        self.diags.push(
                            Diagnostic::error(
                                DiagCode::TypeError,
                                "incompatible operand types for `-`",
                            )
                            .with_span(span),
                        );
                        (ExecPrimOp::Core(PrimOp::SubInt), llty.ty.clone())
                    }
                };
                (
                    ExecExpr::Prim {
                        op: pop,
                        args: vec![lex, rex],
                    },
                    LTy::new(rty, tags),
                )
            }
            BinOp::Mul => {
                let (pop, rty) = match (&llty.ty, &rlty.ty) {
                    (Ty::Int, Ty::Int) => (ExecPrimOp::Core(PrimOp::MulInt), Ty::Int),
                    (Ty::Decimal, Ty::Decimal) => (ExecPrimOp::Core(PrimOp::MulDec), Ty::Decimal),
                    (Ty::Float, Ty::Float) => (ExecPrimOp::MulFloat, Ty::Float),
                    _ => {
                        self.diags.push(
                            Diagnostic::error(
                                DiagCode::TypeError,
                                "incompatible operand types for `*`",
                            )
                            .with_span(span),
                        );
                        (ExecPrimOp::Core(PrimOp::MulInt), llty.ty.clone())
                    }
                };
                (
                    ExecExpr::Prim {
                        op: pop,
                        args: vec![lex, rex],
                    },
                    LTy::new(rty, tags),
                )
            }
            BinOp::Div => {
                let (pop, rty) = match (&llty.ty, &rlty.ty) {
                    (Ty::Int, Ty::Int) => (ExecPrimOp::Core(PrimOp::DivInt), Ty::Int),
                    (Ty::Decimal, Ty::Decimal) => (ExecPrimOp::Core(PrimOp::DivDec), Ty::Decimal),
                    (Ty::Float, Ty::Float) => (ExecPrimOp::DivFloat, Ty::Float),
                    _ => {
                        self.diags.push(
                            Diagnostic::error(
                                DiagCode::TypeError,
                                "incompatible operand types for `/`",
                            )
                            .with_span(span),
                        );
                        (ExecPrimOp::Core(PrimOp::DivInt), llty.ty.clone())
                    }
                };
                (
                    ExecExpr::Prim {
                        op: pop,
                        args: vec![lex, rex],
                    },
                    LTy::new(rty, tags),
                )
            }
            BinOp::Mod => (
                ExecExpr::Prim {
                    op: ExecPrimOp::Core(PrimOp::ModInt),
                    args: vec![lex, rex],
                },
                LTy::new(Ty::Int, tags),
            ),
            BinOp::Is => (
                ExecExpr::Prim {
                    op: ExecPrimOp::Core(PrimOp::Eq),
                    args: vec![lex, rex],
                },
                LTy::new(Ty::Bool, tags),
            ),
            BinOp::Pipe | BinOp::Coalesce => unreachable!("handled above"),
        }
    }

    fn check_decimal_from_expr(&mut self, expr: &Expr, target: &Ty) -> (ExecExpr, LTy) {
        match &expr.kind {
            ExprKind::Int(raw) => self.check_int_lit(raw, Some(target), expr.span),
            ExprKind::Decimal(raw) => self.check_decimal_lit(raw, Some(target), expr.span),
            ExprKind::Unary {
                op: UnaryOp::Neg,
                expr: inner,
            } => {
                let (e, lty) = self.check_decimal_from_expr(inner, target);
                let pop = match target {
                    Ty::Float => ExecPrimOp::NegFloat,
                    Ty::Decimal => ExecPrimOp::Core(PrimOp::NegDec),
                    _ => ExecPrimOp::Core(PrimOp::NegInt),
                };
                (
                    ExecExpr::Prim {
                        op: pop,
                        args: vec![e],
                    },
                    lty,
                )
            }
            _ => (ExecExpr::Lit(Literal::Unit), LTy::public(target.clone())),
        }
    }

    // -----------------------------------------------------------------------
    // Pipelines (`|>`): Relational Table Verbs, Charts & Report Builders
    // -----------------------------------------------------------------------

    #[expect(
        clippy::too_many_arguments,
        reason = "iterative pipe chain checker processes arbitrarily long pipelines in O(1) stack and O(N) time"
    )]
    fn check_pipe_chain(
        &mut self,
        lhs: &Expr,
        rhs: &Expr,
        span: Span,
        env: &HashMap<Ident, VarBinding>,
        pc: &TagSet,
        scope: LocalScopeKind,
        ret_ctx: Option<(&str, Option<&Ty>)>,
    ) -> (ExecExpr, LTy) {
        // Iteratively peel all left-associative `|>` stages onto a heap Vec so
        // 200,000-stage pipes check in O(N) time and O(1) stack!
        let mut stages: Vec<(&Expr, Span, Span)> = Vec::new();
        stages.push((rhs, span, lhs.span));
        let mut base = lhs;
        while let ExprKind::Binary {
            op: BinOp::Pipe,
            lhs: llhs,
            rhs: lrhs,
        } = &base.kind
        {
            stages.push((lrhs.as_ref(), base.span, llhs.span));
            base = llhs.as_ref();
        }

        let (mut cur_ex, mut cur_lty) = self.check_expr(base, env, None, pc, scope, ret_ctx);
        while let Some((stage_rhs, stage_span, lhs_span)) = stages.pop() {
            let ExprKind::Call { callee, args } = &stage_rhs.kind else {
                let mut diag = Diagnostic::error(
                    DiagCode::TypeError,
                    "right-hand side of `|>` must be a call",
                )
                .with_span(stage_rhs.span);
                if matches!(&cur_lty.ty, Ty::Table(_))
                    && let ExprKind::Ident(name) = &stage_rhs.kind
                {
                    match name.as_str() {
                        "empty?" => {
                            diag = diag.with_hint(
                                "`.empty?` is a `Table` property, not a `|>` pipeline verb; access `tbl.empty?` instead",
                            );
                        }
                        "first!" => {
                            diag = diag.with_hint(
                                "`.first!` is a `Table` property, not a `|>` pipeline verb; access `tbl.first!` instead",
                            );
                        }
                        "first" => {
                            diag = diag.with_hint(
                                "`Table` has property `.first!` (not a `|>` pipeline verb); access `tbl.first!` instead",
                            );
                        }
                        "count" | "profile" => {
                            diag = diag.with_hint(format!(
                                "`.{name}()` is a `Table` method, not a `|>` pipeline verb; call `tbl.{name}()` instead"
                            ));
                        }
                        _ => {}
                    }
                }
                self.diags.push(diag);
                continue;
            };
            let ExprKind::Ident(verb) = &callee.kind else {
                self.diags.push(
                    Diagnostic::error(
                        DiagCode::TypeError,
                        "right-hand side of `|>` must be a verb/function call",
                    )
                    .with_span(callee.span),
                );
                continue;
            };

            // Report pipeline verbs (`add_summary`, `add_chart`, `add_table`).
            if let Ty::Report(rtags) = &cur_lty.ty {
                let rtags = rtags.clone();
                let (next_ex, next_lty) = self.check_report_pipe(
                    cur_ex,
                    rtags,
                    cur_lty.tags,
                    verb,
                    args,
                    stage_span,
                    env,
                    pc,
                    scope,
                    ret_ctx,
                );
                cur_ex = next_ex;
                cur_lty = next_lty;
                continue;
            }

            // Table pipeline verbs and chart constructors.
            if let Ty::Table(in_tt) = &cur_lty.ty {
                let in_tt = in_tt.clone();
                let (next_ex, next_lty) = if verb.starts_with("chart_") {
                    self.check_chart_verb(
                        cur_ex,
                        &in_tt,
                        &cur_lty.tags,
                        verb,
                        args,
                        stage_span,
                        env,
                        pc,
                        scope,
                        ret_ctx,
                    )
                } else {
                    let in_plan = expr_to_plan(cur_ex);
                    self.check_table_verb(
                        in_plan,
                        in_tt,
                        cur_lty.tags,
                        verb,
                        args,
                        stage_span,
                        env,
                        pc,
                        scope,
                        ret_ctx,
                    )
                };
                cur_ex = next_ex;
                cur_lty = next_lty;
                continue;
            }

            // Generic pipe `x |> f(a, b)` -> `f(x, a, b)` reusing the already-checked `(cur_ex, cur_lty)`!
            let (next_ex, next_lty) = self.check_pipe_generic_call(
                callee, verb, cur_ex, cur_lty, lhs_span, args, stage_span, env, pc, scope, ret_ctx,
            );
            cur_ex = next_ex;
            cur_lty = next_lty;
        }
        (cur_ex, cur_lty)
    }

    #[expect(
        clippy::too_many_arguments,
        reason = "generic pipe call passes pre-evaluated first argument to avoid O(2^N) re-checking"
    )]
    fn check_pipe_generic_call(
        &mut self,
        callee: &Expr,
        fname: &str,
        first_ex: ExecExpr,
        first_lty: LTy,
        first_span: Span,
        rest_args: &[CallArg],
        span: Span,
        env: &HashMap<Ident, VarBinding>,
        pc: &TagSet,
        scope: LocalScopeKind,
        ret_ctx: Option<(&str, Option<&Ty>)>,
    ) -> (ExecExpr, LTy) {
        if fname == "date_trunc" {
            if let Some(CallArg::Positional(b)) = rest_args.first() {
                if let ExprKind::Atom(unit) = &b.kind {
                    if unit == "month" && first_lty.ty == Ty::Date {
                        return (
                            ExecExpr::Prim {
                                op: ExecPrimOp::Core(PrimOp::DateTruncMonth),
                                args: vec![first_ex],
                            },
                            first_lty,
                        );
                    }
                    return (
                        ExecExpr::Prim {
                            op: ExecPrimOp::DateTruncUnit(unit.clone()),
                            args: vec![first_ex],
                        },
                        first_lty,
                    );
                }
                let (eb, lb) = self.check_expr(b, env, Some(&Ty::Duration), pc, scope, ret_ctx);
                return (
                    ExecExpr::Prim {
                        op: ExecPrimOp::DateTruncDuration,
                        args: vec![first_ex, eb],
                    },
                    LTy::new(first_lty.ty, first_lty.tags.union(&lb.tags)),
                );
            }
            self.diags.push(
                Diagnostic::error(DiagCode::TypeError, "`date_trunc` expects 2 arguments")
                    .with_span(span),
            );
            return (ExecExpr::Lit(Literal::Unit), LTy::public(Ty::Unit));
        }

        if fname == "months_between" || fname == "days_between" {
            let [CallArg::Positional(b)] = rest_args else {
                self.diags.push(
                    Diagnostic::error(
                        DiagCode::TypeError,
                        format!("`{fname}` expects 2 `Date` arguments"),
                    )
                    .with_span(span),
                );
                return (ExecExpr::Lit(Literal::int(0i64)), LTy::public(Ty::Int));
            };
            if first_lty.ty != Ty::Date {
                self.diags.push(
                    Diagnostic::error(
                        DiagCode::TypeError,
                        format!("`{fname}` expects `Date` as first argument"),
                    )
                    .with_span(first_span),
                );
            }
            let (eb, lb) = self.check_expr(b, env, Some(&Ty::Date), pc, scope, ret_ctx);
            if lb.ty != Ty::Date {
                self.diags.push(
                    Diagnostic::error(
                        DiagCode::TypeError,
                        format!("`{fname}` expects `Date` as second argument"),
                    )
                    .with_span(b.span),
                );
            }
            let op = if fname == "months_between" {
                ExecPrimOp::MonthsBetween
            } else {
                ExecPrimOp::DaysBetween
            };
            return (
                ExecExpr::Prim {
                    op,
                    args: vec![first_ex, eb],
                },
                LTy::new(Ty::Int, first_lty.tags.union(&lb.tags)),
            );
        }
        if fname == "add_days" {
            let Some(days_e) = extract_one_arg(rest_args, "days") else {
                self.diags.push(
                    Diagnostic::error(DiagCode::TypeError, "`add_days` expects `(Date, Int)`")
                        .with_span(span),
                );
                return (first_ex, first_lty);
            };
            return self.check_date_add_days_expr(
                first_ex, first_lty, first_span, days_e, env, pc, scope, ret_ctx,
            );
        }
        if fname == "at_midnight_in_tz" {
            let Some(tz_e) = extract_one_arg(rest_args, "tz") else {
                self.diags.push(
                    Diagnostic::error(
                        DiagCode::TypeError,
                        "`at_midnight_in_tz` expects `(Date, Text)`",
                    )
                    .with_span(span),
                );
                return (
                    ExecExpr::Lit(Literal::timestamp(0i64)),
                    LTy::new(Ty::Timestamp, first_lty.tags),
                );
            };
            return self.check_date_midnight_tz_expr(
                first_ex, first_lty, first_span, tz_e, env, pc, scope, ret_ctx,
            );
        }
        if (fname == "in_tz" || fname == "date_in_tz")
            && let [CallArg::Positional(z)] = rest_args
        {
            if first_lty.ty != Ty::Timestamp {
                self.diags.push(
                    Diagnostic::error(
                        DiagCode::TypeError,
                        format!("`{fname}` expects `Timestamp` as first argument"),
                    )
                    .with_span(first_span),
                );
            }
            let (ez, lz) = self.check_expr(z, env, Some(&Ty::Text), pc, scope, ret_ctx);
            if lz.ty != Ty::Text {
                self.diags.push(
                    Diagnostic::error(
                        DiagCode::TypeError,
                        format!("`{fname}` expects a `Text` IANA timezone name"),
                    )
                    .with_span(z.span),
                );
            }
            let (op, out_ty) = if fname == "in_tz" {
                (ExecPrimOp::InTz, Ty::Text)
            } else {
                (ExecPrimOp::DateInTz, Ty::Date)
            };
            return (
                ExecExpr::Prim {
                    op,
                    args: vec![first_ex, ez],
                },
                LTy::new(out_ty, first_lty.tags.union(&lz.tags)),
            );
        }

        if let Some(sig) = self.fn_sigs.get(fname).cloned() {
            if !sig.is_pure && !pc.is_empty() {
                self.diags.push(
                    Diagnostic::error(
                        DiagCode::PrivacyError,
                        format!(
                            "cannot call impure function `{fname}` under sensitive control flow {:?}",
                            pc.elems()
                        ),
                    )
                    .with_span(span),
                );
            }
            let ret_lty = self
                .ensure_fn_checked(fname)
                .or(sig.ret)
                .unwrap_or_else(|| LTy::public(Ty::Unit));
            let total_args = 1 + rest_args.len();
            if total_args != sig.params.len() {
                self.diags.push(
                    Diagnostic::error(
                        DiagCode::TypeError,
                        format!(
                            "function `{fname}` expects {} argument(s), got {total_args}",
                            sig.params.len(),
                        ),
                    )
                    .with_span(span),
                );
            }
            let mut lowered_args = Vec::with_capacity(total_args);
            let mut arg_tags = first_lty.tags.clone();
            let a0 = if let Some((_, p0)) = sig.params.first() {
                self.coerce_expr(
                    first_ex,
                    &first_lty,
                    p0,
                    first_span,
                    &format!("argument 1 of `{fname}`"),
                )
            } else {
                first_ex
            };
            lowered_args.push(a0);
            for (i, arg) in rest_args.iter().enumerate() {
                let expr_arg = match arg {
                    CallArg::Positional(e) | CallArg::Named { value: e, .. } => e,
                };
                let param_lty = sig.params.get(i + 1).map(|(_, l)| l);
                let (mut aex, alty) =
                    self.check_expr(expr_arg, env, param_lty.map(|l| &l.ty), pc, scope, ret_ctx);
                if let Some(plty) = param_lty {
                    aex = self.coerce_expr(
                        aex,
                        &alty,
                        plty,
                        expr_arg.span,
                        &format!("argument {} of `{fname}`", i + 2),
                    );
                }
                arg_tags = arg_tags.union(&alty.tags);
                lowered_args.push(aex);
            }
            let out_ret = taint_return_with_pc(ret_lty, &arg_tags, pc);
            return (
                ExecExpr::Call {
                    fn_name: fname.to_string(),
                    args: lowered_args,
                },
                out_ret,
            );
        }

        // Higher-order function value in generic pipe (`x |> f(a)`).
        let (fex, flty) = self.check_expr(callee, env, None, pc, scope, ret_ctx);
        self.check_hof_app(
            fex,
            flty,
            Some((first_ex, first_lty, first_span)),
            rest_args,
            span,
            env,
            pc,
            scope,
            ret_ctx,
        )
    }

    #[expect(
        clippy::too_many_arguments,
        reason = "report builder verb checking propagates sensitivity tags"
    )]
    fn check_report_pipe(
        &mut self,
        rep_ex: ExecExpr,
        rep_tags: TagSet,
        outer_tags: TagSet,
        verb: &str,
        args: &[CallArg],
        span: Span,
        env: &HashMap<Ident, VarBinding>,
        pc: &TagSet,
        scope: LocalScopeKind,
        ret_ctx: Option<(&str, Option<&Ty>)>,
    ) -> (ExecExpr, LTy) {
        let Some(CallArg::Positional(arg0)) = args.first() else {
            self.diags.push(
                Diagnostic::error(DiagCode::TypeError, format!("`{verb}` requires 1 argument"))
                    .with_span(span),
            );
            return (rep_ex, LTy::new(Ty::Report(rep_tags), outer_tags));
        };
        let (aex, alty) = self.check_expr(arg0, env, None, pc, scope, ret_ctx);
        let merged = rep_tags.union(&alty.effective_tags());
        let op = match verb {
            "add_summary" => PrimOp::ReportAddSummary,
            "add_chart" => PrimOp::ReportAddChart,
            "add_table" => PrimOp::ReportAddTable,
            _ => {
                self.diags.push(
                    Diagnostic::error(
                        DiagCode::TypeError,
                        format!("unknown `Report` verb `{verb}`"),
                    )
                    .with_span(span),
                );
                return (rep_ex, LTy::new(Ty::Report(merged), outer_tags));
            }
        };
        (
            ExecExpr::Prim {
                op: ExecPrimOp::Core(op),
                args: vec![rep_ex, aex],
            },
            LTy::new(Ty::Report(merged), outer_tags),
        )
    }

    #[expect(
        clippy::too_many_arguments,
        reason = "chart builder verb validates column refs and propagates table sensitivity tags"
    )]
    fn check_chart_verb(
        &mut self,
        tbl_ex: ExecExpr,
        in_tt: &TableTy,
        outer_tags: &TagSet,
        verb: &str,
        args: &[CallArg],
        span: Span,
        env: &HashMap<Ident, VarBinding>,
        pc: &TagSet,
        scope: LocalScopeKind,
        ret_ctx: Option<(&str, Option<&Ty>)>,
    ) -> (ExecExpr, LTy) {
        let kind = match verb {
            "chart_bar" => ChartKind::Bar,
            "chart_line" => ChartKind::Line,
            "chart_scatter" => ChartKind::Scatter,
            "chart_histogram" => ChartKind::Histogram,
            "chart_heatmap" => ChartKind::Heatmap,
            _ => {
                self.diags.push(
                    Diagnostic::error(DiagCode::TypeError, format!("unknown chart verb `{verb}`"))
                        .with_span(span),
                );
                ChartKind::Bar
            }
        };
        let mut x_col: Option<Ident> = None;
        let mut y_col: Option<Ident> = None;
        let mut color_col: Option<Ident> = None;
        let mut value_col: Option<Ident> = None;
        let mut title_expr: Option<ExecExpr> = None;
        let mut trendline_expr: Option<ExecExpr> = None;
        let mut bins_expr: Option<ExecExpr> = None;
        let mut extra_tags = TagSet::empty();

        for arg in args {
            match arg {
                CallArg::Named { name, value, .. } => match name.name.as_str() {
                    "x" | "y" | "color" | "value" | "column" => {
                        if let ExprKind::DotField(m) = &value.kind {
                            if let Some(c) = in_tt.find_col(&m.name) {
                                extra_tags = extra_tags.union(&c.tags);
                                match name.name.as_str() {
                                    "x" | "column" => x_col = Some(m.name.clone()),
                                    "y" => y_col = Some(m.name.clone()),
                                    "color" => color_col = Some(m.name.clone()),
                                    "value" => value_col = Some(m.name.clone()),
                                    _ => {}
                                }
                            } else {
                                self.diags.push(
                                    Diagnostic::error(
                                        DiagCode::TypeError,
                                        format!("unknown column `.{}` in `{verb}`", m.name),
                                    )
                                    .with_span(m.span),
                                );
                            }
                        } else {
                            self.diags.push(
                                Diagnostic::error(
                                    DiagCode::TypeError,
                                    format!(
                                        "`{}:` in `{verb}` expects a `.column` reference",
                                        name.name
                                    ),
                                )
                                .with_span(value.span),
                            );
                        }
                    }
                    "title" => {
                        let (tex, tlty) =
                            self.check_expr(value, env, Some(&Ty::Text), pc, scope, ret_ctx);
                        if tlty.ty != Ty::Text {
                            self.diags.push(
                                Diagnostic::error(
                                    DiagCode::TypeError,
                                    format!("`title:` in `{verb}` must be `Text`"),
                                )
                                .with_span(value.span),
                            );
                        }
                        extra_tags = extra_tags.union(&tlty.effective_tags());
                        title_expr = Some(tex);
                    }
                    "trendline" => {
                        let (mex, mlty) =
                            self.check_expr(value, env, Some(&Ty::LinearModel), pc, scope, ret_ctx);
                        if mlty.ty != Ty::LinearModel {
                            self.diags.push(
                                Diagnostic::error(
                                    DiagCode::TypeError,
                                    format!("`trendline:` in `{verb}` must be a `LinearModel`"),
                                )
                                .with_span(value.span),
                            );
                        }
                        extra_tags = extra_tags.union(&mlty.effective_tags());
                        trendline_expr = Some(mex);
                    }
                    "bins" => {
                        let (bex, blty) =
                            self.check_expr(value, env, Some(&Ty::Int), pc, scope, ret_ctx);
                        if blty.ty != Ty::Int {
                            self.diags.push(
                                Diagnostic::error(
                                    DiagCode::TypeError,
                                    format!("`bins:` in `{verb}` must be `Int`"),
                                )
                                .with_span(value.span),
                            );
                        }
                        extra_tags = extra_tags.union(&blty.effective_tags());
                        bins_expr = Some(bex);
                    }
                    _ => {}
                },
                CallArg::Positional(e) => {
                    if let ExprKind::DotField(m) = &e.kind {
                        if let Some(c) = in_tt.find_col(&m.name) {
                            extra_tags = extra_tags.union(&c.tags);
                            if x_col.is_none() {
                                x_col = Some(m.name.clone());
                            } else if y_col.is_none() {
                                y_col = Some(m.name.clone());
                            }
                        } else {
                            self.diags.push(
                                Diagnostic::error(
                                    DiagCode::TypeError,
                                    format!("unknown column `.{}` in `{verb}`", m.name),
                                )
                                .with_span(m.span),
                            );
                        }
                    }
                }
            }
        }
        let chart_tags = in_tt
            .row_tags
            .union(&in_tt.order_tags)
            .union(&extra_tags)
            .union(outer_tags);
        let mut prim_args = vec![tbl_ex];
        let has_title_expr = if let Some(tex) = title_expr {
            prim_args.push(tex);
            true
        } else {
            false
        };
        let has_trendline_expr = if let Some(mex) = trendline_expr {
            prim_args.push(mex);
            true
        } else {
            false
        };
        let has_bins_expr = if let Some(bex) = bins_expr {
            prim_args.push(bex);
            true
        } else {
            false
        };
        (
            ExecExpr::Prim {
                op: ExecPrimOp::ChartMakeEx {
                    kind,
                    x_col,
                    y_col,
                    color_col,
                    value_col,
                    has_title_expr,
                    has_trendline_expr,
                    has_bins_expr,
                },
                args: prim_args,
            },
            LTy::new(Ty::Chart(chart_tags), TagSet::empty()),
        )
    }

    #[expect(
        clippy::too_many_arguments,
        reason = "relational verb checker updates structural TableTy and privacy metadata"
    )]
    fn check_table_verb(
        &mut self,
        in_plan: ExecPlan,
        in_tt: TableTy,
        outer_tags: TagSet,
        verb: &str,
        args: &[CallArg],
        span: Span,
        env: &HashMap<Ident, VarBinding>,
        pc: &TagSet,
        scope: LocalScopeKind,
        ret_ctx: Option<(&str, Option<&Ty>)>,
    ) -> (ExecExpr, LTy) {
        match verb {
            "where" => {
                let Some(CallArg::Positional(pred)) = args.first() else {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::TypeError,
                            "`where` expects 1 predicate argument",
                        )
                        .with_span(span),
                    );
                    return (
                        ExecExpr::Rel(Box::new(in_plan)),
                        LTy::new(Ty::Table(in_tt), outer_tags),
                    );
                };
                let (re, re_ty, re_tags) =
                    self.check_row_expr(pred, &in_tt.cols, env, Some(&Ty::Bool), false);
                if re_ty != Ty::Bool {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::TypeError,
                            "`where` predicate must return `Bool`",
                        )
                        .with_span(pred.span),
                    );
                }
                let mut out_tt = in_tt;
                out_tt.row_tags = out_tt.row_tags.union(&re_tags);
                (
                    ExecExpr::Rel(Box::new(ExecPlan::Filter {
                        input: Box::new(in_plan),
                        pred: re,
                    })),
                    LTy::new(Ty::Table(out_tt), outer_tags),
                )
            }
            "select" => {
                let mut keep_cols = Vec::new();
                let mut renames = Vec::new();
                let mut out_cols = Vec::new();
                for arg in args {
                    match arg {
                        CallArg::Positional(e) => {
                            if let ExprKind::DotField(m) = &e.kind {
                                if let Some(cs) = in_tt.find_col(&m.name) {
                                    keep_cols.push(m.name.clone());
                                    out_cols.push(cs.clone());
                                } else {
                                    self.diags.push(
                                        Diagnostic::error(
                                            DiagCode::TypeError,
                                            format!("unknown column `.{}` in `select`", m.name),
                                        )
                                        .with_span(m.span),
                                    );
                                }
                            } else {
                                self.diags.push(
                                    Diagnostic::error(
                                        DiagCode::TypeError,
                                        "`select` expects `.col` or `alias: .col`",
                                    )
                                    .with_span(e.span),
                                );
                            }
                        }
                        CallArg::Named { name, value, .. } => {
                            if let ExprKind::DotField(m) = &value.kind {
                                if let Some(cs) = in_tt.find_col(&m.name) {
                                    keep_cols.push(m.name.clone());
                                    renames.push((m.name.clone(), name.name.clone()));
                                    let mut renamed = cs.clone();
                                    renamed.name = name.name.clone();
                                    out_cols.push(renamed);
                                } else {
                                    self.diags.push(
                                        Diagnostic::error(
                                            DiagCode::TypeError,
                                            format!("unknown column `.{}` in `select`", m.name),
                                        )
                                        .with_span(m.span),
                                    );
                                }
                            } else {
                                self.diags.push(
                                    Diagnostic::error(
                                        DiagCode::TypeError,
                                        "`select` alias value must be `.col`",
                                    )
                                    .with_span(value.span),
                                );
                            }
                        }
                    }
                }
                if out_cols.is_empty() {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::TypeError,
                            "`select` must retain at least one column",
                        )
                        .with_span(span),
                    );
                }
                let mut plan = ExecPlan::Select {
                    input: Box::new(in_plan),
                    cols: keep_cols,
                };
                if !renames.is_empty() {
                    plan = ExecPlan::Rename {
                        input: Box::new(plan),
                        pairs: renames,
                    };
                }
                let mut out_tt = in_tt;
                out_tt.cols = out_cols;
                (
                    ExecExpr::Rel(Box::new(plan)),
                    LTy::new(Ty::Table(out_tt), outer_tags),
                )
            }
            "drop" => {
                let mut drop_cols = Vec::new();
                for arg in args {
                    if let CallArg::Positional(e) = arg
                        && let ExprKind::DotField(m) = &e.kind
                    {
                        if in_tt.find_col(&m.name).is_none() {
                            self.diags.push(
                                Diagnostic::error(
                                    DiagCode::TypeError,
                                    format!("unknown column `.{}` in `drop`", m.name),
                                )
                                .with_span(m.span),
                            );
                        }
                        drop_cols.push(m.name.clone());
                    }
                }
                let mut out_tt = in_tt;
                out_tt.cols.retain(|c| !drop_cols.contains(&c.name));
                if out_tt.cols.is_empty() {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::TypeError,
                            "`drop` cannot remove all columns from a table",
                        )
                        .with_span(span),
                    );
                }
                (
                    ExecExpr::Rel(Box::new(ExecPlan::Drop {
                        input: Box::new(in_plan),
                        cols: drop_cols,
                    })),
                    LTy::new(Ty::Table(out_tt), outer_tags),
                )
            }
            "rename" => {
                let mut pairs = Vec::new();
                let mut out_tt = in_tt;
                for arg in args {
                    if let CallArg::Named { name, value, .. } = arg
                        && let ExprKind::DotField(m) = &value.kind
                    {
                        if let Some(c) = out_tt.cols.iter_mut().find(|c| c.name == m.name) {
                            c.name = name.name.clone();
                            pairs.push((m.name.clone(), name.name.clone()));
                        } else {
                            self.diags.push(
                                Diagnostic::error(
                                    DiagCode::TypeError,
                                    format!("unknown column `.{}` in `rename`", m.name),
                                )
                                .with_span(m.span),
                            );
                        }
                    } else {
                        self.diags.push(
                            Diagnostic::error(
                                DiagCode::TypeError,
                                "`rename` expects `new_name: .old_name`",
                            )
                            .with_span(arg.span()),
                        );
                    }
                }
                (
                    ExecExpr::Rel(Box::new(ExecPlan::Rename {
                        input: Box::new(in_plan),
                        pairs,
                    })),
                    LTy::new(Ty::Table(out_tt), outer_tags),
                )
            }
            "derive" => {
                let mut items = Vec::new();
                let mut out_tt = in_tt;
                for arg in args {
                    let CallArg::Named { name, value, .. } = arg else {
                        self.diags.push(
                            Diagnostic::error(
                                DiagCode::TypeError,
                                "`derive` expects `col_name: expr` arguments",
                            )
                            .with_span(arg.span()),
                        );
                        continue;
                    };
                    // Detect `bucket(.col, cuts: [...], labels: [...])` built-in declassifier.
                    if let ExprKind::Call {
                        callee,
                        args: bargs,
                    } = &value.kind
                        && let ExprKind::Ident(fn_name) = &callee.kind
                        && fn_name == "bucket"
                    {
                        if let Some((item, spec)) =
                            self.check_bucket_call(&name.name, bargs, &out_tt, value.span)
                        {
                            upsert_col(&mut out_tt.cols, spec);
                            items.push(item);
                        }
                        continue;
                    }
                    // Detect `coarsen(.col, allow: [...], other: "...")` built-in declassifier.
                    if let ExprKind::Call {
                        callee,
                        args: cargs,
                    } = &value.kind
                        && let ExprKind::Ident(fn_name) = &callee.kind
                        && fn_name == "coarsen"
                    {
                        if let Some((item, spec)) =
                            self.check_coarsen_call(&name.name, cargs, &out_tt, value.span)
                        {
                            upsert_col(&mut out_tt.cols, spec);
                            items.push(item);
                        }
                        continue;
                    }
                    let (re, re_ty, re_tags) =
                        self.check_row_expr(value, &out_tt.cols, env, None, false);
                    let scalar_ty = re_ty.to_scalar_ty().unwrap_or_else(|| {
                        self.diags.push(
                            Diagnostic::error(
                                DiagCode::TypeError,
                                format!("derived column `{}` must have a scalar type", name.name),
                            )
                            .with_span(value.span),
                        );
                        ScalarTy::Unit
                    });
                    let spec = ColSpec {
                        name: name.name.clone(),
                        ty: scalar_ty,
                        tags: re_tags,
                        bucketed: crate::runtime::ir::is_exec_row_expr_coarsened(&re, &out_tt.cols),
                        agg_kind: AggKind::Raw,
                    };
                    upsert_col(&mut out_tt.cols, spec);
                    items.push(ExecDeriveItem::ColExpr {
                        name: name.name.clone(),
                        expr: Box::new(re),
                    });
                }
                (
                    ExecExpr::Rel(Box::new(ExecPlan::Derive {
                        input: Box::new(in_plan),
                        items,
                    })),
                    LTy::new(Ty::Table(out_tt), outer_tags),
                )
            }
            "sort_by" | "sort_desc" => {
                let dir = if verb == "sort_desc" {
                    SortDir::Desc
                } else {
                    SortDir::Asc
                };
                let mut keys = Vec::new();
                let mut key_tags = TagSet::empty();
                for arg in args {
                    if let CallArg::Positional(e) = arg
                        && let ExprKind::DotField(m) = &e.kind
                    {
                        if let Some(c) = in_tt.find_col(&m.name) {
                            key_tags = key_tags.union(&c.tags);
                            keys.push((m.name.clone(), dir));
                        } else {
                            self.diags.push(
                                Diagnostic::error(
                                    DiagCode::TypeError,
                                    format!("unknown sort column `.{}`", m.name),
                                )
                                .with_span(m.span),
                            );
                        }
                    }
                }
                let mut out_tt = in_tt;
                for c in &mut out_tt.cols {
                    c.agg_kind = AggKind::Raw;
                }
                out_tt.order_tags = out_tt.order_tags.union(&key_tags);
                out_tt.grouped_by = None;
                out_tt.summarized = false;
                out_tt.distinct_by = None;
                (
                    ExecExpr::Rel(Box::new(ExecPlan::Sort {
                        input: Box::new(in_plan),
                        keys,
                    })),
                    LTy::new(Ty::Table(out_tt), outer_tags),
                )
            }
            "distinct" => {
                let mut cols = Vec::new();
                let mut key_tags = TagSet::empty();
                if args.is_empty() {
                    for c in &in_tt.cols {
                        key_tags = key_tags.union(&c.tags);
                    }
                } else {
                    for arg in args {
                        if let CallArg::Positional(e) = arg
                            && let ExprKind::DotField(m) = &e.kind
                        {
                            if let Some(c) = in_tt.find_col(&m.name) {
                                key_tags = key_tags.union(&c.tags);
                                cols.push(m.name.clone());
                            } else {
                                self.diags.push(
                                    Diagnostic::error(
                                        DiagCode::TypeError,
                                        format!("unknown column `.{}` in `distinct`", m.name),
                                    )
                                    .with_span(m.span),
                                );
                            }
                        }
                    }
                }
                let mut out_tt = in_tt;
                out_tt.row_tags = out_tt.row_tags.union(&key_tags);
                (
                    ExecExpr::Rel(Box::new(ExecPlan::Distinct {
                        input: Box::new(in_plan),
                        cols,
                    })),
                    LTy::new(Ty::Table(out_tt), outer_tags),
                )
            }
            "dedupe_by" => self.check_dedupe_by_verb(in_plan, in_tt, outer_tags, args, span),
            "limit" => {
                let n = match args.first() {
                    Some(CallArg::Positional(Expr {
                        kind: ExprKind::Int(raw),
                        ..
                    })) => raw.replace('_', "").parse::<u64>().unwrap_or(0),
                    _ => {
                        self.diags.push(
                            Diagnostic::error(
                                DiagCode::TypeError,
                                "`limit` expects a non-negative integer literal",
                            )
                            .with_span(span),
                        );
                        0
                    }
                };
                let mut out_tt = in_tt;
                for c in &mut out_tt.cols {
                    c.agg_kind = AggKind::Raw;
                }
                out_tt.row_tags = out_tt.row_tags.union(&out_tt.order_tags);
                out_tt.grouped_by = None;
                out_tt.summarized = false;
                out_tt.distinct_by = None;
                (
                    ExecExpr::Rel(Box::new(ExecPlan::Limit {
                        input: Box::new(in_plan),
                        n: BigInt::from(n),
                    })),
                    LTy::new(Ty::Table(out_tt), outer_tags),
                )
            }
            "group_by" => {
                let mut keys = Vec::new();
                let mut key_tags = TagSet::empty();
                for arg in args {
                    if let CallArg::Positional(e) = arg
                        && let ExprKind::DotField(m) = &e.kind
                    {
                        if let Some(c) = in_tt.find_col(&m.name) {
                            key_tags = key_tags.union(&c.tags);
                            keys.push(m.name.clone());
                        } else {
                            self.diags.push(
                                Diagnostic::error(
                                    DiagCode::TypeError,
                                    format!("unknown grouping column `.{}`", m.name),
                                )
                                .with_span(m.span),
                            );
                        }
                    }
                }
                let mut out_tt = in_tt;
                out_tt.row_tags = out_tt.row_tags.union(&key_tags);
                out_tt.grouped_by = Some(keys.clone());
                out_tt.summarized = false;
                out_tt.distinct_by = None;
                (
                    ExecExpr::Rel(Box::new(ExecPlan::GroupBy {
                        input: Box::new(in_plan),
                        keys,
                    })),
                    LTy::new(Ty::Table(out_tt), outer_tags),
                )
            }
            "summarize" => self.check_summarize_verb(in_plan, in_tt, outer_tags, args, span, env),
            "suppress_small_groups" => {
                self.check_suppress_verb(in_plan, in_tt, outer_tags, args, span)
            }
            "shuffle" => self.check_shuffle_verb(
                in_plan, in_tt, outer_tags, args, span, env, pc, scope, ret_ctx,
            ),
            "suppress_small_cells" => {
                self.check_suppress_cells_verb(in_plan, in_tt, outer_tags, args, span)
            }
            "format_csv" => self.check_format_csv_call(
                ExecExpr::Rel(Box::new(in_plan)),
                &in_tt,
                &outer_tags,
                args,
                span,
                env,
                pc,
                scope,
                ret_ctx,
            ),
            "window" => self.check_window_verb(in_plan, in_tt, outer_tags, args, span, env),
            "fill_gaps" => self.check_fill_gaps_verb(in_plan, in_tt, outer_tags, args, span),
            "pivot_wider" => self.check_pivot_wider_verb(in_plan, in_tt, outer_tags, args, span),
            "pivot_longer" => self.check_pivot_longer_verb(in_plan, in_tt, outer_tags, args, span),
            "crosstab" => self.check_crosstab_verb(in_plan, in_tt, outer_tags, args, span),
            "union" => {
                let Some(CallArg::Positional(other_e)) = args.first() else {
                    self.diags.push(
                        Diagnostic::error(DiagCode::TypeError, "`union` requires 1 table argument")
                            .with_span(span),
                    );
                    return (
                        ExecExpr::Rel(Box::new(in_plan)),
                        LTy::new(Ty::Table(in_tt), outer_tags),
                    );
                };
                let (oex, olty) = self.check_expr(other_e, env, None, pc, scope, ret_ctx);
                let mut out_tt = in_tt;
                if let Ty::Table(ott) = &olty.ty {
                    if ott.cols.len() != out_tt.cols.len()
                        || out_tt
                            .cols
                            .iter()
                            .zip(&ott.cols)
                            .any(|(a, b)| a.name != b.name || a.ty != b.ty)
                    {
                        self.diags.push(
                            Diagnostic::error(
                                DiagCode::TypeError,
                                "`union` requires tables with matching column names and types",
                            )
                            .with_span(span),
                        );
                    } else {
                        for (a, b) in out_tt.cols.iter_mut().zip(&ott.cols) {
                            a.tags = a.tags.union(&b.tags);
                            a.bucketed = a.bucketed && b.bucketed;
                        }
                        out_tt.row_tags = out_tt.row_tags.union(&ott.row_tags);
                        out_tt.order_tags = TagSet::empty();
                    }
                } else {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::TypeError,
                            "`union` argument must be a `Table`",
                        )
                        .with_span(other_e.span),
                    );
                }
                let rplan = expr_to_plan(oex);
                (
                    ExecExpr::Rel(Box::new(ExecPlan::Union {
                        left: Box::new(in_plan),
                        right: Box::new(rplan),
                    })),
                    LTy::new(Ty::Table(out_tt), outer_tags.union(&olty.tags)),
                )
            }
            "redact" => {
                let col_name = match args.first() {
                    Some(CallArg::Positional(Expr {
                        kind: ExprKind::DotField(m),
                        ..
                    })) => m.name.clone(),
                    _ => {
                        self.diags.push(
                            Diagnostic::error(
                                DiagCode::TypeError,
                                "`redact` expects a `.column` argument",
                            )
                            .with_span(span),
                        );
                        String::new()
                    }
                };
                let mut out_tt = in_tt;
                if let Some(c) = out_tt.cols.iter_mut().find(|c| c.name == col_name) {
                    c.ty = ScalarTy::Text;
                    c.tags = TagSet::empty();
                    c.bucketed = false;
                } else if !col_name.is_empty() {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::TypeError,
                            format!("unknown column `.{col_name}` in `redact`"),
                        )
                        .with_span(span),
                    );
                }
                (
                    ExecExpr::Rel(Box::new(ExecPlan::Redact {
                        input: Box::new(in_plan),
                        col: col_name,
                        replacement: "[REDACTED]".to_string(),
                    })),
                    LTy::new(Ty::Table(out_tt), outer_tags),
                )
            }
            "pseudonymize" => {
                let col_name = match args.first() {
                    Some(CallArg::Positional(Expr {
                        kind: ExprKind::DotField(m),
                        ..
                    })) => m.name.clone(),
                    _ => {
                        self.diags.push(
                            Diagnostic::error(
                                DiagCode::TypeError,
                                "`pseudonymize` expects `.column, key: secret`",
                            )
                            .with_span(span),
                        );
                        String::new()
                    }
                };
                let key_expr = args.iter().find_map(|a| match a {
                    CallArg::Named { name, value, .. } if name.name == "key" => Some(value),
                    _ => None,
                });
                let secret_ex = if let Some(ke) = key_expr {
                    let (sex, slty) = self.check_expr(ke, env, None, pc, scope, ret_ctx);
                    if !matches!(slty.ty, Ty::Secret(_)) {
                        self.diags.push(
                            Diagnostic::error(
                                DiagCode::CapabilityError,
                                "`pseudonymize(..., key: ...)` requires a `Secret` capability",
                            )
                            .with_span(ke.span),
                        );
                    }
                    sex
                } else {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::CapabilityError,
                            "`pseudonymize` requires a `key: secret` argument",
                        )
                        .with_span(span),
                    );
                    ExecExpr::Lit(Literal::Unit)
                };
                let mut out_tt = in_tt;
                if let Some(c) = out_tt.cols.iter_mut().find(|c| c.name == col_name) {
                    c.ty = ScalarTy::Text;
                    c.tags = c.tags.remove("pii");
                    c.bucketed = false;
                } else if !col_name.is_empty() {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::TypeError,
                            format!("unknown column `.{col_name}` in `pseudonymize`"),
                        )
                        .with_span(span),
                    );
                }
                (
                    ExecExpr::Rel(Box::new(ExecPlan::Pseudonymize {
                        input: Box::new(in_plan),
                        col: col_name,
                        secret: Box::new(secret_ex),
                    })),
                    LTy::new(Ty::Table(out_tt), outer_tags),
                )
            }
            "join_one"
            | "join_many_to_one"
            | "join_many"
            | "left_join_one"
            | "left_join_many_to_one"
            | "semi_join"
            | "anti_join" => {
                let kind = match verb {
                    "join_one" => JoinKind::InnerOne,
                    "join_many_to_one" => JoinKind::InnerManyToOne,
                    "join_many" => JoinKind::InnerMany,
                    "left_join_one" => JoinKind::LeftOne,
                    "left_join_many_to_one" => JoinKind::LeftManyToOne,
                    "semi_join" => JoinKind::Semi,
                    _ => JoinKind::Anti,
                };
                self.check_join_verb(
                    kind, in_plan, in_tt, outer_tags, args, span, env, pc, scope, ret_ctx,
                )
            }
            _ => {
                let mut diag = Diagnostic::error(
                    DiagCode::TypeError,
                    format!("unknown table pipeline verb `{verb}`"),
                )
                .with_span(span);
                match verb {
                    "count" => {
                        diag = diag.with_hint(
                            "`.count()` is a `Table` method, not a `|>` pipeline verb; call `tbl.count()` instead (or bind the pipeline result first)",
                        );
                    }
                    "empty?" => {
                        diag = diag.with_hint(
                            "`.empty?` is a `Table` property, not a `|>` pipeline verb; access `tbl.empty?` without `()` instead",
                        );
                    }
                    "first!" => {
                        diag = diag.with_hint(
                            "`.first!` is a `Table` property, not a `|>` pipeline verb; access `tbl.first!` without `()` instead",
                        );
                    }
                    "first" => {
                        diag = diag.with_hint(
                            "`Table` has property `.first!` (not a `|>` pipeline verb or `.first`); access `tbl.first!` without `()` instead (check `tbl.empty?` first if it may be empty)",
                        );
                    }
                    "profile" => {
                        diag = diag.with_hint(
                            "`.profile()` is a `Table` method, not a `|>` pipeline verb; call `tbl.profile()` instead",
                        );
                    }
                    "sum" | "mean" | "stddev" => {
                        diag = diag.with_hint(format!(
                            "`.{verb}(.col)` is a `Table` method, not a `|>` pipeline verb; call `tbl.{verb}(.col)` or use `|> summarize(...)` instead"
                        ));
                    }
                    _ => {}
                }
                self.diags.push(diag);
                (
                    ExecExpr::Rel(Box::new(in_plan)),
                    LTy::new(Ty::Table(in_tt), outer_tags),
                )
            }
        }
    }

    fn check_bucket_call(
        &mut self,
        out_col: &str,
        args: &[CallArg],
        in_tt: &TableTy,
        span: Span,
    ) -> Option<(ExecDeriveItem, ColSpec)> {
        let source = match args.first() {
            Some(CallArg::Positional(Expr {
                kind: ExprKind::DotField(m),
                ..
            })) => m.name.clone(),
            _ => {
                self.diags.push(
                    Diagnostic::error(
                        DiagCode::TypeError,
                        "`bucket` expects `.col, cuts: [...], labels: [...]`",
                    )
                    .with_span(span),
                );
                return None;
            }
        };
        let Some(src_col) = in_tt.find_col(&source) else {
            self.diags.push(
                Diagnostic::error(
                    DiagCode::TypeError,
                    format!("unknown column `.{source}` in `bucket`"),
                )
                .with_span(span),
            );
            return None;
        };
        let cuts_arg = args.iter().find_map(|a| match a {
            CallArg::Named { name, value, .. } if name.name == "cuts" => Some(value),
            _ => None,
        });
        let labels_arg = args.iter().find_map(|a| match a {
            CallArg::Named { name, value, .. } if name.name == "labels" => Some(value),
            _ => None,
        });
        let target_ty = src_col.ty.to_ty();
        let mut cuts = Vec::new();
        if let Some(Expr {
            kind: ExprKind::List(items),
            ..
        }) = cuts_arg
        {
            for it in items {
                let (e, _) = self.check_expr(
                    it,
                    &HashMap::new(),
                    Some(&target_ty),
                    &TagSet::empty(),
                    LocalScopeKind::Normal,
                    None,
                );
                if let Some(l) = e.into_lit() {
                    cuts.push(l);
                } else {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::PrivacyError,
                            "`bucket` cuts must be compile-time constant literals",
                        )
                        .with_span(it.span),
                    );
                }
            }
        } else {
            self.diags.push(
                Diagnostic::error(
                    DiagCode::TypeError,
                    "`bucket` requires `cuts: [...]` list literal",
                )
                .with_span(span),
            );
        }
        let mut labels = Vec::new();
        if let Some(Expr {
            kind: ExprKind::List(items),
            ..
        }) = labels_arg
        {
            for it in items {
                if let ExprKind::Text { value: s, .. } = &it.kind {
                    labels.push(s.clone());
                } else {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::PrivacyError,
                            "`bucket` labels must be compile-time string literals",
                        )
                        .with_span(it.span),
                    );
                }
            }
        } else {
            self.diags.push(
                Diagnostic::error(
                    DiagCode::TypeError,
                    "`bucket` requires `labels: [...]` list literal",
                )
                .with_span(span),
            );
        }
        if labels.len() != cuts.len() + 1 {
            self.diags.push(
                Diagnostic::error(
                    DiagCode::TypeError,
                    format!(
                        "`bucket` requires `labels.len() == cuts.len() + 1` (got {} labels for {} cuts)",
                        labels.len(),
                        cuts.len()
                    ),
                )
                .with_span(span),
            );
        }
        let spec = ColSpec {
            name: out_col.to_string(),
            ty: ScalarTy::Text,
            // Stays tagged on individual rows; clears under `suppress_small_groups` because `bucketed = true`!
            tags: src_col.tags.clone(),
            bucketed: true,
            agg_kind: AggKind::Raw,
        };
        Some((
            ExecDeriveItem::BucketCol {
                name: out_col.to_string(),
                source,
                cuts,
                labels,
            },
            spec,
        ))
    }

    fn check_coarsen_call(
        &mut self,
        out_col: &str,
        args: &[CallArg],
        in_tt: &TableTy,
        span: Span,
    ) -> Option<(ExecDeriveItem, ColSpec)> {
        let source = match args.first() {
            Some(CallArg::Positional(Expr {
                kind: ExprKind::DotField(m),
                ..
            })) => m.name.clone(),
            _ => {
                self.diags.push(
                    Diagnostic::error(
                        DiagCode::TypeError,
                        "`coarsen` expects `.col, allow: [...], other: \"...\"`",
                    )
                    .with_span(span),
                );
                return None;
            }
        };
        let Some(src_col) = in_tt.find_col(&source) else {
            self.diags.push(
                Diagnostic::error(
                    DiagCode::TypeError,
                    format!("unknown column `.{source}` in `coarsen`"),
                )
                .with_span(span),
            );
            return None;
        };
        let is_text = matches!(&src_col.ty, ScalarTy::Text)
            || matches!(&src_col.ty, ScalarTy::Option(inner) if matches!(inner.as_ref(), ScalarTy::Text));
        if !is_text {
            self.diags.push(
                Diagnostic::error(
                    DiagCode::TypeError,
                    format!(
                        "`coarsen` requires a `Text` or `Text?` column, found `{:?}` on `.{source}`",
                        src_col.ty
                    ),
                )
                .with_span(span),
            );
            return None;
        }
        let mut valid = true;
        let mut allow_arg: Option<&Expr> = None;
        let mut other_arg: Option<&Expr> = None;
        for arg in args.iter().skip(1) {
            match arg {
                CallArg::Positional(e) => {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::TypeError,
                            "`coarsen` expects named arguments `allow: [...]` and `other: \"...\"` after `.col`",
                        )
                        .with_span(e.span),
                    );
                    valid = false;
                }
                CallArg::Named { name, value, .. } if name.name == "allow" => {
                    if allow_arg.is_some() {
                        self.diags.push(
                            Diagnostic::error(
                                DiagCode::TypeError,
                                "duplicate `allow:` argument in `coarsen`",
                            )
                            .with_span(name.span),
                        );
                        valid = false;
                    } else {
                        allow_arg = Some(value);
                    }
                }
                CallArg::Named { name, value, .. } if name.name == "other" => {
                    if other_arg.is_some() {
                        self.diags.push(
                            Diagnostic::error(
                                DiagCode::TypeError,
                                "duplicate `other:` argument in `coarsen`",
                            )
                            .with_span(name.span),
                        );
                        valid = false;
                    } else {
                        other_arg = Some(value);
                    }
                }
                CallArg::Named { name, .. } => {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::TypeError,
                            format!("unknown argument `{}:` in `coarsen`", name.name),
                        )
                        .with_span(name.span),
                    );
                    valid = false;
                }
            }
        }
        let mut allow = Vec::new();
        match allow_arg {
            Some(Expr {
                kind: ExprKind::List(items),
                span: list_span,
            }) => {
                for it in items {
                    if let ExprKind::Text { value: s, .. } = &it.kind {
                        allow.push(s.clone());
                    } else {
                        self.diags.push(
                            Diagnostic::error(
                                DiagCode::PrivacyError,
                                "`coarsen` `allow:` entries must be compile-time string literals",
                            )
                            .with_span(it.span),
                        );
                        valid = false;
                    }
                }
                if allow.is_empty() && valid {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::TypeError,
                            "`coarsen` requires a non-empty `allow: [...]` list",
                        )
                        .with_span(*list_span),
                    );
                    valid = false;
                }
            }
            Some(other_expr) => {
                self.diags.push(
                    Diagnostic::error(
                        DiagCode::TypeError,
                        "`coarsen` requires `allow: [...]` list literal",
                    )
                    .with_span(other_expr.span),
                );
                valid = false;
            }
            None => {
                self.diags.push(
                    Diagnostic::error(
                        DiagCode::TypeError,
                        "`coarsen` requires `allow: [...]` list literal",
                    )
                    .with_span(span),
                );
                valid = false;
            }
        }
        let other = match other_arg {
            Some(Expr {
                kind: ExprKind::Text { value: s, .. },
                ..
            }) => s.clone(),
            Some(other_expr) => {
                self.diags.push(
                    Diagnostic::error(
                        DiagCode::PrivacyError,
                        "`coarsen` `other:` must be a compile-time string literal",
                    )
                    .with_span(other_expr.span),
                );
                valid = false;
                String::new()
            }
            None => {
                self.diags.push(
                    Diagnostic::error(
                        DiagCode::TypeError,
                        "`coarsen` requires `other: \"...\"` string literal",
                    )
                    .with_span(span),
                );
                valid = false;
                String::new()
            }
        };
        if !valid {
            return None;
        }
        let spec = ColSpec {
            name: out_col.to_string(),
            ty: ScalarTy::Text,
            // Always produces non-null `Text`; clears under `suppress_small_groups` & `suppress_small_cells`.
            tags: src_col.tags.clone(),
            bucketed: true,
            agg_kind: AggKind::Raw,
        };
        Some((
            ExecDeriveItem::CoarsenCol {
                name: out_col.to_string(),
                source,
                allow,
                other,
            },
            spec,
        ))
    }

    fn parse_dedupe_order_spec(
        &mut self,
        expr: &Expr,
        in_tt: &TableTy,
    ) -> Option<(Ident, SortDir)> {
        match &expr.kind {
            ExprKind::DotField(m) => {
                if in_tt.find_col(&m.name).is_some() {
                    Some((m.name.clone(), SortDir::Asc))
                } else {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::TypeError,
                            format!("unknown `order_by` column `.{}` in `dedupe_by`", m.name),
                        )
                        .with_span(m.span),
                    );
                    None
                }
            }
            ExprKind::Call { callee, args } if matches!(&callee.kind, ExprKind::Ident(n) if n == "asc" || n == "desc") =>
            {
                let ExprKind::Ident(fname) = &callee.kind else {
                    return None;
                };
                let dir = if fname == "desc" {
                    SortDir::Desc
                } else {
                    SortDir::Asc
                };
                if args.len() != 1 {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::TypeError,
                            format!("`{fname}(.col)` in `dedupe_by(order_by: ...)` expects 1 `.column` argument"),
                        )
                        .with_span(expr.span),
                    );
                    return None;
                }
                let Some(CallArg::Positional(Expr {
                    kind: ExprKind::DotField(m),
                    ..
                })) = args.first()
                else {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::TypeError,
                            format!("`{fname}(.col)` in `dedupe_by(order_by: ...)` expects a `.column` argument"),
                        )
                        .with_span(expr.span),
                    );
                    return None;
                };
                if in_tt.find_col(&m.name).is_some() {
                    Some((m.name.clone(), dir))
                } else {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::TypeError,
                            format!("unknown `order_by` column `.{}` in `dedupe_by`", m.name),
                        )
                        .with_span(m.span),
                    );
                    None
                }
            }
            _ => {
                self.diags.push(
                    Diagnostic::error(
                        DiagCode::TypeError,
                        "`dedupe_by` `order_by:` entries must be `.col`, `asc(.col)`, or `desc(.col)`",
                    )
                    .with_span(expr.span),
                );
                None
            }
        }
    }

    fn check_dedupe_by_verb(
        &mut self,
        in_plan: ExecPlan,
        in_tt: TableTy,
        outer_tags: TagSet,
        args: &[CallArg],
        span: Span,
    ) -> (ExecExpr, LTy) {
        let mut keys: Vec<Ident> = Vec::new();
        let mut key_tags = TagSet::empty();
        let mut order_by: Vec<(Ident, SortDir)> = Vec::new();
        let mut ord_tags = TagSet::empty();
        let mut keep = DedupeKeep::First;
        let mut seen_order = false;
        let mut seen_keep = false;
        let mut saw_pos_err = false;

        for arg in args {
            match arg {
                CallArg::Positional(Expr {
                    kind: ExprKind::DotField(m),
                    ..
                }) => {
                    if let Some(c) = in_tt.find_col(&m.name) {
                        if keys.contains(&m.name) {
                            self.diags.push(
                                Diagnostic::error(
                                    DiagCode::TypeError,
                                    format!("duplicate key column `.{}` in `dedupe_by`", m.name),
                                )
                                .with_span(m.span),
                            );
                        } else {
                            key_tags = key_tags.union(&c.tags);
                            keys.push(m.name.clone());
                        }
                    } else {
                        saw_pos_err = true;
                        self.diags.push(
                            Diagnostic::error(
                                DiagCode::TypeError,
                                format!("unknown key column `.{}` in `dedupe_by`", m.name),
                            )
                            .with_span(m.span),
                        );
                    }
                }
                CallArg::Positional(e) => {
                    saw_pos_err = true;
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::TypeError,
                            "`dedupe_by` positional key arguments must be `.column` references",
                        )
                        .with_span(e.span),
                    );
                }
                CallArg::Named { name, value, .. } if name.name == "order_by" => {
                    if seen_order {
                        self.diags.push(
                            Diagnostic::error(
                                DiagCode::TypeError,
                                "duplicate `order_by:` argument in `dedupe_by`",
                            )
                            .with_span(name.span),
                        );
                        continue;
                    }
                    seen_order = true;
                    match &value.kind {
                        ExprKind::List(items) => {
                            if items.is_empty() {
                                self.diags.push(
                                    Diagnostic::error(
                                        DiagCode::TypeError,
                                        "`dedupe_by` `order_by: [...]` cannot be empty",
                                    )
                                    .with_span(value.span),
                                );
                            }
                            for it in items {
                                if let Some((col, dir)) = self.parse_dedupe_order_spec(it, &in_tt) {
                                    if let Some(c) = in_tt.find_col(&col) {
                                        ord_tags = ord_tags.union(&c.tags);
                                    }
                                    order_by.push((col, dir));
                                }
                            }
                        }
                        _ => {
                            if let Some((col, dir)) = self.parse_dedupe_order_spec(value, &in_tt) {
                                if let Some(c) = in_tt.find_col(&col) {
                                    ord_tags = ord_tags.union(&c.tags);
                                }
                                order_by.push((col, dir));
                            }
                        }
                    }
                }
                CallArg::Named { name, value, .. } if name.name == "keep" => {
                    if seen_keep {
                        self.diags.push(
                            Diagnostic::error(
                                DiagCode::TypeError,
                                "duplicate `keep:` argument in `dedupe_by`",
                            )
                            .with_span(name.span),
                        );
                        continue;
                    }
                    seen_keep = true;
                    match &value.kind {
                        ExprKind::Atom(a) if a == "first" => keep = DedupeKeep::First,
                        ExprKind::Atom(a) if a == "last" => keep = DedupeKeep::Last,
                        _ => {
                            self.diags.push(
                                Diagnostic::error(
                                    DiagCode::TypeError,
                                    "`dedupe_by` `keep:` must be `:first` or `:last`",
                                )
                                .with_span(value.span),
                            );
                        }
                    }
                }
                CallArg::Named { name, .. } => {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::TypeError,
                            format!("unknown argument `{}:` in `dedupe_by`", name.name),
                        )
                        .with_span(name.span),
                    );
                }
            }
        }

        if keys.is_empty() && !saw_pos_err {
            self.diags.push(
                Diagnostic::error(
                    DiagCode::TypeError,
                    "`dedupe_by` requires at least one `.key` column argument",
                )
                .with_span(span),
            );
        }

        let mut out_tt = in_tt;
        for c in &mut out_tt.cols {
            c.agg_kind = AggKind::Raw;
        }
        out_tt.row_tags = out_tt
            .row_tags
            .union(&key_tags)
            .union(&ord_tags)
            .union(&out_tt.order_tags);
        out_tt.grouped_by = None;
        out_tt.summarized = false;
        out_tt.distinct_by = None;
        (
            ExecExpr::Rel(Box::new(ExecPlan::DedupeBy {
                input: Box::new(in_plan),
                keys,
                order_by,
                keep,
            })),
            LTy::new(Ty::Table(out_tt), outer_tags),
        )
    }

    fn check_summarize_verb(
        &mut self,
        in_plan: ExecPlan,
        in_tt: TableTy,
        outer_tags: TagSet,
        args: &[CallArg],
        span: Span,
        env: &HashMap<Ident, VarBinding>,
    ) -> (ExecExpr, LTy) {
        let group_keys = if in_tt.summarized {
            Vec::new()
        } else {
            in_tt.grouped_by.clone().unwrap_or_default()
        };
        let mut out_cols = Vec::new();
        let mut base_ctx = in_tt.row_tags.clone();
        for gk in &group_keys {
            if let Some(c) = in_tt.find_col(gk) {
                base_ctx = base_ctx.union(&c.tags);
                out_cols.push(ColSpec {
                    name: c.name.clone(),
                    ty: c.ty.clone(),
                    tags: c.tags.clone(),
                    bucketed: c.bucketed,
                    agg_kind: AggKind::GroupKey,
                });
            }
        }

        let group_key_cols = out_cols.clone();
        let mut agg_items = Vec::new();
        let mut post_derives: Vec<ExecDeriveItem> = Vec::new();
        let mut post_drops: Vec<Ident> = Vec::new();
        let mut distinct_key: Option<Ident> = None;

        for arg in args {
            let CallArg::Named { name, value, .. } = arg else {
                self.diags.push(
                    Diagnostic::error(
                        DiagCode::TypeError,
                        "`summarize` expects `name: agg(...)` arguments",
                    )
                    .with_span(arg.span()),
                );
                continue;
            };
            if is_direct_agg_call(value) {
                if let Some((item, spec, dk)) =
                    self.check_agg_call(&name.name, value, &in_tt, &base_ctx, env)
                {
                    if distinct_key.is_none() {
                        distinct_key = dk;
                    }
                    agg_items.push(item);
                    upsert_col(&mut out_cols, spec);
                }
                continue;
            }

            let mut extracted_specs: Vec<ColSpec> = Vec::new();
            let rewritten = self.extract_post_agg_calls(
                value,
                &in_tt,
                &base_ctx,
                env,
                &mut agg_items,
                &mut distinct_key,
                &mut extracted_specs,
                &mut post_drops,
            );
            let mut expr_cols = group_key_cols.clone();
            expr_cols.extend(extracted_specs.iter().cloned());
            let (re, re_ty, re_tags) =
                self.check_row_expr(&rewritten, &expr_cols, env, None, false);
            let scalar_ty = re_ty.to_scalar_ty().unwrap_or_else(|| {
                self.diags.push(
                    Diagnostic::error(
                        DiagCode::TypeError,
                        format!("summary expression `{}` must have a scalar type", name.name),
                    )
                    .with_span(value.span),
                );
                ScalarTy::Unit
            });
            let mut blending_budget = base_ctx.clone();
            for s in &extracted_specs {
                blending_budget = blending_budget.union(&s.tags);
            }
            let has_non_blending = extracted_specs
                .iter()
                .any(|s| s.agg_kind == AggKind::NonBlending);
            let has_blending = extracted_specs
                .iter()
                .any(|s| s.agg_kind == AggKind::Blending);
            let final_agg_kind = if has_non_blending || !re_tags.is_subset(&blending_budget) {
                AggKind::NonBlending
            } else if has_blending {
                AggKind::Blending
            } else {
                AggKind::Raw
            };
            let final_spec = ColSpec {
                name: name.name.clone(),
                ty: scalar_ty,
                tags: re_tags,
                bucketed: false,
                agg_kind: final_agg_kind,
            };
            post_derives.push(ExecDeriveItem::SummaryCol {
                name: name.name.clone(),
                expr: Box::new(re),
                agg_kind: final_agg_kind,
            });
            upsert_col(&mut out_cols, final_spec);
        }

        if agg_items.is_empty() {
            self.diags.push(
                Diagnostic::error(
                    DiagCode::TypeError,
                    "`summarize` requires at least one aggregate",
                )
                .with_span(span),
            );
        }

        let summarize_in = if !group_keys.is_empty() && !matches!(in_plan, ExecPlan::GroupBy { .. })
        {
            ExecPlan::GroupBy {
                input: Box::new(in_plan),
                keys: group_keys.clone(),
            }
        } else if group_keys.is_empty() && in_tt.summarized {
            ExecPlan::GroupBy {
                input: Box::new(in_plan),
                keys: Vec::new(),
            }
        } else {
            in_plan
        };

        let mut plan = ExecPlan::Summarize {
            input: Box::new(summarize_in),
            aggs: agg_items,
            distinct_key: distinct_key.clone(),
        };
        if !post_derives.is_empty() {
            plan = ExecPlan::Derive {
                input: Box::new(plan),
                items: post_derives,
            };
            plan = ExecPlan::Drop {
                input: Box::new(plan),
                cols: post_drops,
            };
        }

        let dk_tags = distinct_key
            .as_deref()
            .and_then(|dk| in_tt.find_col(dk).map(|c| c.tags.clone()))
            .unwrap_or_default();
        let out_tt = TableTy {
            cols: out_cols,
            row_tags: base_ctx.union(&dk_tags),
            order_tags: TagSet::empty(),
            grouped_by: Some(group_keys),
            summarized: true,
            distinct_by: distinct_key,
        };
        (
            ExecExpr::Rel(Box::new(plan)),
            LTy::new(Ty::Table(out_tt), outer_tags),
        )
    }

    fn check_agg_call(
        &mut self,
        out_name: &str,
        expr: &Expr,
        in_tt: &TableTy,
        base_ctx: &TagSet,
        env: &HashMap<Ident, VarBinding>,
    ) -> Option<(ExecAggItem, ColSpec, Option<Ident>)> {
        let ExprKind::Call { callee, args } = &expr.kind else {
            self.diags.push(
                Diagnostic::error(
                    DiagCode::TypeError,
                    "`summarize` entries must be aggregate calls (`count`, `sum`, `mean`, ...)",
                )
                .with_span(expr.span),
            );
            return None;
        };
        let ExprKind::Ident(agg_name) = &callee.kind else {
            self.diags.push(
                Diagnostic::error(DiagCode::TypeError, "invalid aggregate name")
                    .with_span(callee.span),
            );
            return None;
        };

        if agg_name == "count" {
            return Some((
                ExecAggItem {
                    name: out_name.to_string(),
                    op: ExecAggOp::Core(AggOp::Count),
                    arg: None,
                },
                ColSpec {
                    name: out_name.to_string(),
                    ty: ScalarTy::Int,
                    tags: base_ctx.clone(),
                    bucketed: false,
                    agg_kind: AggKind::Blending,
                },
                None,
            ));
        }

        let Some(CallArg::Positional(arg0)) = args.first() else {
            self.diags.push(
                Diagnostic::error(
                    DiagCode::TypeError,
                    format!("`{agg_name}` requires a column/expression argument"),
                )
                .with_span(expr.span),
            );
            return None;
        };
        let (re, re_ty, re_tags) = self.check_row_expr(arg0, &in_tt.cols, env, None, false);
        let s_ty = re_ty.to_scalar_ty().unwrap_or(ScalarTy::Unit);
        let distinct_col = if agg_name == "count_distinct" {
            if let ExecRowExpr::Col(c) = &re {
                Some(c.clone())
            } else {
                None
            }
        } else {
            None
        };

        let (op, out_ty) = match agg_name.as_str() {
            "count_if" => {
                if re_ty != Ty::Bool {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::TypeError,
                            format!("`count_if` expects a `Bool` condition, found `{re_ty:?}`"),
                        )
                        .with_span(arg0.span),
                    );
                }
                (ExecAggOp::CountIf, ScalarTy::Int)
            }
            "count_distinct" => (ExecAggOp::Core(AggOp::CountDistinct), ScalarTy::Int),
            "sum" => {
                let num = numeric_core_of_scalar(&s_ty).unwrap_or(ScalarTy::Int);
                (ExecAggOp::Core(AggOp::Sum), num)
            }
            "mean" | "median" => {
                let op = if agg_name == "mean" {
                    AggOp::Mean
                } else {
                    AggOp::Median
                };
                let out_t = match numeric_core_of_scalar(&s_ty) {
                    Some(ScalarTy::Int) | None => ScalarTy::Option(Box::new(ScalarTy::Float)),
                    Some(num) => ScalarTy::Option(Box::new(num)),
                };
                (ExecAggOp::Core(op), out_t)
            }
            "stddev" | "variance" => {
                let op = if agg_name == "stddev" {
                    AggOp::Stddev
                } else {
                    AggOp::Variance
                };
                (
                    ExecAggOp::Core(op),
                    ScalarTy::Option(Box::new(ScalarTy::Float)),
                )
            }
            "percentile" => {
                let q = match args.get(1) {
                    Some(CallArg::Positional(Expr {
                        kind: ExprKind::Decimal(raw),
                        ..
                    })) => raw.parse::<f64>().unwrap_or(0.5),
                    _ => {
                        self.diags.push(
                            Diagnostic::error(
                                DiagCode::TypeError,
                                "`percentile(.col, q)` requires a float quantile `q` in [0.0, 1.0]",
                            )
                            .with_span(expr.span),
                        );
                        0.5
                    }
                };
                (
                    ExecAggOp::Core(AggOp::Percentile(Float64::from_f64(q))),
                    ScalarTy::Option(Box::new(ScalarTy::Float)),
                )
            }
            "min" => (ExecAggOp::Core(AggOp::Min), ensure_option_scalar(&s_ty)),
            "max" => (ExecAggOp::Core(AggOp::Max), ensure_option_scalar(&s_ty)),
            "first" => (ExecAggOp::Core(AggOp::First), ensure_option_scalar(&s_ty)),
            "last" => (ExecAggOp::Core(AggOp::Last), ensure_option_scalar(&s_ty)),
            _ => {
                self.diags.push(
                    Diagnostic::error(
                        DiagCode::TypeError,
                        format!("unknown aggregate `{agg_name}`"),
                    )
                    .with_span(callee.span),
                );
                return None;
            }
        };

        let agg_kind = if op.is_blending() {
            AggKind::Blending
        } else {
            AggKind::NonBlending
        };
        let extra_order = if op.is_order_sensitive() {
            &in_tt.order_tags
        } else {
            &TagSet::empty()
        };
        let col_tags = re_tags.union(base_ctx).union(extra_order);
        Some((
            ExecAggItem {
                name: out_name.to_string(),
                op,
                arg: Some(re),
            },
            ColSpec {
                name: out_name.to_string(),
                ty: out_ty,
                tags: col_tags,
                bucketed: false,
                agg_kind,
            },
            distinct_col,
        ))
    }

    fn check_suppress_verb(
        &mut self,
        in_plan: ExecPlan,
        in_tt: TableTy,
        outer_tags: TagSet,
        args: &[CallArg],
        span: Span,
    ) -> (ExecExpr, LTy) {
        if !in_tt.summarized {
            self.diags.push(
                Diagnostic::error(
                    DiagCode::PrivacyError,
                    "`suppress_small_groups` requires a summarized table (after `summarize(...)`)",
                )
                .with_span(span),
            );
        }
        let mut min_k: u64 = 5;
        let mut distinct_by: Option<Ident> = None;
        let mut mode = SuppressMode::Drop;
        for arg in args {
            if let CallArg::Named { name, value, .. } = arg {
                match name.name.as_str() {
                    "min" => {
                        if let ExprKind::Int(raw) = &value.kind {
                            min_k = raw.replace('_', "").parse().unwrap_or(0);
                        } else {
                            self.diags.push(
                                Diagnostic::error(
                                    DiagCode::PrivacyError,
                                    "`min:` must be a constant integer",
                                )
                                .with_span(value.span),
                            );
                        }
                    }
                    "distinct_by" => {
                        if let ExprKind::DotField(m) = &value.kind {
                            distinct_by = Some(m.name.clone());
                        }
                    }
                    "mode" => {
                        if let ExprKind::Atom(a) = &value.kind {
                            match a.as_str() {
                                "drop" => mode = SuppressMode::Drop,
                                "mask" => mode = SuppressMode::MaskComplementary,
                                other => self.diags.push(
                                    Diagnostic::error(
                                        DiagCode::PrivacyError,
                                        format!("unknown `suppress_small_groups` mode `:{other}` (expected `:drop` or `:mask`)"),
                                    )
                                    .with_span(value.span),
                                ),
                            }
                        }
                    }
                    _ => {}
                }
            }
        }
        let policy_floor = self
            .resolved
            .policy
            .as_ref()
            .and_then(|p| p.min_group_size.to_u64())
            .unwrap_or(5)
            .max(5);
        if min_k < policy_floor {
            self.diags.push(
                Diagnostic::error(
                    DiagCode::PrivacyError,
                    format!(
                        "`suppress_small_groups(min: {min_k})` is below the required minimum group floor ({policy_floor})"
                    ),
                )
                .with_span(span),
            );
        }
        if let Some(ref req_dk) = distinct_by
            && in_tt.distinct_by.as_ref() != Some(req_dk)
        {
            self.diags.push(
                Diagnostic::error(
                    DiagCode::PrivacyError,
                    format!(
                        "`suppress_small_groups(distinct_by: .{req_dk})` requires a matching `count_distinct(.{req_dk})` in `summarize`"
                    ),
                )
                .with_span(span),
            );
        }

        // Apply exact declassification semantics matching `src/core/check.rs` and `privacy.md`:
        // Clears `order_tags`, `Blending` aggregates, and `bucketed` `GroupKey`s.
        // Keeps non-bucketed `GroupKey` tags (in both column and `row_tags`) and `NonBlending`
        // (`median`, `percentile`, `min`, `max`, `first`, `last`) tagged, resetting `agg_kind` to `Raw`.
        let raw_key_tags = TagSet::union_list(
            in_tt
                .cols
                .iter()
                .filter(|c| c.agg_kind == AggKind::GroupKey && !c.bucketed)
                .map(|c| &c.tags),
        );
        let mut out_cols = Vec::with_capacity(in_tt.cols.len());
        for c in &in_tt.cols {
            let new_tags = match c.agg_kind {
                AggKind::Blending => TagSet::empty(),
                AggKind::GroupKey if c.bucketed => TagSet::empty(),
                AggKind::GroupKey | AggKind::NonBlending | AggKind::Raw => c.tags.clone(),
            };
            let new_ty = match (mode, c.agg_kind) {
                (SuppressMode::MaskComplementary, AggKind::Blending | AggKind::NonBlending) => {
                    ensure_option_scalar(&c.ty)
                }
                _ => c.ty.clone(),
            };
            out_cols.push(ColSpec {
                name: c.name.clone(),
                ty: new_ty,
                tags: new_tags,
                bucketed: false,
                agg_kind: AggKind::Raw,
            });
        }
        let out_tt = TableTy {
            cols: out_cols,
            row_tags: raw_key_tags,
            order_tags: TagSet::empty(),
            grouped_by: None,
            summarized: false,
            distinct_by: None,
        };
        (
            ExecExpr::Rel(Box::new(ExecPlan::SuppressSmallGroups {
                input: Box::new(in_plan),
                min_k: BigInt::from(min_k),
                distinct_by,
                mode,
            })),
            LTy::new(Ty::Table(out_tt), outer_tags),
        )
    }

    #[expect(
        clippy::too_many_arguments,
        reason = "shuffle checks seed expression in caller scope while clearing order_tags"
    )]
    fn check_shuffle_verb(
        &mut self,
        in_plan: ExecPlan,
        in_tt: TableTy,
        outer_tags: TagSet,
        args: &[CallArg],
        span: Span,
        env: &HashMap<Ident, VarBinding>,
        pc: &TagSet,
        scope: LocalScopeKind,
        ret_ctx: Option<(&str, Option<&Ty>)>,
    ) -> (ExecExpr, LTy) {
        let mut seed_arg: Option<&Expr> = None;
        for arg in args {
            match arg {
                CallArg::Named { name, value, .. } if name.name == "seed" => {
                    if seed_arg.is_some() {
                        self.diags.push(
                            Diagnostic::error(
                                DiagCode::TypeError,
                                "duplicate `seed:` argument in `shuffle`",
                            )
                            .with_span(name.span),
                        );
                    } else {
                        seed_arg = Some(value);
                    }
                }
                other => {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::TypeError,
                            "`shuffle` expects a single named argument `seed: Int`",
                        )
                        .with_span(other.span()),
                    );
                }
            }
        }
        let seed_ex = if let Some(se) = seed_arg {
            let (ex, lty) = self.check_expr(se, env, Some(&Ty::Int), pc, scope, ret_ctx);
            if lty.ty != Ty::Int {
                self.diags.push(
                    Diagnostic::error(
                        DiagCode::TypeError,
                        format!("`shuffle(seed: ...)` requires `Int`, found `{:?}`", lty.ty),
                    )
                    .with_span(se.span),
                );
            }
            let mut out_tt = in_tt;
            for c in &mut out_tt.cols {
                c.agg_kind = AggKind::Raw;
            }
            out_tt.order_tags = lty.effective_tags();
            out_tt.grouped_by = None;
            out_tt.summarized = false;
            out_tt.distinct_by = None;
            return (
                ExecExpr::Rel(Box::new(ExecPlan::Shuffle {
                    input: Box::new(in_plan),
                    seed: Box::new(ex),
                })),
                LTy::new(Ty::Table(out_tt), outer_tags),
            );
        } else {
            self.diags.push(
                Diagnostic::error(DiagCode::TypeError, "`shuffle` requires `seed: Int`")
                    .with_span(span),
            );
            ExecExpr::Lit(Literal::int(0i64))
        };
        let mut out_tt = in_tt;
        for c in &mut out_tt.cols {
            c.agg_kind = AggKind::Raw;
        }
        out_tt.order_tags = TagSet::empty();
        out_tt.grouped_by = None;
        out_tt.summarized = false;
        out_tt.distinct_by = None;
        (
            ExecExpr::Rel(Box::new(ExecPlan::Shuffle {
                input: Box::new(in_plan),
                seed: Box::new(seed_ex),
            })),
            LTy::new(Ty::Table(out_tt), outer_tags),
        )
    }

    fn check_suppress_cells_verb(
        &mut self,
        in_plan: ExecPlan,
        in_tt: TableTy,
        outer_tags: TagSet,
        args: &[CallArg],
        span: Span,
    ) -> (ExecExpr, LTy) {
        let mut by_cols: Vec<Ident> = Vec::new();
        let mut saw_by = false;
        let mut min_k_opt: Option<u64> = None;
        let mut distinct_by: Option<Ident> = None;

        for arg in args {
            match arg {
                CallArg::Named { name, value, .. } => match name.name.as_str() {
                    "by" => {
                        if saw_by {
                            self.diags.push(
                                Diagnostic::error(
                                    DiagCode::TypeError,
                                    "duplicate `by:` argument in `suppress_small_cells`",
                                )
                                .with_span(name.span),
                            );
                            continue;
                        }
                        saw_by = true;
                        match &value.kind {
                            ExprKind::List(items) => {
                                for it in items {
                                    if let ExprKind::DotField(m) = &it.kind {
                                        if in_tt.find_col(&m.name).is_none() {
                                            self.diags.push(
                                                Diagnostic::error(
                                                    DiagCode::TypeError,
                                                    format!(
                                                        "unknown column `.{}` in `suppress_small_cells(by: ...)`",
                                                        m.name
                                                    ),
                                                )
                                                .with_span(m.span),
                                            );
                                        } else if !by_cols.contains(&m.name) {
                                            by_cols.push(m.name.clone());
                                        }
                                    } else {
                                        self.diags.push(
                                            Diagnostic::error(
                                                DiagCode::TypeError,
                                                "`suppress_small_cells(by: [...])` entries must be `.column` references",
                                            )
                                            .with_span(it.span),
                                        );
                                    }
                                }
                            }
                            _ => {
                                self.diags.push(
                                    Diagnostic::error(
                                        DiagCode::TypeError,
                                        "`suppress_small_cells` expects `by: [.col1, ...]`",
                                    )
                                    .with_span(value.span),
                                );
                            }
                        }
                    }
                    "min" => {
                        if let ExprKind::Int(raw) = &value.kind {
                            match raw.replace('_', "").parse::<u64>() {
                                Ok(n) => min_k_opt = Some(n),
                                Err(_) => {
                                    self.diags.push(
                                        Diagnostic::error(
                                            DiagCode::PrivacyError,
                                            "`min:` in `suppress_small_cells` must be a non-negative integer literal",
                                        )
                                        .with_span(value.span),
                                    );
                                }
                            }
                        } else {
                            self.diags.push(
                                Diagnostic::error(
                                    DiagCode::PrivacyError,
                                    "`min:` in `suppress_small_cells` must be a constant integer literal",
                                )
                                .with_span(value.span),
                            );
                        }
                    }
                    "distinct_by" => {
                        if let ExprKind::DotField(m) = &value.kind {
                            if in_tt.find_col(&m.name).is_none() {
                                self.diags.push(
                                    Diagnostic::error(
                                        DiagCode::TypeError,
                                        format!(
                                            "unknown column `.{}` in `suppress_small_cells(distinct_by: ...)`",
                                            m.name
                                        ),
                                    )
                                    .with_span(m.span),
                                );
                            }
                            distinct_by = Some(m.name.clone());
                        } else {
                            self.diags.push(
                                Diagnostic::error(
                                    DiagCode::TypeError,
                                    "`suppress_small_cells(distinct_by: ...)` expects a `.column` reference",
                                )
                                .with_span(value.span),
                            );
                        }
                    }
                    other => {
                        self.diags.push(
                            Diagnostic::error(
                                DiagCode::TypeError,
                                format!("unknown argument `{other}:` in `suppress_small_cells`"),
                            )
                            .with_span(name.span),
                        );
                    }
                },
                CallArg::Positional(e) => {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::TypeError,
                            "`suppress_small_cells` expects named arguments `by: [...], min: k`",
                        )
                        .with_span(e.span),
                    );
                }
            }
        }

        if !saw_by || by_cols.is_empty() {
            self.diags.push(
                Diagnostic::error(
                    DiagCode::TypeError,
                    "`suppress_small_cells` requires a non-empty `by: [.col1, ...]` quasi-identifier list",
                )
                .with_span(span),
            );
        }

        let min_k = match min_k_opt {
            Some(n) => n,
            None => {
                if !args
                    .iter()
                    .any(|a| matches!(a, CallArg::Named { name, .. } if name.name == "min"))
                {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::PrivacyError,
                            "`suppress_small_cells` requires a constant integer `min: k`",
                        )
                        .with_span(span),
                    );
                }
                0
            }
        };

        let policy_floor = self
            .resolved
            .policy
            .as_ref()
            .and_then(|p| p.min_group_size.to_u64())
            .unwrap_or(2)
            .max(2);
        if min_k < policy_floor {
            self.diags.push(
                Diagnostic::error(
                    DiagCode::PrivacyError,
                    format!(
                        "`suppress_small_cells(min: {min_k})` is below the required minimum cell floor ({policy_floor})"
                    ),
                )
                .with_span(span),
            );
        }

        for c in &in_tt.cols {
            if c.tags.contains("pii") || c.tags.contains("secret") {
                self.diags.push(
                    Diagnostic::error(
                        DiagCode::PrivacyError,
                        format!(
                            "`suppress_small_cells` cannot run while column `.{}` still carries `[pii]` or `[secret]`",
                            c.name
                        ),
                    )
                    .with_span(span)
                    .with_hint(
                        "drop, select away, redact, or pseudonymize `[pii]`/`[secret]` columns before calling `suppress_small_cells`",
                    ),
                );
            }
        }

        let out_cols = in_tt
            .cols
            .iter()
            .map(|c| {
                let clear_ferpa = by_cols.contains(&c.name) || c.bucketed;
                ColSpec {
                    name: c.name.clone(),
                    ty: c.ty.clone(),
                    tags: if clear_ferpa {
                        c.tags.remove("ferpa")
                    } else {
                        c.tags.clone()
                    },
                    bucketed: c.bucketed,
                    agg_kind: AggKind::Raw,
                }
            })
            .collect();
        let out_tt = TableTy {
            cols: out_cols,
            row_tags: TagSet::empty(),
            order_tags: in_tt.order_tags,
            grouped_by: None,
            summarized: false,
            distinct_by: None,
        };
        (
            ExecExpr::Rel(Box::new(ExecPlan::SuppressSmallCells {
                input: Box::new(in_plan),
                by_cols,
                min_k: BigInt::from(min_k),
                distinct_by,
            })),
            LTy::new(Ty::Table(out_tt), outer_tags),
        )
    }

    #[expect(
        clippy::too_many_arguments,
        reason = "format_csv helper shares validation across method, pipe, and free-call syntax"
    )]
    fn check_format_csv_call(
        &mut self,
        tbl_ex: ExecExpr,
        tbl_tt: &TableTy,
        tbl_tags: &TagSet,
        rest_args: &[CallArg],
        span: Span,
        env: &HashMap<Ident, VarBinding>,
        pc: &TagSet,
        scope: LocalScopeKind,
        ret_ctx: Option<(&str, Option<&Ty>)>,
    ) -> (ExecExpr, LTy) {
        let mut san_arg: Option<&Expr> = None;
        for arg in rest_args {
            match arg {
                CallArg::Named { name, value, .. } if name.name == "sanitize_formulas" => {
                    if san_arg.is_some() {
                        self.diags.push(
                            Diagnostic::error(
                                DiagCode::TypeError,
                                "duplicate `sanitize_formulas:` argument in `format_csv`",
                            )
                            .with_span(name.span),
                        );
                    } else {
                        san_arg = Some(value);
                    }
                }
                other => {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::TypeError,
                            "`format_csv` only accepts optional `sanitize_formulas: Bool`",
                        )
                        .with_span(other.span()),
                    );
                }
            }
        }
        let mut out_tags = tbl_tt.total_tags().union(tbl_tags);
        let san_ex = if let Some(se) = san_arg {
            let (ex, lty) = self.check_expr(se, env, Some(&Ty::Bool), pc, scope, ret_ctx);
            if lty.ty != Ty::Bool {
                self.diags.push(
                    Diagnostic::error(
                        DiagCode::TypeError,
                        format!(
                            "`sanitize_formulas:` in `format_csv` must be `Bool`, found `{:?}`",
                            lty.ty
                        ),
                    )
                    .with_span(se.span),
                );
            }
            out_tags = out_tags.union(&lty.effective_tags());
            ex
        } else {
            let _ = span;
            ExecExpr::Lit(Literal::Bool(false))
        };
        (
            ExecExpr::Prim {
                op: ExecPrimOp::FormatCsv,
                args: vec![tbl_ex, san_ex],
            },
            LTy::new(Ty::Text, out_tags),
        )
    }

    fn check_window_verb(
        &mut self,
        in_plan: ExecPlan,
        in_tt: TableTy,
        outer_tags: TagSet,
        args: &[CallArg],
        span: Span,
        env: &HashMap<Ident, VarBinding>,
    ) -> (ExecExpr, LTy) {
        let mut over = Vec::new();
        let mut order = Vec::new();
        let mut win_named: Vec<(&ast::SpannedName, &Expr)> = Vec::new();

        for arg in args {
            let CallArg::Named { name, value, .. } = arg else {
                continue;
            };
            match name.name.as_str() {
                "over" => {
                    if let ExprKind::List(items) = &value.kind {
                        for it in items {
                            if let ExprKind::DotField(m) = &it.kind {
                                over.push(m.name.clone());
                            }
                        }
                    } else if let ExprKind::DotField(m) = &value.kind {
                        over.push(m.name.clone());
                    }
                }
                "order" => {
                    if let ExprKind::DotField(m) = &value.kind {
                        order.push((m.name.clone(), SortDir::Asc));
                    } else if let ExprKind::List(items) = &value.kind {
                        for it in items {
                            if let ExprKind::DotField(m) = &it.kind {
                                order.push((m.name.clone(), SortDir::Asc));
                            }
                        }
                    }
                }
                _ => win_named.push((name, value)),
            }
        }

        let mut ctx_tags = in_tt.row_tags.clone();
        for c in &over {
            if let Some(cs) = in_tt.find_col(c) {
                ctx_tags = ctx_tags.union(&cs.tags);
            }
        }
        for (c, _) in &order {
            if let Some(cs) = in_tt.find_col(c) {
                ctx_tags = ctx_tags.union(&cs.tags);
            }
        }

        let mut out_tt = in_tt;
        let mut win_items = Vec::new();
        let mut post_derives = Vec::new();
        let mut post_drops = Vec::new();

        for (name, val_expr) in win_named {
            // Direct window function call (`rolling_mean(...)`, `lag(...)`, `row_number()`, ...)
            if let Some((wfn, wty, wtags)) =
                self.try_parse_window_call(val_expr, &out_tt, &ctx_tags)
            {
                win_items.push(WindowItem {
                    name: name.name.clone(),
                    win_fn: wfn,
                    over: over.clone(),
                    order: order.clone(),
                });
                upsert_col(
                    &mut out_tt.cols,
                    ColSpec {
                        name: name.name.clone(),
                        ty: wty,
                        tags: wtags,
                        bucketed: false,
                        agg_kind: AggKind::Raw,
                    },
                );
                continue;
            }
            // Compound expression around a window call (e.g. `.students - lag(.students, 1)`)!
            if let ExprKind::Binary {
                op: BinOp::Sub,
                lhs,
                rhs,
            } = &val_expr.kind
                && let Some((wfn, wty, wtags)) = self.try_parse_window_call(rhs, &out_tt, &ctx_tags)
            {
                let tmp = self.fresh("win");
                win_items.push(WindowItem {
                    name: tmp.clone(),
                    win_fn: wfn,
                    over: over.clone(),
                    order: order.clone(),
                });
                let mut aug_cols = out_tt.cols.clone();
                aug_cols.push(ColSpec {
                    name: tmp.clone(),
                    ty: wty.clone(),
                    tags: wtags.clone(),
                    bucketed: false,
                    agg_kind: AggKind::Raw,
                });
                let (lre, lty, ltags) = self.check_row_expr(lhs, &aug_cols, env, None, false);
                let (opt_op, res_ty) = match lty {
                    Ty::Int => (
                        ExecPrimOp::OptSubInt,
                        ScalarTy::Option(Box::new(ScalarTy::Int)),
                    ),
                    Ty::Decimal => (
                        ExecPrimOp::OptSubDec,
                        ScalarTy::Option(Box::new(ScalarTy::Decimal)),
                    ),
                    _ => (
                        ExecPrimOp::OptSubFloat,
                        ScalarTy::Option(Box::new(ScalarTy::Float)),
                    ),
                };
                post_derives.push(ExecDeriveItem::ColExpr {
                    name: name.name.clone(),
                    expr: Box::new(ExecRowExpr::Prim {
                        op: opt_op,
                        args: vec![lre, ExecRowExpr::Col(tmp.clone())],
                    }),
                });
                post_drops.push(tmp);
                upsert_col(
                    &mut out_tt.cols,
                    ColSpec {
                        name: name.name.clone(),
                        ty: res_ty,
                        tags: ltags.union(&wtags),
                        bucketed: false,
                        agg_kind: AggKind::Raw,
                    },
                );
                continue;
            }

            self.diags.push(
                Diagnostic::error(
                    DiagCode::TypeError,
                    format!("unsupported window expression for `{}`", name.name),
                )
                .with_span(span),
            );
        }

        let mut plan = ExecPlan::Window {
            input: Box::new(in_plan),
            items: win_items,
        };
        if !post_derives.is_empty() {
            plan = ExecPlan::Derive {
                input: Box::new(plan),
                items: post_derives,
            };
            plan = ExecPlan::Drop {
                input: Box::new(plan),
                cols: post_drops,
            };
        }
        (
            ExecExpr::Rel(Box::new(plan)),
            LTy::new(Ty::Table(out_tt), outer_tags),
        )
    }

    fn try_parse_window_call(
        &self,
        expr: &Expr,
        in_tt: &TableTy,
        ctx_tags: &TagSet,
    ) -> Option<(WindowFn, ScalarTy, TagSet)> {
        let ExprKind::Call { callee, args } = &expr.kind else {
            return None;
        };
        let ExprKind::Ident(wname) = &callee.kind else {
            return None;
        };
        match wname.as_str() {
            "row_number" => Some((WindowFn::RowNumber, ScalarTy::Int, ctx_tags.clone())),
            "lag" | "lead" => {
                let col = match args.first()? {
                    CallArg::Positional(Expr {
                        kind: ExprKind::DotField(m),
                        ..
                    }) => m.name.clone(),
                    _ => return None,
                };
                let offset = match args.get(1) {
                    Some(CallArg::Positional(Expr {
                        kind: ExprKind::Int(raw),
                        ..
                    })) => raw.replace('_', "").parse::<u64>().unwrap_or(1),
                    _ => 1,
                };
                let c = in_tt.find_col(&col)?;
                let wfn = if wname == "lag" {
                    WindowFn::Lag {
                        col,
                        offset: BigInt::from(offset),
                    }
                } else {
                    WindowFn::Lead {
                        col,
                        offset: BigInt::from(offset),
                    }
                };
                Some((wfn, ensure_option_scalar(&c.ty), c.tags.union(ctx_tags)))
            }
            "rank" => {
                let col = match args.first()? {
                    CallArg::Positional(Expr {
                        kind: ExprKind::DotField(m),
                        ..
                    }) => m.name.clone(),
                    _ => return None,
                };
                let c = in_tt.find_col(&col)?;
                Some((
                    WindowFn::Rank { col },
                    ScalarTy::Int,
                    c.tags.union(ctx_tags),
                ))
            }
            "running_sum" => {
                let col = match args.first()? {
                    CallArg::Positional(Expr {
                        kind: ExprKind::DotField(m),
                        ..
                    }) => m.name.clone(),
                    _ => return None,
                };
                let c = in_tt.find_col(&col)?;
                let num = numeric_core_of_scalar(&c.ty)?;
                Some((WindowFn::RunningSum { col }, num, c.tags.union(ctx_tags)))
            }
            "rolling_mean" => {
                let col = match args.first()? {
                    CallArg::Positional(Expr {
                        kind: ExprKind::DotField(m),
                        ..
                    }) => m.name.clone(),
                    _ => return None,
                };
                let window_size = match args.get(1) {
                    Some(
                        CallArg::Positional(Expr {
                            kind: ExprKind::Int(raw),
                            ..
                        })
                        | CallArg::Named {
                            value:
                                Expr {
                                    kind: ExprKind::Int(raw),
                                    ..
                                },
                            ..
                        },
                    ) => raw.replace('_', "").parse::<u64>().unwrap_or(1),
                    _ => 1,
                };
                let c = in_tt.find_col(&col)?;
                numeric_core_of_scalar(&c.ty)?;
                Some((
                    WindowFn::RollingMean {
                        col,
                        window_size: BigInt::from(window_size),
                    },
                    ScalarTy::Option(Box::new(ScalarTy::Float)),
                    c.tags.union(ctx_tags),
                ))
            }
            _ => None,
        }
    }

    fn check_fill_gaps_verb(
        &mut self,
        in_plan: ExecPlan,
        in_tt: TableTy,
        outer_tags: TagSet,
        args: &[CallArg],
        span: Span,
    ) -> (ExecExpr, LTy) {
        let col = match args.first() {
            Some(CallArg::Positional(Expr {
                kind: ExprKind::DotField(m),
                ..
            })) => m.name.clone(),
            _ => {
                self.diags.push(
                    Diagnostic::error(
                        DiagCode::TypeError,
                        "`fill_gaps` expects `.time_col, every: duration, ...`",
                    )
                    .with_span(span),
                );
                String::new()
            }
        };
        let mut step_micros: i64 = MICROS_PER_MINUTE;
        let mut over = Vec::new();
        let mut fill = Vec::new();

        for arg in args {
            let CallArg::Named { name, value, .. } = arg else {
                continue;
            };
            match name.name.as_str() {
                "every" => {
                    if let Some(us) = eval_const_duration_micros(value) {
                        step_micros = us;
                    }
                }
                "over" => {
                    if let ExprKind::List(items) = &value.kind {
                        for it in items {
                            if let ExprKind::DotField(m) = &it.kind {
                                over.push(m.name.clone());
                            }
                        }
                    }
                }
                "fill" => {
                    if let ExprKind::Map(entries) = &value.kind {
                        for (k, v) in entries {
                            let cname = match &k.kind {
                                ExprKind::Ident(s) => s.clone(),
                                ExprKind::Text { value: s, .. } => s.clone(),
                                _ => continue,
                            };
                            let target_ty = in_tt.find_col(&cname).map(|c| match &c.ty {
                                ScalarTy::Option(inner) => inner.to_ty(),
                                other => other.to_ty(),
                            });
                            let (ve, _) = self.check_expr(
                                v,
                                &HashMap::new(),
                                target_ty.as_ref(),
                                &TagSet::empty(),
                                LocalScopeKind::Normal,
                                None,
                            );
                            if let Some(l) = ve.into_lit() {
                                fill.push((cname, l));
                            }
                        }
                    }
                }
                _ => {}
            }
        }

        // Columns NOT in `col`, `over`, or `fill` become `Option(T)` for synthesized gap rows.
        let mut out_tt = in_tt;
        for c in &mut out_tt.cols {
            let is_key = c.name == col || over.contains(&c.name);
            let is_filled = fill.iter().any(|(fnm, _)| *fnm == c.name);
            if !is_key && !is_filled {
                c.ty = ensure_option_scalar(&c.ty);
            }
        }
        (
            ExecExpr::Rel(Box::new(ExecPlan::FillGaps {
                input: Box::new(in_plan),
                col,
                step_micros: BigInt::from(step_micros),
                over,
                fill,
            })),
            LTy::new(Ty::Table(out_tt), outer_tags),
        )
    }

    fn check_pivot_wider_verb(
        &mut self,
        in_plan: ExecPlan,
        in_tt: TableTy,
        outer_tags: TagSet,
        args: &[CallArg],
        span: Span,
    ) -> (ExecExpr, LTy) {
        let mut names_from = String::new();
        let mut values_from = String::new();
        let mut static_cols = Vec::new();
        let mut fill_expr: Option<&Expr> = None;

        for arg in args {
            let CallArg::Named { name, value, .. } = arg else {
                continue;
            };
            match name.name.as_str() {
                "names_from" => {
                    if let ExprKind::DotField(m) = &value.kind {
                        names_from = m.name.clone();
                    }
                }
                "values_from" => {
                    if let ExprKind::DotField(m) = &value.kind {
                        values_from = m.name.clone();
                    }
                }
                "columns" => {
                    if let ExprKind::List(items) = &value.kind {
                        for it in items {
                            if let ExprKind::Text { value: s, .. } = &it.kind {
                                static_cols.push(s.clone());
                            }
                        }
                    }
                }
                "fill" => fill_expr = Some(value),
                _ => {}
            }
        }

        let val_col = in_tt.find_col(&values_from).cloned();
        let names_col = in_tt.find_col(&names_from).cloned();
        let (val_ty, val_tags) = match (&val_col, &names_col) {
            (Some(vc), Some(nc)) => (vc.ty.clone(), vc.tags.union(&nc.tags)),
            _ => {
                self.diags.push(
                    Diagnostic::error(
                        DiagCode::TypeError,
                        "`pivot_wider` requires valid `names_from:` and `values_from:` columns",
                    )
                    .with_span(span),
                );
                (ScalarTy::Decimal, TagSet::empty())
            }
        };
        let fill_lit = if let Some(fe) = fill_expr {
            let t = val_ty.to_ty();
            let (e, _) = self.check_expr(
                fe,
                &HashMap::new(),
                Some(&t),
                &TagSet::empty(),
                LocalScopeKind::Normal,
                None,
            );
            e.into_lit().unwrap_or(Literal::Unit)
        } else {
            Literal::NoneLit(val_ty.to_ty())
        };

        let mut out_cols: Vec<ColSpec> = in_tt
            .cols
            .iter()
            .filter(|c| c.name != names_from && c.name != values_from)
            .cloned()
            .collect();
        for sc in &static_cols {
            out_cols.push(ColSpec {
                name: sc.clone(),
                ty: val_ty.clone(),
                tags: val_tags.clone(),
                bucketed: false,
                agg_kind: AggKind::Raw,
            });
        }
        let out_tt = TableTy {
            cols: out_cols,
            row_tags: in_tt.row_tags,
            order_tags: TagSet::empty(),
            grouped_by: None,
            summarized: false,
            distinct_by: None,
        };
        (
            ExecExpr::Rel(Box::new(ExecPlan::PivotWider {
                input: Box::new(in_plan),
                names_from,
                values_from,
                static_cols,
                fill: fill_lit,
            })),
            LTy::new(Ty::Table(out_tt), outer_tags),
        )
    }

    fn check_pivot_longer_verb(
        &mut self,
        in_plan: ExecPlan,
        in_tt: TableTy,
        outer_tags: TagSet,
        args: &[CallArg],
        span: Span,
    ) -> (ExecExpr, LTy) {
        let mut melt_cols: Vec<Ident> = Vec::new();
        let mut names_to = String::new();
        let mut values_to = String::new();

        for arg in args {
            let CallArg::Named { name, value, .. } = arg else {
                continue;
            };
            match name.name.as_str() {
                "cols" => {
                    if let ExprKind::List(items) = &value.kind {
                        for it in items {
                            if let ExprKind::DotField(m) = &it.kind {
                                if melt_cols.contains(&m.name) {
                                    self.diags.push(
                                        Diagnostic::error(
                                            DiagCode::TypeError,
                                            format!(
                                                "duplicate column `.{}` in `pivot_longer` `cols:`",
                                                m.name
                                            ),
                                        )
                                        .with_span(m.span),
                                    );
                                } else {
                                    melt_cols.push(m.name.clone());
                                }
                            } else {
                                self.diags.push(
                                    Diagnostic::error(
                                        DiagCode::TypeError,
                                        "`pivot_longer` `cols:` items must be `.column` references",
                                    )
                                    .with_span(it.span),
                                );
                            }
                        }
                    } else {
                        self.diags.push(
                            Diagnostic::error(
                                DiagCode::TypeError,
                                "`pivot_longer` `cols:` must be a list of `.column` references",
                            )
                            .with_span(value.span),
                        );
                    }
                }
                "names_to" => {
                    if let ExprKind::Text { value: s, .. } = &value.kind {
                        names_to = s.clone();
                    } else {
                        self.diags.push(
                            Diagnostic::error(
                                DiagCode::TypeError,
                                "`pivot_longer` `names_to:` must be a string literal",
                            )
                            .with_span(value.span),
                        );
                    }
                }
                "values_to" => {
                    if let ExprKind::Text { value: s, .. } = &value.kind {
                        values_to = s.clone();
                    } else {
                        self.diags.push(
                            Diagnostic::error(
                                DiagCode::TypeError,
                                "`pivot_longer` `values_to:` must be a string literal",
                            )
                            .with_span(value.span),
                        );
                    }
                }
                _ => {}
            }
        }

        if melt_cols.is_empty() {
            self.diags.push(
                Diagnostic::error(
                    DiagCode::TypeError,
                    "`pivot_longer` requires a non-empty `cols: [.a, .b, ...]` list",
                )
                .with_span(span),
            );
        }
        if names_to.is_empty() || values_to.is_empty() {
            self.diags.push(
                Diagnostic::error(
                    DiagCode::TypeError,
                    "`pivot_longer` requires non-empty `names_to:` and `values_to:` string literals",
                )
                .with_span(span),
            );
        }
        if !names_to.is_empty() && names_to == values_to {
            self.diags.push(
                Diagnostic::error(
                    DiagCode::TypeError,
                    format!(
                        "`pivot_longer` `names_to` and `values_to` cannot share name `{names_to}`"
                    ),
                )
                .with_span(span),
            );
        }

        let mut unified_ty: Option<ScalarTy> = None;
        let mut val_tags = TagSet::empty();
        for cname in &melt_cols {
            let Some(cs) = in_tt.find_col(cname) else {
                self.diags.push(
                    Diagnostic::error(
                        DiagCode::TypeError,
                        format!("unknown column `.{cname}` in `pivot_longer`"),
                    )
                    .with_span(span),
                );
                continue;
            };
            val_tags = val_tags.union(&cs.tags);
            unified_ty = match unified_ty {
                None => Some(cs.ty.clone()),
                Some(prev) => match unify_pivot_scalar(&prev, &cs.ty) {
                    Some(u) => Some(u),
                    None => {
                        self.diags.push(
                            Diagnostic::error(
                                DiagCode::TypeError,
                                format!(
                                    "`pivot_longer` cannot unify column `.{cname}` of type `{:?}` with `{:?}`",
                                    cs.ty, prev
                                ),
                            )
                            .with_span(span),
                        );
                        Some(prev)
                    }
                },
            };
        }

        let value_ty = unified_ty.unwrap_or(ScalarTy::Float);
        let mut out_cols: Vec<ColSpec> = in_tt
            .cols
            .iter()
            .filter(|c| !melt_cols.contains(&c.name))
            .map(|c| ColSpec {
                agg_kind: AggKind::Raw,
                ..c.clone()
            })
            .collect();

        for kept in &out_cols {
            if kept.name == names_to || kept.name == values_to {
                self.diags.push(
                    Diagnostic::error(
                        DiagCode::TypeError,
                        format!(
                            "`pivot_longer` output column `{}` collides with retained ID column",
                            kept.name
                        ),
                    )
                    .with_span(span),
                );
            }
        }

        out_cols.push(ColSpec {
            name: names_to.clone(),
            ty: ScalarTy::Text,
            tags: TagSet::empty(),
            bucketed: false,
            agg_kind: AggKind::Raw,
        });
        out_cols.push(ColSpec {
            name: values_to.clone(),
            ty: value_ty.clone(),
            tags: val_tags.clone(),
            bucketed: false,
            agg_kind: AggKind::Raw,
        });

        let out_tt = TableTy {
            cols: out_cols,
            row_tags: in_tt.row_tags,
            order_tags: in_tt.order_tags,
            grouped_by: None,
            summarized: false,
            distinct_by: None,
        };
        (
            ExecExpr::Rel(Box::new(ExecPlan::PivotLonger {
                input: Box::new(in_plan),
                cols: melt_cols,
                names_to,
                values_to,
                value_ty,
                value_tags: val_tags,
            })),
            LTy::new(Ty::Table(out_tt), outer_tags),
        )
    }

    fn check_crosstab_verb(
        &mut self,
        in_plan: ExecPlan,
        in_tt: TableTy,
        outer_tags: TagSet,
        args: &[CallArg],
        _span: Span,
    ) -> (ExecExpr, LTy) {
        let mut rows_col = String::new();
        let mut cols_col = String::new();
        let mut values_col = String::new();
        let mut fill = Literal::int(0i64);
        for arg in args {
            let CallArg::Named { name, value, .. } = arg else {
                continue;
            };
            match name.name.as_str() {
                "rows" => {
                    if let ExprKind::DotField(m) = &value.kind {
                        rows_col = m.name.clone();
                    }
                }
                "cols" => {
                    if let ExprKind::DotField(m) = &value.kind {
                        cols_col = m.name.clone();
                    }
                }
                "values" => {
                    if let ExprKind::DotField(m) = &value.kind {
                        values_col = m.name.clone();
                    }
                }
                "fill" => {
                    let (e, _) = self.check_expr(
                        value,
                        &HashMap::new(),
                        None,
                        &TagSet::empty(),
                        LocalScopeKind::Normal,
                        None,
                    );
                    if let Some(l) = e.into_lit() {
                        fill = l;
                    }
                }
                _ => {}
            }
        }
        let tags = in_tt.total_tags().union(&outer_tags);
        (
            ExecExpr::Rel(Box::new(ExecPlan::Crosstab {
                input: Box::new(in_plan),
                rows_col,
                cols_col,
                values_col,
                fill,
            })),
            LTy::new(Ty::DynamicTable(tags), TagSet::empty()),
        )
    }

    #[expect(
        clippy::too_many_arguments,
        reason = "join verb validates keys, column collisions, suffixes, and tag propagation"
    )]
    fn check_join_verb(
        &mut self,
        kind: JoinKind,
        left_plan: ExecPlan,
        left_tt: TableTy,
        outer_tags: TagSet,
        args: &[CallArg],
        span: Span,
        env: &HashMap<Ident, VarBinding>,
        pc: &TagSet,
        scope: LocalScopeKind,
        ret_ctx: Option<(&str, Option<&Ty>)>,
    ) -> (ExecExpr, LTy) {
        let Some(CallArg::Positional(right_e)) = args.first() else {
            self.diags.push(
                Diagnostic::error(
                    DiagCode::TypeError,
                    "join requires a right-hand table argument",
                )
                .with_span(span),
            );
            return (
                ExecExpr::Rel(Box::new(left_plan)),
                LTy::new(Ty::Table(left_tt), outer_tags),
            );
        };
        let (rex, rlty) = self.check_expr(right_e, env, None, pc, scope, ret_ctx);
        let right_tt = match &rlty.ty {
            Ty::Table(tt) => tt.clone(),
            _ => {
                self.diags.push(
                    Diagnostic::error(
                        DiagCode::TypeError,
                        "join right-hand operand must be a `Table`",
                    )
                    .with_span(right_e.span),
                );
                return (
                    ExecExpr::Rel(Box::new(left_plan)),
                    LTy::new(Ty::Table(left_tt), outer_tags),
                );
            }
        };

        let mut join_on = JoinOn::SameKeys(Vec::new());
        let mut suffixes: Suffixes = None;
        for arg in &args[1..] {
            let CallArg::Named { name, value, .. } = arg else {
                continue;
            };
            match name.name.as_str() {
                "on" => {
                    join_on = self.parse_join_on(value);
                }
                "suffixes" => {
                    if let ExprKind::Tuple(ts) = &value.kind
                        && ts.len() == 2
                        && let (ExprKind::Text { value: s1, .. }, ExprKind::Text { value: s2, .. }) =
                            (&ts[0].kind, &ts[1].kind)
                    {
                        suffixes = Some((s1.clone(), s2.clone()));
                    } else {
                        self.diags.push(
                            Diagnostic::error(DiagCode::TypeError, "`suffixes:` must be a tuple of 2 strings, e.g. `(\"_left\", \"_right\")`")
                                .with_span(value.span),
                        );
                    }
                }
                _ => {}
            }
        }

        let key_pairs: Vec<(Ident, Ident)> = match &join_on {
            JoinOn::SameKeys(ks) => ks.iter().map(|k| (k.clone(), k.clone())).collect(),
            JoinOn::Pairs(ps) => ps.clone(),
        };
        let mut key_tags = TagSet::empty();
        for (lk, rk) in &key_pairs {
            match (left_tt.find_col(lk), right_tt.find_col(rk)) {
                (Some(lc), Some(rc)) => {
                    if lc.ty != rc.ty {
                        self.diags.push(
                            Diagnostic::error(
                                DiagCode::TypeError,
                                format!("join key type mismatch between `.{lk}` and `.{rk}`"),
                            )
                            .with_span(span),
                        );
                    }
                    key_tags = key_tags.union(&lc.tags).union(&rc.tags);
                }
                (None, _) => self.diags.push(
                    Diagnostic::error(
                        DiagCode::TypeError,
                        format!("unknown left join key `.{lk}`"),
                    )
                    .with_span(span),
                ),
                (_, None) => self.diags.push(
                    Diagnostic::error(
                        DiagCode::TypeError,
                        format!("unknown right join key `.{rk}`"),
                    )
                    .with_span(span),
                ),
            }
        }

        let out_row_tags = left_tt.row_tags.union(&right_tt.row_tags).union(&key_tags);

        let out_cols = match kind {
            JoinKind::Semi | JoinKind::Anti => left_tt.cols.clone(),
            _ => {
                let is_left = matches!(kind, JoinKind::LeftOne | JoinKind::LeftManyToOne);
                let right_skip: HashSet<&str> = match &join_on {
                    JoinOn::SameKeys(ks) => ks.iter().map(String::as_str).collect(),
                    JoinOn::Pairs(_) => HashSet::new(),
                };
                let left_names: HashSet<&str> =
                    left_tt.cols.iter().map(|c| c.name.as_str()).collect();
                let mut collisions = HashSet::new();
                for rc in &right_tt.cols {
                    if !right_skip.contains(rc.name.as_str())
                        && left_names.contains(rc.name.as_str())
                    {
                        collisions.insert(rc.name.clone());
                    }
                }
                if !collisions.is_empty() && suffixes.is_none() {
                    let mut names: Vec<String> = collisions.into_iter().collect();
                    names.sort();
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::TypeError,
                            format!(
                                "overlapping non-key join column(s): {}; pass `suffixes: (\"_left\", \"_right\")` or `select`/`drop` first",
                                names.join(", ")
                            ),
                        )
                        .with_span(span),
                    );
                    left_tt.cols.clone()
                } else {
                    let mut cols = Vec::new();
                    for lc in &left_tt.cols {
                        let mut c = lc.clone();
                        if collisions.contains(&c.name)
                            && let Some((ls, _)) = &suffixes
                        {
                            c.name.push_str(ls);
                        }
                        cols.push(c);
                    }
                    for rc in &right_tt.cols {
                        if right_skip.contains(rc.name.as_str()) {
                            continue;
                        }
                        let mut c = rc.clone();
                        if collisions.contains(&c.name)
                            && let Some((_, rs)) = &suffixes
                        {
                            c.name.push_str(rs);
                        }
                        if is_left {
                            c.ty = ensure_option_scalar(&c.ty);
                        }
                        cols.push(c);
                    }
                    cols
                }
            }
        };

        let out_tt = TableTy {
            cols: out_cols,
            row_tags: out_row_tags,
            order_tags: TagSet::empty(),
            grouped_by: None,
            summarized: false,
            distinct_by: None,
        };
        let right_plan = expr_to_plan(rex);
        (
            ExecExpr::Rel(Box::new(ExecPlan::Join {
                kind,
                left: Box::new(left_plan),
                right: Box::new(right_plan),
                on: join_on,
                suffixes,
            })),
            LTy::new(Ty::Table(out_tt), outer_tags.union(&rlty.tags)),
        )
    }

    fn parse_join_on(&mut self, expr: &Expr) -> JoinOn {
        match &expr.kind {
            ExprKind::DotField(m) => JoinOn::SameKeys(vec![m.name.clone()]),
            ExprKind::List(items) => {
                let mut ks = Vec::new();
                for it in items {
                    if let ExprKind::DotField(m) = &it.kind {
                        ks.push(m.name.clone());
                    }
                }
                JoinOn::SameKeys(ks)
            }
            ExprKind::Binary {
                op: BinOp::Eq,
                lhs,
                rhs,
            } => {
                if let (
                    ExprKind::Field {
                        receiver: lr,
                        member: lm,
                    },
                    ExprKind::Field {
                        receiver: rr,
                        member: rm,
                    },
                ) = (&lhs.kind, &rhs.kind)
                    && matches!(&lr.kind, ExprKind::Ident(s) if s == "left")
                    && matches!(&rr.kind, ExprKind::Ident(s) if s == "right")
                {
                    return JoinOn::Pairs(vec![(lm.name.clone(), rm.name.clone())]);
                }
                self.diags.push(
                    Diagnostic::error(
                        DiagCode::TypeError,
                        "explicit join key must have form `left.a == right.b`",
                    )
                    .with_span(expr.span),
                );
                JoinOn::SameKeys(Vec::new())
            }
            _ => {
                self.diags.push(
                    Diagnostic::error(
                        DiagCode::TypeError,
                        "`on:` expects `.key`, `[.a, .b]`, or `left.a == right.b`",
                    )
                    .with_span(expr.span),
                );
                JoinOn::SameKeys(Vec::new())
            }
        }
    }

    // -----------------------------------------------------------------------
    // Field Access & Calls (Methods, Capabilities, Stdlib, User Functions)
    // -----------------------------------------------------------------------

    /// Iteratively check arbitrarily deep left-leaning postfix chains (`xs.append(1).append(1)...`,
    /// `f()()()...`, `m[1][1]...`, `a.b.c...`) in O(1) call stack.
    fn check_postfix_chain(
        &mut self,
        expr: &Expr,
        env: &HashMap<Ident, VarBinding>,
        expected: Option<&Ty>,
        pc: &TagSet,
        scope: LocalScopeKind,
        ret_ctx: Option<(&str, Option<&Ty>)>,
    ) -> (ExecExpr, LTy) {
        enum PostfixStep<'b> {
            Field(&'b ast::SpannedName, Span),
            MethodCall(&'b ast::SpannedName, &'b [CallArg], Span),
            App(&'b [CallArg], Span),
            Index(&'b Expr, Span),
        }

        let mut steps: Vec<PostfixStep<'_>> = Vec::new();
        let mut cur = expr;
        loop {
            match &cur.kind {
                ExprKind::Field { receiver, member } => {
                    steps.push(PostfixStep::Field(member, cur.span));
                    cur = receiver.as_ref();
                }
                ExprKind::Index { target, index } => {
                    steps.push(PostfixStep::Index(index.as_ref(), cur.span));
                    cur = target.as_ref();
                }
                ExprKind::Call { callee, args } => match &callee.kind {
                    // Static namespace calls (`Stats.corr(...)`, `Report.new(...)`,
                    // `Math.Extra.triple(...)`), constructors (`Ok(...)`), and direct
                    // free-function calls (`foo(...)`) terminate the spine.
                    ExprKind::Field { receiver, .. } if extract_cap_path(receiver).is_some() => {
                        break;
                    }
                    ExprKind::CapName(_) | ExprKind::Ident(_) => break,
                    ExprKind::Field { receiver, member } => {
                        steps.push(PostfixStep::MethodCall(member, args.as_slice(), cur.span));
                        cur = receiver.as_ref();
                    }
                    _ => {
                        steps.push(PostfixStep::App(args.as_slice(), cur.span));
                        cur = callee.as_ref();
                    }
                },
                _ => break,
            }
        }

        let base_exp = if steps.is_empty() { expected } else { None };
        let (mut cur_ex, mut cur_lty) = match &cur.kind {
            ExprKind::Call { callee, args } => {
                self.check_call(callee, args, cur.span, env, base_exp, pc, scope, ret_ctx)
            }
            _ => self.check_expr(cur, env, base_exp, pc, scope, ret_ctx),
        };

        while let Some(step) = steps.pop() {
            let (next_ex, next_lty) = match step {
                PostfixStep::Field(member, sp) => {
                    self.check_field_access_on_val(cur_ex, cur_lty, member, sp, scope)
                }
                PostfixStep::MethodCall(member, args, sp) => self.check_method_call_on_val(
                    cur_ex, cur_lty, member, args, sp, env, pc, scope, ret_ctx,
                ),
                PostfixStep::App(args, sp) => {
                    self.check_hof_app(cur_ex, cur_lty, None, args, sp, env, pc, scope, ret_ctx)
                }
                PostfixStep::Index(index, sp) => {
                    let (iex, ilty) = self.check_expr(index, env, None, pc, scope, ret_ctx);
                    match &cur_lty.ty {
                        Ty::Map { val, .. } => (
                            ExecExpr::Prim {
                                op: ExecPrimOp::Core(PrimOp::MapGet),
                                args: vec![cur_ex, iex],
                            },
                            LTy::new(
                                Ty::Option(Box::new(val.ty.clone())),
                                cur_lty.tags.union(&ilty.tags).union(&val.tags),
                            ),
                        ),
                        _ => {
                            self.diags.push(
                                Diagnostic::error(DiagCode::TypeError, "indexing requires a `Map`")
                                    .with_span(sp),
                            );
                            (ExecExpr::Lit(Literal::Unit), LTy::public(Ty::Unit))
                        }
                    }
                }
            };
            cur_ex = next_ex;
            cur_lty = next_lty;
        }
        (cur_ex, cur_lty)
    }

    fn check_field_access_on_val(
        &mut self,
        rex: ExecExpr,
        rlty: LTy,
        member: &ast::SpannedName,
        span: Span,
        scope: LocalScopeKind,
    ) -> (ExecExpr, LTy) {
        // Duration suffixes on Int (`5.minutes`, `30.days`, `10.seconds`, `2.hours`).
        if rlty.ty == Ty::Int {
            let mult = match member.name.as_str() {
                "seconds" => Some(MICROS_PER_SECOND),
                "minutes" => Some(MICROS_PER_MINUTE),
                "hours" => Some(MICROS_PER_HOUR),
                "days" => Some(MICROS_PER_DAY),
                _ => None,
            };
            if let Some(m) = mult {
                if let ExecExpr::Lit(Literal::Int(n)) = &rex
                    && let Some(v) = n.to_i64()
                    && let Some(us) = v.checked_mul(m)
                {
                    return (
                        ExecExpr::Lit(Literal::duration(us)),
                        LTy::new(Ty::Duration, rlty.tags),
                    );
                }
                return (
                    ExecExpr::Prim {
                        op: ExecPrimOp::MakeDuration,
                        args: vec![rex, ExecExpr::Lit(Literal::int(m))],
                    },
                    LTy::new(Ty::Duration, rlty.tags),
                );
            }
        }
        // Scalar properties (`abs`, `ceil`, `floor`, `trunc`, `to_int`, `to_float`, `to_decimal`, `trim`, ...).
        if let Some((op, out_ty)) = numeric_prop_op(&rlty.ty, member.name.as_str()) {
            return (
                ExecExpr::Prim {
                    op,
                    args: vec![rex],
                },
                LTy::new(out_ty, rlty.tags),
            );
        }
        match (&rlty.ty, member.name.as_str()) {
            (Ty::Text, prop) if text_prop_op(prop).is_some() => {
                if let Some((op, out_ty)) = text_prop_op(prop) {
                    return (
                        ExecExpr::Prim {
                            op,
                            args: vec![rex],
                        },
                        LTy::new(out_ty, rlty.tags),
                    );
                }
            }
            (Ty::Date, prop) if date_prop_op(prop).is_some() => {
                if let Some((op, out_ty)) = date_prop_op(prop) {
                    return (
                        ExecExpr::Prim {
                            op,
                            args: vec![rex],
                        },
                        LTy::new(out_ty, rlty.tags),
                    );
                }
            }
            (Ty::Option(_), "some?") => {
                return (
                    ExecExpr::Prim {
                        op: ExecPrimOp::Core(PrimOp::IsSome),
                        args: vec![rex],
                    },
                    LTy::new(Ty::Bool, rlty.tags),
                );
            }
            (Ty::Option(_), "none?") => {
                return (
                    ExecExpr::Prim {
                        op: ExecPrimOp::Core(PrimOp::IsNone),
                        args: vec![rex],
                    },
                    LTy::new(Ty::Bool, rlty.tags),
                );
            }
            (Ty::List(_), "size" | "len") => {
                return (
                    ExecExpr::Prim {
                        op: ExecPrimOp::Core(PrimOp::ListLen),
                        args: vec![rex],
                    },
                    LTy::new(Ty::Int, rlty.tags),
                );
            }
            (Ty::List(_), "empty?") => {
                return (
                    ExecExpr::Prim {
                        op: ExecPrimOp::Core(PrimOp::ListEmpty),
                        args: vec![rex],
                    },
                    LTy::new(Ty::Bool, rlty.tags),
                );
            }
            (Ty::List(el), "first") => {
                return (
                    ExecExpr::Prim {
                        op: ExecPrimOp::ListFirst,
                        args: vec![rex],
                    },
                    LTy::new(
                        Ty::Option(Box::new(el.ty.clone())),
                        rlty.tags.union(&el.tags),
                    ),
                );
            }
            (Ty::List(el), "first!") => {
                return (
                    ExecExpr::Prim {
                        op: ExecPrimOp::ListFirstBang,
                        args: vec![rex],
                    },
                    LTy::new(el.ty.clone(), rlty.tags.union(&el.tags)),
                );
            }
            (Ty::Table(tt), "empty?") => {
                return (
                    ExecExpr::Prim {
                        op: ExecPrimOp::TableEmpty,
                        args: vec![rex],
                    },
                    LTy::new(Ty::Bool, tt.row_tags.union(&rlty.tags)),
                );
            }
            (Ty::Table(tt), "first!") => {
                let row_ty_name = self.register_table_row_type(tt);
                return (
                    ExecExpr::Prim {
                        op: ExecPrimOp::TableFirstBang,
                        args: vec![rex],
                    },
                    LTy::new(
                        Ty::Data(row_ty_name),
                        tt.row_tags.union(&tt.order_tags).union(&rlty.tags),
                    ),
                );
            }
            (Ty::Args, "list") => {
                return (
                    ExecExpr::Host {
                        op: ExecHostOp::Core(HostOp::ArgsGet),
                        args: vec![rex],
                    },
                    LTy::public(Ty::List(Box::new(LTy::public(Ty::Text)))),
                );
            }
            (Ty::Args, "first") => {
                return (
                    ExecExpr::Host {
                        op: ExecHostOp::ArgsFirst,
                        args: vec![rex],
                    },
                    LTy::public(Ty::Option(Box::new(Ty::Text))),
                );
            }
            (Ty::Console(_), "printed_lines") => {
                self.require_spec_scope(scope, span, "`console.printed_lines`");
                return (
                    ExecExpr::Host {
                        op: ExecHostOp::FakeConsoleLines,
                        args: vec![rex],
                    },
                    LTy::public(Ty::List(Box::new(LTy::public(Ty::Text)))),
                );
            }
            (Ty::Console(_), "printed_errors") => {
                self.require_spec_scope(scope, span, "`console.printed_errors`");
                return (
                    ExecExpr::Host {
                        op: ExecHostOp::FakeConsoleErrors,
                        args: vec![rex],
                    },
                    LTy::public(Ty::List(Box::new(LTy::public(Ty::Text)))),
                );
            }
            (Ty::Console(_), "printed_tables") => {
                self.require_spec_scope(scope, span, "`console.printed_tables`");
                return (
                    ExecExpr::Host {
                        op: ExecHostOp::FakeConsoleTables,
                        args: vec![rex],
                    },
                    LTy::public(Ty::List(Box::new(LTy::public(Ty::Table(
                        TableTy::default(),
                    ))))),
                );
            }
            (Ty::LinearModel, "slope" | "intercept" | "r_squared") => {
                let idx = match member.name.as_str() {
                    "slope" => 0,
                    "intercept" => 1,
                    _ => 2,
                };
                return (
                    ExecExpr::Prim {
                        op: ExecPrimOp::RecordField {
                            type_name: "LinearModel".to_string(),
                            field_name: member.name.clone(),
                            field_idx: idx,
                        },
                        args: vec![rex],
                    },
                    LTy::new(Ty::Float, rlty.tags),
                );
            }
            (Ty::StatTest, "t_stat" | "stat" | "statistic" | "chi2" | "p_value" | "df") => {
                let idx = match member.name.as_str() {
                    "t_stat" | "stat" | "statistic" | "chi2" => 0,
                    "p_value" => 1,
                    _ => 2,
                };
                return (
                    ExecExpr::Prim {
                        op: ExecPrimOp::RecordField {
                            type_name: "StatTest".to_string(),
                            field_name: member.name.clone(),
                            field_idx: idx,
                        },
                        args: vec![rex],
                    },
                    LTy::new(Ty::Float, rlty.tags),
                );
            }
            (Ty::Data(dname), "read_only") if dname == TY_IN_MEMORY_FILES => {
                return (rex, LTy::public(Ty::ReadFiles));
            }
            (Ty::Data(dname), fname) => {
                // TableRow column projection (`bad.line`, `out.first!.department`, ...).
                if let Some(tt) = self.table_row_schemas.get(dname).cloned() {
                    if let Some((idx, cs)) =
                        tt.cols.iter().enumerate().find(|(_, c)| c.name == fname)
                    {
                        return (
                            ExecExpr::Prim {
                                op: ExecPrimOp::RecordField {
                                    type_name: dname.clone(),
                                    field_name: fname.to_string(),
                                    field_idx: idx,
                                },
                                args: vec![rex],
                            },
                            LTy::new(cs.ty.to_ty(), cs.tags.union(&tt.row_tags).union(&rlty.tags)),
                        );
                    }
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::TypeError,
                            format!("table row has no column `{fname}`"),
                        )
                        .with_span(member.span),
                    );
                    return (ExecExpr::Lit(Literal::Unit), LTy::public(Ty::Unit));
                }
                // User struct or UpsertStats field projection.
                if let Some(layout) = self.structs.get(dname).cloned()
                    && let Some(idx) = layout.field_names.iter().position(|f| f == fname)
                {
                    let flty = layout.field_ltys[idx].clone();
                    return (
                        ExecExpr::Prim {
                            op: ExecPrimOp::RecordField {
                                type_name: dname.clone(),
                                field_name: fname.to_string(),
                                field_idx: idx,
                            },
                            args: vec![rex],
                        },
                        LTy::new(flty.ty, flty.tags.union(&rlty.tags)),
                    );
                }
            }
            _ => {}
        }

        self.diags.push(
            Diagnostic::error(
                DiagCode::TypeError,
                format!("unknown field or property `.{}`", member.name),
            )
            .with_span(span),
        );
        (ExecExpr::Lit(Literal::Unit), LTy::public(Ty::Unit))
    }

    #[expect(
        clippy::too_many_arguments,
        reason = "call checker dispatches static namespaces, methods, constructors, and functions"
    )]
    fn check_call(
        &mut self,
        callee: &Expr,
        args: &[CallArg],
        span: Span,
        env: &HashMap<Ident, VarBinding>,
        expected: Option<&Ty>,
        pc: &TagSet,
        scope: LocalScopeKind,
        ret_ctx: Option<(&str, Option<&Ty>)>,
    ) -> (ExecExpr, LTy) {
        // 1. Namespace/module static calls: `Stats.corr(...)`, `Report.new(...)`, `Files.in_memory(...)`,
        //    and imported local/vendored module calls (`Helpers.double(...)`, `Acme.Helpers.double(...)`).
        if let ExprKind::Field { receiver, member } = &callee.kind
            && let Some(ns) = extract_cap_path(receiver)
        {
            return self.check_namespace_call(
                &ns,
                &member.name,
                args,
                span,
                env,
                pc,
                scope,
                ret_ctx,
            );
        }

        // 2. Method calls on a receiver value: `files.read_csv(...)`, `console.print(...)`, `x.round(3)`, etc.
        if let ExprKind::Field { receiver, member } = &callee.kind {
            let (rex, rlty) = self.check_expr(receiver, env, None, pc, scope, ret_ctx);
            return self
                .check_method_call_on_val(rex, rlty, member, args, span, env, pc, scope, ret_ctx);
        }

        // 3. Constructors (`Ok(...)`, `Error(...)`, `Some(...)`, user `Struct(...)`, user `EnumVariant(...)`).
        if let ExprKind::CapName(cname) = &callee.kind {
            return self.check_ctor_call(cname, args, span, env, expected, pc, scope, ret_ctx);
        }

        // 4. Built-in free functions (`date_trunc`, `months_between`, `format_csv`) & user functions.
        if let ExprKind::Ident(fname) = &callee.kind {
            if fname == "format_csv" {
                let Some(CallArg::Positional(tbl_e)) = args.first() else {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::TypeError,
                            "`format_csv` expects `(table, [sanitize_formulas: Bool])`",
                        )
                        .with_span(span),
                    );
                    return (
                        ExecExpr::Lit(Literal::Text(String::new())),
                        LTy::public(Ty::Text),
                    );
                };
                let (tbl_ex, tbl_lty) = self.check_expr(tbl_e, env, None, pc, scope, ret_ctx);
                let Ty::Table(tt) = &tbl_lty.ty else {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::TypeError,
                            format!(
                                "`format_csv` requires a `Table` first argument, found `{:?}`",
                                tbl_lty.ty
                            ),
                        )
                        .with_span(tbl_e.span),
                    );
                    return (
                        ExecExpr::Lit(Literal::Text(String::new())),
                        LTy::new(Ty::Text, tbl_lty.tags),
                    );
                };
                return self.check_format_csv_call(
                    tbl_ex,
                    tt,
                    &tbl_lty.tags,
                    &args[1..],
                    span,
                    env,
                    pc,
                    scope,
                    ret_ctx,
                );
            }
            if fname == "date_trunc" {
                return self.check_date_trunc_expr(args, span, env, pc, scope, ret_ctx);
            }
            if (fname == "months_between" || fname == "days_between")
                && let [CallArg::Positional(a), CallArg::Positional(b)] = args
            {
                let (ea, la) = self.check_expr(a, env, Some(&Ty::Date), pc, scope, ret_ctx);
                if la.ty != Ty::Date {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::TypeError,
                            format!("`{fname}` expects `Date` as first argument"),
                        )
                        .with_span(a.span),
                    );
                }
                let (eb, lb) = self.check_expr(b, env, Some(&Ty::Date), pc, scope, ret_ctx);
                if lb.ty != Ty::Date {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::TypeError,
                            format!("`{fname}` expects `Date` as second argument"),
                        )
                        .with_span(b.span),
                    );
                }
                let op = if fname == "months_between" {
                    ExecPrimOp::MonthsBetween
                } else {
                    ExecPrimOp::DaysBetween
                };
                return (
                    ExecExpr::Prim {
                        op,
                        args: vec![ea, eb],
                    },
                    LTy::new(Ty::Int, la.tags.union(&lb.tags)),
                );
            }
            if fname == "add_days"
                && let (Some(CallArg::Positional(d)), Some(days_e)) = (
                    args.first(),
                    extract_one_arg(&args[1.min(args.len())..], "days"),
                )
            {
                let (ed, ld) = self.check_expr(d, env, Some(&Ty::Date), pc, scope, ret_ctx);
                return self
                    .check_date_add_days_expr(ed, ld, d.span, days_e, env, pc, scope, ret_ctx);
            }
            if fname == "at_midnight_in_tz"
                && let (Some(CallArg::Positional(d)), Some(tz_e)) = (
                    args.first(),
                    extract_one_arg(&args[1.min(args.len())..], "tz"),
                )
            {
                let (ed, ld) = self.check_expr(d, env, Some(&Ty::Date), pc, scope, ret_ctx);
                return self
                    .check_date_midnight_tz_expr(ed, ld, d.span, tz_e, env, pc, scope, ret_ctx);
            }
            if (fname == "in_tz" || fname == "date_in_tz")
                && let [CallArg::Positional(a), CallArg::Positional(z)] = args
            {
                let (ea, la) = self.check_expr(a, env, Some(&Ty::Timestamp), pc, scope, ret_ctx);
                if la.ty != Ty::Timestamp {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::TypeError,
                            format!("`{fname}` expects `Timestamp` as first argument"),
                        )
                        .with_span(a.span),
                    );
                }
                let (ez, lz) = self.check_expr(z, env, Some(&Ty::Text), pc, scope, ret_ctx);
                if lz.ty != Ty::Text {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::TypeError,
                            format!("`{fname}` expects a `Text` IANA timezone name"),
                        )
                        .with_span(z.span),
                    );
                }
                let (op, out_ty) = if fname == "in_tz" {
                    (ExecPrimOp::InTz, Ty::Text)
                } else {
                    (ExecPrimOp::DateInTz, Ty::Date)
                };
                return (
                    ExecExpr::Prim {
                        op,
                        args: vec![ea, ez],
                    },
                    LTy::new(out_ty, la.tags.union(&lz.tags)),
                );
            }
            if let Some(sig) = self.fn_sigs.get(fname).cloned() {
                if !sig.is_pure && !pc.is_empty() {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::PrivacyError,
                            format!(
                                "cannot call impure function `{fname}` under sensitive control flow {:?}",
                                pc.elems()
                            ),
                        )
                        .with_span(span),
                    );
                }
                let ret_lty = self
                    .ensure_fn_checked(fname)
                    .or(sig.ret)
                    .unwrap_or_else(|| LTy::public(Ty::Unit));
                if args.len() != sig.params.len() {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::TypeError,
                            format!(
                                "function `{fname}` expects {} argument(s), got {}",
                                sig.params.len(),
                                args.len()
                            ),
                        )
                        .with_span(span),
                    );
                }
                let mut lowered_args = Vec::with_capacity(args.len());
                let mut arg_tags = TagSet::empty();
                for (i, arg) in args.iter().enumerate() {
                    let expr_arg = match arg {
                        CallArg::Positional(e) | CallArg::Named { value: e, .. } => e,
                    };
                    let param_lty = sig.params.get(i).map(|(_, l)| l);
                    let (mut aex, alty) = self.check_expr(
                        expr_arg,
                        env,
                        param_lty.map(|l| &l.ty),
                        pc,
                        scope,
                        ret_ctx,
                    );
                    if let Some(plty) = param_lty {
                        aex = self.coerce_expr(
                            aex,
                            &alty,
                            plty,
                            expr_arg.span,
                            &format!("argument {} of `{fname}`", i + 1),
                        );
                    }
                    arg_tags = arg_tags.union(&alty.tags);
                    lowered_args.push(aex);
                }
                let out_ret = taint_return_with_pc(ret_lty, &arg_tags, pc);
                return (
                    ExecExpr::Call {
                        fn_name: fname.clone(),
                        args: lowered_args,
                    },
                    out_ret,
                );
            }
        }

        // 5. Higher-order function value call (`f(x)`).
        let (fex, flty) = self.check_expr(callee, env, None, pc, scope, ret_ctx);
        self.check_hof_app(fex, flty, None, args, span, env, pc, scope, ret_ctx)
    }

    /// Check higher-order function / closure application enforcing `pc`, arity, per-argument
    /// sensitivity subtyping (`arg_i.tags ⊆ param_i.tags`), and return-tag propagation.
    #[expect(
        clippy::too_many_arguments,
        reason = "closure application checker validates pc ceiling, arity, and argument sensitivity"
    )]
    fn check_hof_app(
        &mut self,
        fex: ExecExpr,
        flty: LTy,
        first_pre_arg: Option<(ExecExpr, LTy, Span)>,
        rest_args: &[CallArg],
        span: Span,
        env: &HashMap<Ident, VarBinding>,
        pc: &TagSet,
        scope: LocalScopeKind,
        ret_ctx: Option<(&str, Option<&Ty>)>,
    ) -> (ExecExpr, LTy) {
        let total_args = usize::from(first_pre_arg.is_some()) + rest_args.len();
        let (param_ltys, fn_pc, ret_lty) = match &flty.ty {
            Ty::Fn {
                params,
                pc: fpc,
                ret,
            } => (params.clone(), fpc.clone(), ret.as_ref().clone()),
            _ => {
                self.diags.push(
                    Diagnostic::error(
                        DiagCode::TypeError,
                        "attempted to call a non-function value",
                    )
                    .with_span(span),
                );
                let mut lowered = Vec::with_capacity(total_args);
                if let Some((a0, _, _)) = first_pre_arg {
                    lowered.push(a0);
                }
                for arg in rest_args {
                    let e = match arg {
                        CallArg::Positional(e) | CallArg::Named { value: e, .. } => e,
                    };
                    let (ae, _) = self.check_expr(e, env, None, pc, scope, ret_ctx);
                    lowered.push(ae);
                }
                return (
                    ExecExpr::App {
                        fn_expr: Box::new(fex),
                        args: lowered,
                    },
                    LTy::public(Ty::Unit),
                );
            }
        };

        let call_pc = pc.union(&flty.tags);
        if !call_pc.is_subset(&fn_pc) {
            self.diags.push(
                Diagnostic::error(
                    DiagCode::PrivacyError,
                    format!(
                        "cannot call closure under sensitive control flow {:?} exceeding closure bound {:?}",
                        call_pc.elems(),
                        fn_pc.elems()
                    ),
                )
                .with_span(span),
            );
        }
        if total_args != param_ltys.len() {
            self.diags.push(
                Diagnostic::error(
                    DiagCode::TypeError,
                    format!(
                        "closure expects {} argument(s), got {total_args}",
                        param_ltys.len()
                    ),
                )
                .with_span(span),
            );
        }

        let mut lowered = Vec::with_capacity(total_args);
        let mut arg_tags = TagSet::empty();
        let mut arg_idx = 0usize;
        if let Some((mut a0, a0_lty, a0_span)) = first_pre_arg {
            if let Some(plty) = param_ltys.first() {
                a0 = self.coerce_expr(a0, &a0_lty, plty, a0_span, "closure call argument 1");
            }
            arg_tags = arg_tags.union(&a0_lty.tags);
            lowered.push(a0);
            arg_idx = 1;
        }
        for arg in rest_args {
            let e = match arg {
                CallArg::Positional(e) | CallArg::Named { value: e, .. } => e,
            };
            let plty = param_ltys.get(arg_idx);
            let (mut aex, alty) = self.check_expr(e, env, plty.map(|l| &l.ty), pc, scope, ret_ctx);
            if let Some(p) = plty {
                aex = self.coerce_expr(
                    aex,
                    &alty,
                    p,
                    e.span,
                    &format!("closure call argument {}", arg_idx + 1),
                );
            }
            arg_tags = arg_tags.union(&alty.tags);
            lowered.push(aex);
            arg_idx += 1;
        }
        let out_ret = taint_return_with_pc(ret_lty, &arg_tags, &call_pc);
        (
            ExecExpr::App {
                fn_expr: Box::new(fex),
                args: lowered,
            },
            out_ret,
        )
    }

    #[expect(
        clippy::too_many_arguments,
        reason = "namespace call handles stdlib modules and spec-only fake constructors"
    )]
    fn check_namespace_call(
        &mut self,
        ns: &str,
        method: &str,
        args: &[CallArg],
        span: Span,
        env: &HashMap<Ident, VarBinding>,
        pc: &TagSet,
        scope: LocalScopeKind,
        ret_ctx: Option<(&str, Option<&Ty>)>,
    ) -> (ExecExpr, LTy) {
        match (ns, method) {
            ("Report", "new") => {
                let (tex, tlty) = match args.first() {
                    Some(CallArg::Positional(e)) => {
                        self.check_expr(e, env, Some(&Ty::Text), pc, scope, ret_ctx)
                    }
                    _ => (
                        ExecExpr::Lit(Literal::Text(String::new())),
                        LTy::public(Ty::Text),
                    ),
                };
                (
                    ExecExpr::Prim {
                        op: ExecPrimOp::Core(PrimOp::ReportNew),
                        args: vec![tex],
                    },
                    LTy::new(Ty::Report(tlty.effective_tags()), TagSet::empty()),
                )
            }
            ("Table", "concat") => {
                let Some(CallArg::Positional(e)) = args.first() else {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::TypeError,
                            "`Table.concat` expects a `List(Table(...))`",
                        )
                        .with_span(span),
                    );
                    return (ExecExpr::Lit(Literal::Unit), LTy::public(Ty::Unit));
                };
                let (lex, llty) = self.check_expr(e, env, None, pc, scope, ret_ctx);
                let tt = match &llty.ty {
                    Ty::List(el) => match &el.ty {
                        Ty::Table(t) => t.clone(),
                        _ => TableTy::default(),
                    },
                    _ => TableTy::default(),
                };
                (
                    ExecExpr::Prim {
                        op: ExecPrimOp::Core(PrimOp::TableConcat(tt.clone())),
                        args: vec![lex],
                    },
                    LTy::new(Ty::Table(tt), llty.tags),
                )
            }
            ("Args", "of") => {
                self.require_spec_scope(scope, span, "`Args.of(...)`");
                let (lex, _) = match args.first() {
                    Some(CallArg::Positional(e)) => self.check_expr(
                        e,
                        env,
                        Some(&Ty::List(Box::new(LTy::public(Ty::Text)))),
                        pc,
                        scope,
                        ret_ctx,
                    ),
                    _ => (
                        ExecExpr::Prim {
                            op: ExecPrimOp::Core(PrimOp::ListLit(LTy::public(Ty::Text))),
                            args: Vec::new(),
                        },
                        LTy::public(Ty::List(Box::new(LTy::public(Ty::Text)))),
                    ),
                };
                (
                    ExecExpr::Host {
                        op: ExecHostOp::FakeArgsOf,
                        args: vec![lex],
                    },
                    LTy::public(Ty::Args),
                )
            }
            ("Files", "in_memory") => {
                self.require_spec_scope(scope, span, "`Files.in_memory(...)`");
                let (mex, _) = match args.first() {
                    Some(CallArg::Positional(e)) => {
                        self.check_expr(e, env, None, pc, scope, ret_ctx)
                    }
                    _ => (ExecExpr::Lit(Literal::Unit), LTy::public(Ty::Unit)),
                };
                (
                    ExecExpr::Host {
                        op: ExecHostOp::FakeFilesInMemory,
                        args: vec![mex],
                    },
                    LTy::public(Ty::Data(TY_IN_MEMORY_FILES.to_string())),
                )
            }
            ("Console", "fake") => {
                self.require_spec_scope(scope, span, "`Console.fake()`");
                (
                    ExecExpr::Host {
                        op: ExecHostOp::Core(HostOp::FakeConsole(TagSet::empty())),
                        args: Vec::new(),
                    },
                    LTy::public(Ty::Console(TagSet::empty())),
                )
            }
            ("Secret", "fake") => {
                self.require_spec_scope(scope, span, "`Secret.fake(...)`");
                let (sex, _) = match args.first() {
                    Some(CallArg::Positional(e)) => {
                        self.check_expr(e, env, Some(&Ty::Text), pc, scope, ret_ctx)
                    }
                    _ => (
                        ExecExpr::Lit(Literal::Text("fake-secret".to_string())),
                        LTy::public(Ty::Text),
                    ),
                };
                (
                    ExecExpr::Host {
                        op: ExecHostOp::Core(HostOp::FakeSecret("fake".to_string())),
                        args: vec![sex],
                    },
                    LTy::public(Ty::Secret("fake".to_string())),
                )
            }
            ("Https", "fake") => {
                self.require_spec_scope(scope, span, "`Https.fake(...)`");
                let host = match args.first() {
                    Some(CallArg::Positional(Expr {
                        kind: ExprKind::Text { value, .. },
                        ..
                    })) => value.clone(),
                    _ => {
                        self.diags.push(
                            Diagnostic::error(
                                DiagCode::CapabilityError,
                                "`Https.fake` requires a hostname string literal as its first argument",
                            )
                            .with_span(span),
                        );
                        String::new()
                    }
                };
                let resp_expr = named_expr_arg(args, "responses").or_else(|| match args.get(1) {
                    Some(CallArg::Positional(e)) => Some(e),
                    _ => None,
                });
                let resp_ex = if let Some(re) = resp_expr {
                    let (ex, _) = self.check_expr(re, env, None, pc, scope, ret_ctx);
                    ex
                } else {
                    ExecExpr::Lit(Literal::Unit)
                };
                let mut allows = TagSet::empty();
                if let Some(Expr {
                    kind: ExprKind::List(items),
                    ..
                }) = named_expr_arg(args, "allows")
                {
                    let mut tags = Vec::new();
                    for item in items {
                        if let ExprKind::Ident(t) = &item.kind {
                            tags.push(t.clone());
                        }
                    }
                    allows = TagSet::of_list(tags);
                }
                (
                    ExecExpr::Host {
                        op: ExecHostOp::FakeHttps { host: host.clone() },
                        args: vec![resp_ex],
                    },
                    LTy::public(Ty::HttpsAllow { host, allows }),
                )
            }
            ("DB", "in_memory") => {
                self.require_spec_scope(scope, span, "`DB.in_memory(...)`");
                let db = match args.first() {
                    Some(CallArg::Positional(Expr {
                        kind: ExprKind::CapName(s),
                        ..
                    })) => s.clone(),
                    _ => "InMemory".to_string(),
                };
                let mut table_names = Vec::new();
                let mut tbl_args = Vec::new();
                if let Some(CallArg::Positional(Expr {
                    kind: ExprKind::Map(entries),
                    ..
                })) = args.get(1)
                {
                    for (k, v) in entries {
                        let sname = match &k.kind {
                            ExprKind::CapName(s) | ExprKind::Ident(s) => s.clone(),
                            ExprKind::Text { value: s, .. } => s.clone(),
                            _ => continue,
                        };
                        let expected_tbl = self
                            .schemas
                            .get(&sname)
                            .map(|cs| Ty::Table(cs.decl.schema.clone()));
                        let (mut vex, vlty) =
                            self.check_expr(v, env, expected_tbl.as_ref(), pc, scope, ret_ctx);
                        if let Some(Ty::Table(dst_tt)) = &expected_tbl {
                            vex = self.coerce_expr(
                                vex,
                                &vlty,
                                &LTy::public(Ty::Table(dst_tt.clone())),
                                v.span,
                                &format!("DB.in_memory table `{sname}`"),
                            );
                        }
                        table_names.push(sname);
                        tbl_args.push(vex);
                    }
                }
                (
                    ExecExpr::Host {
                        op: ExecHostOp::FakeDbInMemory {
                            db: db.clone(),
                            table_names,
                        },
                        args: tbl_args,
                    },
                    LTy::public(Ty::ReadDB(db)),
                )
            }
            ("Stats", "corr") => {
                let Some(CallArg::Positional(tbl_e)) = args.first() else {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::TypeError,
                            "`Stats.corr` requires a table argument",
                        )
                        .with_span(span),
                    );
                    return (
                        ExecExpr::Lit(Literal::Float(Float64::ZERO)),
                        LTy::public(Ty::Float),
                    );
                };
                let (tex, tlty) = self.check_expr(tbl_e, env, None, pc, scope, ret_ctx);
                let col_x = named_dot_col(args, "x").unwrap_or_default();
                let col_y = named_dot_col(args, "y").unwrap_or_default();
                if let Ty::Table(ref tt) = tlty.ty {
                    for cname in [&col_x, &col_y] {
                        match tt.find_col(cname) {
                            None => self.diags.push(
                                Diagnostic::error(
                                    DiagCode::TypeError,
                                    format!("unknown column `.{cname}` in `Stats.corr`"),
                                )
                                .with_span(span),
                            ),
                            Some(cs) if numeric_core_of_scalar(&cs.ty).is_none() => {
                                self.diags.push(
                                    Diagnostic::error(
                                        DiagCode::TypeError,
                                        format!("`Stats.corr` requires numeric column `.{cname}`"),
                                    )
                                    .with_span(span),
                                );
                            }
                            Some(_) => {}
                        }
                    }
                }
                let is_spearman = match named_expr_arg(args, "method") {
                    None => false,
                    Some(Expr {
                        kind: ExprKind::Atom(m),
                        ..
                    }) if m == "pearson" => false,
                    Some(Expr {
                        kind: ExprKind::Atom(m),
                        ..
                    }) if m == "spearman" => true,
                    Some(other) => {
                        self.diags.push(
                            Diagnostic::error(
                                DiagCode::TypeError,
                                "`Stats.corr` `method:` must be `:pearson` or `:spearman`",
                            )
                            .with_span(other.span),
                        );
                        false
                    }
                };
                let tags = stats_col_tags(&tlty, &[&col_x, &col_y]);
                let op = if is_spearman {
                    ExecPrimOp::StatsCorrSpearman { col_x, col_y }
                } else {
                    ExecPrimOp::Core(PrimOp::StatsCorr { col_x, col_y })
                };
                (
                    ExecExpr::Prim {
                        op,
                        args: vec![tex],
                    },
                    LTy::new(Ty::Float, tags),
                )
            }
            ("Stats", "linear_regression") => {
                let Some(CallArg::Positional(tbl_e)) = args.first() else {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::TypeError,
                            "`Stats.linear_regression` requires a table argument",
                        )
                        .with_span(span),
                    );
                    return (ExecExpr::Lit(Literal::Unit), LTy::public(Ty::LinearModel));
                };
                let (tex, tlty) = self.check_expr(tbl_e, env, None, pc, scope, ret_ctx);
                let col_x = named_dot_col(args, "x").unwrap_or_default();
                let col_y = named_dot_col(args, "y").unwrap_or_default();
                if let Ty::Table(ref tt) = tlty.ty {
                    for cname in [&col_x, &col_y] {
                        match tt.find_col(cname) {
                            None => self.diags.push(
                                Diagnostic::error(
                                    DiagCode::TypeError,
                                    format!(
                                        "unknown column `.{cname}` in `Stats.linear_regression`"
                                    ),
                                )
                                .with_span(span),
                            ),
                            Some(cs) if numeric_core_of_scalar(&cs.ty).is_none() => {
                                self.diags.push(
                                    Diagnostic::error(
                                        DiagCode::TypeError,
                                        format!(
                                            "`Stats.linear_regression` requires numeric column `.{cname}`"
                                        ),
                                    )
                                    .with_span(span),
                                );
                            }
                            Some(_) => {}
                        }
                    }
                }
                let tags = stats_col_tags(&tlty, &[&col_x, &col_y]);
                (
                    ExecExpr::Prim {
                        op: ExecPrimOp::Core(PrimOp::StatsLinReg { col_x, col_y }),
                        args: vec![tex],
                    },
                    LTy::new(Ty::LinearModel, tags),
                )
            }
            ("Stats", "t_test") => {
                if let (Some(CallArg::Positional(a_e)), Some(CallArg::Positional(b_e))) =
                    (args.first(), args.get(1))
                {
                    let (ea, la) = self.check_expr(a_e, env, None, pc, scope, ret_ctx);
                    let (eb, lb) = self.check_expr(b_e, env, None, pc, scope, ret_ctx);
                    let col = named_dot_col(args, "column").unwrap_or_default();
                    let tags = stats_col_tags(&la, &[&col]).union(&stats_col_tags(&lb, &[&col]));
                    return (
                        ExecExpr::Prim {
                            op: ExecPrimOp::StatsWelchTTest { col },
                            args: vec![ea, eb],
                        },
                        LTy::new(Ty::StatTest, tags),
                    );
                }
                (ExecExpr::Lit(Literal::Unit), LTy::public(Ty::StatTest))
            }
            ("Stats", "chi_square") => {
                let Some(CallArg::Positional(tbl_e)) = args.first() else {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::TypeError,
                            "`Stats.chi_square` requires a table argument",
                        )
                        .with_span(span),
                    );
                    return (ExecExpr::Lit(Literal::Unit), LTy::public(Ty::StatTest));
                };
                let (tex, tlty) = self.check_expr(tbl_e, env, None, pc, scope, ret_ctx);
                let xy = (named_dot_col(args, "x"), named_dot_col(args, "y"));
                let oe = (
                    named_dot_col(args, "observed"),
                    named_dot_col(args, "expected"),
                );
                match (xy, oe) {
                    ((Some(col_x), Some(col_y)), (None, None)) => {
                        if let Ty::Table(ref tt) = tlty.ty {
                            for cname in [&col_x, &col_y] {
                                if tt.find_col(cname).is_none() {
                                    self.diags.push(
                                        Diagnostic::error(
                                            DiagCode::TypeError,
                                            format!(
                                                "unknown column `.{cname}` in `Stats.chi_square`"
                                            ),
                                        )
                                        .with_span(span),
                                    );
                                }
                            }
                        }
                        let tags = stats_col_tags(&tlty, &[&col_x, &col_y]);
                        (
                            ExecExpr::Prim {
                                op: ExecPrimOp::StatsChiSquareIndependence { col_x, col_y },
                                args: vec![tex],
                            },
                            LTy::new(Ty::StatTest, tags),
                        )
                    }
                    ((None, None), (Some(observed), Some(expected))) => {
                        if let Ty::Table(ref tt) = tlty.ty {
                            for cname in [&observed, &expected] {
                                match tt.find_col(cname) {
                                    None => self.diags.push(
                                        Diagnostic::error(
                                            DiagCode::TypeError,
                                            format!(
                                                "unknown column `.{cname}` in `Stats.chi_square`"
                                            ),
                                        )
                                        .with_span(span),
                                    ),
                                    Some(cs) if numeric_core_of_scalar(&cs.ty).is_none() => {
                                        self.diags.push(
                                            Diagnostic::error(
                                                DiagCode::TypeError,
                                                format!(
                                                    "`Stats.chi_square` goodness-of-fit requires numeric column `.{cname}`"
                                                ),
                                            )
                                            .with_span(span),
                                        );
                                    }
                                    Some(_) => {}
                                }
                            }
                        }
                        let tags = stats_col_tags(&tlty, &[&observed, &expected]);
                        (
                            ExecExpr::Prim {
                                op: ExecPrimOp::StatsChiSquareGof { observed, expected },
                                args: vec![tex],
                            },
                            LTy::new(Ty::StatTest, tags),
                        )
                    }
                    _ => {
                        self.diags.push(
                            Diagnostic::error(
                                DiagCode::TypeError,
                                "`Stats.chi_square` requires either `(tbl, x: .a, y: .b)` or `(tbl, observed: .obs, expected: .exp)`",
                            )
                            .with_span(span),
                        );
                        (ExecExpr::Lit(Literal::Unit), LTy::public(Ty::StatTest))
                    }
                }
            }
            ("Stats", "outliers") => {
                let Some(CallArg::Positional(tbl_e)) = args.first() else {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::TypeError,
                            "`Stats.outliers` requires a table argument",
                        )
                        .with_span(span),
                    );
                    return (
                        ExecExpr::Lit(Literal::Unit),
                        LTy::public(Ty::Table(TableTy::default())),
                    );
                };
                let (tex, tlty) = self.check_expr(tbl_e, env, None, pc, scope, ret_ctx);
                let col = named_dot_col(args, "column").unwrap_or_default();
                let method = match named_expr_arg(args, "method") {
                    None => crate::stats::OutlierMethod::ZScore,
                    Some(Expr {
                        kind: ExprKind::Atom(m),
                        ..
                    }) if m == "zscore" => crate::stats::OutlierMethod::ZScore,
                    Some(Expr {
                        kind: ExprKind::Atom(m),
                        ..
                    }) if m == "iqr" => crate::stats::OutlierMethod::Iqr,
                    Some(other) => {
                        self.diags.push(
                            Diagnostic::error(
                                DiagCode::TypeError,
                                "`Stats.outliers` `method:` must be `:zscore` or `:iqr`",
                            )
                            .with_span(other.span),
                        );
                        crate::stats::OutlierMethod::ZScore
                    }
                };
                let default_thresh = match method {
                    crate::stats::OutlierMethod::ZScore => 3.0_f64,
                    crate::stats::OutlierMethod::Iqr => 1.5_f64,
                };
                let (thresh_ex, thresh_tags) = match named_expr_arg(args, "threshold") {
                    Some(te) => {
                        let (ex, lty) =
                            self.check_expr(te, env, Some(&Ty::Float), pc, scope, ret_ctx);
                        if !matches!(lty.ty, Ty::Float | Ty::Int | Ty::Decimal) {
                            self.diags.push(
                                Diagnostic::error(
                                    DiagCode::TypeError,
                                    "`Stats.outliers` `threshold:` must be numeric (`Float`, `Decimal`, or `Int`)",
                                )
                                .with_span(te.span),
                            );
                        }
                        (ex, lty.effective_tags())
                    }
                    None => (
                        ExecExpr::Lit(Literal::Float(Float64::from_f64(default_thresh))),
                        TagSet::empty(),
                    ),
                };
                let flag_col = match named_expr_arg(args, "flag") {
                    None => "outlier?".to_string(),
                    Some(Expr {
                        kind: ExprKind::Text { value: s, .. },
                        ..
                    }) if !s.is_empty() => s.clone(),
                    Some(other) => {
                        self.diags.push(
                            Diagnostic::error(
                                DiagCode::TypeError,
                                "`Stats.outliers` `flag:` must be a non-empty string literal",
                            )
                            .with_span(other.span),
                        );
                        "outlier?".to_string()
                    }
                };
                let Ty::Table(ref in_tt) = tlty.ty else {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::TypeError,
                            "`Stats.outliers` first argument must be a `Table`",
                        )
                        .with_span(tbl_e.span),
                    );
                    return (
                        ExecExpr::Lit(Literal::Unit),
                        LTy::public(Ty::Table(TableTy::default())),
                    );
                };
                let col_tags = match in_tt.find_col(&col) {
                    Some(cs) => {
                        if numeric_core_of_scalar(&cs.ty).is_none() {
                            self.diags.push(
                                Diagnostic::error(
                                    DiagCode::TypeError,
                                    format!("`Stats.outliers` requires numeric column `.{col}`"),
                                )
                                .with_span(span),
                            );
                        }
                        cs.tags.clone()
                    }
                    None => {
                        self.diags.push(
                            Diagnostic::error(
                                DiagCode::TypeError,
                                format!("unknown column `.{col}` in `Stats.outliers`"),
                            )
                            .with_span(span),
                        );
                        TagSet::empty()
                    }
                };
                if in_tt.find_col(&flag_col).is_some() {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::TypeError,
                            format!(
                                "`Stats.outliers` flag column `{flag_col}` already exists in table"
                            ),
                        )
                        .with_span(span),
                    );
                }
                let flag_tags = col_tags
                    .union(&in_tt.row_tags)
                    .union(&in_tt.order_tags)
                    .union(&thresh_tags);
                let mut out_cols = in_tt.cols.clone();
                out_cols.push(ColSpec {
                    name: flag_col.clone(),
                    ty: ScalarTy::Bool,
                    tags: flag_tags.clone(),
                    bucketed: false,
                    agg_kind: AggKind::Raw,
                });
                let out_tt = TableTy {
                    cols: out_cols,
                    row_tags: in_tt.row_tags.clone(),
                    order_tags: in_tt.order_tags.clone(),
                    grouped_by: None,
                    summarized: false,
                    distinct_by: None,
                };
                (
                    ExecExpr::Prim {
                        op: ExecPrimOp::StatsOutliers {
                            col,
                            method,
                            flag_col,
                            flag_tags,
                        },
                        args: vec![tex, thresh_ex],
                    },
                    LTy::new(Ty::Table(out_tt), tlty.tags),
                )
            }
            _ => {
                // Qualified call to an imported local or vendored module (`Helpers.double(...)`
                // or `Acme.Helpers.double(...)`).
                if let Some((mod_idx, rm)) =
                    self.resolved.modules.iter().enumerate().find(|(_, m)| {
                        m.full_name == ns || m.full_name.rsplit('.').next() == Some(ns)
                    })
                {
                    if !crate::check::resolve::is_symbol_exposed(rm, method) {
                        self.diags.push(
                            Diagnostic::error(
                                DiagCode::ResolveError,
                                format!(
                                    "function `{method}` is not exposed by module `{}`",
                                    rm.full_name
                                ),
                            )
                            .with_span(span),
                        );
                        return (ExecExpr::Lit(Literal::Unit), LTy::public(Ty::Unit));
                    }
                    if let Some(sig) = self.fn_sigs.get(method).cloned()
                        && sig.module_idx == mod_idx
                    {
                        if !sig.is_pure && !pc.is_empty() {
                            self.diags.push(
                                Diagnostic::error(
                                    DiagCode::PrivacyError,
                                    format!(
                                        "cannot call impure function `{ns}.{method}` under sensitive control flow {:?}",
                                        pc.elems()
                                    ),
                                )
                                .with_span(span),
                            );
                        }
                        let ret_lty = self
                            .ensure_fn_checked(method)
                            .or(sig.ret)
                            .unwrap_or_else(|| LTy::public(Ty::Unit));
                        if args.len() != sig.params.len() {
                            self.diags.push(
                                Diagnostic::error(
                                    DiagCode::TypeError,
                                    format!(
                                        "function `{ns}.{method}` expects {} argument(s), got {}",
                                        sig.params.len(),
                                        args.len()
                                    ),
                                )
                                .with_span(span),
                            );
                        }
                        let mut lowered_args = Vec::with_capacity(args.len());
                        let mut arg_tags = TagSet::empty();
                        for (i, arg) in args.iter().enumerate() {
                            let expr_arg = match arg {
                                CallArg::Positional(e) | CallArg::Named { value: e, .. } => e,
                            };
                            let param_lty = sig.params.get(i).map(|(_, l)| l);
                            let (mut aex, alty) = self.check_expr(
                                expr_arg,
                                env,
                                param_lty.map(|l| &l.ty),
                                pc,
                                scope,
                                ret_ctx,
                            );
                            if let Some(plty) = param_lty {
                                aex = self.coerce_expr(
                                    aex,
                                    &alty,
                                    plty,
                                    expr_arg.span,
                                    &format!("argument {} of `{ns}.{method}`", i + 1),
                                );
                            }
                            arg_tags = arg_tags.union(&alty.tags);
                            lowered_args.push(aex);
                        }
                        let out_ret = taint_return_with_pc(ret_lty, &arg_tags, pc);
                        return (
                            ExecExpr::Call {
                                fn_name: method.to_string(),
                                args: lowered_args,
                            },
                            out_ret,
                        );
                    }
                }
                self.diags.push(
                    Diagnostic::error(
                        DiagCode::ResolveError,
                        format!("unknown static call `{ns}.{method}`"),
                    )
                    .with_span(span),
                );
                (ExecExpr::Lit(Literal::Unit), LTy::public(Ty::Unit))
            }
        }
    }

    #[expect(
        clippy::too_many_arguments,
        reason = "method call handles capabilities, tables, scalars, lists, and privacy sink checks"
    )]
    fn check_method_call_on_val(
        &mut self,
        rex: ExecExpr,
        rlty: LTy,
        member: &ast::SpannedName,
        args: &[CallArg],
        span: Span,
        env: &HashMap<Ident, VarBinding>,
        pc: &TagSet,
        scope: LocalScopeKind,
        ret_ctx: Option<(&str, Option<&Ty>)>,
    ) -> (ExecExpr, LTy) {
        // Capability methods: Console, ReadFiles, WriteFiles, ReadDB, WriteTable, HttpsAllow.
        match (&rlty.ty, member.name.as_str()) {
            (
                Ty::Console(allows),
                "print" | "error" | "print_table" | "print_chart" | "print_profile",
            ) => {
                let Some(CallArg::Positional(arg0)) = args.first() else {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::TypeError,
                            format!("`console.{}` requires 1 argument", member.name),
                        )
                        .with_span(span),
                    );
                    return (ExecExpr::Lit(Literal::Unit), LTy::public(Ty::Unit));
                };
                let (aex, alty) = self.check_expr(arg0, env, None, pc, scope, ret_ctx);
                let eff_tags = alty.effective_tags().union(pc);
                if !eff_tags.is_subset(allows) {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::PrivacyError,
                            format!(
                                "cannot output sensitive value tagged {:?} to `Console` (allows {:?})",
                                eff_tags.elems(),
                                allows.elems()
                            ),
                        )
                        .with_primary(arg0.span, "sensitive data flows into unauthorized `Console` sink")
                        .with_hint("use `redact`, `pseudonymize`, or `suppress_small_groups` before printing"),
                    );
                }
                let hop = match member.name.as_str() {
                    "print" => ExecHostOp::Core(HostOp::ConsolePrint),
                    "error" => ExecHostOp::Core(HostOp::ConsoleError),
                    "print_table" => ExecHostOp::Core(HostOp::ConsolePrintTable),
                    "print_chart" => ExecHostOp::ConsolePrintChart,
                    _ => ExecHostOp::ConsolePrintProfile,
                };
                return (
                    ExecExpr::Host {
                        op: hop,
                        args: vec![rex, aex],
                    },
                    LTy::public(Ty::Unit),
                );
            }
            (Ty::ReadFiles, "read_csv" | "read_jsonl" | "read_xlsx") => {
                let Some(CallArg::Positional(path_e)) = args.first() else {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::TypeError,
                            format!("`files.{}` requires a path argument", member.name),
                        )
                        .with_span(span),
                    );
                    return (ExecExpr::Lit(Literal::Unit), LTy::public(Ty::Unit));
                };
                let (pex, plty) = self.check_expr(path_e, env, Some(&Ty::Text), pc, scope, ret_ctx);
                let Some(schema_name) = named_cap_arg(args, "as") else {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::SchemaError,
                            format!("`files.{}` requires `as: SchemaName`", member.name),
                        )
                        .with_span(span),
                    );
                    return (ExecExpr::Lit(Literal::Unit), LTy::public(Ty::Unit));
                };
                let Some(cs) = self.schemas.get(&schema_name).cloned() else {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::SchemaError,
                            format!("unknown schema `{schema_name}`"),
                        )
                        .with_span(span),
                    );
                    return (ExecExpr::Lit(Literal::Unit), LTy::public(Ty::Unit));
                };
                let mut error_on_bad_rows = false;
                let mut coerce_integral_floats = false;
                let mut seen_as = false;
                let mut seen_bad_mode = false;
                let mut seen_coerce = false;
                let mut seen_sheet = false;
                for arg in args.iter().skip(1) {
                    match arg {
                        CallArg::Positional(e) => {
                            self.diags.push(
                                Diagnostic::error(
                                    DiagCode::TypeError,
                                    format!(
                                        "unexpected positional argument in `files.{}`",
                                        member.name
                                    ),
                                )
                                .with_span(e.span),
                            );
                        }
                        CallArg::Named { name, .. } if name.name == "as" => {
                            if seen_as {
                                self.diags.push(
                                    Diagnostic::error(
                                        DiagCode::TypeError,
                                        format!(
                                            "duplicate `as:` argument in `files.{}`",
                                            member.name
                                        ),
                                    )
                                    .with_span(name.span),
                                );
                            }
                            seen_as = true;
                        }
                        CallArg::Named { name, .. }
                            if member.name == "read_xlsx" && name.name == "sheet" =>
                        {
                            if seen_sheet {
                                self.diags.push(
                                    Diagnostic::error(
                                        DiagCode::TypeError,
                                        "duplicate `sheet:` argument in `files.read_xlsx`",
                                    )
                                    .with_span(name.span),
                                );
                            }
                            seen_sheet = true;
                        }
                        CallArg::Named { name, value, .. }
                            if member.name == "read_csv" && name.name == "on_bad_rows" =>
                        {
                            if seen_bad_mode {
                                self.diags.push(
                                    Diagnostic::error(
                                        DiagCode::TypeError,
                                        "duplicate `on_bad_rows:` argument in `files.read_csv`",
                                    )
                                    .with_span(name.span),
                                );
                            }
                            seen_bad_mode = true;
                            match &value.kind {
                                ExprKind::Atom(a) if a == "quarantine" => error_on_bad_rows = false,
                                ExprKind::Atom(a) if a == "error" => error_on_bad_rows = true,
                                _ => {
                                    self.diags.push(
                                        Diagnostic::error(
                                            DiagCode::TypeError,
                                            "`files.read_csv` `on_bad_rows:` must be `:quarantine` or `:error`",
                                        )
                                        .with_span(value.span),
                                    );
                                }
                            }
                        }
                        CallArg::Named { name, value, .. }
                            if member.name == "read_csv"
                                && name.name == "coerce_integral_floats" =>
                        {
                            if seen_coerce {
                                self.diags.push(
                                    Diagnostic::error(
                                        DiagCode::TypeError,
                                        "duplicate `coerce_integral_floats:` argument in `files.read_csv`",
                                    )
                                    .with_span(name.span),
                                );
                            }
                            seen_coerce = true;
                            if let ExprKind::Bool(b) = &value.kind {
                                coerce_integral_floats = *b;
                            } else {
                                self.diags.push(
                                    Diagnostic::error(
                                        DiagCode::TypeError,
                                        "`files.read_csv` `coerce_integral_floats:` must be a `Bool` literal (`true` or `false`)",
                                    )
                                    .with_span(value.span),
                                );
                            }
                        }
                        CallArg::Named { name, .. }
                            if name.name == "on_bad_rows"
                                || name.name == "coerce_integral_floats" =>
                        {
                            self.diags.push(
                                Diagnostic::error(
                                    DiagCode::TypeError,
                                    format!(
                                        "`files.{}` does not support `{}:`",
                                        member.name, name.name
                                    ),
                                )
                                .with_span(name.span),
                            );
                        }
                        CallArg::Named { name, .. } => {
                            self.diags.push(
                                Diagnostic::error(
                                    DiagCode::TypeError,
                                    format!(
                                        "unknown argument `{}:` in `files.{}`",
                                        name.name, member.name
                                    ),
                                )
                                .with_span(name.span),
                            );
                        }
                    }
                }
                let ok_ty = if error_on_bad_rows {
                    Ty::Table(cs.decl.schema)
                } else {
                    let bad_tt = quarantine_bad_row_table_ty(&cs.decl.schema);
                    Ty::Tuple(vec![
                        LTy::public(Ty::Table(cs.decl.schema)),
                        LTy::public(Ty::Table(bad_tt)),
                    ])
                };
                let res_ty = Ty::Result {
                    ok_ty: Box::new(ok_ty),
                    err_ty: Box::new(Ty::Text),
                };
                let mut call_args = vec![rex, pex];
                let mut out_tags = plty.tags;
                let hop = match member.name.as_str() {
                    "read_csv" => {
                        if !error_on_bad_rows && !coerce_integral_floats {
                            ExecHostOp::Core(HostOp::ReadCsv(schema_name))
                        } else {
                            ExecHostOp::ReadCsvEx {
                                schema: schema_name,
                                error_on_bad_rows,
                                coerce_integral_floats,
                            }
                        }
                    }
                    "read_jsonl" => ExecHostOp::ReadJsonl(schema_name),
                    _ => {
                        let sheet = match named_expr_arg(args, "sheet") {
                            Some(Expr {
                                kind: ExprKind::Text { value, .. },
                                ..
                            }) => Some(value.clone()),
                            Some(sheet_e) => {
                                let (sex, slty) = self.check_expr(
                                    sheet_e,
                                    env,
                                    Some(&Ty::Text),
                                    pc,
                                    scope,
                                    ret_ctx,
                                );
                                out_tags = out_tags.union(&slty.tags);
                                call_args.push(sex);
                                None
                            }
                            None => None,
                        };
                        ExecHostOp::ReadXlsx {
                            schema: schema_name,
                            sheet,
                        }
                    }
                };
                return (
                    ExecExpr::Host {
                        op: hop,
                        args: call_args,
                    },
                    LTy::new(res_ty, out_tags),
                );
            }
            (Ty::ReadFiles, "read_parquet") => {
                let Some(CallArg::Positional(path_e)) = args.first() else {
                    return (ExecExpr::Lit(Literal::Unit), LTy::public(Ty::Unit));
                };
                let (pex, plty) = self.check_expr(path_e, env, Some(&Ty::Text), pc, scope, ret_ctx);
                let Some(schema_name) = named_cap_arg(args, "as") else {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::SchemaError,
                            "`read_parquet` requires `as: SchemaName`",
                        )
                        .with_span(span),
                    );
                    return (ExecExpr::Lit(Literal::Unit), LTy::public(Ty::Unit));
                };
                let Some(cs) = self.schemas.get(&schema_name).cloned() else {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::SchemaError,
                            format!("unknown schema `{schema_name}`"),
                        )
                        .with_span(span),
                    );
                    return (ExecExpr::Lit(Literal::Unit), LTy::public(Ty::Unit));
                };
                let res_ty = Ty::Result {
                    ok_ty: Box::new(Ty::Table(cs.decl.schema.clone())),
                    err_ty: Box::new(Ty::Text),
                };
                return (
                    ExecExpr::Host {
                        op: ExecHostOp::Core(HostOp::ReadParquet(cs.decl.schema)),
                        args: vec![rex, pex],
                    },
                    LTy::new(res_ty, plty.tags),
                );
            }
            (
                Ty::WriteFiles { root, allows },
                "write_html" | "write_markdown" | "write_svg" | "write_parquet" | "write_xlsx"
                | "write_csv" | "write_jsonl" | "write_text" | "write_file",
            ) => {
                let Some(CallArg::Positional(path_e)) = args.first() else {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::TypeError,
                            format!("`out.{}` requires a relative path", member.name),
                        )
                        .with_span(span),
                    );
                    return (ExecExpr::Lit(Literal::Unit), LTy::public(Ty::Unit));
                };
                if let ExprKind::Text { value: p, .. } = &path_e.kind
                    && !crate::core::check::is_safe_relative_path(p)
                {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::CapabilityError,
                            format!("unsafe export path `{p}` escapes `WriteFiles(\"{root}\")` confinement"),
                        )
                        .with_span(path_e.span),
                    );
                }
                let (pex, plty) = self.check_expr(path_e, env, Some(&Ty::Text), pc, scope, ret_ctx);

                let mut payload_expr: Option<&Expr> = None;
                let mut private_expr: Option<&Expr> = None;
                let mut sanitize_expr: Option<&Expr> = None;
                for extra in args.iter().skip(1) {
                    match extra {
                        CallArg::Positional(e) => {
                            if payload_expr.is_none() {
                                payload_expr = Some(e);
                            } else {
                                self.diags.push(
                                    Diagnostic::error(
                                        DiagCode::TypeError,
                                        format!(
                                            "unexpected extra positional argument in `out.{}`",
                                            member.name
                                        ),
                                    )
                                    .with_span(e.span),
                                );
                            }
                        }
                        CallArg::Named { name, value, .. } => match name.name.as_str() {
                            "sheets" if member.name == "write_xlsx" => {
                                if payload_expr.is_some() {
                                    self.diags.push(
                                        Diagnostic::error(
                                            DiagCode::TypeError,
                                            "duplicate payload/`sheets:` argument in `out.write_xlsx`",
                                        )
                                        .with_span(name.span),
                                    );
                                } else {
                                    payload_expr = Some(value);
                                }
                            }
                            "private" => {
                                if private_expr.is_some() {
                                    self.diags.push(
                                        Diagnostic::error(
                                            DiagCode::TypeError,
                                            format!(
                                                "duplicate `private:` argument in `out.{}`",
                                                member.name
                                            ),
                                        )
                                        .with_span(name.span),
                                    );
                                } else {
                                    private_expr = Some(value);
                                }
                            }
                            "sanitize_formulas" if member.name == "write_csv" => {
                                if sanitize_expr.is_some() {
                                    self.diags.push(
                                        Diagnostic::error(
                                            DiagCode::TypeError,
                                            "duplicate `sanitize_formulas:` argument in `out.write_csv`",
                                        )
                                        .with_span(name.span),
                                    );
                                } else {
                                    sanitize_expr = Some(value);
                                }
                            }
                            "sanitize_formulas" => {
                                self.diags.push(
                                    Diagnostic::error(
                                        DiagCode::TypeError,
                                        format!("`sanitize_formulas:` is only valid on `out.write_csv`, not `out.{}`", member.name),
                                    )
                                    .with_span(name.span),
                                );
                            }
                            other => {
                                self.diags.push(
                                    Diagnostic::error(
                                        DiagCode::TypeError,
                                        format!(
                                            "unknown argument `{other}:` in `out.{}`",
                                            member.name
                                        ),
                                    )
                                    .with_span(name.span),
                                );
                            }
                        },
                    }
                }

                let (pay_ex, pay_tags) = if let Some(pe) = payload_expr {
                    let (ex, lty) = self.check_expr(pe, env, None, pc, scope, ret_ctx);
                    if member.name == "write_markdown" && !matches!(lty.ty, Ty::Report(_)) {
                        self.diags.push(
                            Diagnostic::error(
                                DiagCode::TypeError,
                                "`out.write_markdown` requires a `Report` payload",
                            )
                            .with_span(pe.span),
                        );
                    } else if member.name == "write_svg" && !matches!(lty.ty, Ty::Chart(_)) {
                        self.diags.push(
                            Diagnostic::error(
                                DiagCode::TypeError,
                                "`out.write_svg` requires a `Chart` payload",
                            )
                            .with_span(pe.span),
                        );
                    } else if matches!(member.name.as_str(), "write_text" | "write_file")
                        && lty.ty != Ty::Text
                    {
                        self.diags.push(
                            Diagnostic::error(
                                DiagCode::TypeError,
                                format!("`out.{}` requires a `Text` payload", member.name),
                            )
                            .with_span(pe.span),
                        );
                    }
                    let tags = lty.effective_tags();
                    let coerced = if member.name == "write_parquet"
                        && let Ty::Table(ref tt) = lty.ty
                    {
                        // Materialize exact static column types (including derived/summarized
                        // columns) even when the table has 0 rows at runtime.
                        ExecExpr::Prim {
                            op: ExecPrimOp::TableCoerce(tt.clone()),
                            args: vec![ex],
                        }
                    } else {
                        ex
                    };
                    (coerced, tags)
                } else {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::TypeError,
                            format!("`out.{}` requires a payload argument", member.name),
                        )
                        .with_span(span),
                    );
                    (ExecExpr::Lit(Literal::Unit), TagSet::empty())
                };

                let mut total_tags = pay_tags.union(&plty.effective_tags()).union(pc);
                let has_explicit_private = private_expr.is_some();
                let priv_ex = if let Some(pe) = private_expr {
                    let (ex, lty) = self.check_expr(pe, env, Some(&Ty::Bool), pc, scope, ret_ctx);
                    if lty.ty != Ty::Bool {
                        self.diags.push(
                            Diagnostic::error(
                                DiagCode::TypeError,
                                format!(
                                    "`private:` in `out.{}` must be `Bool`, found `{:?}`",
                                    member.name, lty.ty
                                ),
                            )
                            .with_span(pe.span),
                        );
                    }
                    total_tags = total_tags.union(&lty.effective_tags());
                    ex
                } else {
                    ExecExpr::Lit(Literal::Bool(false))
                };
                let san_ex = if let Some(se) = sanitize_expr {
                    let (ex, lty) = self.check_expr(se, env, Some(&Ty::Bool), pc, scope, ret_ctx);
                    if lty.ty != Ty::Bool {
                        self.diags.push(
                            Diagnostic::error(
                                DiagCode::TypeError,
                                format!(
                                    "`sanitize_formulas:` in `out.write_csv` must be `Bool`, found `{:?}`",
                                    lty.ty
                                ),
                            )
                            .with_span(se.span),
                        );
                    }
                    total_tags = total_tags.union(&lty.effective_tags());
                    ex
                } else {
                    ExecExpr::Lit(Literal::Bool(false))
                };

                if !total_tags.is_subset(allows) {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::PrivacyError,
                            format!(
                                "cannot write sensitive data tagged {:?} to `WriteFiles(\"{root}\", allows: {:?})`",
                                total_tags.elems(),
                                allows.elems()
                            ),
                        )
                        .with_span(span),
                    );
                }
                let (hop, op_args) = match member.name.as_str() {
                    "write_csv" => (
                        ExecHostOp::WriteCsv,
                        vec![rex, pex, pay_ex, priv_ex, san_ex],
                    ),
                    "write_jsonl" => (ExecHostOp::WriteJsonl, vec![rex, pex, pay_ex, priv_ex]),
                    "write_markdown" => (
                        ExecHostOp::WriteReportMarkdown,
                        vec![rex, pex, pay_ex, priv_ex],
                    ),
                    "write_svg" => (ExecHostOp::WriteChartSvg, vec![rex, pex, pay_ex, priv_ex]),
                    other => {
                        let core_op = match other {
                            "write_html" => HostOp::WriteReportHtml,
                            "write_parquet" => HostOp::WriteParquet,
                            "write_xlsx" => HostOp::WriteXlsx,
                            _ => HostOp::WriteFile,
                        };
                        if has_explicit_private {
                            (
                                ExecHostOp::WritePrivate { inner: core_op },
                                vec![rex, pex, pay_ex, priv_ex],
                            )
                        } else {
                            (ExecHostOp::Core(core_op), vec![rex, pex, pay_ex])
                        }
                    }
                };
                let res_ty = Ty::Result {
                    ok_ty: Box::new(Ty::Unit),
                    err_ty: Box::new(Ty::Text),
                };
                return (
                    ExecExpr::Host {
                        op: hop,
                        args: op_args,
                    },
                    LTy::public(res_ty),
                );
            }
            (Ty::ReadDB(db), "table") => {
                let sname = match args.first() {
                    Some(CallArg::Positional(Expr {
                        kind: ExprKind::CapName(s),
                        ..
                    })) => s.clone(),
                    _ => {
                        self.diags.push(
                            Diagnostic::error(
                                DiagCode::SchemaError,
                                "`db.table(Schema)` expects a schema name",
                            )
                            .with_span(span),
                        );
                        return (ExecExpr::Lit(Literal::Unit), LTy::public(Ty::Unit));
                    }
                };
                let mut from_table: Option<String> = None;
                for extra in args.iter().skip(1) {
                    match extra {
                        CallArg::Named { name, value, .. } if name.name == "from" => {
                            if from_table.is_some() {
                                self.diags.push(
                                    Diagnostic::error(
                                        DiagCode::TypeError,
                                        "duplicate `from:` argument in `db.table(...)`",
                                    )
                                    .with_span(name.span),
                                );
                                continue;
                            }
                            match &value.kind {
                                ExprKind::Text { value: raw, .. } if !raw.trim().is_empty() => {
                                    from_table = Some(raw.clone());
                                }
                                _ => {
                                    self.diags.push(
                                        Diagnostic::error(
                                            DiagCode::SchemaError,
                                            "`db.table(..., from: \"...\")` requires a non-empty string literal table reference",
                                        )
                                        .with_span(value.span),
                                    );
                                }
                            }
                        }
                        CallArg::Named { name, .. } => {
                            self.diags.push(
                                Diagnostic::error(
                                    DiagCode::TypeError,
                                    format!(
                                        "unknown named argument `{}` in `db.table(...)` (expected `from:`)",
                                        name.name
                                    ),
                                )
                                .with_span(name.span),
                            );
                        }
                        CallArg::Positional(e) => {
                            self.diags.push(
                                Diagnostic::error(
                                    DiagCode::TypeError,
                                    "`db.table(Schema, from: \"...\")` accepts only one positional schema argument",
                                )
                                .with_span(e.span),
                            );
                        }
                    }
                }
                let Some(cs) = self.schemas.get(&sname).cloned() else {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::SchemaError,
                            format!("unknown schema `{sname}`"),
                        )
                        .with_span(span),
                    );
                    return (ExecExpr::Lit(Literal::Unit), LTy::public(Ty::Unit));
                };
                let lookup_name = from_table.as_deref().unwrap_or(&sname);
                let mut resolved_table_name = lookup_name.to_string();
                if let Some(locked_db) = self.schema_lock.and_then(|l| l.find_db(db)) {
                    match locked_db.resolve_table(lookup_name) {
                        Ok(locked_tbl) => {
                            resolved_table_name = locked_tbl.name.clone();
                            for col in &cs.decl.schema.cols {
                                let Some(locked_col) = locked_tbl.find_col(&col.name) else {
                                    self.diags.push(
                                        Diagnostic::error(
                                            DiagCode::SchemaError,
                                            format!(
                                                "column `{}.{}` declared in schema `{sname}` is missing from schema.lock for db `{db}`",
                                                locked_tbl.name, col.name
                                            ),
                                        )
                                        .with_span(span),
                                    );
                                    continue;
                                };
                                let locked_ty = locked_col.effective_scalar_ty();
                                if !crate::db::schema_lock::read_lock_ty_compatible(
                                    &locked_ty, &col.ty,
                                ) {
                                    self.diags.push(
                                        Diagnostic::error(
                                            DiagCode::SchemaError,
                                            format!(
                                                "column `{}.{}` type drift: schema.lock has `{locked_ty:?}`, schema `{sname}` declares `{:?}`",
                                                locked_tbl.name, col.name, col.ty
                                            ),
                                        )
                                        .with_span(span),
                                    );
                                }
                                if !locked_col.tags.is_subset(&col.tags) {
                                    let missing = locked_col.tags.diff(&col.tags);
                                    self.diags.push(
                                        Diagnostic::error(
                                            DiagCode::PrivacyError,
                                            format!(
                                                "column `{}.{}` requires sensitivity tags {:?} from schema.lock, but schema `{sname}` omits {:?}",
                                                locked_tbl.name,
                                                col.name,
                                                locked_col.tags.elems(),
                                                missing.elems()
                                            ),
                                        )
                                        .with_span(span),
                                    );
                                }
                            }
                        }
                        Err(err) => {
                            self.diags.push(
                                Diagnostic::error(DiagCode::SchemaError, err.to_string())
                                    .with_span(span),
                            );
                        }
                    }
                }
                return (
                    ExecExpr::Rel(Box::new(ExecPlan::SourceDB {
                        cap: Box::new(rex),
                        table_name: resolved_table_name,
                        schema: cs.decl.schema.clone(),
                    })),
                    LTy::public(Ty::Table(cs.decl.schema)),
                );
            }
            (
                Ty::WriteTable {
                    db,
                    table_name,
                    allows,
                    ..
                },
                "upsert",
            ) => {
                let Some(CallArg::Positional(tbl_e)) = args.first() else {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::TypeError,
                            "`WriteTable.upsert` requires a table argument",
                        )
                        .with_span(span),
                    );
                    return (ExecExpr::Lit(Literal::Unit), LTy::public(Ty::Unit));
                };
                let (tex, tlty) = self.check_expr(tbl_e, env, None, pc, scope, ret_ctx);
                let eff_tags = tlty.effective_tags().union(pc);
                if !eff_tags.is_subset(allows) {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::PrivacyError,
                            format!(
                                "cannot upsert sensitive table tagged {:?} into `WriteTable({db}, \"{table_name}\", allows: {:?})`",
                                eff_tags.elems(),
                                allows.elems()
                            ),
                        )
                        .with_span(span),
                    );
                }
                let key_col = match named_dot_col(args, "key") {
                    Some(k) => k,
                    None => {
                        self.diags.push(
                            Diagnostic::error(
                                DiagCode::TypeError,
                                "`WriteTable.upsert` requires `key: .column`",
                            )
                            .with_span(span),
                        );
                        String::new()
                    }
                };
                match &tlty.ty {
                    Ty::Table(src_tt) => {
                        if !key_col.is_empty() && src_tt.find_col(&key_col).is_none() {
                            self.diags.push(
                                Diagnostic::error(
                                    DiagCode::TypeError,
                                    format!(
                                        "upsert key column `.{key_col}` does not exist on input table"
                                    ),
                                )
                                .with_span(span),
                            );
                        }
                        if let Some(locked_db) = self.schema_lock.and_then(|l| l.find_db(db)) {
                            match locked_db.resolve_table(table_name) {
                                Ok(locked_tbl) => {
                                    if !key_col.is_empty()
                                        && locked_tbl.find_col(&key_col).is_none()
                                    {
                                        self.diags.push(
                                            Diagnostic::error(
                                                DiagCode::SchemaError,
                                                format!(
                                                    "upsert key column `{}.{key_col}` missing from schema.lock for db `{db}`",
                                                    locked_tbl.name
                                                ),
                                            )
                                            .with_span(span),
                                        );
                                    }
                                    for src_col in &src_tt.cols {
                                        let Some(dest_col) = locked_tbl.find_col(&src_col.name)
                                        else {
                                            self.diags.push(
                                                Diagnostic::error(
                                                    DiagCode::SchemaError,
                                                    format!(
                                                        "column `{}.{}` missing from destination table in schema.lock for db `{db}`",
                                                        locked_tbl.name, src_col.name
                                                    ),
                                                )
                                                .with_span(span),
                                            );
                                            continue;
                                        };
                                        let dest_ty = dest_col.effective_scalar_ty();
                                        if dest_ty != src_col.ty {
                                            self.diags.push(
                                                Diagnostic::error(
                                                    DiagCode::SchemaError,
                                                    format!(
                                                        "column `{}.{}` type drift on WriteTable.upsert: schema.lock has `{dest_ty:?}`, input table has `{:?}`",
                                                        locked_tbl.name, src_col.name, src_col.ty
                                                    ),
                                                )
                                                .with_span(span),
                                            );
                                        }
                                        if !src_col.tags.is_subset(&dest_col.tags) {
                                            let unauth = src_col.tags.diff(&dest_col.tags);
                                            self.diags.push(
                                                Diagnostic::error(
                                                    DiagCode::PrivacyError,
                                                    format!(
                                                        "cannot upsert column `{}` tagged {:?} into destination column `{}.{}` tagged {:?} in schema.lock (unauthorized tags: {:?})",
                                                        src_col.name,
                                                        src_col.tags.elems(),
                                                        locked_tbl.name,
                                                        dest_col.name,
                                                        dest_col.tags.elems(),
                                                        unauth.elems()
                                                    ),
                                                )
                                                .with_span(span),
                                            );
                                        }
                                    }
                                }
                                Err(err) => {
                                    self.diags.push(
                                        Diagnostic::error(DiagCode::SchemaError, err.to_string())
                                            .with_span(span),
                                    );
                                }
                            }
                        }
                    }
                    _ => {
                        self.diags.push(
                            Diagnostic::error(
                                DiagCode::TypeError,
                                "`WriteTable.upsert` first argument must be a `Table(...)`",
                            )
                            .with_span(tbl_e.span),
                        );
                    }
                }
                let res_ty = Ty::Result {
                    ok_ty: Box::new(Ty::Data(TY_UPSERT_STATS.to_string())),
                    err_ty: Box::new(Ty::Text),
                };
                return (
                    ExecExpr::Host {
                        op: ExecHostOp::WriteTableUpsert {
                            key_col,
                            allows: allows.clone(),
                        },
                        args: vec![rex, tex],
                    },
                    LTy::public(res_ty),
                );
            }
            (Ty::RawReadDB(db), "raw_sql") => {
                let sql = match args.first() {
                    Some(CallArg::Positional(Expr {
                        kind: ExprKind::Text { value, .. },
                        ..
                    })) => value.clone(),
                    Some(CallArg::Positional(other)) => {
                        self.diags.push(
                            Diagnostic::error(
                                DiagCode::CapabilityError,
                                "`RawReadDB.raw_sql` requires a compile-time constant SQL string literal (no string interpolation or dynamic expressions; bind values via `params: [...]`)",
                            )
                            .with_span(other.span),
                        );
                        return (ExecExpr::Lit(Literal::Unit), LTy::public(Ty::Unit));
                    }
                    _ => {
                        self.diags.push(
                            Diagnostic::error(
                                DiagCode::TypeError,
                                "`RawReadDB.raw_sql` requires a constant SQL string literal as its first argument",
                            )
                            .with_span(span),
                        );
                        return (ExecExpr::Lit(Literal::Unit), LTy::public(Ty::Unit));
                    }
                };
                let Some(schema_name) = named_cap_arg(args, "as") else {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::SchemaError,
                            "`RawReadDB.raw_sql` requires `as: SchemaName`",
                        )
                        .with_span(span),
                    );
                    return (ExecExpr::Lit(Literal::Unit), LTy::public(Ty::Unit));
                };
                let Some(cs) = self.schemas.get(&schema_name).cloned() else {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::SchemaError,
                            format!("unknown schema `{schema_name}`"),
                        )
                        .with_span(span),
                    );
                    return (ExecExpr::Lit(Literal::Unit), LTy::public(Ty::Unit));
                };
                let mut param_tags = TagSet::empty();
                let params_ex = if let Some(pe) = named_expr_arg(args, "params") {
                    if let ExprKind::List(items) = &pe.kind {
                        let mut pexprs = Vec::with_capacity(items.len());
                        for item in items {
                            let (iex, ilty) = self.check_expr(item, env, None, pc, scope, ret_ctx);
                            if ilty.ty.to_scalar_ty().is_none() {
                                self.diags.push(
                                    Diagnostic::error(
                                        DiagCode::TypeError,
                                        format!(
                                            "`raw_sql` param must be a scalar or `Option` scalar, got `{:?}`",
                                            ilty.ty
                                        ),
                                    )
                                    .with_span(item.span),
                                );
                            }
                            param_tags = param_tags.union(&ilty.effective_tags());
                            pexprs.push(iex);
                        }
                        ExecExpr::Tuple(pexprs)
                    } else {
                        let (pex, plty) = self.check_expr(pe, env, None, pc, scope, ret_ctx);
                        let valid_list = match &plty.ty {
                            Ty::List(elem) => {
                                elem.ty.to_scalar_ty().is_some()
                                    || matches!(
                                        &elem.ty,
                                        Ty::Data(n) if n == TY_UNRESOLVED_LIST_ELEM
                                    )
                            }
                            _ => false,
                        };
                        if !valid_list {
                            self.diags.push(
                                Diagnostic::error(
                                    DiagCode::TypeError,
                                    "`raw_sql` `params:` argument must be a list of scalar values",
                                )
                                .with_span(pe.span),
                            );
                        }
                        param_tags = param_tags.union(&plty.effective_tags());
                        pex
                    }
                } else {
                    ExecExpr::Tuple(Vec::new())
                };

                let taint = param_tags.union(pc);
                let mut out_schema = cs.decl.schema;
                out_schema.row_tags = out_schema.row_tags.union(&taint);
                let res_ty = Ty::Result {
                    ok_ty: Box::new(Ty::Table(out_schema.clone())),
                    err_ty: Box::new(Ty::Text),
                };
                return (
                    ExecExpr::Host {
                        op: ExecHostOp::RawSqlQuery {
                            db: db.clone(),
                            sql,
                            out_schema,
                        },
                        args: vec![rex, params_ex],
                    },
                    LTy::new(res_ty, taint),
                );
            }
            (Ty::HttpsAllow { host, allows }, "get_json") => {
                let Some(CallArg::Positional(url_e)) = args.first() else {
                    return (ExecExpr::Lit(Literal::Unit), LTy::public(Ty::Unit));
                };
                let (uex, ulty) = self.check_expr(url_e, env, Some(&Ty::Text), pc, scope, ret_ctx);
                let url_tags = ulty.effective_tags().union(pc);
                if !url_tags.is_subset(allows) {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::PrivacyError,
                            format!(
                                "cannot send URL tagged {:?} to `HttpsAllow(\"{host}\", allows: {:?})`",
                                url_tags.elems(),
                                allows.elems()
                            ),
                        )
                        .with_span(url_e.span),
                    );
                }
                let hdr_ex = if let Some(he) = named_expr_arg(args, "headers") {
                    let (hex, hlty) = self.check_expr(he, env, None, pc, scope, ret_ctx);
                    // Secrets are permitted in Authorization headers for authenticated HTTPS calls.
                    let non_secret = hlty.effective_tags().remove("secret");
                    if !non_secret.is_subset(allows) {
                        self.diags.push(
                            Diagnostic::error(
                                DiagCode::PrivacyError,
                                format!(
                                    "cannot send headers tagged {:?} to `HttpsAllow(\"{host}\", allows: {:?})`",
                                    non_secret.elems(),
                                    allows.elems()
                                ),
                            )
                            .with_span(he.span),
                        );
                    }
                    hex
                } else {
                    ExecExpr::Lit(Literal::Unit)
                };
                let res_ty = Ty::Result {
                    ok_ty: Box::new(Ty::Data(TY_JSON_RESPONSE.to_string())),
                    err_ty: Box::new(Ty::Text),
                };
                return (
                    ExecExpr::Host {
                        op: ExecHostOp::Core(HostOp::HttpsGetJson),
                        args: vec![rex, uex, hdr_ex],
                    },
                    LTy::public(res_ty),
                );
            }
            (Ty::Data(dname), "parse_table") if dname == TY_JSON_RESPONSE => {
                let (fex, _) = match args.first() {
                    Some(CallArg::Positional(e)) => {
                        self.check_expr(e, env, Some(&Ty::Text), pc, scope, ret_ctx)
                    }
                    _ => (
                        ExecExpr::Lit(Literal::Text(String::new())),
                        LTy::public(Ty::Text),
                    ),
                };
                let Some(sname) = named_cap_arg(args, "as") else {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::SchemaError,
                            "`parse_table` requires `as: SchemaName`",
                        )
                        .with_span(span),
                    );
                    return (ExecExpr::Lit(Literal::Unit), LTy::public(Ty::Unit));
                };
                let Some(cs) = self.schemas.get(&sname).cloned() else {
                    return (ExecExpr::Lit(Literal::Unit), LTy::public(Ty::Unit));
                };
                let bad_tt = quarantine_bad_row_table_ty(&cs.decl.schema);
                let out_ty = Ty::Tuple(vec![
                    LTy::public(Ty::Table(cs.decl.schema)),
                    LTy::public(Ty::Table(bad_tt)),
                ]);
                return (
                    ExecExpr::Host {
                        op: ExecHostOp::JsonParseTable(sname),
                        args: vec![rex, fex],
                    },
                    LTy::public(out_ty),
                );
            }
            (Ty::Data(dname), "bool_at") if dname == TY_JSON_RESPONSE => {
                let (fex, _) = match args.first() {
                    Some(CallArg::Positional(e)) => {
                        self.check_expr(e, env, Some(&Ty::Text), pc, scope, ret_ctx)
                    }
                    _ => (
                        ExecExpr::Lit(Literal::Text(String::new())),
                        LTy::public(Ty::Text),
                    ),
                };
                return (
                    ExecExpr::Host {
                        op: ExecHostOp::JsonBoolAt,
                        args: vec![rex, fex],
                    },
                    LTy::public(Ty::Bool),
                );
            }
            (Ty::Data(dname), "text_at") if dname == TY_JSON_RESPONSE => {
                let (fex, _) = match args.first() {
                    Some(CallArg::Positional(e)) => {
                        self.check_expr(e, env, Some(&Ty::Text), pc, scope, ret_ctx)
                    }
                    _ => (
                        ExecExpr::Lit(Literal::Text(String::new())),
                        LTy::public(Ty::Text),
                    ),
                };
                return (
                    ExecExpr::Host {
                        op: ExecHostOp::JsonTextAt,
                        args: vec![rex, fex],
                    },
                    LTy::public(Ty::Text),
                );
            }
            (Ty::Data(dname), "int_at") if dname == TY_JSON_RESPONSE => {
                let (fex, _) = match args.first() {
                    Some(CallArg::Positional(e)) => {
                        self.check_expr(e, env, Some(&Ty::Text), pc, scope, ret_ctx)
                    }
                    _ => (
                        ExecExpr::Lit(Literal::Text(String::new())),
                        LTy::public(Ty::Text),
                    ),
                };
                return (
                    ExecExpr::Host {
                        op: ExecHostOp::JsonIntAt,
                        args: vec![rex, fex],
                    },
                    LTy::public(Ty::Int),
                );
            }
            (Ty::Option(inner), "or_return") => {
                let Some(CallArg::Positional(ret_e)) = args.first() else {
                    return (rex, LTy::new(inner.as_ref().clone(), rlty.tags));
                };
                let r_exp = ret_ctx.and_then(|(_, t)| t);
                let ret_pc = pc.union(&rlty.tags);
                let (ret_ex, mut ret_lty) =
                    self.check_expr(ret_e, env, r_exp, &ret_pc, scope, ret_ctx);
                ret_lty.tags = ret_lty.tags.union(&ret_pc);
                let ret_ex = if let Some(decl_ret) = self.current_fn_declared_ret.clone() {
                    self.coerce_expr(ret_ex, &ret_lty, &decl_ret, ret_e.span, "`or_return` value")
                } else {
                    ret_ex
                };
                self.record_flow_ret(&ret_lty.tags, &ret_pc);
                let ok_v = self.fresh("or_ret");
                let none_arm = if let Some((lbl, _)) = ret_ctx {
                    ExecExpr::Jump {
                        label: lbl.to_string(),
                        args: vec![ret_ex],
                    }
                } else {
                    ret_ex
                };
                return (
                    ExecExpr::CaseE {
                        scrut: Box::new(rex),
                        arms: vec![
                            ExecCaseArm {
                                pattern: ExecPattern::Ctor {
                                    ctor: "Some".to_string(),
                                    binders: vec![ok_v.clone()],
                                },
                                body: ExecExpr::Var(ok_v),
                            },
                            ExecCaseArm {
                                pattern: ExecPattern::Ctor {
                                    ctor: "None".to_string(),
                                    binders: Vec::new(),
                                },
                                body: none_arm,
                            },
                        ],
                    },
                    LTy::new(inner.as_ref().clone(), rlty.tags),
                );
            }
            (Ty::Text, prop) if args.is_empty() && text_prop_op(prop).is_some() => {
                if let Some((op, out_ty)) = text_prop_op(prop) {
                    return (
                        ExecExpr::Prim {
                            op,
                            args: vec![rex],
                        },
                        LTy::new(out_ty, rlty.tags),
                    );
                }
            }
            (ty, prop @ ("ceil" | "floor" | "trunc" | "to_int"))
                if args.is_empty() && numeric_prop_op(ty, prop).is_some() =>
            {
                if let Some((op, out_ty)) = numeric_prop_op(ty, prop) {
                    return (
                        ExecExpr::Prim {
                            op,
                            args: vec![rex],
                        },
                        LTy::new(out_ty, rlty.tags),
                    );
                }
            }
            (Ty::Text, "contains?" | "starts_with?" | "ends_with?") => {
                let (key, op) = match member.name.as_str() {
                    "contains?" => ("sub", ExecPrimOp::Core(PrimOp::ContainsText)),
                    "starts_with?" => ("prefix", ExecPrimOp::StartsWithText),
                    _ => ("suffix", ExecPrimOp::EndsWithText),
                };
                if let Some(arg_e) = extract_one_arg(args, key) {
                    let (aex, alty) =
                        self.check_expr(arg_e, env, Some(&Ty::Text), pc, scope, ret_ctx);
                    if alty.ty != Ty::Text {
                        self.diags.push(
                            Diagnostic::error(
                                DiagCode::TypeError,
                                format!(
                                    "`.{}` expects a `Text` argument, found `{:?}`",
                                    member.name, alty.ty
                                ),
                            )
                            .with_span(arg_e.span),
                        );
                    }
                    return (
                        ExecExpr::Prim {
                            op,
                            args: vec![rex, aex],
                        },
                        LTy::new(Ty::Bool, rlty.tags.union(&alty.tags)),
                    );
                }
                self.diags.push(
                    Diagnostic::error(
                        DiagCode::TypeError,
                        format!(
                            "`Text.{}` expects 1 `Text` argument (`{key}:`)",
                            member.name
                        ),
                    )
                    .with_span(span),
                );
                return (
                    ExecExpr::Lit(Literal::Bool(false)),
                    LTy::new(Ty::Bool, rlty.tags),
                );
            }
            (Ty::Text, "slice") => {
                if let Some((start_e, len_e)) = extract_two_args(args, "start", "len") {
                    let (sex, slty) =
                        self.check_expr(start_e, env, Some(&Ty::Int), pc, scope, ret_ctx);
                    let (lex, llty) =
                        self.check_expr(len_e, env, Some(&Ty::Int), pc, scope, ret_ctx);
                    if slty.ty != Ty::Int {
                        self.diags.push(
                            Diagnostic::error(
                                DiagCode::TypeError,
                                format!(
                                    "`Text.slice` `start` must be `Int`, found `{:?}`",
                                    slty.ty
                                ),
                            )
                            .with_span(start_e.span),
                        );
                    }
                    if llty.ty != Ty::Int {
                        self.diags.push(
                            Diagnostic::error(
                                DiagCode::TypeError,
                                format!("`Text.slice` `len` must be `Int`, found `{:?}`", llty.ty),
                            )
                            .with_span(len_e.span),
                        );
                    }
                    return (
                        ExecExpr::Prim {
                            op: ExecPrimOp::SliceText,
                            args: vec![rex, sex, lex],
                        },
                        LTy::new(Ty::Text, rlty.tags.union(&slty.tags).union(&llty.tags)),
                    );
                }
                self.diags.push(
                    Diagnostic::error(
                        DiagCode::TypeError,
                        "`Text.slice` expects `(start: Int, len: Int)`",
                    )
                    .with_span(span),
                );
                return (
                    ExecExpr::Lit(Literal::Text(String::new())),
                    LTy::new(Ty::Text, rlty.tags),
                );
            }
            (Ty::Int | Ty::Float | Ty::Decimal, "clamp") => {
                if let Some((lo_e, hi_e)) = extract_two_args(args, "lo", "hi") {
                    let expected_ty = rlty.ty.clone();
                    let (lo_ex, lo_lty) =
                        self.check_expr(lo_e, env, Some(&expected_ty), pc, scope, ret_ctx);
                    let (hi_ex, hi_lty) =
                        self.check_expr(hi_e, env, Some(&expected_ty), pc, scope, ret_ctx);
                    if lo_lty.ty != expected_ty || hi_lty.ty != expected_ty {
                        self.diags.push(
                            Diagnostic::error(
                                DiagCode::TypeError,
                                format!(
                                    "`.clamp(lo, hi)` bounds must match receiver type `{expected_ty:?}`"
                                ),
                            )
                            .with_span(span),
                        );
                    }
                    let op = clamp_op_for_ty(&expected_ty).unwrap_or(ExecPrimOp::ClampInt);
                    return (
                        ExecExpr::Prim {
                            op,
                            args: vec![rex, lo_ex, hi_ex],
                        },
                        LTy::new(
                            expected_ty,
                            rlty.tags.union(&lo_lty.tags).union(&hi_lty.tags),
                        ),
                    );
                }
                self.diags.push(
                    Diagnostic::error(
                        DiagCode::TypeError,
                        "`.clamp` expects `(lo, hi)` bounds of the same numeric type",
                    )
                    .with_span(span),
                );
                return (rex, rlty);
            }
            (Ty::Float, "round_to") => {
                let (step_opt, half_even) = self.parse_round_to_args(args, span);
                if let Some(step_e) = step_opt {
                    let (sex, slty) =
                        self.check_expr(step_e, env, Some(&Ty::Float), pc, scope, ret_ctx);
                    if slty.ty != Ty::Float {
                        self.diags.push(
                            Diagnostic::error(
                                DiagCode::TypeError,
                                format!(
                                    "`Float.round_to` `step` must be `Float`, found `{:?}`",
                                    slty.ty
                                ),
                            )
                            .with_span(step_e.span),
                        );
                    }
                    let op = if half_even {
                        ExecPrimOp::RoundToFloatEven
                    } else {
                        ExecPrimOp::RoundToFloat
                    };
                    return (
                        ExecExpr::Prim {
                            op,
                            args: vec![rex, sex],
                        },
                        LTy::new(Ty::Float, rlty.tags.union(&slty.tags)),
                    );
                }
                return (rex, rlty);
            }
            (Ty::Timestamp, "in_tz" | "date_in_tz") => {
                if let Some(CallArg::Positional(e)) = args.first() {
                    let (aex, alty) = self.check_expr(e, env, Some(&Ty::Text), pc, scope, ret_ctx);
                    if alty.ty != Ty::Text {
                        self.diags.push(
                            Diagnostic::error(
                                DiagCode::TypeError,
                                format!("`.{}` expects a `Text` IANA timezone name", member.name),
                            )
                            .with_span(e.span),
                        );
                    }
                    let (op, out_ty) = if member.name == "in_tz" {
                        (ExecPrimOp::InTz, Ty::Text)
                    } else {
                        (ExecPrimOp::DateInTz, Ty::Date)
                    };
                    return (
                        ExecExpr::Prim {
                            op,
                            args: vec![rex, aex],
                        },
                        LTy::new(out_ty, rlty.tags.union(&alty.tags)),
                    );
                }
            }
            (Ty::Date, "add_days") => {
                if let Some(e) = extract_one_arg(args, "days") {
                    return self
                        .check_date_add_days_expr(rex, rlty, span, e, env, pc, scope, ret_ctx);
                }
                self.diags.push(
                    Diagnostic::error(
                        DiagCode::TypeError,
                        "`Date.add_days` expects 1 `Int` argument",
                    )
                    .with_span(span),
                );
                return (rex, rlty);
            }
            (Ty::Date, "at_midnight_in_tz") => {
                if let Some(e) = extract_one_arg(args, "tz") {
                    return self
                        .check_date_midnight_tz_expr(rex, rlty, span, e, env, pc, scope, ret_ctx);
                }
                self.diags.push(
                    Diagnostic::error(
                        DiagCode::TypeError,
                        "`Date.at_midnight_in_tz` expects a `Text` IANA timezone name",
                    )
                    .with_span(span),
                );
                return (
                    ExecExpr::Lit(Literal::timestamp(0i64)),
                    LTy::new(Ty::Timestamp, rlty.tags),
                );
            }
            (Ty::Float | Ty::Decimal, "round") => {
                let is_dec = rlty.ty == Ty::Decimal;
                let (places_opt, half_even) = self.parse_round_args(args, span);
                let (pex, plty) = if let Some(pe) = places_opt {
                    let (e, l) = self.check_expr(pe, env, Some(&Ty::Int), pc, scope, ret_ctx);
                    if l.ty != Ty::Int {
                        self.diags.push(
                            Diagnostic::error(
                                DiagCode::TypeError,
                                format!("`.round` places must be `Int`, found `{:?}`", l.ty),
                            )
                            .with_span(pe.span),
                        );
                    }
                    (e, l)
                } else {
                    (ExecExpr::Lit(Literal::int(0i64)), LTy::public(Ty::Int))
                };
                let op = match (is_dec, half_even) {
                    (false, false) => ExecPrimOp::RoundFloat,
                    (false, true) => ExecPrimOp::RoundFloatEven,
                    (true, false) => ExecPrimOp::RoundDecimal,
                    (true, true) => ExecPrimOp::RoundDecimalEven,
                };
                return (
                    ExecExpr::Prim {
                        op,
                        args: vec![rex, pex],
                    },
                    LTy::new(rlty.ty, rlty.tags.union(&plty.tags)),
                );
            }
            (Ty::List(el), "append") => {
                if let Some(CallArg::Positional(e)) = args.first() {
                    let hint = if is_unresolved_list(&rlty.ty) {
                        None
                    } else {
                        Some(&el.ty)
                    };
                    let (aex, alty) = self.check_expr(e, env, hint, pc, scope, ret_ctx);
                    let new_el = if is_unresolved_list(&rlty.ty) {
                        alty
                    } else {
                        LTy::new(el.ty.clone(), el.tags.union(&alty.tags))
                    };
                    return (
                        ExecExpr::Prim {
                            op: ExecPrimOp::Core(PrimOp::ListAppend),
                            args: vec![rex, aex],
                        },
                        LTy::new(Ty::List(Box::new(new_el)), rlty.tags),
                    );
                }
            }
            (Ty::LinearModel, "predict") => {
                let Some(CallArg::Positional(x_e)) = args.first() else {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::TypeError,
                            "`LinearModel.predict` requires 1 numeric argument",
                        )
                        .with_span(span),
                    );
                    return (
                        ExecExpr::Lit(Literal::Float(Float64::ZERO)),
                        LTy::new(Ty::Float, rlty.tags),
                    );
                };
                let (xex, xlty) = self.check_expr(x_e, env, Some(&Ty::Float), pc, scope, ret_ctx);
                if !matches!(xlty.ty, Ty::Int | Ty::Float | Ty::Decimal) {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::TypeError,
                            "`LinearModel.predict` argument must be `Int`, `Float`, or `Decimal`",
                        )
                        .with_span(x_e.span),
                    );
                }
                return (
                    ExecExpr::Prim {
                        op: ExecPrimOp::LinearModelPredict,
                        args: vec![rex, xex],
                    },
                    LTy::new(Ty::Float, rlty.tags.union(&xlty.effective_tags())),
                );
            }
            (Ty::Table(tt), "count") => {
                return (
                    ExecExpr::Prim {
                        op: ExecPrimOp::Core(PrimOp::TableCount),
                        args: vec![rex],
                    },
                    LTy::new(Ty::Int, tt.row_tags.union(&rlty.tags)),
                );
            }
            (Ty::Table(tt), "profile") => {
                let col_tags: Vec<(Ident, TagSet)> = tt
                    .cols
                    .iter()
                    .filter(|c| !c.tags.is_empty())
                    .map(|c| (c.name.clone(), c.tags.clone()))
                    .collect();
                let row_tags = tt.row_tags.clone();
                // Column-tagged values are strictly redacted to `[REDACTED:...]` by `profile()`,
                // whereas table-level `row_tags` (e.g. after filtering on a sensitive column)
                // still taint structural row counts and remain on `Ty::Profile`.
                let profile_tags = row_tags.union(&rlty.tags);
                let op = if row_tags.is_empty() && col_tags.is_empty() {
                    ExecPrimOp::Core(PrimOp::TableProfile)
                } else {
                    ExecPrimOp::TableProfileEx { row_tags, col_tags }
                };
                return (
                    ExecExpr::Prim {
                        op,
                        args: vec![rex],
                    },
                    LTy::new(Ty::Profile(profile_tags), TagSet::empty()),
                );
            }
            (Ty::Table(tt), "sum" | "mean" | "stddev") => {
                let col = match args.first() {
                    Some(CallArg::Positional(Expr {
                        kind: ExprKind::DotField(m),
                        ..
                    })) => m.name.clone(),
                    _ => String::new(),
                };
                let Some(cs) = tt.find_col(&col) else {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::TypeError,
                            format!("unknown column `.{col}` in `table.{}(...)`", member.name),
                        )
                        .with_span(span),
                    );
                    return (ExecExpr::Lit(Literal::Unit), LTy::public(Ty::Unit));
                };
                let tags = tt.row_tags.union(&cs.tags).union(&rlty.tags);
                let (pop, out_ty) = match member.name.as_str() {
                    "sum" => (
                        ExecPrimOp::TableColSum(col),
                        numeric_core_of_scalar(&cs.ty).map_or(Ty::Int, |s| s.to_ty()),
                    ),
                    "mean" => {
                        let inner = match numeric_core_of_scalar(&cs.ty) {
                            Some(ScalarTy::Decimal) => Ty::Decimal,
                            _ => Ty::Float,
                        };
                        (ExecPrimOp::TableColMean(col), Ty::Option(Box::new(inner)))
                    }
                    _ => (
                        ExecPrimOp::TableColStddev(col),
                        Ty::Option(Box::new(Ty::Float)),
                    ),
                };
                return (
                    ExecExpr::Prim {
                        op: pop,
                        args: vec![rex],
                    },
                    LTy::new(out_ty, tags),
                );
            }
            (Ty::Table(tt), "format_csv") => {
                return self.check_format_csv_call(
                    rex, tt, &rlty.tags, args, span, env, pc, scope, ret_ctx,
                );
            }
            (Ty::Table(tt), verb) => {
                // Allow method-style table verbs (`long.select(.a, .b)`).
                let in_plan = expr_to_plan(rex);
                return self.check_table_verb(
                    in_plan,
                    tt.clone(),
                    rlty.tags,
                    verb,
                    args,
                    span,
                    env,
                    pc,
                    scope,
                    ret_ctx,
                );
            }
            (ty, "in?") => {
                let Some(base_ty) = in_list_base_ty(ty).cloned() else {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::TypeError,
                            format!("`.in?(list)` is not supported on receiver type `{ty:?}`"),
                        )
                        .with_span(span),
                    );
                    return (
                        ExecExpr::Lit(Literal::Bool(false)),
                        LTy::new(Ty::Bool, rlty.tags),
                    );
                };
                let Some(list_e) = extract_one_arg(args, "list") else {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::TypeError,
                            "`.in?(list)` requires 1 `List` argument",
                        )
                        .with_span(span),
                    );
                    return (
                        ExecExpr::Lit(Literal::Bool(false)),
                        LTy::new(Ty::Bool, rlty.tags),
                    );
                };
                let exp_list_ty = Ty::List(Box::new(LTy::public(base_ty.clone())));
                let (lex, llty) =
                    self.check_expr(list_e, env, Some(&exp_list_ty), pc, scope, ret_ctx);
                match &llty.ty {
                    Ty::List(el) if el.ty == base_ty || is_unresolved_list(&llty.ty) => {}
                    other => {
                        self.diags.push(
                            Diagnostic::error(
                                DiagCode::TypeError,
                                format!("`.in?` expects `List({base_ty:?})`, found `{other:?}`"),
                            )
                            .with_span(list_e.span),
                        );
                    }
                }
                return (
                    ExecExpr::Prim {
                        op: ExecPrimOp::InList,
                        args: vec![rex, lex],
                    },
                    LTy::new(Ty::Bool, rlty.tags.union(&llty.effective_tags())),
                );
            }
            _ => {}
        }

        let mut diag = Diagnostic::error(
            DiagCode::TypeError,
            format!("unknown method `.{}(...)`", member.name),
        )
        .with_span(span);
        if matches!(&rlty.ty, Ty::List(_)) && member.name == "count" {
            diag = diag.with_hint(
                "`List` has no `.count()` method; use `.size` (or `.len`) to get the number of elements",
            );
        }
        self.diags.push(diag);
        (ExecExpr::Lit(Literal::Unit), LTy::public(Ty::Unit))
    }

    #[expect(
        clippy::too_many_arguments,
        reason = "constructor call handles Ok/Error/Some, structs, and enums"
    )]
    fn check_ctor_call(
        &mut self,
        cname: &str,
        args: &[CallArg],
        span: Span,
        env: &HashMap<Ident, VarBinding>,
        expected: Option<&Ty>,
        pc: &TagSet,
        scope: LocalScopeKind,
        ret_ctx: Option<(&str, Option<&Ty>)>,
    ) -> (ExecExpr, LTy) {
        match cname {
            "Ok" => {
                let (ok_hint, err_ty) = match expected {
                    Some(Ty::Result { ok_ty, err_ty }) => {
                        (Some(ok_ty.as_ref()), err_ty.as_ref().clone())
                    }
                    _ => (None, Ty::Text),
                };
                let (vex, vlty) = match args.first() {
                    Some(CallArg::Positional(e)) => {
                        self.check_expr(e, env, ok_hint, pc, scope, ret_ctx)
                    }
                    _ => (ExecExpr::Lit(Literal::Unit), LTy::public(Ty::Unit)),
                };
                (
                    ExecExpr::Prim {
                        op: ExecPrimOp::Core(PrimOp::OkVal(err_ty.clone())),
                        args: vec![vex],
                    },
                    LTy::new(
                        Ty::Result {
                            ok_ty: Box::new(vlty.ty),
                            err_ty: Box::new(err_ty),
                        },
                        vlty.tags,
                    ),
                )
            }
            "Error" => {
                let (ok_ty, err_hint) = match expected {
                    Some(Ty::Result { ok_ty, err_ty }) => {
                        (ok_ty.as_ref().clone(), Some(err_ty.as_ref()))
                    }
                    _ => (Ty::Unit, None),
                };
                let (eex, elty) = match args.first() {
                    Some(CallArg::Positional(e)) => {
                        self.check_expr(e, env, err_hint, pc, scope, ret_ctx)
                    }
                    _ => (ExecExpr::Lit(Literal::Unit), LTy::public(Ty::Unit)),
                };
                (
                    ExecExpr::Prim {
                        op: ExecPrimOp::Core(PrimOp::ErrVal(ok_ty.clone())),
                        args: vec![eex],
                    },
                    LTy::new(
                        Ty::Result {
                            ok_ty: Box::new(ok_ty),
                            err_ty: Box::new(elty.ty),
                        },
                        elty.tags,
                    ),
                )
            }
            "Some" => {
                let hint = match expected {
                    Some(Ty::Option(t)) => Some(t.as_ref()),
                    _ => None,
                };
                let (vex, vlty) = match args.first() {
                    Some(CallArg::Positional(e)) => {
                        self.check_expr(e, env, hint, pc, scope, ret_ctx)
                    }
                    _ => (ExecExpr::Lit(Literal::Unit), LTy::public(Ty::Unit)),
                };
                (
                    ExecExpr::Prim {
                        op: ExecPrimOp::Core(PrimOp::SomeVal(vlty.ty.clone())),
                        args: vec![vex],
                    },
                    LTy::new(Ty::Option(Box::new(vlty.ty)), vlty.tags),
                )
            }
            _ => {
                // Struct constructor (positional or named fields in any order).
                if let Some(layout) = self.structs.get(cname).cloned() {
                    let mut ordered: Vec<Option<ExecExpr>> = vec![None; layout.field_names.len()];
                    for (idx, arg) in args.iter().enumerate() {
                        let (fidx, expr_arg) = match arg {
                            CallArg::Named { name, value, .. } => {
                                if let Some(pos) =
                                    layout.field_names.iter().position(|n| n == &name.name)
                                {
                                    (pos, value)
                                } else {
                                    self.diags.push(
                                        Diagnostic::error(
                                            DiagCode::TypeError,
                                            format!(
                                                "struct `{cname}` has no field `{}`",
                                                name.name
                                            ),
                                        )
                                        .with_span(name.span),
                                    );
                                    continue;
                                }
                            }
                            CallArg::Positional(e) => (idx, e),
                        };
                        if let Some(flty) = layout.field_ltys.get(fidx) {
                            let (mut aex, alty) =
                                self.check_expr(expr_arg, env, Some(&flty.ty), pc, scope, ret_ctx);
                            aex = self.coerce_expr(
                                aex,
                                &alty,
                                flty,
                                expr_arg.span,
                                &format!("field `{}.{}`", cname, layout.field_names[fidx]),
                            );
                            ordered[fidx] = Some(aex);
                        }
                    }
                    let final_args = ordered
                        .into_iter()
                        .map(|o| o.unwrap_or(ExecExpr::Lit(Literal::Unit)))
                        .collect();
                    return (
                        ExecExpr::Ctor {
                            type_name: cname.to_string(),
                            ctor_name: cname.to_string(),
                            args: final_args,
                        },
                        LTy::public(Ty::Data(cname.to_string())),
                    );
                }

                // Enum variant constructor.
                if let Some((enum_name, vidx)) = self.ctor_to_enum.get(cname).cloned() {
                    let cdecl = self
                        .enums
                        .get(&enum_name)
                        .and_then(|d| d.ctors.get(vidx))
                        .cloned();
                    let mut cargs = Vec::with_capacity(args.len());
                    for (i, arg) in args.iter().enumerate() {
                        let e = match arg {
                            CallArg::Positional(e) | CallArg::Named { value: e, .. } => e,
                        };
                        let hint = cdecl.as_ref().and_then(|c| c.fields.get(i)).map(|l| &l.ty);
                        let (ae, _) = self.check_expr(e, env, hint, pc, scope, ret_ctx);
                        cargs.push(ae);
                    }
                    return (
                        ExecExpr::Ctor {
                            type_name: enum_name.clone(),
                            ctor_name: cname.to_string(),
                            args: cargs,
                        },
                        LTy::public(Ty::Data(enum_name)),
                    );
                }

                self.diags.push(
                    Diagnostic::error(
                        DiagCode::ResolveError,
                        format!("unknown constructor `{cname}`"),
                    )
                    .with_span(span),
                );
                (ExecExpr::Lit(Literal::Unit), LTy::public(Ty::Unit))
            }
        }
    }

    fn check_date_trunc_expr(
        &mut self,
        args: &[CallArg],
        span: Span,
        env: &HashMap<Ident, VarBinding>,
        pc: &TagSet,
        scope: LocalScopeKind,
        ret_ctx: Option<(&str, Option<&Ty>)>,
    ) -> (ExecExpr, LTy) {
        let (Some(CallArg::Positional(a)), Some(CallArg::Positional(b))) =
            (args.first(), args.get(1))
        else {
            self.diags.push(
                Diagnostic::error(DiagCode::TypeError, "`date_trunc` expects 2 arguments")
                    .with_span(span),
            );
            return (ExecExpr::Lit(Literal::Unit), LTy::public(Ty::Unit));
        };
        let (ea, la) = self.check_expr(a, env, None, pc, scope, ret_ctx);
        if let ExprKind::Atom(unit) = &b.kind {
            if unit == "month" && la.ty == Ty::Date {
                return (
                    ExecExpr::Prim {
                        op: ExecPrimOp::Core(PrimOp::DateTruncMonth),
                        args: vec![ea],
                    },
                    la,
                );
            }
            return (
                ExecExpr::Prim {
                    op: ExecPrimOp::DateTruncUnit(unit.clone()),
                    args: vec![ea],
                },
                la,
            );
        }
        let (eb, lb) = self.check_expr(b, env, Some(&Ty::Duration), pc, scope, ret_ctx);
        (
            ExecExpr::Prim {
                op: ExecPrimOp::DateTruncDuration,
                args: vec![ea, eb],
            },
            LTy::new(la.ty, la.tags.union(&lb.tags)),
        )
    }

    #[expect(
        clippy::too_many_arguments,
        reason = "expression temporal checker threads environment, sensitivity pc, and return context"
    )]
    fn check_date_add_days_expr(
        &mut self,
        rex: ExecExpr,
        rlty: LTy,
        recv_span: Span,
        days_e: &Expr,
        env: &HashMap<Ident, VarBinding>,
        pc: &TagSet,
        scope: LocalScopeKind,
        ret_ctx: Option<(&str, Option<&Ty>)>,
    ) -> (ExecExpr, LTy) {
        if rlty.ty != Ty::Date {
            self.diags.push(
                Diagnostic::error(
                    DiagCode::TypeError,
                    format!("`add_days` requires a `Date`, found `{:?}`", rlty.ty),
                )
                .with_span(recv_span),
            );
        }
        let (aex, alty) = self.check_expr(days_e, env, Some(&Ty::Int), pc, scope, ret_ctx);
        if alty.ty != Ty::Int {
            self.diags.push(
                Diagnostic::error(
                    DiagCode::TypeError,
                    format!("`add_days` `days` must be `Int`, found `{:?}`", alty.ty),
                )
                .with_span(days_e.span),
            );
        }
        (
            ExecExpr::Prim {
                op: ExecPrimOp::AddDays,
                args: vec![rex, aex],
            },
            LTy::new(Ty::Date, rlty.tags.union(&alty.tags)),
        )
    }

    #[expect(
        clippy::too_many_arguments,
        reason = "expression timezone checker threads environment, sensitivity pc, and return context"
    )]
    fn check_date_midnight_tz_expr(
        &mut self,
        rex: ExecExpr,
        rlty: LTy,
        recv_span: Span,
        tz_e: &Expr,
        env: &HashMap<Ident, VarBinding>,
        pc: &TagSet,
        scope: LocalScopeKind,
        ret_ctx: Option<(&str, Option<&Ty>)>,
    ) -> (ExecExpr, LTy) {
        if rlty.ty != Ty::Date {
            self.diags.push(
                Diagnostic::error(
                    DiagCode::TypeError,
                    format!(
                        "`at_midnight_in_tz` requires a `Date`, found `{:?}`",
                        rlty.ty
                    ),
                )
                .with_span(recv_span),
            );
        }
        let (aex, alty) = self.check_expr(tz_e, env, Some(&Ty::Text), pc, scope, ret_ctx);
        if alty.ty != Ty::Text {
            self.diags.push(
                Diagnostic::error(
                    DiagCode::TypeError,
                    "`at_midnight_in_tz` expects a `Text` IANA timezone name",
                )
                .with_span(tz_e.span),
            );
        }
        (
            ExecExpr::Prim {
                op: ExecPrimOp::AtMidnightInTz,
                args: vec![rex, aex],
            },
            LTy::new(Ty::Timestamp, rlty.tags.union(&alty.tags)),
        )
    }

    #[expect(
        clippy::too_many_arguments,
        reason = "row temporal checker threads table columns and outer scope"
    )]
    fn check_row_date_add_days(
        &mut self,
        re: ExecRowExpr,
        rty: Ty,
        rtags: TagSet,
        recv_span: Span,
        days_e: &Expr,
        cols: &[ColSpec],
        outer_env: &HashMap<Ident, VarBinding>,
        allow_dot_self: bool,
    ) -> (ExecRowExpr, Ty, TagSet) {
        if rty != Ty::Date {
            self.diags.push(
                Diagnostic::error(
                    DiagCode::TypeError,
                    format!("`add_days` requires a `Date`, found `{rty:?}`"),
                )
                .with_span(recv_span),
            );
        }
        let (are, aty, atags) =
            self.check_row_expr(days_e, cols, outer_env, Some(&Ty::Int), allow_dot_self);
        if aty != Ty::Int {
            self.diags.push(
                Diagnostic::error(
                    DiagCode::TypeError,
                    format!("`add_days` `days` must be `Int`, found `{aty:?}`"),
                )
                .with_span(days_e.span),
            );
        }
        (
            ExecRowExpr::Prim {
                op: ExecPrimOp::AddDays,
                args: vec![re, are],
            },
            Ty::Date,
            rtags.union(&atags),
        )
    }

    #[expect(
        clippy::too_many_arguments,
        reason = "row timezone checker threads table columns and outer scope"
    )]
    fn check_row_date_midnight_tz(
        &mut self,
        re: ExecRowExpr,
        rty: Ty,
        rtags: TagSet,
        recv_span: Span,
        tz_e: &Expr,
        cols: &[ColSpec],
        outer_env: &HashMap<Ident, VarBinding>,
        allow_dot_self: bool,
    ) -> (ExecRowExpr, Ty, TagSet) {
        if rty != Ty::Date {
            self.diags.push(
                Diagnostic::error(
                    DiagCode::TypeError,
                    format!("`at_midnight_in_tz` requires a `Date`, found `{rty:?}`"),
                )
                .with_span(recv_span),
            );
        }
        let (are, aty, atags) =
            self.check_row_expr(tz_e, cols, outer_env, Some(&Ty::Text), allow_dot_self);
        if aty != Ty::Text {
            self.diags.push(
                Diagnostic::error(
                    DiagCode::TypeError,
                    "`at_midnight_in_tz` expects a `Text` IANA timezone name",
                )
                .with_span(tz_e.span),
            );
        }
        (
            ExecRowExpr::Prim {
                op: ExecPrimOp::AtMidnightInTz,
                args: vec![re, are],
            },
            Ty::Timestamp,
            rtags.union(&atags),
        )
    }

    // -----------------------------------------------------------------------
    // Control Flow Expressions (`if`, `case`, `table ... end`)
    // -----------------------------------------------------------------------

    #[expect(
        clippy::too_many_arguments,
        reason = "iterative inline if handles arbitrarily long else-if chains in O(1) stack"
    )]
    fn check_if_inline(
        &mut self,
        cond: &Expr,
        then_expr: &Expr,
        else_ifs: &[(Expr, Expr)],
        else_expr: &Expr,
        env: &HashMap<Ident, VarBinding>,
        expected: Option<&Ty>,
        pc: &TagSet,
        scope: LocalScopeKind,
        ret_ctx: Option<(&str, Option<&Ty>)>,
    ) -> (ExecExpr, LTy) {
        let mut cur_pc = pc.clone();
        let mut arms: Vec<(ExecExpr, ExecExpr, LTy, Span)> = Vec::with_capacity(1 + else_ifs.len());

        let (c0, cl0) = self.check_expr(cond, env, Some(&Ty::Bool), &cur_pc, scope, ret_ctx);
        cur_pc = cur_pc.union(&cl0.tags);
        let (t0, tl0) = self.check_expr(then_expr, env, expected, &cur_pc, scope, ret_ctx);
        let target_ty = expected.cloned().unwrap_or_else(|| tl0.ty.clone());
        let mut all_tags = cur_pc.union(&tl0.tags);
        arms.push((c0, t0, tl0, then_expr.span));

        for (ec, et) in else_ifs {
            let (cex, clty) = self.check_expr(ec, env, Some(&Ty::Bool), &cur_pc, scope, ret_ctx);
            cur_pc = cur_pc.union(&clty.tags);
            let (tex, tlty) = self.check_expr(et, env, Some(&target_ty), &cur_pc, scope, ret_ctx);
            all_tags = all_tags.union(&cur_pc).union(&tlty.tags);
            arms.push((cex, tex, tlty, et.span));
        }

        let (mut acc_else, else_lty) =
            self.check_expr(else_expr, env, Some(&target_ty), &cur_pc, scope, ret_ctx);
        all_tags = all_tags.union(&else_lty.tags);
        if else_lty.ty != target_ty {
            acc_else = self.coerce_expr(
                acc_else,
                &else_lty,
                &LTy::new(target_ty.clone(), all_tags.clone()),
                else_expr.span,
                "`if` else branch",
            );
        }

        while let Some((cex, mut tex, tlty, tspan)) = arms.pop() {
            if tlty.ty != target_ty {
                tex = self.coerce_expr(
                    tex,
                    &tlty,
                    &LTy::new(target_ty.clone(), all_tags.clone()),
                    tspan,
                    "`if` branch",
                );
            }
            acc_else = ExecExpr::IfE {
                cond: Box::new(cex),
                then_br: Box::new(tex),
                else_br: Box::new(acc_else),
            };
        }

        (acc_else, LTy::new(target_ty, all_tags))
    }

    #[expect(
        clippy::too_many_arguments,
        reason = "iterative block if handles arbitrarily long else-if chains, branch pc taint, and mutated var tuples"
    )]
    fn check_if_block_with_state(
        &mut self,
        cond: &Expr,
        then_body: &[Stmt],
        else_ifs: &[ast::ElseIfBranch],
        else_body: Option<&ast::ElseBranch>,
        env: &HashMap<Ident, VarBinding>,
        expected: Option<&Ty>,
        pc: &TagSet,
        scope: LocalScopeKind,
        ret_ctx: Option<(&str, Option<&Ty>)>,
        state_vars: &[Ident],
        branch_envs: &mut Vec<HashMap<Ident, VarBinding>>,
    ) -> (ExecExpr, LTy) {
        // Without a trailing `else`, the implicit fallthrough produces `Unit`, so every branch
        // must also produce `Unit` at slot 0 (preventing Core IR branch type mismatch).
        let branch_expected = if else_body.is_none() {
            Some(&Ty::Unit)
        } else {
            expected
        };
        let tail = if state_vars.is_empty() {
            BlockTail::Value
        } else {
            BlockTail::ValueAndState(state_vars)
        };

        let mut cur_pc = pc.clone();
        let mut arms: Vec<(ExecExpr, ExecExpr, LTy, bool, usize, TagSet)> =
            Vec::with_capacity(1 + else_ifs.len());

        let (c0, cl0) = self.check_expr(cond, env, Some(&Ty::Bool), &cur_pc, scope, ret_ctx);
        cur_pc = cur_pc.union(&cl0.tags);
        let mut then_env = env.clone();
        let (t0, tl0) = self.check_block_inner(
            then_body,
            &mut then_env,
            branch_expected,
            &cur_pc,
            scope,
            ret_ctx,
            tail,
            Vec::new(),
            false,
            "",
        );
        let t0_div = block_ends_diverging(then_body);
        let env0_idx = branch_envs.len();
        branch_envs.push(then_env);
        let mut all_tags = cur_pc.union(&tl0.tags);
        let mut out_ty: Option<Ty> = if else_body.is_none() {
            Some(Ty::Unit)
        } else if !t0_div {
            Some(tl0.ty.clone())
        } else {
            None
        };
        arms.push((c0, t0, tl0, t0_div, env0_idx, cur_pc.clone()));

        for ei in else_ifs {
            let (cex, clty) =
                self.check_expr(&ei.cond, env, Some(&Ty::Bool), &cur_pc, scope, ret_ctx);
            cur_pc = cur_pc.union(&clty.tags);
            let mut ei_env = env.clone();
            let (bex, blty) = self.check_block_inner(
                &ei.body,
                &mut ei_env,
                branch_expected.or(out_ty.as_ref()),
                &cur_pc,
                scope,
                ret_ctx,
                tail,
                Vec::new(),
                false,
                "",
            );
            let div = block_ends_diverging(&ei.body);
            let env_idx = branch_envs.len();
            branch_envs.push(ei_env);
            all_tags = all_tags.union(&cur_pc).union(&blty.tags);
            if out_ty.is_none() && !div {
                out_ty = Some(blty.ty.clone());
            }
            arms.push((cex, bex, blty, div, env_idx, cur_pc.clone()));
        }

        let (mut acc_else, else_lty, else_div, else_env_idx) = if let Some(eb) = else_body {
            let mut else_env = env.clone();
            let (eex, elty) = self.check_block_inner(
                &eb.body,
                &mut else_env,
                branch_expected.or(out_ty.as_ref()),
                &cur_pc,
                scope,
                ret_ctx,
                tail,
                Vec::new(),
                false,
                "",
            );
            let div = block_ends_diverging(&eb.body);
            let env_idx = branch_envs.len();
            branch_envs.push(else_env);
            all_tags = all_tags.union(&elty.tags);
            if out_ty.is_none() && !div {
                out_ty = Some(elty.ty.clone());
            }
            (eex, elty, div, env_idx)
        } else {
            let env_idx = branch_envs.len();
            branch_envs.push(env.clone());
            let unit_branch = if state_vars.is_empty() {
                ExecExpr::Lit(Literal::Unit)
            } else {
                build_val_and_var_tuple(ExecExpr::Lit(Literal::Unit), state_vars)
            };
            (
                unit_branch,
                LTy::new(Ty::Unit, cur_pc.clone()),
                false,
                env_idx,
            )
        };

        let resolved_ty = out_ty.unwrap_or(Ty::Unit);
        // When returning a state tuple across branches in Core IR, ensure every non-diverging
        // branch tuple carries identical merged element `LTy.tags` so `t_lty.ty == e_lty.ty`.
        if !state_vars.is_empty() {
            let merged_val_lty = LTy::new(resolved_ty.clone(), all_tags.clone());
            let merged_var_ltys = compute_merged_var_ltys(env, state_vars, branch_envs, &cur_pc);
            if !else_div {
                acc_else = self.harmonize_state_tuple_branch(
                    acc_else,
                    &else_lty,
                    &branch_envs[else_env_idx],
                    &cur_pc,
                    state_vars,
                    &merged_val_lty,
                    &merged_var_ltys,
                );
            }
            while let Some((cex, mut tex, tlty, div, eidx, arm_pc)) = arms.pop() {
                if !div {
                    tex = self.harmonize_state_tuple_branch(
                        tex,
                        &tlty,
                        &branch_envs[eidx],
                        &arm_pc,
                        state_vars,
                        &merged_val_lty,
                        &merged_var_ltys,
                    );
                }
                acc_else = ExecExpr::IfE {
                    cond: Box::new(cex),
                    then_br: Box::new(tex),
                    else_br: Box::new(acc_else),
                };
            }
        } else {
            if else_body.is_none() && !else_div && else_lty.ty != Ty::Unit {
                acc_else = self.discard_branch_to_unit(acc_else, else_lty);
            }
            while let Some((cex, mut tex, tlty, div, _, _)) = arms.pop() {
                if else_body.is_none() && !div && tlty.ty != Ty::Unit {
                    tex = self.discard_branch_to_unit(tex, tlty);
                }
                acc_else = ExecExpr::IfE {
                    cond: Box::new(cex),
                    then_br: Box::new(tex),
                    else_br: Box::new(acc_else),
                };
            }
        }

        (acc_else, LTy::new(resolved_ty, all_tags))
    }

    fn discard_branch_to_unit(&mut self, mut br_ex: ExecExpr, br_lty: LTy) -> ExecExpr {
        let tmp = self.fresh("seq");
        if expr_has_any_jump(&br_ex) {
            let cont = self.fresh("cont");
            rewrite_tail_to_jump(&mut br_ex, &cont);
            ExecExpr::Join {
                label: cont,
                params: vec![(tmp, br_lty)],
                rhs: Box::new(ExecExpr::Lit(Literal::Unit)),
                body: Box::new(br_ex),
            }
        } else {
            ExecExpr::LetE {
                name: tmp,
                lty: br_lty,
                bound: Box::new(br_ex),
                body: Box::new(ExecExpr::Lit(Literal::Unit)),
            }
        }
    }

    #[expect(
        clippy::too_many_arguments,
        reason = "state tuple harmonization needs branch pc, env, and merged target element types"
    )]
    fn harmonize_state_tuple_branch(
        &mut self,
        mut br_ex: ExecExpr,
        br_val_lty: &LTy,
        br_env: &HashMap<Ident, VarBinding>,
        branch_pc: &TagSet,
        state_vars: &[Ident],
        merged_val_lty: &LTy,
        merged_var_ltys: &[LTy],
    ) -> ExecExpr {
        let actual_val_lty = br_val_lty.add_tags(branch_pc);
        let mut needs_widen = actual_val_lty.tags != merged_val_lty.tags;
        let mut br_tup_ltys = Vec::with_capacity(1 + state_vars.len());
        br_tup_ltys.push(actual_val_lty);
        for (v, target_lty) in state_vars.iter().zip(merged_var_ltys) {
            let cur_lty = br_env
                .get(v)
                .map_or_else(|| target_lty.clone(), |b| b.lty.add_tags(branch_pc));
            if cur_lty.tags != target_lty.tags {
                needs_widen = true;
            }
            br_tup_ltys.push(cur_lty);
        }
        if !needs_widen {
            return br_ex;
        }
        let tup_tmp = self.fresh("br_tup");
        let mut proj_names = Vec::with_capacity(1 + state_vars.len());
        let val_name = self.fresh("br_el");
        proj_names.push((val_name, merged_val_lty.clone()));
        for target_lty in merged_var_ltys {
            proj_names.push((self.fresh("br_el"), target_lty.clone()));
        }
        let mut body = ExecExpr::Tuple(
            proj_names
                .iter()
                .map(|(n, _)| ExecExpr::Var(n.clone()))
                .collect(),
        );
        for (idx, (el_name, target_lty)) in proj_names.into_iter().enumerate().rev() {
            body = ExecExpr::LetE {
                name: el_name,
                lty: target_lty,
                bound: Box::new(ExecExpr::Proj {
                    tup: Box::new(ExecExpr::Var(tup_tmp.clone())),
                    idx: BigInt::from(idx),
                }),
                body: Box::new(body),
            };
        }
        let tup_lty = LTy::new(Ty::Tuple(br_tup_ltys), merged_val_lty.tags.clone());
        if expr_has_any_jump(&br_ex) {
            let cont = self.fresh("br_join");
            rewrite_tail_to_jump(&mut br_ex, &cont);
            ExecExpr::Join {
                label: cont,
                params: vec![(tup_tmp, tup_lty)],
                rhs: Box::new(body),
                body: Box::new(br_ex),
            }
        } else {
            ExecExpr::LetE {
                name: tup_tmp,
                lty: tup_lty,
                bound: Box::new(br_ex),
                body: Box::new(body),
            }
        }
    }

    #[expect(
        clippy::too_many_arguments,
        reason = "case expression groups flat arms, binds pattern vars, propagates scrutinee taint and mutated vars"
    )]
    fn check_case_with_state(
        &mut self,
        scrut: &Expr,
        lines: &[ast::CaseLine],
        span: Span,
        env: &HashMap<Ident, VarBinding>,
        expected: Option<&Ty>,
        pc: &TagSet,
        scope: LocalScopeKind,
        ret_ctx: Option<(&str, Option<&Ty>)>,
        state_vars: &[Ident],
        arm_envs: &mut Vec<HashMap<Ident, VarBinding>>,
    ) -> (ExecExpr, LTy) {
        let (sex, slty) = self.check_expr(scrut, env, None, pc, scope, ret_ctx);
        let case_pc = pc.union(&slty.tags);
        let tail = if state_vars.is_empty() {
            BlockTail::Value
        } else {
            BlockTail::ValueAndState(state_vars)
        };

        // Group flat `CaseLine`s into borrowed arms without cloning deep expressions.
        enum CaseArmBody<'b> {
            Inline(&'b Expr),
            Stmts(Vec<&'b Stmt>),
        }
        let mut grouped: Vec<(&Expr, CaseArmBody<'_>)> = Vec::new();
        for line in lines {
            match line {
                ast::CaseLine::ArmHeader { pattern, .. } => {
                    grouped.push((pattern, CaseArmBody::Stmts(Vec::new())));
                }
                ast::CaseLine::ArmInline { pattern, expr, .. } => {
                    grouped.push((pattern, CaseArmBody::Inline(expr)));
                }
                ast::CaseLine::Stmt(st) => {
                    if let Some((_, CaseArmBody::Stmts(body))) = grouped.last_mut() {
                        body.push(st);
                    } else {
                        self.diags.push(
                            Diagnostic::error(
                                DiagCode::ParseError,
                                "statement inside `case` must follow a `pattern:` arm header",
                            )
                            .with_span(st.span),
                        );
                    }
                }
            }
        }

        let mut raw_arms: Vec<(ExecPattern, ExecExpr, LTy, bool, usize)> =
            Vec::with_capacity(grouped.len());
        let mut out_ty: Option<Ty> = expected.cloned();
        let mut out_tags = case_pc.clone();

        for (pat_expr, arm_body) in grouped {
            let mut arm_env = env.clone();
            let pat = self.check_case_pattern(pat_expr, &slty, &mut arm_env);
            let (body_ex, body_lty, arm_diverges) = match arm_body {
                CaseArmBody::Inline(expr) => {
                    let (ex, lty) =
                        self.check_expr(expr, &arm_env, out_ty.as_ref(), &case_pc, scope, ret_ctx);
                    let wrapped = if state_vars.is_empty() {
                        ex
                    } else {
                        build_val_and_var_tuple(ex, state_vars)
                    };
                    (wrapped, lty, false)
                }
                CaseArmBody::Stmts(body_stmts) => {
                    let (ex, lty) = self.check_stmt_refs_inner(
                        &body_stmts,
                        &mut arm_env,
                        out_ty.as_ref(),
                        &case_pc,
                        scope,
                        ret_ctx,
                        tail,
                        Vec::new(),
                        false,
                        "",
                    );
                    let diverges = body_stmts.last().is_some_and(|s| {
                        matches!(
                            s.kind,
                            StmtKind::Return { guard: None, .. }
                                | StmtKind::Break { guard: None, .. }
                                | StmtKind::Continue { guard: None, .. }
                                | StmtKind::Stop(_)
                        )
                    });
                    (ex, lty, diverges)
                }
            };
            let env_idx = arm_envs.len();
            arm_envs.push(arm_env);
            // If an arm jumps away via `return`, its static type is Unit; don't overwrite a real arm type!
            if out_ty.is_none() && !arm_diverges {
                out_ty = Some(body_lty.ty.clone());
            }
            out_tags = out_tags.union(&body_lty.tags);
            raw_arms.push((pat, body_ex, body_lty, arm_diverges, env_idx));
        }

        let resolved_ty = out_ty.unwrap_or(Ty::Unit);
        let arms: Vec<ExecCaseArm> = if !state_vars.is_empty() {
            let merged_val_lty = LTy::new(resolved_ty.clone(), out_tags.clone());
            let merged_var_ltys = compute_merged_var_ltys(env, state_vars, arm_envs, &case_pc);
            raw_arms
                .into_iter()
                .map(|(pat, mut body_ex, body_lty, div, eidx)| {
                    if !div {
                        body_ex = self.harmonize_state_tuple_branch(
                            body_ex,
                            &body_lty,
                            &arm_envs[eidx],
                            &case_pc,
                            state_vars,
                            &merged_val_lty,
                            &merged_var_ltys,
                        );
                    }
                    ExecCaseArm {
                        pattern: pat,
                        body: body_ex,
                    }
                })
                .collect()
        } else {
            raw_arms
                .into_iter()
                .map(|(pat, body_ex, _, _, _)| ExecCaseArm {
                    pattern: pat,
                    body: body_ex,
                })
                .collect()
        };

        if arms.is_empty() {
            self.diags.push(
                Diagnostic::error(DiagCode::ExhaustivenessError, "`case` has no match arms")
                    .with_span(span),
            );
        }

        (
            ExecExpr::CaseE {
                scrut: Box::new(sex),
                arms,
            },
            LTy::new(resolved_ty, out_tags),
        )
    }

    fn check_case_pattern(
        &mut self,
        pat: &Expr,
        scrut_lty: &LTy,
        arm_env: &mut HashMap<Ident, VarBinding>,
    ) -> ExecPattern {
        match &pat.kind {
            ExprKind::Underscore => ExecPattern::Wildcard,
            ExprKind::Ident(n) => {
                arm_env.insert(
                    n.clone(),
                    VarBinding {
                        lty: scrut_lty.clone(),
                        mutable: false,
                    },
                );
                ExecPattern::Bind(n.clone())
            }
            ExprKind::None => ExecPattern::Ctor {
                ctor: "None".to_string(),
                binders: Vec::new(),
            },
            ExprKind::CapName(cname) => ExecPattern::Ctor {
                ctor: cname.clone(),
                binders: Vec::new(),
            },
            ExprKind::Call { callee, args } => {
                let cname = match &callee.kind {
                    ExprKind::CapName(s) => s.clone(),
                    _ => "_".to_string(),
                };
                let mut binders = Vec::with_capacity(args.len());
                let field_ltys: Vec<LTy> = match (cname.as_str(), &scrut_lty.ty) {
                    ("Ok", Ty::Result { ok_ty, .. }) => {
                        vec![LTy::new(ok_ty.as_ref().clone(), scrut_lty.tags.clone())]
                    }
                    ("Error", Ty::Result { err_ty, .. }) => {
                        vec![LTy::new(err_ty.as_ref().clone(), scrut_lty.tags.clone())]
                    }
                    ("Err", Ty::Result { .. }) => {
                        self.diags.push(
                            Diagnostic::error(
                                DiagCode::TypeError,
                                "`Result` error variant is `Error(...)`, not `Err(...)`",
                            )
                            .with_span(pat.span),
                        );
                        Vec::new()
                    }
                    ("Some", Ty::Option(inner)) => {
                        vec![LTy::new(inner.as_ref().clone(), scrut_lty.tags.clone())]
                    }
                    (_, Ty::Data(dname)) => self
                        .enums
                        .get(dname)
                        .and_then(|d| d.ctors.iter().find(|c| c.name == cname))
                        .map(|c| {
                            c.fields
                                .iter()
                                .map(|f| LTy::new(f.ty.clone(), f.tags.union(&scrut_lty.tags)))
                                .collect()
                        })
                        .unwrap_or_default(),
                    _ => Vec::new(),
                };
                for (i, a) in args.iter().enumerate() {
                    let bname = match a {
                        CallArg::Positional(Expr {
                            kind: ExprKind::Ident(s),
                            ..
                        }) => s.clone(),
                        _ => self.fresh("wild"),
                    };
                    let blty = field_ltys
                        .get(i)
                        .cloned()
                        .unwrap_or_else(|| LTy::new(Ty::Unit, scrut_lty.tags.clone()));
                    arm_env.insert(
                        bname.clone(),
                        VarBinding {
                            lty: blty,
                            mutable: false,
                        },
                    );
                    binders.push(bname);
                }
                ExecPattern::Ctor {
                    ctor: cname,
                    binders,
                }
            }
            ExprKind::List(items) => {
                let elem_lty = match &scrut_lty.ty {
                    Ty::List(el) => LTy::new(el.ty.clone(), el.tags.union(&scrut_lty.tags)),
                    _ => LTy::new(Ty::Unit, scrut_lty.tags.clone()),
                };
                let mut names = Vec::with_capacity(items.len());
                for it in items {
                    let bname = match &it.kind {
                        ExprKind::Ident(s) => s.clone(),
                        _ => self.fresh("wild"),
                    };
                    arm_env.insert(
                        bname.clone(),
                        VarBinding {
                            lty: elem_lty.clone(),
                            mutable: false,
                        },
                    );
                    names.push(bname);
                }
                ExecPattern::ListExact(names)
            }
            ExprKind::Int(raw) => {
                let v = raw.replace('_', "").parse::<i64>().unwrap_or(0);
                ExecPattern::Lit(Literal::int(v))
            }
            ExprKind::Text { value, .. } => ExecPattern::Lit(Literal::Text(value.clone())),
            ExprKind::Bool(b) => ExecPattern::Lit(Literal::Bool(*b)),
            _ => ExecPattern::Wildcard,
        }
    }

    #[expect(
        clippy::too_many_arguments,
        reason = "table literal inference resolves column types, nullability, and dynamic cells"
    )]
    fn check_table_lit(
        &mut self,
        headers: &[ast::SpannedName],
        rows: &[Vec<Expr>],
        span: Span,
        env: &HashMap<Ident, VarBinding>,
        expected: Option<&Ty>,
        pc: &TagSet,
        scope: LocalScopeKind,
        ret_ctx: Option<(&str, Option<&Ty>)>,
    ) -> (ExecExpr, LTy) {
        let exp_tt = match expected {
            Some(Ty::Table(tt)) => Some(tt),
            _ => None,
        };
        let ncols = headers.len();
        let mut col_tys: Vec<Option<ScalarTy>> = vec![None; ncols];
        let mut col_has_none: Vec<bool> = vec![false; ncols];
        let mut col_tags: Vec<TagSet> = vec![TagSet::empty(); ncols];
        let mut init_row_tags = TagSet::empty();

        if let Some(ett) = exp_tt {
            init_row_tags = ett.row_tags.clone();
            for (ci, h) in headers.iter().enumerate() {
                if let Some(cs) = ett.find_col(&h.name) {
                    col_tys[ci] = Some(cs.ty.clone());
                    col_tags[ci] = col_tags[ci].union(&cs.tags);
                }
            }
        }

        // First pass: type-check every cell expression and determine unified column ScalarTy.
        let mut cell_exprs: Vec<Vec<(ExecExpr, LTy)>> = Vec::with_capacity(rows.len());
        let mut all_const_lits = true;

        for row in rows {
            if row.len() != ncols {
                self.diags.push(
                    Diagnostic::error(
                        DiagCode::TypeError,
                        format!(
                            "table literal row has {} cells, expected {ncols}",
                            row.len()
                        ),
                    )
                    .with_span(span),
                );
                continue;
            }
            let mut r_out = Vec::with_capacity(ncols);
            for (ci, cell) in row.iter().enumerate() {
                let hint = col_tys[ci].as_ref().map(|st| match st {
                    ScalarTy::Option(inner) => inner.to_ty(),
                    other => other.to_ty(),
                });
                let (cex, clty) = self.check_expr(cell, env, hint.as_ref(), pc, scope, ret_ctx);
                if !matches!(cex, ExecExpr::Lit(_)) {
                    all_const_lits = false;
                }
                col_tags[ci] = col_tags[ci].union(&clty.effective_tags());
                if matches!(cell.kind, ExprKind::None) {
                    col_has_none[ci] = true;
                } else if let Some(st) = clty.ty.to_scalar_ty() {
                    let base_st = match &st {
                        ScalarTy::Option(inner) => {
                            col_has_none[ci] = true;
                            inner.as_ref().clone()
                        }
                        other => other.clone(),
                    };
                    if col_tys[ci].is_none() {
                        col_tys[ci] = Some(base_st);
                    }
                }
                r_out.push((cex, clty));
            }
            cell_exprs.push(r_out);
        }

        let mut cols = Vec::with_capacity(ncols);
        for (ci, h) in headers.iter().enumerate() {
            let mut ty = col_tys[ci].clone().unwrap_or_else(|| {
                if col_has_none[ci] {
                    ScalarTy::Unit
                } else {
                    ScalarTy::Text
                }
            });
            if col_has_none[ci] {
                ty = ensure_option_scalar(&ty);
            }
            cols.push(ColSpec {
                name: h.name.clone(),
                ty,
                tags: col_tags[ci].clone(),
                bucketed: false,
                agg_kind: AggKind::Raw,
            });
        }

        let tt = TableTy {
            cols: cols.clone(),
            row_tags: init_row_tags,
            order_tags: TagSet::empty(),
            grouped_by: None,
            summarized: false,
            distinct_by: None,
        };

        // If all cells are constant literals AND no column needs Option wrapping of a literal,
        // emit a pure Core IR v0.1 `TableLit`!
        let needs_dynamic =
            !all_const_lits || cols.iter().any(|c| c.ty.is_option()) && !rows.is_empty();
        if !needs_dynamic {
            let mut lit_rows = Vec::with_capacity(cell_exprs.len());
            for r in cell_exprs {
                let mut cells = Vec::with_capacity(ncols);
                for (cex, _) in r {
                    if let Some(l) = cex.into_lit() {
                        cells.push(l);
                    }
                }
                lit_rows.push(RowLit { cells });
            }
            return (
                ExecExpr::TableLit {
                    schema: tt.clone(),
                    rows: lit_rows,
                },
                LTy::public(Ty::Table(tt)),
            );
        }

        // Dynamic table builder (wraps non-null cells in `SomeVal` for `T?` columns and evaluates expressions).
        let mut flat_args = Vec::with_capacity(cell_exprs.len() * ncols);
        for r in cell_exprs {
            for (ci, (mut cex, clty)) in r.into_iter().enumerate() {
                if let ScalarTy::Option(inner) = &cols[ci].ty {
                    if matches!(cex, ExecExpr::Lit(Literal::NoneLit(_))) {
                        cex = ExecExpr::Lit(Literal::NoneLit(inner.to_ty()));
                    } else if !clty.ty.is_option() {
                        cex = ExecExpr::Prim {
                            op: ExecPrimOp::Core(PrimOp::SomeVal(inner.to_ty())),
                            args: vec![cex],
                        };
                    }
                }
                flat_args.push(cex);
            }
        }
        (
            ExecExpr::Prim {
                op: ExecPrimOp::TableBuildDynamic(tt.clone()),
                args: flat_args,
            },
            LTy::public(Ty::Table(tt)),
        )
    }

    // -----------------------------------------------------------------------
    // Row Expression Checking (inside `where`, `derive`, `summarize`, `schema where`)
    // -----------------------------------------------------------------------

    #[expect(
        clippy::too_many_arguments,
        reason = "handles built-in row method calls and schema-where shorthands"
    )]
    fn check_row_method_call(
        &mut self,
        re: ExecRowExpr,
        rty: Ty,
        rtags: TagSet,
        member: &str,
        args: &[CallArg],
        call_span: Span,
        recv_span: Span,
        cols: &[ColSpec],
        outer_env: &HashMap<Ident, VarBinding>,
        allow_dot_self: bool,
    ) -> Option<(ExecRowExpr, Ty, TagSet)> {
        if args.is_empty()
            && rty == Ty::Text
            && let Some((op, out_ty)) = text_prop_op(member)
        {
            return Some((ExecRowExpr::Prim { op, args: vec![re] }, out_ty, rtags));
        }
        if args.is_empty()
            && matches!(member, "ceil" | "floor" | "trunc" | "to_int")
            && let Some((op, out_ty)) = numeric_prop_op(&rty, member)
        {
            return Some((ExecRowExpr::Prim { op, args: vec![re] }, out_ty, rtags));
        }
        match member {
            "contains?" | "starts_with?" | "ends_with?" => {
                if rty != Ty::Text {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::TypeError,
                            format!("`.{member}` requires a `Text` receiver, found `{rty:?}`"),
                        )
                        .with_span(recv_span),
                    );
                    return Some((ExecRowExpr::Lit(Literal::Bool(false)), Ty::Bool, rtags));
                }
                let (key, op) = match member {
                    "contains?" => ("sub", ExecPrimOp::Core(PrimOp::ContainsText)),
                    "starts_with?" => ("prefix", ExecPrimOp::StartsWithText),
                    _ => ("suffix", ExecPrimOp::EndsWithText),
                };
                let Some(arg_e) = extract_one_arg(args, key) else {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::TypeError,
                            format!("`Text.{member}` expects 1 `Text` argument (`{key}:`)"),
                        )
                        .with_span(call_span),
                    );
                    return Some((ExecRowExpr::Lit(Literal::Bool(false)), Ty::Bool, rtags));
                };
                let (are, aty, atags) =
                    self.check_row_expr(arg_e, cols, outer_env, Some(&Ty::Text), allow_dot_self);
                if aty != Ty::Text {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::TypeError,
                            format!("`Text.{member}` expects a `Text` argument, found `{aty:?}`"),
                        )
                        .with_span(arg_e.span),
                    );
                }
                Some((
                    ExecRowExpr::Prim {
                        op,
                        args: vec![re, are],
                    },
                    Ty::Bool,
                    rtags.union(&atags),
                ))
            }
            "slice" => {
                if rty != Ty::Text {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::TypeError,
                            format!("`.slice` requires a `Text` receiver, found `{rty:?}`"),
                        )
                        .with_span(recv_span),
                    );
                    return Some((
                        ExecRowExpr::Lit(Literal::Text(String::new())),
                        Ty::Text,
                        rtags,
                    ));
                }
                let Some((start_e, len_e)) = extract_two_args(args, "start", "len") else {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::TypeError,
                            "`Text.slice` expects `(start: Int, len: Int)`",
                        )
                        .with_span(call_span),
                    );
                    return Some((
                        ExecRowExpr::Lit(Literal::Text(String::new())),
                        Ty::Text,
                        rtags,
                    ));
                };
                let (sre, sty, stags) =
                    self.check_row_expr(start_e, cols, outer_env, Some(&Ty::Int), allow_dot_self);
                let (lre, lty, ltags) =
                    self.check_row_expr(len_e, cols, outer_env, Some(&Ty::Int), allow_dot_self);
                if sty != Ty::Int {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::TypeError,
                            format!("`Text.slice` `start` must be `Int`, found `{sty:?}`"),
                        )
                        .with_span(start_e.span),
                    );
                }
                if lty != Ty::Int {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::TypeError,
                            format!("`Text.slice` `len` must be `Int`, found `{lty:?}`"),
                        )
                        .with_span(len_e.span),
                    );
                }
                Some((
                    ExecRowExpr::Prim {
                        op: ExecPrimOp::SliceText,
                        args: vec![re, sre, lre],
                    },
                    Ty::Text,
                    rtags.union(&stags).union(&ltags),
                ))
            }
            "in?" => {
                let Some(base_ty) = in_list_base_ty(&rty).cloned() else {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::TypeError,
                            format!("`.in?(list)` is not supported on receiver type `{rty:?}`"),
                        )
                        .with_span(recv_span),
                    );
                    return Some((ExecRowExpr::Lit(Literal::Bool(false)), Ty::Bool, rtags));
                };
                let Some(list_e) = extract_one_arg(args, "list") else {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::TypeError,
                            "`.in?(list)` requires 1 `List` argument",
                        )
                        .with_span(call_span),
                    );
                    return Some((ExecRowExpr::Lit(Literal::Bool(false)), Ty::Bool, rtags));
                };
                let exp_list_ty = Ty::List(Box::new(LTy::public(base_ty.clone())));
                let (lre, lty, ltags) = self.check_row_expr(
                    list_e,
                    cols,
                    outer_env,
                    Some(&exp_list_ty),
                    allow_dot_self,
                );
                match &lty {
                    Ty::List(el) if el.ty == base_ty || is_unresolved_list(&lty) => {}
                    other => {
                        self.diags.push(
                            Diagnostic::error(
                                DiagCode::TypeError,
                                format!("`.in?` expects `List({base_ty:?})`, found `{other:?}`"),
                            )
                            .with_span(list_e.span),
                        );
                    }
                }
                Some((
                    ExecRowExpr::Prim {
                        op: ExecPrimOp::InList,
                        args: vec![re, lre],
                    },
                    Ty::Bool,
                    rtags.union(&ltags),
                ))
            }
            "clamp" => {
                let Some(op) = clamp_op_for_ty(&rty) else {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::TypeError,
                            format!(
                                "`.clamp` requires `Int`, `Float`, or `Decimal`, found `{rty:?}`"
                            ),
                        )
                        .with_span(recv_span),
                    );
                    return Some((re, rty, rtags));
                };
                let Some((lo_e, hi_e)) = extract_two_args(args, "lo", "hi") else {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::TypeError,
                            "`.clamp` expects `(lo, hi)` bounds of the same numeric type",
                        )
                        .with_span(call_span),
                    );
                    return Some((re, rty, rtags));
                };
                let (lo_re, lo_ty, lo_tags) =
                    self.check_row_expr(lo_e, cols, outer_env, Some(&rty), allow_dot_self);
                let (hi_re, hi_ty, hi_tags) =
                    self.check_row_expr(hi_e, cols, outer_env, Some(&rty), allow_dot_self);
                if lo_ty != rty || hi_ty != rty {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::TypeError,
                            format!("`.clamp(lo, hi)` bounds must match receiver type `{rty:?}`"),
                        )
                        .with_span(call_span),
                    );
                }
                Some((
                    ExecRowExpr::Prim {
                        op,
                        args: vec![re, lo_re, hi_re],
                    },
                    rty,
                    rtags.union(&lo_tags).union(&hi_tags),
                ))
            }
            "round_to" => {
                if rty != Ty::Float {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::TypeError,
                            format!("`.round_to` requires a `Float` receiver, found `{rty:?}`"),
                        )
                        .with_span(recv_span),
                    );
                    return Some((re, rty, rtags));
                }
                let (step_opt, half_even) = self.parse_round_to_args(args, call_span);
                let Some(step_e) = step_opt else {
                    return Some((re, Ty::Float, rtags));
                };
                let (sre, sty, stags) =
                    self.check_row_expr(step_e, cols, outer_env, Some(&Ty::Float), allow_dot_self);
                if sty != Ty::Float {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::TypeError,
                            format!("`Float.round_to` `step` must be `Float`, found `{sty:?}`"),
                        )
                        .with_span(step_e.span),
                    );
                }
                let pop = if half_even {
                    ExecPrimOp::RoundToFloatEven
                } else {
                    ExecPrimOp::RoundToFloat
                };
                Some((
                    ExecRowExpr::Prim {
                        op: pop,
                        args: vec![re, sre],
                    },
                    Ty::Float,
                    rtags.union(&stags),
                ))
            }
            "round" => {
                if !matches!(rty, Ty::Float | Ty::Decimal) {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::TypeError,
                            format!("`.round` requires `Float` or `Decimal`, found `{rty:?}`"),
                        )
                        .with_span(recv_span),
                    );
                    return Some((re, rty, rtags));
                }
                let (places_opt, half_even) = self.parse_round_args(args, call_span);
                let (are, _, atags) = if let Some(a0) = places_opt {
                    let (e, ty, tg) =
                        self.check_row_expr(a0, cols, outer_env, Some(&Ty::Int), allow_dot_self);
                    if ty != Ty::Int {
                        self.diags.push(
                            Diagnostic::error(
                                DiagCode::TypeError,
                                format!("`.round` places must be `Int`, found `{ty:?}`"),
                            )
                            .with_span(a0.span),
                        );
                    }
                    (e, ty, tg)
                } else {
                    (
                        ExecRowExpr::Lit(Literal::int(0i64)),
                        Ty::Int,
                        TagSet::empty(),
                    )
                };
                let pop = match (rty == Ty::Decimal, half_even) {
                    (false, false) => ExecPrimOp::RoundFloat,
                    (false, true) => ExecPrimOp::RoundFloatEven,
                    (true, false) => ExecPrimOp::RoundDecimal,
                    (true, true) => ExecPrimOp::RoundDecimalEven,
                };
                Some((
                    ExecRowExpr::Prim {
                        op: pop,
                        args: vec![re, are],
                    },
                    rty,
                    rtags.union(&atags),
                ))
            }
            "in_tz" | "date_in_tz" => {
                let Some(CallArg::Positional(a0)) = args.first() else {
                    return None;
                };
                if rty != Ty::Timestamp {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::TypeError,
                            format!("`.{member}` requires a `Timestamp` receiver"),
                        )
                        .with_span(recv_span),
                    );
                }
                let (are, aty, atags) =
                    self.check_row_expr(a0, cols, outer_env, Some(&Ty::Text), allow_dot_self);
                if aty != Ty::Text {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::TypeError,
                            format!("`.{member}` expects a `Text` IANA timezone name"),
                        )
                        .with_span(a0.span),
                    );
                }
                let (op, out_ty) = if member == "in_tz" {
                    (ExecPrimOp::InTz, Ty::Text)
                } else {
                    (ExecPrimOp::DateInTz, Ty::Date)
                };
                Some((
                    ExecRowExpr::Prim {
                        op,
                        args: vec![re, are],
                    },
                    out_ty,
                    rtags.union(&atags),
                ))
            }
            "add_days" => {
                if let Some(a0) = extract_one_arg(args, "days") {
                    return Some(self.check_row_date_add_days(
                        re,
                        rty,
                        rtags,
                        recv_span,
                        a0,
                        cols,
                        outer_env,
                        allow_dot_self,
                    ));
                }
                self.diags.push(
                    Diagnostic::error(
                        DiagCode::TypeError,
                        "`Date.add_days` expects 1 `Int` argument",
                    )
                    .with_span(call_span),
                );
                Some((re, rty, rtags))
            }
            "at_midnight_in_tz" => {
                if let Some(a0) = extract_one_arg(args, "tz") {
                    return Some(self.check_row_date_midnight_tz(
                        re,
                        rty,
                        rtags,
                        recv_span,
                        a0,
                        cols,
                        outer_env,
                        allow_dot_self,
                    ));
                }
                self.diags.push(
                    Diagnostic::error(
                        DiagCode::TypeError,
                        "`Date.at_midnight_in_tz` expects a `Text` IANA timezone name",
                    )
                    .with_span(call_span),
                );
                Some((
                    ExecRowExpr::Lit(Literal::timestamp(0i64)),
                    Ty::Timestamp,
                    rtags,
                ))
            }
            "predict" if rty == Ty::LinearModel => {
                let Some(CallArg::Positional(a0)) = args.first() else {
                    return None;
                };
                let (are, aty, atags) =
                    self.check_row_expr(a0, cols, outer_env, Some(&Ty::Float), allow_dot_self);
                if !matches!(aty, Ty::Int | Ty::Float | Ty::Decimal) {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::TypeError,
                            "`LinearModel.predict` argument must be `Int`, `Float`, or `Decimal`",
                        )
                        .with_span(a0.span),
                    );
                }
                Some((
                    ExecRowExpr::Prim {
                        op: ExecPrimOp::LinearModelPredict,
                        args: vec![re, are],
                    },
                    Ty::Float,
                    rtags.union(&atags),
                ))
            }
            _ => None,
        }
    }

    fn check_row_expr(
        &mut self,
        expr: &Expr,
        cols: &[ColSpec],
        outer_env: &HashMap<Ident, VarBinding>,
        expected: Option<&Ty>,
        allow_dot_self: bool,
    ) -> (ExecRowExpr, Ty, TagSet) {
        match &expr.kind {
            ExprKind::Int(raw) => {
                let (e, lty) = self.check_int_lit(raw, expected, expr.span);
                let lit = e.into_lit().unwrap_or_else(|| Literal::int(0i64));
                (ExecRowExpr::Lit(lit), lty.ty, TagSet::empty())
            }
            ExprKind::Decimal(raw) => {
                let (e, lty) = self.check_decimal_lit(raw, expected, expr.span);
                let lit = e.into_lit().unwrap_or(Literal::Decimal(BigInt::ZERO));
                (ExecRowExpr::Lit(lit), lty.ty, TagSet::empty())
            }
            ExprKind::Date(raw) => {
                let d = parse_iso_date(raw).unwrap_or(0);
                (
                    ExecRowExpr::Lit(Literal::date(d)),
                    Ty::Date,
                    TagSet::empty(),
                )
            }
            ExprKind::Timestamp(raw) => {
                let ts = parse_iso_timestamp(raw).unwrap_or(0);
                (
                    ExecRowExpr::Lit(Literal::timestamp(ts)),
                    Ty::Timestamp,
                    TagSet::empty(),
                )
            }
            ExprKind::Text { value, .. } => (
                ExecRowExpr::Lit(Literal::Text(value.clone())),
                Ty::Text,
                TagSet::empty(),
            ),
            ExprKind::InterpText { parts, .. } => {
                let mut acc: Option<ExecRowExpr> = None;
                let mut tags = TagSet::empty();
                for part in parts {
                    let piece = match part {
                        ast::InterpPart::Literal { value, .. } => {
                            if value.is_empty() {
                                continue;
                            }
                            ExecRowExpr::Lit(Literal::Text(value.clone()))
                        }
                        ast::InterpPart::Expr(ex) => {
                            let (re, rty, rtags) =
                                self.check_row_expr(ex, cols, outer_env, None, allow_dot_self);
                            tags = tags.union(&rtags);
                            if rty == Ty::Text {
                                re
                            } else {
                                ExecRowExpr::Prim {
                                    op: ExecPrimOp::ValToText,
                                    args: vec![re],
                                }
                            }
                        }
                    };
                    acc = Some(match acc {
                        None => piece,
                        Some(prev) => ExecRowExpr::Prim {
                            op: ExecPrimOp::Core(PrimOp::ConcatText),
                            args: vec![prev, piece],
                        },
                    });
                }
                (
                    acc.unwrap_or_else(|| ExecRowExpr::Lit(Literal::Text(String::new()))),
                    Ty::Text,
                    tags,
                )
            }
            ExprKind::Atom(a) => (
                ExecRowExpr::Lit(Literal::Text(format!(":{a}"))),
                Ty::Text,
                TagSet::empty(),
            ),
            ExprKind::Bool(b) => (
                ExecRowExpr::Lit(Literal::Bool(*b)),
                Ty::Bool,
                TagSet::empty(),
            ),
            ExprKind::None => {
                let inner = match expected {
                    Some(Ty::Option(t)) => t.as_ref().clone(),
                    _ => Ty::Unit,
                };
                (
                    ExecRowExpr::Lit(Literal::NoneLit(inner.clone())),
                    Ty::Option(Box::new(inner)),
                    TagSet::empty(),
                )
            }
            ExprKind::List(elems) => {
                let exp_elem = match expected {
                    Some(Ty::List(el)) => Some(el.as_ref().clone()),
                    _ => None,
                };
                if elems.is_empty() {
                    let elem_lty = exp_elem.unwrap_or_else(|| {
                        LTy::public(Ty::Data(TY_UNRESOLVED_LIST_ELEM.to_string()))
                    });
                    return (
                        ExecRowExpr::Prim {
                            op: ExecPrimOp::Core(PrimOp::ListLit(elem_lty.clone())),
                            args: Vec::new(),
                        },
                        Ty::List(Box::new(elem_lty)),
                        TagSet::empty(),
                    );
                }
                let mut res = Vec::with_capacity(elems.len());
                let mut inferred_elem: Option<LTy> = exp_elem;
                let mut tags = TagSet::empty();
                for e in elems {
                    let hint = inferred_elem.as_ref().map(|l| &l.ty);
                    let (ere, ety, etags) =
                        self.check_row_expr(e, cols, outer_env, hint, allow_dot_self);
                    tags = tags.union(&etags);
                    inferred_elem = Some(match inferred_elem {
                        None => LTy::new(ety, etags),
                        Some(prev) => {
                            if prev.ty != ety {
                                self.diags.push(
                                    Diagnostic::error(
                                        DiagCode::TypeError,
                                        format!(
                                            "list elements must share type `{:?}`, found `{:?}`",
                                            prev.ty, ety
                                        ),
                                    )
                                    .with_span(e.span),
                                );
                            }
                            LTy::new(prev.ty, prev.tags.union(&etags))
                        }
                    });
                    res.push(ere);
                }
                let el = inferred_elem.unwrap_or_else(|| LTy::public(Ty::Unit));
                (
                    ExecRowExpr::Prim {
                        op: ExecPrimOp::Core(PrimOp::ListLit(el.clone())),
                        args: res,
                    },
                    Ty::List(Box::new(el)),
                    tags,
                )
            }
            ExprKind::DotSelf => {
                if allow_dot_self && let Some(sc) = cols.iter().find(|c| c.name == "__self") {
                    return (
                        ExecRowExpr::Col("__self".to_string()),
                        sc.ty.to_ty(),
                        sc.tags.clone(),
                    );
                }
                self.diags.push(
                    Diagnostic::error(
                        DiagCode::TypeError,
                        "`.` is only valid inside a `schema where` or `promise` clause",
                    )
                    .with_span(expr.span),
                );
                (ExecRowExpr::Lit(Literal::Unit), Ty::Unit, TagSet::empty())
            }
            ExprKind::DotField(m) => {
                // Inside `schema where`, `.empty?` means `.__self.empty?`!
                if allow_dot_self
                    && let Some(sc) = cols.iter().find(|c| c.name == "__self")
                    && let Some((re, ty)) = row_property(
                        ExecRowExpr::Col("__self".to_string()),
                        &sc.ty.to_ty(),
                        &m.name,
                    )
                {
                    return (re, ty, sc.tags.clone());
                }
                if let Some(c) = cols.iter().find(|c| c.name == m.name) {
                    (
                        ExecRowExpr::Col(c.name.clone()),
                        c.ty.to_ty(),
                        c.tags.clone(),
                    )
                } else {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::TypeError,
                            format!("unknown column `.{}` in row expression", m.name),
                        )
                        .with_span(m.span),
                    );
                    (ExecRowExpr::Lit(Literal::Unit), Ty::Unit, TagSet::empty())
                }
            }
            ExprKind::Ident(name) => {
                if let Some(b) = outer_env.get(name) {
                    (
                        ExecRowExpr::OuterVar(name.clone()),
                        b.lty.ty.clone(),
                        b.lty.effective_tags(),
                    )
                } else if let Some(c) = self.consts.get(name) {
                    (
                        ExecRowExpr::ConstRef(name.clone()),
                        c.lty.ty.clone(),
                        c.lty.effective_tags(),
                    )
                } else {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::ResolveError,
                            format!("unknown variable `{name}` in row expression (use `.{name}` for a column)"),
                        )
                        .with_span(expr.span),
                    );
                    (ExecRowExpr::Lit(Literal::Unit), Ty::Unit, TagSet::empty())
                }
            }
            ExprKind::Paren(inner) => {
                self.check_row_expr(inner, cols, outer_env, expected, allow_dot_self)
            }
            ExprKind::Unary { op, expr: inner } => {
                let (re, rty, rtags) =
                    self.check_row_expr(inner, cols, outer_env, expected, allow_dot_self);
                let (pop, out_ty) = match op {
                    UnaryOp::Not => (ExecPrimOp::Core(PrimOp::NotBool), Ty::Bool),
                    UnaryOp::Neg => match rty {
                        Ty::Decimal => (ExecPrimOp::Core(PrimOp::NegDec), Ty::Decimal),
                        Ty::Float => (ExecPrimOp::NegFloat, Ty::Float),
                        _ => (ExecPrimOp::Core(PrimOp::NegInt), Ty::Int),
                    },
                    UnaryOp::Try => {
                        self.diags.push(
                            Diagnostic::error(
                                DiagCode::TypeError,
                                "`try` is not allowed inside a pure row expression",
                            )
                            .with_span(expr.span),
                        );
                        return (re, rty, rtags);
                    }
                };
                (
                    ExecRowExpr::Prim {
                        op: pop,
                        args: vec![re],
                    },
                    out_ty,
                    rtags,
                )
            }
            ExprKind::Binary { op, lhs, rhs } => {
                if *op == BinOp::Coalesce {
                    let (lre, lty, ltags) =
                        self.check_row_expr(lhs, cols, outer_env, None, allow_dot_self);
                    let inner = match &lty {
                        Ty::Option(t) => t.as_ref().clone(),
                        other => other.clone(),
                    };
                    let (rre, _, rtags) =
                        self.check_row_expr(rhs, cols, outer_env, Some(&inner), allow_dot_self);
                    return (
                        ExecRowExpr::Coalesce {
                            opt_expr: Box::new(lre),
                            default_expr: Box::new(rre),
                        },
                        inner,
                        ltags.union(&rtags),
                    );
                }

                // Iteratively flatten long left-associative binary row expressions in O(1) stack.
                let mut chain: Vec<(BinOp, &Expr)> = Vec::new();
                chain.push((*op, rhs.as_ref()));
                let mut base = lhs.as_ref();
                while let ExprKind::Binary {
                    op: lop,
                    lhs: llhs,
                    rhs: lrhs,
                } = &base.kind
                {
                    if *lop == BinOp::Coalesce {
                        break;
                    }
                    chain.push((*lop, lrhs.as_ref()));
                    base = llhs.as_ref();
                }

                let (mut lre, mut lty, mut ltags) =
                    self.check_row_expr(base, cols, outer_env, None, allow_dot_self);
                let mut lhs_lit_expr: Option<&Expr> = Some(base);

                while let Some((cur_op, cur_rhs)) = chain.pop() {
                    let rhs_hint = match &lty {
                        Ty::Option(inner)
                            if matches!(cur_op, BinOp::Eq | BinOp::Ne)
                                && !matches!(cur_rhs.kind, ExprKind::None) =>
                        {
                            Some(inner.as_ref())
                        }
                        t => Some(t),
                    };
                    let (mut rre, mut rty, rtags) =
                        self.check_row_expr(cur_rhs, cols, outer_env, rhs_hint, allow_dot_self);

                    if lty != rty {
                        let lhs_target = match (&rty, cur_op) {
                            (Ty::Option(inner), BinOp::Eq | BinOp::Ne) => inner.as_ref(),
                            (other, _) => other,
                        };
                        let rhs_target = match (&lty, cur_op) {
                            (Ty::Option(inner), BinOp::Eq | BinOp::Ne) => inner.as_ref(),
                            (other, _) => other,
                        };
                        if let Some(le) = lhs_lit_expr
                            && matches!(lty, Ty::Decimal)
                            && matches!(lhs_target, Ty::Float)
                            && is_numeric_lit(le)
                        {
                            let (e, l) = self.check_decimal_from_expr(le, &Ty::Float);
                            if let Some(lit) = e.into_lit() {
                                lre = ExecRowExpr::Lit(lit);
                                lty = l.ty;
                            }
                        } else if let Some(le) = lhs_lit_expr
                            && matches!(lty, Ty::Int)
                            && matches!(lhs_target, Ty::Decimal | Ty::Float)
                            && is_numeric_lit(le)
                        {
                            let (e, l) = self.check_decimal_from_expr(le, lhs_target);
                            if let Some(lit) = e.into_lit() {
                                lre = ExecRowExpr::Lit(lit);
                                lty = l.ty;
                            }
                        } else if matches!(rty, Ty::Int | Ty::Decimal)
                            && matches!(rhs_target, Ty::Float)
                            && is_numeric_lit(cur_rhs)
                        {
                            let (e, l) = self.check_decimal_from_expr(cur_rhs, &Ty::Float);
                            if let Some(lit) = e.into_lit() {
                                rre = ExecRowExpr::Lit(lit);
                                rty = l.ty;
                            }
                        } else if matches!(rty, Ty::Int)
                            && matches!(rhs_target, Ty::Decimal)
                            && is_numeric_lit(cur_rhs)
                        {
                            let (e, l) = self.check_decimal_from_expr(cur_rhs, &Ty::Decimal);
                            if let Some(lit) = e.into_lit() {
                                rre = ExecRowExpr::Lit(lit);
                                rty = l.ty;
                            }
                        }
                    }

                    if matches!(cur_op, BinOp::Eq | BinOp::Ne) {
                        // Refine untyped `none` (`Option(Unit)`) against concrete `Option(T)` on either side.
                        if matches!(&lty, Ty::Option(li) if matches!(li.as_ref(), Ty::Unit))
                            && matches!(&lre, ExecRowExpr::Lit(Literal::NoneLit(Ty::Unit)))
                            && let Ty::Option(ri) = &rty
                            && !matches!(ri.as_ref(), Ty::Unit)
                        {
                            lre = ExecRowExpr::Lit(Literal::NoneLit(ri.as_ref().clone()));
                            lty = rty.clone();
                        } else if matches!(&rty, Ty::Option(ri) if matches!(ri.as_ref(), Ty::Unit))
                            && matches!(&rre, ExecRowExpr::Lit(Literal::NoneLit(Ty::Unit)))
                            && let Ty::Option(li) = &lty
                            && !matches!(li.as_ref(), Ty::Unit)
                        {
                            rre = ExecRowExpr::Lit(Literal::NoneLit(li.as_ref().clone()));
                            rty = lty.clone();
                        }

                        // Coerce `Option(T) == T` or `T == Option(T)` cleanly inside row expressions.
                        if let Ty::Option(inner) = &lty
                            && **inner == rty
                        {
                            rre = ExecRowExpr::Prim {
                                op: ExecPrimOp::Core(PrimOp::SomeVal(rty.clone())),
                                args: vec![rre],
                            };
                            rty = lty.clone();
                        } else if let Ty::Option(inner) = &rty
                            && **inner == lty
                        {
                            lre = ExecRowExpr::Prim {
                                op: ExecPrimOp::Core(PrimOp::SomeVal(lty.clone())),
                                args: vec![lre],
                            };
                            lty = rty.clone();
                        }
                    }
                    let tags = ltags.union(&rtags);
                    let (pop, out_ty) = match cur_op {
                        BinOp::And => (ExecPrimOp::Core(PrimOp::AndBool), Ty::Bool),
                        BinOp::Or => (ExecPrimOp::Core(PrimOp::OrBool), Ty::Bool),
                        BinOp::Eq => (ExecPrimOp::Core(PrimOp::Eq), Ty::Bool),
                        BinOp::Ne => (ExecPrimOp::Core(PrimOp::Ne), Ty::Bool),
                        BinOp::Lt => (ExecPrimOp::Core(PrimOp::Lt), Ty::Bool),
                        BinOp::Le => (ExecPrimOp::Core(PrimOp::Le), Ty::Bool),
                        BinOp::Gt => (ExecPrimOp::Core(PrimOp::Gt), Ty::Bool),
                        BinOp::Ge => (ExecPrimOp::Core(PrimOp::Ge), Ty::Bool),
                        BinOp::Add => match (&lty, &rty) {
                            (Ty::Decimal, Ty::Decimal) => {
                                (ExecPrimOp::Core(PrimOp::AddDec), Ty::Decimal)
                            }
                            (Ty::Float, Ty::Float) => (ExecPrimOp::AddFloat, Ty::Float),
                            (Ty::Text, Ty::Text) => {
                                (ExecPrimOp::Core(PrimOp::ConcatText), Ty::Text)
                            }
                            (Ty::Timestamp, Ty::Duration) => {
                                (ExecPrimOp::Core(PrimOp::AddDuration), Ty::Timestamp)
                            }
                            _ => (ExecPrimOp::Core(PrimOp::AddInt), Ty::Int),
                        },
                        BinOp::Sub => match (&lty, &rty) {
                            (Ty::Decimal, Ty::Decimal) => {
                                (ExecPrimOp::Core(PrimOp::SubDec), Ty::Decimal)
                            }
                            (Ty::Float, Ty::Float) => (ExecPrimOp::SubFloat, Ty::Float),
                            (Ty::Timestamp, Ty::Timestamp) => {
                                (ExecPrimOp::Core(PrimOp::DiffTimestamp), Ty::Duration)
                            }
                            _ => (ExecPrimOp::Core(PrimOp::SubInt), Ty::Int),
                        },
                        BinOp::Mul => match (&lty, &rty) {
                            (Ty::Decimal, Ty::Decimal) => {
                                (ExecPrimOp::Core(PrimOp::MulDec), Ty::Decimal)
                            }
                            (Ty::Float, Ty::Float) => (ExecPrimOp::MulFloat, Ty::Float),
                            _ => (ExecPrimOp::Core(PrimOp::MulInt), Ty::Int),
                        },
                        BinOp::Div => match (&lty, &rty) {
                            (Ty::Decimal, Ty::Decimal) => {
                                (ExecPrimOp::Core(PrimOp::DivDec), Ty::Decimal)
                            }
                            (Ty::Float, Ty::Float) => (ExecPrimOp::DivFloat, Ty::Float),
                            _ => (ExecPrimOp::Core(PrimOp::DivInt), Ty::Int),
                        },
                        BinOp::Mod => (ExecPrimOp::Core(PrimOp::ModInt), Ty::Int),
                        _ => (ExecPrimOp::Core(PrimOp::Eq), Ty::Bool),
                    };
                    lre = ExecRowExpr::Prim {
                        op: pop,
                        args: vec![lre, rre],
                    };
                    lty = out_ty;
                    ltags = tags;
                    lhs_lit_expr = None;
                }
                (lre, lty, ltags)
            }
            ExprKind::Field { receiver, member } => {
                // Duration literals inside row expressions (`5.minutes`).
                if let Some(us) = eval_const_duration_micros(expr) {
                    return (
                        ExecRowExpr::Lit(Literal::duration(us)),
                        Ty::Duration,
                        TagSet::empty(),
                    );
                }
                let (re, rty, rtags) =
                    self.check_row_expr(receiver, cols, outer_env, None, allow_dot_self);
                if let Some((out_re, out_ty)) = row_property(re, &rty, &member.name) {
                    (out_re, out_ty, rtags)
                } else {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::TypeError,
                            format!("unknown row property `.{}`", member.name),
                        )
                        .with_span(expr.span),
                    );
                    (ExecRowExpr::Lit(Literal::Unit), Ty::Unit, rtags)
                }
            }
            ExprKind::Call { callee, args } => {
                // Shorthand `.contains?("@")`, `.starts_with?(...)`, `.in?(...)`, etc. in `schema where`!
                if allow_dot_self
                    && let ExprKind::DotField(m) = &callee.kind
                    && let Some(sc) = cols.iter().find(|c| c.name == "__self")
                    && let Some(out) = self.check_row_method_call(
                        ExecRowExpr::Col("__self".to_string()),
                        sc.ty.to_ty(),
                        sc.tags.clone(),
                        &m.name,
                        args,
                        expr.span,
                        callee.span,
                        cols,
                        outer_env,
                        allow_dot_self,
                    )
                {
                    return out;
                }
                // Method calls inside row expressions (`.lower`, `.slice`, `.starts_with?`, `.in?`, `.clamp`, etc.).
                if let ExprKind::Field { receiver, member } = &callee.kind {
                    let (re, rty, rtags) =
                        self.check_row_expr(receiver, cols, outer_env, None, allow_dot_self);
                    if let Some(out) = self.check_row_method_call(
                        re,
                        rty,
                        rtags,
                        &member.name,
                        args,
                        expr.span,
                        receiver.span,
                        cols,
                        outer_env,
                        allow_dot_self,
                    ) {
                        return out;
                    }
                }
                // Free row functions (`date_trunc`, `months_between`, or pure user `fn`).
                if let ExprKind::Ident(fname) = &callee.kind {
                    if fname == "date_trunc"
                        && let [CallArg::Positional(a), CallArg::Positional(b)] = args.as_slice()
                    {
                        let (ea, ta, tga) =
                            self.check_row_expr(a, cols, outer_env, None, allow_dot_self);
                        if let ExprKind::Atom(unit) = &b.kind {
                            let op = if unit == "month" && ta == Ty::Date {
                                ExecPrimOp::Core(PrimOp::DateTruncMonth)
                            } else {
                                ExecPrimOp::DateTruncUnit(unit.clone())
                            };
                            return (ExecRowExpr::Prim { op, args: vec![ea] }, ta, tga);
                        }
                        let (eb, _, tgb) = self.check_row_expr(
                            b,
                            cols,
                            outer_env,
                            Some(&Ty::Duration),
                            allow_dot_self,
                        );
                        return (
                            ExecRowExpr::Prim {
                                op: ExecPrimOp::DateTruncDuration,
                                args: vec![ea, eb],
                            },
                            ta,
                            tga.union(&tgb),
                        );
                    }
                    if (fname == "months_between" || fname == "days_between")
                        && let [CallArg::Positional(a), CallArg::Positional(b)] = args.as_slice()
                    {
                        let (ea, ta, tga) = self.check_row_expr(
                            a,
                            cols,
                            outer_env,
                            Some(&Ty::Date),
                            allow_dot_self,
                        );
                        if ta != Ty::Date {
                            self.diags.push(
                                Diagnostic::error(
                                    DiagCode::TypeError,
                                    format!("`{fname}` expects `Date` as first argument"),
                                )
                                .with_span(a.span),
                            );
                        }
                        let (eb, tb, tgb) = self.check_row_expr(
                            b,
                            cols,
                            outer_env,
                            Some(&Ty::Date),
                            allow_dot_self,
                        );
                        if tb != Ty::Date {
                            self.diags.push(
                                Diagnostic::error(
                                    DiagCode::TypeError,
                                    format!("`{fname}` expects `Date` as second argument"),
                                )
                                .with_span(b.span),
                            );
                        }
                        let op = if fname == "months_between" {
                            ExecPrimOp::MonthsBetween
                        } else {
                            ExecPrimOp::DaysBetween
                        };
                        return (
                            ExecRowExpr::Prim {
                                op,
                                args: vec![ea, eb],
                            },
                            Ty::Int,
                            tga.union(&tgb),
                        );
                    }
                    if fname == "add_days"
                        && let (Some(CallArg::Positional(d)), Some(days_e)) = (
                            args.first(),
                            extract_one_arg(&args[1.min(args.len())..], "days"),
                        )
                    {
                        let (re, rty, rtags) = self.check_row_expr(
                            d,
                            cols,
                            outer_env,
                            Some(&Ty::Date),
                            allow_dot_self,
                        );
                        return self.check_row_date_add_days(
                            re,
                            rty,
                            rtags,
                            d.span,
                            days_e,
                            cols,
                            outer_env,
                            allow_dot_self,
                        );
                    }
                    if fname == "at_midnight_in_tz"
                        && let (Some(CallArg::Positional(d)), Some(tz_e)) = (
                            args.first(),
                            extract_one_arg(&args[1.min(args.len())..], "tz"),
                        )
                    {
                        let (re, rty, rtags) = self.check_row_expr(
                            d,
                            cols,
                            outer_env,
                            Some(&Ty::Date),
                            allow_dot_self,
                        );
                        return self.check_row_date_midnight_tz(
                            re,
                            rty,
                            rtags,
                            d.span,
                            tz_e,
                            cols,
                            outer_env,
                            allow_dot_self,
                        );
                    }
                    if (fname == "in_tz" || fname == "date_in_tz")
                        && let [CallArg::Positional(a), CallArg::Positional(z)] = args.as_slice()
                    {
                        let (ea, ta, tga) = self.check_row_expr(
                            a,
                            cols,
                            outer_env,
                            Some(&Ty::Timestamp),
                            allow_dot_self,
                        );
                        if ta != Ty::Timestamp {
                            self.diags.push(
                                Diagnostic::error(
                                    DiagCode::TypeError,
                                    format!("`{fname}` expects `Timestamp` as first argument"),
                                )
                                .with_span(a.span),
                            );
                        }
                        let (ez, tz, tgz) = self.check_row_expr(
                            z,
                            cols,
                            outer_env,
                            Some(&Ty::Text),
                            allow_dot_self,
                        );
                        if tz != Ty::Text {
                            self.diags.push(
                                Diagnostic::error(
                                    DiagCode::TypeError,
                                    format!("`{fname}` expects a `Text` IANA timezone name"),
                                )
                                .with_span(z.span),
                            );
                        }
                        let (op, out_ty) = if fname == "in_tz" {
                            (ExecPrimOp::InTz, Ty::Text)
                        } else {
                            (ExecPrimOp::DateInTz, Ty::Date)
                        };
                        return (
                            ExecRowExpr::Prim {
                                op,
                                args: vec![ea, ez],
                            },
                            out_ty,
                            tga.union(&tgz),
                        );
                    }
                    if let Some(sig) = self.fn_sigs.get(fname).cloned() {
                        if !sig.is_pure {
                            self.diags.push(
                                Diagnostic::error(
                                    DiagCode::CapabilityError,
                                    format!("impure function `{fname}` cannot be called inside a pure table pipeline"),
                                )
                                .with_span(expr.span),
                            );
                        }
                        let ret_lty = self
                            .ensure_fn_checked(fname)
                            .or(sig.ret)
                            .unwrap_or_else(|| LTy::public(Ty::Unit));
                        let mut rargs = Vec::with_capacity(args.len());
                        let mut tags = ret_lty.tags;
                        for (i, arg) in args.iter().enumerate() {
                            let e = match arg {
                                CallArg::Positional(e) | CallArg::Named { value: e, .. } => e,
                            };
                            let hint = sig.params.get(i).map(|(_, l)| &l.ty);
                            let (are, _, atags) =
                                self.check_row_expr(e, cols, outer_env, hint, allow_dot_self);
                            tags = tags.union(&atags);
                            rargs.push(are);
                        }
                        return (
                            ExecRowExpr::CallPure {
                                fn_name: fname.clone(),
                                args: rargs,
                            },
                            ret_lty.ty,
                            tags,
                        );
                    }
                }
                let mut diag = match &callee.kind {
                    ExprKind::Ident(fname) => Diagnostic::error(
                        DiagCode::TypeError,
                        format!("unsupported call `{fname}(...)` in row expression"),
                    ),
                    _ => {
                        Diagnostic::error(DiagCode::TypeError, "unsupported call in row expression")
                    }
                }
                .with_span(expr.span);
                if let ExprKind::Ident(fname) = &callee.kind {
                    match fname.as_str() {
                        "pseudonymize" => {
                            diag = diag.with_hint(
                                "`pseudonymize` is a table pipeline verb, not a row function; use `|> pseudonymize(.col, key: secret)` instead of calling it inside `derive(...)`",
                            );
                        }
                        "redact" => {
                            diag = diag.with_hint(
                                "`redact` is a table pipeline verb, not a row function; use `|> redact(.col)` instead of calling it inside `derive(...)`",
                            );
                        }
                        "coarsen" => {
                            diag = diag.with_hint(
                                "`coarsen` is a `derive(...)` column declassifier, not a general row expression; write `|> derive(out = coarsen(.col, allow: [...], other: \"...\"))`",
                            );
                        }
                        "dedupe_by" => {
                            diag = diag.with_hint(
                                "`dedupe_by` is a table pipeline verb, not a row function; use `|> dedupe_by(.k, order_by: [desc(.ts)], keep: :first)` instead",
                            );
                        }
                        "suppress_small_groups" => {
                            diag = diag.with_hint(
                                "`suppress_small_groups` is a table pipeline verb, not a row function; pipe it directly after `summarize(...)` as `|> suppress_small_groups(min: k, distinct_by: .id)`",
                            );
                        }
                        "suppress_small_cells" => {
                            diag = diag.with_hint(
                                "`suppress_small_cells` is a table pipeline verb, not a row function; use `|> suppress_small_cells(by: [...], min: k)` instead",
                            );
                        }
                        "shuffle" => {
                            diag = diag.with_hint(
                                "`shuffle` is a table pipeline verb, not a row function; use `|> shuffle(seed: 42)` instead",
                            );
                        }
                        _ => {}
                    }
                }
                self.diags.push(diag);
                (ExecRowExpr::Lit(Literal::Unit), Ty::Unit, TagSet::empty())
            }
            ExprKind::IfInline {
                cond,
                then_expr,
                else_ifs,
                else_expr,
            } => self.check_row_if_inline(
                cond,
                then_expr,
                else_ifs,
                else_expr,
                cols,
                outer_env,
                expected,
                allow_dot_self,
            ),
            _ => {
                self.diags.push(
                    Diagnostic::error(
                        DiagCode::TypeError,
                        "unsupported construct in pure row expression",
                    )
                    .with_span(expr.span),
                );
                (ExecRowExpr::Lit(Literal::Unit), Ty::Unit, TagSet::empty())
            }
        }
    }

    #[expect(
        clippy::too_many_arguments,
        reason = "iterative row-level inline if handles arbitrarily long else-if chains in O(1) stack"
    )]
    fn check_row_if_inline(
        &mut self,
        cond: &Expr,
        then_expr: &Expr,
        else_ifs: &[(Expr, Expr)],
        else_expr: &Expr,
        cols: &[ColSpec],
        outer_env: &HashMap<Ident, VarBinding>,
        expected: Option<&Ty>,
        allow_dot_self: bool,
    ) -> (ExecRowExpr, Ty, TagSet) {
        let mut arms: Vec<(ExecRowExpr, ExecRowExpr, Ty)> = Vec::with_capacity(1 + else_ifs.len());
        let (c0, _, ct0) =
            self.check_row_expr(cond, cols, outer_env, Some(&Ty::Bool), allow_dot_self);
        let (t0, tty, tt0) =
            self.check_row_expr(then_expr, cols, outer_env, expected, allow_dot_self);
        let mut tags = ct0.union(&tt0);
        arms.push((c0, t0, tty.clone()));
        let hint = expected.or_else(|| {
            if matches!(&tty, Ty::Option(inner) if **inner == Ty::Unit) {
                None
            } else {
                Some(&tty)
            }
        });
        for (ec, et) in else_ifs {
            let (cre, _, ctags) =
                self.check_row_expr(ec, cols, outer_env, Some(&Ty::Bool), allow_dot_self);
            let (tre, tre_ty, ttags) =
                self.check_row_expr(et, cols, outer_env, hint, allow_dot_self);
            tags = tags.union(&ctags).union(&ttags);
            arms.push((cre, tre, tre_ty));
        }
        let (mut acc, else_ty, etags) =
            self.check_row_expr(else_expr, cols, outer_env, hint, allow_dot_self);
        tags = tags.union(&etags);

        let any_opt = matches!(tty, Ty::Option(_))
            || arms.iter().any(|(_, _, t)| matches!(t, Ty::Option(_)))
            || matches!(else_ty, Ty::Option(_));
        let concrete_non_opt = std::iter::once(&tty)
            .chain(arms.iter().map(|(_, _, t)| t))
            .chain(std::iter::once(&else_ty))
            .find_map(|t| match t {
                Ty::Option(inner) if **inner != Ty::Unit => Some((**inner).clone()),
                Ty::Option(_) => None,
                other => Some(other.clone()),
            });

        let wrap_opt_branch = |br: ExecRowExpr, br_ty: &Ty, inner: &Ty| -> ExecRowExpr {
            if *br_ty == *inner {
                ExecRowExpr::Prim {
                    op: ExecPrimOp::Core(PrimOp::SomeVal(inner.clone())),
                    args: vec![br],
                }
            } else if matches!(br, ExecRowExpr::Lit(Literal::NoneLit(_))) {
                ExecRowExpr::Lit(Literal::NoneLit(inner.clone()))
            } else {
                br
            }
        };

        let out_ty = if any_opt && let Some(ref inner) = concrete_non_opt {
            acc = wrap_opt_branch(acc, &else_ty, inner);
            while let Some((cre, tre, tre_ty)) = arms.pop() {
                let wrapped = wrap_opt_branch(tre, &tre_ty, inner);
                acc = ExecRowExpr::IfE {
                    cond: Box::new(cre),
                    then_br: Box::new(wrapped),
                    else_br: Box::new(acc),
                };
            }
            Ty::Option(Box::new(inner.clone()))
        } else {
            while let Some((cre, tre, _)) = arms.pop() {
                acc = ExecRowExpr::IfE {
                    cond: Box::new(cre),
                    then_br: Box::new(tre),
                    else_br: Box::new(acc),
                };
            }
            tty
        };
        (acc, out_ty, tags)
    }

    // -----------------------------------------------------------------------
    // Subtyping, Boundary Coercion & Privacy Enforcement
    // -----------------------------------------------------------------------

    fn coerce_expr(
        &mut self,
        expr: ExecExpr,
        actual: &LTy,
        expected: &LTy,
        span: Span,
        context: &str,
    ) -> ExecExpr {
        // Table structural subtyping & boundary coercion:
        // - Width subtyping: `src_tt` may carry extra columns; every column required by `dst_tt`
        //   must be present with compatible scalar type (`T <: T?`, literal `Decimal -> Float`)
        //   and `sc.tags ⊆ dc.tags`.
        // - Row-tag privacy: `src_tt.row_tags ⊆ dst_tt.total_tags()`.
        if let (Ty::Table(src_tt), Ty::Table(dst_tt)) = (&actual.ty, &expected.ty) {
            let allowed_row_tags = dst_tt.total_tags();
            if !src_tt.row_tags.is_subset(&allowed_row_tags) {
                self.diags.push(
                    Diagnostic::error(
                        DiagCode::PrivacyError,
                        format!(
                            "{context}: table carries row sensitivity tags {:?} not permitted by expected schema {:?}",
                            src_tt.row_tags.elems(),
                            allowed_row_tags.elems()
                        ),
                    )
                    .with_span(span),
                );
            }
            let is_empty_lit =
                matches!(expr, ExecExpr::TableLit { ref rows, .. } if rows.is_empty());
            let exact_layout_match = src_tt.cols.len() == dst_tt.cols.len()
                && src_tt
                    .cols
                    .iter()
                    .zip(&dst_tt.cols)
                    .all(|(s, d)| s.name == d.name && s.ty == d.ty);
            let mut needs_coerce = !exact_layout_match;
            for dc in &dst_tt.cols {
                let Some(sc) = src_tt.find_col(&dc.name) else {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::TypeError,
                            format!("{context}: table is missing required column `{}`", dc.name),
                        )
                        .with_span(span),
                    );
                    continue;
                };
                let ty_compat = scalar_ty_coercible(&sc.ty, &dc.ty) || is_empty_lit;
                if !ty_compat {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::TypeError,
                            format!("{context}: incompatible type for column `{}`", dc.name),
                        )
                        .with_span(span),
                    );
                }
                if !sc.tags.is_subset(&dc.tags) {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::PrivacyError,
                            format!(
                                "{context}: column `{}` carries sensitivity tags {:?} not allowed by target {:?}",
                                dc.name,
                                sc.tags.elems(),
                                dc.tags.elems()
                            ),
                        )
                        .with_span(span),
                    );
                }
            }
            if needs_coerce {
                return ExecExpr::Prim {
                    op: ExecPrimOp::TableCoerce(dst_tt.clone()),
                    args: vec![expr],
                };
            }
            needs_coerce = false;
            let _ = needs_coerce;
            return expr;
        }

        // Scalar/general `T <: Option(T)` promotion.
        if let Ty::Option(inner) = &expected.ty
            && **inner == actual.ty
        {
            return ExecExpr::Prim {
                op: ExecPrimOp::Core(PrimOp::SomeVal(actual.ty.clone())),
                args: vec![expr],
            };
        }

        // Strictly enforce sensitivity tag non-laundering on all scalar/record boundaries:
        // tagged values may never flow into an untagged or under-tagged target.
        if !actual.tags.is_subset(&expected.tags) {
            self.diags.push(
                Diagnostic::error(
                    DiagCode::PrivacyError,
                    format!(
                        "{context}: sensitivity tags {:?} exceed target {:?}",
                        actual.tags.elems(),
                        expected.tags.elems()
                    ),
                )
                .with_span(span),
            );
        }

        expr
    }

    fn require_spec_scope(&mut self, scope: LocalScopeKind, span: Span, what: &str) {
        if !matches!(scope, LocalScopeKind::Spec) {
            self.diags.push(
                Diagnostic::error(
                    DiagCode::CapabilityError,
                    format!("{what} is a test double and may only be used inside `test`, `examples`, or `promise` blocks"),
                )
                .with_span(span),
            );
        }
    }
}

#[derive(Clone, Copy)]
enum BlockTail<'a> {
    Value,
    StateTuple(&'a [Ident]),
    ValueAndState(&'a [Ident]),
}

fn build_var_tuple(names: &[Ident]) -> ExecExpr {
    ExecExpr::Tuple(names.iter().map(|n| ExecExpr::Var(n.clone())).collect())
}

fn build_val_and_var_tuple(val: ExecExpr, names: &[Ident]) -> ExecExpr {
    let mut elems = Vec::with_capacity(1 + names.len());
    elems.push(val);
    elems.extend(names.iter().map(|n| ExecExpr::Var(n.clone())));
    ExecExpr::Tuple(elems)
}

fn wrap_guard_expr(jmp: ExecExpr, guard: Option<ExecExpr>) -> ExecExpr {
    match guard {
        Some(gex) => ExecExpr::IfE {
            cond: Box::new(gex),
            then_br: Box::new(jmp),
            else_br: Box::new(ExecExpr::Lit(Literal::Unit)),
        },
        None => jmp,
    }
}

fn merge_loop_mut_vars(
    working: &mut HashMap<Ident, VarBinding>,
    body: &HashMap<Ident, VarBinding>,
    state_names: &[Ident],
) -> bool {
    let mut changed = false;
    for name in state_names {
        if let (Some(wb), Some(bb)) = (working.get_mut(name), body.get(name)) {
            let merged_tags = wb.lty.tags.union(&bb.lty.tags);
            if is_unresolved_list(&wb.lty.ty) && !is_unresolved_list(&bb.lty.ty) {
                wb.lty = LTy::new(bb.lty.ty.clone(), merged_tags);
                changed = true;
            } else if merged_tags != wb.lty.tags {
                wb.lty.tags = merged_tags;
                changed = true;
            }
        }
    }
    changed
}

fn commit_loop_mut_vars(
    outer: &mut HashMap<Ident, VarBinding>,
    working: &HashMap<Ident, VarBinding>,
    state_names: &[Ident],
) -> Vec<(Ident, LTy)> {
    let mut state_vars = Vec::with_capacity(state_names.len());
    for name in state_names {
        if let (Some(ob), Some(wb)) = (outer.get_mut(name), working.get(name)) {
            ob.lty = wb.lty.clone();
            state_vars.push((name.clone(), ob.lty.clone()));
        }
    }
    state_vars
}

fn merge_branch_mut_vars(
    outer: &mut HashMap<Ident, VarBinding>,
    written: &[Ident],
    branch_envs: &[HashMap<Ident, VarBinding>],
    branch_pc: &TagSet,
) {
    for name in written {
        let Some(ob) = outer.get_mut(name) else {
            continue;
        };
        let mut merged_tags = ob.lty.tags.union(branch_pc);
        let mut refined_ty: Option<Ty> = None;
        for benv in branch_envs {
            if let Some(bb) = benv.get(name) {
                merged_tags = merged_tags.union(&bb.lty.tags);
                if is_unresolved_list(&ob.lty.ty)
                    && !is_unresolved_list(&bb.lty.ty)
                    && refined_ty.is_none()
                {
                    refined_ty = Some(bb.lty.ty.clone());
                }
            }
        }
        if let Some(rt) = refined_ty {
            ob.lty = LTy::new(rt, merged_tags);
        } else {
            ob.lty.tags = merged_tags;
        }
    }
}

fn collect_mutated_outer_vars_if(
    then_body: &[Stmt],
    else_ifs: &[ast::ElseIfBranch],
    else_body: Option<&ast::ElseBranch>,
    env: &HashMap<Ident, VarBinding>,
) -> Vec<Ident> {
    let mut work: Vec<&[Stmt]> = Vec::new();
    work.push(then_body);
    for ei in else_ifs {
        work.push(&ei.body);
    }
    if let Some(eb) = else_body {
        work.push(&eb.body);
    }
    collect_mutated_outer_vars_work(work, env)
}

fn collect_mutated_outer_vars_case(
    lines: &[ast::CaseLine],
    env: &HashMap<Ident, VarBinding>,
) -> Vec<Ident> {
    let mut work: Vec<&[Stmt]> = Vec::new();
    for line in lines {
        if let ast::CaseLine::Stmt(st) = line {
            work.push(std::slice::from_ref(st));
        }
    }
    collect_mutated_outer_vars_work(work, env)
}

fn collect_mutated_outer_vars_work(
    mut stmt_slices: Vec<&[Stmt]>,
    env: &HashMap<Ident, VarBinding>,
) -> Vec<Ident> {
    let mut found: HashSet<Ident> = HashSet::new();
    let mut expr_stack: Vec<&Expr> = Vec::new();

    while let Some(stmts) = stmt_slices.pop() {
        for st in stmts {
            match &st.kind {
                StmtKind::Assign { lhs, rhs } => {
                    record_assign_lhs(lhs, env, &mut found);
                    expr_stack.push(rhs);
                }
                StmtKind::Var { value, .. } => expr_stack.push(value),
                StmtKind::Expr(e) | StmtKind::Assert(e) => expr_stack.push(e),
                StmtKind::Return { value, guard } => {
                    if let Some(v) = value {
                        expr_stack.push(v);
                    }
                    if let Some(g) = guard {
                        expr_stack.push(g);
                    }
                }
                StmtKind::Break { guard } | StmtKind::Continue { guard } => {
                    if let Some(g) = guard {
                        expr_stack.push(g);
                    }
                }
                StmtKind::Stop(Some(e)) => expr_stack.push(e),
                StmtKind::Stop(None) => {}
                StmtKind::For { iter, body, .. } => {
                    expr_stack.push(iter);
                    stmt_slices.push(body);
                }
                StmtKind::While { cond, body } => {
                    expr_stack.push(cond);
                    stmt_slices.push(body);
                }
            }
        }
        while let Some(ex) = expr_stack.pop() {
            match &ex.kind {
                ExprKind::IfBlock {
                    then_body,
                    else_ifs,
                    else_body,
                    ..
                } => {
                    stmt_slices.push(then_body);
                    for ei in else_ifs {
                        stmt_slices.push(&ei.body);
                    }
                    if let Some(eb) = else_body {
                        stmt_slices.push(&eb.body);
                    }
                }
                ExprKind::Case { lines, .. } => {
                    for line in lines {
                        if let ast::CaseLine::Stmt(st) = line {
                            stmt_slices.push(std::slice::from_ref(st));
                        }
                    }
                }
                _ => {}
            }
        }
    }

    let mut out: Vec<Ident> = found.into_iter().collect();
    out.sort();
    out
}

fn record_assign_lhs(lhs: &Expr, env: &HashMap<Ident, VarBinding>, found: &mut HashSet<Ident>) {
    match &lhs.kind {
        ExprKind::Ident(name) => {
            if env.get(name).is_some_and(|b| b.mutable) {
                found.insert(name.clone());
            }
        }
        ExprKind::Tuple(elems) => {
            for el in elems {
                record_assign_lhs(el, env, found);
            }
        }
        _ => {}
    }
}

fn taint_return_with_pc(mut ret_lty: LTy, arg_tags: &TagSet, pc: &TagSet) -> LTy {
    let extra = arg_tags.union(pc);
    if extra.is_empty() {
        return ret_lty;
    }
    if let Ty::Table(ref mut tt) = ret_lty.ty {
        tt.row_tags = tt.row_tags.union(pc);
        tt.order_tags = tt.order_tags.union(pc);
        ret_lty.tags = ret_lty.tags.union(pc);
    } else {
        ret_lty.tags = ret_lty.tags.union(&extra);
    }
    ret_lty
}

fn block_ends_diverging(stmts: &[Stmt]) -> bool {
    stmts.last().is_some_and(|s| {
        matches!(
            s.kind,
            StmtKind::Return { guard: None, .. } | StmtKind::Stop(_)
        )
    })
}

fn compute_merged_var_ltys(
    outer: &HashMap<Ident, VarBinding>,
    state_vars: &[Ident],
    branch_envs: &[HashMap<Ident, VarBinding>],
    branch_pc: &TagSet,
) -> Vec<LTy> {
    state_vars
        .iter()
        .map(|name| {
            let mut lty = outer
                .get(name)
                .map_or_else(|| LTy::public(Ty::Unit), |b| b.lty.clone());
            lty.tags = lty.tags.union(branch_pc);
            for benv in branch_envs {
                if let Some(bb) = benv.get(name) {
                    let merged_tags = lty.tags.union(&bb.lty.tags);
                    if is_unresolved_list(&lty.ty) && !is_unresolved_list(&bb.lty.ty) {
                        lty = LTy::new(bb.lty.ty.clone(), merged_tags);
                    } else {
                        lty.tags = merged_tags;
                    }
                }
            }
            lty
        })
        .collect()
}

/// Iteratively check whether `expr` contains any `ExecExpr::Jump` node.
fn expr_has_any_jump(expr: &ExecExpr) -> bool {
    let mut stack = vec![expr];
    while let Some(cur) = stack.pop() {
        match cur {
            ExecExpr::Jump { .. } => return true,
            ExecExpr::LetE { bound, body, .. }
            | ExecExpr::Join {
                rhs: bound, body, ..
            } => {
                stack.push(bound);
                stack.push(body);
            }
            ExecExpr::IfE {
                cond,
                then_br,
                else_br,
            } => {
                stack.push(cond);
                stack.push(then_br);
                stack.push(else_br);
            }
            ExecExpr::CaseE { scrut, arms } => {
                stack.push(scrut);
                for a in arms {
                    stack.push(&a.body);
                }
            }
            ExecExpr::ForLoop {
                iter_expr,
                body,
                after,
                ..
            } => {
                stack.push(iter_expr);
                stack.push(body);
                stack.push(after);
            }
            ExecExpr::WhileLoop {
                cond, body, after, ..
            } => {
                stack.push(cond);
                stack.push(body);
                stack.push(after);
            }
            ExecExpr::App { fn_expr, args } => {
                stack.push(fn_expr);
                stack.extend(args.iter());
            }
            ExecExpr::Call { args, .. }
            | ExecExpr::Tuple(args)
            | ExecExpr::Ctor { args, .. }
            | ExecExpr::Prim { args, .. }
            | ExecExpr::Host { args, .. } => stack.extend(args.iter()),
            ExecExpr::Proj { tup: e, .. }
            | ExecExpr::Assert { cond: e, .. }
            | ExecExpr::Fail(e) => stack.push(e),
            ExecExpr::Stop {
                detail: Some(e), ..
            } => stack.push(e),
            _ => {}
        }
    }
    false
}

/// Iteratively rewrite all non-diverging tail leaves of `expr` into `Jump(cont_lbl, [leaf])`
/// so conditional early exits lower into strict tail-position Core IR `Join` continuations.
fn rewrite_tail_to_jump(expr: &mut ExecExpr, cont_lbl: &str) {
    let mut stack: Vec<&mut ExecExpr> = vec![expr];
    while let Some(cur) = stack.pop() {
        match cur {
            ExecExpr::Jump { .. } | ExecExpr::Stop { .. } | ExecExpr::Fail(_) => {}
            ExecExpr::IfE {
                then_br, else_br, ..
            } => {
                stack.push(then_br.as_mut());
                stack.push(else_br.as_mut());
            }
            ExecExpr::CaseE { arms, .. } => {
                for a in arms {
                    stack.push(&mut a.body);
                }
            }
            ExecExpr::LetE { body, .. } => {
                stack.push(body.as_mut());
            }
            ExecExpr::Join { rhs, body, .. } => {
                stack.push(rhs.as_mut());
                stack.push(body.as_mut());
            }
            ExecExpr::ForLoop { after, .. } | ExecExpr::WhileLoop { after, .. } => {
                stack.push(after.as_mut());
            }
            other => {
                let leaf = std::mem::replace(other, ExecExpr::Lit(Literal::Unit));
                *other = ExecExpr::Jump {
                    label: cont_lbl.to_string(),
                    args: vec![leaf],
                };
            }
        }
    }
}

/// Iteratively collect outer mutable `var` names referenced or assigned inside a lambda body.
fn collect_captured_mut_vars_lambda(
    body: &ast::LambdaBody,
    env: &HashMap<Ident, VarBinding>,
    shadowed: &HashSet<Ident>,
) -> Vec<Ident> {
    let mut found: HashSet<Ident> = HashSet::new();
    let mut expr_stack: Vec<&Expr> = Vec::new();
    let mut stmt_slices: Vec<&[Stmt]> = Vec::new();
    match body {
        ast::LambdaBody::Expr(e) => expr_stack.push(e.as_ref()),
        ast::LambdaBody::Block(stmts) => stmt_slices.push(stmts.as_slice()),
    }

    loop {
        while let Some(stmts) = stmt_slices.pop() {
            for st in stmts {
                match &st.kind {
                    StmtKind::Var { value, .. } => expr_stack.push(value),
                    StmtKind::Assign { lhs, rhs } => {
                        expr_stack.push(lhs);
                        expr_stack.push(rhs);
                    }
                    StmtKind::Assert(e) | StmtKind::Expr(e) => expr_stack.push(e),
                    StmtKind::Return { value, guard } => {
                        if let Some(v) = value {
                            expr_stack.push(v);
                        }
                        if let Some(g) = guard {
                            expr_stack.push(g);
                        }
                    }
                    StmtKind::Break { guard } | StmtKind::Continue { guard } => {
                        if let Some(g) = guard {
                            expr_stack.push(g);
                        }
                    }
                    StmtKind::Stop(Some(e)) => expr_stack.push(e),
                    StmtKind::Stop(None) => {}
                    StmtKind::For { iter, body, .. } => {
                        expr_stack.push(iter);
                        stmt_slices.push(body);
                    }
                    StmtKind::While { cond, body } => {
                        expr_stack.push(cond);
                        stmt_slices.push(body);
                    }
                }
            }
        }
        let Some(ex) = expr_stack.pop() else {
            break;
        };
        match &ex.kind {
            ExprKind::Ident(name) => {
                if !shadowed.contains(name) && env.get(name).is_some_and(|b| b.mutable) {
                    found.insert(name.clone());
                }
            }
            ExprKind::Paren(e) | ExprKind::Unary { expr: e, .. } => expr_stack.push(e),
            ExprKind::Binary { lhs, rhs, .. } => {
                expr_stack.push(lhs);
                expr_stack.push(rhs);
            }
            ExprKind::Field { receiver, .. } => expr_stack.push(receiver),
            ExprKind::Index { target, index } => {
                expr_stack.push(target);
                expr_stack.push(index);
            }
            ExprKind::Tuple(xs) | ExprKind::List(xs) => expr_stack.extend(xs.iter()),
            ExprKind::Map(pairs) => {
                for (k, v) in pairs {
                    expr_stack.push(k);
                    expr_stack.push(v);
                }
            }
            ExprKind::InterpText { parts, .. } => {
                for p in parts {
                    if let ast::InterpPart::Expr(e) = p {
                        expr_stack.push(e);
                    }
                }
            }
            ExprKind::Call { callee, args } => {
                expr_stack.push(callee);
                for a in args {
                    match a {
                        CallArg::Positional(e) | CallArg::Named { value: e, .. } => {
                            expr_stack.push(e);
                        }
                    }
                }
            }
            ExprKind::IfInline {
                cond,
                then_expr,
                else_ifs,
                else_expr,
            } => {
                expr_stack.push(cond);
                expr_stack.push(then_expr);
                for (c, t) in else_ifs {
                    expr_stack.push(c);
                    expr_stack.push(t);
                }
                expr_stack.push(else_expr);
            }
            ExprKind::IfBlock {
                cond,
                then_body,
                else_ifs,
                else_body,
            } => {
                expr_stack.push(cond);
                stmt_slices.push(then_body);
                for ei in else_ifs {
                    expr_stack.push(&ei.cond);
                    stmt_slices.push(&ei.body);
                }
                if let Some(eb) = else_body {
                    stmt_slices.push(&eb.body);
                }
            }
            ExprKind::Case { scrut, lines } => {
                expr_stack.push(scrut);
                for line in lines {
                    match line {
                        ast::CaseLine::ArmHeader { .. } => {}
                        ast::CaseLine::ArmInline { expr, .. } => expr_stack.push(expr),
                        ast::CaseLine::Stmt(st) => stmt_slices.push(std::slice::from_ref(st)),
                    }
                }
            }
            ExprKind::Lambda { body: inner, .. } => match inner {
                ast::LambdaBody::Expr(e) => expr_stack.push(e),
                ast::LambdaBody::Block(ss) => stmt_slices.push(ss),
            },
            ExprKind::TableLit { rows, .. } => {
                for r in rows {
                    expr_stack.extend(r.iter());
                }
            }
            _ => {}
        }
    }

    let mut out: Vec<Ident> = found.into_iter().collect();
    out.sort();
    out
}

enum BlockStep {
    Bind(Ident, LTy, ExecExpr),
    Effect(LTy, ExecExpr),
    Final(ExecExpr),
    Loop(Box<LoopStep>),
}

enum LoopStep {
    For {
        item_var: Ident,
        iter_expr: ExecExpr,
        state_vars: Vec<(Ident, LTy)>,
        body: ExecExpr,
    },
    While {
        cond: ExecExpr,
        state_vars: Vec<(Ident, LTy)>,
        body: ExecExpr,
    },
}

fn expr_jumps_to(expr: &ExecExpr, label: &str) -> bool {
    let mut stack = vec![expr];
    while let Some(cur) = stack.pop() {
        match cur {
            ExecExpr::Jump { label: l, args } => {
                if l == label {
                    return true;
                }
                stack.extend(args.iter());
            }
            ExecExpr::LetE { bound, body, .. }
            | ExecExpr::Join {
                rhs: bound, body, ..
            } => {
                stack.push(bound);
                stack.push(body);
            }
            ExecExpr::IfE {
                cond,
                then_br,
                else_br,
            } => {
                stack.push(cond);
                stack.push(then_br);
                stack.push(else_br);
            }
            ExecExpr::CaseE { scrut, arms } => {
                stack.push(scrut);
                for a in arms {
                    stack.push(&a.body);
                }
            }
            ExecExpr::ForLoop {
                iter_expr,
                body,
                after,
                ..
            } => {
                stack.push(iter_expr);
                stack.push(body);
                stack.push(after);
            }
            ExecExpr::WhileLoop {
                cond, body, after, ..
            } => {
                stack.push(cond);
                stack.push(body);
                stack.push(after);
            }
            ExecExpr::App { fn_expr, args } => {
                stack.push(fn_expr);
                stack.extend(args.iter());
            }
            ExecExpr::Call { args, .. }
            | ExecExpr::Tuple(args)
            | ExecExpr::Ctor { args, .. }
            | ExecExpr::Prim { args, .. }
            | ExecExpr::Host { args, .. } => {
                stack.extend(args.iter());
            }
            ExecExpr::Proj { tup: e, .. }
            | ExecExpr::Assert { cond: e, .. }
            | ExecExpr::Fail(e) => stack.push(e),
            ExecExpr::Stop {
                detail: Some(e), ..
            } => stack.push(e),
            _ => {}
        }
    }
    false
}

fn scalar_ty_coercible(src: &ScalarTy, dst: &ScalarTy) -> bool {
    if src == dst {
        return true;
    }
    match (src, dst) {
        (ScalarTy::Option(s), ScalarTy::Option(_)) if matches!(s.as_ref(), ScalarTy::Unit) => true,
        (ScalarTy::Option(s), ScalarTy::Option(d)) => scalar_ty_coercible(s, d),
        (s, ScalarTy::Option(d)) => scalar_ty_coercible(s, d),
        (ScalarTy::Int, ScalarTy::Decimal | ScalarTy::Float)
        | (ScalarTy::Decimal, ScalarTy::Float) => true,
        _ => false,
    }
}

fn expr_to_plan(expr: ExecExpr) -> ExecPlan {
    expr.into_plan()
}

fn upsert_col(cols: &mut Vec<ColSpec>, spec: ColSpec) {
    if let Some(existing) = cols.iter_mut().find(|c| c.name == spec.name) {
        *existing = spec;
    } else {
        cols.push(spec);
    }
}

fn is_quarantine_bad_row_table(tt: &TableTy) -> bool {
    tt.cols.len() == 5
        && tt.cols[0].name == "line"
        && tt.cols[0].ty == ScalarTy::Int
        && tt.cols[1].name == "column"
        && tt.cols[1].ty == ScalarTy::Text
        && tt.cols[2].name == "error_kind"
        && tt.cols[2].ty == ScalarTy::Text
        && tt.cols[3].name == "raw_value"
        && tt.cols[3].ty == ScalarTy::Text
        && tt.cols[4].name == "raw_line"
        && tt.cols[4].ty == ScalarTy::Text
}

fn for_target_binds(target: &ast::ForTarget, ident: &str) -> bool {
    match target {
        ast::ForTarget::Name(n) => n.name == ident,
        ast::ForTarget::Wildcard(_) => false,
        ast::ForTarget::Tuple(parts, _) => parts.iter().any(|p| for_target_binds(p, ident)),
    }
}

fn assign_lhs_binds(lhs: &Expr, ident: &str) -> bool {
    match &lhs.kind {
        ExprKind::Ident(n) => n == ident,
        ExprKind::Tuple(parts) => parts.iter().any(|p| assign_lhs_binds(p, ident)),
        _ => false,
    }
}

fn stmts_reference_ident(stmts: &[&Stmt], ident: &str) -> bool {
    for st in stmts {
        match &st.kind {
            StmtKind::Var { name, value, .. } => {
                if expr_references_ident(value, ident) {
                    return true;
                }
                if name.name == ident {
                    return false;
                }
            }
            StmtKind::Assign { lhs, rhs } => {
                if expr_references_ident(rhs, ident) {
                    return true;
                }
                if assign_lhs_binds(lhs, ident) {
                    return false;
                }
            }
            StmtKind::Assert(e) | StmtKind::Expr(e) => {
                if expr_references_ident(e, ident) {
                    return true;
                }
            }
            StmtKind::Return { value, guard } => {
                if value
                    .as_ref()
                    .is_some_and(|e| expr_references_ident(e, ident))
                    || guard
                        .as_ref()
                        .is_some_and(|e| expr_references_ident(e, ident))
                {
                    return true;
                }
            }
            StmtKind::Break { guard } | StmtKind::Continue { guard } => {
                if guard
                    .as_ref()
                    .is_some_and(|e| expr_references_ident(e, ident))
                {
                    return true;
                }
            }
            StmtKind::Stop(opt) => {
                if opt
                    .as_ref()
                    .is_some_and(|e| expr_references_ident(e, ident))
                {
                    return true;
                }
            }
            StmtKind::For { target, iter, body } => {
                if expr_references_ident(iter, ident) {
                    return true;
                }
                if !for_target_binds(target, ident) && stmt_slice_references_ident(body, ident) {
                    return true;
                }
            }
            StmtKind::While { cond, body } => {
                if expr_references_ident(cond, ident) || stmt_slice_references_ident(body, ident) {
                    return true;
                }
            }
        }
    }
    false
}

fn stmt_slice_references_ident(stmts: &[Stmt], ident: &str) -> bool {
    let refs: Vec<&Stmt> = stmts.iter().collect();
    stmts_reference_ident(&refs, ident)
}

fn expr_references_ident(expr: &Expr, ident: &str) -> bool {
    match &expr.kind {
        ExprKind::Ident(n) => n == ident,
        ExprKind::Int(_)
        | ExprKind::Decimal(_)
        | ExprKind::Date(_)
        | ExprKind::Timestamp(_)
        | ExprKind::Text { .. }
        | ExprKind::Atom(_)
        | ExprKind::Bool(_)
        | ExprKind::None
        | ExprKind::CapName(_)
        | ExprKind::Underscore
        | ExprKind::DotField(_)
        | ExprKind::DotSelf => false,
        ExprKind::InterpText { parts, .. } => parts.iter().any(|p| match p {
            ast::InterpPart::Literal { .. } => false,
            ast::InterpPart::Expr(e) => expr_references_ident(e, ident),
        }),
        ExprKind::Paren(inner)
        | ExprKind::Unary { expr: inner, .. }
        | ExprKind::Field {
            receiver: inner, ..
        } => expr_references_ident(inner, ident),
        ExprKind::Binary { lhs, rhs, .. }
        | ExprKind::Index {
            target: lhs,
            index: rhs,
        } => expr_references_ident(lhs, ident) || expr_references_ident(rhs, ident),
        ExprKind::Tuple(xs) | ExprKind::List(xs) => {
            xs.iter().any(|x| expr_references_ident(x, ident))
        }
        ExprKind::Map(pairs) => pairs
            .iter()
            .any(|(k, v)| expr_references_ident(k, ident) || expr_references_ident(v, ident)),
        ExprKind::Call { callee, args } => {
            expr_references_ident(callee, ident)
                || args.iter().any(|a| match a {
                    CallArg::Positional(e) | CallArg::Named { value: e, .. } => {
                        expr_references_ident(e, ident)
                    }
                })
        }
        ExprKind::IfInline {
            cond,
            then_expr,
            else_ifs,
            else_expr,
        } => {
            expr_references_ident(cond, ident)
                || expr_references_ident(then_expr, ident)
                || else_ifs.iter().any(|(c, t)| {
                    expr_references_ident(c, ident) || expr_references_ident(t, ident)
                })
                || expr_references_ident(else_expr, ident)
        }
        ExprKind::IfBlock {
            cond,
            then_body,
            else_ifs,
            else_body,
        } => {
            expr_references_ident(cond, ident)
                || stmt_slice_references_ident(then_body, ident)
                || else_ifs.iter().any(|b| {
                    expr_references_ident(&b.cond, ident)
                        || stmt_slice_references_ident(&b.body, ident)
                })
                || else_body
                    .as_ref()
                    .is_some_and(|b| stmt_slice_references_ident(&b.body, ident))
        }
        ExprKind::Case { scrut, lines } => {
            if expr_references_ident(scrut, ident) {
                return true;
            }
            let mut arm_stmts: Vec<&Stmt> = Vec::new();
            for line in lines {
                match line {
                    ast::CaseLine::ArmHeader { .. } => {
                        if stmts_reference_ident(&arm_stmts, ident) {
                            return true;
                        }
                        arm_stmts.clear();
                    }
                    ast::CaseLine::ArmInline { expr, .. } => {
                        if stmts_reference_ident(&arm_stmts, ident) {
                            return true;
                        }
                        arm_stmts.clear();
                        if expr_references_ident(expr, ident) {
                            return true;
                        }
                    }
                    ast::CaseLine::Stmt(st) => arm_stmts.push(st),
                }
            }
            stmts_reference_ident(&arm_stmts, ident)
        }
        ExprKind::Lambda { params, body } => {
            let shadowed = params.iter().any(|p| match p {
                ast::LambdaParam::Name(n) => n.name == ident,
                ast::LambdaParam::Wildcard(_) => false,
            });
            if shadowed {
                return false;
            }
            match body {
                ast::LambdaBody::Expr(e) => expr_references_ident(e, ident),
                ast::LambdaBody::Block(stmts) => stmt_slice_references_ident(stmts, ident),
            }
        }
        ExprKind::TableLit { rows, .. } => rows
            .iter()
            .any(|row| row.iter().any(|c| expr_references_ident(c, ident))),
    }
}

fn is_capability_ty(ty: &Ty) -> bool {
    matches!(
        ty,
        Ty::Args
            | Ty::Clock
            | Ty::Console(_)
            | Ty::ReadFiles
            | Ty::WriteFiles { .. }
            | Ty::ReadDB(_)
            | Ty::WriteTable { .. }
            | Ty::RawReadDB(_)
            | Ty::HttpsAllow { .. }
            | Ty::Secret(_)
            | Ty::Declassify(_)
    )
}

fn is_unresolved_list(ty: &Ty) -> bool {
    matches!(
        ty,
        Ty::List(el) if matches!(&el.ty, Ty::Data(n) if n == TY_UNRESOLVED_LIST_ELEM)
    )
}

fn is_numeric_lit(expr: &Expr) -> bool {
    match &expr.kind {
        ExprKind::Int(_) | ExprKind::Decimal(_) => true,
        ExprKind::Unary {
            op: UnaryOp::Neg,
            expr: inner,
        } => is_numeric_lit(inner),
        _ => false,
    }
}

fn eval_const_duration_micros(expr: &Expr) -> Option<i64> {
    if let ExprKind::Field { receiver, member } = &expr.kind
        && let ExprKind::Int(raw) = &receiver.kind
    {
        let n: i64 = raw.replace('_', "").parse().ok()?;
        let mult = match member.name.as_str() {
            "seconds" => MICROS_PER_SECOND,
            "minutes" => MICROS_PER_MINUTE,
            "hours" => MICROS_PER_HOUR,
            "days" => MICROS_PER_DAY,
            _ => return None,
        };
        return n.checked_mul(mult);
    }
    None
}

fn row_property(re: ExecRowExpr, ty: &Ty, prop: &str) -> Option<(ExecRowExpr, Ty)> {
    if *ty == Ty::Int {
        let mult = match prop {
            "seconds" => Some(MICROS_PER_SECOND),
            "minutes" => Some(MICROS_PER_MINUTE),
            "hours" => Some(MICROS_PER_HOUR),
            "days" => Some(MICROS_PER_DAY),
            _ => None,
        };
        if let Some(m) = mult {
            return Some((
                ExecRowExpr::Prim {
                    op: ExecPrimOp::MakeDuration,
                    args: vec![re, ExecRowExpr::Lit(Literal::int(m))],
                },
                Ty::Duration,
            ));
        }
    }
    if let (Ty::Text, Some((op, out_ty))) = (ty, text_prop_op(prop)) {
        return Some((ExecRowExpr::Prim { op, args: vec![re] }, out_ty));
    }
    if let (Ty::Date, Some((op, out_ty))) = (ty, date_prop_op(prop)) {
        return Some((ExecRowExpr::Prim { op, args: vec![re] }, out_ty));
    }
    if let Some((op, out_ty)) = numeric_prop_op(ty, prop) {
        return Some((ExecRowExpr::Prim { op, args: vec![re] }, out_ty));
    }
    match (ty, prop) {
        (Ty::Option(_), "some?") => Some((
            ExecRowExpr::Prim {
                op: ExecPrimOp::Core(PrimOp::IsSome),
                args: vec![re],
            },
            Ty::Bool,
        )),
        (Ty::Option(_), "none?") => Some((
            ExecRowExpr::Prim {
                op: ExecPrimOp::Core(PrimOp::IsNone),
                args: vec![re],
            },
            Ty::Bool,
        )),
        _ => None,
    }
}

fn named_dot_col(args: &[CallArg], key: &str) -> Option<Ident> {
    args.iter().find_map(|a| match a {
        CallArg::Named { name, value, .. } if name.name == key => {
            if let ExprKind::DotField(m) = &value.kind {
                Some(m.name.clone())
            } else {
                None
            }
        }
        _ => None,
    })
}

fn named_cap_arg(args: &[CallArg], key: &str) -> Option<Ident> {
    args.iter().find_map(|a| match a {
        CallArg::Named { name, value, .. } if name.name == key => {
            if let ExprKind::CapName(s) = &value.kind {
                Some(s.clone())
            } else {
                None
            }
        }
        _ => None,
    })
}

fn named_expr_arg<'a>(args: &'a [CallArg], key: &str) -> Option<&'a Expr> {
    args.iter().find_map(|a| match a {
        CallArg::Named { name, value, .. } if name.name == key => Some(value),
        _ => None,
    })
}

fn extract_cap_path(expr: &Expr) -> Option<String> {
    match &expr.kind {
        ExprKind::CapName(name) => Some(name.clone()),
        ExprKind::Field { receiver, member } => {
            if member
                .name
                .chars()
                .next()
                .is_some_and(|c| c.is_ascii_uppercase())
            {
                let prefix = extract_cap_path(receiver)?;
                Some(format!("{prefix}.{}", member.name))
            } else {
                None
            }
        }
        _ => None,
    }
}

fn stats_col_tags(tlty: &LTy, cols: &[&str]) -> TagSet {
    let mut tags = tlty.tags.clone();
    if let Ty::Table(tt) = &tlty.ty {
        tags = tags.union(&tt.row_tags).union(&tt.order_tags);
        for c in cols {
            if let Some(cs) = tt.find_col(c) {
                tags = tags.union(&cs.tags);
            }
        }
    }
    tags
}

fn unify_pivot_scalar(a: &ScalarTy, b: &ScalarTy) -> Option<ScalarTy> {
    if a == b {
        return Some(a.clone());
    }
    match (a, b) {
        (ScalarTy::Option(ia), ScalarTy::Option(ib)) => {
            unify_pivot_scalar(ia, ib).map(|u| ScalarTy::Option(Box::new(u)))
        }
        (ScalarTy::Option(ia), other) => {
            unify_pivot_scalar(ia, other).map(|u| ScalarTy::Option(Box::new(u)))
        }
        (other, ScalarTy::Option(ib)) => {
            unify_pivot_scalar(other, ib).map(|u| ScalarTy::Option(Box::new(u)))
        }
        (ScalarTy::Int, ScalarTy::Decimal) | (ScalarTy::Decimal, ScalarTy::Int) => {
            Some(ScalarTy::Decimal)
        }
        (ScalarTy::Int | ScalarTy::Decimal, ScalarTy::Float)
        | (ScalarTy::Float, ScalarTy::Int | ScalarTy::Decimal) => Some(ScalarTy::Float),
        _ => None,
    }
}

fn sanitize_ident(s: &str) -> String {
    s.chars()
        .map(|c| if c.is_ascii_alphanumeric() { c } else { '_' })
        .take(48)
        .collect()
}

/// Rewrite standalone `.` and bare table-aggregate calls (`sum(.col)`, `mean(.col)`, `count()`)
/// inside a `promise` expression to refer to `self_var`.
fn rewrite_promise_self(expr: &Expr, self_var: &str, is_table: bool) -> Expr {
    let sp = expr.span;
    match &expr.kind {
        ExprKind::DotSelf => Expr {
            kind: ExprKind::Ident(self_var.to_string()),
            span: sp,
        },
        ExprKind::Call { callee, args } if is_table => {
            if let ExprKind::Ident(fname) = &callee.kind
                && matches!(fname.as_str(), "sum" | "mean" | "stddev" | "count")
            {
                return Expr {
                    kind: ExprKind::Call {
                        callee: Box::new(Expr {
                            kind: ExprKind::Field {
                                receiver: Box::new(Expr {
                                    kind: ExprKind::Ident(self_var.to_string()),
                                    span: sp,
                                }),
                                member: ast::SpannedName::new(fname.clone(), callee.span),
                            },
                            span: callee.span,
                        }),
                        args: args.clone(),
                    },
                    span: sp,
                };
            }
            Expr {
                kind: ExprKind::Call {
                    callee: Box::new(rewrite_promise_self(callee, self_var, is_table)),
                    args: args
                        .iter()
                        .map(|a| match a {
                            CallArg::Positional(e) => {
                                CallArg::Positional(rewrite_promise_self(e, self_var, is_table))
                            }
                            CallArg::Named { name, value, span } => CallArg::Named {
                                name: name.clone(),
                                value: rewrite_promise_self(value, self_var, is_table),
                                span: *span,
                            },
                        })
                        .collect(),
                },
                span: sp,
            }
        }
        ExprKind::Binary { op, lhs, rhs } => Expr {
            kind: ExprKind::Binary {
                op: *op,
                lhs: Box::new(rewrite_promise_self(lhs, self_var, is_table)),
                rhs: Box::new(rewrite_promise_self(rhs, self_var, is_table)),
            },
            span: sp,
        },
        ExprKind::Unary { op, expr: inner } => Expr {
            kind: ExprKind::Unary {
                op: *op,
                expr: Box::new(rewrite_promise_self(inner, self_var, is_table)),
            },
            span: sp,
        },
        ExprKind::Paren(inner) => Expr {
            kind: ExprKind::Paren(Box::new(rewrite_promise_self(inner, self_var, is_table))),
            span: sp,
        },
        _ => expr.clone(),
    }
}

fn numeric_prop_op(ty: &Ty, prop: &str) -> Option<(ExecPrimOp, Ty)> {
    match (ty, prop) {
        (Ty::Int, "to_decimal") => Some((ExecPrimOp::Core(PrimOp::IntToDec), Ty::Decimal)),
        (Ty::Int, "to_float") => Some((ExecPrimOp::IntToFloat, Ty::Float)),
        (Ty::Int, "abs") => Some((ExecPrimOp::AbsInt, Ty::Int)),
        (Ty::Float, "abs") => Some((ExecPrimOp::AbsFloat, Ty::Float)),
        (Ty::Float, "ceil") => Some((ExecPrimOp::CeilFloat, Ty::Int)),
        (Ty::Float, "floor") => Some((ExecPrimOp::FloorFloat, Ty::Int)),
        (Ty::Float, "trunc" | "to_int") => Some((ExecPrimOp::TruncFloat, Ty::Int)),
        (Ty::Decimal, "abs") => Some((ExecPrimOp::AbsDecimal, Ty::Decimal)),
        (Ty::Decimal, "to_float") => Some((ExecPrimOp::DecToFloat, Ty::Float)),
        (Ty::Decimal, "ceil") => Some((ExecPrimOp::CeilDecimal, Ty::Int)),
        (Ty::Decimal, "floor") => Some((ExecPrimOp::FloorDecimal, Ty::Int)),
        (Ty::Decimal, "trunc" | "to_int") => Some((ExecPrimOp::TruncDecimal, Ty::Int)),
        _ => None,
    }
}

const AGG_FN_NAMES: &[&str] = &[
    "count",
    "count_if",
    "count_distinct",
    "sum",
    "mean",
    "avg",
    "median",
    "stddev",
    "variance",
    "percentile",
    "min",
    "max",
    "first",
    "last",
];

fn is_direct_agg_call(expr: &Expr) -> bool {
    matches!(
        &expr.kind,
        ExprKind::Call { callee, .. }
            if matches!(&callee.kind, ExprKind::Ident(n) if AGG_FN_NAMES.contains(&n.as_str()))
    )
}

impl Checker<'_> {
    fn parse_round_mode_atom(&mut self, value: &Expr) -> bool {
        match &value.kind {
            ExprKind::Atom(a) if a == "half_away" => false,
            ExprKind::Atom(a) if a == "half_even" => true,
            ExprKind::Atom(other) => {
                self.diags.push(
                    Diagnostic::error(
                        DiagCode::TypeError,
                        format!(
                            "unknown rounding mode `:{other}` (expected `:half_away` or `:half_even`)"
                        ),
                    )
                    .with_span(value.span),
                );
                false
            }
            _ => {
                self.diags.push(
                    Diagnostic::error(
                        DiagCode::TypeError,
                        "`mode:` must be `:half_away` or `:half_even`",
                    )
                    .with_span(value.span),
                );
                false
            }
        }
    }

    fn parse_round_args<'a>(
        &mut self,
        args: &'a [CallArg],
        call_span: Span,
    ) -> (Option<&'a Expr>, bool) {
        let mut places: Option<&'a Expr> = None;
        let mut half_even = false;
        let mut seen_mode = false;
        for arg in args {
            match arg {
                CallArg::Positional(e) => {
                    if places.is_some() {
                        self.diags.push(
                            Diagnostic::error(
                                DiagCode::TypeError,
                                "`.round` accepts at most 1 positional `Int` argument and optional `mode:`",
                            )
                            .with_span(e.span),
                        );
                    } else {
                        places = Some(e);
                    }
                }
                CallArg::Named { name, value, span } if name.name == "mode" => {
                    if seen_mode {
                        self.diags.push(
                            Diagnostic::error(DiagCode::TypeError, "duplicate `mode:` argument")
                                .with_span(*span),
                        );
                    }
                    seen_mode = true;
                    half_even = self.parse_round_mode_atom(value);
                }
                CallArg::Named { name, span, .. } => {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::TypeError,
                            format!("unexpected named argument `{}:` in `.round`", name.name),
                        )
                        .with_span(*span),
                    );
                }
            }
        }
        let _ = call_span;
        (places, half_even)
    }

    fn parse_round_to_args<'a>(
        &mut self,
        args: &'a [CallArg],
        call_span: Span,
    ) -> (Option<&'a Expr>, bool) {
        let mut step: Option<&'a Expr> = None;
        let mut half_even = false;
        let mut seen_mode = false;
        for arg in args {
            match arg {
                CallArg::Positional(e) => {
                    if step.is_some() {
                        self.diags.push(
                            Diagnostic::error(
                                DiagCode::TypeError,
                                "`Float.round_to` accepts 1 `step` argument and optional `mode:`",
                            )
                            .with_span(e.span),
                        );
                    } else {
                        step = Some(e);
                    }
                }
                CallArg::Named { name, value, span } if name.name == "step" => {
                    if step.is_some() {
                        self.diags.push(
                            Diagnostic::error(DiagCode::TypeError, "duplicate `step:` argument")
                                .with_span(*span),
                        );
                    } else {
                        step = Some(value);
                    }
                }
                CallArg::Named { name, value, span } if name.name == "mode" => {
                    if seen_mode {
                        self.diags.push(
                            Diagnostic::error(DiagCode::TypeError, "duplicate `mode:` argument")
                                .with_span(*span),
                        );
                    }
                    seen_mode = true;
                    half_even = self.parse_round_mode_atom(value);
                }
                CallArg::Named { name, span, .. } => {
                    self.diags.push(
                        Diagnostic::error(
                            DiagCode::TypeError,
                            format!("unexpected named argument `{}:` in `.round_to`", name.name),
                        )
                        .with_span(*span),
                    );
                }
            }
        }
        if step.is_none() {
            self.diags.push(
                Diagnostic::error(
                    DiagCode::TypeError,
                    "`Float.round_to` expects 1 `Float` argument (`step:`) and optional `mode:`",
                )
                .with_span(call_span),
            );
        }
        (step, half_even)
    }

    #[expect(
        clippy::too_many_arguments,
        reason = "recursively extracts nested aggregate calls inside summarize post-expressions"
    )]
    fn extract_post_agg_calls(
        &mut self,
        expr: &Expr,
        in_tt: &TableTy,
        base_ctx: &TagSet,
        env: &HashMap<Ident, VarBinding>,
        agg_items: &mut Vec<ExecAggItem>,
        distinct_key: &mut Option<Ident>,
        extracted_specs: &mut Vec<ColSpec>,
        post_drops: &mut Vec<Ident>,
    ) -> Expr {
        if is_direct_agg_call(expr) {
            let tmp_col = self.fresh("agg");
            if let Some((item, spec, dk)) =
                self.check_agg_call(&tmp_col, expr, in_tt, base_ctx, env)
            {
                if distinct_key.is_none() {
                    *distinct_key = dk;
                }
                agg_items.push(item);
                extracted_specs.push(spec);
                post_drops.push(tmp_col.clone());
            }
            return Expr {
                kind: ExprKind::DotField(ast::SpannedName::new(tmp_col, expr.span)),
                span: expr.span,
            };
        }
        let sp = expr.span;
        let kind = match &expr.kind {
            ExprKind::Call { callee, args } => ExprKind::Call {
                callee: Box::new(self.extract_post_agg_calls(
                    callee,
                    in_tt,
                    base_ctx,
                    env,
                    agg_items,
                    distinct_key,
                    extracted_specs,
                    post_drops,
                )),
                args: args
                    .iter()
                    .map(|a| match a {
                        CallArg::Positional(e) => CallArg::Positional(self.extract_post_agg_calls(
                            e,
                            in_tt,
                            base_ctx,
                            env,
                            agg_items,
                            distinct_key,
                            extracted_specs,
                            post_drops,
                        )),
                        CallArg::Named { name, value, span } => CallArg::Named {
                            name: name.clone(),
                            value: self.extract_post_agg_calls(
                                value,
                                in_tt,
                                base_ctx,
                                env,
                                agg_items,
                                distinct_key,
                                extracted_specs,
                                post_drops,
                            ),
                            span: *span,
                        },
                    })
                    .collect(),
            },
            ExprKind::Field { receiver, member } => ExprKind::Field {
                receiver: Box::new(self.extract_post_agg_calls(
                    receiver,
                    in_tt,
                    base_ctx,
                    env,
                    agg_items,
                    distinct_key,
                    extracted_specs,
                    post_drops,
                )),
                member: member.clone(),
            },
            ExprKind::Unary { op, expr: inner } => ExprKind::Unary {
                op: *op,
                expr: Box::new(self.extract_post_agg_calls(
                    inner,
                    in_tt,
                    base_ctx,
                    env,
                    agg_items,
                    distinct_key,
                    extracted_specs,
                    post_drops,
                )),
            },
            ExprKind::Binary { op, lhs, rhs } => ExprKind::Binary {
                op: *op,
                lhs: Box::new(self.extract_post_agg_calls(
                    lhs,
                    in_tt,
                    base_ctx,
                    env,
                    agg_items,
                    distinct_key,
                    extracted_specs,
                    post_drops,
                )),
                rhs: Box::new(self.extract_post_agg_calls(
                    rhs,
                    in_tt,
                    base_ctx,
                    env,
                    agg_items,
                    distinct_key,
                    extracted_specs,
                    post_drops,
                )),
            },
            ExprKind::Paren(inner) => ExprKind::Paren(Box::new(self.extract_post_agg_calls(
                inner,
                in_tt,
                base_ctx,
                env,
                agg_items,
                distinct_key,
                extracted_specs,
                post_drops,
            ))),
            ExprKind::Tuple(elems) => ExprKind::Tuple(
                elems
                    .iter()
                    .map(|e| {
                        self.extract_post_agg_calls(
                            e,
                            in_tt,
                            base_ctx,
                            env,
                            agg_items,
                            distinct_key,
                            extracted_specs,
                            post_drops,
                        )
                    })
                    .collect(),
            ),
            ExprKind::List(elems) => ExprKind::List(
                elems
                    .iter()
                    .map(|e| {
                        self.extract_post_agg_calls(
                            e,
                            in_tt,
                            base_ctx,
                            env,
                            agg_items,
                            distinct_key,
                            extracted_specs,
                            post_drops,
                        )
                    })
                    .collect(),
            ),
            ExprKind::Map(entries) => ExprKind::Map(
                entries
                    .iter()
                    .map(|(k, v)| {
                        (
                            self.extract_post_agg_calls(
                                k,
                                in_tt,
                                base_ctx,
                                env,
                                agg_items,
                                distinct_key,
                                extracted_specs,
                                post_drops,
                            ),
                            self.extract_post_agg_calls(
                                v,
                                in_tt,
                                base_ctx,
                                env,
                                agg_items,
                                distinct_key,
                                extracted_specs,
                                post_drops,
                            ),
                        )
                    })
                    .collect(),
            ),
            ExprKind::Index { target, index } => ExprKind::Index {
                target: Box::new(self.extract_post_agg_calls(
                    target,
                    in_tt,
                    base_ctx,
                    env,
                    agg_items,
                    distinct_key,
                    extracted_specs,
                    post_drops,
                )),
                index: Box::new(self.extract_post_agg_calls(
                    index,
                    in_tt,
                    base_ctx,
                    env,
                    agg_items,
                    distinct_key,
                    extracted_specs,
                    post_drops,
                )),
            },
            ExprKind::InterpText { parts, multiline } => ExprKind::InterpText {
                parts: parts
                    .iter()
                    .map(|p| match p {
                        ast::InterpPart::Literal { value, raw } => ast::InterpPart::Literal {
                            value: value.clone(),
                            raw: raw.clone(),
                        },
                        ast::InterpPart::Expr(ex) => {
                            ast::InterpPart::Expr(self.extract_post_agg_calls(
                                ex,
                                in_tt,
                                base_ctx,
                                env,
                                agg_items,
                                distinct_key,
                                extracted_specs,
                                post_drops,
                            ))
                        }
                    })
                    .collect(),
                multiline: *multiline,
            },
            ExprKind::IfInline {
                cond,
                then_expr,
                else_ifs,
                else_expr,
            } => ExprKind::IfInline {
                cond: Box::new(self.extract_post_agg_calls(
                    cond,
                    in_tt,
                    base_ctx,
                    env,
                    agg_items,
                    distinct_key,
                    extracted_specs,
                    post_drops,
                )),
                then_expr: Box::new(self.extract_post_agg_calls(
                    then_expr,
                    in_tt,
                    base_ctx,
                    env,
                    agg_items,
                    distinct_key,
                    extracted_specs,
                    post_drops,
                )),
                else_ifs: else_ifs
                    .iter()
                    .map(|(ec, et)| {
                        (
                            self.extract_post_agg_calls(
                                ec,
                                in_tt,
                                base_ctx,
                                env,
                                agg_items,
                                distinct_key,
                                extracted_specs,
                                post_drops,
                            ),
                            self.extract_post_agg_calls(
                                et,
                                in_tt,
                                base_ctx,
                                env,
                                agg_items,
                                distinct_key,
                                extracted_specs,
                                post_drops,
                            ),
                        )
                    })
                    .collect(),
                else_expr: Box::new(self.extract_post_agg_calls(
                    else_expr,
                    in_tt,
                    base_ctx,
                    env,
                    agg_items,
                    distinct_key,
                    extracted_specs,
                    post_drops,
                )),
            },
            ExprKind::Int(_)
            | ExprKind::Decimal(_)
            | ExprKind::Date(_)
            | ExprKind::Timestamp(_)
            | ExprKind::Text { .. }
            | ExprKind::Atom(_)
            | ExprKind::Bool(_)
            | ExprKind::None
            | ExprKind::Ident(_)
            | ExprKind::CapName(_)
            | ExprKind::Underscore
            | ExprKind::DotField(_)
            | ExprKind::DotSelf
            | ExprKind::IfBlock { .. }
            | ExprKind::Case { .. }
            | ExprKind::Lambda { .. }
            | ExprKind::TableLit { .. } => expr.kind.clone(),
        };
        Expr { kind, span: sp }
    }
}

fn date_prop_op(prop: &str) -> Option<(ExecPrimOp, Ty)> {
    match prop {
        "year" => Some((ExecPrimOp::DateYear, Ty::Int)),
        _ => None,
    }
}

fn text_prop_op(prop: &str) -> Option<(ExecPrimOp, Ty)> {
    match prop {
        "empty?" => Some((ExecPrimOp::Core(PrimOp::EmptyText), Ty::Bool)),
        "trim" => Some((ExecPrimOp::Core(PrimOp::TrimText), Ty::Text)),
        "ascii_lowercase" => Some((ExecPrimOp::Core(PrimOp::LowerAsciiText), Ty::Text)),
        "lower" => Some((ExecPrimOp::LowerText, Ty::Text)),
        "upper" => Some((ExecPrimOp::UpperText, Ty::Text)),
        "try_parse_date" => Some((ExecPrimOp::TryParseDate, Ty::Option(Box::new(Ty::Date)))),
        "try_parse_int" => Some((ExecPrimOp::TryParseInt, Ty::Option(Box::new(Ty::Int)))),
        "try_parse_decimal" => Some((
            ExecPrimOp::TryParseDecimal,
            Ty::Option(Box::new(Ty::Decimal)),
        )),
        "try_parse_float" => Some((ExecPrimOp::TryParseFloat, Ty::Option(Box::new(Ty::Float)))),
        _ => None,
    }
}

fn extract_one_arg<'a>(args: &'a [CallArg], key: &str) -> Option<&'a Expr> {
    if args.len() != 1 {
        return None;
    }
    match &args[0] {
        CallArg::Positional(e) => Some(e),
        CallArg::Named { name, value, .. } if name.name == key => Some(value),
        _ => None,
    }
}

fn extract_two_args<'a>(args: &'a [CallArg], k0: &str, k1: &str) -> Option<(&'a Expr, &'a Expr)> {
    if args.len() != 2 {
        return None;
    }
    match (&args[0], &args[1]) {
        (CallArg::Positional(a), CallArg::Positional(b)) => Some((a, b)),
        (
            CallArg::Named {
                name: n0,
                value: v0,
                ..
            },
            CallArg::Named {
                name: n1,
                value: v1,
                ..
            },
        ) => {
            if n0.name == k0 && n1.name == k1 {
                Some((v0, v1))
            } else if n0.name == k1 && n1.name == k0 {
                Some((v1, v0))
            } else {
                None
            }
        }
        (
            CallArg::Positional(a),
            CallArg::Named {
                name: n1, value: b, ..
            },
        ) if n1.name == k1 => Some((a, b)),
        _ => None,
    }
}

fn in_list_base_ty(ty: &Ty) -> Option<&Ty> {
    let base = match ty {
        Ty::Option(inner) => inner.as_ref(),
        other => other,
    };
    matches!(
        base,
        Ty::Text | Ty::Int | Ty::Decimal | Ty::Float | Ty::Date | Ty::Bool
    )
    .then_some(base)
}

fn clamp_op_for_ty(ty: &Ty) -> Option<ExecPrimOp> {
    match ty {
        Ty::Int => Some(ExecPrimOp::ClampInt),
        Ty::Float => Some(ExecPrimOp::ClampFloat),
        Ty::Decimal => Some(ExecPrimOp::ClampDecimal),
        _ => None,
    }
}
