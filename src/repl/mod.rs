//! Safe interactive REPL (`dana repl`) and `untyped` data explorer.
//!
//! Security & privacy invariants:
//! - Compiled under `#[forbid(unsafe_code)]` via `src/lib.rs` (pure line-buffered `BufRead`,
//!   zero `termios` FFI, zero external crates).
//! - **Read-only by default:** pre-binds `files: ReadFiles`, `console: Console`, and any
//!   `--db Name=URI` as `Name: ReadDB(Name)`. Never binds `WriteFiles`, `WriteTable`,
//!   `HttpsAllow`, `Secret`, `RawReadDB`, or `Declassify`.
//! - **Privacy-redacted by default:** sensitive scalars, composite values, tables (per-column
//!   AND `row_tags`), charts, reports, and profiles whose tags are not a subset of
//!   `--show-sensitive` automatically render as `[REDACTED:<sorted,tags>]`.
//! - **Policy ceiling:** if `dana.policy` sets `forbid repl_show_sensitive` and
//!   `--show-sensitive` is non-empty, [`ReplSession::new`] hard-fails immediately with
//!   [`DiagCode::PrivacyError`] (`E0202`).
//! - **Real compiler & VM:** every expression and binding runs through `parse_module`,
//!   `resolve_module_in_dir`, `check_resolved_with_lock`, `lower_program`, and
//!   `eval_exec_entry_vm` (2,048-row vectorized columnar VM + SQL pushdown).

use std::collections::HashMap;
use std::fmt::Write as _;
use std::io::{self, BufRead, Write};
use std::path::{Path, PathBuf};

use crate::base::{DiagCode, Diagnostic, FileId, SourceMap, render_diagnostic};
use crate::check::{check_resolved_with_lock, resolve_module_in_dir};
use crate::core::syntax::{Ident, LTy, Policy, ScalarTy, TableTy, TagSet, Ty};
use crate::db::SqlDialect;
use crate::db::schema_lock::SchemaLockFile;
use crate::formats::compress::strip_compression_ext;
use crate::formats::infer::{
    InferredSchema, default_schema_name_from_path, infer_schema_from_file, read_csv_file_untyped,
    read_jsonl_file_untyped,
};
use crate::formats::parquet::{infer_parquet_schema_from_file, read_parquet_file_untyped};
use crate::formats::time::{format_iso_date, format_iso_timestamp};
use crate::formats::xlsx::{infer_xlsx_schema_from_file, read_xlsx_file_untyped};
use crate::lower::lower_program;
use crate::oracle::value::{TableVal, Val, redact_tags, render_decimal, render_public_val};
use crate::plan::{bind_exec_plan_sources, exec_plan_db_names, explain_exec_plan_with_pushdown};
use crate::runtime::{EvalProgramResult, ExecExpr, ExecPlan, RunConfig, StructLayout};
use crate::stats::profile::{format_scalar_ty_name, render_profile_terminal};
use crate::syntax::{
    CallArg, Expr, ExprKind, FragmentItem, Stmt, StmtKind, TokenKind, TopItem, lex, parse_fragment,
    parse_module,
};
use crate::viz::terminal::render_chart_terminal;
use crate::vm::{VmConfig, eval_exec_entry_vm};

const REPL_ENTRY_FN: &str = "__repl_entry";
const MAX_TABLE_PREVIEW_ROWS: usize = 50;

/// Configuration for a [`ReplSession`].
#[derive(Clone, Debug)]
pub struct ReplConfig {
    pub policy: Option<Policy>,
    /// Ordered `(DbName, URI)` bindings supplied via `--db Name=URI`.
    pub db_bindings: Vec<(String, String)>,
    /// SQLite attachments supplied via `--attach [DB:]schema=PATH`.
    pub sqlite_attachments: Vec<(Option<String>, String, String)>,
    pub schema_lock: Option<SchemaLockFile>,
    /// Sensitivity tags explicitly allowed for local interactive display (`--show-sensitive`).
    pub allowed_show_tags: TagSet,
    pub work_dir: PathBuf,
    pub vm_cfg: VmConfig,
}

impl Default for ReplConfig {
    fn default() -> Self {
        Self {
            policy: None,
            db_bindings: Vec::new(),
            sqlite_attachments: Vec::new(),
            schema_lock: None,
            allowed_show_tags: TagSet::empty(),
            work_dir: std::env::current_dir().unwrap_or_else(|_| PathBuf::from(".")),
            vm_cfg: VmConfig::default(),
        }
    }
}

/// Output produced by evaluating one REPL input or meta-command.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ReplOutput {
    /// Expression or binding evaluated cleanly.
    Value {
        rendered: String,
        ty_desc: String,
        stdout: Vec<String>,
        stderr: Vec<String>,
    },
    /// Informational response from a declaration or meta-command (`:help`, `:type`, `:vars`, etc.).
    Info(String),
    /// Parse, type, privacy, policy, or runtime error (session state left unchanged).
    Error(String),
    /// User requested `:quit` / `:q`.
    Exit,
    /// Blank line or comment-only input.
    Empty,
}

#[derive(Clone, Debug)]
struct TopDeclEntry {
    kind: &'static str,
    name: String,
    source: String,
}

#[derive(Clone, Debug)]
struct UntypedBinding {
    param_name: String,
    schema_name: String,
    schema_src: String,
    table: TableVal,
}

/// Persistent safe interactive Dana REPL session.
#[derive(Debug)]
pub struct ReplSession {
    cfg: ReplConfig,
    uses: Vec<String>,
    top_decls: Vec<TopDeclEntry>,
    bindings: Vec<String>,
    var_types: Vec<(String, LTy)>,
    untyped_tables: Vec<UntypedBinding>,
    var_inferred_schemas: HashMap<String, InferredSchema>,
    next_untyped_id: usize,
}

impl ReplSession {
    /// Construct a new [`ReplSession`], enforcing `dana.policy`'s `forbid repl_show_sensitive`
    /// rule immediately before any code runs.
    ///
    /// # Errors
    /// Returns a [`Diagnostic`] with [`DiagCode::PrivacyError`] (`E0202`) if
    /// `cfg.allowed_show_tags` is non-empty and `cfg.policy` forbids `repl_show_sensitive`.
    pub fn new(cfg: ReplConfig) -> Result<Self, Diagnostic> {
        if !cfg.allowed_show_tags.is_empty()
            && cfg.policy.as_ref().is_some_and(|p| p.forbid_repl_sensitive)
        {
            return Err(Diagnostic::error(
                DiagCode::PrivacyError,
                format!(
                    "`dana.policy` forbids `--show-sensitive` in `dana repl` (requested tags: [{}])",
                    cfg.allowed_show_tags.elems().join(", ")
                ),
            )
            .with_hint(
                "omit `--show-sensitive` to run `dana repl` with automatic [REDACTED:<tags>] protection",
            ));
        }
        Ok(Self {
            cfg,
            uses: Vec::new(),
            top_decls: Vec::new(),
            bindings: Vec::new(),
            var_types: Vec::new(),
            untyped_tables: Vec::new(),
            var_inferred_schemas: HashMap::new(),
            next_untyped_id: 1,
        })
    }

    /// Return the sensitivity tags permitted for local interactive display in this session.
    #[must_use]
    pub const fn allowed_show_tags(&self) -> &TagSet {
        &self.cfg.allowed_show_tags
    }

    /// Reset all session definitions, variable bindings, and loaded `untyped` datasets.
    pub fn reset(&mut self) {
        self.uses.clear();
        self.top_decls.clear();
        self.bindings.clear();
        self.var_types.clear();
        self.untyped_tables.clear();
        self.var_inferred_schemas.clear();
        self.next_untyped_id = 1;
    }

    /// Determine whether `buf` is syntactically incomplete and requires additional input lines
    /// (open `... end` blocks, unclosed delimiters, unterminated triple-quoted string, or
    /// trailing `|>` pipeline operator).
    #[must_use]
    pub fn is_incomplete_input(buf: &str) -> bool {
        let trimmed = buf.trim();
        if trimmed.is_empty() || trimmed.starts_with(':') {
            return false;
        }
        let lexed = match lex(FileId(0), buf) {
            Ok(out) => out,
            Err(d) => {
                let msg = d.message().to_ascii_lowercase();
                return msg.contains("unterminated");
            }
        };
        let toks = &lexed.tokens;
        let mut paren_depth: i32 = 0;
        let mut bracket_depth: i32 = 0;
        let mut brace_depth: i32 = 0;
        let mut block_depth: i32 = 0;
        let mut last_sig: Option<&TokenKind> = None;

        for idx in 0..toks.len() {
            let kind = &toks[idx].kind;
            match kind {
                TokenKind::Newline | TokenKind::Eof => continue,
                TokenKind::LParen => paren_depth += 1,
                TokenKind::RParen => paren_depth -= 1,
                TokenKind::LBrack => bracket_depth += 1,
                TokenKind::RBrack => bracket_depth -= 1,
                TokenKind::LBrace => brace_depth += 1,
                TokenKind::RBrace => brace_depth -= 1,
                TokenKind::KwSchema
                | TokenKind::KwStruct
                | TokenKind::KwEnum
                | TokenKind::KwExamples
                | TokenKind::KwTest
                | TokenKind::KwFor
                | TokenKind::KwWhile
                | TokenKind::KwCase
                | TokenKind::KwTable => {
                    block_depth += 1;
                }
                TokenKind::KwFn => {
                    // Named `fn name(...)` opens a block; anonymous lambda `fn(...)` does not.
                    let next_sig = next_non_nl_token(toks, idx + 1);
                    if !matches!(next_sig, Some(TokenKind::LParen)) {
                        block_depth += 1;
                    }
                }
                TokenKind::KwIf => {
                    // `else if` does not open a new `end`; postfix guard (`return x if`,
                    // `break if`, `continue if`) does not; inline `if cond: a else: b` does not.
                    let is_else_if = matches!(last_sig, Some(TokenKind::KwElse));
                    let starts_stmt_or_expr = last_sig.is_none()
                        || matches!(
                            prev_raw_token(toks, idx),
                            None | Some(
                                TokenKind::Newline
                                    | TokenKind::Assign
                                    | TokenKind::LParen
                                    | TokenKind::Colon
                                    | TokenKind::Comma
                            )
                        );
                    let has_colon_same_line = line_has_colon(toks, idx + 1);
                    if !is_else_if && starts_stmt_or_expr && !has_colon_same_line {
                        block_depth += 1;
                    }
                }
                TokenKind::KwEnd => {
                    block_depth = (block_depth - 1).max(0);
                }
                _ => {}
            }
            last_sig = Some(kind);
        }

        paren_depth > 0
            || bracket_depth > 0
            || brace_depth > 0
            || block_depth > 0
            || matches!(last_sig, Some(TokenKind::Pipe))
    }

    /// Evaluate one complete REPL command, declaration, binding, or expression.
    pub fn eval_input(&mut self, raw: &str) -> ReplOutput {
        let trimmed = raw.trim();
        if trimmed.is_empty() || is_comment_only(trimmed) {
            return ReplOutput::Empty;
        }
        if trimmed.starts_with(':') {
            return self.handle_meta_command(trimmed);
        }

        // Inspect first token to separate top-level declarations from statements/expressions.
        let lexed = match lex(FileId(0), trimmed) {
            Ok(l) => l,
            Err(d) => {
                let mut sm = SourceMap::new();
                let _ = sm.add_file("<repl>".to_string(), trimmed.to_string());
                return ReplOutput::Error(render_diagnostic(&d, &sm));
            }
        };
        let mut sig_iter = lexed
            .tokens
            .iter()
            .filter(|t| !matches!(t.kind, TokenKind::Newline | TokenKind::Eof));
        let first = sig_iter.next().map(|t| &t.kind);
        let second = sig_iter.next().map(|t| &t.kind);

        match first {
            None => ReplOutput::Empty,
            Some(TokenKind::KwUse) => self.eval_use_decl(trimmed),
            Some(
                TokenKind::KwTag
                | TokenKind::KwSchema
                | TokenKind::KwStruct
                | TokenKind::KwEnum
                | TokenKind::KwConst,
            ) => self.eval_top_decl(trimmed),
            Some(TokenKind::KwFn) if !matches!(second, Some(TokenKind::LParen)) => {
                self.eval_top_decl(trimmed)
            }
            Some(TokenKind::KwModule) => ReplOutput::Error(
                "REPL inputs do not need a `module` header; enter declarations, bindings, or expressions directly.".to_string(),
            ),
            _ => self.eval_stmt_or_expr(trimmed),
        }
    }

    fn handle_meta_command(&mut self, line: &str) -> ReplOutput {
        let (cmd, arg) = match line.find(char::is_whitespace) {
            Some(pos) => (&line[..pos], line[pos..].trim()),
            None => (line, ""),
        };
        match cmd {
            ":help" | ":h" => ReplOutput::Info(self.render_help()),
            ":quit" | ":q" | ":exit" => ReplOutput::Exit,
            ":reset" => {
                self.reset();
                ReplOutput::Info("session reset".to_string())
            }
            ":vars" => ReplOutput::Info(self.render_vars()),
            ":type" => {
                if arg.is_empty() {
                    ReplOutput::Error("usage: :type <expr>".to_string())
                } else {
                    self.cmd_type(arg)
                }
            }
            ":profile" => {
                if arg.is_empty() {
                    ReplOutput::Error("usage: :profile <expr>".to_string())
                } else {
                    self.cmd_profile(arg)
                }
            }
            ":explain" => {
                if arg.is_empty() {
                    ReplOutput::Error("usage: :explain <expr>".to_string())
                } else {
                    self.cmd_explain(arg)
                }
            }
            ":infer-schema" => {
                if arg.is_empty() {
                    ReplOutput::Error("usage: :infer-schema <var_or_path>".to_string())
                } else {
                    self.cmd_infer_schema(arg)
                }
            }
            other => ReplOutput::Error(format!(
                "unknown REPL command `{other}` (type `:help` for available commands)"
            )),
        }
    }

    fn render_help(&self) -> String {
        let mut out = String::new();
        out.push_str("Dana Safe REPL (read-only, privacy-redacted by default)\n");
        out.push_str("Meta-commands:\n");
        out.push_str("  :help                       Show this help message\n");
        out.push_str(
            "  :type <expr>                Show inferred Dana type and sensitivity tags\n",
        );
        out.push_str("  :profile <expr>             Print privacy-redacted dataset profile\n");
        out.push_str(
            "  :explain <expr>             Show optimized plan, SQL pushdown & sensitivity provenance\n",
        );
        out.push_str(
            "  :infer-schema <var|path>    Print ready-to-paste `schema ... end` declaration\n",
        );
        out.push_str(
            "  :vars                       List pre-bound capabilities, definitions & variables\n",
        );
        out.push_str("  :reset                      Clear session definitions and variables\n");
        out.push_str("  :quit, :q                   Exit the REPL\n");
        out.push_str("Untyped exploration helpers (REPL-only):\n");
        out.push_str("  untyped.read_csv(\"path.csv\")\n");
        out.push_str("  untyped.read_jsonl(\"path.jsonl\")\n");
        out.push_str("  untyped.read_parquet(\"path.parquet\")\n");
        out.push_str("  untyped.read_xlsx(\"path.xlsx\", sheet: \"Sheet1\")\n");
        if self.cfg.allowed_show_tags.is_empty() {
            out.push_str("Privacy display: ALL sensitive tags redacted ([REDACTED:<tags>])\n");
        } else {
            let _ = writeln!(
                out,
                "Privacy display: showing [{}] locally (all other tags redacted)",
                self.cfg.allowed_show_tags.elems().join(", ")
            );
        }
        out.trim_end().to_string()
    }

    fn render_vars(&self) -> String {
        let mut out = String::new();
        out.push_str("Capabilities (read-only):\n");
        out.push_str("  files : ReadFiles\n");
        out.push_str("  console : Console\n");
        for (db_name, _) in &self.cfg.db_bindings {
            let _ = writeln!(out, "  {db_name} : ReadDB({db_name})");
        }
        if !self.top_decls.is_empty() {
            out.push_str("Definitions:\n");
            for d in &self.top_decls {
                let _ = writeln!(out, "  {} {}", d.kind, d.name);
            }
        }
        out.push_str("Variables:\n");
        if self.var_types.is_empty() {
            out.push_str("  (none)\n");
        } else {
            for (name, lty) in &self.var_types {
                let _ = writeln!(out, "  {name} : {}", format_lty_human(lty));
            }
        }
        out.trim_end().to_string()
    }

    fn eval_use_decl(&mut self, src: &str) -> ReplOutput {
        let mut next_uses = self.uses.clone();
        if !next_uses.iter().any(|u| u == src) {
            next_uses.push(src.to_string());
        }
        let module_src = self.build_module_source(
            &next_uses,
            &self.top_decls,
            &self.untyped_tables,
            &self.bindings,
            "Unit",
        );
        match self.compile_module(&module_src) {
            Ok(_) => {
                self.uses = next_uses;
                ReplOutput::Info(format!("imported `{src}`"))
            }
            Err(err) => ReplOutput::Error(err),
        }
    }

    fn eval_top_decl(&mut self, src: &str) -> ReplOutput {
        let mut sm = SourceMap::new();
        let fid = sm.add_file("<repl>".to_string(), format!("{src}\n"));
        let frag = match parse_fragment(fid, &format!("{src}\n")) {
            Ok(f) => f,
            Err(d) => return ReplOutput::Error(render_diagnostic(&d, &sm)),
        };
        let mut next_decls = self.top_decls.clone();
        let mut summary = Vec::new();
        for item in frag.items {
            let FragmentItem::Top(top) = item else {
                return ReplOutput::Error(
                    "mixed top-level declarations and statements are not supported in a single REPL turn".to_string(),
                );
            };
            let (kind, name) = match &top {
                TopItem::Tag(t) => ("tag", t.name.name.clone()),
                TopItem::Schema(s) => ("schema", s.name.name.clone()),
                TopItem::Struct(s) => ("struct", s.name.name.clone()),
                TopItem::Enum(e) => ("enum", e.name.name.clone()),
                TopItem::Const(c) => ("const", c.name.name.clone()),
                TopItem::Fn(f) => ("fn", f.name.name.clone()),
                TopItem::Test(t) => ("test", t.name.clone()),
            };
            // Replace any prior definition with the same kind+name so REPL users can refine items.
            next_decls.retain(|d| !(d.kind == kind && d.name == name));
            next_decls.push(TopDeclEntry {
                kind,
                name: name.clone(),
                source: src.to_string(),
            });
            summary.push(format!("defined {kind} {name}"));
        }
        if summary.is_empty() {
            return ReplOutput::Empty;
        }

        let module_src = self.build_module_source(
            &self.uses,
            &next_decls,
            &self.untyped_tables,
            &self.bindings,
            "Unit",
        );
        match self.compile_module(&module_src) {
            Ok(_) => {
                self.top_decls = next_decls;
                ReplOutput::Info(summary.join("\n"))
            }
            Err(err) => ReplOutput::Error(err),
        }
    }

    fn eval_stmt_or_expr(&mut self, src: &str) -> ReplOutput {
        let mut temp_untyped = Vec::new();
        let mut temp_next_id = self.next_untyped_id;
        let (rewritten_src, direct_untyped_binding) =
            match self.rewrite_untyped_calls(src, &mut temp_untyped, &mut temp_next_id) {
                Ok(pair) => pair,
                Err(msg) => return ReplOutput::Error(msg),
            };
        let db_rewritten = self.rewrite_db_cap_refs(&rewritten_src);

        // Parse fragment to detect variable binding(s) vs. bare expression/statement.
        let mut sm = SourceMap::new();
        let fid = sm.add_file("<repl>".to_string(), format!("{db_rewritten}\n"));
        let frag = match parse_fragment(fid, &format!("{db_rewritten}\n")) {
            Ok(f) => f,
            Err(d) => return ReplOutput::Error(render_diagnostic(&d, &sm)),
        };

        let mut bound_names: Vec<String> = Vec::new();
        let mut is_persistent_binding = false;
        if let [FragmentItem::Stmt(stmt)] = frag.items.as_slice() {
            match &stmt.kind {
                StmtKind::Var { name, .. } => {
                    bound_names.push(name.name.clone());
                    is_persistent_binding = true;
                }
                StmtKind::Assign { lhs, .. } => {
                    collect_lhs_bound_names(lhs, &mut bound_names);
                    is_persistent_binding = !bound_names.is_empty();
                }
                _ => {}
            }
        }

        let mut all_untyped = self.untyped_tables.clone();
        all_untyped.extend(temp_untyped.iter().cloned());

        let (tail_code, extra_bindings) = if is_persistent_binding {
            let ret_expr = if bound_names.len() == 1 {
                bound_names[0].clone()
            } else {
                format!("({})", bound_names.join(", "))
            };
            let mut next_b = self.bindings.clone();
            next_b.push(db_rewritten.clone());
            (ret_expr, next_b)
        } else {
            (db_rewritten.clone(), self.bindings.clone())
        };

        let module_src = self.build_module_source(
            &self.uses,
            &self.top_decls,
            &all_untyped,
            &extra_bindings,
            &tail_code,
        );
        let lowered = match self.compile_module(&module_src) {
            Ok(l) => l,
            Err(err) => return ReplOutput::Error(err),
        };

        let prebound: Vec<(Ident, Val)> = all_untyped
            .iter()
            .map(|u| (u.param_name.clone(), Val::Table(u.table.clone())))
            .collect();
        let run_cfg = self.make_run_config();
        match eval_exec_entry_vm(
            &lowered.exec,
            REPL_ENTRY_FN,
            &prebound,
            &run_cfg,
            &self.cfg.vm_cfg,
        ) {
            EvalProgramResult::Ok {
                val,
                ret_lty,
                stdout,
                stderr,
            } => {
                if is_persistent_binding {
                    self.next_untyped_id = temp_next_id;
                    self.untyped_tables.extend(temp_untyped);
                    self.bindings.push(db_rewritten);
                    if bound_names.len() == 1 {
                        self.record_var_type(bound_names[0].clone(), (*ret_lty).clone());
                        if let Some(inferred) = direct_untyped_binding {
                            let mut renamed = inferred;
                            renamed.name = ident_to_cap_schema_name(&bound_names[0]);
                            self.var_inferred_schemas
                                .insert(bound_names[0].clone(), renamed);
                        } else {
                            self.var_inferred_schemas.remove(&bound_names[0]);
                        }
                    } else if let Ty::Tuple(elem_ltys) = &ret_lty.ty {
                        for (name, elty) in bound_names.iter().zip(elem_ltys) {
                            let tagged = LTy::new(elty.ty.clone(), elty.tags.union(&ret_lty.tags));
                            self.record_var_type(name.clone(), tagged);
                            self.var_inferred_schemas.remove(name);
                        }
                    }
                }
                let ty_desc = format_lty_human(&ret_lty);
                let rendered = if matches!(val.as_ref(), Val::Unit)
                    && ret_lty.ty == Ty::Unit
                    && ret_lty.tags.is_empty()
                {
                    String::new()
                } else {
                    format_repl_value(
                        &val,
                        &ret_lty,
                        &self.cfg.allowed_show_tags,
                        &lowered.exec.struct_layouts,
                    )
                };
                ReplOutput::Value {
                    rendered,
                    ty_desc,
                    stdout,
                    stderr,
                }
            }
            EvalProgramResult::Stopped { bug, .. } => {
                ReplOutput::Error(format!("runtime stop ({:?}): {}", bug.kind, bug.message))
            }
            EvalProgramResult::Failed { message, .. } => {
                ReplOutput::Error(format!("runtime error: {message}"))
            }
        }
    }

    fn cmd_type(&self, expr_src: &str) -> ReplOutput {
        let mut temp_untyped = Vec::new();
        let mut temp_next_id = self.next_untyped_id;
        let (rewritten_src, _) =
            match self.rewrite_untyped_calls(expr_src, &mut temp_untyped, &mut temp_next_id) {
                Ok(pair) => pair,
                Err(msg) => return ReplOutput::Error(msg),
            };
        let db_rewritten = self.rewrite_db_cap_refs(&rewritten_src);
        let mut all_untyped = self.untyped_tables.clone();
        all_untyped.extend(temp_untyped);

        let module_src = self.build_module_source(
            &self.uses,
            &self.top_decls,
            &all_untyped,
            &self.bindings,
            &db_rewritten,
        );
        let lowered = match self.compile_module(&module_src) {
            Ok(l) => l,
            Err(err) => return ReplOutput::Error(err),
        };
        let Some(entry_fn) = lowered.exec.find_fun(REPL_ENTRY_FN) else {
            return ReplOutput::Error("internal error: missing REPL entry".to_string());
        };
        ReplOutput::Info(format_lty_human(&entry_fn.ret))
    }

    fn cmd_profile(&mut self, expr_src: &str) -> ReplOutput {
        let mut temp_untyped = Vec::new();
        let mut temp_next_id = self.next_untyped_id;
        let (rewritten_src, _) =
            match self.rewrite_untyped_calls(expr_src, &mut temp_untyped, &mut temp_next_id) {
                Ok(pair) => pair,
                Err(msg) => return ReplOutput::Error(msg),
            };
        let db_rewritten = self.rewrite_db_cap_refs(&rewritten_src);
        let mut all_untyped = self.untyped_tables.clone();
        all_untyped.extend(temp_untyped);

        let prof_tail = format!("({db_rewritten}).profile()");
        let module_src = self.build_module_source(
            &self.uses,
            &self.top_decls,
            &all_untyped,
            &self.bindings,
            &prof_tail,
        );
        let lowered = match self.compile_module(&module_src) {
            Ok(l) => l,
            Err(err) => return ReplOutput::Error(err),
        };
        let prebound: Vec<(Ident, Val)> = all_untyped
            .iter()
            .map(|u| (u.param_name.clone(), Val::Table(u.table.clone())))
            .collect();
        let run_cfg = self.make_run_config();
        match eval_exec_entry_vm(
            &lowered.exec,
            REPL_ENTRY_FN,
            &prebound,
            &run_cfg,
            &self.cfg.vm_cfg,
        ) {
            EvalProgramResult::Ok { val, ret_lty, .. } => ReplOutput::Info(format_repl_value(
                &val,
                &ret_lty,
                &self.cfg.allowed_show_tags,
                &lowered.exec.struct_layouts,
            )),
            EvalProgramResult::Stopped { bug, .. } => {
                ReplOutput::Error(format!("runtime stop ({:?}): {}", bug.kind, bug.message))
            }
            EvalProgramResult::Failed { message, .. } => {
                ReplOutput::Error(format!("runtime error: {message}"))
            }
        }
    }

    fn cmd_explain(&self, expr_src: &str) -> ReplOutput {
        let mut temp_untyped = Vec::new();
        let mut temp_next_id = self.next_untyped_id;
        let (rewritten_src, _) =
            match self.rewrite_untyped_calls(expr_src, &mut temp_untyped, &mut temp_next_id) {
                Ok(pair) => pair,
                Err(msg) => return ReplOutput::Error(msg),
            };
        let db_rewritten = self.rewrite_db_cap_refs(&rewritten_src);
        let mut all_untyped = self.untyped_tables.clone();
        all_untyped.extend(temp_untyped);

        let module_src = self.build_module_source(
            &self.uses,
            &self.top_decls,
            &all_untyped,
            &self.bindings,
            &db_rewritten,
        );
        let lowered = match self.compile_module(&module_src) {
            Ok(l) => l,
            Err(err) => return ReplOutput::Error(err),
        };
        let Some(entry_fn) = lowered.exec.find_fun(REPL_ENTRY_FN) else {
            return ReplOutput::Error("internal error: missing REPL entry".to_string());
        };

        // Collect all prior local `let` bindings so `:explain x` or `:explain x |> where(...)`
        // resolves `x` into its underlying relational plan (including DB pushdown sources!).
        let mut local_plans: HashMap<String, ExecPlan> = HashMap::new();
        let tail_expr = collect_let_plans_and_tail(&entry_fn.body, &mut local_plans);

        let mut target_plans: Vec<ExecPlan> = Vec::new();
        match tail_expr {
            ExecExpr::Rel(plan) => {
                target_plans.push(bind_exec_plan_sources(plan, &local_plans));
            }
            ExecExpr::Var(v) => {
                if let Some(p) = local_plans.get(v) {
                    target_plans.push(p.clone());
                }
            }
            other => {
                let mut found = Vec::new();
                collect_plans_in_expr(other, &mut found);
                for p in found {
                    target_plans.push(bind_exec_plan_sources(p, &local_plans));
                }
            }
        }

        if target_plans.is_empty() {
            return ReplOutput::Info(format!(
                "no relational plan in expression (inferred type: {})",
                format_lty_human(&entry_fn.ret)
            ));
        }

        let mut out = String::new();
        for (idx, plan) in target_plans.iter().enumerate() {
            let db_names = exec_plan_db_names(plan, &lowered.exec);
            let db_name = db_names.first().cloned().unwrap_or_default();
            let dialect = self.infer_dialect_for_db(&db_name);
            let _ = writeln!(out, "-- plan #{idx} (dialect: {dialect}) --");
            out.push_str(&explain_exec_plan_with_pushdown(
                plan,
                &lowered.exec,
                &db_name,
                dialect,
                self.cfg.schema_lock.as_ref(),
            ));
        }
        ReplOutput::Info(out.trim_end().to_string())
    }

    fn cmd_infer_schema(&self, raw_arg: &str) -> ReplOutput {
        let arg = raw_arg.trim();
        let unquoted = strip_quotes(arg);

        // 1. Bound `untyped` table variable in session?
        if let Some(inferred) = self.var_inferred_schemas.get(arg) {
            return ReplOutput::Info(inferred.render_dana().trim_end().to_string());
        }

        // 2. Bound typed `Table(...)` variable in session?
        if let Some((_, lty)) = self.var_types.iter().rev().find(|(n, _)| n == arg)
            && let Ty::Table(tt) = &lty.ty
        {
            return ReplOutput::Info(
                render_table_ty_as_schema(&ident_to_cap_schema_name(arg), tt)
                    .trim_end()
                    .to_string(),
            );
        }

        // 3. Data file path on disk (CSV, TSV, JSONL, Parquet, XLSX, including .gz/.zst).
        let path = self.resolve_data_path(unquoted);
        if !path.is_file() {
            return ReplOutput::Error(format!(
                "unknown session table `{arg}` and file `{}` not found",
                path.display()
            ));
        }
        let schema_name = default_schema_name_from_path(&path);
        let lower_inner = strip_compression_ext(&path.to_string_lossy()).to_ascii_lowercase();
        let res = if lower_inner.ends_with(".parquet") {
            infer_parquet_schema_from_file(&path, &schema_name)
        } else if lower_inner.ends_with(".xlsx") {
            infer_xlsx_schema_from_file(&path, None, &schema_name)
        } else {
            infer_schema_from_file(&path, &schema_name, None, 10_000)
        };
        match res {
            Ok(schema) => ReplOutput::Info(schema.render_dana().trim_end().to_string()),
            Err(msg) => ReplOutput::Error(format!("infer-schema failed: {msg}")),
        }
    }

    fn infer_dialect_for_db(&self, db_name: &str) -> SqlDialect {
        if !db_name.is_empty()
            && let Some((_, uri)) = self.cfg.db_bindings.iter().find(|(n, _)| n == db_name)
        {
            let lower = uri.to_ascii_lowercase();
            if lower.starts_with("sqlite:") || lower.ends_with(".sqlite") || lower.ends_with(".db")
            {
                return SqlDialect::Sqlite;
            }
            if lower.starts_with("postgres://") || lower.starts_with("postgresql://") {
                return SqlDialect::Postgres;
            }
        }
        if let Some(lock) = &self.cfg.schema_lock {
            if !db_name.is_empty()
                && let Some(db) = lock.find_db(db_name)
            {
                return db.dialect;
            }
            if let Some(first) = lock.dbs.first() {
                return first.dialect;
            }
        }
        if let Some((_, uri)) = self.cfg.db_bindings.first()
            && uri.to_ascii_lowercase().starts_with("sqlite:")
        {
            return SqlDialect::Sqlite;
        }
        SqlDialect::Postgres
    }

    fn record_var_type(&mut self, name: String, lty: LTy) {
        if let Some(slot) = self.var_types.iter_mut().find(|(n, _)| n == &name) {
            slot.1 = lty;
        } else {
            self.var_types.push((name, lty));
        }
    }

    fn resolve_data_path(&self, raw_path: &str) -> PathBuf {
        let p = Path::new(raw_path);
        if p.is_absolute() {
            p.to_path_buf()
        } else {
            self.cfg.work_dir.join(p)
        }
    }

    fn make_run_config(&self) -> RunConfig {
        let mut db_map = HashMap::new();
        for (n, uri) in &self.cfg.db_bindings {
            db_map.insert(n.clone(), uri.clone());
        }
        RunConfig {
            args: Vec::new(),
            allow_export: TagSet::empty(),
            work_dir: Some(self.cfg.work_dir.clone()),
            live_io: true,
            db_bindings: db_map,
            sqlite_attachments: self.cfg.sqlite_attachments.clone(),
            schema_lock: self.cfg.schema_lock.clone(),
            dry_run: true,
            ..RunConfig::default()
        }
    }

    fn build_module_source(
        &self,
        uses: &[String],
        top_decls: &[TopDeclEntry],
        untyped_tables: &[UntypedBinding],
        bindings: &[String],
        tail_code: &str,
    ) -> String {
        let mut out = String::new();
        out.push_str("module ReplSession\n");
        let has_stats = uses.iter().any(|u| u.trim() == "use Stats");
        if !has_stats {
            out.push_str("use Stats\n");
        }
        for u in uses {
            out.push_str(u.trim());
            out.push('\n');
        }
        out.push('\n');

        for u in untyped_tables {
            out.push_str(&u.schema_src);
            out.push('\n');
        }

        for d in top_decls {
            out.push_str(d.source.trim());
            out.push_str("\n\n");
        }

        // Pre-bind strictly read-only capabilities (`ReadFiles`, `Console`, `ReadDB(...)`)
        // plus pre-loaded `untyped` exploration tables.
        let mut params = vec![
            "files: ReadFiles".to_string(),
            "console: Console".to_string(),
        ];
        let mut used_param_names = vec!["files".to_string(), "console".to_string()];
        for (idx, (db_name, _)) in self.cfg.db_bindings.iter().enumerate() {
            let internal = format!("__repl_db_{idx}");
            params.push(format!("{internal}: ReadDB({db_name})"));
            used_param_names.push(internal);
            let lower = db_name.to_ascii_lowercase();
            if is_valid_lower_ident(&lower) && !used_param_names.contains(&lower) {
                params.push(format!("{lower}: ReadDB({db_name})"));
                used_param_names.push(lower);
            }
        }
        for u in untyped_tables {
            params.push(format!("{}: Table({})", u.param_name, u.schema_name));
        }

        let _ = writeln!(out, "fn {REPL_ENTRY_FN}({})", params.join(", "));
        for b in bindings {
            for line in b.lines() {
                out.push_str("  ");
                out.push_str(line);
                out.push('\n');
            }
        }
        for line in tail_code.lines() {
            out.push_str("  ");
            out.push_str(line);
            out.push('\n');
        }
        out.push_str("end\n");
        out
    }

    fn compile_module(&self, src: &str) -> Result<crate::lower::LoweredProgram, String> {
        let mut sm = SourceMap::new();
        let fid = sm.add_file("<repl>".to_string(), src.to_string());
        let parsed = parse_module(fid, src).map_err(|d| render_diagnostic(&d, &sm))?;
        let resolved = resolve_module_in_dir(
            fid,
            parsed,
            Some(&self.cfg.work_dir),
            self.cfg.policy.clone(),
            &mut sm,
        )
        .map_err(|ds| {
            ds.iter()
                .map(|d| render_diagnostic(d, &sm))
                .collect::<String>()
        })?;
        let checked = check_resolved_with_lock(&resolved, &sm, self.cfg.schema_lock.as_ref())
            .map_err(|ds| {
                ds.iter()
                    .map(|d| render_diagnostic(d, &sm))
                    .collect::<String>()
            })?;
        lower_program(checked).map_err(|d| render_diagnostic(&d, &sm))
    }

    /// Rewrite `CapName` references matching a `--db Name=URI` binding (e.g. `Seminary.table(...)`)
    /// into their internal `__repl_db_<idx>` parameter name, leaving string literals, comments,
    /// and capability type annotations (`ReadDB(Seminary)`) untouched.
    fn rewrite_db_cap_refs(&self, src: &str) -> String {
        if self.cfg.db_bindings.is_empty() {
            return src.to_string();
        }
        let Ok(lexed) = lex(FileId(0), src) else {
            return src.to_string();
        };
        let toks = &lexed.tokens;
        let mut replacements: Vec<(usize, usize, String)> = Vec::new();

        for idx in 0..toks.len() {
            let TokenKind::CapName(ref name) = toks[idx].kind else {
                continue;
            };
            let Some(db_idx) = self.cfg.db_bindings.iter().position(|(n, _)| n == name) else {
                continue;
            };
            // Do not rewrite if this CapName is a user-defined schema/struct/enum.
            if self.top_decls.iter().any(|d| d.name == *name) {
                continue;
            }
            // Only rewrite in expression position when followed by `.` (e.g. `Seminary.table(...)`),
            // or passed as a value when not preceded by `ReadDB(` / `WriteTable(` / `as:`.
            let next_is_dot = matches!(toks.get(idx + 1).map(|t| &t.kind), Some(TokenKind::Dot));
            let prev_is_type_ctx =
                idx >= 2 && matches!(toks[idx - 1].kind, TokenKind::LParen | TokenKind::Colon);
            if next_is_dot || !prev_is_type_ctx {
                replacements.push((
                    toks[idx].span.start as usize,
                    toks[idx].span.end as usize,
                    format!("__repl_db_{db_idx}"),
                ));
            }
        }
        if replacements.is_empty() {
            return src.to_string();
        }
        apply_span_replacements(src, &replacements)
    }

    /// Detect and load all `untyped.read_{csv,jsonl,parquet,xlsx}(...)` calls inside `src`,
    /// returning the rewritten source (with each call replaced by its pre-bound table parameter)
    /// and an optional [`InferredSchema`] when the whole statement is `var = untyped.read_*(...)`.
    fn rewrite_untyped_calls(
        &self,
        src: &str,
        out_untyped: &mut Vec<UntypedBinding>,
        next_id: &mut usize,
    ) -> Result<(String, Option<InferredSchema>), String> {
        if !src.contains("untyped") {
            return Ok((src.to_string(), None));
        }
        let mut sm = SourceMap::new();
        let fid = sm.add_file("<repl>".to_string(), format!("{src}\n"));
        let frag =
            parse_fragment(fid, &format!("{src}\n")).map_err(|d| render_diagnostic(&d, &sm))?;

        let mut calls: Vec<UntypedCallSite> = Vec::new();
        let mut direct_rhs_span: Option<(usize, usize)> = None;
        for item in &frag.items {
            if let FragmentItem::Stmt(st) = item {
                if let StmtKind::Assign { lhs, rhs } = &st.kind
                    && matches!(lhs.kind, ExprKind::Ident(_))
                {
                    direct_rhs_span = Some((rhs.span.start as usize, rhs.span.end as usize));
                } else if let StmtKind::Var { value, .. } = &st.kind {
                    direct_rhs_span = Some((value.span.start as usize, value.span.end as usize));
                }
                collect_untyped_calls_stmt(st, &mut calls)?;
            }
        }
        if calls.is_empty() {
            return Ok((src.to_string(), None));
        }

        let mut replacements: Vec<(usize, usize, String)> = Vec::with_capacity(calls.len());
        let mut direct_schema: Option<InferredSchema> = None;

        for call in calls {
            let resolved_path = self.resolve_data_path(&call.path);
            let id = *next_id;
            *next_id += 1;
            let schema_name = format!("ReplUntyped_{id}");
            let param_name = format!("__repl_u_{id}");

            let (inferred, table) = match call.method.as_str() {
                "read_csv" => read_csv_file_untyped(&resolved_path, &schema_name, None)?,
                "read_jsonl" => read_jsonl_file_untyped(&resolved_path, &schema_name)?,
                "read_parquet" => read_parquet_file_untyped(&resolved_path, &schema_name)?,
                "read_xlsx" => {
                    read_xlsx_file_untyped(&resolved_path, call.sheet.as_deref(), &schema_name)?
                }
                other => {
                    return Err(format!(
                        "unknown `untyped` method `{other}` (expected `read_csv`, `read_jsonl`, `read_parquet`, or `read_xlsx`)"
                    ));
                }
            };

            let schema_src = render_untyped_public_schema(&schema_name, &inferred);
            if direct_rhs_span == Some((call.start, call.end)) {
                direct_schema = Some(inferred.clone());
            }
            out_untyped.push(UntypedBinding {
                param_name: param_name.clone(),
                schema_name,
                schema_src,
                table,
            });
            replacements.push((call.start, call.end, param_name));
        }

        Ok((apply_span_replacements(src, &replacements), direct_schema))
    }
}

/// Run an interactive or piped line-buffered REPL loop against arbitrary `BufRead`/`Write` streams.
///
/// When `exit_on_error` is `true` (used by `--eval`), any error returns exit code `1`.
pub fn run_repl_reader<R: BufRead, W: Write, E: Write>(
    session: &mut ReplSession,
    mut reader: R,
    out: &mut W,
    err: &mut E,
    interactive: bool,
    exit_on_error: bool,
) -> i32 {
    if interactive {
        let _ = writeln!(
            out,
            "Dana v0.6 Safe REPL (read-only, sensitive values redacted by default). Type :help or :quit."
        );
    }
    let mut buf = String::new();
    let mut line = String::new();
    let mut had_error = false;

    loop {
        if interactive {
            let prompt = if buf.is_empty() { "dana> " } else { "....> " };
            let _ = write!(out, "{prompt}");
            let _ = out.flush();
        }
        line.clear();
        match reader.read_line(&mut line) {
            Ok(0) => {
                if !buf.trim().is_empty() {
                    let res = session.eval_input(&buf);
                    if emit_repl_output(&res, out, err) {
                        had_error = true;
                    }
                }
                break;
            }
            Ok(_) => {
                buf.push_str(&line);
                if ReplSession::is_incomplete_input(&buf) {
                    continue;
                }
                let input = std::mem::take(&mut buf);
                let res = session.eval_input(&input);
                match res {
                    ReplOutput::Exit => break,
                    other => {
                        if emit_repl_output(&other, out, err) {
                            had_error = true;
                            if exit_on_error {
                                return 1;
                            }
                        }
                    }
                }
            }
            Err(e) => {
                let _ = writeln!(err, "dana repl: read error: {e}");
                return 1;
            }
        }
    }

    if exit_on_error && had_error { 1 } else { 0 }
}

/// Run the line-buffered `dana repl` session on process `stdin`/`stdout`/`stderr`.
pub fn run_repl_stdio(session: &mut ReplSession, interactive: bool) -> i32 {
    let stdin = io::stdin();
    let stdout = io::stdout();
    let stderr = io::stderr();
    let mut out = stdout.lock();
    let mut err = stderr.lock();
    run_repl_reader(
        session,
        stdin.lock(),
        &mut out,
        &mut err,
        interactive,
        false,
    )
}

fn emit_repl_output<W: Write, E: Write>(res: &ReplOutput, out: &mut W, err: &mut E) -> bool {
    match res {
        ReplOutput::Empty | ReplOutput::Exit => false,
        ReplOutput::Info(msg) => {
            if !msg.is_empty() {
                let _ = writeln!(out, "{msg}");
            }
            false
        }
        ReplOutput::Error(msg) => {
            let _ = writeln!(err, "{}", msg.trim_end());
            true
        }
        ReplOutput::Value {
            rendered,
            stdout,
            stderr,
            ..
        } => {
            for s in stdout {
                let _ = writeln!(out, "{s}");
            }
            for s in stderr {
                let _ = writeln!(err, "{s}");
            }
            if !rendered.is_empty() {
                let _ = writeln!(out, "{rendered}");
            }
            false
        }
    }
}

// ===========================================================================
// Privacy-Safe REPL Value & Type Formatting
// ===========================================================================

/// Format a Dana [`LTy`] for `:type` and `:vars` output (never inspects runtime values).
#[must_use]
pub fn format_lty_human(lty: &LTy) -> String {
    let base = format_ty_human(&lty.ty);
    if lty.tags.is_empty() {
        base
    } else {
        format!("{base} [{}]", lty.tags.elems().join(", "))
    }
}

fn format_ty_human(ty: &Ty) -> String {
    match ty {
        Ty::Unit => "Unit".to_string(),
        Ty::Bool => "Bool".to_string(),
        Ty::Int => "Int".to_string(),
        Ty::Decimal => "Decimal".to_string(),
        Ty::Float => "Float".to_string(),
        Ty::Text => "Text".to_string(),
        Ty::Bytes => "Bytes".to_string(),
        Ty::Date => "Date".to_string(),
        Ty::Timestamp => "Timestamp".to_string(),
        Ty::Duration => "Duration".to_string(),
        Ty::LinearModel => "LinearModel".to_string(),
        Ty::StatTest => "StatTest".to_string(),
        Ty::Option(inner) => format!("{}?", format_ty_human(inner)),
        Ty::Result { ok_ty, err_ty } => {
            format!(
                "Result({}, {})",
                format_ty_human(ok_ty),
                format_ty_human(err_ty)
            )
        }
        Ty::Tuple(elems) => {
            let parts: Vec<String> = elems.iter().map(format_lty_human).collect();
            format!("({})", parts.join(", "))
        }
        Ty::List(elem) => format!("List({})", format_lty_human(elem)),
        Ty::Map { key, val } => {
            format!("Map({}, {})", format_lty_human(key), format_lty_human(val))
        }
        Ty::Data(name) => name.clone(),
        Ty::Table(tt) => {
            let cols: Vec<String> = tt
                .cols
                .iter()
                .map(|c| {
                    let t = format_scalar_ty_name(&c.ty);
                    if c.tags.is_empty() {
                        format!("{}: {t}", c.name)
                    } else {
                        format!("{}: {t} [{}]", c.name, c.tags.elems().join(", "))
                    }
                })
                .collect();
            let mut s = format!("Table({})", cols.join(", "));
            if !tt.row_tags.is_empty() {
                let _ = write!(s, " [row_tags: {}]", tt.row_tags.elems().join(", "));
            }
            if !tt.order_tags.is_empty() {
                let _ = write!(s, " [order_tags: {}]", tt.order_tags.elems().join(", "));
            }
            s
        }
        Ty::DynamicTable(tags) => fmt_tagged_cap("DynamicTable", tags),
        Ty::Chart(tags) => fmt_tagged_cap("Chart", tags),
        Ty::Report(tags) => fmt_tagged_cap("Report", tags),
        Ty::Profile(tags) => fmt_tagged_cap("Profile", tags),
        Ty::Fn { params, ret, .. } => {
            let ps: Vec<String> = params.iter().map(format_lty_human).collect();
            format!("fn({}) : {}", ps.join(", "), format_lty_human(ret))
        }
        Ty::Args => "Args".to_string(),
        Ty::Clock => "Clock".to_string(),
        Ty::Console(allows) => fmt_cap_allows("Console", allows),
        Ty::ReadFiles => "ReadFiles".to_string(),
        Ty::WriteFiles { root, allows } => {
            if allows.is_empty() {
                format!("WriteFiles(\"{root}\")")
            } else {
                format!(
                    "WriteFiles(\"{root}\", allows: [{}])",
                    allows.elems().join(", ")
                )
            }
        }
        Ty::ReadDB(db) => format!("ReadDB({db})"),
        Ty::RawReadDB(db) => format!("RawReadDB({db})"),
        Ty::WriteTable { db, table_name, .. } => format!("WriteTable({db}, \"{table_name}\")"),
        Ty::HttpsAllow { host, .. } => format!("HttpsAllow(\"{host}\")"),
        Ty::Secret(name) => format!("Secret(\"{name}\")"),
        Ty::Declassify(allows) => fmt_cap_allows("Declassify", allows),
    }
}

fn fmt_tagged_cap(name: &str, tags: &TagSet) -> String {
    if tags.is_empty() {
        name.to_string()
    } else {
        format!("{name} [{}]", tags.elems().join(", "))
    }
}

fn fmt_cap_allows(name: &str, allows: &TagSet) -> String {
    if allows.is_empty() {
        name.to_string()
    } else {
        format!("{name}(allows: [{}])", allows.elems().join(", "))
    }
}

/// Privacy-preserving REPL value renderer.
///
/// Any scalar, table cell, chart, report, or composite field whose effective sensitivity tags
/// are NOT a subset of `allowed_show_tags` renders as `[REDACTED:<sorted,tags>]` without ever
/// exposing the underlying value.
#[must_use]
pub fn format_repl_value(
    val: &Val,
    lty: &LTy,
    allowed_show_tags: &TagSet,
    struct_layouts: &HashMap<Ident, StructLayout>,
) -> String {
    // Tables handle per-column & row_tags redaction so column headers and row count remain visible.
    if let (Val::Table(tv), Ty::Table(tt)) = (val, &lty.ty) {
        return format_repl_table(tv, tt, &lty.tags, allowed_show_tags);
    }
    if let (Val::Columnar(vm), Ty::Table(tt)) = (val, &lty.ty) {
        return format_repl_vm_table(vm, tt, &lty.tags, allowed_show_tags);
    }

    // Profiles redact every tagged column inside `ProfileVal`, AND if `Ty::Profile(ptags)` carries
    // table-level `row_tags` (e.g. after filtering on a sensitive column), redact the entire
    // profile summary so filtered row counts cannot leak.
    if let (Val::Profile(pv), Ty::Profile(ptags)) = (val, &lty.ty) {
        let unallowed = lty.tags.union(ptags).diff(allowed_show_tags);
        if !unallowed.is_empty() {
            return redact_tags(&unallowed);
        }
        return render_profile_terminal(pv);
    }

    // Charts & Reports check their embedded tag set as well as outer tags.
    if let (Val::Chart(cv), Ty::Chart(ctags)) = (val, &lty.ty) {
        let unallowed = lty.tags.union(ctags).diff(allowed_show_tags);
        if !unallowed.is_empty() {
            return redact_tags(&unallowed);
        }
        return render_chart_terminal(cv);
    }
    if let (Val::Report(rv), Ty::Report(rtags)) = (val, &lty.ty) {
        let unallowed = lty.tags.union(rtags).diff(allowed_show_tags);
        if !unallowed.is_empty() {
            return redact_tags(&unallowed);
        }
        return format!(
            "Report(\"{}\", {} summaries, {} charts, {} tables)",
            rv.title,
            rv.summaries.len(),
            rv.charts.len(),
            rv.tables.len()
        );
    }

    // Any outer unallowed sensitivity tag immediately redacts without inspecting `val`.
    let outer_unallowed = lty.tags.diff(allowed_show_tags);
    if !outer_unallowed.is_empty() {
        return redact_tags(&outer_unallowed);
    }

    match (val, &lty.ty) {
        (Val::OptNone, _) => "none".to_string(),
        (Val::OptSome(inner), Ty::Option(inner_ty)) => format_repl_value(
            inner,
            &LTy::new((**inner_ty).clone(), lty.tags.clone()),
            allowed_show_tags,
            struct_layouts,
        ),
        (Val::ResOk(inner), Ty::Result { ok_ty, .. }) => format!(
            "Ok({})",
            format_repl_value(
                inner,
                &LTy::new((**ok_ty).clone(), lty.tags.clone()),
                allowed_show_tags,
                struct_layouts,
            )
        ),
        (Val::ResErr(inner), Ty::Result { err_ty, .. }) => format!(
            "Error({})",
            format_repl_value(
                inner,
                &LTy::new((**err_ty).clone(), lty.tags.clone()),
                allowed_show_tags,
                struct_layouts,
            )
        ),
        (Val::Tuple(vals), Ty::Tuple(ltys)) => {
            let parts: Vec<String> = vals
                .iter()
                .zip(ltys)
                .map(|(v, el)| {
                    let eff = LTy::new(el.ty.clone(), el.tags.union(&lty.tags));
                    format_repl_value(v, &eff, allowed_show_tags, struct_layouts)
                })
                .collect();
            format!("({})", parts.join(", "))
        }
        (Val::List(vals), Ty::List(el)) => {
            let eff = LTy::new(el.ty.clone(), el.tags.union(&lty.tags));
            let parts: Vec<String> = vals
                .iter()
                .map(|v| format_repl_value(v, &eff, allowed_show_tags, struct_layouts))
                .collect();
            format!("[{}]", parts.join(", "))
        }
        (Val::Map(pairs), Ty::Map { key, val: vty }) => {
            let k_eff = LTy::new(key.ty.clone(), key.tags.union(&lty.tags));
            let v_eff = LTy::new(vty.ty.clone(), vty.tags.union(&lty.tags));
            let parts: Vec<String> = pairs
                .iter()
                .map(|(k, v)| {
                    format!(
                        "{}: {}",
                        format_repl_value(k, &k_eff, allowed_show_tags, struct_layouts),
                        format_repl_value(v, &v_eff, allowed_show_tags, struct_layouts)
                    )
                })
                .collect();
            format!("{{{}}}", parts.join(", "))
        }
        (
            Val::Ctor {
                type_name,
                ctor_name,
                fields,
            },
            Ty::Data(_),
        ) => {
            if let Some(layout) = struct_layouts.get(type_name) {
                let parts: Vec<String> = layout
                    .field_names
                    .iter()
                    .zip(&layout.field_ltys)
                    .zip(fields)
                    .map(|((fname, flty), fv)| {
                        let eff = LTy::new(flty.ty.clone(), flty.tags.union(&lty.tags));
                        format!(
                            "{fname}: {}",
                            format_repl_value(fv, &eff, allowed_show_tags, struct_layouts)
                        )
                    })
                    .collect();
                format!("{ctor_name}({})", parts.join(", "))
            } else if fields.is_empty() {
                ctor_name.clone()
            } else {
                let parts: Vec<String> = fields.iter().map(format_public_scalar).collect();
                format!("{ctor_name}({})", parts.join(", "))
            }
        }
        (
            Val::LinearModel {
                slope,
                intercept,
                r2,
            },
            _,
        ) => format!(
            "LinearModel(slope: {}, intercept: {}, r_squared: {})",
            slope.to_f64(),
            intercept.to_f64(),
            r2.to_f64()
        ),
        (Val::StatTest { stat, p_value }, _) => format!(
            "StatTest(stat: {}, p_value: {})",
            stat.to_f64(),
            p_value.to_f64()
        ),
        (Val::DynTable { headers, rows }, Ty::DynamicTable(dtags)) => {
            let unallowed = lty.tags.union(dtags).diff(allowed_show_tags);
            let redact_marker = if unallowed.is_empty() {
                None
            } else {
                Some(redact_tags(&unallowed))
            };
            format_dyn_table(headers, rows, redact_marker.as_deref())
        }
        (other, _) => format_public_scalar(other),
    }
}

fn format_public_scalar(v: &Val) -> String {
    match v {
        Val::Unit => "Unit".to_string(),
        Val::Bool(b) => b.to_string(),
        Val::Int(n) => n.to_string(),
        Val::Decimal(d) => render_decimal(d),
        Val::Float(f) => format!("{}", f.to_f64()),
        Val::Text(s) => format!("\"{s}\""),
        Val::Date(d) => d.to_i64().map_or_else(|| d.to_string(), format_iso_date),
        Val::Timestamp(ts) => ts
            .to_i64()
            .map_or_else(|| ts.to_string(), format_iso_timestamp),
        Val::OptNone => "none".to_string(),
        Val::OptSome(inner) => format_public_scalar(inner),
        other => render_public_val(other),
    }
}

fn format_public_cell(v: &Val) -> String {
    match v {
        Val::Text(s) => s.clone(),
        Val::Date(d) => d.to_i64().map_or_else(|| d.to_string(), format_iso_date),
        Val::Timestamp(ts) => ts
            .to_i64()
            .map_or_else(|| ts.to_string(), format_iso_timestamp),
        Val::Decimal(d) => render_decimal(d),
        Val::Float(f) => format!("{}", f.to_f64()),
        Val::OptNone => "none".to_string(),
        Val::OptSome(inner) => format_public_cell(inner),
        other => render_public_val(other),
    }
}

fn format_repl_table(
    tv: &TableVal,
    tt: &TableTy,
    outer_tags: &TagSet,
    allowed_show_tags: &TagSet,
) -> String {
    let col_count = tv.cols.len();
    let total_rows = tv.rows.len();
    let preview_rows = total_rows.min(MAX_TABLE_PREVIEW_ROWS);

    // Precompute per-column redaction markers combining static `TableTy`, runtime `TableVal`,
    // table `row_tags`, and outer `LTy.tags`.
    let col_redactions: Vec<Option<String>> = tv
        .cols
        .iter()
        .enumerate()
        .map(|(i, rt_col)| {
            let st_tags = tt
                .cols
                .get(i)
                .map_or_else(TagSet::empty, |c| c.tags.clone());
            let eff = rt_col
                .tags
                .union(&st_tags)
                .union(&tt.row_tags)
                .union(&tt.order_tags)
                .union(outer_tags);
            let unallowed = eff.diff(allowed_show_tags);
            if unallowed.is_empty() {
                None
            } else {
                Some(redact_tags(&unallowed))
            }
        })
        .collect();

    let mut widths: Vec<usize> = tv.cols.iter().map(|c| c.name.chars().count()).collect();
    let mut rendered_rows: Vec<Vec<String>> = Vec::with_capacity(preview_rows);
    for row in tv.rows.iter().take(preview_rows) {
        let mut rcells = Vec::with_capacity(col_count);
        for ci in 0..col_count {
            let cell_str = if let Some(marker) = &col_redactions[ci] {
                marker.clone()
            } else {
                row.cells
                    .get(ci)
                    .map_or_else(|| "none".to_string(), format_public_cell)
            };
            widths[ci] = widths[ci].max(cell_str.chars().count());
            rcells.push(cell_str);
        }
        rendered_rows.push(rcells);
    }

    let mut out = String::new();
    out.push('|');
    for (ci, c) in tv.cols.iter().enumerate() {
        let pad = widths[ci].saturating_sub(c.name.chars().count());
        out.push(' ');
        out.push_str(&c.name);
        for _ in 0..pad {
            out.push(' ');
        }
        out.push_str(" |");
    }
    out.push('\n');
    out.push('|');
    for &w in &widths {
        out.push(' ');
        for _ in 0..w {
            out.push('-');
        }
        out.push_str(" |");
    }
    for row in rendered_rows {
        out.push('\n');
        out.push('|');
        for (ci, cell) in row.iter().enumerate() {
            let pad = widths[ci].saturating_sub(cell.chars().count());
            out.push(' ');
            out.push_str(cell);
            for _ in 0..pad {
                out.push(' ');
            }
            out.push_str(" |");
        }
    }
    if total_rows > preview_rows {
        let _ = write!(out, "\n... ({} more rows)", total_rows - preview_rows);
    }
    let _ = write!(out, "\n({total_rows} rows, {col_count} cols)");
    out
}

fn format_repl_vm_table(
    vm: &crate::vm::ops::VmTable,
    tt: &TableTy,
    outer_tags: &TagSet,
    allowed_show_tags: &TagSet,
) -> String {
    let col_count = vm.cols.len();
    let total_rows = vm.total_rows();
    let preview_rows = total_rows.min(MAX_TABLE_PREVIEW_ROWS);

    // Precompute per-column redaction markers combining static `TableTy`, runtime `VmTable`,
    // table `row_tags`, `order_tags`, and outer `LTy.tags`.
    let col_redactions: Vec<Option<String>> = vm
        .cols
        .iter()
        .enumerate()
        .map(|(i, rt_col)| {
            let st_tags = tt
                .cols
                .get(i)
                .map_or_else(TagSet::empty, |c| c.tags.clone());
            let eff = rt_col
                .tags
                .union(&st_tags)
                .union(&tt.row_tags)
                .union(&tt.order_tags)
                .union(outer_tags);
            let unallowed = eff.diff(allowed_show_tags);
            if unallowed.is_empty() {
                None
            } else {
                Some(redact_tags(&unallowed))
            }
        })
        .collect();

    let mut widths: Vec<usize> = vm.cols.iter().map(|c| c.name.chars().count()).collect();
    let sample_rows = vm.collect_rows_limited(preview_rows);
    let mut rendered_rows: Vec<Vec<String>> = Vec::with_capacity(sample_rows.len());
    for row_cells in &sample_rows {
        let mut rcells = Vec::with_capacity(col_count);
        for ci in 0..col_count {
            let cell_str = if let Some(marker) = &col_redactions[ci] {
                marker.clone()
            } else {
                row_cells
                    .get(ci)
                    .map_or_else(|| "none".to_string(), format_public_cell)
            };
            widths[ci] = widths[ci].max(cell_str.chars().count());
            rcells.push(cell_str);
        }
        rendered_rows.push(rcells);
    }

    let mut out = String::new();
    out.push('|');
    for (ci, c) in vm.cols.iter().enumerate() {
        let pad = widths[ci].saturating_sub(c.name.chars().count());
        out.push(' ');
        out.push_str(&c.name);
        for _ in 0..pad {
            out.push(' ');
        }
        out.push_str(" |");
    }
    out.push('\n');
    out.push('|');
    for &w in &widths {
        out.push(' ');
        for _ in 0..w {
            out.push('-');
        }
        out.push_str(" |");
    }
    for row in rendered_rows {
        out.push('\n');
        out.push('|');
        for (ci, cell) in row.iter().enumerate() {
            let pad = widths[ci].saturating_sub(cell.chars().count());
            out.push(' ');
            out.push_str(cell);
            for _ in 0..pad {
                out.push(' ');
            }
            out.push_str(" |");
        }
    }
    if total_rows > preview_rows {
        let _ = write!(out, "\n... ({} more rows)", total_rows - preview_rows);
    }
    let _ = write!(out, "\n({total_rows} rows, {col_count} cols)");
    out
}

fn format_dyn_table(headers: &[String], rows: &[Vec<Val>], redact_marker: Option<&str>) -> String {
    let preview_rows = rows.len().min(MAX_TABLE_PREVIEW_ROWS);
    let mut widths: Vec<usize> = headers.iter().map(|h| h.chars().count()).collect();
    let mut rendered: Vec<Vec<String>> = Vec::with_capacity(preview_rows);
    for row in rows.iter().take(preview_rows) {
        let mut rcells = Vec::with_capacity(headers.len());
        for (ci, width) in widths.iter_mut().enumerate() {
            let cell_str = if let Some(marker) = redact_marker {
                marker.to_string()
            } else {
                row.get(ci)
                    .map_or_else(|| "none".to_string(), format_public_cell)
            };
            *width = (*width).max(cell_str.chars().count());
            rcells.push(cell_str);
        }
        rendered.push(rcells);
    }

    let mut out = String::new();
    out.push('|');
    for (ci, h) in headers.iter().enumerate() {
        let pad = widths[ci].saturating_sub(h.chars().count());
        out.push(' ');
        out.push_str(h);
        for _ in 0..pad {
            out.push(' ');
        }
        out.push_str(" |");
    }
    out.push('\n');
    out.push('|');
    for &w in &widths {
        out.push(' ');
        for _ in 0..w {
            out.push('-');
        }
        out.push_str(" |");
    }
    for row in rendered {
        out.push('\n');
        out.push('|');
        for (ci, cell) in row.iter().enumerate() {
            let pad = widths[ci].saturating_sub(cell.chars().count());
            out.push(' ');
            out.push_str(cell);
            for _ in 0..pad {
                out.push(' ');
            }
            out.push_str(" |");
        }
    }
    let _ = write!(out, "\n({} rows, {} cols)", rows.len(), headers.len());
    out
}

// ===========================================================================
// Internal Helpers (`untyped` AST scanning, explain helpers, schema rendering)
// ===========================================================================

struct UntypedCallSite {
    start: usize,
    end: usize,
    method: String,
    path: String,
    sheet: Option<String>,
}

fn collect_untyped_calls_stmt(st: &Stmt, out: &mut Vec<UntypedCallSite>) -> Result<(), String> {
    match &st.kind {
        StmtKind::Var { value, .. } | StmtKind::Expr(value) | StmtKind::Assert(value) => {
            collect_untyped_calls_expr(value, out)
        }
        StmtKind::Assign { lhs, rhs } => {
            collect_untyped_calls_expr(lhs, out)?;
            collect_untyped_calls_expr(rhs, out)
        }
        StmtKind::Return { value, guard } => {
            if let Some(v) = value {
                collect_untyped_calls_expr(v, out)?;
            }
            if let Some(g) = guard {
                collect_untyped_calls_expr(g, out)?;
            }
            Ok(())
        }
        StmtKind::Break { guard } | StmtKind::Continue { guard } => {
            if let Some(g) = guard {
                collect_untyped_calls_expr(g, out)?;
            }
            Ok(())
        }
        StmtKind::Stop(Some(e)) => collect_untyped_calls_expr(e, out),
        StmtKind::Stop(None) => Ok(()),
        StmtKind::For { iter, body, .. } => {
            collect_untyped_calls_expr(iter, out)?;
            for s in body {
                collect_untyped_calls_stmt(s, out)?;
            }
            Ok(())
        }
        StmtKind::While { cond, body } => {
            collect_untyped_calls_expr(cond, out)?;
            for s in body {
                collect_untyped_calls_stmt(s, out)?;
            }
            Ok(())
        }
    }
}

fn collect_untyped_calls_expr(expr: &Expr, out: &mut Vec<UntypedCallSite>) -> Result<(), String> {
    match &expr.kind {
        ExprKind::Call { callee, args } => {
            if let ExprKind::Field { receiver, member } = &callee.kind
                && matches!(&receiver.kind, ExprKind::Ident(name) if name == "untyped")
            {
                let path = match args.first() {
                    Some(CallArg::Positional(Expr {
                        kind: ExprKind::Text { value, .. },
                        ..
                    })) => value.clone(),
                    _ => {
                        return Err(format!(
                            "`untyped.{}` requires a string literal file path as its first argument",
                            member.name
                        ));
                    }
                };
                let mut sheet = None;
                for arg in args.iter().skip(1) {
                    if let CallArg::Named { name, value, .. } = arg
                        && name.name == "sheet"
                    {
                        if let ExprKind::Text { value: s, .. } = &value.kind {
                            sheet = Some(s.clone());
                        } else {
                            return Err(
                                "`untyped.read_xlsx` `sheet:` argument must be a string literal"
                                    .to_string(),
                            );
                        }
                    }
                }
                out.push(UntypedCallSite {
                    start: expr.span.start as usize,
                    end: expr.span.end as usize,
                    method: member.name.clone(),
                    path,
                    sheet,
                });
                return Ok(());
            }
            collect_untyped_calls_expr(callee, out)?;
            for a in args {
                match a {
                    CallArg::Positional(e) | CallArg::Named { value: e, .. } => {
                        collect_untyped_calls_expr(e, out)?;
                    }
                }
            }
            Ok(())
        }
        ExprKind::Field { receiver, .. }
        | ExprKind::Unary { expr: receiver, .. }
        | ExprKind::Paren(receiver) => collect_untyped_calls_expr(receiver, out),
        ExprKind::Binary { lhs, rhs, .. } => {
            collect_untyped_calls_expr(lhs, out)?;
            collect_untyped_calls_expr(rhs, out)
        }
        ExprKind::Index { target, index } => {
            collect_untyped_calls_expr(target, out)?;
            collect_untyped_calls_expr(index, out)
        }
        ExprKind::Tuple(xs) | ExprKind::List(xs) => {
            for e in xs {
                collect_untyped_calls_expr(e, out)?;
            }
            Ok(())
        }
        ExprKind::Map(pairs) => {
            for (k, v) in pairs {
                collect_untyped_calls_expr(k, out)?;
                collect_untyped_calls_expr(v, out)?;
            }
            Ok(())
        }
        ExprKind::IfInline {
            cond,
            then_expr,
            else_ifs,
            else_expr,
        } => {
            collect_untyped_calls_expr(cond, out)?;
            collect_untyped_calls_expr(then_expr, out)?;
            for (c, b) in else_ifs {
                collect_untyped_calls_expr(c, out)?;
                collect_untyped_calls_expr(b, out)?;
            }
            collect_untyped_calls_expr(else_expr, out)
        }
        ExprKind::IfBlock {
            cond,
            then_body,
            else_ifs,
            else_body,
        } => {
            collect_untyped_calls_expr(cond, out)?;
            for s in then_body {
                collect_untyped_calls_stmt(s, out)?;
            }
            for br in else_ifs {
                collect_untyped_calls_expr(&br.cond, out)?;
                for s in &br.body {
                    collect_untyped_calls_stmt(s, out)?;
                }
            }
            if let Some(eb) = else_body {
                for s in &eb.body {
                    collect_untyped_calls_stmt(s, out)?;
                }
            }
            Ok(())
        }
        ExprKind::Case { scrut, lines } => {
            collect_untyped_calls_expr(scrut, out)?;
            for line in lines {
                match line {
                    crate::syntax::CaseLine::ArmHeader { .. } => {}
                    crate::syntax::CaseLine::ArmInline { expr, .. } => {
                        collect_untyped_calls_expr(expr, out)?;
                    }
                    crate::syntax::CaseLine::Stmt(s) => {
                        collect_untyped_calls_stmt(s, out)?;
                    }
                }
            }
            Ok(())
        }
        ExprKind::Lambda { body, .. } => match body {
            crate::syntax::LambdaBody::Expr(e) => collect_untyped_calls_expr(e, out),
            crate::syntax::LambdaBody::Block(stmts) => {
                for s in stmts {
                    collect_untyped_calls_stmt(s, out)?;
                }
                Ok(())
            }
        },
        ExprKind::TableLit { rows, .. } => {
            for row in rows {
                for cell in row {
                    collect_untyped_calls_expr(cell, out)?;
                }
            }
            Ok(())
        }
        ExprKind::InterpText { parts, .. } => {
            for p in parts {
                if let crate::syntax::InterpPart::Expr(e) = p {
                    collect_untyped_calls_expr(e, out)?;
                }
            }
            Ok(())
        }
        ExprKind::Int(_)
        | ExprKind::Decimal(_)
        | ExprKind::Date(_)
        | ExprKind::Timestamp(_)
        | ExprKind::Text { .. }
        | ExprKind::Bool(_)
        | ExprKind::None
        | ExprKind::Atom(_)
        | ExprKind::DotSelf
        | ExprKind::DotField(_)
        | ExprKind::Ident(_)
        | ExprKind::CapName(_)
        | ExprKind::Underscore => Ok(()),
    }
}

fn collect_lhs_bound_names(lhs: &Expr, out: &mut Vec<String>) {
    match &lhs.kind {
        ExprKind::Ident(n) => out.push(n.clone()),
        ExprKind::Tuple(elems) => {
            for e in elems {
                collect_lhs_bound_names(e, out);
            }
        }
        _ => {}
    }
}

fn render_untyped_public_schema(schema_name: &str, inferred: &InferredSchema) -> String {
    let mut out = String::new();
    let _ = writeln!(out, "schema {schema_name}");
    for c in &inferred.cols {
        let opt = if c.nullable { "?" } else { "" };
        let _ = writeln!(out, "  {}: {}{opt}", c.name, c.ty.dana_name());
    }
    out.push_str("end\n");
    out
}

fn render_table_ty_as_schema(schema_name: &str, tt: &TableTy) -> String {
    let mut out = String::new();
    if tt.row_tags.is_empty() {
        let _ = writeln!(out, "schema {schema_name}");
    } else {
        let _ = writeln!(
            out,
            "schema {schema_name} [{}]",
            tt.row_tags.elems().join(", ")
        );
    }
    for c in &tt.cols {
        let ty_str = format_scalar_ty_name(&c.ty);
        if c.tags.is_empty() {
            let _ = writeln!(out, "  {}: {ty_str}", c.name);
        } else {
            let _ = writeln!(
                out,
                "  {}: {ty_str} [{}]",
                c.name,
                c.tags.elems().join(", ")
            );
        }
    }
    out.push_str("end\n");
    out
}

fn collect_let_plans_and_tail<'a>(
    mut expr: &'a ExecExpr,
    local_plans: &mut HashMap<String, ExecPlan>,
) -> &'a ExecExpr {
    loop {
        match expr {
            ExecExpr::LetE {
                name, bound, body, ..
            } => {
                match bound.as_ref() {
                    ExecExpr::Rel(plan) => {
                        let resolved = bind_exec_plan_sources(plan, local_plans);
                        local_plans.insert(name.clone(), resolved);
                    }
                    ExecExpr::Var(v) => {
                        if let Some(prev) = local_plans.get(v).cloned() {
                            local_plans.insert(name.clone(), prev);
                        }
                    }
                    _ => {}
                }
                expr = body;
            }
            ExecExpr::Join { body, .. } => {
                expr = body;
            }
            other => return other,
        }
    }
}

fn collect_plans_in_expr<'a>(expr: &'a ExecExpr, out: &mut Vec<&'a ExecPlan>) {
    match expr {
        ExecExpr::Rel(plan) => out.push(plan),
        ExecExpr::LetE { bound, body, .. }
        | ExecExpr::Join {
            rhs: bound, body, ..
        } => {
            collect_plans_in_expr(bound, out);
            collect_plans_in_expr(body, out);
        }
        ExecExpr::IfE {
            cond,
            then_br,
            else_br,
        } => {
            collect_plans_in_expr(cond, out);
            collect_plans_in_expr(then_br, out);
            collect_plans_in_expr(else_br, out);
        }
        ExecExpr::CaseE { scrut, arms } => {
            collect_plans_in_expr(scrut, out);
            for a in arms {
                collect_plans_in_expr(&a.body, out);
            }
        }
        ExecExpr::App { fn_expr, args } => {
            collect_plans_in_expr(fn_expr, out);
            for a in args {
                collect_plans_in_expr(a, out);
            }
        }
        ExecExpr::Call { args, .. }
        | ExecExpr::Jump { args, .. }
        | ExecExpr::Tuple(args)
        | ExecExpr::Ctor { args, .. }
        | ExecExpr::Prim { args, .. }
        | ExecExpr::Host { args, .. } => {
            for a in args {
                collect_plans_in_expr(a, out);
            }
        }
        ExecExpr::Proj { tup: e, .. } | ExecExpr::Assert { cond: e, .. } | ExecExpr::Fail(e) => {
            collect_plans_in_expr(e, out);
        }
        ExecExpr::Lam { body, .. } => collect_plans_in_expr(body, out),
        ExecExpr::ForLoop {
            iter_expr,
            body,
            after,
            ..
        } => {
            collect_plans_in_expr(iter_expr, out);
            collect_plans_in_expr(body, out);
            collect_plans_in_expr(after, out);
        }
        ExecExpr::WhileLoop {
            cond, body, after, ..
        } => {
            collect_plans_in_expr(cond, out);
            collect_plans_in_expr(body, out);
            collect_plans_in_expr(after, out);
        }
        ExecExpr::Stop {
            detail: Some(d), ..
        } => collect_plans_in_expr(d, out),
        ExecExpr::Lit(_)
        | ExecExpr::Var(_)
        | ExecExpr::ConstRef(_)
        | ExecExpr::TableLit { .. }
        | ExecExpr::CheckPromise { .. }
        | ExecExpr::Stop { detail: None, .. } => {}
    }
}

fn apply_span_replacements(src: &str, replacements: &[(usize, usize, String)]) -> String {
    let mut sorted = replacements.to_vec();
    sorted.sort_by_key(|(s, _, _)| *s);
    let mut out = String::with_capacity(src.len());
    let mut cursor = 0usize;
    for (start, end, repl) in sorted {
        if start < cursor || end > src.len() {
            continue;
        }
        out.push_str(&src[cursor..start]);
        out.push_str(&repl);
        cursor = end;
    }
    out.push_str(&src[cursor..]);
    out
}

fn is_comment_only(s: &str) -> bool {
    s.lines().all(|l| {
        let t = l.trim();
        t.is_empty() || t.starts_with('#')
    })
}

fn is_valid_lower_ident(s: &str) -> bool {
    let mut chars = s.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    first.is_ascii_lowercase() && chars.all(|c| c.is_ascii_alphanumeric() || c == '_')
}

fn ident_to_cap_schema_name(ident: &str) -> String {
    let mut out = String::new();
    for part in ident.split(|c: char| !c.is_ascii_alphanumeric()) {
        let mut chars = part.chars();
        if let Some(first) = chars.next() {
            out.push(first.to_ascii_uppercase());
            for ch in chars {
                out.push(ch.to_ascii_lowercase());
            }
        }
    }
    if out.is_empty() || !out.as_bytes()[0].is_ascii_uppercase() {
        "Record".to_string()
    } else {
        out
    }
}

fn strip_quotes(s: &str) -> &str {
    s.strip_prefix('"')
        .and_then(|r| r.strip_suffix('"'))
        .or_else(|| s.strip_prefix('\'').and_then(|r| r.strip_suffix('\'')))
        .unwrap_or(s)
}

fn next_non_nl_token(toks: &[crate::syntax::Token], mut idx: usize) -> Option<&TokenKind> {
    while idx < toks.len() {
        match &toks[idx].kind {
            TokenKind::Newline => idx += 1,
            TokenKind::Eof => return None,
            other => return Some(other),
        }
    }
    None
}

fn prev_raw_token(toks: &[crate::syntax::Token], idx: usize) -> Option<&TokenKind> {
    if idx == 0 {
        None
    } else {
        Some(&toks[idx - 1].kind)
    }
}

fn line_has_colon(toks: &[crate::syntax::Token], mut idx: usize) -> bool {
    let mut depth = 0i32;
    while idx < toks.len() {
        match toks[idx].kind {
            TokenKind::Newline | TokenKind::Eof => return false,
            TokenKind::LParen | TokenKind::LBrack | TokenKind::LBrace => depth += 1,
            TokenKind::RParen | TokenKind::RBrack | TokenKind::RBrace => depth -= 1,
            TokenKind::Colon if depth == 0 => return true,
            _ => {}
        }
        idx += 1;
    }
    false
}

/// Ensure `ScalarTy` import stays synchronized with `format_scalar_ty_name`.
const _: fn(&ScalarTy) -> String = format_scalar_ty_name;
