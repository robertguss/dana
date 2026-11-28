//! Multi-module loader and name resolver for Dana.
//!
//! Resolves:
//! - Built-in standard library namespaces (`Stats`, `Report`, `Table`, `Args`, `Files`,
//!   `DB`, `Console`, `Https`, `Secret`, `Math`, `Text`, `Date`, `Timestamp`).
//! - Local project modules: `Seminary.Enrollment` -> `seminary/enrollment.dana` (CapCase
//!   segments map to lowercase hyphenated directories/files per Reference §2.1).
//! - Hash-pinned `vendor/` modules (enforced **pure by default**: cannot mint ambient I/O).

use std::collections::{HashMap, HashSet};
use std::fs;
use std::path::{Path, PathBuf};

use crate::base::{DiagCode, Diagnostic, FileId, SourceMap, Span};
use crate::core::syntax::{BUILT_IN_TAGS, Policy};
use crate::syntax::ast::*;
use crate::syntax::parse_module;

/// Built-in stdlib module namespaces available without disk files.
pub const STDLIB_MODULES: &[&str] = &[
    "Stats",
    "Report",
    "Table",
    "Args",
    "Files",
    "DB",
    "Console",
    "Https",
    "LocalHttp",
    "LocalSocket",
    "Secret",
    "Math",
    "Text",
    "Date",
    "Timestamp",
];

/// Provenance of a loaded Dana module.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ModuleOrigin {
    Root,
    Local,
    Vendor,
}

/// One parsed and resolved Dana module.
#[derive(Clone, Debug)]
pub struct ResolvedModule {
    pub full_name: String,
    pub file_id: FileId,
    pub origin: ModuleOrigin,
    pub module: Module,
    pub exposed_all: bool,
    pub exposed_names: HashSet<String>,
}

/// Complete resolved program (root module + transitively imported local/vendor modules + policy).
#[derive(Clone, Debug)]
pub struct ResolvedProgram {
    pub root_name: String,
    pub modules: Vec<ResolvedModule>,
    pub module_index: HashMap<String, usize>,
    pub declared_tags: HashSet<String>,
    pub policy: Option<Policy>,
}

impl ResolvedProgram {
    #[must_use]
    pub fn root(&self) -> &ResolvedModule {
        &self.modules[0]
    }

    #[must_use]
    pub fn is_valid_tag(&self, tag: &str) -> bool {
        BUILT_IN_TAGS.contains(&tag) || self.declared_tags.contains(tag)
    }
}

/// Convert a `CapCase` module segment into lowercase-hyphenated filename form (`CourseOutcomes` -> `course-outcomes`).
#[must_use]
pub fn cap_segment_to_kebab(seg: &str) -> String {
    let mut out = String::with_capacity(seg.len() + 4);
    for (i, ch) in seg.chars().enumerate() {
        if ch.is_ascii_uppercase() {
            if i > 0 {
                out.push('-');
            }
            out.push(ch.to_ascii_lowercase());
        } else {
            out.push(ch);
        }
    }
    out
}

/// Map a module path `["Seminary", "Enrollment"]` to relative path `seminary/enrollment.dana`.
#[must_use]
pub fn module_path_to_rel(path: &[SpannedName]) -> PathBuf {
    let mut rel = PathBuf::new();
    for (idx, seg) in path.iter().enumerate() {
        let piece = cap_segment_to_kebab(&seg.name);
        if idx + 1 == path.len() {
            rel.push(format!("{piece}.dana"));
        } else {
            rel.push(piece);
        }
    }
    rel
}

#[must_use]
pub fn join_module_path(path: &[SpannedName]) -> String {
    path.iter()
        .map(|s| s.name.as_str())
        .collect::<Vec<_>>()
        .join(".")
}

/// Resolve an already-parsed in-memory root module (no disk imports except stdlib).
///
/// # Errors
/// Returns diagnostics on duplicate declarations, cyclic/missing imports, or invalid tags.
pub fn resolve_module(
    file_id: FileId,
    module: Module,
    policy: Option<Policy>,
) -> Result<ResolvedProgram, Vec<Diagnostic>> {
    let mut sm = SourceMap::new();
    resolve_with_loader(file_id, module, None, policy, &mut sm)
}

/// Resolve an already-parsed in-memory root module using an optional base directory for
/// local and SHA-256 hash-pinned `vendor/` module imports.
///
/// # Errors
/// Returns diagnostics on duplicate declarations, cyclic/missing imports, unpinned/tampered
/// vendored modules, or invalid tags.
pub fn resolve_module_in_dir(
    file_id: FileId,
    module: Module,
    root_dir: Option<&Path>,
    policy: Option<Policy>,
    sm: &mut SourceMap,
) -> Result<ResolvedProgram, Vec<Diagnostic>> {
    resolve_with_loader(file_id, module, root_dir, policy, sm)
}

/// Parse and resolve a `.dana` file from disk along with any local or `vendor/` module imports.
///
/// # Errors
/// Returns diagnostics on I/O, lex/parse, duplicate declaration, cycle, or missing import errors.
pub fn resolve_path(
    path: &Path,
    policy: Option<Policy>,
    sm: &mut SourceMap,
) -> Result<ResolvedProgram, Vec<Diagnostic>> {
    let src = fs::read_to_string(path).map_err(|e| {
        vec![Diagnostic::error(
            DiagCode::IoError,
            format!("cannot read `{}`: {e}", path.display()),
        )]
    })?;
    let fid = sm.add_file(path.display().to_string(), src.clone());
    let module = parse_module(fid, &src).map_err(|d| vec![d])?;
    let root_dir = path.parent().map(Path::to_path_buf);
    resolve_with_loader(fid, module, root_dir.as_deref(), policy, sm)
}

fn resolve_with_loader(
    root_fid: FileId,
    root_module: Module,
    root_dir: Option<&Path>,
    policy: Option<Policy>,
    sm: &mut SourceMap,
) -> Result<ResolvedProgram, Vec<Diagnostic>> {
    let mut diags = Vec::new();
    let mut modules = Vec::new();
    let mut module_index = HashMap::new();
    let mut visiting = HashSet::new();
    let mut declared_tags = HashSet::new();

    let root_name = join_module_path(&root_module.header.path);
    load_recursive(
        root_name.clone(),
        root_fid,
        ModuleOrigin::Root,
        root_module,
        root_dir,
        sm,
        &mut visiting,
        &mut modules,
        &mut module_index,
        &mut declared_tags,
        &mut diags,
    );

    if !diags.is_empty() {
        return Err(diags);
    }

    // Ensure root module is always at index 0.
    if let Some(&root_pos) = module_index.get(&root_name)
        && root_pos != 0
    {
        modules.swap(0, root_pos);
        module_index.clear();
        for (i, m) in modules.iter().enumerate() {
            module_index.insert(m.full_name.clone(), i);
        }
    }

    Ok(ResolvedProgram {
        root_name,
        modules,
        module_index,
        declared_tags,
        policy,
    })
}

#[expect(
    clippy::too_many_arguments,
    reason = "recursive module loader carries shared resolution state"
)]
fn load_recursive(
    full_name: String,
    file_id: FileId,
    origin: ModuleOrigin,
    module: Module,
    root_dir: Option<&Path>,
    sm: &mut SourceMap,
    visiting: &mut HashSet<String>,
    modules: &mut Vec<ResolvedModule>,
    module_index: &mut HashMap<String, usize>,
    declared_tags: &mut HashSet<String>,
    diags: &mut Vec<Diagnostic>,
) {
    if module_index.contains_key(&full_name) {
        return;
    }
    visiting.insert(full_name.clone());

    // Validate duplicate top-level item names inside this module and collect custom `tag`s.
    let mut seen_types = HashSet::new();
    let mut seen_values = HashSet::new();
    for item in &module.items {
        match item {
            TopItem::Tag(t) => {
                declared_tags.insert(t.name.name.clone());
            }
            TopItem::Schema(s) => {
                if !seen_types.insert(s.name.name.clone()) {
                    diags.push(
                        Diagnostic::error(
                            DiagCode::ResolveError,
                            format!(
                                "duplicate type/schema `{}` in module `{full_name}`",
                                s.name.name
                            ),
                        )
                        .with_span(s.name.span),
                    );
                }
            }
            TopItem::Struct(s) => {
                if !seen_types.insert(s.name.name.clone()) {
                    diags.push(
                        Diagnostic::error(
                            DiagCode::ResolveError,
                            format!(
                                "duplicate type/struct `{}` in module `{full_name}`",
                                s.name.name
                            ),
                        )
                        .with_span(s.name.span),
                    );
                }
            }
            TopItem::Enum(e) => {
                if !seen_types.insert(e.name.name.clone()) {
                    diags.push(
                        Diagnostic::error(
                            DiagCode::ResolveError,
                            format!(
                                "duplicate type/enum `{}` in module `{full_name}`",
                                e.name.name
                            ),
                        )
                        .with_span(e.name.span),
                    );
                }
            }
            TopItem::Const(c) => {
                if !seen_values.insert(c.name.name.clone()) {
                    diags.push(
                        Diagnostic::error(
                            DiagCode::ResolveError,
                            format!("duplicate const `{}` in module `{full_name}`", c.name.name),
                        )
                        .with_span(c.name.span),
                    );
                }
            }
            TopItem::Fn(f) => {
                if !seen_values.insert(f.name.name.clone()) {
                    diags.push(
                        Diagnostic::error(
                            DiagCode::ResolveError,
                            format!(
                                "duplicate function `{}` in module `{full_name}`",
                                f.name.name
                            ),
                        )
                        .with_span(f.name.span),
                    );
                }
            }
            TopItem::Test(_) => {}
        }
    }

    // Load imported `use` modules.
    for u in &module.header.uses {
        let dep_name = join_module_path(&u.path);
        if STDLIB_MODULES.contains(&dep_name.as_str()) {
            continue;
        }
        if visiting.contains(&dep_name) {
            diags.push(
                Diagnostic::error(
                    DiagCode::ResolveError,
                    format!("cyclic module import involving `{dep_name}`"),
                )
                .with_span(u.span),
            );
            continue;
        }
        if module_index.contains_key(&dep_name) {
            continue;
        }
        let Some(base_dir) = root_dir else {
            diags.push(
                Diagnostic::error(
                    DiagCode::ResolveError,
                    format!("unknown module `{dep_name}` (no search directory available)"),
                )
                .with_span(u.span),
            );
            continue;
        };
        let rel = module_path_to_rel(&u.path);
        let local_path = base_dir.join(&rel);
        let vendor_root = base_dir.join("vendor");
        let vendor_path = vendor_root.join(&rel);
        // Any import path starting with `Vendor.*` maps into `base_dir/vendor/...` and MUST
        // stay `ModuleOrigin::Vendor` (never `ModuleOrigin::Local`) so `vendor/vendor.lock`
        // SHA-256 pinning and vendor restrictions cannot be bypassed via `use Vendor.<Mod>`.
        let (chosen_path, dep_origin, vendor_rel) = if let Ok(stripped) = rel.strip_prefix("vendor")
        {
            if local_path.is_file() {
                (local_path, ModuleOrigin::Vendor, stripped.to_path_buf())
            } else if vendor_path.is_file() {
                (vendor_path, ModuleOrigin::Vendor, rel.clone())
            } else {
                diags.push(
                    Diagnostic::error(
                        DiagCode::ResolveError,
                        format!(
                            "cannot find vendored module `{dep_name}` (searched `{}` and `{}`)",
                            local_path.display(),
                            vendor_path.display()
                        ),
                    )
                    .with_span(u.span),
                );
                continue;
            }
        } else if local_path.is_file() {
            (local_path, ModuleOrigin::Local, PathBuf::new())
        } else if vendor_path.is_file() {
            (vendor_path, ModuleOrigin::Vendor, rel.clone())
        } else {
            diags.push(
                Diagnostic::error(
                    DiagCode::ResolveError,
                    format!(
                        "cannot find module `{dep_name}` (searched `{}` and `{}`)",
                        local_path.display(),
                        vendor_path.display()
                    ),
                )
                .with_span(u.span),
            );
            continue;
        };
        if dep_origin == ModuleOrigin::Vendor {
            // Reject symlinks anywhere along `vendor/<vendor_rel>` (matching `verify_vendor_dir`).
            let mut probe = vendor_root.clone();
            let mut has_symlink = fs::symlink_metadata(&probe)
                .map(|m| m.file_type().is_symlink())
                .unwrap_or(false);
            for comp in vendor_rel.components() {
                probe.push(comp);
                if fs::symlink_metadata(&probe)
                    .map(|m| m.file_type().is_symlink())
                    .unwrap_or(false)
                {
                    has_symlink = true;
                    break;
                }
            }
            if has_symlink {
                diags.push(
                    Diagnostic::error(
                        DiagCode::ResolveError,
                        format!(
                            "symlinks are forbidden inside vendor directory: `{}`",
                            chosen_path.display()
                        ),
                    )
                    .with_span(u.span),
                );
                continue;
            }
        }
        match fs::read(&chosen_path) {
            Ok(bytes) => {
                if dep_origin == ModuleOrigin::Vendor {
                    let rel_posix = crate::check::vendor::rel_path_to_posix(&vendor_rel);
                    if let Err(msg) = crate::check::vendor::verify_vendor_module(
                        &vendor_root,
                        &dep_name,
                        &rel_posix,
                        &bytes,
                    ) {
                        diags.push(
                            Diagnostic::error(DiagCode::ResolveError, msg)
                                .with_span(u.span)
                                .with_hint("run `dana vendor pin` to update vendor/vendor.lock"),
                        );
                        continue;
                    }
                }
                let dep_src = match String::from_utf8(bytes) {
                    Ok(s) => s,
                    Err(e) => {
                        diags.push(
                            Diagnostic::error(
                                DiagCode::IoError,
                                format!(
                                    "module `{}` is not valid UTF-8: {e}",
                                    chosen_path.display()
                                ),
                            )
                            .with_span(u.span),
                        );
                        continue;
                    }
                };
                let dep_fid = sm.add_file(chosen_path.display().to_string(), dep_src.clone());
                match parse_module(dep_fid, &dep_src) {
                    Ok(dep_mod) => {
                        let actual_name = join_module_path(&dep_mod.header.path);
                        if actual_name != dep_name {
                            diags.push(
                                Diagnostic::error(
                                    DiagCode::ResolveError,
                                    format!(
                                        "module path mismatch: expected `module {dep_name}`, found `module {actual_name}`"
                                    ),
                                )
                                .with_span(dep_mod.header.span),
                            );
                        }
                        load_recursive(
                            dep_name,
                            dep_fid,
                            dep_origin,
                            dep_mod,
                            root_dir,
                            sm,
                            visiting,
                            modules,
                            module_index,
                            declared_tags,
                            diags,
                        );
                    }
                    Err(d) => diags.push(d),
                }
            }
            Err(e) => diags.push(
                Diagnostic::error(
                    DiagCode::IoError,
                    format!("cannot read module `{}`: {e}", chosen_path.display()),
                )
                .with_span(u.span),
            ),
        }
    }

    let (exposed_all, exposed_names) = match &module.header.expose {
        None => (true, HashSet::new()),
        Some(ex) => {
            let mut set = HashSet::new();
            for item in &ex.items {
                match item {
                    ExposeItem::Value(n) | ExposeItem::Type(n) | ExposeItem::TypeAll(n) => {
                        set.insert(n.name.clone());
                    }
                }
            }
            (false, set)
        }
    };

    visiting.remove(&full_name);
    let idx = modules.len();
    module_index.insert(full_name.clone(), idx);
    modules.push(ResolvedModule {
        full_name,
        file_id,
        origin,
        module,
        exposed_all,
        exposed_names,
    });
}

/// Helper to check whether a module exposes a given symbol name.
#[must_use]
pub fn is_symbol_exposed(m: &ResolvedModule, name: &str) -> bool {
    m.exposed_all || m.exposed_names.contains(name)
}

/// Validate a tag name against built-in and program-declared custom tags.
#[must_use]
pub fn check_tag_declared(resolved: &ResolvedProgram, tag: &str, span: Span) -> Option<Diagnostic> {
    if resolved.is_valid_tag(tag) {
        None
    } else {
        Some(
            Diagnostic::error(
                DiagCode::PrivacyError,
                format!("undeclared sensitivity tag `[{tag}]`"),
            )
            .with_primary(span, "declare custom tags at module level with `tag name`"),
        )
    }
}
