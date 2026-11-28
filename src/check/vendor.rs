//! SHA-256 hash-pinned vendored module lockfile (`vendor/vendor.lock`) support.
//!
//! Canonical `vendor/vendor.lock` format:
//! ```text
//! # Dana vendored module SHA-256 lockfile
//! version 1
//! module <Module.Path> path "<rel_posix_path>" sha256 "<64_lowercase_hex>"
//! ```
//!
//! Compiles under `#[forbid(unsafe_code)]` via `src/lib.rs`, reusing Dana's pure-Rust
//! FIPS 180-4 SHA-256 implementation in [`crate::formats::crypto`].

use std::collections::{BTreeMap, HashMap, HashSet};
use std::fmt::Write as _;
use std::fs;
use std::path::{Component, Path};

use crate::base::FileId;
use crate::check::resolve::{cap_segment_to_kebab, join_module_path};
use crate::formats::crypto::{sha256, to_hex_lower};
use crate::syntax::parse_module;

/// Name of the lockfile stored inside a `vendor/` directory.
pub const VENDOR_LOCK_FILENAME: &str = "vendor.lock";

/// Single hash-pinned module record in `vendor/vendor.lock`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VendorEntry {
    pub module: String,
    pub path: String,
    pub sha256: String,
}

/// Parsed representation of `vendor/vendor.lock`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VendorLock {
    pub version: u32,
    pub entries: Vec<VendorEntry>,
}

impl Default for VendorLock {
    fn default() -> Self {
        Self {
            version: 1,
            entries: Vec::new(),
        }
    }
}

/// Compute lowercase 64-character hexadecimal SHA-256 digest of `bytes`.
#[must_use]
pub fn sha256_hex(bytes: &[u8]) -> String {
    to_hex_lower(&sha256(bytes))
}

/// Return the expected relative POSIX path under `vendor/` for `module_name` (`TextNorm` -> `"text-norm.dana"`,
/// `Util.TextNorm` -> `"util/text-norm.dana"`), matching `use <Module>` resolution rules.
#[must_use]
pub fn expected_vendor_module_rel_path(module_name: &str) -> String {
    let segs: Vec<&str> = module_name.split('.').collect();
    let mut parts = Vec::with_capacity(segs.len());
    for (idx, seg) in segs.iter().enumerate() {
        let kebab = cap_segment_to_kebab(seg);
        if idx + 1 == segs.len() {
            parts.push(format!("{kebab}.dana"));
        } else {
            parts.push(kebab);
        }
    }
    parts.join("/")
}

/// Convert a relative [`Path`] into canonical POSIX slash-separated form (`a/b/c.dana`).
#[must_use]
pub fn rel_path_to_posix(rel: &Path) -> String {
    let mut parts = Vec::new();
    for comp in rel.components() {
        if let Component::Normal(os) = comp {
            parts.push(os.to_string_lossy().into_owned());
        }
    }
    parts.join("/")
}

fn is_valid_module_path(name: &str) -> bool {
    if name.is_empty() {
        return false;
    }
    name.split('.').all(|seg| {
        let mut chars = seg.chars();
        let Some(first) = chars.next() else {
            return false;
        };
        first.is_ascii_uppercase() && chars.all(|c| c.is_ascii_alphanumeric() || c == '_')
    })
}

fn is_safe_vendor_rel_path(path: &str) -> bool {
    if path.is_empty()
        || path.starts_with('/')
        || path.contains('\\')
        || path.contains('\0')
        || !path.ends_with(".dana")
    {
        return false;
    }
    path.split('/')
        .all(|seg| !seg.is_empty() && seg != "." && seg != "..")
}

fn is_valid_sha256_hex(hex: &str) -> bool {
    hex.len() == 64
        && hex
            .bytes()
            .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
}

fn strip_lock_comment(line: &str) -> &str {
    let mut in_quotes = false;
    let mut escaped = false;
    for (idx, ch) in line.char_indices() {
        if escaped {
            escaped = false;
            continue;
        }
        if in_quotes {
            if ch == '\\' {
                escaped = true;
            } else if ch == '"' {
                in_quotes = false;
            }
        } else if ch == '"' {
            in_quotes = true;
        } else if ch == '#' {
            return &line[..idx];
        }
    }
    line
}

fn parse_quoted_str(s: &str, line_no: usize) -> Result<(String, &str), String> {
    let Some(rest) = s.strip_prefix('"') else {
        return Err(format!(
            "line {line_no}: expected quoted string, found `{s}`"
        ));
    };
    let mut out = String::new();
    let mut escaped = false;
    for (idx, ch) in rest.char_indices() {
        if escaped {
            match ch {
                '"' => out.push('"'),
                '\\' => out.push('\\'),
                'n' => out.push('\n'),
                't' => out.push('\t'),
                other => out.push(other),
            }
            escaped = false;
            continue;
        }
        if ch == '\\' {
            escaped = true;
            continue;
        }
        if ch == '"' {
            return Ok((out, &rest[idx + 1..]));
        }
        out.push(ch);
    }
    Err(format!("line {line_no}: unterminated quoted string"))
}

fn escape_quoted_str(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for ch in s.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\t' => out.push_str("\\t"),
            c => out.push(c),
        }
    }
    out
}

/// Parse canonical `vendor/vendor.lock` text into a [`VendorLock`].
///
/// # Errors
/// Returns an error description on syntax errors, missing/unsupported version, invalid
/// paths or SHA-256 digests, or duplicate module/path entries.
pub fn parse_vendor_lock(src: &str) -> Result<VendorLock, String> {
    let mut version: Option<u32> = None;
    let mut entries = Vec::new();
    let mut seen_modules = HashSet::new();
    let mut seen_paths = HashSet::new();

    for (idx, raw_line) in src.lines().enumerate() {
        let line_no = idx + 1;
        let line = strip_lock_comment(raw_line.trim_end_matches('\r')).trim();
        if line.is_empty() {
            continue;
        }
        if let Some(rest) = line.strip_prefix("version")
            && rest.starts_with(char::is_whitespace)
        {
            let ver_str = rest.trim();
            let v: u32 = ver_str
                .parse()
                .map_err(|_| format!("line {line_no}: invalid vendor.lock version `{ver_str}`"))?;
            if v != 1 {
                return Err(format!(
                    "line {line_no}: unsupported vendor.lock version `{v}` (expected `1`)"
                ));
            }
            if version.is_some() {
                return Err(format!("line {line_no}: duplicate `version` declaration"));
            }
            version = Some(v);
            continue;
        }
        if let Some(rest) = line.strip_prefix("module")
            && rest.starts_with(char::is_whitespace)
        {
            let rest = rest.trim_start();
            let Some(ws_idx) = rest.find(char::is_whitespace) else {
                return Err(format!(
                    "line {line_no}: expected `path \"...\" sha256 \"...\"` after module name"
                ));
            };
            let module = &rest[..ws_idx];
            if !is_valid_module_path(module) {
                return Err(format!(
                    "line {line_no}: invalid module path `{module}` in vendor.lock"
                ));
            }
            let after_mod = rest[ws_idx..].trim_start();
            let Some(after_path_kw) = after_mod
                .strip_prefix("path")
                .filter(|r| r.starts_with(char::is_whitespace))
            else {
                return Err(format!(
                    "line {line_no}: expected `path \"...\"` after `module {module}`"
                ));
            };
            let (path, tail1) = parse_quoted_str(after_path_kw.trim_start(), line_no)?;
            if !is_safe_vendor_rel_path(&path) {
                return Err(format!(
                    "line {line_no}: unsafe or invalid vendored module path `{path}`"
                ));
            }
            let tail1 = tail1.trim_start();
            let Some(after_sha_kw) = tail1
                .strip_prefix("sha256")
                .filter(|r| r.starts_with(char::is_whitespace))
            else {
                return Err(format!(
                    "line {line_no}: expected `sha256 \"...\"` after path for `{module}`"
                ));
            };
            let (sha256, tail2) = parse_quoted_str(after_sha_kw.trim_start(), line_no)?;
            if !tail2.trim().is_empty() {
                return Err(format!(
                    "line {line_no}: unexpected trailing tokens `{}`",
                    tail2.trim()
                ));
            }
            if !is_valid_sha256_hex(&sha256) {
                return Err(format!(
                    "line {line_no}: invalid SHA-256 hex digest `{sha256}` (expected 64 lowercase hex chars)"
                ));
            }
            if !seen_modules.insert(module.to_string()) {
                return Err(format!(
                    "line {line_no}: duplicate vendored module `{module}` in vendor.lock"
                ));
            }
            if !seen_paths.insert(path.clone()) {
                return Err(format!(
                    "line {line_no}: duplicate vendored path `{path}` in vendor.lock"
                ));
            }
            entries.push(VendorEntry {
                module: module.to_string(),
                path,
                sha256,
            });
            continue;
        }
        return Err(format!(
            "line {line_no}: unrecognized vendor.lock statement `{line}`"
        ));
    }

    let Some(ver) = version else {
        return Err("vendor.lock must declare `version 1`".to_string());
    };
    Ok(VendorLock {
        version: ver,
        entries,
    })
}

/// Format a [`VendorLock`] canonically in deterministic sorted order.
#[must_use]
pub fn format_vendor_lock(lock: &VendorLock) -> String {
    let mut entries = lock.entries.clone();
    entries.sort_by(|a, b| a.module.cmp(&b.module).then_with(|| a.path.cmp(&b.path)));
    let mut out = String::new();
    out.push_str("# Dana vendored module SHA-256 lockfile\n");
    let _ = writeln!(out, "version {}", lock.version);
    for e in &entries {
        let _ = writeln!(
            out,
            "module {} path \"{}\" sha256 \"{}\"",
            e.module,
            escape_quoted_str(&e.path),
            e.sha256
        );
    }
    out
}

fn collect_dana_files_recursive(
    root: &Path,
    dir: &Path,
    out: &mut Vec<(String, std::path::PathBuf)>,
) -> Result<(), String> {
    let entries = fs::read_dir(dir)
        .map_err(|e| format!("cannot read vendor directory `{}`: {e}", dir.display()))?;
    for entry in entries {
        let entry = entry.map_err(|e| format!("cannot inspect `{}`: {e}", dir.display()))?;
        let path = entry.path();
        let file_type = entry
            .file_type()
            .map_err(|e| format!("cannot stat `{}`: {e}", path.display()))?;
        if file_type.is_symlink() {
            return Err(format!(
                "symlinks are forbidden inside vendor directory: `{}`",
                path.display()
            ));
        }
        if file_type.is_dir() {
            collect_dana_files_recursive(root, &path, out)?;
        } else if file_type.is_file() && path.extension().and_then(|s| s.to_str()) == Some("dana") {
            let rel = path.strip_prefix(root).map_err(|e| {
                format!(
                    "cannot compute relative path for `{}` under `{}`: {e}",
                    path.display(),
                    root.display()
                )
            })?;
            out.push((rel_path_to_posix(rel), path));
        }
    }
    Ok(())
}

/// Recursively scan `.dana` files in `vendor_dir`, parse each module's `module <Name>` header,
/// compute exact SHA-256 digests, and write canonical `vendor/vendor.lock`.
///
/// Returns `(lock, pinned_rel_paths)` sorted deterministically.
///
/// # Errors
/// Returns an error string if `vendor_dir` cannot be read, any `.dana` module fails to parse,
/// duplicate module names exist, or `vendor.lock` cannot be written.
pub fn pin_vendor_dir(vendor_dir: &Path) -> Result<(VendorLock, Vec<String>), String> {
    if !vendor_dir.is_dir() {
        return Err(format!(
            "vendor directory `{}` does not exist or is not a directory",
            vendor_dir.display()
        ));
    }
    let mut files = Vec::new();
    collect_dana_files_recursive(vendor_dir, vendor_dir, &mut files)?;
    files.sort_by(|a, b| a.0.cmp(&b.0));

    let mut entries = Vec::with_capacity(files.len());
    let mut seen_modules: HashMap<String, String> = HashMap::new();

    for (rel_posix, full_path) in &files {
        let bytes = fs::read(full_path)
            .map_err(|e| format!("cannot read `{}`: {e}", full_path.display()))?;
        let src = std::str::from_utf8(&bytes)
            .map_err(|e| format!("vendored module `{rel_posix}` is not valid UTF-8: {e}"))?;
        let parsed = parse_module(FileId(0), src).map_err(|d| {
            format!(
                "cannot parse vendored module `{rel_posix}`: {}",
                d.message()
            )
        })?;
        let mod_name = join_module_path(&parsed.header.path);
        if let Some(prev_path) = seen_modules.insert(mod_name.clone(), rel_posix.clone()) {
            return Err(format!(
                "duplicate vendored module `{mod_name}` in `{prev_path}` and `{rel_posix}`"
            ));
        }
        let digest = sha256_hex(&bytes);
        entries.push(VendorEntry {
            module: mod_name,
            path: rel_posix.clone(),
            sha256: digest,
        });
    }

    entries.sort_by(|a, b| a.module.cmp(&b.module).then_with(|| a.path.cmp(&b.path)));
    let lock = VendorLock {
        version: 1,
        entries,
    };
    let rendered = format_vendor_lock(&lock);
    let lock_path = vendor_dir.join(VENDOR_LOCK_FILENAME);
    fs::write(&lock_path, rendered)
        .map_err(|e| format!("cannot write `{}`: {e}", lock_path.display()))?;

    let mut pinned_paths: Vec<String> = lock.entries.iter().map(|e| e.path.clone()).collect();
    pinned_paths.sort();
    Ok((lock, pinned_paths))
}

/// Verify `vendor/vendor.lock` offline against every `.dana` file in `vendor_dir`.
///
/// Checks that:
/// 1. `vendor/vendor.lock` exists and parses cleanly;
/// 2. Every pinned file exists on disk with matching exact SHA-256 digest and module header;
/// 3. No unpinned `.dana` files exist anywhere under `vendor_dir`.
///
/// # Errors
/// Returns a non-empty list of verification failure messages.
pub fn verify_vendor_dir(vendor_dir: &Path) -> Result<Vec<String>, Vec<String>> {
    if !vendor_dir.is_dir() {
        return Err(vec![format!(
            "vendor directory `{}` does not exist or is not a directory",
            vendor_dir.display()
        )]);
    }
    let lock_path = vendor_dir.join(VENDOR_LOCK_FILENAME);
    let lock_src = match fs::read_to_string(&lock_path) {
        Ok(s) => s,
        Err(e) => {
            return Err(vec![format!(
                "cannot read `{}`: {e} (run `dana vendor pin` to create it)",
                lock_path.display()
            )]);
        }
    };
    let lock = match parse_vendor_lock(&lock_src) {
        Ok(l) => l,
        Err(e) => {
            return Err(vec![format!("invalid `{}`: {e}", lock_path.display())]);
        }
    };

    let mut disk_files = Vec::new();
    if let Err(e) = collect_dana_files_recursive(vendor_dir, vendor_dir, &mut disk_files) {
        return Err(vec![e]);
    }
    let disk_map: BTreeMap<String, std::path::PathBuf> = disk_files.into_iter().collect();

    let mut errors = Vec::new();
    let mut pinned_paths = HashSet::new();
    let mut verified_paths = Vec::new();

    for entry in &lock.entries {
        pinned_paths.insert(entry.path.clone());
        let Some(full_path) = disk_map.get(&entry.path) else {
            errors.push(format!(
                "missing pinned vendored module `{}` (`{}`)",
                entry.module, entry.path
            ));
            continue;
        };
        let bytes = match fs::read(full_path) {
            Ok(b) => b,
            Err(e) => {
                errors.push(format!("cannot read `{}`: {e}", full_path.display()));
                continue;
            }
        };
        let actual_sha = sha256_hex(&bytes);
        if actual_sha != entry.sha256 {
            errors.push(format!(
                "SHA-256 hash mismatch for vendored module `{}` (`{}`): expected `{}`, got `{}`",
                entry.module, entry.path, entry.sha256, actual_sha
            ));
            continue;
        }
        match std::str::from_utf8(&bytes)
            .map_err(|e| format!("invalid UTF-8: {e}"))
            .and_then(|s| parse_module(FileId(0), s).map_err(|d| d.message().to_string()))
        {
            Ok(parsed) => {
                let actual_mod = join_module_path(&parsed.header.path);
                if actual_mod != entry.module {
                    errors.push(format!(
                        "module header mismatch for `{}`: lockfile expects `{}`, file declares `{}`",
                        entry.path, entry.module, actual_mod
                    ));
                    continue;
                }
            }
            Err(e) => {
                errors.push(format!(
                    "cannot parse vendored module `{}`: {e}",
                    entry.path
                ));
                continue;
            }
        }
        verified_paths.push(entry.path.clone());
    }

    for disk_rel in disk_map.keys() {
        if !pinned_paths.contains(disk_rel) {
            errors.push(format!(
                "unpinned vendored module `{disk_rel}` in `{}` (run `dana vendor pin`)",
                vendor_dir.display()
            ));
        }
    }

    if !errors.is_empty() {
        return Err(errors);
    }
    verified_paths.sort();
    Ok(verified_paths)
}

/// Verify a single vendored module's exact raw `bytes` against `vendor_dir/vendor.lock`.
///
/// Called automatically by the module resolver before loading any `ModuleOrigin::Vendor` import.
///
/// # Errors
/// Returns an explanatory error string on missing `vendor.lock`, malformed lockfile, unpinned
/// module/path, or SHA-256 hash mismatch.
pub fn verify_vendor_module(
    vendor_dir: &Path,
    expected_module: &str,
    rel_path: &str,
    bytes: &[u8],
) -> Result<(), String> {
    let lock_path = vendor_dir.join(VENDOR_LOCK_FILENAME);
    let lock_src = fs::read_to_string(&lock_path).map_err(|_| {
        format!(
            "missing `{}` required to verify vendored module `{expected_module}` (`{rel_path}`)",
            lock_path.display()
        )
    })?;
    let lock = parse_vendor_lock(&lock_src)
        .map_err(|e| format!("invalid `{}`: {e}", lock_path.display()))?;

    let Some(entry) = lock.entries.iter().find(|e| e.module == expected_module) else {
        return Err(format!(
            "vendored module `{expected_module}` (`{rel_path}`) is not pinned in `{}`",
            lock_path.display()
        ));
    };
    if entry.path != rel_path {
        return Err(format!(
            "vendored module `{expected_module}` path mismatch in `{}`: expected `{}`, found `{rel_path}`",
            lock_path.display(),
            entry.path
        ));
    }
    let actual = sha256_hex(bytes);
    if actual != entry.sha256 {
        return Err(format!(
            "SHA-256 hash mismatch for vendored module `{expected_module}` (`{rel_path}`): expected `{}`, got `{actual}`",
            entry.sha256
        ));
    }
    Ok(())
}
