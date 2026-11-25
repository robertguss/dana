//! Offline, deterministic, git-friendly `schema.lock` codec, tag-preserving merge,
//! and schema-drift verification.
//!
//! Format example:
//! ```text
//! version 1
//!
//! db Analytics dialect postgres
//!   table "orders"
//!     col id: Int pk
//!     col customer_email: Text tags [pii]
//!     col amount: Decimal
//!     col notes: Text?
//!   end
//! end
//! ```

use std::fmt::{self, Write as _};

use crate::core::syntax::{AggKind, ColSpec, Ident, ScalarTy, TableTy, TagSet};

use super::{DbError, SqlDialect};

/// Current `schema.lock` file format version.
pub const SCHEMA_LOCK_VERSION: u32 = 1;

/// One locked column entry inside a [`LockedTable`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LockedCol {
    pub name: Ident,
    /// Non-option base scalar type (nullability is tracked separately via `nullable`).
    pub ty: ScalarTy,
    pub nullable: bool,
    pub pk: bool,
    pub tags: TagSet,
}

impl LockedCol {
    /// Return the effective Dana [`ScalarTy`], wrapping in `ScalarTy::Option` when `nullable`.
    #[must_use]
    pub fn effective_scalar_ty(&self) -> ScalarTy {
        if self.nullable && !self.ty.is_option() {
            ScalarTy::Option(Box::new(self.ty.clone()))
        } else {
            self.ty.clone()
        }
    }

    /// Convert this locked column into a Dana [`ColSpec`].
    #[must_use]
    pub fn to_col_spec(&self) -> ColSpec {
        ColSpec {
            name: self.name.clone(),
            ty: self.effective_scalar_ty(),
            tags: self.tags.clone(),
            bucketed: false,
            agg_kind: AggKind::Raw,
        }
    }
}

/// One locked database table inside a [`LockedDb`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LockedTable {
    pub name: Ident,
    pub cols: Vec<LockedCol>,
}

impl LockedTable {
    #[must_use]
    pub fn find_col(&self, name: &str) -> Option<&LockedCol> {
        self.cols.iter().find(|c| c.name == name)
    }

    /// Convert this locked table into a Dana [`TableTy`].
    #[must_use]
    pub fn to_table_ty(&self) -> TableTy {
        TableTy {
            cols: self.cols.iter().map(LockedCol::to_col_spec).collect(),
            row_tags: TagSet::empty(),
            order_tags: TagSet::empty(),
            grouped_by: None,
            summarized: false,
            distinct_by: None,
        }
    }
}

/// One locked logical database inside a [`SchemaLock`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LockedDb {
    pub name: Ident,
    pub dialect: SqlDialect,
    pub tables: Vec<LockedTable>,
}

impl LockedDb {
    #[must_use]
    pub fn find_table(&self, name: &str) -> Option<&LockedTable> {
        self.tables.iter().find(|t| t.name == name)
    }

    /// Resolve a Dana schema or table name against this locked database:
    /// 1. Exact name match
    /// 2. Unique ASCII case-insensitive match
    /// 3. Unique `snake_case` match (e.g. `CourseEnrollment` -> `course_enrollment`)
    ///
    /// # Errors
    /// Returns [`DbError::SchemaDrift`] if no table matches or if the fuzzy match is ambiguous.
    pub fn resolve_table(&self, name: &str) -> Result<&LockedTable, DbError> {
        if let Some(exact) = self.find_table(name) {
            return Ok(exact);
        }

        let ci_matches: Vec<&LockedTable> = self
            .tables
            .iter()
            .filter(|t| t.name.eq_ignore_ascii_case(name))
            .collect();
        if ci_matches.len() == 1 {
            return Ok(ci_matches[0]);
        }
        if ci_matches.len() > 1 {
            let names: Vec<&str> = ci_matches.iter().map(|t| t.name.as_str()).collect();
            return Err(DbError::SchemaDrift(format!(
                "ambiguous case-insensitive table match for `{name}` in db `{}`: {:?}",
                self.name, names
            )));
        }

        let target_snake = to_snake_case(name);
        let snake_matches: Vec<&LockedTable> = self
            .tables
            .iter()
            .filter(|t| to_snake_case(&t.name) == target_snake)
            .collect();
        if snake_matches.len() == 1 {
            return Ok(snake_matches[0]);
        }
        if snake_matches.len() > 1 {
            let names: Vec<&str> = snake_matches.iter().map(|t| t.name.as_str()).collect();
            return Err(DbError::SchemaDrift(format!(
                "ambiguous snake_case table match for `{name}` in db `{}`: {:?}",
                self.name, names
            )));
        }

        Err(DbError::SchemaDrift(format!(
            "table `{name}` not found in schema.lock for db `{}`",
            self.name
        )))
    }
}

/// Convert `PascalCase` / `camelCase` identifiers into canonical `snake_case`.
#[must_use]
pub fn to_snake_case(name: &str) -> String {
    let mut out = String::with_capacity(name.len() + 4);
    let chars: Vec<char> = name.chars().collect();
    for (idx, &ch) in chars.iter().enumerate() {
        if ch.is_ascii_uppercase() {
            if idx > 0 {
                let prev = chars[idx - 1];
                let next_is_lower = chars.get(idx + 1).is_some_and(|n| n.is_ascii_lowercase());
                if prev != '_'
                    && (prev.is_ascii_lowercase() || prev.is_ascii_digit() || next_is_lower)
                {
                    out.push('_');
                }
            }
            out.push(ch.to_ascii_lowercase());
        } else {
            out.push(ch.to_ascii_lowercase());
        }
    }
    out
}

/// Root offline `schema.lock` document.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SchemaLock {
    pub version: u32,
    pub dbs: Vec<LockedDb>,
}

/// Alias for [`SchemaLock`] matching the Phase 3 pushdown & lockfile API.
pub type SchemaLockFile = SchemaLock;

impl Default for SchemaLock {
    fn default() -> Self {
        Self {
            version: SCHEMA_LOCK_VERSION,
            dbs: Vec::new(),
        }
    }
}

impl SchemaLock {
    #[must_use]
    pub fn find_db(&self, name: &str) -> Option<&LockedDb> {
        self.dbs.iter().find(|d| d.name == name)
    }
}

/// Summary of one column whose type or nullability changed across a `schema-sync`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ColChangeSummary {
    pub table: Ident,
    pub col: Ident,
    pub old_ty: ScalarTy,
    pub old_nullable: bool,
    pub new_ty: ScalarTy,
    pub new_nullable: bool,
}

/// Human-readable report produced by [`merge_schema_lock`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SchemaSyncReport {
    pub db_name: Ident,
    pub tables_added: Vec<Ident>,
    pub tables_removed: Vec<Ident>,
    pub cols_added: Vec<(Ident, Ident)>,
    pub cols_removed: Vec<(Ident, Ident)>,
    pub cols_changed: Vec<ColChangeSummary>,
    pub tags_preserved: usize,
}

impl fmt::Display for SchemaSyncReport {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "schema sync for db `{}`:", self.db_name)?;
        if self.tables_added.is_empty()
            && self.tables_removed.is_empty()
            && self.cols_added.is_empty()
            && self.cols_removed.is_empty()
            && self.cols_changed.is_empty()
        {
            writeln!(f, "  no structural changes")?;
        } else {
            for t in &self.tables_added {
                writeln!(f, "  + table \"{t}\"")?;
            }
            for t in &self.tables_removed {
                writeln!(f, "  - table \"{t}\"")?;
            }
            for (t, c) in &self.cols_added {
                writeln!(f, "  + col {t}.{c}")?;
            }
            for (t, c) in &self.cols_removed {
                writeln!(f, "  - col {t}.{c}")?;
            }
            for ch in &self.cols_changed {
                let old_opt = if ch.old_nullable { "?" } else { "" };
                let new_opt = if ch.new_nullable { "?" } else { "" };
                writeln!(
                    f,
                    "  ~ col {}.{}: {}{} -> {}{}",
                    ch.table,
                    ch.col,
                    format_scalar_ty(&ch.old_ty),
                    old_opt,
                    format_scalar_ty(&ch.new_ty),
                    new_opt
                )?;
            }
        }
        writeln!(f, "  sensitivity tags preserved: {}", self.tags_preserved)
    }
}

/// Format a [`SchemaLock`] into its canonical, deterministic, git-friendly text form.
#[must_use]
pub fn format_schema_lock(lock: &SchemaLock) -> String {
    let mut out = String::new();
    let _ = writeln!(out, "version {}", lock.version);

    let mut dbs: Vec<&LockedDb> = lock.dbs.iter().collect();
    dbs.sort_by(|a, b| a.name.cmp(&b.name));

    for db in dbs {
        out.push('\n');
        let _ = writeln!(out, "db {} dialect {}", db.name, db.dialect);
        let mut tables: Vec<&LockedTable> = db.tables.iter().collect();
        tables.sort_by(|a, b| a.name.cmp(&b.name));
        for tbl in tables {
            let _ = writeln!(out, "  table {}", quote_lock_string(&tbl.name));
            for col in &tbl.cols {
                let mut line = format!("    col {}: {}", col.name, format_scalar_ty(&col.ty));
                if col.nullable {
                    line.push('?');
                }
                if col.pk {
                    line.push_str(" pk");
                }
                if !col.tags.is_empty() {
                    let _ = write!(line, " tags [{}]", col.tags.elems().join(", "));
                }
                out.push_str(&line);
                out.push('\n');
            }
            out.push_str("  end\n");
        }
        out.push_str("end\n");
    }
    out
}

/// Parse a `schema.lock` text document into a [`SchemaLock`].
///
/// # Errors
/// Returns [`DbError::LockParse`] on syntax errors, unsupported versions, or unclosed blocks.
pub fn parse_schema_lock(src: &str) -> Result<SchemaLock, DbError> {
    let mut version: Option<u32> = None;
    let mut dbs: Vec<LockedDb> = Vec::new();
    let mut cur_db: Option<LockedDb> = None;
    let mut cur_table: Option<LockedTable> = None;

    for (idx, raw_line) in src.lines().enumerate() {
        let line_no = idx + 1;
        let line = raw_line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }

        if let Some(rest) = line.strip_prefix("version ") {
            if version.is_some() || cur_db.is_some() {
                return Err(DbError::LockParse(format!(
                    "line {line_no}: unexpected `version` declaration"
                )));
            }
            let v: u32 = rest.trim().parse().map_err(|_| {
                DbError::LockParse(format!("line {line_no}: invalid version `{}`", rest.trim()))
            })?;
            if v != SCHEMA_LOCK_VERSION {
                return Err(DbError::LockParse(format!(
                    "line {line_no}: unsupported schema.lock version {v} (expected {SCHEMA_LOCK_VERSION})"
                )));
            }
            version = Some(v);
            continue;
        }

        if version.is_none() {
            return Err(DbError::LockParse(format!(
                "line {line_no}: expected `version {SCHEMA_LOCK_VERSION}` header before `{line}`"
            )));
        }

        if line == "end" {
            if let Some(tbl) = cur_table.take() {
                let db = cur_db.as_mut().ok_or_else(|| {
                    DbError::LockParse(format!("line {line_no}: internal parser state error"))
                })?;
                if db.tables.iter().any(|t| t.name == tbl.name) {
                    return Err(DbError::LockParse(format!(
                        "line {line_no}: duplicate table `{}` in db `{}`",
                        tbl.name, db.name
                    )));
                }
                db.tables.push(tbl);
            } else if let Some(db) = cur_db.take() {
                if dbs.iter().any(|d| d.name == db.name) {
                    return Err(DbError::LockParse(format!(
                        "line {line_no}: duplicate db `{}`",
                        db.name
                    )));
                }
                dbs.push(db);
            } else {
                return Err(DbError::LockParse(format!(
                    "line {line_no}: unexpected `end` with no open block"
                )));
            }
            continue;
        }

        if let Some(rest) = line.strip_prefix("db ") {
            if cur_db.is_some() {
                return Err(DbError::LockParse(format!(
                    "line {line_no}: nested `db` block is not allowed"
                )));
            }
            let parts: Vec<&str> = rest.split_whitespace().collect();
            if parts.len() != 3 || parts[1] != "dialect" {
                return Err(DbError::LockParse(format!(
                    "line {line_no}: expected `db <Name> dialect <sqlite|postgres>`"
                )));
            }
            let dialect = match parts[2] {
                "sqlite" => SqlDialect::Sqlite,
                "postgres" => SqlDialect::Postgres,
                other => {
                    return Err(DbError::LockParse(format!(
                        "line {line_no}: unknown dialect `{other}`"
                    )));
                }
            };
            cur_db = Some(LockedDb {
                name: parts[0].to_string(),
                dialect,
                tables: Vec::new(),
            });
            continue;
        }

        if let Some(rest) = line.strip_prefix("table ") {
            if cur_db.is_none() || cur_table.is_some() {
                return Err(DbError::LockParse(format!(
                    "line {line_no}: `table` must appear directly inside a `db` block"
                )));
            }
            let name = parse_lock_table_name(rest.trim(), line_no)?;
            cur_table = Some(LockedTable {
                name,
                cols: Vec::new(),
            });
            continue;
        }

        if let Some(rest) = line.strip_prefix("col ") {
            let tbl = cur_table.as_mut().ok_or_else(|| {
                DbError::LockParse(format!(
                    "line {line_no}: `col` must appear inside a `table` block"
                ))
            })?;
            let col = parse_locked_col(rest.trim(), line_no)?;
            if tbl.cols.iter().any(|c| c.name == col.name) {
                return Err(DbError::LockParse(format!(
                    "line {line_no}: duplicate column `{}` in table `{}`",
                    col.name, tbl.name
                )));
            }
            tbl.cols.push(col);
            continue;
        }

        return Err(DbError::LockParse(format!(
            "line {line_no}: unrecognized schema.lock directive `{line}`"
        )));
    }

    if cur_table.is_some() || cur_db.is_some() {
        return Err(DbError::LockParse(
            "unexpected EOF: unclosed `db` or `table` block (missing `end`)".to_string(),
        ));
    }

    let version = version.ok_or_else(|| {
        DbError::LockParse(format!(
            "empty schema.lock: missing `version {SCHEMA_LOCK_VERSION}` header"
        ))
    })?;

    Ok(SchemaLock { version, dbs })
}

/// Merge a freshly introspected [`LockedDb`] into an existing [`SchemaLock`], preserving
/// human-authored sensitivity tags on matching `(table, column)` entries and returning a
/// structured [`SchemaSyncReport`].
#[must_use]
pub fn merge_schema_lock(
    existing: &SchemaLock,
    fresh: &LockedDb,
) -> (SchemaLock, SchemaSyncReport) {
    let old_db = existing.find_db(&fresh.name);

    let mut tables_added = Vec::new();
    let mut tables_removed = Vec::new();
    let mut cols_added = Vec::new();
    let mut cols_removed = Vec::new();
    let mut cols_changed = Vec::new();
    let mut tags_preserved = 0usize;

    let mut merged_tables = Vec::with_capacity(fresh.tables.len());

    if let Some(prev_db) = old_db {
        for prev_tbl in &prev_db.tables {
            if fresh.find_table(&prev_tbl.name).is_none() {
                tables_removed.push(prev_tbl.name.clone());
            }
        }
    }

    for fresh_tbl in &fresh.tables {
        let prev_tbl = old_db.and_then(|d| d.find_table(&fresh_tbl.name));
        if prev_tbl.is_none() {
            tables_added.push(fresh_tbl.name.clone());
        }
        if let Some(pt) = prev_tbl {
            for prev_col in &pt.cols {
                if fresh_tbl.find_col(&prev_col.name).is_none() {
                    cols_removed.push((fresh_tbl.name.clone(), prev_col.name.clone()));
                }
            }
        }

        let mut merged_cols = Vec::with_capacity(fresh_tbl.cols.len());
        for fresh_col in &fresh_tbl.cols {
            let mut col = fresh_col.clone();
            if let Some(pt) = prev_tbl {
                match pt.find_col(&fresh_col.name) {
                    None => {
                        cols_added.push((fresh_tbl.name.clone(), fresh_col.name.clone()));
                    }
                    Some(prev_col) => {
                        if !prev_col.tags.is_empty() {
                            col.tags = prev_col.tags.union(&fresh_col.tags);
                            tags_preserved += prev_col.tags.elems().len();
                        }
                        if prev_col.ty != fresh_col.ty || prev_col.nullable != fresh_col.nullable {
                            cols_changed.push(ColChangeSummary {
                                table: fresh_tbl.name.clone(),
                                col: fresh_col.name.clone(),
                                old_ty: prev_col.ty.clone(),
                                old_nullable: prev_col.nullable,
                                new_ty: fresh_col.ty.clone(),
                                new_nullable: fresh_col.nullable,
                            });
                        }
                    }
                }
            }
            merged_cols.push(col);
        }
        merged_tables.push(LockedTable {
            name: fresh_tbl.name.clone(),
            cols: merged_cols,
        });
    }

    merged_tables.sort_by(|a, b| a.name.cmp(&b.name));
    tables_added.sort();
    tables_removed.sort();

    let merged_db = LockedDb {
        name: fresh.name.clone(),
        dialect: fresh.dialect,
        tables: merged_tables,
    };

    let mut dbs: Vec<LockedDb> = existing
        .dbs
        .iter()
        .filter(|d| d.name != fresh.name)
        .cloned()
        .collect();
    dbs.push(merged_db);
    dbs.sort_by(|a, b| a.name.cmp(&b.name));

    let next_lock = SchemaLock {
        version: existing.version,
        dbs,
    };
    let report = SchemaSyncReport {
        db_name: fresh.name.clone(),
        tables_added,
        tables_removed,
        cols_added,
        cols_removed,
        cols_changed,
        tags_preserved,
    };
    (next_lock, report)
}

/// Verify that a Dana [`TableTy`] matches the locked schema for `(db_name, table_name)`.
///
/// Checks:
/// 1. `db_name` and `table_name` exist in `lock`.
/// 2. Every column in `expected` exists in the locked table with an identical effective [`ScalarTy`].
/// 3. Privacy monotonicity: every sensitivity tag locked on a column is present on the corresponding
///    column in `expected` (`locked_col.tags ⊆ expected_col.tags`).
///
/// # Errors
/// Returns [`DbError::SchemaDrift`] describing the exact mismatch.
pub fn verify_table_against_lock(
    lock: &SchemaLock,
    db_name: &str,
    table_name: &str,
    expected: &TableTy,
) -> Result<(), DbError> {
    let db = lock.find_db(db_name).ok_or_else(|| {
        DbError::SchemaDrift(format!("database `{db_name}` not found in schema.lock"))
    })?;
    let tbl = db.find_table(table_name).ok_or_else(|| {
        DbError::SchemaDrift(format!(
            "table `{table_name}` not found in schema.lock for db `{db_name}`"
        ))
    })?;

    for col in &expected.cols {
        let Some(locked_col) = tbl.find_col(&col.name) else {
            return Err(DbError::SchemaDrift(format!(
                "column `{}.{}` missing from schema.lock for db `{db_name}`",
                table_name, col.name
            )));
        };
        let locked_ty = locked_col.effective_scalar_ty();
        if locked_ty != col.ty {
            return Err(DbError::SchemaDrift(format!(
                "column `{}.{}` type drift: schema.lock has `{:?}`, code expects `{:?}`",
                table_name, col.name, locked_ty, col.ty
            )));
        }
        if !locked_col.tags.is_subset(&col.tags) {
            let missing = locked_col.tags.diff(&col.tags);
            return Err(DbError::SchemaDrift(format!(
                "column `{}.{}` dropped locked sensitivity tags [{}]",
                table_name,
                col.name,
                missing.elems().join(", ")
            )));
        }
    }
    Ok(())
}

fn quote_lock_string(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for ch in s.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

fn parse_lock_table_name(raw: &str, line_no: usize) -> Result<String, DbError> {
    if let Some(inner) = raw.strip_prefix('"') {
        let Some(body) = inner.strip_suffix('"') else {
            return Err(DbError::LockParse(format!(
                "line {line_no}: unterminated quoted table name `{raw}`"
            )));
        };
        let mut out = String::with_capacity(body.len());
        let mut chars = body.chars();
        while let Some(c) = chars.next() {
            if c == '\\' {
                match chars.next() {
                    Some('"') => out.push('"'),
                    Some('\\') => out.push('\\'),
                    Some(other) => {
                        return Err(DbError::LockParse(format!(
                            "line {line_no}: invalid escape `\\{other}` in table name"
                        )));
                    }
                    None => {
                        return Err(DbError::LockParse(format!(
                            "line {line_no}: trailing backslash in table name"
                        )));
                    }
                }
            } else {
                out.push(c);
            }
        }
        if out.is_empty() {
            return Err(DbError::LockParse(format!(
                "line {line_no}: empty table name"
            )));
        }
        Ok(out)
    } else if !raw.is_empty() && !raw.contains(char::is_whitespace) {
        Ok(raw.to_string())
    } else {
        Err(DbError::LockParse(format!(
            "line {line_no}: invalid table name `{raw}`"
        )))
    }
}

fn parse_locked_col(rest: &str, line_no: usize) -> Result<LockedCol, DbError> {
    let (name_part, spec_part) = rest.split_once(':').ok_or_else(|| {
        DbError::LockParse(format!(
            "line {line_no}: expected `col <name>: <Type>[?] [pk] [tags [...]]`"
        ))
    })?;
    let name = name_part.trim();
    if name.is_empty() || name.contains(char::is_whitespace) {
        return Err(DbError::LockParse(format!(
            "line {line_no}: invalid column name `{name}`"
        )));
    }

    let spec = spec_part.trim();
    let (before_tags, tags) = if let Some(tag_idx) = spec.find("tags") {
        let before = spec[..tag_idx].trim();
        let after = spec[tag_idx + 4..].trim();
        let parsed_tags = parse_tag_list(after, line_no)?;
        (before, parsed_tags)
    } else {
        (spec, TagSet::empty())
    };

    let tokens: Vec<&str> = before_tags.split_whitespace().collect();
    if tokens.is_empty() || tokens.len() > 2 {
        return Err(DbError::LockParse(format!(
            "line {line_no}: malformed column specification `{spec}`"
        )));
    }
    let pk = if tokens.len() == 2 {
        if tokens[1] == "pk" {
            true
        } else {
            return Err(DbError::LockParse(format!(
                "line {line_no}: unexpected column modifier `{}` (expected `pk`)",
                tokens[1]
            )));
        }
    } else {
        false
    };

    let raw_ty = tokens[0];
    let (base_ty_str, nullable) = match raw_ty.strip_suffix('?') {
        Some(b) => (b, true),
        None => (raw_ty, false),
    };
    let ty = parse_scalar_ty(base_ty_str, line_no)?;

    Ok(LockedCol {
        name: name.to_string(),
        ty,
        nullable,
        pk,
        tags,
    })
}

fn parse_tag_list(raw: &str, line_no: usize) -> Result<TagSet, DbError> {
    let inner = raw
        .strip_prefix('[')
        .and_then(|s| s.strip_suffix(']'))
        .ok_or_else(|| {
            DbError::LockParse(format!(
                "line {line_no}: expected `tags [t1, t2]` but got `{raw}`"
            ))
        })?;
    let mut tags = Vec::new();
    for item in inner.split(',') {
        let t = item.trim();
        if !t.is_empty() {
            if t.contains(char::is_whitespace) {
                return Err(DbError::LockParse(format!(
                    "line {line_no}: invalid tag `{t}`"
                )));
            }
            tags.push(t.to_string());
        }
    }
    Ok(TagSet::of_list(tags))
}

fn format_scalar_ty(ty: &ScalarTy) -> String {
    match ty {
        ScalarTy::Unit => "Unit".to_string(),
        ScalarTy::Bool => "Bool".to_string(),
        ScalarTy::Int => "Int".to_string(),
        ScalarTy::Decimal => "Decimal".to_string(),
        ScalarTy::Float => "Float".to_string(),
        ScalarTy::Text => "Text".to_string(),
        ScalarTy::Bytes => "Bytes".to_string(),
        ScalarTy::Date => "Date".to_string(),
        ScalarTy::Timestamp => "Timestamp".to_string(),
        ScalarTy::Duration => "Duration".to_string(),
        ScalarTy::Data(name) => format!("Data({name})"),
        ScalarTy::Option(inner) => format!("{}?", format_scalar_ty(inner)),
    }
}

fn parse_scalar_ty(raw: &str, line_no: usize) -> Result<ScalarTy, DbError> {
    match raw {
        "Unit" => Ok(ScalarTy::Unit),
        "Bool" => Ok(ScalarTy::Bool),
        "Int" => Ok(ScalarTy::Int),
        "Decimal" => Ok(ScalarTy::Decimal),
        "Float" => Ok(ScalarTy::Float),
        "Text" => Ok(ScalarTy::Text),
        "Bytes" => Ok(ScalarTy::Bytes),
        "Date" => Ok(ScalarTy::Date),
        "Timestamp" => Ok(ScalarTy::Timestamp),
        "Duration" => Ok(ScalarTy::Duration),
        other => {
            if let Some(name) = other
                .strip_prefix("Data(")
                .and_then(|s| s.strip_suffix(')'))
                && !name.is_empty()
            {
                return Ok(ScalarTy::Data(name.to_string()));
            }
            Err(DbError::LockParse(format!(
                "line {line_no}: unknown scalar type `{other}`"
            )))
        }
    }
}
