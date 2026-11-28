//! Safe SQLite database driver implementing [`DbConnection`] over [`crate::ffi::sqlite`].
//!
//! Compiled strictly under `#[forbid(unsafe_code)]`. Supports:
//! - Lossless Dana <-> SQLite scalar & `Option(T)` codecs (including 18-digit exact `Decimal`;
//!   declare columns as `DECIMAL_TEXT` or `TEXT` in SQLite DDL to avoid SQLite's `NUMERIC`
//!   affinity coercing >15-digit text values to IEEE-754 `REAL`)
//! - Strict column count & storage-class schema-drift verification
//! - Direct 2,048-row columnar batch streaming into [`VmTable`]
//! - `sqlite_master` + `PRAGMA table_info` schema introspection into [`LockedDb`]
//! - Transactional parameterized `upsert_table` and strictly read-only `dry_run` diffs.

use crate::core::bigint::BigInt;
use crate::core::syntax::{Float64, ScalarTy, TableTy, TagSet};
use crate::ffi::sqlite::{
    SqliteConn, SqliteFfiError, SqliteOpenMode, SqliteStmt, SqliteValueType, StepResult,
};
use crate::formats::time::{
    format_iso_date, format_iso_timestamp, parse_decimal_bigint_strict, parse_iso_date,
};
use crate::oracle::value::{TableVal, Val};
use crate::vm::ops::VmTable;

use super::schema_lock::{LockedCol, LockedDb, LockedTable};
use super::{
    ColumnarBatchBuilder, DbConnection, DbError, SqlDialect, SqlParam, SqliteUri, UpsertDiff,
    compute_upsert_diff, decimal_from_i64, format_decimal_canonical, make_table_row,
    parse_decimal_from_f64, parse_iso_timestamp_flexible, quote_sql_ident, quote_sql_table_ref,
    validate_sqlite_attach_schema,
};

/// Safe SQLite driver implementing [`DbConnection`].
#[derive(Debug)]
pub struct SqliteDriver {
    conn: SqliteConn,
    attached_schemas: Vec<String>,
}

impl SqliteDriver {
    /// Open a SQLite database from a parsed [`SqliteUri`].
    ///
    /// # Errors
    /// Returns [`DbError::Connection`] if opening or attaching secondary databases fails.
    pub fn open(uri: &SqliteUri) -> Result<Self, DbError> {
        let mode = if uri.read_only {
            SqliteOpenMode::ReadOnly
        } else {
            SqliteOpenMode::ReadWriteCreate
        };
        let conn = SqliteConn::open(&uri.path, mode).map_err(map_conn_err)?;
        let mut driver = Self {
            conn,
            attached_schemas: Vec::new(),
        };
        for (schema, path) in &uri.attachments {
            driver.attach_database(schema, path)?;
        }
        Ok(driver)
    }

    /// Open a fresh private in-memory SQLite database.
    ///
    /// # Errors
    /// Returns [`DbError::Connection`] if opening fails.
    pub fn open_in_memory() -> Result<Self, DbError> {
        let conn = SqliteConn::open_in_memory().map_err(map_conn_err)?;
        Ok(Self {
            conn,
            attached_schemas: Vec::new(),
        })
    }

    /// Wrap an already-opened [`SqliteConn`].
    #[must_use]
    pub const fn from_conn(conn: SqliteConn) -> Self {
        Self {
            conn,
            attached_schemas: Vec::new(),
        }
    }

    /// Borrow the underlying safe [`SqliteConn`].
    #[must_use]
    pub const fn conn(&self) -> &SqliteConn {
        &self.conn
    }

    /// Execute a semicolon-separated SQL batch (useful for DDL setup).
    ///
    /// # Errors
    /// Returns [`DbError::Query`] if any statement fails.
    pub fn execute_batch(&mut self, sql: &str) -> Result<(), DbError> {
        self.conn.execute_batch(sql).map_err(map_query_err)
    }

    fn is_attached_schema(&mut self, schema: &str) -> bool {
        if self
            .attached_schemas
            .iter()
            .any(|s| s.eq_ignore_ascii_case(schema))
        {
            return true;
        }
        let Ok(mut stmt) = self.conn.prepare("PRAGMA database_list") else {
            return false;
        };
        while let Ok(StepResult::Row) = stmt.step() {
            if let Ok(db_alias) = stmt.column_text(1)
                && db_alias.eq_ignore_ascii_case(schema)
            {
                return true;
            }
        }
        false
    }

    fn main_object_exists(&mut self, name: &str) -> bool {
        let Ok(mut stmt) = self.conn.prepare(
            "SELECT 1 FROM main.sqlite_master WHERE type IN ('table', 'view') AND name = ? LIMIT 1",
        ) else {
            return false;
        };
        if stmt.bind_text(1, name).is_err() {
            return false;
        }
        matches!(stmt.step(), Ok(StepResult::Row))
    }

    fn introspect_namespace(
        &mut self,
        schema_name: Option<&str>,
    ) -> Result<Vec<LockedTable>, DbError> {
        let master_sql = match schema_name {
            Some(s) => format!(
                "SELECT name FROM {}.sqlite_master                  WHERE type = 'table' AND name NOT LIKE 'sqlite_%'                  ORDER BY name",
                quote_sql_ident(s)
            ),
            None => "SELECT name FROM main.sqlite_master                      WHERE type = 'table' AND name NOT LIKE 'sqlite_%'                      ORDER BY name"
                .to_string(),
        };
        let mut table_names = Vec::new();
        {
            let mut stmt = self.conn.prepare(&master_sql).map_err(map_query_err)?;
            while stmt.step().map_err(map_query_err)? == StepResult::Row {
                table_names.push(stmt.column_text(0).map_err(map_query_err)?);
            }
        }

        let mut tables = Vec::with_capacity(table_names.len());
        for tname in table_names {
            let pragma_sql = match schema_name {
                Some(s) => format!(
                    "PRAGMA {}.table_info({})",
                    quote_sql_ident(s),
                    quote_sql_ident(&tname)
                ),
                None => format!("PRAGMA main.table_info({})", quote_sql_ident(&tname)),
            };
            let mut stmt = self.conn.prepare(&pragma_sql).map_err(map_query_err)?;
            let mut cols = Vec::new();
            while stmt.step().map_err(map_query_err)? == StepResult::Row {
                let col_name = stmt.column_text(1).map_err(map_query_err)?;
                let declared_ty = stmt.column_text(2).map_err(map_query_err)?;
                let notnull = stmt.column_int64(3) != 0;
                let pk = stmt.column_int64(5) > 0;
                cols.push(LockedCol {
                    name: col_name,
                    ty: map_sqlite_declared_type(&declared_ty),
                    nullable: !notnull && !pk,
                    pk,
                    tags: TagSet::empty(),
                });
            }
            let emitted_name = match schema_name {
                Some(s) => format!("{s}.{tname}"),
                None => tname,
            };
            tables.push(LockedTable {
                name: emitted_name,
                cols,
            });
        }
        Ok(tables)
    }
}

fn map_conn_err(e: SqliteFfiError) -> DbError {
    DbError::Connection(e.to_string())
}

fn map_query_err(e: SqliteFfiError) -> DbError {
    DbError::Query(e.to_string())
}

fn bind_params(stmt: &mut SqliteStmt<'_>, params: &[SqlParam]) -> Result<(), DbError> {
    for (idx, param) in params.iter().enumerate() {
        let bind_idx = i32::try_from(idx + 1)
            .map_err(|_| DbError::Query("SQL parameter count exceeds i32::MAX".to_string()))?;
        match param {
            SqlParam::Null => stmt.bind_null(bind_idx),
            SqlParam::Bool(b) => stmt.bind_int64(bind_idx, i64::from(*b)),
            SqlParam::Int(i) | SqlParam::Duration(i) => stmt.bind_int64(bind_idx, *i),
            SqlParam::Decimal(d) => stmt.bind_text(bind_idx, &format_decimal_canonical(d)),
            SqlParam::Float(f) => stmt.bind_double(bind_idx, f.to_f64()),
            SqlParam::Text(s) => stmt.bind_text(bind_idx, s),
            SqlParam::Bytes(bs) => stmt.bind_blob(bind_idx, bs),
            SqlParam::Date(days) => stmt.bind_text(bind_idx, &format_iso_date(*days)),
            SqlParam::Timestamp(us) => stmt.bind_text(bind_idx, &format_iso_timestamp(*us)),
        }
        .map_err(map_query_err)?;
    }
    Ok(())
}

fn decode_sqlite_cell(
    stmt: &SqliteStmt<'_>,
    col_idx: usize,
    col_name: &str,
    ty: &ScalarTy,
) -> Result<Val, DbError> {
    let storage = stmt.column_type(col_idx);
    if let ScalarTy::Option(inner) = ty {
        if storage == SqliteValueType::Null {
            return Ok(Val::OptNone);
        }
        let v = decode_sqlite_cell(stmt, col_idx, col_name, inner)?;
        return Ok(Val::OptSome(Box::new(v)));
    }
    if storage == SqliteValueType::Null {
        return Err(DbError::SchemaDrift(format!(
            "unexpected NULL in non-nullable column `{col_name}` (expected {ty:?})"
        )));
    }
    match ty {
        ScalarTy::Unit => Ok(Val::Unit),
        ScalarTy::Bool => match storage {
            SqliteValueType::Integer => match stmt.column_int64(col_idx) {
                0 => Ok(Val::Bool(false)),
                1 => Ok(Val::Bool(true)),
                other => Err(DbError::SchemaDrift(format!(
                    "column `{col_name}` expected Bool (0/1), got integer {other}"
                ))),
            },
            SqliteValueType::Text => {
                let s = stmt.column_text(col_idx).map_err(map_query_err)?;
                match s.to_ascii_lowercase().as_str() {
                    "true" | "t" | "1" => Ok(Val::Bool(true)),
                    "false" | "f" | "0" => Ok(Val::Bool(false)),
                    _ => Err(DbError::SchemaDrift(format!(
                        "column `{col_name}` expected Bool, got text `{s}`"
                    ))),
                }
            }
            other => Err(DbError::SchemaDrift(format!(
                "column `{col_name}` expected Bool, got SQLite {other:?}"
            ))),
        },
        ScalarTy::Int => match storage {
            SqliteValueType::Integer => Ok(Val::Int(BigInt::from(stmt.column_int64(col_idx)))),
            other => Err(DbError::SchemaDrift(format!(
                "column `{col_name}` expected Int, got SQLite {other:?}"
            ))),
        },
        ScalarTy::Float => match storage {
            SqliteValueType::Float => {
                Ok(Val::Float(Float64::from_f64(stmt.column_double(col_idx))))
            }
            SqliteValueType::Integer => Ok(Val::Float(Float64::from_f64(
                stmt.column_int64(col_idx) as f64,
            ))),
            other => Err(DbError::SchemaDrift(format!(
                "column `{col_name}` expected Float, got SQLite {other:?}"
            ))),
        },
        ScalarTy::Decimal => match storage {
            SqliteValueType::Text => {
                let s = stmt.column_text(col_idx).map_err(map_query_err)?;
                let d = parse_decimal_bigint_strict(&s)
                    .map_err(|e| DbError::TypeConversion(format!("column `{col_name}`: {e}")))?;
                Ok(Val::Decimal(d))
            }
            SqliteValueType::Integer => {
                let d = decimal_from_i64(stmt.column_int64(col_idx))?;
                Ok(Val::Decimal(d))
            }
            SqliteValueType::Float => {
                let d = parse_decimal_from_f64(stmt.column_double(col_idx))?;
                Ok(Val::Decimal(d))
            }
            other => Err(DbError::SchemaDrift(format!(
                "column `{col_name}` expected Decimal, got SQLite {other:?}"
            ))),
        },
        ScalarTy::Text => match storage {
            SqliteValueType::Text => {
                let s = stmt.column_text(col_idx).map_err(map_query_err)?;
                Ok(Val::Text(s))
            }
            other => Err(DbError::SchemaDrift(format!(
                "column `{col_name}` expected Text, got SQLite {other:?}"
            ))),
        },
        ScalarTy::Bytes => match storage {
            SqliteValueType::Blob => Ok(Val::Bytes(stmt.column_blob(col_idx))),
            other => Err(DbError::SchemaDrift(format!(
                "column `{col_name}` expected Bytes (BLOB), got SQLite {other:?}"
            ))),
        },
        ScalarTy::Date => match storage {
            SqliteValueType::Text => {
                let s = stmt.column_text(col_idx).map_err(map_query_err)?;
                let days = parse_iso_date(s.trim())
                    .map_err(|e| DbError::TypeConversion(format!("column `{col_name}`: {e}")))?;
                Ok(Val::Date(BigInt::from(days)))
            }
            SqliteValueType::Integer => Ok(Val::Date(BigInt::from(stmt.column_int64(col_idx)))),
            other => Err(DbError::SchemaDrift(format!(
                "column `{col_name}` expected Date, got SQLite {other:?}"
            ))),
        },
        ScalarTy::Timestamp => match storage {
            SqliteValueType::Text => {
                let s = stmt.column_text(col_idx).map_err(map_query_err)?;
                let us = parse_iso_timestamp_flexible(&s)?;
                Ok(Val::Timestamp(BigInt::from(us)))
            }
            SqliteValueType::Integer => {
                Ok(Val::Timestamp(BigInt::from(stmt.column_int64(col_idx))))
            }
            other => Err(DbError::SchemaDrift(format!(
                "column `{col_name}` expected Timestamp, got SQLite {other:?}"
            ))),
        },
        ScalarTy::Duration => match storage {
            SqliteValueType::Integer => Ok(Val::Duration(BigInt::from(stmt.column_int64(col_idx)))),
            other => Err(DbError::SchemaDrift(format!(
                "column `{col_name}` expected Duration (INTEGER micros), got SQLite {other:?}"
            ))),
        },
        ScalarTy::Data(name) => Err(DbError::TypeConversion(format!(
            "unsupported ADT column `{col_name}: {name}` in SQLite query"
        ))),
        ScalarTy::Option(_) => Err(DbError::TypeConversion(
            "unreachable nested option state".to_string(),
        )),
    }
}

fn map_sqlite_declared_type(raw_type: &str) -> ScalarTy {
    let upper = raw_type.trim().to_ascii_uppercase();
    if upper.contains("BOOL") {
        ScalarTy::Bool
    } else if upper.contains("INT") {
        ScalarTy::Int
    } else if upper.contains("DEC") || upper.contains("NUM") {
        ScalarTy::Decimal
    } else if upper.contains("REAL") || upper.contains("FLOA") || upper.contains("DOUB") {
        ScalarTy::Float
    } else if upper.contains("BLOB") || upper.contains("BYTE") || upper.contains("BIN") {
        ScalarTy::Bytes
    } else if upper.contains("TIMESTAMP") || upper.contains("DATETIME") {
        ScalarTy::Timestamp
    } else if upper.contains("DATE") {
        ScalarTy::Date
    } else if upper.contains("DURATION") || upper.contains("INTERVAL") {
        ScalarTy::Duration
    } else {
        ScalarTy::Text
    }
}

impl DbConnection for SqliteDriver {
    fn dialect(&self) -> SqlDialect {
        SqlDialect::Sqlite
    }

    fn query_rows(
        &mut self,
        sql: &str,
        params: &[SqlParam],
        expected_schema: &TableTy,
    ) -> Result<TableVal, DbError> {
        let mut stmt = self.conn.prepare(sql).map_err(map_query_err)?;
        let actual_cols = stmt.column_count();
        if actual_cols != expected_schema.cols.len() {
            return Err(DbError::SchemaDrift(format!(
                "SQLite query returned {actual_cols} columns, expected {}",
                expected_schema.cols.len()
            )));
        }
        bind_params(&mut stmt, params)?;

        let mut rows = Vec::new();
        while stmt.step().map_err(map_query_err)? == StepResult::Row {
            let mut cells = Vec::with_capacity(expected_schema.cols.len());
            for (ci, spec) in expected_schema.cols.iter().enumerate() {
                cells.push(decode_sqlite_cell(&stmt, ci, &spec.name, &spec.ty)?);
            }
            rows.push(make_table_row(cells));
        }

        Ok(TableVal {
            cols: expected_schema.cols.clone(),
            rows,
        })
    }

    fn query_batches(
        &mut self,
        sql: &str,
        params: &[SqlParam],
        expected_schema: &TableTy,
        batch_size: usize,
    ) -> Result<VmTable, DbError> {
        let mut stmt = self.conn.prepare(sql).map_err(map_query_err)?;
        let actual_cols = stmt.column_count();
        if actual_cols != expected_schema.cols.len() {
            return Err(DbError::SchemaDrift(format!(
                "SQLite query returned {actual_cols} columns, expected {}",
                expected_schema.cols.len()
            )));
        }
        bind_params(&mut stmt, params)?;

        let mut builder = ColumnarBatchBuilder::new(expected_schema.cols.clone(), batch_size);
        while stmt.step().map_err(map_query_err)? == StepResult::Row {
            let mut cells = Vec::with_capacity(expected_schema.cols.len());
            for (ci, spec) in expected_schema.cols.iter().enumerate() {
                cells.push(decode_sqlite_cell(&stmt, ci, &spec.name, &spec.ty)?);
            }
            builder.push_row(cells)?;
        }

        Ok(builder.finish())
    }

    fn introspect_schema(&mut self, db_name: &str) -> Result<LockedDb, DbError> {
        let mut tables = self.introspect_namespace(None)?;
        let attached = self.attached_schemas.clone();
        for s in attached {
            tables.extend(self.introspect_namespace(Some(&s))?);
        }
        Ok(LockedDb {
            name: db_name.to_string(),
            dialect: SqlDialect::Sqlite,
            tables,
        })
    }

    fn introspect_schema_with_schemas(
        &mut self,
        db_name: &str,
        schemas: &[String],
    ) -> Result<LockedDb, DbError> {
        if schemas.is_empty() {
            return self.introspect_schema(db_name);
        }
        let mut tables = Vec::new();
        if schemas
            .iter()
            .any(|s| s.eq_ignore_ascii_case("main") || s.eq_ignore_ascii_case("public"))
        {
            tables.extend(self.introspect_namespace(None)?);
        }
        let attached = self.attached_schemas.clone();
        for s in attached {
            if schemas.iter().any(|req| req == &s) {
                tables.extend(self.introspect_namespace(Some(&s))?);
            }
        }
        Ok(LockedDb {
            name: db_name.to_string(),
            dialect: SqlDialect::Sqlite,
            tables,
        })
    }

    fn upsert_table(
        &mut self,
        table: &str,
        key_col: &str,
        data: &TableVal,
        dry_run: bool,
    ) -> Result<UpsertDiff, DbError> {
        if data.cols.is_empty() {
            return Err(DbError::Query(
                "cannot upsert table with zero columns".to_string(),
            ));
        }
        let key_idx = data
            .cols
            .iter()
            .position(|c| c.name == key_col)
            .ok_or_else(|| {
                DbError::Query(format!(
                    "upsert key column `{key_col}` not found in table `{table}`"
                ))
            })?;

        let quoted_table = self.resolve_table_sql_ref(table);
        let quoted_cols: Vec<String> = data.cols.iter().map(|c| quote_sql_ident(&c.name)).collect();
        let quoted_key = quote_sql_ident(key_col);

        // Read existing rows matching incoming keys (strictly read-only query).
        let select_sql = format!(
            "SELECT {} FROM {quoted_table} WHERE {quoted_key} = ?",
            quoted_cols.join(", ")
        );
        let diff = match self.conn.prepare(&select_sql) {
            Ok(mut select_stmt) => compute_upsert_diff(table, key_idx, data, |key_val| {
                select_stmt.reset().map_err(map_query_err)?;
                select_stmt.clear_bindings().map_err(map_query_err)?;
                let key_param = SqlParam::from_val(key_val)?;
                bind_params(&mut select_stmt, &[key_param])?;
                if select_stmt.step().map_err(map_query_err)? == StepResult::Row {
                    let mut cells = Vec::with_capacity(data.cols.len());
                    for (ci, spec) in data.cols.iter().enumerate() {
                        cells.push(decode_sqlite_cell(&select_stmt, ci, &spec.name, &spec.ty)?);
                    }
                    Ok(Some(cells))
                } else {
                    Ok(None)
                }
            })?,
            Err(err) if dry_run && err.message.to_ascii_lowercase().contains("no such table") => {
                compute_upsert_diff(table, key_idx, data, |_| Ok(None))?
            }
            Err(err) => return Err(map_query_err(err)),
        };

        if dry_run || data.rows.is_empty() {
            return Ok(diff);
        }

        // Execute parameterized transactional upsert.
        let placeholders = vec!["?"; data.cols.len()].join(", ");
        let update_assignments: Vec<String> = data
            .cols
            .iter()
            .filter(|c| c.name != key_col)
            .map(|c| {
                let q = quote_sql_ident(&c.name);
                format!("{q} = excluded.{q}")
            })
            .collect();
        let upsert_sql = if update_assignments.is_empty() {
            format!(
                "INSERT INTO {quoted_table} ({}) VALUES ({placeholders}) \
                 ON CONFLICT({quoted_key}) DO NOTHING",
                quoted_cols.join(", ")
            )
        } else {
            format!(
                "INSERT INTO {quoted_table} ({}) VALUES ({placeholders}) \
                 ON CONFLICT({quoted_key}) DO UPDATE SET {}",
                quoted_cols.join(", "),
                update_assignments.join(", ")
            )
        };

        self.execute("BEGIN IMMEDIATE", &[])?;
        let tx_res: Result<(), DbError> = (|| {
            let mut upsert_stmt = self.conn.prepare(&upsert_sql).map_err(map_query_err)?;
            for row in &data.rows {
                upsert_stmt.reset().map_err(map_query_err)?;
                upsert_stmt.clear_bindings().map_err(map_query_err)?;
                let mut params = Vec::with_capacity(row.cells.len());
                for cell in &row.cells {
                    params.push(SqlParam::from_val(cell)?);
                }
                bind_params(&mut upsert_stmt, &params)?;
                while upsert_stmt.step().map_err(map_query_err)? == StepResult::Row {}
            }
            Ok(())
        })();

        match tx_res {
            Ok(()) => {
                self.execute("COMMIT", &[])?;
                Ok(diff)
            }
            Err(e) => {
                let _ = self.execute("ROLLBACK", &[]);
                Err(e)
            }
        }
    }

    fn execute(&mut self, sql: &str, params: &[SqlParam]) -> Result<u64, DbError> {
        let mut stmt = self.conn.prepare(sql).map_err(map_query_err)?;
        bind_params(&mut stmt, params)?;
        while stmt.step().map_err(map_query_err)? == StepResult::Row {}
        Ok(self.conn.changes())
    }

    fn attach_database(&mut self, schema: &str, path: &str) -> Result<(), DbError> {
        validate_sqlite_attach_schema(schema)?;
        if self
            .attached_schemas
            .iter()
            .any(|s| s.eq_ignore_ascii_case(schema))
        {
            return Err(DbError::Connection(format!(
                "duplicate SQLite attach schema `{schema}`"
            )));
        }
        let sql = format!("ATTACH DATABASE ? AS {}", quote_sql_ident(schema));
        let mut stmt = self.conn.prepare(&sql).map_err(map_conn_err)?;
        bind_params(&mut stmt, &[SqlParam::Text(path.to_string())])?;
        while stmt.step().map_err(map_conn_err)? == StepResult::Row {}
        self.attached_schemas.push(schema.to_string());
        Ok(())
    }

    fn resolve_table_sql_ref(&mut self, table: &str) -> String {
        if let Some((schema, rel)) = table.split_once('.')
            && !schema.is_empty()
            && !rel.is_empty()
            && !rel.contains('.')
        {
            if schema.eq_ignore_ascii_case("main")
                || schema.eq_ignore_ascii_case("temp")
                || self.is_attached_schema(schema)
            {
                return format!("{}.{}", quote_sql_ident(schema), quote_sql_ident(rel));
            }
            if self.main_object_exists(table) {
                return quote_sql_ident(table);
            }
            let flat = format!("{schema}_{rel}");
            if self.main_object_exists(&flat) {
                return quote_sql_ident(&flat);
            }
            return quote_sql_table_ref(table);
        }
        quote_sql_ident(table)
    }
}
