//! Host `World`, isolated fake capability stores, evaluation `Outcome`,
//! and canonical observable `ExecReport` extraction.
//!
//! Mirrors `formal/DanaCore/Eval.lean` §4 byte-for-byte.

use crate::core::bigint::BigInt;
use crate::core::syntax::{Ident, TableTy, TagSet};
use crate::oracle::value::{Bug, TableVal, Val, render_public_val};

#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct FakeConsoleState {
    pub stdout: Vec<String>,
    pub stderr: Vec<String>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct FakeFilesState {
    pub files: Vec<(String, String)>,
}

#[derive(Clone, Debug)]
pub struct StoredTable {
    pub db: Ident,
    pub table_name: Ident,
    pub schema: TableTy,
    pub rows: Vec<Vec<Val>>,
}

#[derive(Clone, Debug, Default)]
pub struct FakeDBState {
    pub db: Ident,
    pub tables: Vec<StoredTable>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct FakeHttpsState {
    pub host: String,
    pub responses: Vec<(String, String)>,
    pub requests: Vec<String>,
}

pub type WrittenTableRecord = (Ident, Ident, Vec<Ident>, Vec<Vec<Val>>);
pub type RenderedWrittenTable = (Ident, Ident, Vec<Ident>, Vec<Vec<String>>);

/// Execution world holding real host state and isolated per-handle fake states.
#[derive(Clone, Debug, Default)]
pub struct World {
    pub args: Vec<String>,
    pub clock_micros: BigInt,
    pub stdout: Vec<String>,
    pub stderr: Vec<String>,
    pub real_csv_fixtures: Vec<(String, TableVal, TableVal)>,
    pub written_files: Vec<(String, String)>,
    pub real_db_tables: Vec<StoredTable>,
    pub written_tables: Vec<WrittenTableRecord>,
    pub real_secrets: Vec<(String, String)>,
    pub runtime_allow_export: TagSet,
    // Independent fake capability heaps for `spec` (`test` / `example` / `promise`)
    pub fake_consoles: Vec<FakeConsoleState>,
    pub fake_files: Vec<FakeFilesState>,
    pub fake_dbs: Vec<FakeDBState>,
    pub fake_https: Vec<FakeHttpsState>,
    pub fake_secrets: Vec<String>,
}

#[derive(Clone, Debug)]
pub enum Outcome {
    Ok(Val, World),
    Stopped(Bug, World),
    Failed(String, World),
    Jumped(Ident, Vec<Val>, World),
    Wrong,
    OutOfFuel,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub enum ExitStatus {
    #[default]
    Ok,
    Stopped,
    Failed,
}

/// Canonical observable execution report shared across `danacore` (Lean)
/// and the naive Rust oracle (`src/oracle/`).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ExecReport {
    pub status: ExitStatus,
    pub diagnostic: Option<String>,
    pub stdout: Vec<String>,
    pub stderr: Vec<String>,
    pub written_files: Vec<(String, String)>,
    pub written_tables: Vec<RenderedWrittenTable>,
    pub fake_consoles: Vec<FakeConsoleState>,
    pub fake_files: Vec<FakeFilesState>,
}

fn render_tables(wts: &[WrittenTableRecord]) -> Vec<RenderedWrittenTable> {
    wts.iter()
        .map(|(db, tbl, cols, rows)| {
            let rendered_rows = rows
                .iter()
                .map(|r| r.iter().map(render_public_val).collect())
                .collect();
            (db.clone(), tbl.clone(), cols.clone(), rendered_rows)
        })
        .collect()
}

#[must_use]
pub fn extract_report(out: Outcome) -> Option<ExecReport> {
    match out {
        Outcome::Ok(_, w) => Some(ExecReport {
            status: ExitStatus::Ok,
            diagnostic: None,
            stdout: w.stdout,
            stderr: w.stderr,
            written_files: w.written_files,
            written_tables: render_tables(&w.written_tables),
            fake_consoles: w.fake_consoles,
            fake_files: w.fake_files,
        }),
        Outcome::Stopped(bug, w) => Some(ExecReport {
            status: ExitStatus::Stopped,
            diagnostic: Some(bug.message),
            stdout: w.stdout,
            stderr: w.stderr,
            written_files: w.written_files,
            written_tables: render_tables(&w.written_tables),
            fake_consoles: w.fake_consoles,
            fake_files: w.fake_files,
        }),
        Outcome::Failed(msg, w) => Some(ExecReport {
            status: ExitStatus::Failed,
            diagnostic: Some(msg),
            stdout: w.stdout,
            stderr: w.stderr,
            written_files: w.written_files,
            written_tables: render_tables(&w.written_tables),
            fake_consoles: w.fake_consoles,
            fake_files: w.fake_files,
        }),
        Outcome::Jumped(_, _, _) | Outcome::Wrong | Outcome::OutOfFuel => None,
    }
}
