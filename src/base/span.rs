//! Byte-offset source spans and `O(log N)` line/column lookup tables.

use crate::core::bigint::BigInt;
use crate::core::syntax::SourceSpan;

/// Index of a source file inside a [`SourceMap`].
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FileId(pub u32);

/// Half-open byte span `[start, end)` within a single [`SourceFile`].
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct Span {
    pub file: FileId,
    pub start: u32,
    pub end: u32,
}

impl Span {
    #[must_use]
    pub const fn new(file: FileId, start: u32, end: u32) -> Self {
        Self { file, start, end }
    }

    #[must_use]
    pub const fn point(file: FileId, offset: u32) -> Self {
        Self {
            file,
            start: offset,
            end: offset,
        }
    }

    /// Merge two spans from the same file into their minimal covering span.
    #[must_use]
    pub const fn merge(self, other: Self) -> Self {
        let start = if self.start <= other.start {
            self.start
        } else {
            other.start
        };
        let end = if self.end >= other.end {
            self.end
        } else {
            other.end
        };
        Self {
            file: self.file,
            start,
            end,
        }
    }
}

/// 1-based line and UTF-8 scalar column coordinates.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct LineCol {
    pub line: u32,
    pub col: u32,
}

/// A loaded source file with precomputed line-start byte offsets.
#[derive(Clone, Debug)]
pub struct SourceFile {
    pub id: FileId,
    pub name: String,
    pub source: String,
    line_starts: Vec<u32>,
}

impl SourceFile {
    #[must_use]
    pub fn new(id: FileId, name: impl Into<String>, source: impl Into<String>) -> Self {
        let source = source.into();
        let mut line_starts = vec![0u32];
        for (idx, b) in source.bytes().enumerate() {
            if b == b'\n'
                && let Ok(next) = u32::try_from(idx + 1)
            {
                line_starts.push(next);
            }
        }
        Self {
            id,
            name: name.into(),
            source,
            line_starts,
        }
    }

    /// Compute 1-based `(line, col)` for a byte offset in `self.source`.
    #[must_use]
    pub fn line_col(&self, byte_offset: u32) -> LineCol {
        let clamped = (byte_offset as usize).min(self.source.len());
        let line_idx = match self
            .line_starts
            .binary_search(&(u32::try_from(clamped).unwrap_or(u32::MAX)))
        {
            Ok(i) => i,
            Err(ins) => ins.saturating_sub(1),
        };
        let line_start = self.line_starts[line_idx] as usize;
        // Snap end to a UTF-8 char boundary defensively.
        let mut end = clamped;
        while end > line_start && !self.source.is_char_boundary(end) {
            end -= 1;
        }
        let col_count = self.source[line_start..end].chars().count();
        LineCol {
            line: u32::try_from(line_idx + 1).unwrap_or(u32::MAX),
            col: u32::try_from(col_count + 1).unwrap_or(u32::MAX),
        }
    }

    /// Return the text of a 1-based line without its trailing `\r` or `\n`.
    #[must_use]
    pub fn line_text(&self, line_1based: u32) -> Option<&str> {
        let idx = usize::try_from(line_1based).ok()?.checked_sub(1)?;
        let start = *self.line_starts.get(idx)? as usize;
        let end = self
            .line_starts
            .get(idx + 1)
            .map_or(self.source.len(), |&o| o as usize);
        let raw = self.source.get(start..end)?;
        Some(raw.trim_end_matches(['\n', '\r']))
    }
}

/// Registry of loaded source files indexed by [`FileId`].
#[derive(Clone, Debug, Default)]
pub struct SourceMap {
    files: Vec<SourceFile>,
}

impl SourceMap {
    #[must_use]
    pub const fn new() -> Self {
        Self { files: Vec::new() }
    }

    pub fn add_file(&mut self, name: impl Into<String>, source: impl Into<String>) -> FileId {
        let id = FileId(u32::try_from(self.files.len()).unwrap_or(u32::MAX));
        self.files.push(SourceFile::new(id, name, source));
        id
    }

    #[must_use]
    pub fn file(&self, id: FileId) -> Option<&SourceFile> {
        self.files.get(id.0 as usize)
    }

    #[must_use]
    pub fn line_col(&self, file: FileId, byte_offset: u32) -> LineCol {
        self.file(file)
            .map_or(LineCol { line: 1, col: 1 }, |f| f.line_col(byte_offset))
    }

    #[must_use]
    pub fn to_core_span(&self, span: Span) -> SourceSpan {
        let Some(f) = self.file(span.file) else {
            return SourceSpan::default();
        };
        let start = f.line_col(span.start);
        let end = f.line_col(span.end);
        SourceSpan {
            file: f.name.clone(),
            start_line: BigInt::from(u64::from(start.line)),
            start_col: BigInt::from(u64::from(start.col)),
            end_line: BigInt::from(u64::from(end.line)),
            end_col: BigInt::from(u64::from(end.col)),
        }
    }
}
