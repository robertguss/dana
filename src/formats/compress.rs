//! Transparent `.gz` (gzip) and `.zst` (Zstandard) stream detection, decoding, and encoding.

use std::fmt;
use std::fs::File;
use std::io::{self, BufReader, Read, Write};
use std::path::Path;

use crate::ffi::{GzipReader, GzipWriter, ZstdReader, ZstdWriter};

/// Supported transparent file compression containers.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum CompressionKind {
    Plain,
    Gzip,
    Zstd,
}

/// Detect compression format from magic bytes (`1F 8B` gzip, `28 B5 2F FD` zstd).
#[must_use]
pub fn detect_compression_magic(prefix: &[u8]) -> CompressionKind {
    if prefix.len() >= 2 && prefix[0] == 0x1F && prefix[1] == 0x8B {
        CompressionKind::Gzip
    } else if prefix.len() >= 4
        && prefix[0] == 0x28
        && prefix[1] == 0xB5
        && prefix[2] == 0x2F
        && prefix[3] == 0xFD
    {
        CompressionKind::Zstd
    } else {
        CompressionKind::Plain
    }
}

/// Detect compression format from file path extension (`.gz`, `.gzip`, `.zst`, `.zstd`).
#[must_use]
pub fn detect_compression_path(path: &str) -> CompressionKind {
    let lower = path.to_ascii_lowercase();
    if lower.ends_with(".gz") || lower.ends_with(".gzip") {
        CompressionKind::Gzip
    } else if lower.ends_with(".zst") || lower.ends_with(".zstd") {
        CompressionKind::Zstd
    } else {
        CompressionKind::Plain
    }
}

/// Strip a trailing compression extension (`.gz`, `.gzip`, `.zst`, `.zstd`) to reveal the inner format extension.
#[must_use]
pub fn strip_compression_ext(path: &str) -> &str {
    let lower = path.to_ascii_lowercase();
    for ext in [".gzip", ".zstd", ".gz", ".zst"] {
        if lower.ends_with(ext) {
            return &path[..path.len() - ext.len()];
        }
    }
    path
}

struct PrefixReader<R: Read> {
    prefix: [u8; 4],
    pos: usize,
    len: usize,
    inner: R,
}

impl<R: Read> Read for PrefixReader<R> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        if self.pos < self.len {
            let n = (self.len - self.pos).min(buf.len());
            buf[..n].copy_from_slice(&self.prefix[self.pos..self.pos + n]);
            self.pos += n;
            return Ok(n);
        }
        self.inner.read(buf)
    }
}

enum DecodeInner<R: Read> {
    Plain(PrefixReader<R>),
    Gzip(GzipReader<PrefixReader<R>>),
    Zstd(ZstdReader<PrefixReader<R>>),
}

/// Streaming reader that auto-detects `.gz` / `.zst` magic bytes (or honors an explicit hint)
/// and transparently decompresses without buffering the full file in memory.
pub struct AutoDecodeReader<R: Read> {
    kind: CompressionKind,
    inner: DecodeInner<R>,
}

impl<R: Read> fmt::Debug for AutoDecodeReader<R> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("AutoDecodeReader")
            .field("kind", &self.kind)
            .finish_non_exhaustive()
    }
}

impl<R: Read> AutoDecodeReader<R> {
    /// Peek up to 4 bytes from `reader` and wrap it in the matching streaming decompressor.
    ///
    /// # Errors
    /// Returns an `io::Error` if reading the magic prefix or initializing the decoder fails.
    pub fn new(mut reader: R) -> io::Result<Self> {
        let mut prefix = [0u8; 4];
        let mut len = 0usize;
        while len < 4 {
            let n = reader.read(&mut prefix[len..])?;
            if n == 0 {
                break;
            }
            len += n;
        }
        let kind = detect_compression_magic(&prefix[..len]);
        let prefixed = PrefixReader {
            prefix,
            pos: 0,
            len,
            inner: reader,
        };
        let inner = match kind {
            CompressionKind::Plain => DecodeInner::Plain(prefixed),
            CompressionKind::Gzip => DecodeInner::Gzip(GzipReader::new(prefixed)?),
            CompressionKind::Zstd => DecodeInner::Zstd(ZstdReader::new(prefixed)?),
        };
        Ok(Self { kind, inner })
    }

    /// Wrap `reader` with an explicit [`CompressionKind`] (e.g., when path extension mandates `.gz`/`.zst`).
    ///
    /// # Errors
    /// Returns an `io::Error` if initializing the decoder fails.
    pub fn with_kind(reader: R, kind: CompressionKind) -> io::Result<Self> {
        let prefixed = PrefixReader {
            prefix: [0u8; 4],
            pos: 0,
            len: 0,
            inner: reader,
        };
        let inner = match kind {
            CompressionKind::Plain => DecodeInner::Plain(prefixed),
            CompressionKind::Gzip => DecodeInner::Gzip(GzipReader::new(prefixed)?),
            CompressionKind::Zstd => DecodeInner::Zstd(ZstdReader::new(prefixed)?),
        };
        Ok(Self { kind, inner })
    }

    /// Returns the detected or configured [`CompressionKind`].
    #[must_use]
    pub const fn kind(&self) -> CompressionKind {
        self.kind
    }
}

impl<R: Read> Read for AutoDecodeReader<R> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        match &mut self.inner {
            DecodeInner::Plain(r) => r.read(buf),
            DecodeInner::Gzip(r) => r.read(buf),
            DecodeInner::Zstd(r) => r.read(buf),
        }
    }
}

/// Streaming writer that optionally wraps an output sink in gzip or zstd compression.
pub enum AutoEncodeWriter<W: Write> {
    Plain(W),
    Gzip(GzipWriter<W>),
    Zstd(ZstdWriter<W>),
}

impl<W: Write> fmt::Debug for AutoEncodeWriter<W> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Plain(_) => f.write_str("AutoEncodeWriter::Plain"),
            Self::Gzip(_) => f.write_str("AutoEncodeWriter::Gzip"),
            Self::Zstd(_) => f.write_str("AutoEncodeWriter::Zstd"),
        }
    }
}

impl<W: Write> AutoEncodeWriter<W> {
    /// Wrap `writer` according to `kind`.
    ///
    /// # Errors
    /// Returns an `io::Error` if initializing the compressor fails.
    pub fn new(writer: W, kind: CompressionKind) -> io::Result<Self> {
        match kind {
            CompressionKind::Plain => Ok(Self::Plain(writer)),
            CompressionKind::Gzip => Ok(Self::Gzip(GzipWriter::new(writer)?)),
            CompressionKind::Zstd => Ok(Self::Zstd(ZstdWriter::new(writer)?)),
        }
    }

    /// Finish the compressed stream, flush the underlying writer, and return ownership of `W`.
    ///
    /// # Errors
    /// Returns any compression trailer or I/O flush error.
    pub fn finish(self) -> io::Result<W> {
        match self {
            Self::Plain(mut w) => {
                w.flush()?;
                Ok(w)
            }
            Self::Gzip(w) => w.finish(),
            Self::Zstd(w) => w.finish(),
        }
    }
}

impl<W: Write> Write for AutoEncodeWriter<W> {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        match self {
            Self::Plain(w) => w.write(buf),
            Self::Gzip(w) => w.write(buf),
            Self::Zstd(w) => w.write(buf),
        }
    }

    fn flush(&mut self) -> io::Result<()> {
        match self {
            Self::Plain(w) => w.flush(),
            Self::Gzip(w) => w.flush(),
            Self::Zstd(w) => w.flush(),
        }
    }
}

/// Open a file with transparent `.gz`/`.zst` decompression (by extension if compressed, else magic bytes).
///
/// # Errors
/// Returns an `io::Error` if opening or initializing decompression fails.
pub fn open_auto_decoded_file(path: &Path) -> io::Result<BufReader<AutoDecodeReader<File>>> {
    let file = File::open(path)?;
    let path_str = path.to_string_lossy();
    let ext_kind = detect_compression_path(&path_str);
    let reader = match ext_kind {
        CompressionKind::Plain => AutoDecodeReader::new(file)?,
        kind => AutoDecodeReader::with_kind(file, kind)?,
    };
    Ok(BufReader::new(reader))
}

/// Compress raw `bytes` using `kind` and return the encoded bytes.
///
/// # Errors
/// Returns any compression error.
pub fn compress_bytes(bytes: &[u8], kind: CompressionKind) -> io::Result<Vec<u8>> {
    let mut enc = AutoEncodeWriter::new(Vec::new(), kind)?;
    enc.write_all(bytes)?;
    enc.finish()
}

/// Decompress raw `bytes` using auto-detected magic bytes (or explicit `kind`).
///
/// # Errors
/// Returns any decompression error.
pub fn decompress_bytes(bytes: &[u8]) -> io::Result<Vec<u8>> {
    let mut dec = AutoDecodeReader::new(io::Cursor::new(bytes))?;
    let mut out = Vec::new();
    dec.read_to_end(&mut out)?;
    Ok(out)
}
