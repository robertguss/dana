//! Safe RAII streaming Zstandard reader and writer backed by the allowlisted system `libzstd`.

#![expect(
    unsafe_code,
    reason = "isolated FFI bindings to allowlisted system libzstd"
)]

use std::ffi::{CStr, c_char, c_int, c_uint, c_void};
use std::fmt;
use std::io::{self, Read, Write};
use std::ptr;

const ZSTD_C_COMPRESSION_LEVEL: c_int = 100;
const ZSTD_E_CONTINUE: c_int = 0;
const ZSTD_E_FLUSH: c_int = 1;
const ZSTD_E_END: c_int = 2;
const DEFAULT_ZSTD_LEVEL: c_int = 3;

#[repr(C)]
struct ZstdInBuffer {
    src: *const c_void,
    size: usize,
    pos: usize,
}

#[repr(C)]
struct ZstdOutBuffer {
    dst: *mut c_void,
    size: usize,
    pos: usize,
}

#[repr(C)]
struct ZstdDStream {
    _opaque: [u8; 0],
}

#[repr(C)]
struct ZstdCStream {
    _opaque: [u8; 0],
}

unsafe extern "C" {
    fn ZSTD_isError(code: usize) -> c_uint;
    fn ZSTD_getErrorName(code: usize) -> *const c_char;

    fn ZSTD_createDStream() -> *mut ZstdDStream;
    fn ZSTD_freeDStream(zds: *mut ZstdDStream) -> usize;
    fn ZSTD_decompressStream(
        zds: *mut ZstdDStream,
        output: *mut ZstdOutBuffer,
        input: *mut ZstdInBuffer,
    ) -> usize;
    fn ZSTD_DStreamInSize() -> usize;

    fn ZSTD_createCStream() -> *mut ZstdCStream;
    fn ZSTD_freeCStream(zcs: *mut ZstdCStream) -> usize;
    fn ZSTD_CCtx_setParameter(cctx: *mut ZstdCStream, param: c_int, value: c_int) -> usize;
    fn ZSTD_compressStream2(
        cctx: *mut ZstdCStream,
        output: *mut ZstdOutBuffer,
        input: *mut ZstdInBuffer,
        end_op: c_int,
    ) -> usize;
    fn ZSTD_CStreamOutSize() -> usize;
}

fn check_zstd(code: usize, context: &str) -> io::Result<usize> {
    // SAFETY: `ZSTD_isError` and `ZSTD_getErrorName` are pure C status inspection functions
    // accepting any `size_t` returned by libzstd.
    let is_err = unsafe { ZSTD_isError(code) } != 0;
    if is_err {
        // SAFETY: `ZSTD_getErrorName` returns a static NUL-terminated ASCII string for any error code.
        let msg = unsafe { CStr::from_ptr(ZSTD_getErrorName(code)) }
            .to_string_lossy()
            .into_owned();
        Err(io::Error::new(
            io::ErrorKind::InvalidData,
            format!("{context}: {msg}"),
        ))
    } else {
        Ok(code)
    }
}

/// Safe RAII streaming Zstandard decompressor implementing [`Read`].
///
/// Supports multi-frame `.zst` streams and strictly rejects truncated or corrupted frames
/// with [`io::ErrorKind::InvalidData`].
pub struct ZstdReader<R: Read> {
    inner: R,
    dstream: *mut ZstdDStream,
    in_buf: Vec<u8>,
    in_pos: usize,
    in_len: usize,
    eof: bool,
    source_eof: bool,
    in_frame: bool,
    any_bytes_seen: bool,
    may_have_buffered_out: bool,
}

impl<R: Read> fmt::Debug for ZstdReader<R> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ZstdReader")
            .field("eof", &self.eof)
            .field("in_frame", &self.in_frame)
            .finish_non_exhaustive()
    }
}

impl<R: Read> ZstdReader<R> {
    /// Wrap `inner` in a streaming Zstandard decompressor.
    ///
    /// # Errors
    /// Returns an `io::Error` if `libzstd` fails to allocate the decompression context.
    pub fn new(inner: R) -> io::Result<Self> {
        // SAFETY: `ZSTD_createDStream` takes no pointers and returns a fresh context or NULL on OOM.
        let dstream = unsafe { ZSTD_createDStream() };
        if dstream.is_null() {
            return Err(io::Error::other("ZSTD_createDStream returned null"));
        }
        // SAFETY: `ZSTD_DStreamInSize` is a pure constant query.
        let rec_in = unsafe { ZSTD_DStreamInSize() }.max(16 * 1024);
        Ok(Self {
            inner,
            dstream,
            in_buf: vec![0u8; rec_in],
            in_pos: 0,
            in_len: 0,
            eof: false,
            source_eof: false,
            in_frame: false,
            any_bytes_seen: false,
            may_have_buffered_out: false,
        })
    }
}

impl<R: Read> Read for ZstdReader<R> {
    fn read(&mut self, out: &mut [u8]) -> io::Result<usize> {
        if out.is_empty() || self.eof {
            return Ok(0);
        }

        loop {
            if self.in_pos == self.in_len && !self.may_have_buffered_out {
                if !self.source_eof {
                    let n = self.inner.read(&mut self.in_buf)?;
                    self.in_pos = 0;
                    self.in_len = n;
                    if n > 0 {
                        self.any_bytes_seen = true;
                    } else {
                        self.source_eof = true;
                    }
                }
                if self.source_eof && self.in_pos == self.in_len {
                    if self.in_frame {
                        return Err(io::Error::new(
                            io::ErrorKind::InvalidData,
                            "truncated zstd frame before end-of-frame",
                        ));
                    }
                    if !self.any_bytes_seen {
                        return Err(io::Error::new(
                            io::ErrorKind::InvalidData,
                            "empty zstd stream",
                        ));
                    }
                    self.eof = true;
                    return Ok(0);
                }
            }

            let mut z_in = ZstdInBuffer {
                src: if self.in_pos < self.in_len {
                    self.in_buf.as_ptr().cast::<c_void>()
                } else {
                    ptr::null()
                },
                size: if self.in_pos < self.in_len {
                    self.in_len
                } else {
                    0
                },
                pos: if self.in_pos < self.in_len {
                    self.in_pos
                } else {
                    0
                },
            };
            let mut z_out = ZstdOutBuffer {
                dst: out.as_mut_ptr().cast::<c_void>(),
                size: out.len(),
                pos: 0,
            };

            // SAFETY: `self.dstream` is a live non-null context; `z_in` (when non-empty) references
            // `self.in_buf` and `z_out` references `out`, which are disjoint valid byte buffers.
            let raw_ret = unsafe { ZSTD_decompressStream(self.dstream, &mut z_out, &mut z_in) };
            let hint = check_zstd(raw_ret, "zstd decompression error")?;

            if self.in_pos < self.in_len {
                self.in_pos = z_in.pos;
            }
            self.in_frame = hint != 0;
            // If `out` filled completely, libzstd may still hold buffered output bytes even when
            // `in_pos == in_len`, so drain on the next call before declaring EOF/truncation.
            self.may_have_buffered_out = z_out.pos == out.len() && hint != 0;

            if z_out.pos > 0 {
                return Ok(z_out.pos);
            }
        }
    }
}

impl<R: Read> Drop for ZstdReader<R> {
    fn drop(&mut self) {
        if !self.dstream.is_null() {
            // SAFETY: `self.dstream` was created by `ZSTD_createDStream` and is freed once here.
            let _ = unsafe { ZSTD_freeDStream(self.dstream) };
            self.dstream = ptr::null_mut();
        }
    }
}

/// Safe RAII streaming Zstandard compressor implementing [`Write`] with explicit fallible [`Self::finish`].
pub struct ZstdWriter<W: Write> {
    inner: Option<W>,
    cstream: *mut ZstdCStream,
    out_buf: Vec<u8>,
    finished: bool,
}

impl<W: Write> fmt::Debug for ZstdWriter<W> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ZstdWriter")
            .field("finished", &self.finished)
            .finish_non_exhaustive()
    }
}

impl<W: Write> ZstdWriter<W> {
    /// Wrap `inner` in a streaming Zstandard compressor at default level (3).
    ///
    /// # Errors
    /// Returns an `io::Error` if `libzstd` fails to allocate or configure the context.
    pub fn new(inner: W) -> io::Result<Self> {
        Self::with_level(inner, DEFAULT_ZSTD_LEVEL)
    }

    /// Wrap `inner` in a streaming Zstandard compressor with explicit compression level.
    ///
    /// # Errors
    /// Returns an `io::Error` if `libzstd` fails to allocate or rejects the level.
    pub fn with_level(inner: W, level: i32) -> io::Result<Self> {
        // SAFETY: `ZSTD_createCStream` allocates a fresh context or returns NULL on OOM.
        let cstream = unsafe { ZSTD_createCStream() };
        if cstream.is_null() {
            return Err(io::Error::other("ZSTD_createCStream returned null"));
        }
        // SAFETY: `cstream` is non-null and freshly allocated.
        let rc =
            unsafe { ZSTD_CCtx_setParameter(cstream, ZSTD_C_COMPRESSION_LEVEL, level as c_int) };
        if let Err(e) = check_zstd(rc, "zstd set compression level failed") {
            // SAFETY: free the freshly created context before returning error.
            let _ = unsafe { ZSTD_freeCStream(cstream) };
            return Err(e);
        }
        // SAFETY: `ZSTD_CStreamOutSize` is a pure constant query.
        let rec_out = unsafe { ZSTD_CStreamOutSize() }.max(16 * 1024);
        Ok(Self {
            inner: Some(inner),
            cstream,
            out_buf: vec![0u8; rec_out],
            finished: false,
        })
    }

    fn pump_compress(&mut self, input: &[u8], end_op: c_int) -> io::Result<()> {
        let Some(writer) = self.inner.as_mut() else {
            return Err(io::Error::other("zstd writer already finished"));
        };
        let mut z_in = ZstdInBuffer {
            src: if input.is_empty() {
                ptr::null()
            } else {
                input.as_ptr().cast::<c_void>()
            },
            size: input.len(),
            pos: 0,
        };
        loop {
            let mut z_out = ZstdOutBuffer {
                dst: self.out_buf.as_mut_ptr().cast::<c_void>(),
                size: self.out_buf.len(),
                pos: 0,
            };
            // SAFETY: `self.cstream` is live; `z_in` and `z_out` point to disjoint valid buffers.
            let raw_ret =
                unsafe { ZSTD_compressStream2(self.cstream, &mut z_out, &mut z_in, end_op) };
            let remaining = check_zstd(raw_ret, "zstd compression error")?;
            if z_out.pos > 0 {
                writer.write_all(&self.out_buf[..z_out.pos])?;
            }
            let done = if end_op == ZSTD_E_CONTINUE {
                z_in.pos == z_in.size
            } else {
                remaining == 0 && z_in.pos == z_in.size
            };
            if done {
                return Ok(());
            }
        }
    }

    /// Finish the Zstandard frame, flush the underlying writer, and return ownership of the inner writer.
    ///
    /// # Errors
    /// Returns any compression or I/O flush error.
    pub fn finish(mut self) -> io::Result<W> {
        if !self.finished {
            self.pump_compress(&[], ZSTD_E_END)?;
            if let Some(w) = self.inner.as_mut() {
                w.flush()?;
            }
            self.finished = true;
        }
        self.inner
            .take()
            .ok_or_else(|| io::Error::other("zstd writer inner missing"))
    }
}

impl<W: Write> Write for ZstdWriter<W> {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        if self.finished {
            return Err(io::Error::other("write after zstd finish"));
        }
        if buf.is_empty() {
            return Ok(0);
        }
        self.pump_compress(buf, ZSTD_E_CONTINUE)?;
        Ok(buf.len())
    }

    fn flush(&mut self) -> io::Result<()> {
        if self.finished {
            return Ok(());
        }
        self.pump_compress(&[], ZSTD_E_FLUSH)?;
        if let Some(w) = self.inner.as_mut() {
            w.flush()?;
        }
        Ok(())
    }
}

impl<W: Write> Drop for ZstdWriter<W> {
    fn drop(&mut self) {
        if !self.finished && self.inner.is_some() {
            let _ = self.pump_compress(&[], ZSTD_E_END);
            if let Some(w) = self.inner.as_mut() {
                let _ = w.flush();
            }
            self.finished = true;
        }
        if !self.cstream.is_null() {
            // SAFETY: `self.cstream` was created by `ZSTD_createCStream` and is freed once here.
            let _ = unsafe { ZSTD_freeCStream(self.cstream) };
            self.cstream = ptr::null_mut();
        }
    }
}
