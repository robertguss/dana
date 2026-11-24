//! Safe RAII streaming gzip reader and writer backed by the allowlisted system `zlib`.

#![expect(
    unsafe_code,
    reason = "isolated FFI bindings to allowlisted system zlib (libz)"
)]

use std::ffi::{CStr, c_char, c_int, c_uint, c_ulong, c_void};
use std::fmt;
use std::io::{self, Read, Write};
use std::mem::{MaybeUninit, size_of};
use std::ptr;

const Z_NO_FLUSH: c_int = 0;
const Z_SYNC_FLUSH: c_int = 2;
const Z_FINISH: c_int = 4;

const Z_OK: c_int = 0;
const Z_STREAM_END: c_int = 1;
const Z_BUF_ERROR: c_int = -5;

const Z_DEFLATED: c_int = 8;
const Z_DEFAULT_STRATEGY: c_int = 0;

/// Window bits: 15 + 32 enables automatic gzip and zlib header detection.
const INFLATE_WINDOW_BITS_AUTO: c_int = 15 + 32;
/// Window bits: 15 + 16 writes a standard RFC 1952 gzip header and CRC-32 trailer.
const DEFLATE_WINDOW_BITS_GZIP: c_int = 15 + 16;
const DEFAULT_MEM_LEVEL: c_int = 8;
const DEFAULT_COMPRESSION_LEVEL: c_int = 6;
const BUF_CAPACITY: usize = 32 * 1024;

/// Matches `struct z_stream_s` in `/usr/include/zlib.h`.
#[repr(C)]
struct ZStream {
    next_in: *const u8,
    avail_in: c_uint,
    total_in: c_ulong,
    next_out: *mut u8,
    avail_out: c_uint,
    total_out: c_ulong,
    msg: *const c_char,
    state: *mut c_void,
    zalloc: *mut c_void,
    zfree: *mut c_void,
    opaque: *mut c_void,
    data_type: c_int,
    adler: c_ulong,
    reserved: c_ulong,
}

unsafe extern "C" {
    fn inflateInit2_(
        strm: *mut ZStream,
        window_bits: c_int,
        version: *const c_char,
        stream_size: c_int,
    ) -> c_int;
    fn inflate(strm: *mut ZStream, flush: c_int) -> c_int;
    fn inflateReset(strm: *mut ZStream) -> c_int;
    fn inflateEnd(strm: *mut ZStream) -> c_int;

    fn deflateInit2_(
        strm: *mut ZStream,
        level: c_int,
        method: c_int,
        window_bits: c_int,
        mem_level: c_int,
        strategy: c_int,
        version: *const c_char,
        stream_size: c_int,
    ) -> c_int;
    fn deflate(strm: *mut ZStream, flush: c_int) -> c_int;
    fn deflateEnd(strm: *mut ZStream) -> c_int;
}

fn zeroed_zstream() -> Box<ZStream> {
    // SAFETY: `ZStream` is a C POD struct (`#[repr(C)]`) of pointers and integers;
    // all-zero initialization is explicitly required by zlib before `inflateInit2_`/`deflateInit2_`
    // (setting `zalloc`/`zfree`/`opaque` to NULL for default allocators).
    let strm = unsafe { MaybeUninit::<ZStream>::zeroed().assume_init() };
    Box::new(strm)
}

fn zlib_err(strm: &ZStream, code: c_int, context: &str) -> io::Error {
    let detail = if strm.msg.is_null() {
        format!("zlib code {code}")
    } else {
        // SAFETY: When non-null, zlib guarantees `strm.msg` points to a static NUL-terminated ASCII string.
        unsafe { CStr::from_ptr(strm.msg) }
            .to_string_lossy()
            .into_owned()
    };
    io::Error::new(io::ErrorKind::InvalidData, format!("{context}: {detail}"))
}

/// Safe RAII streaming gzip/zlib decompressor implementing [`Read`].
///
/// Supports multi-member (concatenated) gzip streams and strictly rejects truncated or
/// CRC-corrupted streams with [`io::ErrorKind::InvalidData`].
pub struct GzipReader<R: Read> {
    inner: R,
    strm: Box<ZStream>,
    in_buf: Vec<u8>,
    in_pos: usize,
    in_len: usize,
    eof: bool,
    source_eof: bool,
    member_done: bool,
    any_bytes_seen: bool,
    may_have_buffered_out: bool,
}

impl<R: Read> fmt::Debug for GzipReader<R> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("GzipReader")
            .field("eof", &self.eof)
            .field("member_done", &self.member_done)
            .finish_non_exhaustive()
    }
}

impl<R: Read> GzipReader<R> {
    /// Wrap `inner` in a streaming gzip/zlib decompressor.
    ///
    /// # Errors
    /// Returns an `io::Error` if `zlib` fails to initialize the inflate state.
    pub fn new(inner: R) -> io::Result<Self> {
        let mut strm = zeroed_zstream();
        let ver = c"1.3";
        // SAFETY: `strm` is heap-pinned in a `Box`, zero-initialized, `ver` is a valid
        // NUL-terminated version string, and `size_of::<ZStream>()` checks ABI compatibility.
        let rc = unsafe {
            inflateInit2_(
                ptr::from_mut(strm.as_mut()),
                INFLATE_WINDOW_BITS_AUTO,
                ver.as_ptr(),
                size_of::<ZStream>() as c_int,
            )
        };
        if rc != Z_OK {
            return Err(zlib_err(&strm, rc, "gzip inflateInit2 failed"));
        }
        Ok(Self {
            inner,
            strm,
            in_buf: vec![0u8; BUF_CAPACITY],
            in_pos: 0,
            in_len: 0,
            eof: false,
            source_eof: false,
            member_done: false,
            any_bytes_seen: false,
            may_have_buffered_out: false,
        })
    }

    fn refill(&mut self) -> io::Result<usize> {
        if self.in_pos < self.in_len {
            return Ok(self.in_len - self.in_pos);
        }
        if self.source_eof {
            return Ok(0);
        }
        let n = self.inner.read(&mut self.in_buf)?;
        self.in_pos = 0;
        self.in_len = n;
        if n > 0 {
            self.any_bytes_seen = true;
        } else {
            self.source_eof = true;
        }
        Ok(n)
    }
}

impl<R: Read> Read for GzipReader<R> {
    fn read(&mut self, out: &mut [u8]) -> io::Result<usize> {
        if out.is_empty() || self.eof {
            return Ok(0);
        }

        loop {
            if self.member_done {
                let avail = self.refill()?;
                if avail == 0 {
                    self.eof = true;
                    return Ok(0);
                }
                // Multi-member gzip stream: reset inflate state for the next member.
                // SAFETY: `self.strm` is a live initialized zlib inflate stream.
                let rc = unsafe { inflateReset(ptr::from_mut(self.strm.as_mut())) };
                if rc != Z_OK {
                    return Err(zlib_err(&self.strm, rc, "gzip inflateReset failed"));
                }
                self.member_done = false;
                self.may_have_buffered_out = false;
            }

            if self.in_pos == self.in_len && !self.may_have_buffered_out {
                let n = self.refill()?;
                if n == 0 {
                    if !self.any_bytes_seen {
                        return Err(io::Error::new(
                            io::ErrorKind::InvalidData,
                            "empty gzip stream",
                        ));
                    }
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidData,
                        "truncated gzip stream before trailer",
                    ));
                }
            }

            let avail_in = (self.in_len - self.in_pos).min(c_uint::MAX as usize) as c_uint;
            let avail_out = out.len().min(c_uint::MAX as usize) as c_uint;

            self.strm.next_in = if avail_in == 0 {
                ptr::null()
            } else {
                self.in_buf[self.in_pos..].as_ptr()
            };
            self.strm.avail_in = avail_in;
            self.strm.next_out = out.as_mut_ptr();
            self.strm.avail_out = avail_out;

            // SAFETY: `next_in` (when non-null) points to `avail_in` valid readable bytes inside
            // `self.in_buf`, `next_out` points to `avail_out` valid writable bytes inside `out`,
            // and both buffers do not alias while `inflate` executes.
            let rc = unsafe { inflate(ptr::from_mut(self.strm.as_mut()), Z_NO_FLUSH) };

            let consumed = (avail_in - self.strm.avail_in) as usize;
            let produced = (avail_out - self.strm.avail_out) as usize;
            self.in_pos += consumed;

            // Clear borrowed pointers before returning or mutating buffers.
            self.strm.next_in = ptr::null();
            self.strm.avail_in = 0;
            self.strm.next_out = ptr::null_mut();
            self.strm.avail_out = 0;

            match rc {
                Z_OK => {
                    self.may_have_buffered_out = produced == avail_out as usize;
                    if produced > 0 {
                        return Ok(produced);
                    }
                }
                Z_STREAM_END => {
                    self.member_done = true;
                    self.may_have_buffered_out = false;
                    if produced > 0 {
                        return Ok(produced);
                    }
                }
                Z_BUF_ERROR => {
                    self.may_have_buffered_out = false;
                    if produced > 0 {
                        return Ok(produced);
                    }
                    if consumed == 0 && self.in_pos == self.in_len {
                        let n = self.refill()?;
                        if n == 0 {
                            return Err(io::Error::new(
                                io::ErrorKind::InvalidData,
                                "truncated gzip stream",
                            ));
                        }
                    }
                }
                other => {
                    return Err(zlib_err(&self.strm, other, "gzip decompression error"));
                }
            }
        }
    }
}

impl<R: Read> Drop for GzipReader<R> {
    fn drop(&mut self) {
        // SAFETY: `self.strm` was initialized by `inflateInit2_` and is never freed elsewhere.
        // Return code is intentionally ignored because `Drop` must never panic.
        let _ = unsafe { inflateEnd(ptr::from_mut(self.strm.as_mut())) };
    }
}

/// Safe RAII streaming gzip compressor implementing [`Write`] with explicit fallible [`Self::finish`].
pub struct GzipWriter<W: Write> {
    inner: Option<W>,
    strm: Box<ZStream>,
    out_buf: Vec<u8>,
    finished: bool,
}

impl<W: Write> fmt::Debug for GzipWriter<W> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("GzipWriter")
            .field("finished", &self.finished)
            .finish_non_exhaustive()
    }
}

impl<W: Write> GzipWriter<W> {
    /// Wrap `inner` in a streaming gzip compressor at default level (6).
    ///
    /// # Errors
    /// Returns an `io::Error` if `zlib` fails to initialize the deflate state.
    pub fn new(inner: W) -> io::Result<Self> {
        Self::with_level(inner, DEFAULT_COMPRESSION_LEVEL)
    }

    /// Wrap `inner` in a streaming gzip compressor with explicit compression level `0..=9`.
    ///
    /// # Errors
    /// Returns an `io::Error` if `zlib` rejects the level or fails allocation.
    pub fn with_level(inner: W, level: i32) -> io::Result<Self> {
        let mut strm = zeroed_zstream();
        let ver = c"1.3";
        // SAFETY: `strm` is heap-pinned and zero-initialized; `ver` is NUL-terminated.
        let rc = unsafe {
            deflateInit2_(
                ptr::from_mut(strm.as_mut()),
                level.clamp(0, 9) as c_int,
                Z_DEFLATED,
                DEFLATE_WINDOW_BITS_GZIP,
                DEFAULT_MEM_LEVEL,
                Z_DEFAULT_STRATEGY,
                ver.as_ptr(),
                size_of::<ZStream>() as c_int,
            )
        };
        if rc != Z_OK {
            return Err(zlib_err(&strm, rc, "gzip deflateInit2 failed"));
        }
        Ok(Self {
            inner: Some(inner),
            strm,
            out_buf: vec![0u8; BUF_CAPACITY],
            finished: false,
        })
    }

    fn pump_deflate(&mut self, mut input: &[u8], flush: c_int) -> io::Result<()> {
        let Some(writer) = self.inner.as_mut() else {
            return Err(io::Error::other("gzip writer already finished"));
        };
        loop {
            let avail_in = input.len().min(c_uint::MAX as usize) as c_uint;
            let avail_out = self.out_buf.len().min(c_uint::MAX as usize) as c_uint;

            self.strm.next_in = if avail_in == 0 {
                ptr::null()
            } else {
                input.as_ptr()
            };
            self.strm.avail_in = avail_in;
            self.strm.next_out = self.out_buf.as_mut_ptr();
            self.strm.avail_out = avail_out;

            // SAFETY: `next_in` (when non-null) points to `avail_in` valid readable bytes,
            // `next_out` points to `avail_out` valid writable bytes in `self.out_buf`, and
            // the two slices do not alias.
            let rc = unsafe { deflate(ptr::from_mut(self.strm.as_mut()), flush) };

            let consumed = (avail_in - self.strm.avail_in) as usize;
            let produced = (avail_out - self.strm.avail_out) as usize;
            input = &input[consumed..];

            self.strm.next_in = ptr::null();
            self.strm.avail_in = 0;
            self.strm.next_out = ptr::null_mut();
            self.strm.avail_out = 0;

            if produced > 0 {
                writer.write_all(&self.out_buf[..produced])?;
            }

            match rc {
                Z_OK => {
                    if flush == Z_NO_FLUSH && input.is_empty() && produced < avail_out as usize {
                        return Ok(());
                    }
                    if flush == Z_SYNC_FLUSH && input.is_empty() && produced < avail_out as usize {
                        return Ok(());
                    }
                    // For Z_FINISH or full output buffer, keep pumping until Z_STREAM_END or drained.
                }
                Z_STREAM_END => {
                    return Ok(());
                }
                Z_BUF_ERROR if flush != Z_FINISH && input.is_empty() => {
                    return Ok(());
                }
                other => {
                    return Err(zlib_err(&self.strm, other, "gzip compression error"));
                }
            }
        }
    }

    /// Finish the gzip stream, write the RFC 1952 CRC-32 trailer, flush the underlying writer,
    /// and return ownership of the inner writer.
    ///
    /// # Errors
    /// Returns any compression or I/O flush error.
    pub fn finish(mut self) -> io::Result<W> {
        if !self.finished {
            self.pump_deflate(&[], Z_FINISH)?;
            if let Some(w) = self.inner.as_mut() {
                w.flush()?;
            }
            self.finished = true;
        }
        self.inner
            .take()
            .ok_or_else(|| io::Error::other("gzip writer inner missing"))
    }
}

impl<W: Write> Write for GzipWriter<W> {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        if self.finished {
            return Err(io::Error::other("write after gzip finish"));
        }
        if buf.is_empty() {
            return Ok(0);
        }
        self.pump_deflate(buf, Z_NO_FLUSH)?;
        Ok(buf.len())
    }

    fn flush(&mut self) -> io::Result<()> {
        if self.finished {
            return Ok(());
        }
        self.pump_deflate(&[], Z_SYNC_FLUSH)?;
        if let Some(w) = self.inner.as_mut() {
            w.flush()?;
        }
        Ok(())
    }
}

impl<W: Write> Drop for GzipWriter<W> {
    fn drop(&mut self) {
        if !self.finished && self.inner.is_some() {
            // Best-effort trailer flush on drop; never panic.
            let _ = self.pump_deflate(&[], Z_FINISH);
            if let Some(w) = self.inner.as_mut() {
                let _ = w.flush();
            }
            self.finished = true;
        }
        // SAFETY: `self.strm` was initialized by `deflateInit2_` and is freed exactly once here.
        let _ = unsafe { deflateEnd(ptr::from_mut(self.strm.as_mut())) };
    }
}
