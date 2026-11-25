//! Safe RAII TLS client and test server acceptor backed by the allowlisted system OpenSSL 3
//! (`libssl` + `libcrypto`).
//!
//! All raw `SSL*` and `SSL_CTX*` pointers are strictly confined to this module with explicit
//! `// SAFETY:` invariants. [`TlsStream`] owns its underlying [`TcpStream`] and guarantees that
//! `SSL_shutdown` / `SSL_free` always execute BEFORE the `TcpStream` file descriptor is closed.

#![expect(
    unsafe_code,
    reason = "isolated FFI bindings to allowlisted system OpenSSL (libssl/libcrypto)"
)]

use std::ffi::{CStr, CString, c_char, c_int, c_long, c_ulong, c_void};
use std::fmt;
use std::io::{self, Read, Write};
use std::net::{IpAddr, TcpStream};
use std::os::fd::AsRawFd;
use std::ptr;

const SSL_VERIFY_NONE: c_int = 0x00;
const SSL_VERIFY_PEER: c_int = 0x01;
const SSL_FILETYPE_PEM: c_int = 1;
const SSL_CTRL_SET_TLSEXT_HOSTNAME: c_int = 55;
const TLSEXT_NAMETYPE_HOST_NAME: c_long = 0;

const SSL_ERROR_NONE: c_int = 0;
const SSL_ERROR_WANT_READ: c_int = 2;
const SSL_ERROR_WANT_WRITE: c_int = 3;
const SSL_ERROR_SYSCALL: c_int = 5;
const SSL_ERROR_ZERO_RETURN: c_int = 6;

#[repr(C)]
struct SslMethod {
    _opaque: [u8; 0],
}

#[repr(C)]
struct SslCtx {
    _opaque: [u8; 0],
}

#[repr(C)]
struct Ssl {
    _opaque: [u8; 0],
}

unsafe extern "C" {
    fn TLS_client_method() -> *const SslMethod;
    fn TLS_server_method() -> *const SslMethod;

    fn SSL_CTX_new(method: *const SslMethod) -> *mut SslCtx;
    fn SSL_CTX_free(ctx: *mut SslCtx);
    fn SSL_CTX_set_default_verify_paths(ctx: *mut SslCtx) -> c_int;
    fn SSL_CTX_set_verify(ctx: *mut SslCtx, mode: c_int, callback: *const c_void);
    fn SSL_CTX_load_verify_locations(
        ctx: *mut SslCtx,
        ca_file: *const c_char,
        ca_path: *const c_char,
    ) -> c_int;
    fn SSL_CTX_use_certificate_file(ctx: *mut SslCtx, file: *const c_char, ty: c_int) -> c_int;
    fn SSL_CTX_use_PrivateKey_file(ctx: *mut SslCtx, file: *const c_char, ty: c_int) -> c_int;

    fn SSL_new(ctx: *mut SslCtx) -> *mut Ssl;
    fn SSL_free(ssl: *mut Ssl);
    fn SSL_set_fd(ssl: *mut Ssl, fd: c_int) -> c_int;
    fn SSL_ctrl(ssl: *mut Ssl, cmd: c_int, larg: c_long, parg: *mut c_void) -> c_long;
    fn SSL_set1_host(ssl: *mut Ssl, hostname: *const c_char) -> c_int;

    fn SSL_connect(ssl: *mut Ssl) -> c_int;
    fn SSL_accept(ssl: *mut Ssl) -> c_int;
    fn SSL_read(ssl: *mut Ssl, buf: *mut c_void, num: c_int) -> c_int;
    fn SSL_write(ssl: *mut Ssl, buf: *const c_void, num: c_int) -> c_int;
    fn SSL_shutdown(ssl: *mut Ssl) -> c_int;
    fn SSL_get_error(ssl: *const Ssl, ret: c_int) -> c_int;

    fn ERR_get_error() -> c_ulong;
    fn ERR_error_string_n(e: c_ulong, buf: *mut c_char, len: usize);
}

fn clear_openssl_errors() {
    loop {
        // SAFETY: `ERR_get_error` pops from OpenSSL's thread-local error queue with no pointers.
        if unsafe { ERR_get_error() } == 0 {
            break;
        }
    }
}

fn drain_openssl_errors() -> String {
    let mut parts = Vec::new();
    let mut buf = [0 as c_char; 256];
    loop {
        // SAFETY: `ERR_get_error` pops from OpenSSL's thread-local error queue.
        let code = unsafe { ERR_get_error() };
        if code == 0 {
            break;
        }
        // SAFETY: `buf` is a valid writable buffer of `buf.len()` bytes; `ERR_error_string_n`
        // always writes a NUL-terminated ASCII string within `buf.len()`.
        unsafe { ERR_error_string_n(code, buf.as_mut_ptr(), buf.len()) };
        // SAFETY: `ERR_error_string_n` NUL-terminated `buf`.
        let s = unsafe { CStr::from_ptr(buf.as_ptr()) }
            .to_string_lossy()
            .into_owned();
        parts.push(s);
    }
    if parts.is_empty() {
        "unknown OpenSSL error".to_string()
    } else {
        parts.join("; ")
    }
}

fn ssl_io_error(ssl: *const Ssl, ret: c_int, context: &str) -> io::Error {
    // SAFETY: `ssl` is a live `SSL*` pointer for the duration of this call.
    let err_code = unsafe { SSL_get_error(ssl, ret) };
    let detail = drain_openssl_errors();
    if err_code == SSL_ERROR_SYSCALL {
        let os_err = io::Error::last_os_error();
        if os_err.raw_os_error().unwrap_or(0) != 0 {
            return io::Error::new(os_err.kind(), format!("{context}: {os_err} ({detail})"));
        }
    }
    io::Error::other(format!("{context} (ssl_err={err_code}): {detail}"))
}

/// Configuration for a TLS client handshake via [`TlsStream::connect`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TlsClientConfig {
    /// Verify the peer certificate chain against system trust store or `ca_cert_path`.
    pub verify_peer: bool,
    /// Verify the peer certificate's DNS SAN / CN matches `server_name` (requires `verify_peer`).
    pub verify_hostname: bool,
    /// Optional path to a PEM CA certificate bundle/file used instead of system default paths.
    pub ca_cert_path: Option<String>,
}

impl Default for TlsClientConfig {
    fn default() -> Self {
        Self {
            verify_peer: true,
            verify_hostname: true,
            ca_cert_path: None,
        }
    }
}

/// Safe RAII TLS stream wrapping an owned [`TcpStream`], implementing [`Read`] and [`Write`].
///
/// # Drop Order Safety Invariant
/// `TlsStream::drop` ALWAYS calls `SSL_shutdown(self.ssl)`, `SSL_free(self.ssl)`, and (when owned)
/// `SSL_CTX_free(self.ctx)` BEFORE Rust drops the `_tcp: TcpStream` field. Therefore, OpenSSL's
/// internal socket fd (registered via `SSL_set_fd`) remains open and valid for the entire lifetime
/// of `self.ssl` and is never closed prematurely or double-closed.
pub struct TlsStream {
    ssl: *mut Ssl,
    /// Non-null for client-created streams; null for server-accepted streams (where `SSL_new`
    /// already holds an internal OpenSSL reference count on the acceptor's `SSL_CTX*`).
    owned_ctx: *mut SslCtx,
    _tcp: TcpStream,
}

// SAFETY: `TlsStream` exclusively owns its `SSL*`, optional `SSL_CTX*`, and `TcpStream` (not
// `Clone`, not `Sync`). OpenSSL `SSL*` objects may be moved across threads as long as they are
// never used concurrently from multiple threads.
unsafe impl Send for TlsStream {}

impl fmt::Debug for TlsStream {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("TlsStream").finish_non_exhaustive()
    }
}

impl TlsStream {
    /// Upgrade an established [`TcpStream`] to a client TLS session with SNI and certificate checks.
    ///
    /// # Errors
    /// Returns an `io::Error` if OpenSSL context setup, CA loading, SNI/hostname setup, or the
    /// TLS handshake fails.
    pub fn connect(
        tcp: TcpStream,
        server_name: &str,
        config: &TlsClientConfig,
    ) -> io::Result<Self> {
        clear_openssl_errors();
        // SAFETY: `TLS_client_method` returns a static `SSL_METHOD*` descriptor.
        let method = unsafe { TLS_client_method() };
        // SAFETY: `method` is a valid client method returned by `TLS_client_method`.
        let ctx = unsafe { SSL_CTX_new(method) };
        if ctx.is_null() {
            return Err(io::Error::other(format!(
                "SSL_CTX_new failed: {}",
                drain_openssl_errors()
            )));
        }

        let setup_res: io::Result<*mut Ssl> = (|| {
            if config.verify_peer {
                if let Some(ca_path) = &config.ca_cert_path {
                    let c_ca = CString::new(ca_path.as_str()).map_err(|_| {
                        io::Error::new(
                            io::ErrorKind::InvalidInput,
                            "ca_cert_path contains interior NUL byte",
                        )
                    })?;
                    // SAFETY: `ctx` is live and `c_ca` is a valid NUL-terminated path string.
                    let ok =
                        unsafe { SSL_CTX_load_verify_locations(ctx, c_ca.as_ptr(), ptr::null()) };
                    if ok != 1 {
                        return Err(io::Error::other(format!(
                            "SSL_CTX_load_verify_locations(`{ca_path}`) failed: {}",
                            drain_openssl_errors()
                        )));
                    }
                } else {
                    // SAFETY: `ctx` is live; configures system default CA trust paths.
                    let ok = unsafe { SSL_CTX_set_default_verify_paths(ctx) };
                    if ok != 1 {
                        return Err(io::Error::other(format!(
                            "SSL_CTX_set_default_verify_paths failed: {}",
                            drain_openssl_errors()
                        )));
                    }
                }
                // SAFETY: `ctx` is live; NULL callback uses OpenSSL's built-in X.509 verifier.
                unsafe { SSL_CTX_set_verify(ctx, SSL_VERIFY_PEER, ptr::null()) };
            } else {
                // SAFETY: `ctx` is live; disables peer certificate verification when explicitly requested.
                unsafe { SSL_CTX_set_verify(ctx, SSL_VERIFY_NONE, ptr::null()) };
            }

            // SAFETY: `ctx` is a valid initialized `SSL_CTX*`.
            let ssl = unsafe { SSL_new(ctx) };
            if ssl.is_null() {
                return Err(io::Error::other(format!(
                    "SSL_new failed: {}",
                    drain_openssl_errors()
                )));
            }

            if !server_name.is_empty() {
                let c_host = CString::new(server_name).map_err(|_| {
                    // SAFETY: free `ssl` before propagating error.
                    unsafe { SSL_free(ssl) };
                    io::Error::new(
                        io::ErrorKind::InvalidInput,
                        "server_name contains interior NUL byte",
                    )
                })?;

                // RFC 6066 SNI applies to DNS hostnames (not literal IP addresses).
                if server_name.parse::<IpAddr>().is_err() {
                    // SAFETY: `ssl` is live and `c_host` is a valid NUL-terminated hostname;
                    // OpenSSL copies the hostname string inside `SSL_ctrl`.
                    let sni_ok = unsafe {
                        SSL_ctrl(
                            ssl,
                            SSL_CTRL_SET_TLSEXT_HOSTNAME,
                            TLSEXT_NAMETYPE_HOST_NAME,
                            c_host.as_ptr().cast_mut().cast::<c_void>(),
                        )
                    };
                    if sni_ok != 1 {
                        // SAFETY: free `ssl` before returning error.
                        unsafe { SSL_free(ssl) };
                        return Err(io::Error::other(format!(
                            "failed to set TLS SNI hostname: {}",
                            drain_openssl_errors()
                        )));
                    }
                }

                if config.verify_peer && config.verify_hostname {
                    // SAFETY: `ssl` is live and `c_host` is a valid NUL-terminated string;
                    // `SSL_set1_host` copies the hostname for post-handshake verification.
                    let host_ok = unsafe { SSL_set1_host(ssl, c_host.as_ptr()) };
                    if host_ok != 1 {
                        // SAFETY: free `ssl` before returning error.
                        unsafe { SSL_free(ssl) };
                        return Err(io::Error::other(format!(
                            "SSL_set1_host failed: {}",
                            drain_openssl_errors()
                        )));
                    }
                }
            }

            let fd = tcp.as_raw_fd();
            // SAFETY: `ssl` is live and `fd` belongs to `tcp`, which will be moved into the
            // returned `TlsStream` and kept open until after `SSL_free(ssl)` in `Drop`.
            let fd_ok = unsafe { SSL_set_fd(ssl, fd) };
            if fd_ok != 1 {
                // SAFETY: free `ssl` before returning error.
                unsafe { SSL_free(ssl) };
                return Err(io::Error::other(format!(
                    "SSL_set_fd failed: {}",
                    drain_openssl_errors()
                )));
            }

            // SAFETY: `ssl` is live and bound to the open `TcpStream` fd.
            let conn_rc = unsafe { SSL_connect(ssl) };
            if conn_rc != 1 {
                let err = ssl_io_error(ssl, conn_rc, "TLS client handshake failed");
                // SAFETY: free `ssl` before returning error.
                unsafe { SSL_free(ssl) };
                return Err(err);
            }

            Ok(ssl)
        })();

        match setup_res {
            Ok(ssl) => Ok(Self {
                ssl,
                owned_ctx: ctx,
                _tcp: tcp,
            }),
            Err(e) => {
                // SAFETY: `ctx` was created above and no live `TlsStream` owns it on error.
                unsafe { SSL_CTX_free(ctx) };
                Err(e)
            }
        }
    }
}

impl Read for TlsStream {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        if buf.is_empty() {
            return Ok(0);
        }
        let max_len = buf.len().min(c_int::MAX as usize) as c_int;
        loop {
            clear_openssl_errors();
            // SAFETY: `self.ssl` is live (bound to open `self._tcp`), and `buf` is valid for
            // `max_len` writable bytes.
            let rc = unsafe { SSL_read(self.ssl, buf.as_mut_ptr().cast::<c_void>(), max_len) };
            if rc > 0 {
                return Ok(rc as usize);
            }
            // SAFETY: `self.ssl` is live.
            match unsafe { SSL_get_error(self.ssl, rc) } {
                SSL_ERROR_ZERO_RETURN => return Ok(0),
                SSL_ERROR_WANT_READ | SSL_ERROR_WANT_WRITE => continue,
                SSL_ERROR_NONE => return Ok(0),
                _ => return Err(ssl_io_error(self.ssl, rc, "TLS read failed")),
            }
        }
    }
}

impl Write for TlsStream {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        if buf.is_empty() {
            return Ok(0);
        }
        let max_len = buf.len().min(c_int::MAX as usize) as c_int;
        loop {
            clear_openssl_errors();
            // SAFETY: `self.ssl` is live (bound to open `self._tcp`), and `buf` is valid for
            // `max_len` readable bytes.
            let rc = unsafe { SSL_write(self.ssl, buf.as_ptr().cast::<c_void>(), max_len) };
            if rc > 0 {
                return Ok(rc as usize);
            }
            // SAFETY: `self.ssl` is live.
            match unsafe { SSL_get_error(self.ssl, rc) } {
                SSL_ERROR_WANT_READ | SSL_ERROR_WANT_WRITE => continue,
                _ => return Err(ssl_io_error(self.ssl, rc, "TLS write failed")),
            }
        }
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

impl Drop for TlsStream {
    fn drop(&mut self) {
        if !self.ssl.is_null() {
            // SAFETY: Rust executes `Drop::drop` BEFORE dropping struct fields, so `self._tcp`
            // remains open while `SSL_shutdown` sends best-effort close_notify over the fd.
            let _ = unsafe { SSL_shutdown(self.ssl) };
            // SAFETY: `self.ssl` was created by `SSL_new` and is freed exactly once here,
            // strictly before `self._tcp` is dropped and closes the underlying file descriptor.
            unsafe { SSL_free(self.ssl) };
            self.ssl = ptr::null_mut();
        }
        if !self.owned_ctx.is_null() {
            // SAFETY: `self.owned_ctx` was created by `SSL_CTX_new` for this client stream and
            // is freed exactly once here after `self.ssl` has been freed.
            unsafe { SSL_CTX_free(self.owned_ctx) };
            self.owned_ctx = ptr::null_mut();
        }
    }
}

/// Safe RAII TLS server acceptor backed by an OpenSSL `SSL_CTX*` loaded from PEM files.
///
/// Used by loopback integration tests to verify real OpenSSL TLS handshakes, SNI, hostname
/// verification, and untrusted certificate rejection end-to-end.
pub struct TlsServerAcceptor {
    ctx: *mut SslCtx,
}

// SAFETY: `TlsServerAcceptor` owns a configured immutable `SSL_CTX*` whose internal reference
// count is atomically managed by OpenSSL when `SSL_new`/`SSL_free` are invoked.
unsafe impl Send for TlsServerAcceptor {}

impl fmt::Debug for TlsServerAcceptor {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("TlsServerAcceptor").finish_non_exhaustive()
    }
}

impl TlsServerAcceptor {
    /// Load a server certificate chain and private key from PEM files.
    ///
    /// # Errors
    /// Returns an error string if OpenSSL fails to initialize the server context or load either PEM file.
    pub fn from_pem_files(cert_path: &str, key_path: &str) -> Result<Self, String> {
        clear_openssl_errors();
        let c_cert = CString::new(cert_path)
            .map_err(|_| "cert_path contains interior NUL byte".to_string())?;
        let c_key = CString::new(key_path)
            .map_err(|_| "key_path contains interior NUL byte".to_string())?;

        // SAFETY: `TLS_server_method` returns a static `SSL_METHOD*` descriptor.
        let method = unsafe { TLS_server_method() };
        // SAFETY: `method` is a valid server method.
        let ctx = unsafe { SSL_CTX_new(method) };
        if ctx.is_null() {
            return Err(format!("SSL_CTX_new failed: {}", drain_openssl_errors()));
        }

        // SAFETY: `ctx` is live and `c_cert` is a valid NUL-terminated path.
        let cert_ok =
            unsafe { SSL_CTX_use_certificate_file(ctx, c_cert.as_ptr(), SSL_FILETYPE_PEM) };
        if cert_ok != 1 {
            let err = drain_openssl_errors();
            // SAFETY: free `ctx` on error.
            unsafe { SSL_CTX_free(ctx) };
            return Err(format!(
                "SSL_CTX_use_certificate_file(`{cert_path}`) failed: {err}"
            ));
        }

        // SAFETY: `ctx` is live and `c_key` is a valid NUL-terminated path.
        let key_ok = unsafe { SSL_CTX_use_PrivateKey_file(ctx, c_key.as_ptr(), SSL_FILETYPE_PEM) };
        if key_ok != 1 {
            let err = drain_openssl_errors();
            // SAFETY: free `ctx` on error.
            unsafe { SSL_CTX_free(ctx) };
            return Err(format!(
                "SSL_CTX_use_PrivateKey_file(`{key_path}`) failed: {err}"
            ));
        }

        Ok(Self { ctx })
    }

    /// Perform a server-side TLS handshake on an accepted [`TcpStream`].
    ///
    /// # Errors
    /// Returns an error string if `SSL_new`, `SSL_set_fd`, or `SSL_accept` fails.
    pub fn accept(&self, tcp: TcpStream) -> Result<TlsStream, String> {
        clear_openssl_errors();
        // SAFETY: `self.ctx` is a valid server `SSL_CTX*`; `SSL_new` increments OpenSSL's internal
        // refcount on `self.ctx` so the returned `SSL*` remains valid even if `self` drops later.
        let ssl = unsafe { SSL_new(self.ctx) };
        if ssl.is_null() {
            return Err(format!("SSL_new failed: {}", drain_openssl_errors()));
        }

        let fd = tcp.as_raw_fd();
        // SAFETY: `ssl` is live and `tcp` will be moved into `TlsStream` so the fd stays open
        // until after `SSL_free(ssl)` executes in `TlsStream::drop`.
        let fd_ok = unsafe { SSL_set_fd(ssl, fd) };
        if fd_ok != 1 {
            let err = drain_openssl_errors();
            // SAFETY: free `ssl` on error.
            unsafe { SSL_free(ssl) };
            return Err(format!("SSL_set_fd failed: {err}"));
        }

        // SAFETY: `ssl` is live and bound to the open `TcpStream` fd.
        let rc = unsafe { SSL_accept(ssl) };
        if rc != 1 {
            let err = ssl_io_error(ssl, rc, "TLS server accept failed");
            // SAFETY: free `ssl` on error.
            unsafe { SSL_free(ssl) };
            return Err(err.to_string());
        }

        Ok(TlsStream {
            ssl,
            // Owned by `TlsServerAcceptor` (OpenSSL's `SSL_new`/`SSL_free` refcounts `ctx` internally).
            owned_ctx: ptr::null_mut(),
            _tcp: tcp,
        })
    }
}

impl Drop for TlsServerAcceptor {
    fn drop(&mut self) {
        if !self.ctx.is_null() {
            // SAFETY: `self.ctx` was created by `SSL_CTX_new` and is released once here; OpenSSL's
            // internal reference count keeps it alive for any accepted `TlsStream` still open.
            unsafe { SSL_CTX_free(self.ctx) };
            self.ctx = ptr::null_mut();
        }
    }
}
