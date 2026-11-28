//! Capability-gated local HTTP/1.1 loopback (`LocalHttpAllow`) and Unix domain socket
//! (`LocalSocketAllow`) client built under `#[forbid(unsafe_code)]`.
//!
//! Security invariants:
//! - Strictly separated from [`crate::net::https`] (`HttpsAllow`): rejects `https://` and non-loopback
//!   hosts, so remote TLS validation can never silently downgrade.
//! - Compile-time & runtime authority checks require an explicit loopback host (`127.0.0.0/8`,
//!   `[::1]`, or `localhost`) paired with an explicit non-zero port.
//! - Post-DNS anti-SSRF / DNS-rebinding guard verifies EVERY resolved `SocketAddr::ip().is_loopback()`
//!   before calling `TcpStream::connect_timeout` against the verified address.
//! - `LocalSocketAllow` validates clean paths (no `..` traversal, control chars, or symlinks),
//!   canonicalizes the parent directory, and verifies `file_type().is_socket()` via `lstat`.
//! - Never follows HTTP redirects (all 3xx/non-2xx fail cleanly via shared
//!   [`crate::net::https::parse_http_response_from_reader`]).

use std::io::Write;
use std::net::{Ipv4Addr, Ipv6Addr, SocketAddr, TcpStream, ToSocketAddrs};
use std::path::{Component, Path};
use std::time::Duration;

use crate::formats::json::{JsonValue, parse_json};
use crate::net::https::{
    HttpsClientConfig, HttpsError, HttpsResponse, JsonResponse, build_http_request_head,
    decode_json_response, parse_http_response_from_reader, parse_nonzero_port, write_http_request,
};

/// Validated `host:port` authority restricted exclusively to loopback hosts (`127.0.0.0/8`,
/// `[::1]`, or `localhost`) with an explicit non-zero port.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParsedLoopbackAuthority {
    pub host: String,
    pub port: u16,
}

impl ParsedLoopbackAuthority {
    /// Canonical `host:port` string (`[::1]:port` for IPv6, lowercase `localhost:port`).
    #[must_use]
    pub fn canonical_authority(&self) -> String {
        if self.host.contains(':') {
            format!("[{}]:{}", self.host, self.port)
        } else {
            format!("{}:{}", self.host, self.port)
        }
    }

    /// HTTP/1.1 `Host` header value (omits `:80`).
    #[must_use]
    pub fn host_header(&self) -> String {
        let formatted_host = if self.host.contains(':') {
            format!("[{}]", self.host)
        } else {
            self.host.clone()
        };
        if self.port == 80 {
            formatted_host
        } else {
            format!("{formatted_host}:{}", self.port)
        }
    }
}

/// Resolved plain `http://` request targeting an exact pinned loopback `host:port`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResolvedLocalHttpUrl {
    pub authority: ParsedLoopbackAuthority,
    pub path_and_query: String,
}

/// Strictly parse a pinned `LocalHttpAllow` target (`127.0.0.1:8091`, `localhost:8091`, or
/// `[::1]:8091`). Portless literals and non-loopback hosts are rejected.
///
/// # Errors
/// Returns [`HttpsError`] on empty/control characters, missing `:port`, wildcards, userinfo,
/// paths, or non-loopback hosts/IPs.
pub fn parse_loopback_authority(raw: &str) -> Result<ParsedLoopbackAuthority, HttpsError> {
    if raw.is_empty() || raw.bytes().any(|b| b <= 0x20 || b == 0x7F) {
        return Err(HttpsError::new(
            "`LocalHttpAllow` authority cannot be empty or contain control/whitespace characters",
        ));
    }
    if raw.contains("://")
        || raw.contains('@')
        || raw.contains('/')
        || raw.contains('?')
        || raw.contains('#')
        || raw.contains('*')
    {
        return Err(HttpsError::new(format!(
            "`LocalHttpAllow` expects `host:port` without scheme, userinfo, path, or wildcard; found `{raw}`"
        )));
    }

    let (host, port) = if let Some(after_lb) = raw.strip_prefix('[') {
        let Some((ipv6_str, after_rb)) = after_lb.split_once(']') else {
            return Err(HttpsError::new(format!(
                "unterminated IPv6 literal in `LocalHttpAllow` target `{raw}`"
            )));
        };
        let Some(port_str) = after_rb.strip_prefix(':') else {
            return Err(HttpsError::new(format!(
                "`LocalHttpAllow` target `{raw}` must specify an explicit `:port` (e.g. `[::1]:8091`)"
            )));
        };
        let ip: Ipv6Addr = ipv6_str.parse().map_err(|_| {
            HttpsError::new(format!(
                "invalid IPv6 literal `[{ipv6_str}]` in `LocalHttpAllow` target `{raw}`"
            ))
        })?;
        if !ip.is_loopback() {
            return Err(HttpsError::new(format!(
                "`LocalHttpAllow` forbids non-loopback IPv6 address `[{ipv6_str}]` (only `[::1]` is permitted)"
            )));
        }
        (ip.to_string(), parse_nonzero_port(port_str, "local HTTP")?)
    } else if let Some((h, port_str)) = raw.rsplit_once(':') {
        if h.contains(':') {
            return Err(HttpsError::new(format!(
                "unbracketed IPv6 literal in `LocalHttpAllow` target `{raw}` (use `[::1]:port`)"
            )));
        }
        if h.is_empty() {
            return Err(HttpsError::new(format!(
                "`LocalHttpAllow` target `{raw}` is missing host before `:port`"
            )));
        }
        let port = parse_nonzero_port(port_str, "local HTTP")?;
        if h.eq_ignore_ascii_case("localhost") {
            ("localhost".to_string(), port)
        } else if let Ok(ip) = h.parse::<Ipv4Addr>() {
            if !ip.is_loopback() {
                return Err(HttpsError::new(format!(
                    "`LocalHttpAllow` forbids non-loopback IPv4 address `{h}` (must be `127.0.0.0/8` or `localhost`)"
                )));
            }
            (ip.to_string(), port)
        } else {
            return Err(HttpsError::new(format!(
                "`LocalHttpAllow` forbids non-loopback host `{h}` (only `127.0.0.0/8`, `[::1]`, or `localhost` is permitted)"
            )));
        }
    } else {
        return Err(HttpsError::new(format!(
            "`LocalHttpAllow` target `{raw}` must include an explicit `:port` (wildcard loopback ports are forbidden; use `--local-http Name=ready:FILE` for ephemeral `--port 0` servers)"
        )));
    };

    Ok(ParsedLoopbackAuthority { host, port })
}

/// Parse a CLI or env runtime binding for a named `LocalHttpAllow(Name)` capability.
/// Accepts `http://<loopback-host>:<port>` (with optional trailing `/`) or `ready:<path>` pointing
/// to a readiness JSON file containing `"url"` or `"port"` (such as `mo serve --ready-file`).
///
/// # Errors
/// Returns [`HttpsError`] if reading `ready:<path>` fails or the resulting endpoint is invalid or non-loopback.
pub fn parse_local_http_binding_value(raw: &str) -> Result<ParsedLoopbackAuthority, HttpsError> {
    let trimmed = raw.trim();
    if let Some(ready_path) = trimmed.strip_prefix("ready:") {
        if ready_path.is_empty() {
            return Err(HttpsError::new("empty path after `ready:` binding"));
        }
        let content = std::fs::read_to_string(ready_path).map_err(|e| {
            HttpsError::new(format!(
                "failed to read local HTTP ready-file `{ready_path}`: {e}"
            ))
        })?;
        let doc = parse_json(&content).map_err(|e| {
            HttpsError::new(format!(
                "invalid JSON in local HTTP ready-file `{ready_path}`: {e}"
            ))
        })?;
        if let Some(JsonValue::Str(url)) = doc.get("url") {
            return parse_loopback_http_base_url(url);
        }
        if let Some(JsonValue::Number(port_num)) = doc.get("port") {
            let p_val = port_num.trim();
            let port = parse_nonzero_port(p_val, "local HTTP")?;
            return Ok(ParsedLoopbackAuthority {
                host: "127.0.0.1".to_string(),
                port,
            });
        }
        return Err(HttpsError::new(format!(
            "ready-file `{ready_path}` must contain a string `\"url\"` or integer `\"port\"`"
        )));
    }
    parse_loopback_http_base_url(trimmed)
}

fn parse_loopback_http_base_url(url: &str) -> Result<ParsedLoopbackAuthority, HttpsError> {
    if url.bytes().any(|b| b <= 0x20 || b == 0x7F) {
        return Err(HttpsError::new(
            "local HTTP base URL contains forbidden whitespace or control characters",
        ));
    }
    let Some((scheme, rest)) = url.split_once("://") else {
        return Err(HttpsError::new(format!(
            "local HTTP binding `{url}` must start with `http://`"
        )));
    };
    if scheme.eq_ignore_ascii_case("https") {
        return Err(HttpsError::new(
            "`LocalHttpAllow` forbids `https://` bindings; use `HttpsAllow` for TLS endpoints",
        ));
    }
    if !scheme.eq_ignore_ascii_case("http") {
        return Err(HttpsError::new(format!(
            "unsupported scheme `{scheme}://` in `LocalHttpAllow` binding (expected `http://`)"
        )));
    }
    let authority = rest.strip_suffix('/').unwrap_or(rest);
    parse_loopback_authority(authority)
}

/// Resolve a request target (either an `http://<host>:<port>/...` URL or a relative `/path?query`)
/// against a pinned loopback authority.
///
/// # Errors
/// Returns [`HttpsError`] if the URL uses `https://`, targets another host or port, contains
/// userinfo or control bytes, or omits a scheme when not starting with `/`.
pub fn resolve_local_http_url(
    url_or_path: &str,
    allowed: &ParsedLoopbackAuthority,
) -> Result<ResolvedLocalHttpUrl, HttpsError> {
    if url_or_path.is_empty() || url_or_path.bytes().any(|b| b <= 0x20 || b == 0x7F) {
        return Err(HttpsError::new(
            "local HTTP URL contains forbidden whitespace or control characters",
        ));
    }
    if url_or_path.starts_with('/') {
        let clean = url_or_path
            .split_once('#')
            .map_or(url_or_path, |(before, _)| before);
        return Ok(ResolvedLocalHttpUrl {
            authority: allowed.clone(),
            path_and_query: clean.to_string(),
        });
    }

    let Some((scheme, rest)) = url_or_path.split_once("://") else {
        return Err(HttpsError::new(format!(
            "invalid local HTTP URL `{url_or_path}`: use `/path` or `http://{}/path`",
            allowed.canonical_authority()
        )));
    };
    if scheme.eq_ignore_ascii_case("https") {
        return Err(HttpsError::new(
            "`LocalHttpAllow` forbids `https://` URLs; use `HttpsAllow` for remote TLS endpoints",
        ));
    }
    if !scheme.eq_ignore_ascii_case("http") {
        return Err(HttpsError::new(format!(
            "unsupported URL scheme `{scheme}://` for `LocalHttpAllow`"
        )));
    }

    let without_frag = rest.split_once('#').map_or(rest, |(before, _)| before);
    let split_pos = without_frag.find(['/', '?']).unwrap_or(without_frag.len());
    let authority_str = &without_frag[..split_pos];
    let tail = &without_frag[split_pos..];

    let req_auth = parse_loopback_authority(authority_str)?;
    if !req_auth.host.eq_ignore_ascii_case(&allowed.host) || req_auth.port != allowed.port {
        return Err(HttpsError::new(format!(
            "local HTTP target `{}` is not permitted by `LocalHttpAllow(\"{}\")`",
            req_auth.canonical_authority(),
            allowed.canonical_authority()
        )));
    }

    let path_and_query = if tail.is_empty() {
        "/".to_string()
    } else if tail.starts_with('?') {
        format!("/{tail}")
    } else {
        tail.to_string()
    };

    Ok(ResolvedLocalHttpUrl {
        authority: req_auth,
        path_and_query,
    })
}

/// Validate a Unix domain socket path string literal or CLI/env binding.
///
/// # Errors
/// Returns [`HttpsError`] if the path is empty, contains control chars/NUL, `://`, or `..` traversal.
pub fn validate_local_socket_path(raw: &str) -> Result<String, HttpsError> {
    if raw.is_empty() || raw.bytes().any(|b| b < 0x20 || b == 0x7F) {
        return Err(HttpsError::new(
            "`LocalSocketAllow` path cannot be empty or contain control/NUL characters",
        ));
    }
    if raw.contains("://") {
        return Err(HttpsError::new(format!(
            "`LocalSocketAllow` expects a filesystem socket path, not URL `{raw}`"
        )));
    }
    if Path::new(raw)
        .components()
        .any(|c| matches!(c, Component::ParentDir))
    {
        return Err(HttpsError::new(format!(
            "`LocalSocketAllow` forbids parent directory `..` traversal in `{raw}`"
        )));
    }
    Ok(raw.to_string())
}

/// Resolve an HTTP request path/query target sent over `LocalSocketAllow` (must begin with `/`).
///
/// # Errors
/// Returns [`HttpsError`] if the target contains control chars, a URL scheme, or lacks leading `/`.
pub fn resolve_local_socket_path_and_query(url_or_path: &str) -> Result<String, HttpsError> {
    if url_or_path.is_empty() || url_or_path.bytes().any(|b| b <= 0x20 || b == 0x7F) {
        return Err(HttpsError::new(
            "local socket HTTP path contains forbidden whitespace or control characters",
        ));
    }
    if url_or_path.contains("://") || !url_or_path.starts_with('/') {
        return Err(HttpsError::new(format!(
            "`LocalSocketAllow` expects a relative `/path[?query]`, found `{url_or_path}`"
        )));
    }
    let clean = url_or_path
        .split_once('#')
        .map_or(url_or_path, |(before, _)| before);
    Ok(clean.to_string())
}

/// Perform a post-DNS anti-SSRF check ensuring EVERY resolved `SocketAddr::ip().is_loopback()`,
/// then connect directly to the verified address with configured timeouts.
fn connect_loopback_tcp(
    authority: &ParsedLoopbackAuthority,
    timeout: Duration,
) -> Result<TcpStream, HttpsError> {
    let addrs: Vec<SocketAddr> = (authority.host.as_str(), authority.port)
        .to_socket_addrs()
        .map_err(|e| HttpsError::new(format!("local HTTP DNS lookup failed: {e}")))?
        .collect();
    if addrs.is_empty() {
        return Err(HttpsError::new(format!(
            "local HTTP host `{}` resolved to no addresses",
            authority.host
        )));
    }
    for addr in &addrs {
        if !addr.ip().is_loopback() {
            return Err(HttpsError::new(format!(
                "local HTTP anti-SSRF guard blocked non-loopback resolved address `{addr}` for `{}`",
                authority.canonical_authority()
            )));
        }
    }

    let mut last_err = None;
    for addr in &addrs {
        match TcpStream::connect_timeout(addr, timeout) {
            Ok(tcp) => {
                let _ = tcp.set_read_timeout(Some(timeout));
                let _ = tcp.set_write_timeout(Some(timeout));
                return Ok(tcp);
            }
            Err(e) => last_err = Some(e),
        }
    }
    let msg = last_err.map_or_else(
        || "no loopback socket connected".to_string(),
        |e| e.to_string(),
    );
    Err(HttpsError::new(format!(
        "local HTTP loopback connect to `{}` failed: {msg}",
        authority.canonical_authority()
    )))
}

#[cfg(unix)]
fn connect_local_socket(
    socket_path: &str,
    timeout: Duration,
) -> Result<std::os::unix::net::UnixStream, HttpsError> {
    use std::os::unix::fs::FileTypeExt;
    use std::os::unix::net::UnixStream;

    let validated = validate_local_socket_path(socket_path)?;
    let raw_path = Path::new(&validated);
    let raw_meta = std::fs::symlink_metadata(raw_path)
        .map_err(|e| HttpsError::new(format!("local socket `{validated}` inspect failed: {e}")))?;
    if raw_meta.file_type().is_symlink() {
        return Err(HttpsError::new(format!(
            "`LocalSocketAllow` refuses symlink socket target `{validated}`"
        )));
    }
    if !raw_meta.file_type().is_socket() {
        return Err(HttpsError::new(format!(
            "`LocalSocketAllow` target `{validated}` is not a Unix domain socket"
        )));
    }

    let parent = raw_path
        .parent()
        .filter(|p| !p.as_os_str().is_empty())
        .unwrap_or_else(|| Path::new("."));
    let file_name = raw_path.file_name().ok_or_else(|| {
        HttpsError::new(format!(
            "`LocalSocketAllow` target `{validated}` has no socket filename"
        ))
    })?;
    let canon_parent = std::fs::canonicalize(parent).map_err(|e| {
        HttpsError::new(format!(
            "local socket parent canonicalization failed for `{validated}`: {e}"
        ))
    })?;
    let canon_path = canon_parent.join(file_name);
    let canon_meta = std::fs::symlink_metadata(&canon_path).map_err(|e| {
        HttpsError::new(format!(
            "local socket `{}` re-check failed: {e}",
            canon_path.display()
        ))
    })?;
    if canon_meta.file_type().is_symlink() || !canon_meta.file_type().is_socket() {
        return Err(HttpsError::new(format!(
            "`LocalSocketAllow` refuses non-socket or symlinked target `{}`",
            canon_path.display()
        )));
    }

    let stream = UnixStream::connect(&canon_path).map_err(|e| {
        HttpsError::new(format!(
            "local Unix socket connect to `{}` failed: {e}",
            canon_path.display()
        ))
    })?;
    let _ = stream.set_read_timeout(Some(timeout));
    let _ = stream.set_write_timeout(Some(timeout));
    Ok(stream)
}

/// Perform a capability-gated plaintext HTTP/1.1 request against an explicitly pinned loopback
/// `host:port` authority, rejecting redirects & non-2xx statuses and verifying loopback post-DNS.
///
/// # Errors
/// Returns [`HttpsError`] on scheme/authority mismatch, anti-SSRF denial, transport failure, or
/// invalid/oversized/non-2xx HTTP responses.
pub fn local_http_request_bytes(
    method: &str,
    url_or_path: &str,
    allowed: &ParsedLoopbackAuthority,
    headers: &[(String, String)],
    body: Option<&[u8]>,
    cfg: &HttpsClientConfig,
) -> Result<HttpsResponse, HttpsError> {
    let resolved = resolve_local_http_url(url_or_path, allowed)?;
    let host_hdr = resolved.authority.host_header();
    let req_head = build_http_request_head(
        method,
        &resolved.path_and_query,
        &host_hdr,
        headers,
        body,
        "LocalHttpAllow",
    )?;
    let timeout = Duration::from_secs(cfg.timeout_secs.max(1));
    let mut tcp = connect_loopback_tcp(&resolved.authority, timeout)?;
    write_http_request(&mut tcp, &req_head, body, "LocalHttpAllow")?;
    tcp.flush()
        .map_err(|e| HttpsError::new(format!("local HTTP request flush failed: {e}")))?;
    parse_http_response_from_reader(tcp, cfg)
}

/// Perform a `LocalHttpAllow` `GET` request returning parsed JSON.
///
/// # Errors
/// Returns [`HttpsError`] on policy/loopback/transport/HTTP/JSON error.
pub fn local_http_get_json(
    url_or_path: &str,
    allowed: &ParsedLoopbackAuthority,
    headers: &[(String, String)],
    cfg: &HttpsClientConfig,
) -> Result<JsonResponse, HttpsError> {
    let resp = local_http_request_bytes("GET", url_or_path, allowed, headers, None, cfg)?;
    decode_json_response(resp, "local HTTP", false)
}

/// Perform a `LocalHttpAllow` write request (`POST` or `PUT`) with a JSON body (`empty 2xx -> null`).
///
/// # Errors
/// Returns [`HttpsError`] on policy/loopback/transport/HTTP/JSON error.
pub fn local_http_write_json(
    method: &str,
    url_or_path: &str,
    allowed: &ParsedLoopbackAuthority,
    body_json: &str,
    headers: &[(String, String)],
    cfg: &HttpsClientConfig,
) -> Result<JsonResponse, HttpsError> {
    let resp = local_http_request_bytes(
        method,
        url_or_path,
        allowed,
        headers,
        Some(body_json.as_bytes()),
        cfg,
    )?;
    decode_json_response(resp, "local HTTP", true)
}

/// Perform a `LocalHttpAllow` `DELETE` request returning parsed JSON (`empty 2xx -> null`).
///
/// # Errors
/// Returns [`HttpsError`] on policy/loopback/transport/HTTP/JSON error.
pub fn local_http_delete_json(
    url_or_path: &str,
    allowed: &ParsedLoopbackAuthority,
    headers: &[(String, String)],
    cfg: &HttpsClientConfig,
) -> Result<JsonResponse, HttpsError> {
    let resp = local_http_request_bytes("DELETE", url_or_path, allowed, headers, None, cfg)?;
    decode_json_response(resp, "local HTTP", true)
}

/// Perform a capability-gated HTTP/1.1 request over an allowed Unix domain socket path.
///
/// # Errors
/// Returns [`HttpsError`] on invalid path, symlink rejection, transport failure, or non-2xx HTTP response.
#[cfg(unix)]
pub fn local_socket_request_bytes(
    method: &str,
    url_or_path: &str,
    socket_path: &str,
    headers: &[(String, String)],
    body: Option<&[u8]>,
    cfg: &HttpsClientConfig,
) -> Result<HttpsResponse, HttpsError> {
    let path_and_query = resolve_local_socket_path_and_query(url_or_path)?;
    let req_head = build_http_request_head(
        method,
        &path_and_query,
        "localhost",
        headers,
        body,
        "LocalSocketAllow",
    )?;
    let timeout = Duration::from_secs(cfg.timeout_secs.max(1));
    let mut sock = connect_local_socket(socket_path, timeout)?;
    write_http_request(&mut sock, &req_head, body, "LocalSocketAllow")?;
    sock.flush()
        .map_err(|e| HttpsError::new(format!("local socket request flush failed: {e}")))?;
    parse_http_response_from_reader(sock, cfg)
}

#[cfg(not(unix))]
pub fn local_socket_request_bytes(
    _method: &str,
    _url_or_path: &str,
    _socket_path: &str,
    _headers: &[(String, String)],
    _body: Option<&[u8]>,
    _cfg: &HttpsClientConfig,
) -> Result<HttpsResponse, HttpsError> {
    Err(HttpsError::new(
        "`LocalSocketAllow` is only supported on Unix platforms",
    ))
}

/// Perform a `LocalSocketAllow` `GET` request returning parsed JSON.
///
/// # Errors
/// Returns [`HttpsError`] on socket/HTTP/JSON error.
pub fn local_socket_get_json(
    url_or_path: &str,
    socket_path: &str,
    headers: &[(String, String)],
    cfg: &HttpsClientConfig,
) -> Result<JsonResponse, HttpsError> {
    let resp = local_socket_request_bytes("GET", url_or_path, socket_path, headers, None, cfg)?;
    decode_json_response(resp, "local socket", false)
}

/// Perform a `LocalSocketAllow` write request (`POST` or `PUT`) returning parsed JSON (`empty 2xx -> null`).
///
/// # Errors
/// Returns [`HttpsError`] on socket/HTTP/JSON error.
pub fn local_socket_write_json(
    method: &str,
    url_or_path: &str,
    socket_path: &str,
    body_json: &str,
    headers: &[(String, String)],
    cfg: &HttpsClientConfig,
) -> Result<JsonResponse, HttpsError> {
    let resp = local_socket_request_bytes(
        method,
        url_or_path,
        socket_path,
        headers,
        Some(body_json.as_bytes()),
        cfg,
    )?;
    decode_json_response(resp, "local socket", true)
}

/// Perform a `LocalSocketAllow` `DELETE` request returning parsed JSON (`empty 2xx -> null`).
///
/// # Errors
/// Returns [`HttpsError`] on socket/HTTP/JSON error.
pub fn local_socket_delete_json(
    url_or_path: &str,
    socket_path: &str,
    headers: &[(String, String)],
    cfg: &HttpsClientConfig,
) -> Result<JsonResponse, HttpsError> {
    let resp = local_socket_request_bytes("DELETE", url_or_path, socket_path, headers, None, cfg)?;
    decode_json_response(resp, "local socket", true)
}
