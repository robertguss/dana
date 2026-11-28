//! Capability-gated HTTP/1.1 HTTPS client built on [`crate::ffi::TlsStream`] and
//! [`crate::formats::json`] (`#[forbid(unsafe_code)]`).
//!
//! Security invariants:
//! - Strictly requires the `https://` scheme (rejects plain `http://`).
//! - Enforces exact ASCII case-insensitive host match against `HttpsAllow.host` BEFORE opening TCP.
//! - Rejects userinfo (`user:pass@host`) and CR/LF injection in URLs and headers.
//! - NEVER follows HTTP redirects (all 3xx responses fail with an explicit error).
//! - Always enables peer certificate + hostname/IP verification (`verify_peer: true, verify_hostname: true`).
//! - Enforces strict response header and body byte caps (32 MiB default), including after gzip decompression.

use std::collections::HashMap;
use std::fmt::{self, Write as _};
use std::io::{BufRead, BufReader, Cursor, Read, Write};
use std::net::TcpStream;
use std::time::Duration;

use crate::core::bigint::BigInt;
use crate::core::check::quarantine_bad_row_table_ty;
use crate::core::syntax::TableTy;
use crate::ffi::{GzipReader, TlsClientConfig, TlsStream};
use crate::formats::json::{JsonValue, json_value_to_dana, parse_json, to_json_compact};
use crate::oracle::value::{TableRow, TableVal, Val};

/// Default maximum HTTPS response body size in bytes (32 MiB, enforced both raw and post-gzip).
pub const DEFAULT_MAX_HTTPS_RESPONSE_BYTES: usize = 32 * 1024 * 1024;
/// Maximum HTTP response header section size (64 KiB).
pub const MAX_HTTPS_HEADER_BYTES: usize = 64 * 1024;
/// Default socket read/write timeout in seconds.
pub const DEFAULT_HTTPS_TIMEOUT_SECS: u64 = 30;

/// Typed error returned by the capability-gated HTTPS client and JSON response helpers.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HttpsError {
    pub message: String,
}

impl HttpsError {
    #[must_use]
    pub fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
        }
    }
}

impl fmt::Display for HttpsError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.message)
    }
}

impl std::error::Error for HttpsError {}

/// Strictly validated `https://` URL.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParsedHttpsUrl {
    pub host: String,
    pub port: u16,
    pub path_and_query: String,
}

impl ParsedHttpsUrl {
    /// Parse and strictly validate an `https://` URL.
    ///
    /// # Errors
    /// Returns [`HttpsError`] if the scheme is not `https`, if userinfo or control bytes are
    /// present, or if the host or port is malformed.
    pub fn parse(raw: &str) -> Result<Self, HttpsError> {
        if raw.bytes().any(|b| b <= 0x20 || b == 0x7F) {
            return Err(HttpsError::new(
                "HTTPS URL contains forbidden whitespace or control characters",
            ));
        }
        let Some((scheme, rest)) = raw.split_once("://") else {
            return Err(HttpsError::new(format!(
                "invalid HTTPS URL `{raw}`: missing `https://` scheme"
            )));
        };
        if scheme.eq_ignore_ascii_case("http") {
            return Err(HttpsError::new(
                "HTTPS required: plain `http://` URLs are forbidden",
            ));
        }
        if !scheme.eq_ignore_ascii_case("https") {
            return Err(HttpsError::new(format!(
                "unsupported URL scheme `{scheme}://`: only `https://` is permitted"
            )));
        }

        // Drop any `#fragment`
        let without_frag = rest.split_once('#').map_or(rest, |(before, _)| before);
        let split_pos = without_frag.find(['/', '?']).unwrap_or(without_frag.len());
        let authority = &without_frag[..split_pos];
        let tail = &without_frag[split_pos..];

        if authority.is_empty() {
            return Err(HttpsError::new("HTTPS URL is missing host"));
        }
        if authority.contains('@') {
            return Err(HttpsError::new(
                "userinfo (`user@host`) is forbidden in HTTPS URLs",
            ));
        }

        let (host, port) = if let Some(after_lb) = authority.strip_prefix('[') {
            // Bracketed IPv6 literal `[::1]` or `[::1]:8443`
            let Some((ipv6, after_rb)) = after_lb.split_once(']') else {
                return Err(HttpsError::new("unterminated IPv6 literal in HTTPS URL"));
            };
            if ipv6.is_empty() {
                return Err(HttpsError::new("empty IPv6 literal in HTTPS URL"));
            }
            let port = if after_rb.is_empty() {
                443u16
            } else if let Some(port_str) = after_rb.strip_prefix(':') {
                parse_port(port_str)?
            } else {
                return Err(HttpsError::new("invalid authority after IPv6 literal"));
            };
            (ipv6.to_string(), port)
        } else if let Some((h, port_str)) = authority.rsplit_once(':') {
            if h.contains(':') {
                return Err(HttpsError::new(
                    "unbracketed IPv6 address in HTTPS URL (use `[addr]`)",
                ));
            }
            if h.is_empty() {
                return Err(HttpsError::new("HTTPS URL is missing host before `:port`"));
            }
            (h.to_string(), parse_port(port_str)?)
        } else {
            (authority.to_string(), 443u16)
        };

        let path_and_query = if tail.is_empty() {
            "/".to_string()
        } else if tail.starts_with('?') {
            format!("/{tail}")
        } else {
            tail.to_string()
        };

        Ok(Self {
            host,
            port,
            path_and_query,
        })
    }

    /// Parse an `https://` URL and enforce exact ASCII case-insensitive match against `allowed_host`.
    ///
    /// # Errors
    /// Returns [`HttpsError`] if URL parsing fails or if the host does not match `allowed_host`.
    pub fn parse_and_check_host(raw: &str, allowed_host: &str) -> Result<Self, HttpsError> {
        let parsed = Self::parse(raw)?;
        let expected = allowed_host
            .strip_prefix('[')
            .and_then(|s| s.strip_suffix(']'))
            .unwrap_or(allowed_host);
        if !parsed.host.eq_ignore_ascii_case(expected) {
            return Err(HttpsError::new(format!(
                "HTTPS host `{}` is not permitted by `HttpsAllow(\"{allowed_host}\")`",
                parsed.host
            )));
        }
        Ok(parsed)
    }

    /// Format the HTTP `Host:` header value (omits `:443`, brackets IPv6 literals).
    #[must_use]
    pub fn host_header(&self) -> String {
        let formatted_host = if self.host.contains(':') {
            format!("[{}]", self.host)
        } else {
            self.host.clone()
        };
        if self.port == 443 {
            formatted_host
        } else {
            format!("{formatted_host}:{}", self.port)
        }
    }
}

pub(crate) fn parse_nonzero_port(s: &str, scheme_label: &str) -> Result<u16, HttpsError> {
    let p: u16 = s
        .parse()
        .map_err(|_| HttpsError::new(format!("invalid {scheme_label} port `{s}`")))?;
    if p == 0 {
        return Err(HttpsError::new(format!("{scheme_label} port cannot be 0")));
    }
    Ok(p)
}

fn parse_port(s: &str) -> Result<u16, HttpsError> {
    parse_nonzero_port(s, "HTTPS")
}

/// Client configuration for capability-gated HTTPS requests.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HttpsClientConfig {
    /// Optional custom PEM CA certificate path (e.g., for loopback tests or private CAs).
    pub ca_cert_path: Option<String>,
    /// Hard upper bound on response body bytes (both raw and post-gzip).
    pub max_response_bytes: usize,
    /// Socket read/write timeout in seconds.
    pub timeout_secs: u64,
}

/// Type alias for [`HttpsClientConfig`].
pub type HttpsConfig = HttpsClientConfig;

impl Default for HttpsClientConfig {
    fn default() -> Self {
        Self {
            ca_cert_path: None,
            max_response_bytes: DEFAULT_MAX_HTTPS_RESPONSE_BYTES,
            timeout_secs: DEFAULT_HTTPS_TIMEOUT_SECS,
        }
    }
}

/// Decoded HTTP/1.1 response returned by [`https_get_bytes`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HttpsResponse {
    pub status: u16,
    pub headers: Vec<(String, String)>,
    pub body: Vec<u8>,
}

/// Perform a capability-gated HTTP/1.1 request (`GET`, `POST`, `PUT`, etc.) over verified TLS
/// (`verify_peer: true`, `verify_hostname: true`), strictly enforcing `allowed_host`, rejecting
/// redirects & non-2xx status codes, supporting chunked transfer-encoding and transparent gzip
/// decompression.
///
/// # Errors
/// Returns [`HttpsError`] on scheme/host policy denial, invalid headers, TLS handshake or
/// certificate failure, non-2xx status (including redirects), malformed HTTP framing, or size cap breach.
pub(crate) fn build_http_request_head(
    method: &str,
    path_and_query: &str,
    host_header: &str,
    headers: &[(String, String)],
    body: Option<&[u8]>,
    cap_label: &str,
) -> Result<String, HttpsError> {
    let mut has_content_type = false;
    for (k, v) in headers {
        if k.is_empty()
            || k.bytes()
                .any(|b| b <= 0x20 || b >= 0x7F || b == b':' || b == b'\r' || b == b'\n')
        {
            return Err(HttpsError::new(format!("invalid HTTP header name `{k}`")));
        }
        if v.bytes().any(|b| b == b'\r' || b == b'\n' || b == 0) {
            return Err(HttpsError::new(format!(
                "HTTP header `{k}` value contains forbidden CR/LF/NUL character"
            )));
        }
        if k.eq_ignore_ascii_case("host") {
            return Err(HttpsError::new(format!(
                "overriding the `Host` header is forbidden on `{cap_label}` requests"
            )));
        }
        if k.eq_ignore_ascii_case("content-length") || k.eq_ignore_ascii_case("transfer-encoding") {
            return Err(HttpsError::new(format!(
                "overriding `{k}` header is forbidden on `{cap_label}` requests"
            )));
        }
        if k.eq_ignore_ascii_case("content-type") {
            has_content_type = true;
        }
    }

    let mut req = String::new();
    let _ = write!(
        req,
        "{method} {path_and_query} HTTP/1.1\r\nHost: {host_header}\r\nUser-Agent: dana/0.2\r\nAccept: application/json\r\nAccept-Encoding: gzip\r\nConnection: close\r\n",
    );
    if let Some(payload) = body {
        if !has_content_type {
            req.push_str("Content-Type: application/json\r\n");
        }
        let _ = write!(req, "Content-Length: {}\r\n", payload.len());
    }
    for (k, v) in headers {
        if k.eq_ignore_ascii_case("connection") || k.eq_ignore_ascii_case("accept-encoding") {
            continue;
        }
        let _ = write!(req, "{k}: {v}\r\n");
    }
    req.push_str("\r\n");
    Ok(req)
}

pub(crate) fn write_http_request<W: Write>(
    stream: &mut W,
    head: &str,
    body: Option<&[u8]>,
    cap_label: &str,
) -> Result<(), HttpsError> {
    stream
        .write_all(head.as_bytes())
        .map_err(|e| HttpsError::new(format!("{cap_label} request write failed: {e}")))?;
    if let Some(payload) = body
        && !payload.is_empty()
    {
        stream
            .write_all(payload)
            .map_err(|e| HttpsError::new(format!("{cap_label} body write failed: {e}")))?;
    }
    Ok(())
}

pub fn https_request_bytes(
    method: &str,
    url: &str,
    allowed_host: &str,
    headers: &[(String, String)],
    body: Option<&[u8]>,
    cfg: &HttpsClientConfig,
) -> Result<HttpsResponse, HttpsError> {
    let parsed = ParsedHttpsUrl::parse_and_check_host(url, allowed_host)?;
    let req_head = build_http_request_head(
        method,
        &parsed.path_and_query,
        &parsed.host_header(),
        headers,
        body,
        "HttpsAllow",
    )?;

    let tcp = TcpStream::connect((parsed.host.as_str(), parsed.port))
        .map_err(|e| HttpsError::new(format!("HTTPS TCP connect failed: {e}")))?;
    let timeout = Some(Duration::from_secs(cfg.timeout_secs.max(1)));
    let _ = tcp.set_read_timeout(timeout);
    let _ = tcp.set_write_timeout(timeout);

    let tls_cfg = TlsClientConfig {
        verify_peer: true,
        verify_hostname: true,
        ca_cert_path: cfg.ca_cert_path.clone(),
    };
    let mut tls = TlsStream::connect(tcp, &parsed.host, &tls_cfg)
        .map_err(|e| HttpsError::new(format!("HTTPS TLS handshake failed: {e}")))?;

    write_http_request(&mut tls, &req_head, body, "HttpsAllow")?;
    tls.flush()
        .map_err(|e| HttpsError::new(format!("HTTPS request flush failed: {e}")))?;

    parse_http_response_from_reader(tls, cfg)
}

/// Perform a capability-gated HTTP/1.1 `GET` over verified TLS (`verify_peer: true`,
/// `verify_hostname: true`), strictly enforcing `allowed_host`, rejecting redirects & non-2xx
/// status codes, supporting chunked transfer-encoding and transparent gzip decompression.
///
/// # Errors
/// Returns [`HttpsError`] on scheme/host policy denial, invalid headers, TLS handshake or
/// certificate failure, non-2xx status (including redirects), malformed HTTP framing, or size cap breach.
pub fn https_get_bytes(
    url: &str,
    allowed_host: &str,
    headers: &[(String, String)],
    cfg: &HttpsClientConfig,
) -> Result<HttpsResponse, HttpsError> {
    https_request_bytes("GET", url, allowed_host, headers, None, cfg)
}

/// Parse an HTTP/1.1 response from any [`Read`] stream, enforcing header budget, 2xx status
/// (rejecting redirects), `Content-Length` / `Transfer-Encoding: chunked` framing, body byte
/// caps, and transparent `gzip` decompression.
///
/// Reused directly by [`https_get_bytes`] and [`https_get_json`] so in-process fuzzing exercises
/// the exact production HTTP/1.1 decoder.
///
/// # Errors
/// Returns [`HttpsError`] on malformed framing, header/body cap violations, redirects or non-2xx
/// status codes, conflicting `Content-Length`, or invalid/oversized gzip payloads.
pub fn parse_http_response_from_reader<R: Read>(
    stream: R,
    cfg: &HttpsConfig,
) -> Result<HttpsResponse, HttpsError> {
    let mut reader = BufReader::new(stream);
    let mut header_budget = MAX_HTTPS_HEADER_BYTES;

    let status_line = read_http_line(&mut reader, &mut header_budget)?;
    let status = parse_status_line(&status_line)?;

    let mut resp_headers = Vec::new();
    loop {
        let line = read_http_line(&mut reader, &mut header_budget)?;
        if line.is_empty() {
            break;
        }
        let Some((name, value)) = line.split_once(':') else {
            return Err(HttpsError::new(format!(
                "malformed HTTP response header line `{line}`"
            )));
        };
        resp_headers.push((name.trim().to_ascii_lowercase(), value.trim().to_string()));
    }

    if (300..400).contains(&status) {
        return Err(HttpsError::new(format!(
            "HTTPS redirects are forbidden (server returned HTTP {status})"
        )));
    }
    if !(200..300).contains(&status) {
        return Err(HttpsError::new(format!(
            "HTTPS GET failed with HTTP status {status}"
        )));
    }

    let is_chunked = resp_headers.iter().any(|(k, v)| {
        k == "transfer-encoding"
            && v.split(',')
                .any(|tok| tok.trim().eq_ignore_ascii_case("chunked"))
    });
    let content_length: Option<usize> = if is_chunked {
        None
    } else {
        let mut found = None;
        for (k, v) in &resp_headers {
            if k == "content-length" {
                let len: usize = v
                    .parse()
                    .map_err(|_| HttpsError::new(format!("invalid HTTP Content-Length `{v}`")))?;
                if let Some(prev) = found
                    && prev != len
                {
                    return Err(HttpsError::new(
                        "conflicting Content-Length headers in HTTPS response",
                    ));
                }
                found = Some(len);
            }
        }
        found
    };

    let raw_body = if is_chunked {
        read_chunked_body(&mut reader, cfg.max_response_bytes)?
    } else if let Some(len) = content_length {
        if len > cfg.max_response_bytes {
            return Err(HttpsError::new(format!(
                "HTTPS response Content-Length ({len}) exceeds limit ({})",
                cfg.max_response_bytes
            )));
        }
        // Stream lazily via `take(len)` so truncated responses claiming a huge `Content-Length`
        // never eagerly preallocate `len` bytes before observing EOF.
        let mut buf = Vec::with_capacity(len.min(64 * 1024));
        reader
            .by_ref()
            .take(len as u64)
            .read_to_end(&mut buf)
            .map_err(|e| HttpsError::new(format!("truncated HTTPS response body: {e}")))?;
        if buf.len() != len {
            return Err(HttpsError::new(format!(
                "truncated HTTPS response body: expected {len} bytes, got {}",
                buf.len()
            )));
        }
        buf
    } else {
        read_to_eof_capped(&mut reader, cfg.max_response_bytes)?
    };

    let content_encoding = resp_headers
        .iter()
        .find(|(k, _)| k == "content-encoding")
        .map(|(_, v)| v.to_ascii_lowercase());
    let body = match content_encoding.as_deref() {
        None | Some("" | "identity") => raw_body,
        Some("gzip" | "x-gzip") => {
            let gz = GzipReader::new(Cursor::new(raw_body))
                .map_err(|e| HttpsError::new(format!("gzip init failed: {e}")))?;
            let mut limited = gz.take(cfg.max_response_bytes.saturating_add(1) as u64);
            let mut out = Vec::new();
            limited
                .read_to_end(&mut out)
                .map_err(|e| HttpsError::new(format!("gzip response decode failed: {e}")))?;
            if out.len() > cfg.max_response_bytes {
                return Err(HttpsError::new(format!(
                    "gzip-decoded HTTPS response exceeds limit ({})",
                    cfg.max_response_bytes
                )));
            }
            out
        }
        Some(other) => {
            return Err(HttpsError::new(format!(
                "unsupported HTTP Content-Encoding `{other}`"
            )));
        }
    };

    Ok(HttpsResponse {
        status,
        headers: resp_headers,
        body,
    })
}

fn read_http_line<R: BufRead>(reader: &mut R, budget: &mut usize) -> Result<String, HttpsError> {
    if *budget == 0 {
        return Err(HttpsError::new(
            "HTTPS response headers exceed maximum header size",
        ));
    }
    let mut raw = Vec::new();
    let cap = budget.saturating_add(1) as u64;
    let mut limited = reader.take(cap);
    let n = limited
        .read_until(b'\n', &mut raw)
        .map_err(|e| HttpsError::new(format!("HTTPS header read failed: {e}")))?;
    if n == 0 {
        return Err(HttpsError::new(
            "unexpected EOF while reading HTTPS response headers",
        ));
    }
    if n > *budget {
        return Err(HttpsError::new(
            "HTTPS response headers exceed maximum header size",
        ));
    }
    *budget -= n;
    let s = String::from_utf8(raw)
        .map_err(|_| HttpsError::new("non-UTF-8 bytes in HTTP response header"))?;
    Ok(s.trim_end_matches(['\r', '\n']).to_string())
}

fn parse_status_line(line: &str) -> Result<u16, HttpsError> {
    let mut parts = line.split_ascii_whitespace();
    let Some(ver) = parts.next() else {
        return Err(HttpsError::new("empty HTTP response status line"));
    };
    if !ver.starts_with("HTTP/1.") {
        return Err(HttpsError::new(format!(
            "unsupported HTTP response version `{ver}`"
        )));
    }
    let Some(code_str) = parts.next() else {
        return Err(HttpsError::new(format!(
            "missing HTTP status code in `{line}`"
        )));
    };
    code_str
        .parse::<u16>()
        .map_err(|_| HttpsError::new(format!("invalid HTTP status code `{code_str}`")))
}

fn read_chunked_body<R: BufRead>(reader: &mut R, max_bytes: usize) -> Result<Vec<u8>, HttpsError> {
    let mut out = Vec::new();
    let mut line_budget = MAX_HTTPS_HEADER_BYTES;
    loop {
        let size_line = read_http_line(reader, &mut line_budget)?;
        let hex_part = size_line
            .split_once(';')
            .map_or(size_line.as_str(), |(h, _)| h)
            .trim();
        let chunk_size = usize::from_str_radix(hex_part, 16)
            .map_err(|_| HttpsError::new(format!("invalid HTTP chunk size `{size_line}`")))?;
        if chunk_size == 0 {
            // Drain optional trailer headers up to blank line
            loop {
                let trailer = read_http_line(reader, &mut line_budget)?;
                if trailer.is_empty() {
                    break;
                }
            }
            return Ok(out);
        }
        if out
            .len()
            .checked_add(chunk_size)
            .is_none_or(|total| total > max_bytes)
        {
            return Err(HttpsError::new(format!(
                "chunked HTTPS response exceeds limit ({max_bytes} bytes)"
            )));
        }
        let before = out.len();
        reader
            .by_ref()
            .take(chunk_size as u64)
            .read_to_end(&mut out)
            .map_err(|e| HttpsError::new(format!("truncated HTTP chunk payload: {e}")))?;
        if out.len() - before != chunk_size {
            return Err(HttpsError::new(format!(
                "truncated HTTP chunk payload: expected {chunk_size} bytes, got {}",
                out.len() - before
            )));
        }
        // Read trailing CRLF (or LF) after chunk data
        let mut crlf = [0u8; 2];
        reader
            .read_exact(&mut crlf[..1])
            .map_err(|e| HttpsError::new(format!("missing HTTP chunk terminator: {e}")))?;
        if crlf[0] == b'\r' {
            reader
                .read_exact(&mut crlf[1..2])
                .map_err(|e| HttpsError::new(format!("truncated HTTP chunk CRLF: {e}")))?;
            if crlf[1] != b'\n' {
                return Err(HttpsError::new("invalid HTTP chunk CRLF terminator"));
            }
        } else if crlf[0] != b'\n' {
            return Err(HttpsError::new("invalid HTTP chunk line terminator"));
        }
    }
}

fn read_to_eof_capped<R: Read>(reader: &mut R, max_bytes: usize) -> Result<Vec<u8>, HttpsError> {
    let mut out = Vec::new();
    let mut limited = reader.take(max_bytes.saturating_add(1) as u64);
    limited
        .read_to_end(&mut out)
        .map_err(|e| HttpsError::new(format!("HTTPS body read failed: {e}")))?;
    if out.len() > max_bytes {
        return Err(HttpsError::new(format!(
            "HTTPS response body exceeds limit ({max_bytes} bytes)"
        )));
    }
    Ok(out)
}

pub(crate) fn decode_json_response(
    resp: HttpsResponse,
    scheme_label: &str,
    allow_empty_null: bool,
) -> Result<JsonResponse, HttpsError> {
    if allow_empty_null && resp.body.iter().all(u8::is_ascii_whitespace) {
        return Ok(JsonResponse::from_value(JsonValue::Null));
    }
    let text = String::from_utf8(resp.body).map_err(|e| {
        HttpsError::new(format!(
            "{scheme_label} JSON response is not valid UTF-8: {e}"
        ))
    })?;
    JsonResponse::from_json_str(&text)
}

/// Perform a capability-gated HTTPS `GET` and parse the UTF-8 JSON body into a [`JsonResponse`].
///
/// # Errors
/// Returns [`HttpsError`] on transport/policy/status failure or invalid UTF-8 / JSON.
pub fn https_get_json(
    url: &str,
    allowed_host: &str,
    headers: &[(String, String)],
    cfg: &HttpsClientConfig,
) -> Result<JsonResponse, HttpsError> {
    let resp = https_get_bytes(url, allowed_host, headers, cfg)?;
    decode_json_response(resp, "HTTPS", false)
}

fn https_write_json(
    method: &str,
    url: &str,
    allowed_host: &str,
    body_json: &str,
    headers: &[(String, String)],
    cfg: &HttpsClientConfig,
) -> Result<JsonResponse, HttpsError> {
    let resp = https_request_bytes(
        method,
        url,
        allowed_host,
        headers,
        Some(body_json.as_bytes()),
        cfg,
    )?;
    decode_json_response(resp, "HTTPS", true)
}

/// Perform a capability-gated HTTPS `POST` with a JSON payload and parse the response JSON (empty
/// 2xx responses decode as `null`).
///
/// # Errors
/// Returns [`HttpsError`] on transport/policy/status failure or non-empty invalid UTF-8 / JSON.
pub fn https_post_json(
    url: &str,
    allowed_host: &str,
    body_json: &str,
    headers: &[(String, String)],
    cfg: &HttpsClientConfig,
) -> Result<JsonResponse, HttpsError> {
    https_write_json("POST", url, allowed_host, body_json, headers, cfg)
}

/// Perform a capability-gated HTTPS `PUT` with a JSON payload and parse the response JSON (empty
/// 2xx responses decode as `null`).
///
/// # Errors
/// Returns [`HttpsError`] on transport/policy/status failure or non-empty invalid UTF-8 / JSON.
pub fn https_put_json(
    url: &str,
    allowed_host: &str,
    body_json: &str,
    headers: &[(String, String)],
    cfg: &HttpsClientConfig,
) -> Result<JsonResponse, HttpsError> {
    https_write_json("PUT", url, allowed_host, body_json, headers, cfg)
}

/// Resolve a field path against an arbitrary [`JsonValue`], checking exact object key first and
/// otherwise walking dotted object keys and numeric array indices (e.g. `"geometry.coordinates.0"`).
#[must_use]
pub fn resolve_json_path<'a>(root: &'a JsonValue, path: &str) -> Option<&'a JsonValue> {
    if path.is_empty() {
        return Some(root);
    }
    if let Some(direct) = root.get(path) {
        return Some(direct);
    }
    let mut cur = root;
    for seg in path.split('.') {
        cur = match cur {
            JsonValue::Object(_) => cur.get(seg)?,
            JsonValue::Array(arr) => arr.get(seg.parse::<usize>().ok()?)?,
            _ => return None,
        };
    }
    Some(cur)
}

// ---------------------------------------------------------------------------
// JsonResponse Runtime Helpers
// ---------------------------------------------------------------------------

/// Parsed JSON response payload exposing typed extraction and quarantine-first table parsing.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct JsonResponse {
    doc: JsonValue,
}

impl JsonResponse {
    /// Parse a raw JSON string into a [`JsonResponse`] using Dana's iterative RFC 8259 parser.
    ///
    /// # Errors
    /// Returns [`HttpsError`] if `raw` is not valid RFC 8259 JSON.
    pub fn from_json_str(raw: &str) -> Result<Self, HttpsError> {
        let doc =
            parse_json(raw).map_err(|e| HttpsError::new(format!("invalid JSON response: {e}")))?;
        Ok(Self { doc })
    }

    #[must_use]
    pub const fn from_value(doc: JsonValue) -> Self {
        Self { doc }
    }

    #[must_use]
    pub const fn value(&self) -> &JsonValue {
        &self.doc
    }

    /// Resolve a field path (exact key first, otherwise dotted nested object/array path like
    /// `"meta.has_more"` or `"items.0.id"`).
    #[must_use]
    pub fn resolve_path(&self, field: &str) -> Option<&JsonValue> {
        resolve_json_path(&self.doc, field)
    }

    /// Extract a JSON array at `field` (supporting dotted keys) into quarantine-first
    /// `(valid_rows, bad_rows)` tables matching `schema` and `check_constraint`.
    ///
    /// # Errors
    /// Returns an error string if `field` does not resolve to a JSON array.
    pub fn parse_table<F>(
        &self,
        field: &str,
        schema: &TableTy,
        check_constraint: F,
    ) -> Result<(TableVal, TableVal), String>
    where
        F: FnMut(usize, &Val) -> bool,
    {
        self.parse_table_with_fields(field, schema, &HashMap::new(), check_constraint)
    }

    /// Extract a JSON array at `field` using optional per-column dotted object/array path
    /// overrides in `field_paths` (`column_name -> "nested.path.or.0"`).
    ///
    /// # Errors
    /// Returns an error string if `field` does not resolve to a JSON array.
    pub fn parse_table_with_fields<F>(
        &self,
        field: &str,
        schema: &TableTy,
        field_paths: &HashMap<String, String>,
        mut check_constraint: F,
    ) -> Result<(TableVal, TableVal), String>
    where
        F: FnMut(usize, &Val) -> bool,
    {
        let target = self
            .resolve_path(field)
            .ok_or_else(|| format!("JSON response missing field `{field}`"))?;
        let JsonValue::Array(items) = target else {
            return Err(format!("JSON response field `{field}` is not an array"));
        };

        let bad_tt = quarantine_bad_row_table_ty(schema);
        let mut good_rows = Vec::with_capacity(items.len());
        let mut bad_rows = Vec::new();

        for (idx, item) in items.iter().enumerate() {
            let line_no = idx + 1;
            let raw_item = to_json_compact(item);
            let valid_container = item.as_object().is_some()
                || (!field_paths.is_empty() && matches!(item, JsonValue::Array(_)));
            if !valid_container {
                bad_rows.push(TableRow {
                    cells: vec![
                        Val::Int(BigInt::from(line_no)),
                        Val::Text(String::new()),
                        Val::Text("BadJson".to_string()),
                        Val::Text(raw_item.clone()),
                        Val::Text(raw_item),
                    ],
                    group_meta: None,
                });
                continue;
            }

            let mut cells = Vec::with_capacity(schema.cols.len());
            let mut bad_hit: Option<(&str, &str, String)> = None;

            for (ci, col) in schema.cols.iter().enumerate() {
                let raw_jval = if let Some(path) = field_paths.get(&col.name) {
                    resolve_json_path(item, path)
                } else {
                    item.get(&col.name)
                };
                match json_value_to_dana(raw_jval, &col.ty) {
                    Ok(val) => {
                        let ok = match &val {
                            Val::OptNone => true,
                            Val::OptSome(inner) => check_constraint(ci, inner),
                            other => check_constraint(ci, other),
                        };
                        if !ok {
                            let raw_str = raw_jval.map(to_json_compact).unwrap_or_default();
                            bad_hit = Some((col.name.as_str(), "ConstraintFailed", raw_str));
                            break;
                        }
                        cells.push(val);
                    }
                    Err(kind) => {
                        let raw_str = raw_jval.map(to_json_compact).unwrap_or_default();
                        bad_hit = Some((col.name.as_str(), kind, raw_str));
                        break;
                    }
                }
            }

            if let Some((col_name, err_kind, raw_val)) = bad_hit {
                bad_rows.push(TableRow {
                    cells: vec![
                        Val::Int(BigInt::from(line_no)),
                        Val::Text(col_name.to_string()),
                        Val::Text(err_kind.to_string()),
                        Val::Text(raw_val),
                        Val::Text(raw_item),
                    ],
                    group_meta: None,
                });
            } else {
                good_rows.push(TableRow {
                    cells,
                    group_meta: None,
                });
            }
        }

        Ok((
            TableVal {
                cols: schema.cols.clone(),
                rows: good_rows,
            },
            TableVal {
                cols: bad_tt.cols,
                rows: bad_rows,
            },
        ))
    }

    /// Return `true` iff dotted `field` exists in the JSON response and is not `null`.
    #[must_use]
    pub fn has_path(&self, field: &str) -> bool {
        matches!(self.resolve_path(field), Some(v) if !matches!(v, JsonValue::Null))
    }

    /// Read a `Bool` at `field` (supports dotted keys; missing or `null` returns `false`).
    ///
    /// # Errors
    /// Returns an error string if the value exists and is neither `bool` nor `null`.
    pub fn bool_at(&self, field: &str) -> Result<bool, String> {
        match self.resolve_path(field) {
            Some(JsonValue::Bool(b)) => Ok(*b),
            None | Some(JsonValue::Null) => Ok(false),
            Some(_) => Err(format!("JSON response field `{field}` is not a Bool")),
        }
    }

    /// Read a `Text` string at `field` (supports dotted keys; missing or `null` returns `""`).
    ///
    /// # Errors
    /// Returns an error string if the value exists and is neither a string nor `null`.
    pub fn text_at(&self, field: &str) -> Result<String, String> {
        match self.resolve_path(field) {
            Some(JsonValue::Str(s)) => Ok(s.clone()),
            None | Some(JsonValue::Null) => Ok(String::new()),
            Some(_) => Err(format!("JSON response field `{field}` is not Text")),
        }
    }

    /// Read an `Int` (`i64`) at `field` (supports dotted keys).
    ///
    /// # Errors
    /// Returns an error string if `field` is missing or is not an exact `i64` JSON number.
    pub fn int_at(&self, field: &str) -> Result<i64, String> {
        let Some(v) = self.resolve_path(field) else {
            return Err(format!("JSON response missing integer field `{field}`"));
        };
        v.as_i64()
            .ok_or_else(|| format!("JSON response field `{field}` is not an Int"))
    }
}
