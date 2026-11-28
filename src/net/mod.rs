//! Capability-gated networking utilities (`HttpsAllow` HTTP/1.1 client over OpenSSL TLS).
//!
//! Compiles under `#[forbid(unsafe_code)]` (enforced on `pub mod net` in `src/lib.rs`);
//! all TLS FFI stays isolated in [`crate::ffi::tls`].

pub mod https;

pub use https::{
    DEFAULT_MAX_HTTPS_RESPONSE_BYTES, HttpsClientConfig, HttpsConfig, HttpsError, HttpsResponse,
    JsonResponse, ParsedHttpsUrl, https_get_bytes, https_get_json, https_post_json, https_put_json,
    https_request_bytes, parse_http_response_from_reader, resolve_json_path,
};
