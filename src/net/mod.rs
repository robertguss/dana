//! Capability-gated networking utilities (`HttpsAllow` over OpenSSL TLS, plus
//! `LocalHttpAllow` loopback HTTP/1.1 and `LocalSocketAllow` Unix domain socket clients).
//!
//! Compiles under `#[forbid(unsafe_code)]` (enforced on `pub mod net` in `src/lib.rs`);
//! all TLS FFI stays isolated in [`crate::ffi::tls`].

pub mod https;
pub mod local_http;

pub use https::{
    DEFAULT_MAX_HTTPS_RESPONSE_BYTES, HttpsClientConfig, HttpsConfig, HttpsError, HttpsResponse,
    JsonResponse, ParsedHttpsUrl, https_get_bytes, https_get_json, https_post_json, https_put_json,
    https_request_bytes, parse_http_response_from_reader, resolve_json_path,
};
pub use local_http::{
    ParsedLoopbackAuthority, ResolvedLocalHttpUrl, local_http_delete_json, local_http_get_json,
    local_http_request_bytes, local_http_write_json, local_socket_delete_json,
    local_socket_get_json, local_socket_request_bytes, local_socket_write_json,
    parse_local_http_binding_value, parse_loopback_authority, resolve_local_http_url,
    resolve_local_socket_path_and_query, validate_local_socket_path,
};
