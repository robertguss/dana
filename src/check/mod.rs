//! Dana static analysis: `dana.policy` parsing, multi-module resolution, boundary
//! schema validation, structural `Table(...)` type inference, and flow-sensitive
//! sensitivity & capability verification.

pub mod policy;
pub mod resolve;
pub mod types;
pub mod vendor;

pub use policy::parse_policy;
pub use resolve::{
    ModuleOrigin, ResolvedModule, ResolvedProgram, resolve_module, resolve_module_in_dir,
    resolve_path,
};
pub use types::{
    CheckedProgram, check_module, check_module_with_lock, check_resolved, check_resolved_with_lock,
};
pub use vendor::{
    VENDOR_LOCK_FILENAME, VendorEntry, VendorLock, expected_vendor_module_rel_path,
    format_vendor_lock, parse_vendor_lock, pin_vendor_dir, sha256_hex, verify_vendor_dir,
    verify_vendor_module,
};
