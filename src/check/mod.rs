//! Dana static analysis: `dana.policy` parsing, multi-module resolution, boundary
//! schema validation, structural `Table(...)` type inference, and flow-sensitive
//! sensitivity & capability verification.

pub mod policy;
pub mod resolve;
pub mod types;

pub use policy::parse_policy;
pub use resolve::{ModuleOrigin, ResolvedModule, ResolvedProgram, resolve_module, resolve_path};
pub use types::{CheckedProgram, check_module, check_resolved};
