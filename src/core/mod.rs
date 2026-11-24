//! Dana Core IR v0.1 AST, arbitrary-precision integer arithmetic,
//! canonical `(dana-core 0.1 ...)` wire codec, and decidable static verifier.

pub mod bigint;
pub mod check;
pub mod stack;
pub mod syntax;
pub mod text;

pub use bigint::{BigInt, DEC_MAX, DEC_MIN, DEC_SCALE, INT64_MAX, INT64_MIN};
pub use check::{
    CheckError, check_program, is_safe_relative_path, is_well_typed_program, join_confined_path,
};
pub use stack::with_large_stack;
pub use syntax::*;
pub use text::{
    SExp, WireError, parse_canonical_sexp, parse_program, print_program, print_report, print_sexp,
};
