#![forbid(unsafe_code)]

//! Dana Core IR v0.1 (`core`) and naive row-by-row differential oracle (`oracle`).
//!
//! Zero external crates (`std` only) and `#![forbid(unsafe_code)]` across the crate.

pub mod core;
pub mod oracle;
