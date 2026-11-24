#![forbid(unsafe_code)]

//! Thin binary entry point for the `dana` CLI toolchain.

use std::process::ExitCode;

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let code = dana::cli::run_cli(&args);
    let byte = u8::try_from(code).unwrap_or(1);
    ExitCode::from(byte)
}
