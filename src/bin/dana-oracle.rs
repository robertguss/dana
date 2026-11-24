#![forbid(unsafe_code)]

//! Standalone Dana Core IR v0.1 CLI oracle (`dana-oracle`), mirroring `formal/Main.lean`.
//!
//! Usage:
//!   dana-oracle <file.core> [--fuel N] [--allow-export tag1,tag2]
//!   dana-oracle run <file.core> [--fuel N] [--allow-export tag1,tag2]
//!   dana-oracle check <file.core>
//!   dana-oracle fmt <file.core>

use std::env;
use std::fs;
use std::io::{self, Write};
use std::process::ExitCode;

use dana::core::{check_program, parse_program, print_program, print_report, with_large_stack};
use dana::oracle::{CliMode, ExitStatus, World, parse_cli_args, run_program};

fn run_cli(args: &[String]) -> u8 {
    let opts = match parse_cli_args(args) {
        Ok(o) => o,
        Err(e) => {
            eprintln!("dana-oracle error: {e}");
            return 2;
        }
    };
    let wire = match fs::read_to_string(&opts.path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("dana-oracle io error: {e}");
            return 2;
        }
    };
    let prog = match parse_program(&wire) {
        Ok(p) => p,
        Err(e) => {
            eprintln!("dana-oracle parse error: {e}");
            return 1;
        }
    };
    if opts.mode == CliMode::Fmt {
        let mut stdout = io::stdout().lock();
        if let Err(e) = stdout.write_all(print_program(&prog).as_bytes()) {
            eprintln!("dana-oracle io error: {e}");
            return 2;
        }
        return 0;
    }
    if let Err(e) = check_program(&prog) {
        eprintln!("dana-oracle check error: {e}");
        return 1;
    }
    if opts.mode == CliMode::Check {
        println!("ok");
        return 0;
    }
    let init_world = World {
        runtime_allow_export: opts.allow_export,
        ..World::default()
    };
    match run_program(opts.fuel, &prog, init_world) {
        Err(e) => {
            eprintln!("dana-oracle runtime error: {e}");
            1
        }
        Ok(report) => {
            let mut stdout = io::stdout().lock();
            if let Err(e) = stdout.write_all(print_report(&report).as_bytes()) {
                eprintln!("dana-oracle io error: {e}");
                return 2;
            }
            match report.status {
                ExitStatus::Ok => 0,
                ExitStatus::Stopped | ExitStatus::Failed => 1,
            }
        }
    }
}

fn main() -> ExitCode {
    let args: Vec<String> = env::args().skip(1).collect();
    ExitCode::from(with_large_stack(|| run_cli(&args)))
}
