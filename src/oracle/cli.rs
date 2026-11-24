//! Strict CLI argument parser for `dana-oracle`, matching `formal/Main.lean` 1-to-1.

use std::fmt;

use crate::core::syntax::{Tag, TagSet};

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub enum CliMode {
    #[default]
    Run,
    Check,
    Fmt,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CliOpts {
    pub mode: CliMode,
    pub path: String,
    pub fuel: usize,
    pub allow_export: TagSet,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CliError {
    pub message: String,
}

impl CliError {
    #[must_use]
    pub fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
        }
    }
}

impl fmt::Display for CliError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.message)
    }
}

impl std::error::Error for CliError {}

fn is_tag_start_char(c: char) -> bool {
    c.is_ascii_alphabetic() || c == '_'
}

fn is_tag_ident_char(c: char) -> bool {
    is_tag_start_char(c) || c.is_ascii_digit() || c == '-'
}

fn parse_ascii_nat(raw: &str) -> Option<usize> {
    if raw.is_empty() || !raw.bytes().all(|b| b.is_ascii_digit()) {
        return None;
    }
    Some(raw.parse::<usize>().unwrap_or(usize::MAX))
}

pub fn parse_comma_tags(raw: &str) -> Result<TagSet, CliError> {
    if raw.is_empty() {
        return Err(CliError::new("empty tag list for --allow-export"));
    }
    if raw.starts_with("--") {
        return Err(CliError::new(format!(
            "missing argument for --allow-export (got flag '{raw}')"
        )));
    }
    let mut seen: Vec<Tag> = Vec::new();
    for part in raw.split(',') {
        let mut chars = part.chars();
        let valid = match chars.next() {
            None => false,
            Some(first) => is_tag_start_char(first) && chars.all(is_tag_ident_char),
        };
        if !valid {
            return Err(CliError::new(format!(
                "invalid tag '{part}' in --allow-export"
            )));
        }
        if seen.iter().any(|s| s == part) {
            return Err(CliError::new(format!(
                "duplicate tag '{part}' in --allow-export"
            )));
        }
        seen.push(part.to_string());
    }
    Ok(TagSet::of_list(seen))
}

pub fn parse_cli_args(args: &[String]) -> Result<CliOpts, CliError> {
    let mut mode = CliMode::Run;
    let mut mode_set = false;
    let mut path: Option<String> = None;
    let mut fuel: usize = 4096;
    let mut fuel_set = false;
    let mut allow_export = TagSet::empty();
    let mut allow_export_set = false;

    let mut i = 0;
    while i < args.len() {
        let arg = &args[i];
        match arg.as_str() {
            "run" => {
                if !mode_set && path.is_none() {
                    mode = CliMode::Run;
                    mode_set = true;
                    i += 1;
                } else {
                    return Err(CliError::new("unexpected positional argument 'run'"));
                }
            }
            "check" => {
                if !mode_set && path.is_none() {
                    mode = CliMode::Check;
                    mode_set = true;
                    i += 1;
                } else {
                    return Err(CliError::new("unexpected positional argument 'check'"));
                }
            }
            "fmt" => {
                if !mode_set && path.is_none() {
                    mode = CliMode::Fmt;
                    mode_set = true;
                    i += 1;
                } else {
                    return Err(CliError::new("unexpected positional argument 'fmt'"));
                }
            }
            "--fuel" => {
                let Some(n_str) = args.get(i + 1) else {
                    return Err(CliError::new("missing argument for --fuel"));
                };
                if fuel_set {
                    return Err(CliError::new("duplicate --fuel flag"));
                }
                if n_str.starts_with("--") {
                    return Err(CliError::new(format!(
                        "missing argument for --fuel (got flag '{n_str}')"
                    )));
                }
                match parse_ascii_nat(n_str) {
                    Some(n) => {
                        fuel = n;
                        fuel_set = true;
                        i += 2;
                    }
                    None => {
                        return Err(CliError::new(format!("invalid --fuel integer '{n_str}'")));
                    }
                }
            }
            "--allow-export" => {
                let Some(t_str) = args.get(i + 1) else {
                    return Err(CliError::new("missing argument for --allow-export"));
                };
                if allow_export_set {
                    return Err(CliError::new("duplicate --allow-export flag"));
                }
                allow_export = parse_comma_tags(t_str)?;
                allow_export_set = true;
                i += 2;
            }
            other => {
                if other.starts_with("--") {
                    return Err(CliError::new(format!("unknown flag '{other}'")));
                } else if path.is_none() {
                    path = Some(arg.clone());
                    i += 1;
                } else {
                    return Err(CliError::new(format!(
                        "unexpected positional argument '{other}'"
                    )));
                }
            }
        }
    }

    match path {
        Some(p) => Ok(CliOpts {
            mode,
            path: p,
            fuel,
            allow_export,
        }),
        None => Err(CliError::new(
            "usage: dana-oracle [run|check|fmt] <file.core> [--fuel <N>] [--allow-export <tags>]",
        )),
    }
}
