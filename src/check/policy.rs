//! Parser for institutional `dana.policy` upper-bound privacy policy files.
//!
//! Grammar (see `examples/dana.policy` and `docs/design/privacy.md`):
//! ```text
//! version 1
//! min_group_size 5
//! forbid manual_declassify
//! forbid repl_show_sensitive
//! forbid local_http
//! forbid local_socket
//! allow console tags [...]
//! allow export "prefix/" tags [...]
//! allow https  "host"    tags [...]
//! allow local_http   "127.0.0.1:8091" tags [...]
//! allow local_socket "/run/mo.sock"   tags [...]
//! allow write  Db.table  tags [...]
//! ```

use crate::base::{DiagCode, Diagnostic, FileId, Span};
use crate::core::bigint::BigInt;
use crate::core::syntax::{Policy, PolicyWriteRule, TagSet};

/// Parse a `dana.policy` document into a verified [`Policy`].
///
/// # Errors
/// Returns a [`Diagnostic`] with [`DiagCode::PolicyError`] on syntax or version errors.
pub fn parse_policy(file: FileId, src: &str) -> Result<Policy, Diagnostic> {
    let mut policy = Policy::default();
    let mut saw_version = false;
    let mut byte_offset = 0usize;

    for raw_line in src.split('\n') {
        let line_start = byte_offset;
        let line_len = raw_line.len();
        byte_offset += line_len + 1;

        let line = raw_line.trim_end_matches('\r');
        // Strip `#` comment outside quotes.
        let code = strip_policy_comment(line).trim();
        if code.is_empty() {
            continue;
        }
        let span = Span::new(
            file,
            u32::try_from(line_start).unwrap_or(u32::MAX),
            u32::try_from(line_start + line_len).unwrap_or(u32::MAX),
        );

        if let Some(rest) = code.strip_prefix("version")
            && rest.starts_with(char::is_whitespace)
        {
            let ver = rest.trim();
            if ver != "1" {
                return Err(Diagnostic::error(
                    DiagCode::PolicyError,
                    format!("unsupported dana.policy version `{ver}` (expected `1`)"),
                )
                .with_span(span));
            }
            saw_version = true;
            continue;
        }

        if let Some(rest) = code.strip_prefix("min_group_size")
            && rest.starts_with(char::is_whitespace)
        {
            let num_str = rest.trim();
            let n: u64 = num_str.parse().map_err(|_| {
                Diagnostic::error(
                    DiagCode::PolicyError,
                    format!("invalid `min_group_size` integer `{num_str}`"),
                )
                .with_span(span)
            })?;
            if n == 0 {
                return Err(Diagnostic::error(
                    DiagCode::PolicyError,
                    "`min_group_size` must be a positive integer",
                )
                .with_span(span));
            }
            policy.min_group_size = BigInt::from(n);
            continue;
        }

        if let Some(rest) = code.strip_prefix("forbid")
            && rest.starts_with(char::is_whitespace)
        {
            match rest.trim() {
                "manual_declassify" => policy.forbid_manual_declassify = true,
                "repl_show_sensitive" => policy.forbid_repl_sensitive = true,
                "local_http" => policy.forbid_local_http = true,
                "local_socket" => policy.forbid_local_socket = true,
                other => {
                    return Err(Diagnostic::error(
                        DiagCode::PolicyError,
                        format!("unknown `forbid` directive `{other}`"),
                    )
                    .with_span(span));
                }
            }
            continue;
        }

        if let Some(rest) = code.strip_prefix("allow")
            && rest.starts_with(char::is_whitespace)
        {
            let rest = rest.trim();
            if let Some(after) = rest.strip_prefix("console")
                && after.starts_with(char::is_whitespace)
            {
                let tags = parse_tags_clause(after.trim(), span)?;
                policy.allow_console = policy.allow_console.union(&tags);
                continue;
            }
            if let Some(after) = rest.strip_prefix("export")
                && after.starts_with(char::is_whitespace)
            {
                let (prefix, tail) = parse_quoted_string(after.trim(), span)?;
                let tags = parse_tags_clause(tail.trim(), span)?;
                policy.allow_export.push((prefix, tags));
                continue;
            }
            if let Some(after) = rest.strip_prefix("https")
                && after.starts_with(char::is_whitespace)
            {
                let (host, tail) = parse_quoted_string(after.trim(), span)?;
                let tags = parse_tags_clause(tail.trim(), span)?;
                policy.allow_https.push((host, tags));
                continue;
            }
            if let Some(after) = rest.strip_prefix("local_http")
                && after.starts_with(char::is_whitespace)
            {
                let (target, tags) = parse_policy_target_and_tags(after.trim(), span)?;
                policy.allow_local_http.push((target, tags));
                continue;
            }
            if let Some(after) = rest.strip_prefix("local_socket")
                && after.starts_with(char::is_whitespace)
            {
                let (target, tags) = parse_policy_target_and_tags(after.trim(), span)?;
                policy.allow_local_socket.push((target, tags));
                continue;
            }
            if let Some(after) = rest.strip_prefix("write")
                && after.starts_with(char::is_whitespace)
            {
                let after = after.trim();
                let split_idx = after.find(char::is_whitespace).ok_or_else(|| {
                    Diagnostic::error(
                        DiagCode::PolicyError,
                        "expected `tags [...]` after `allow write Db.table`",
                    )
                    .with_span(span)
                })?;
                let target = &after[..split_idx];
                let tail = after[split_idx..].trim();
                let (db, table) = target.split_once('.').ok_or_else(|| {
                    Diagnostic::error(
                        DiagCode::PolicyError,
                        format!("expected `Db.table` target, found `{target}`"),
                    )
                    .with_span(span)
                })?;
                if db.is_empty() || table.is_empty() {
                    return Err(Diagnostic::error(
                        DiagCode::PolicyError,
                        format!("invalid `Db.table` target `{target}`"),
                    )
                    .with_span(span));
                }
                let tags = parse_tags_clause(tail, span)?;
                policy.allow_write.push(PolicyWriteRule {
                    db: db.to_string(),
                    table: table.to_string(),
                    tags,
                });
                continue;
            }
        }

        return Err(Diagnostic::error(
            DiagCode::PolicyError,
            format!("unrecognized policy statement: `{code}`"),
        )
        .with_span(span));
    }

    if !saw_version {
        return Err(Diagnostic::error(
            DiagCode::PolicyError,
            "dana.policy must declare `version 1`",
        )
        .with_span(Span::point(file, 0)));
    }

    Ok(policy)
}

fn strip_policy_comment(line: &str) -> &str {
    let mut in_quotes = false;
    let mut escaped = false;
    for (idx, ch) in line.char_indices() {
        if escaped {
            escaped = false;
            continue;
        }
        if in_quotes {
            if ch == '\\' {
                escaped = true;
            } else if ch == '"' {
                in_quotes = false;
            }
        } else if ch == '"' {
            in_quotes = true;
        } else if ch == '#' {
            return &line[..idx];
        }
    }
    line
}

fn parse_quoted_string(s: &str, span: Span) -> Result<(String, &str), Diagnostic> {
    let Some(rest) = s.strip_prefix('"') else {
        return Err(Diagnostic::error(
            DiagCode::PolicyError,
            format!("expected quoted string, found `{s}`"),
        )
        .with_span(span));
    };
    let mut out = String::new();
    let mut escaped = false;
    for (idx, ch) in rest.char_indices() {
        if escaped {
            match ch {
                '"' => out.push('"'),
                '\\' => out.push('\\'),
                'n' => out.push('\n'),
                't' => out.push('\t'),
                other => out.push(other),
            }
            escaped = false;
            continue;
        }
        if ch == '\\' {
            escaped = true;
            continue;
        }
        if ch == '"' {
            return Ok((out, &rest[idx + 1..]));
        }
        out.push(ch);
    }
    Err(
        Diagnostic::error(DiagCode::PolicyError, "unterminated string in dana.policy")
            .with_span(span),
    )
}

fn parse_policy_target_and_tags(s: &str, span: Span) -> Result<(String, TagSet), Diagnostic> {
    if s.starts_with('"') {
        let (target, tail) = parse_quoted_string(s, span)?;
        let tags = parse_tags_clause(tail.trim(), span)?;
        Ok((target, tags))
    } else {
        let split_idx = s.find(char::is_whitespace).ok_or_else(|| {
            Diagnostic::error(
                DiagCode::PolicyError,
                format!("expected `tags [...]` after target `{s}`"),
            )
            .with_span(span)
        })?;
        let target = &s[..split_idx];
        let tail = s[split_idx..].trim();
        if target.is_empty()
            || !target
                .bytes()
                .all(|b| b.is_ascii_alphanumeric() || b == b'_' || b == b'-')
        {
            return Err(Diagnostic::error(
                DiagCode::PolicyError,
                format!("invalid named local target `{target}` in dana.policy"),
            )
            .with_span(span));
        }
        let tags = parse_tags_clause(tail, span)?;
        Ok((target.to_string(), tags))
    }
}

fn parse_tags_clause(s: &str, span: Span) -> Result<TagSet, Diagnostic> {
    let rest = s
        .strip_prefix("tags")
        .filter(|r| r.starts_with(char::is_whitespace) || r.starts_with('['))
        .ok_or_else(|| {
            Diagnostic::error(
                DiagCode::PolicyError,
                format!("expected `tags [...]`, found `{s}`"),
            )
            .with_span(span)
        })?
        .trim();
    let inner = rest
        .strip_prefix('[')
        .and_then(|r| r.strip_suffix(']'))
        .ok_or_else(|| {
            Diagnostic::error(
                DiagCode::PolicyError,
                format!("expected `[tag1, tag2]`, found `{rest}`"),
            )
            .with_span(span)
        })?
        .trim();
    if inner.is_empty() {
        return Ok(TagSet::empty());
    }
    let mut tags = Vec::new();
    for part in inner.split(',') {
        let t = part.trim();
        if t.is_empty()
            || !t
                .bytes()
                .all(|b| b.is_ascii_lowercase() || b.is_ascii_digit() || b == b'_')
        {
            return Err(Diagnostic::error(
                DiagCode::PolicyError,
                format!("invalid sensitivity tag `{t}` in dana.policy"),
            )
            .with_span(span));
        }
        tags.push(t.to_string());
    }
    Ok(TagSet::of_list(tags))
}
