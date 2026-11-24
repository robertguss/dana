//! Parser parity and formatter idempotence tests against the entire Phase 0 Bison corpus:
//! - All 10 `examples/*.dana`
//! - All fenced ```dana blocks in `docs/reference/README.md` and `README.md`
//! - All `grammar/tests/{good,bad,bad-files}/*.dana`

use std::fs;
use std::path::{Path, PathBuf};

use dana::base::{FileId, SourceMap};
use dana::syntax::{format_module, parse_fragment, parse_module};

fn repo_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

fn collect_dana_files(dir: &Path) -> Result<Vec<PathBuf>, String> {
    let entries = fs::read_dir(dir).map_err(|e| format!("read_dir {}: {e}", dir.display()))?;
    let mut files: Vec<PathBuf> = entries
        .filter_map(|e| e.ok().map(|de| de.path()))
        .filter(|p| p.extension().and_then(|s| s.to_str()) == Some("dana"))
        .collect();
    files.sort();
    Ok(files)
}

fn extract_markdown_blocks(md_path: &Path) -> Result<Vec<(usize, bool, String)>, String> {
    let text =
        fs::read_to_string(md_path).map_err(|e| format!("read {}: {e}", md_path.display()))?;
    let mut blocks = Vec::new();
    let mut is_fragment = true;
    let mut in_block = false;
    let mut buf = Vec::new();
    let mut start_line = 0usize;

    for (idx, line) in text.lines().enumerate() {
        let trimmed = line.trim();
        if trimmed.starts_with("<!--") && trimmed.contains("dana-example:") {
            is_fragment = !trimmed.contains("file");
            continue;
        }
        if !in_block && trimmed == "```dana" {
            in_block = true;
            buf.clear();
            start_line = idx + 2;
            continue;
        }
        if in_block && trimmed == "```" {
            let mut code = buf.join("\n");
            code.push('\n');
            blocks.push((start_line, is_fragment, code));
            in_block = false;
            is_fragment = true;
            continue;
        }
        if in_block {
            buf.push(line);
        }
    }
    Ok(blocks)
}

#[test]
fn examples_parse_and_format_idempotently() -> Result<(), String> {
    let root = repo_root();
    let examples = collect_dana_files(&root.join("examples"))?;
    assert_eq!(examples.len(), 10, "expected all 10 Phase 0 examples");

    let mut sm = SourceMap::new();
    for path in examples {
        let src = fs::read_to_string(&path).map_err(|e| format!("read {}: {e}", path.display()))?;
        let fid = sm.add_file(path.display().to_string(), src.clone());
        let module = parse_module(fid, &src).map_err(|d| {
            format!(
                "failed to parse {}:\n{}",
                path.display(),
                dana::base::render_diagnostic(&d, &sm)
            )
        })?;

        let formatted1 = format_module(&module);
        let fid2 = sm.add_file(format!("{}:fmt1", path.display()), formatted1.clone());
        let module2 = parse_module(fid2, &formatted1).map_err(|d| {
            format!(
                "formatted output of {} failed to re-parse:\n{}\n--- FORMATTED ---\n{formatted1}",
                path.display(),
                dana::base::render_diagnostic(&d, &sm)
            )
        })?;
        assert_eq!(
            module.comments.len(),
            module2.comments.len(),
            "comment count changed after formatting {}",
            path.display()
        );
        let formatted2 = format_module(&module2);
        assert_eq!(
            formatted1,
            formatted2,
            "formatter not idempotent on {}",
            path.display()
        );
    }
    Ok(())
}

#[test]
fn reference_and_readme_snippets_parse() -> Result<(), String> {
    let root = repo_root();
    let mut sm = SourceMap::new();
    let mut total = 0usize;

    for rel in ["docs/reference/README.md", "README.md"] {
        let md_path = root.join(rel);
        for (line, is_fragment, code) in extract_markdown_blocks(&md_path)? {
            total += 1;
            let fid = sm.add_file(format!("{rel}:{line}"), code.clone());
            if is_fragment {
                parse_fragment(fid, &code).map_err(|d| {
                    format!(
                        "failed to parse fragment {rel}:{line}:\n{}",
                        dana::base::render_diagnostic(&d, &sm)
                    )
                })?;
            } else {
                parse_module(fid, &code).map_err(|d| {
                    format!(
                        "failed to parse file snippet {rel}:{line}:\n{}",
                        dana::base::render_diagnostic(&d, &sm)
                    )
                })?;
            }
        }
    }
    assert!(total >= 10, "expected >= 10 fenced dana blocks in docs");
    Ok(())
}

#[test]
fn bison_grammar_positive_and_negative_parity() -> Result<(), String> {
    let root = repo_root();
    let mut sm = SourceMap::new();

    let good = collect_dana_files(&root.join("grammar/tests/good"))?;
    assert!(!good.is_empty());
    for path in good {
        let src = fs::read_to_string(&path).map_err(|e| format!("read {}: {e}", path.display()))?;
        let fid = sm.add_file(path.display().to_string(), src.clone());
        parse_fragment(fid, &src).map_err(|d| {
            format!(
                "positive test {} should parse:\n{}",
                path.display(),
                dana::base::render_diagnostic(&d, &sm)
            )
        })?;
    }

    let bad = collect_dana_files(&root.join("grammar/tests/bad"))?;
    assert!(!bad.is_empty());
    for path in bad {
        let src = fs::read_to_string(&path).map_err(|e| format!("read {}: {e}", path.display()))?;
        let fid = sm.add_file(path.display().to_string(), src.clone());
        assert!(
            parse_fragment(fid, &src).is_err(),
            "negative fragment {} unexpectedly parsed",
            path.display()
        );
    }

    let bad_files = collect_dana_files(&root.join("grammar/tests/bad-files"))?;
    assert!(!bad_files.is_empty());
    for path in bad_files {
        let src = fs::read_to_string(&path).map_err(|e| format!("read {}: {e}", path.display()))?;
        let fid = sm.add_file(path.display().to_string(), src.clone());
        assert!(
            parse_module(fid, &src).is_err(),
            "negative full file {} unexpectedly parsed",
            path.display()
        );
    }
    Ok(())
}

#[test]
fn deep_nesting_returns_diagnostic_instead_of_stack_overflow() {
    let depth = 2000usize;
    let src = format!("{}{}", "(".repeat(depth), ")".repeat(depth));
    let res = parse_fragment(FileId(0), &src);
    assert!(res.is_err(), "deep nesting should hit MAX_NESTING_DEPTH");
}

#[test]
fn formatter_preserves_else_comments_inline_comments_and_blank_lines() -> Result<(), String> {
    let src = "\
module FmtPreservation

schema Section
  a: Text
  b: Text  # stays on b
  c: Int
  d: Float?  # stays on d
end

fn f(c: Bool) : Int
  x = 1

  if c
    # comment in then
    x + 1
  else if not c
    # comment in else if
    x + 2
  else
    # comment in else
    x + 3
  end
end
";
    let mut sm = SourceMap::new();
    let fid = sm.add_file("fmt_preserve.dana", src);
    let m = parse_module(fid, src).map_err(|d| dana::base::render_diagnostic(&d, &sm))?;
    let out = format_module(&m);
    assert_eq!(
        out, src,
        "formatter must preserve else/inline comments and single blank lines exactly"
    );
    Ok(())
}

#[test]
fn diagnostic_snippet_truncates_huge_lines() {
    let huge_line = format!(
        "module Huge\n\nfn main() : Int\n  {}@\nend\n",
        "1 + ".repeat(50_000)
    );
    let mut sm = SourceMap::new();
    let fid = sm.add_file("huge.dana", huge_line.clone());
    let err = parse_module(fid, &huge_line).expect_err("expected lex error on `@`");
    let rendered = dana::base::render_diagnostic(&err, &sm);
    assert!(
        rendered.len() < 1000,
        "rendered diagnostic should truncate huge lines, got {} bytes",
        rendered.len()
    );
    assert!(
        rendered.contains("..."),
        "expected truncation ellipsis in rendered diagnostic:\n{rendered}"
    );
}
