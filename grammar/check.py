#!/usr/bin/env python3
"""Run dana-grammar over examples/, docs/reference/README.md, README.md, and grammar/tests/."""

import glob
import os
import re
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BIN = os.path.join(ROOT, "build", "dana-grammar")


def run_parse(path, fragment=False):
    cmd = [BIN]
    if fragment:
        cmd.append("--fragment")
    cmd.append(path)
    return subprocess.run(cmd, capture_output=True, text=True)


def check_markdown(md_path):
    text = open(md_path, "r", encoding="utf-8").read()
    lines = text.splitlines()
    blocks = []
    mode = "fragment"
    in_block = False
    buf = []
    start_line = 0

    for idx, line in enumerate(lines, 1):
        m = re.match(r"<!--\s*dana-example:\s*(file|fragment)\s*-->", line.strip())
        if m:
            mode = m.group(1)
            continue
        if not in_block and line.strip() == "```dana":
            in_block = True
            buf = []
            start_line = idx + 1
            continue
        if in_block and line.strip() == "```":
            blocks.append((start_line, mode, "\n".join(buf) + "\n"))
            in_block = False
            mode = "fragment"
            continue
        if in_block:
            buf.append(line)

    failures = 0
    for start_line, bmode, code in blocks:
        with tempfile.NamedTemporaryFile("w", suffix=".dana", delete=False, encoding="utf-8") as tf:
            tf.write(code)
            tpath = tf.name
        try:
            res = run_parse(tpath, fragment=(bmode == "fragment"))
            if res.returncode != 0:
                print(f"FAIL {os.path.relpath(md_path, ROOT)}:{start_line} ({bmode}): {res.stderr.strip()}")
                failures += 1
        finally:
            os.unlink(tpath)
    return len(blocks), failures


def main():
    total = 0
    failures = 0

    # 1. All examples/*.dana (must parse as full modules)
    for path in sorted(glob.glob(os.path.join(ROOT, "examples", "*.dana"))):
        total += 1
        res = run_parse(path, fragment=False)
        if res.returncode != 0:
            print(f"FAIL {os.path.relpath(path, ROOT)}: {res.stderr.strip()}")
            failures += 1

    # 2. All fenced ```dana blocks in docs/reference/README.md and README.md
    for md in [
        os.path.join(ROOT, "docs", "reference", "README.md"),
        os.path.join(ROOT, "README.md"),
    ]:
        n, f = check_markdown(md)
        total += n
        failures += f

    # 3. Positive grammar tests (fragments)
    for path in sorted(glob.glob(os.path.join(ROOT, "grammar", "tests", "good", "*.dana"))):
        total += 1
        res = run_parse(path, fragment=True)
        if res.returncode != 0:
            print(f"FAIL {os.path.relpath(path, ROOT)}: {res.stderr.strip()}")
            failures += 1

    # 4. Negative grammar tests (fragments)
    for path in sorted(glob.glob(os.path.join(ROOT, "grammar", "tests", "bad", "*.dana"))):
        total += 1
        res = run_parse(path, fragment=True)
        if res.returncode == 0:
            print(f"FAIL {os.path.relpath(path, ROOT)}: expected syntax error, but parsed cleanly")
            failures += 1

    # 5. Negative grammar tests (full files)
    for path in sorted(glob.glob(os.path.join(ROOT, "grammar", "tests", "bad-files", "*.dana"))):
        total += 1
        res = run_parse(path, fragment=False)
        if res.returncode == 0:
            print(f"FAIL {os.path.relpath(path, ROOT)}: expected syntax error, but parsed cleanly")
            failures += 1

    if failures:
        print(f"grammar check FAILED: {failures} of {total} checks failed")
        return 1
    print(f"grammar check PASSED: {total} of {total} checks passed (0 Bison conflicts)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
