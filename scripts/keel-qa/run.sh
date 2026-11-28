#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"

if [ -d "$HOME/.local/share/mise/shims" ] && [[ ":$PATH:" != *":$HOME/.local/share/mise/shims:"* ]]; then
  export PATH="$HOME/.local/share/mise/shims:$PATH"
fi

for tool in sqlite3 python3 runkeel statkeel sheetkeel maskkeel datakeel driftkeel litekeel; do
  if ! command -v "$tool" >/dev/null 2>&1; then
    echo "error: required tool '$tool' not found on PATH." >&2
    echo "Install keel-stack CLIs from https://github.com/robertguss/keel-stack and retry." >&2
    exit 127
  fi
done

DANA_BIN="${DANA_BIN:-$REPO_ROOT/target/release/dana}"
if [ ! -x "$DANA_BIN" ]; then
  echo "Building release dana binary..." >&2
  cargo build --release --manifest-path "$REPO_ROOT/Cargo.toml"
fi

TMP_WORK="$(mktemp -d "${TMPDIR:-/tmp}/dana_keel_qa.XXXXXX")"
trap 'rm -rf "$TMP_WORK"' EXIT

cp "$SCRIPT_DIR/dana.policy" \
   "$SCRIPT_DIR/qa_pipeline.dana" \
   "$SCRIPT_DIR/qa_contract.odcs.yaml" \
   "$SCRIPT_DIR/qa_pipeline.toml" \
   "$TMP_WORK/"

mkdir -p "$TMP_WORK/qa-in" "$TMP_WORK/qa-out"

python3 - "$TMP_WORK/qa-in/readings.csv" <<'PY'
import sys

out_path = sys.argv[1]
lines = [
    "id,record_code,email,age_years,region,score_f,elevation_m,amount,active?,reading_date,note"
]
regions = (
    [("north", 12), ("south", 10), ("east", 8)]
)
idx = 1
for reg, count in regions:
    for j in range(count):
        age = 22 + (idx % 12)
        score = 60.0 + float((idx * 7) % 35)
        elev = [0.0, 100.0, 396.0, 125.5, 250.0, 42.25][idx % 6]
        if idx == 15:
            elev = 2400.0  # clear IQR outlier
        amt = f"{10 + idx}.{(idx * 5) % 100:02d}"
        active = "true" if (idx % 3 != 0) else "false"
        day = 1 + (idx % 28)
        if idx == 1:
            note = "=SUM(1,2)"  # verify formula sanitization in CSV export
        elif idx % 4 == 0:
            note = ""
        else:
            note = f"  obs-{idx}  "
        lines.append(
            f"{idx},REC-{idx:03d},user{idx}@example.edu,{age},{reg},{score},{elev},{amt},{active},2026-11-{day:02d},{note}"
        )
        idx += 1

# Duplicate ID to exercise dedupe_by(.id)
lines.append("1,REC-001-DUP,dup@example.edu,24,north,99.0,50.0,99.99,false,2026-11-01,dup")
# Two malformed rows to exercise CSV quarantine
lines.append("bad_id,REC-BAD1,bad1@example.edu,25,north,50.0,10.0,1.00,true,2026-11-02,bad")
lines.append("999,,bad2@example.edu,25,south,50.0,10.0,1.00,true,2026-11-02,empty_code")

with open(out_path, "w", encoding="utf-8") as f:
    f.write("\n".join(lines) + "\n")
PY

sqlite3 "$TMP_WORK/qa-out/qa.sqlite" <<'SQL'
CREATE TABLE "qa_metrics" (
  "id" INTEGER PRIMARY KEY NOT NULL,
  "record_code" TEXT NOT NULL,
  "contact_hash" TEXT NOT NULL,
  "region" TEXT NOT NULL,
  "region_bucket" TEXT NOT NULL,
  "score_f" REAL NOT NULL,
  "elevation_m" REAL NOT NULL,
  "note_len" INTEGER NOT NULL,
  "reading_date" DATE NOT NULL
);
SQL

export DANA_BIN
export DANA_SECRET_QA_SALT="keel-qa-deterministic-salt"

echo "== Running Dana + keel-stack black-box QA DAG in $TMP_WORK =="
(
  cd "$TMP_WORK"
  runkeel run --format agent --no-save qa_pipeline.toml
)
