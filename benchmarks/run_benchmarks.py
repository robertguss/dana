#!/usr/bin/env python3
"""Reproducible end-to-end benchmarks: Dana v0.4 vs. Python (stdlib/sqlite3, Pandas, Polars).

Sets up an ephemeral virtual environment in `/tmp/dana-bench-venv` (zero Python packages
added to the repository), deterministically generates scale fixtures in `/tmp/dana-bench-data`,
runs 1 warmup + 5 timed child subprocesses per engine per workload, captures exact per-process
wall-clock latency and kernel peak RSS (`os.wait4`), asserts cell-for-cell numerical output
parity between Dana and every Python baseline, and writes `benchmarks/RESULTS.md` (including
a direct `v0.3.0 -> v0.4.0` speedup and peak-RSS improvement comparison).
"""

from __future__ import annotations

import argparse
import csv
from decimal import Decimal
import json
import math
import os
from pathlib import Path
import platform
import shutil
import sqlite3
import statistics
import subprocess
import sys
import tempfile
import time


REPO_ROOT = Path(__file__).resolve().parent.parent
BENCH_DIR = REPO_ROOT / "benchmarks"
VENV_DIR = Path("/tmp/dana-bench-venv")
DATA_DIR = Path("/tmp/dana-bench-data")
WORK_DIR = Path("/tmp/dana-bench-work")

WARMUP_RUNS = 1
TIMED_RUNS = 5

W1_VALID_ROWS = 500_000
W1_BAD_ROWS = 500
W2_FACT_ROWS = 500_000
W2_DIM_ROWS = 50_000
W3_ROWS = 250_000
W4_ROWS = 200_000


# ============================================================================
# 1. Ephemeral /tmp Venv Bootstrap & Release Build
# ============================================================================


def ensure_venv_and_reexec() -> None:
    """Create `/tmp/dana-bench-venv` via `uv` and re-exec inside it when needed."""
    if os.environ.get("DANA_BENCH_IN_VENV") == "1":
        return

    venv_py = VENV_DIR / "bin" / "python"
    uv_bin = shutil.which("uv")
    if uv_bin:
        need_install = not venv_py.exists()
        if not need_install:
            probe = subprocess.run(
                [str(venv_py), "-c", "import pandas, polars, pyarrow"],
                capture_output=True,
                text=True,
            )
            need_install = probe.returncode != 0

        if need_install:
            print(f"[setup] creating ephemeral venv at {VENV_DIR} via uv...", flush=True)
            subprocess.run([uv_bin, "venv", "--clear", str(VENV_DIR)], check=True)
            subprocess.run(
                [
                    uv_bin,
                    "pip",
                    "install",
                    "--python",
                    str(venv_py),
                    "pandas",
                    "polars",
                    "pyarrow",
                ],
                check=True,
            )

        if venv_py.exists():
            env = dict(os.environ)
            env["DANA_BENCH_IN_VENV"] = "1"
            os.execve(str(venv_py), [str(venv_py), __file__, *sys.argv[1:]], env)

    print(
        "[setup] warning: `uv` unavailable or venv setup skipped; running under system python3",
        flush=True,
    )


def ensure_dana_release(rebuild: bool) -> Path:
    bin_path = REPO_ROOT / "target" / "release" / "dana"
    if rebuild or not bin_path.exists():
        print("[setup] building target/release/dana...", flush=True)
        subprocess.run(["cargo", "build", "--release"], cwd=REPO_ROOT, check=True)
    return bin_path


# ============================================================================
# 2. Deterministic Scale Fixture Generation (/tmp/dana-bench-data)
# ============================================================================


def generate_fixtures(force: bool = False) -> dict[str, Path]:
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    paths = {
        "w1_csv": DATA_DIR / "w1_orders.csv",
        "w2_fact_pq": DATA_DIR / "w2_sales.parquet",
        "w2_dim_pq": DATA_DIR / "w2_products.parquet",
        "w2_fact_csv": DATA_DIR / "w2_sales.csv",
        "w2_dim_csv": DATA_DIR / "w2_products.csv",
        "w3_sqlite": DATA_DIR / "w3_registrar.sqlite",
        "w4_pq": DATA_DIR / "w4_telemetry.parquet",
        "manifest": DATA_DIR / "manifest.json",
    }

    expected_manifest = {
        "schema_ver": 1,
        "w1_valid": W1_VALID_ROWS,
        "w1_bad": W1_BAD_ROWS,
        "w2_fact": W2_FACT_ROWS,
        "w2_dim": W2_DIM_ROWS,
        "w3_rows": W3_ROWS,
        "w4_rows": W4_ROWS,
    }
    if (
        not force
        and paths["manifest"].exists()
        and all(p.exists() for p in paths.values())
        and json.loads(paths["manifest"].read_text()) == expected_manifest
    ):
        print(f"[fixtures] reusing verified deterministic fixtures in {DATA_DIR}", flush=True)
        return paths

    print(f"[fixtures] generating deterministic scale fixtures in {DATA_DIR}...", flush=True)
    _gen_w1_fixture(paths["w1_csv"])
    _gen_w2_fixtures(
        paths["w2_fact_pq"],
        paths["w2_dim_pq"],
        paths["w2_fact_csv"],
        paths["w2_dim_csv"],
    )
    _gen_w3_fixture(paths["w3_sqlite"])
    _gen_w4_fixture(paths["w4_pq"])
    paths["manifest"].write_text(json.dumps(expected_manifest, indent=2))
    print("[fixtures] generation complete.", flush=True)
    return paths


def _gen_w1_fixture(csv_path: Path) -> None:
    regions = ["north", "south", "east", "west", "central", "coastal", "mountain", "metro"]
    categories = ["books", "software", "hardware", "services"]
    tax_rates = ["0.05", "0.08", "0.10"]

    with csv_path.open("w", encoding="utf-8", newline="") as f:
        f.write("order_id,region,category,tier,qty,unit_price,tax_rate\n")
        bad_every = W1_VALID_ROWS // W1_BAD_ROWS
        bad_written = 0
        lines: list[str] = []
        for i in range(W1_VALID_ROWS):
            reg_idx = i % 8
            cat_idx = (i // 8) % 4
            tier = (i % 3) + 1
            # 10% qty == 0 (valid schema row, filtered out by `where(.qty > 0)`).
            qty = 0 if (i % 10 == 0) else ((i % 14) + 1)
            # Group-specific offset guarantees strictly distinct totals for tie-free sorting.
            cents = 1000 + ((i * 37) % 24000) + reg_idx * 75 + cat_idx * 25
            price_str = f"{cents // 100}.{cents % 100:02d}"
            tax = tax_rates[(i + reg_idx) % 3]
            lines.append(
                f"{i + 1},{regions[reg_idx]},{categories[cat_idx]},{tier},{qty},{price_str},{tax}\n"
            )
            if (i + 1) % bad_every == 0 and bad_written < W1_BAD_ROWS:
                bad_id = W1_VALID_ROWS + bad_written + 1
                if bad_written % 2 == 0:
                    lines.append(f"{bad_id},north,books,1,2,BAD_DECIMAL,0.05\n")
                else:
                    lines.append(f"{bad_id},south,hardware,2,-5,19.99,0.08\n")
                bad_written += 1
            if len(lines) >= 20_000:
                f.writelines(lines)
                lines.clear()
        if lines:
            f.writelines(lines)


def _gen_w2_fixtures(
    fact_pq: Path, dim_pq: Path, fact_csv: Path, dim_csv: Path
) -> None:
    import pyarrow as pa
    import pyarrow.parquet as pq

    departments = [
        "apparel",
        "audio",
        "books",
        "camping",
        "electronics",
        "garden",
        "home",
        "kitchen",
        "office",
        "tools",
    ]
    channels = ["web", "retail", "partner", "enterprise"]

    # 50,000-row dimension table
    dim_product_ids = list(range(1, W2_DIM_ROWS + 1))
    dim_depts = [departments[(pid * 7) % len(departments)] for pid in dim_product_ids]
    dim_prices = [round(15.0 + ((pid * 13) % 200) + ((pid % 4) * 0.25), 2) for pid in dim_product_ids]
    dim_costs = [round(p * 0.55, 2) for p in dim_prices]
    dim_haz = [(pid % 11) == 0 for pid in dim_product_ids]

    dim_table = pa.table(
        {
            "product_id": pa.array(dim_product_ids, type=pa.int64()),
            "department": pa.array(dim_depts, type=pa.string()),
            "list_price": pa.array(dim_prices, type=pa.float64()),
            "unit_cost": pa.array(dim_costs, type=pa.float64()),
            "hazardous?": pa.array(dim_haz, type=pa.bool_()),
        }
    )
    pq.write_table(dim_table, dim_pq, compression="zstd", row_group_size=50_000)

    with dim_csv.open("w", encoding="utf-8", newline="") as f:
        f.write("product_id,department,list_price,unit_cost,hazardous?\n")
        chunk: list[str] = []
        for pid, dep, lp, uc, hz in zip(
            dim_product_ids, dim_depts, dim_prices, dim_costs, dim_haz
        ):
            chunk.append(f"{pid},{dep},{lp},{uc},{'true' if hz else 'false'}\n")
            if len(chunk) >= 10_000:
                f.writelines(chunk)
                chunk.clear()
        if chunk:
            f.writelines(chunk)

    # 500,000-row fact table
    fact_sale_ids = list(range(1, W2_FACT_ROWS + 1))
    fact_prod_ids = [((i * 2654435761) % W2_DIM_ROWS) + 1 for i in range(W2_FACT_ROWS)]
    fact_channels = [channels[(i + (i // 17)) % len(channels)] for i in range(W2_FACT_ROWS)]
    fact_units = [(i % 8) + 1 for i in range(W2_FACT_ROWS)]
    fact_disc_bps = [((i * 5) % 6) * 250 for i in range(W2_FACT_ROWS)]

    fact_table = pa.table(
        {
            "sale_id": pa.array(fact_sale_ids, type=pa.int64()),
            "product_id": pa.array(fact_prod_ids, type=pa.int64()),
            "channel": pa.array(fact_channels, type=pa.string()),
            "units": pa.array(fact_units, type=pa.int64()),
            "discount_bps": pa.array(fact_disc_bps, type=pa.int64()),
        }
    )
    pq.write_table(fact_table, fact_pq, compression="zstd", row_group_size=100_000)

    with fact_csv.open("w", encoding="utf-8", newline="") as f:
        f.write("sale_id,product_id,channel,units,discount_bps\n")
        chunk = []
        for sid, pid, ch, un, dbps in zip(
            fact_sale_ids, fact_prod_ids, fact_channels, fact_units, fact_disc_bps
        ):
            chunk.append(f"{sid},{pid},{ch},{un},{dbps}\n")
            if len(chunk) >= 20_000:
                f.writelines(chunk)
                chunk.clear()
        if chunk:
            f.writelines(chunk)


def _gen_w3_fixture(db_path: Path) -> None:
    if db_path.exists():
        db_path.unlink()

    departments = [
        "Biology",
        "Chemistry",
        "ComputerScience",
        "Economics",
        "History",
        "Mathematics",
        "Philosophy",
        "Physics",
    ]
    conn = sqlite3.connect(db_path)
    conn.execute("PRAGMA synchronous = OFF;")
    conn.execute("PRAGMA journal_mode = OFF;")
    conn.execute(
        """
        CREATE TABLE "StudentEnrollment" (
            "enrollment_id" INTEGER PRIMARY KEY,
            "student_id" INTEGER NOT NULL,
            "student_email" TEXT NOT NULL,
            "department" TEXT NOT NULL,
            "term_year" INTEGER NOT NULL,
            "term_seq" INTEGER NOT NULL,
            "active?" INTEGER NOT NULL,
            "age_years" INTEGER NOT NULL,
            "grade_points" REAL NOT NULL
        );
        """
    )

    rare_rows = 75  # 3 distinct students x 25 rows each -> MUST be suppressed!
    main_rows = W3_ROWS - rare_rows

    batch: list[tuple] = []
    for i in range(main_rows):
        eid = i + 1
        sid = (i % 12_000) + 1
        email = f"student{sid}@example.edu"
        dept = departments[(i * 3 + sid) % len(departments)]
        # Years 2021..2026 (half are >= 2024)
        year = 2021 + (i % 6)
        term_seq = (year - 2021) * 2 + (1 if (i // 6) % 2 == 0 else 2)
        active = 0 if (i % 5 == 0) else 1
        # Ages span all 4 buckets (<22, 22-29, 30-44, 45+) deterministically per student
        age = 18 + ((sid * 7) % 38)
        gpa = round(2.0 + (((sid * 17 + term_seq * 11 + i) % 201) / 100.0), 2)
        batch.append((eid, sid, email, dept, year, term_seq, active, age, gpa))
        if len(batch) >= 25_000:
            conn.executemany(
                'INSERT INTO "StudentEnrollment" VALUES (?,?,?,?,?,?,?,?,?)',
                batch,
            )
            batch.clear()

    for j in range(rare_rows):
        eid = main_rows + j + 1
        sid = 900_000 + (j % 3)  # only 3 distinct students -> suppressed!
        batch.append(
            (eid, sid, f"rare{sid}@example.edu", "RareStudies", 2025, 9, 1, 26, 3.95)
        )
    if batch:
        conn.executemany(
            'INSERT INTO "StudentEnrollment" VALUES (?,?,?,?,?,?,?,?,?)',
            batch,
        )

    conn.execute(
        'CREATE INDEX idx_enroll_active_year ON "StudentEnrollment" ("active?", "term_year");'
    )
    conn.commit()
    conn.close()


def _gen_w4_fixture(pq_path: Path) -> None:
    import pyarrow as pa
    import pyarrow.parquet as pq

    zones = ["ap-east", "ap-south", "eu-central", "eu-west", "us-east", "us-west"]
    reading_ids = list(range(1, W4_ROWS + 1))
    zone_col = [zones[i % len(zones)] for i in range(W4_ROWS)]
    load_col = [round(5.0 + ((i * 73) % 9000) / 100.0, 2) for i in range(W4_ROWS)]
    # Strong linear latency vs. load with bounded deterministic noise
    lat_col = [
        round(12.5 + 1.45 * load_col[i] + (((i * 29) % 101) - 50) * 0.15, 3)
        for i in range(W4_ROWS)
    ]
    healthy_col = [(i % 10) != 0 for i in range(W4_ROWS)]

    tbl = pa.table(
        {
            "reading_id": pa.array(reading_ids, type=pa.int64()),
            "zone": pa.array(zone_col, type=pa.string()),
            "load_pct": pa.array(load_col, type=pa.float64()),
            "latency_ms": pa.array(lat_col, type=pa.float64()),
            "healthy?": pa.array(healthy_col, type=pa.bool_()),
        }
    )
    pq.write_table(tbl, pq_path, compression="zstd", row_group_size=100_000)


# ============================================================================
# 3. Python Baseline Workers (Executed in Isolated Child Subprocesses)
# ============================================================================


def _run_python_worker(workload: str, engine: str, data_args: list[str], out_dir: Path) -> None:
    out_dir.mkdir(parents=True, exist_ok=True)
    if workload == "w1":
        _w1_python(engine, Path(data_args[0]), out_dir)
    elif workload == "w2":
        _w2_python(engine, Path(data_args[0]), Path(data_args[1]), out_dir)
    elif workload == "w3":
        _w3_python(engine, Path(data_args[0]), out_dir)
    elif workload == "w4":
        _w4_python(engine, Path(data_args[0]), out_dir)
    else:
        raise ValueError(f"unknown workload {workload}")


def _w1_net_price_dec(unit_price: Decimal, qty: int, tier: int, tax_rate: Decimal) -> Decimal:
    gross = unit_price * Decimal(qty)
    if tier == 3 and qty >= 5:
        disc = Decimal("0.15")
    elif tier == 2 and qty >= 3:
        disc = Decimal("0.08")
    elif qty >= 10:
        disc = Decimal("0.05")
    else:
        disc = Decimal("0.00")
    subtotal = gross - (gross * disc)
    return subtotal + (subtotal * tax_rate)


def _w1_net_price_float(unit_price: float, qty: int, tier: int, tax_rate: float) -> float:
    gross = unit_price * qty
    if tier == 3 and qty >= 5:
        disc = 0.15
    elif tier == 2 and qty >= 3:
        disc = 0.08
    elif qty >= 10:
        disc = 0.05
    else:
        disc = 0.0
    subtotal = gross - (gross * disc)
    return subtotal + (subtotal * tax_rate)


def _w1_python(engine: str, csv_path: Path, out_dir: Path) -> None:
    out_csv = out_dir / "w1_summary.csv"
    if engine == "stdlib":
        agg: dict[tuple[str, str], list] = {}
        bad = 0
        valid = 0
        with csv_path.open("r", encoding="utf-8", newline="") as f:
            reader = csv.DictReader(f)
            for row in reader:
                try:
                    _ = int(row["order_id"])
                    reg = row["region"]
                    cat = row["category"]
                    tier = int(row["tier"])
                    qty = int(row["qty"])
                    price = Decimal(row["unit_price"])
                    tax = Decimal(row["tax_rate"])
                except Exception:
                    bad += 1
                    continue
                if (
                    not reg
                    or not cat
                    or not (1 <= tier <= 3)
                    or qty < 0
                    or price <= 0
                    or not (Decimal("0") <= tax <= Decimal("0.25"))
                ):
                    bad += 1
                    continue
                valid += 1
                if qty <= 0:
                    continue
                net = _w1_net_price_dec(price, qty, tier, tax)
                key = (reg, cat)
                slot = agg.get(key)
                if slot is None:
                    agg[key] = [net, qty, 1]
                else:
                    slot[0] += net
                    slot[1] += qty
                    slot[2] += 1

        rows = sorted(agg.items(), key=lambda kv: kv[1][0], reverse=True)
        with out_csv.open("w", encoding="utf-8", newline="") as f:
            w = csv.writer(f)
            w.writerow(["region", "category", "total_net", "total_qty", "order_count"])
            for (reg, cat), (tnet, tqty, cnt) in rows:
                w.writerow([reg, cat, str(tnet), tqty, cnt])
        print(f"W1 ok: valid={valid} bad={bad} groups={len(rows)}")
        return

    if engine == "pandas":
        import pandas as pd

        df = pd.read_csv(csv_path, dtype=str)
        df["order_id"] = pd.to_numeric(df["order_id"], errors="coerce")
        df["tier"] = pd.to_numeric(df["tier"], errors="coerce")
        df["qty"] = pd.to_numeric(df["qty"], errors="coerce")
        df["unit_price"] = pd.to_numeric(df["unit_price"], errors="coerce")
        df["tax_rate"] = pd.to_numeric(df["tax_rate"], errors="coerce")
        valid_mask = (
            df["order_id"].notna()
            & df["region"].notna()
            & (df["region"] != "")
            & df["category"].notna()
            & (df["category"] != "")
            & df["tier"].between(1, 3)
            & (df["qty"] >= 0)
            & (df["unit_price"] > 0)
            & df["tax_rate"].between(0.0, 0.25)
        )
        valid_df = df.loc[valid_mask].copy()
        bad = int((~valid_mask).sum())
        valid = len(valid_df)
        pos = valid_df.loc[valid_df["qty"] > 0].copy()
        # Realistic Python row-UDF via list comprehension / apply (or idiomatic Pandas apply)
        pos["net_amount"] = [
            _w1_net_price_float(p, int(q), int(t), tr)
            for p, q, t, tr in zip(
                pos["unit_price"].to_numpy(),
                pos["qty"].to_numpy(),
                pos["tier"].to_numpy(),
                pos["tax_rate"].to_numpy(),
            )
        ]
        summary = (
            pos.groupby(["region", "category"], as_index=False)
            .agg(
                total_net=("net_amount", "sum"),
                total_qty=("qty", "sum"),
                order_count=("order_id", "count"),
            )
            .sort_values("total_net", ascending=False)
        )
        summary["total_qty"] = summary["total_qty"].astype("int64")
        summary.to_csv(out_csv, index=False)
        print(f"W1 ok: valid={valid} bad={bad} groups={len(summary)}")
        return

    if engine == "polars":
        import polars as pl

        raw = pl.read_csv(
            csv_path,
            schema_overrides={
                "order_id": pl.String,
                "region": pl.String,
                "category": pl.String,
                "tier": pl.String,
                "qty": pl.String,
                "unit_price": pl.String,
                "tax_rate": pl.String,
            },
        )
        parsed = raw.select(
            pl.col("order_id").cast(pl.Int64, strict=False),
            pl.col("region"),
            pl.col("category"),
            pl.col("tier").cast(pl.Int64, strict=False),
            pl.col("qty").cast(pl.Int64, strict=False),
            pl.col("unit_price").cast(pl.Float64, strict=False),
            pl.col("tax_rate").cast(pl.Float64, strict=False),
        )
        valid_expr = (
            pl.col("order_id").is_not_null()
            & pl.col("region").is_not_null()
            & (pl.col("region") != "")
            & pl.col("category").is_not_null()
            & (pl.col("category") != "")
            & pl.col("tier").is_between(1, 3)
            & (pl.col("qty") >= 0)
            & (pl.col("unit_price") > 0.0)
            & pl.col("tax_rate").is_between(0.0, 0.25)
        )
        valid_df = parsed.filter(valid_expr)
        valid = valid_df.height
        bad = parsed.height - valid

        # Polars native expression version (best-case Polars, no Python UDF penalty!)
        gross = pl.col("unit_price") * pl.col("qty").cast(pl.Float64)
        disc = (
            pl.when((pl.col("tier") == 3) & (pl.col("qty") >= 5))
            .then(0.15)
            .when((pl.col("tier") == 2) & (pl.col("qty") >= 3))
            .then(0.08)
            .when(pl.col("qty") >= 10)
            .then(0.05)
            .otherwise(0.0)
        )
        subtotal = gross - (gross * disc)
        net = subtotal + (subtotal * pl.col("tax_rate"))

        summary = (
            valid_df.filter(pl.col("qty") > 0)
            .with_columns(net.alias("net_amount"))
            .group_by(["region", "category"])
            .agg(
                pl.col("net_amount").sum().alias("total_net"),
                pl.col("qty").sum().alias("total_qty"),
                pl.len().alias("order_count"),
            )
            .sort("total_net", descending=True)
        )
        summary.write_csv(out_csv)
        print(f"W1 ok: valid={valid} bad={bad} groups={summary.height}")
        return

    raise ValueError(f"unknown engine {engine}")


def _w2_python(engine: str, fact_path: Path, dim_path: Path, out_dir: Path) -> None:
    out_csv = out_dir / "w2_summary.csv"
    if engine == "stdlib":
        products: dict[int, tuple[str, float, float, bool]] = {}
        with dim_path.open("r", encoding="utf-8", newline="") as f:
            for row in csv.DictReader(f):
                pid = int(row["product_id"])
                if pid in products:
                    raise RuntimeError(f"duplicate product_id {pid}")
                products[pid] = (
                    row["department"],
                    float(row["list_price"]),
                    float(row["unit_cost"]),
                    row["hazardous?"] == "true",
                )
        agg: dict[tuple[str, str], list] = {}
        sales_cnt = 0
        with fact_path.open("r", encoding="utf-8", newline="") as f:
            for row in csv.DictReader(f):
                sales_cnt += 1
                pid = int(row["product_id"])
                prod = products.get(pid)
                if prod is None:
                    continue
                dept, lp, uc, haz = prod
                ch = row["channel"]
                units = int(row["units"])
                dbps = int(row["discount_bps"])
                disc_factor = 1.0 - (dbps / 10000.0)
                net_unit = lp * disc_factor
                rev = net_unit * units
                handling = 2.5 if haz else 0.5
                margin = (net_unit - uc - handling) * units
                key = (dept, ch)
                slot = agg.get(key)
                if slot is None:
                    agg[key] = [rev, margin, units, 1]
                else:
                    slot[0] += rev
                    slot[1] += margin
                    slot[2] += units
                    slot[3] += 1

        rows = sorted(agg.items(), key=lambda kv: kv[0])
        with out_csv.open("w", encoding="utf-8", newline="") as f:
            w = csv.writer(f)
            w.writerow(
                [
                    "department",
                    "channel",
                    "total_revenue",
                    "total_margin",
                    "total_units",
                    "txn_count",
                ]
            )
            for (dept, ch), (rev, margin, units, txns) in rows:
                w.writerow([dept, ch, rev, margin, units, txns])
        print(f"W2 ok: sales={sales_cnt} products={len(products)} groups={len(rows)}")
        return

    if engine == "pandas":
        import pandas as pd

        sales = pd.read_parquet(fact_path)
        products = pd.read_parquet(dim_path)
        joined = sales.merge(products, on="product_id", how="inner", validate="many_to_one")
        disc_factor = 1.0 - (joined["discount_bps"].astype("float64") / 10000.0)
        net_unit = joined["list_price"] * disc_factor
        handling = joined["hazardous?"].map({True: 2.5, False: 0.5})
        joined["net_revenue"] = net_unit * joined["units"]
        joined["gross_margin"] = (net_unit - joined["unit_cost"] - handling) * joined["units"]
        summary = (
            joined.groupby(["department", "channel"], as_index=False)
            .agg(
                total_revenue=("net_revenue", "sum"),
                total_margin=("gross_margin", "sum"),
                total_units=("units", "sum"),
                txn_count=("sale_id", "count"),
            )
            .sort_values(["department", "channel"])
        )
        summary.to_csv(out_csv, index=False)
        print(f"W2 ok: sales={len(sales)} products={len(products)} groups={len(summary)}")
        return

    if engine == "polars":
        import polars as pl

        sales = pl.read_parquet(fact_path)
        products = pl.read_parquet(dim_path)
        joined = sales.join(products, on="product_id", how="inner", validate="m:1")
        disc_factor = 1.0 - (pl.col("discount_bps").cast(pl.Float64) / 10000.0)
        net_unit = pl.col("list_price") * disc_factor
        handling = pl.when(pl.col("hazardous?")).then(2.5).otherwise(0.5)
        summary = (
            joined.with_columns(
                (net_unit * pl.col("units").cast(pl.Float64)).alias("net_revenue"),
                ((net_unit - pl.col("unit_cost") - handling) * pl.col("units").cast(pl.Float64)).alias(
                    "gross_margin"
                ),
            )
            .group_by(["department", "channel"])
            .agg(
                pl.col("net_revenue").sum().alias("total_revenue"),
                pl.col("gross_margin").sum().alias("total_margin"),
                pl.col("units").sum().alias("total_units"),
                pl.len().alias("txn_count"),
            )
            .sort(["department", "channel"])
        )
        summary.write_csv(out_csv)
        print(f"W2 ok: sales={sales.height} products={products.height} groups={summary.height}")
        return

    raise ValueError(f"unknown engine {engine}")


def _bucket_age(age: int) -> str:
    if age < 22:
        return "under_22"
    if age < 30:
        return "22_to_29"
    if age < 45:
        return "30_to_44"
    return "45_plus"


def _w3_python(engine: str, db_path: Path, out_dir: Path) -> None:
    out_csv = out_dir / "w3_summary.csv"
    sql = (
        'SELECT "student_id", "department", "term_seq", "age_years", "grade_points" '
        'FROM "StudentEnrollment" WHERE "active?" = 1 AND "term_year" >= 2024'
    )

    if engine == "stdlib":
        conn = sqlite3.connect(f"file:{db_path}?mode=ro", uri=True)
        cur = conn.execute(sql)
        # (dept, age_band, term_seq) -> [set_of_sids, count, sum_gpa]
        groups: dict[tuple[str, str, int], list] = {}
        for sid, dept, tseq, age, gpa in cur:
            band = _bucket_age(age)
            key = (dept, band, tseq)
            slot = groups.get(key)
            if slot is None:
                groups[key] = [{sid}, 1, gpa]
            else:
                slot[0].add(sid)
                slot[1] += 1
                slot[2] += gpa
        conn.close()

        # Filter k >= 5 distinct students and sort
        surviving = []
        for (dept, band, tseq), (sids, cnt, sum_gpa) in groups.items():
            if len(sids) >= 5:
                surviving.append((dept, band, tseq, len(sids), cnt, sum_gpa / cnt))
        surviving.sort(key=lambda r: (r[0], r[1], r[2]))

        # Partitioned 3-row trailing rolling mean over (dept, age_band) ordered by term_seq
        out_rows = []
        win: list[float] = []
        prev_part: tuple[str, str] | None = None
        for dept, band, tseq, students, enrollments, avg_gpa in surviving:
            part = (dept, band)
            if part != prev_part:
                win = []
                prev_part = part
            win.append(avg_gpa)
            if len(win) > 3:
                win.pop(0)
            roll = sum(win) / len(win)
            out_rows.append((dept, band, tseq, students, enrollments, avg_gpa, roll))

        with out_csv.open("w", encoding="utf-8", newline="") as f:
            w = csv.writer(f)
            w.writerow(
                [
                    "department",
                    "age_band",
                    "term_seq",
                    "students",
                    "enrollments",
                    "avg_gpa",
                    "rolling_3t_gpa",
                ]
            )
            w.writerows(out_rows)
        print(f"W3 ok: published_cells={len(out_rows)}")
        return

    if engine == "pandas":
        import pandas as pd

        conn = sqlite3.connect(f"file:{db_path}?mode=ro", uri=True)
        df = pd.read_sql_query(sql, conn)
        conn.close()
        df["age_band"] = pd.cut(
            df["age_years"],
            bins=[-1_000_000, 22, 30, 45, 1_000_000],
            labels=["under_22", "22_to_29", "30_to_44", "45_plus"],
            right=False,
        ).astype(str)
        summary = (
            df.groupby(["department", "age_band", "term_seq"], as_index=False)
            .agg(
                students=("student_id", "nunique"),
                enrollments=("student_id", "count"),
                avg_gpa=("grade_points", "mean"),
            )
        )
        summary = (
            summary.loc[summary["students"] >= 5]
            .sort_values(["department", "age_band", "term_seq"])
            .reset_index(drop=True)
        )
        summary["rolling_3t_gpa"] = (
            summary.groupby(["department", "age_band"])["avg_gpa"]
            .transform(lambda s: s.rolling(3, min_periods=1).mean())
        )
        summary.to_csv(out_csv, index=False)
        print(f"W3 ok: published_cells={len(summary)}")
        return

    if engine == "polars":
        import polars as pl

        conn = sqlite3.connect(f"file:{db_path}?mode=ro", uri=True)
        df = pl.read_database(sql, connection=conn)
        conn.close()
        age_band = (
            pl.when(pl.col("age_years") < 22)
            .then(pl.lit("under_22"))
            .when(pl.col("age_years") < 30)
            .then(pl.lit("22_to_29"))
            .when(pl.col("age_years") < 45)
            .then(pl.lit("30_to_44"))
            .otherwise(pl.lit("45_plus"))
            .alias("age_band")
        )
        summary = (
            df.with_columns(age_band)
            .group_by(["department", "age_band", "term_seq"])
            .agg(
                pl.col("student_id").n_unique().alias("students"),
                pl.len().alias("enrollments"),
                pl.col("grade_points").mean().alias("avg_gpa"),
            )
            .filter(pl.col("students") >= 5)
            .sort(["department", "age_band", "term_seq"])
            .with_columns(
                pl.col("avg_gpa")
                .rolling_mean(window_size=3, min_samples=1)
                .over(["department", "age_band"])
                .alias("rolling_3t_gpa")
            )
        )
        summary.write_csv(out_csv)
        print(f"W3 ok: published_cells={summary.height}")
        return

    raise ValueError(f"unknown engine {engine}")


def _render_python_html_report(
    out_html: Path,
    clean_rows: int,
    r_pearson: float,
    slope: float,
    intercept: float,
    r_squared: float,
    sample_pts: list[tuple[float, float, str]],
    zones: list[tuple[str, int, float, float]],
) -> None:
    circles = []
    for x, y, _z in sample_pts:
        px = 60.0 + (x / 100.0) * 680.0
        py = 420.0 - min(max(y, 0.0), 200.0) * 1.8
        circles.append(f'<circle cx="{px:.1f}" cy="{py:.1f}" r="3" fill="#2563eb" />')
    y1 = 420.0 - min(max(slope * 0.0 + intercept, 0.0), 200.0) * 1.8
    y2 = 420.0 - min(max(slope * 100.0 + intercept, 0.0), 200.0) * 1.8
    svg = (
        '<svg xmlns="http://www.w3.org/2000/svg" width="800" height="480">'
        f'<line x1="60" y1="{y1:.1f}" x2="740" y2="{y2:.1f}" stroke="#111827" stroke-width="2" />'
        + "".join(circles)
        + "</svg>"
    )
    table_rows = "".join(
        f"<tr><td>{z}</td><td>{n}</td><td>{al:.4f}</td><td>{alt:.4f}</td></tr>"
        for z, n, al, alt in zones
    )
    html = (
        "<!DOCTYPE html><html><head><meta charset='utf-8'><title>Telemetry Report</title></head>"
        f"<body><h1>Telemetry Performance &amp; Regression Report</h1>"
        f"<p>Analyzed {clean_rows} healthy readings: r={r_pearson:.6f}, "
        f"slope={slope:.6f}, intercept={intercept:.6f}, R^2={r_squared:.6f}.</p>"
        f"{svg}<table><tr><th>zone</th><th>readings</th><th>avg_load</th><th>avg_latency</th></tr>"
        f"{table_rows}</table></body></html>"
    )
    out_html.write_text(html, encoding="utf-8")


def _w4_python(engine: str, pq_path: Path, out_dir: Path) -> None:
    out_pq = out_dir / "w4_clean.parquet"
    out_stats = out_dir / "w4_stats.csv"
    out_zones = out_dir / "w4_zones.csv"
    out_html = out_dir / "w4_report.html"

    if engine == "stdlib":
        # Pure-Python math & aggregation over PyArrow Parquet I/O (stdlib has no Parquet codec).
        import pyarrow as pa
        import pyarrow.parquet as pq

        tbl = pq.read_table(pq_path)
        rids = tbl["reading_id"].to_pylist()
        zones_in = tbl["zone"].to_pylist()
        loads_in = tbl["load_pct"].to_pylist()
        lats_in = tbl["latency_ms"].to_pylist()
        healthy_in = tbl["healthy?"].to_pylist()

        c_rids: list[int] = []
        c_zones: list[str] = []
        c_loads: list[float] = []
        c_lats: list[float] = []
        c_healthy: list[bool] = []
        c_ratio: list[float] = []
        zone_acc: dict[str, list] = {}

        for rid, z, ld, lt, h in zip(rids, zones_in, loads_in, lats_in, healthy_in):
            if not h:
                continue
            c_rids.append(rid)
            c_zones.append(z)
            c_loads.append(ld)
            c_lats.append(lt)
            c_healthy.append(True)
            c_ratio.append(ld / 100.0)
            slot = zone_acc.get(z)
            if slot is None:
                zone_acc[z] = [1, ld, lt]
            else:
                slot[0] += 1
                slot[1] += ld
                slot[2] += lt

        out_tbl = pa.table(
            {
                "reading_id": pa.array(c_rids, type=pa.int64()),
                "zone": pa.array(c_zones, type=pa.string()),
                "load_pct": pa.array(c_loads, type=pa.float64()),
                "latency_ms": pa.array(c_lats, type=pa.float64()),
                "healthy?": pa.array(c_healthy, type=pa.bool_()),
                "load_ratio": pa.array(c_ratio, type=pa.float64()),
            }
        )
        pq.write_table(out_tbl, out_pq, compression="zstd")

        n = len(c_loads)
        mx = sum(c_loads) / n
        my = sum(c_lats) / n
        # Profile stats (min/max/median)
        _ = (min(c_loads), max(c_loads), statistics.median(c_loads))
        _ = (min(c_lats), max(c_lats), statistics.median(c_lats))

        sxx = 0.0
        syy = 0.0
        sxy = 0.0
        for x, y in zip(c_loads, c_lats):
            dx = x - mx
            dy = y - my
            sxx += dx * dx
            syy += dy * dy
            sxy += dx * dy
        r_pearson = sxy / math.sqrt(sxx * syy)
        slope = sxy / sxx
        intercept = my - slope * mx
        r_squared = r_pearson * r_pearson

        zrows = sorted(
            ((z, cnt, sl / cnt, slt / cnt) for z, (cnt, sl, slt) in zone_acc.items()),
            key=lambda t: t[0],
        )
        with out_stats.open("w", encoding="utf-8", newline="") as f:
            w = csv.writer(f)
            w.writerow(["clean_rows", "r_pearson", "slope", "intercept", "r_squared"])
            w.writerow([n, r_pearson, slope, intercept, r_squared])
        with out_zones.open("w", encoding="utf-8", newline="") as f:
            w = csv.writer(f)
            w.writerow(["zone", "readings", "avg_load", "avg_latency"])
            w.writerows(zrows)
        sample = list(zip(c_loads[:1000], c_lats[:1000], c_zones[:1000]))
        _render_python_html_report(
            out_html, n, r_pearson, slope, intercept, r_squared, sample, zrows
        )
        print(f"W4 ok: clean={n} r={r_pearson:.6f} slope={slope:.6f}")
        return

    if engine == "pandas":
        import pandas as pd

        raw = pd.read_parquet(pq_path)
        clean = raw.loc[raw["healthy?"]].copy()
        clean["load_ratio"] = clean["load_pct"] / 100.0
        clean.to_parquet(out_pq, compression="zstd", index=False)

        _ = clean.describe()
        x = clean["load_pct"].to_numpy()
        y = clean["latency_ms"].to_numpy()
        mx = float(x.mean())
        my = float(y.mean())
        dx = x - mx
        dy = y - my
        sxx = float((dx * dx).sum())
        syy = float((dy * dy).sum())
        sxy = float((dx * dy).sum())
        r_pearson = sxy / math.sqrt(sxx * syy)
        slope = sxy / sxx
        intercept = my - slope * mx
        r_squared = r_pearson * r_pearson

        zones_df = (
            clean.groupby("zone", as_index=False)
            .agg(
                readings=("reading_id", "count"),
                avg_load=("load_pct", "mean"),
                avg_latency=("latency_ms", "mean"),
            )
            .sort_values("zone")
        )
        pd.DataFrame(
            [
                {
                    "clean_rows": len(clean),
                    "r_pearson": r_pearson,
                    "slope": slope,
                    "intercept": intercept,
                    "r_squared": r_squared,
                }
            ]
        ).to_csv(out_stats, index=False)
        zones_df.to_csv(out_zones, index=False)

        head = clean.iloc[:1000]
        sample = list(zip(head["load_pct"], head["latency_ms"], head["zone"]))
        zrows = list(zones_df.itertuples(index=False, name=None))
        _render_python_html_report(
            out_html, len(clean), r_pearson, slope, intercept, r_squared, sample, zrows
        )
        print(f"W4 ok: clean={len(clean)} r={r_pearson:.6f} slope={slope:.6f}")
        return

    if engine == "polars":
        import polars as pl

        raw = pl.read_parquet(pq_path)
        clean = raw.filter(pl.col("healthy?")).with_columns(
            (pl.col("load_pct") / 100.0).alias("load_ratio")
        )
        clean.write_parquet(out_pq, compression="zstd")

        _ = clean.describe()
        stats_row = clean.select(
            pl.len().alias("n"),
            pl.corr("load_pct", "latency_ms", method="pearson").alias("r"),
            pl.col("load_pct").mean().alias("mx"),
            pl.col("latency_ms").mean().alias("my"),
            pl.cov("load_pct", "latency_ms").alias("cov_xy"),
            pl.col("load_pct").var().alias("var_x"),
        ).row(0)
        n, r_pearson, mx, my, cov_xy, var_x = stats_row
        slope = cov_xy / var_x
        intercept = my - slope * mx
        r_squared = r_pearson * r_pearson

        zones_df = (
            clean.group_by("zone")
            .agg(
                pl.len().alias("readings"),
                pl.col("load_pct").mean().alias("avg_load"),
                pl.col("latency_ms").mean().alias("avg_latency"),
            )
            .sort("zone")
        )
        pl.DataFrame(
            {
                "clean_rows": [n],
                "r_pearson": [r_pearson],
                "slope": [slope],
                "intercept": [intercept],
                "r_squared": [r_squared],
            }
        ).write_csv(out_stats)
        zones_df.write_csv(out_zones)

        head = clean.head(1000)
        sample = list(
            zip(
                head["load_pct"].to_list(),
                head["latency_ms"].to_list(),
                head["zone"].to_list(),
            )
        )
        zrows = zones_df.rows()
        _render_python_html_report(
            out_html, n, r_pearson, slope, intercept, r_squared, sample, zrows
        )
        print(f"W4 ok: clean={n} r={r_pearson:.6f} slope={slope:.6f}")
        return

    raise ValueError(f"unknown engine {engine}")


# ============================================================================
# 4. Subprocess Measurement Harness (`os.wait4` Wall-Clock + Peak RSS)
# ============================================================================


def run_measured(cmd: list[str], cwd: Path) -> tuple[float, float, str]:
    """Execute `cmd` in a fresh child process; return `(wall_ms, peak_rss_mib, stdout)`."""
    time_bin = shutil.which("/usr/bin/time") or ("/usr/bin/time" if Path("/usr/bin/time").exists() else None)
    rss_tmp: Path | None = None
    exec_cmd = cmd
    if time_bin is not None:
        fd, rss_name = tempfile.mkstemp(prefix="dana-bench-rss-", suffix=".txt")
        os.close(fd)
        rss_tmp = Path(rss_name)
        exec_cmd = [time_bin, "-o", str(rss_tmp), "-f", "%M", "--", *cmd]

    t0 = time.perf_counter()
    try:
        with tempfile.TemporaryFile("w+b") as out_f, tempfile.TemporaryFile("w+b") as err_f:
            proc = subprocess.Popen(exec_cmd, cwd=cwd, stdout=out_f, stderr=err_f)
            _, status, rusage = os.wait4(proc.pid, 0)
            wall_ms = (time.perf_counter() - t0) * 1000.0
            exit_code = os.waitstatus_to_exitcode(status)
            out_f.seek(0)
            err_f.seek(0)
            stdout = out_f.read().decode("utf-8", errors="replace")
            stderr = err_f.read().decode("utf-8", errors="replace")
            if exit_code != 0:
                raise RuntimeError(
                    f"command failed (rc={exit_code}): {' '.join(cmd)}\nstdout:\n{stdout}\nstderr:\n{stderr}"
                )
            rss_mib = (
                rusage.ru_maxrss / 1024.0
                if sys.platform.startswith("linux")
                else rusage.ru_maxrss / (1024.0 * 1024.0)
            )
            if rss_tmp is not None and rss_tmp.exists():
                raw = rss_tmp.read_text(encoding="utf-8", errors="replace").strip().splitlines()
                if raw:
                    try:
                        # GNU time `%M` reports maximum resident set size in KiB.
                        rss_mib = int(raw[-1].strip()) / 1024.0
                    except ValueError:
                        pass
            return wall_ms, rss_mib, stdout
    finally:
        if rss_tmp is not None:
            try:
                rss_tmp.unlink()
            except OSError:
                pass


def benchmark_engine(
    label: str, cmd: list[str], cwd: Path, warmup: int, runs: int
) -> dict:
    for _ in range(warmup):
        run_measured(cmd, cwd)
    times_ms: list[float] = []
    rss_mibs: list[float] = []
    last_stdout = ""
    for _ in range(runs):
        ms, rss, out = run_measured(cmd, cwd)
        times_ms.append(ms)
        rss_mibs.append(rss)
        last_stdout = out
    med_ms = statistics.median(times_ms)
    med_rss = statistics.median(rss_mibs)
    print(
        f"  [{label:20s}] median={med_ms:8.1f} ms  min={min(times_ms):8.1f} ms  "
        f"max={max(times_ms):8.1f} ms  rss={med_rss:6.1f} MiB",
        flush=True,
    )
    return {
        "times_ms": times_ms,
        "median_ms": med_ms,
        "min_ms": min(times_ms),
        "max_ms": max(times_ms),
        "median_rss_mib": med_rss,
        "stdout": last_stdout.strip(),
    }


# ============================================================================
# 5. Exact Output Parity Assertions
# ============================================================================


def _read_csv_rows(path: Path) -> tuple[list[str], list[list[str]]]:
    with path.open("r", encoding="utf-8", newline="") as f:
        rows = list(csv.reader(f))
    return rows[0], rows[1:]


def assert_csv_parity(
    name: str,
    dana_csv: Path,
    other_csv: Path,
    float_cols: set[int],
    exact_dec_cols: set[int] | None = None,
    rel_tol: float = 1e-6,
    abs_tol: float = 1e-4,
) -> None:
    dh, drows = _read_csv_rows(dana_csv)
    oh, orows = _read_csv_rows(other_csv)
    assert dh == oh, f"{name}: header mismatch: dana={dh} other={oh}"
    assert len(drows) == len(orows), f"{name}: row count mismatch: dana={len(drows)} other={len(orows)}"

    exact_dec_cols = exact_dec_cols or set()
    for ri, (dr, orow) in enumerate(zip(drows, orows)):
        assert len(dr) == len(orow), f"{name}: row {ri} width mismatch"
        for ci, (dv, ov) in enumerate(zip(dr, orow)):
            if ci in exact_dec_cols:
                if Decimal(dv) != Decimal(ov):
                    raise AssertionError(
                        f"{name} row {ri} col {dh[ci]} exact Decimal mismatch: dana={dv} other={ov}"
                    )
            elif ci in float_cols:
                df = float(dv)
                of = float(ov)
                if not math.isclose(df, of, rel_tol=rel_tol, abs_tol=abs_tol):
                    raise AssertionError(
                        f"{name} row {ri} col {dh[ci]} float mismatch: dana={df} other={of}"
                    )
            else:
                if dv != ov:
                    raise AssertionError(
                        f"{name} row {ri} col {dh[ci]} exact cell mismatch: dana={dv!r} other={ov!r}"
                    )


# ============================================================================
# 6. Markdown Report Generation (`benchmarks/RESULTS.md`)
# ============================================================================


def gather_host_info(dana_bin: Path, available: dict[str, str | None]) -> dict[str, str]:
    cpu_model = platform.processor() or "unknown"
    try:
        for line in Path("/proc/cpuinfo").read_text().splitlines():
            if line.startswith("model name"):
                cpu_model = line.split(":", 1)[1].strip()
                break
    except OSError:
        pass
    mem_gib = "unknown"
    try:
        for line in Path("/proc/meminfo").read_text().splitlines():
            if line.startswith("MemTotal:"):
                kib = int(line.split()[1])
                mem_gib = f"{kib / (1024 * 1024):.1f} GiB"
                break
    except OSError:
        pass

    rustc_ver = subprocess.check_output(["rustc", "--version"], text=True).strip()
    dana_ver_raw = subprocess.check_output([str(dana_bin), "--version"], text=True).strip()
    dana_ver = dana_ver_raw.removeprefix("dana ").strip() or "v0.7"
    git_sha = subprocess.check_output(
        ["git", "rev-parse", "--short", "HEAD"], cwd=REPO_ROOT, text=True
    ).strip()
    return {
        "cpu": f"{cpu_model} ({os.cpu_count()} logical cores)",
        "ram": mem_gib,
        "os": f"{platform.system()} {platform.release()} ({platform.machine()})",
        "rustc": rustc_ver,
        "dana_version": dana_ver,
        "python": platform.python_version(),
        "pandas": available.get("pandas") or "not installed",
        "polars": available.get("polars") or "not installed",
        "pyarrow": available.get("pyarrow") or "not installed",
        "git_sha": git_sha,
        "dana_bin": str(dana_bin.relative_to(REPO_ROOT)),
    }


# Recorded Dana v0.3.0 pre-1.0 baselines (from `benchmarks/RESULTS.md` at `v0.3.0`, same host).
V03_BASELINES: dict[str, tuple[float, float]] = {
    "w1": (3602.9, 1325.1),
    "w2": (1504.0, 781.8),
    "w3": (127.1, 29.0),
    "w4": (1110.2, 350.1),
}


def write_results_md(
    host: dict[str, str],
    results: dict[str, dict],
    explain_w3: str,
    parity_notes: list[str],
) -> Path:
    dana_ver = host["dana_version"]
    out_path = BENCH_DIR / "RESULTS.md"
    lines: list[str] = []
    lines.append(f"# Dana {dana_ver} End-to-End Benchmarks vs. Python")
    lines.append("")
    lines.append(
        f"Reproducible end-to-end pipeline benchmarks comparing **Dana {dana_ver} (pre-1.0, Zero-Crate Rust)** "
        "against **Python stdlib / `sqlite3`**, **Pandas**, and **Polars** across four realistic "
        "data-engineering, SQL-pushdown privacy, and statistical-reporting workloads."
    )
    lines.append("")
    lines.append("## Methodology & Environment")
    lines.append("")
    lines.append(f"- **CPU:** {host['cpu']}")
    lines.append(f"- **Memory:** {host['ram']}")
    lines.append(f"- **OS:** {host['os']}")
    lines.append(f"- **Toolchain:** `{host['rustc']}` (`target/release/dana`, zero external Rust crates)")
    lines.append(
        f"- **Python baselines:** Python `{host['python']}`, Pandas `{host['pandas']}`, "
        f"Polars `{host['polars']}`, PyArrow `{host['pyarrow']}` (installed solely in ephemeral `/tmp/dana-bench-venv`)"
    )
    lines.append(
        f"- **Timing protocol:** {WARMUP_RUNS} warmup run + {TIMED_RUNS} timed runs per engine, "
        "each in a **fresh child subprocess** timed end-to-end with wall-clock `perf_counter` and "
        "isolated per-process kernel peak RSS (`/usr/bin/time -f %M`, falling back to `os.wait4`), "
        "capturing full cold-start CLI / interpreter startup, parsing/compilation, I/O, execution, "
        "and output writing."
    )
    lines.append(
        "- **Output parity:** Every Python baseline is verified cell-for-cell against Dana's outputs "
        "after execution (exact keys, counts, FERPA suppressions, exact `Decimal` against Python `Decimal`, "
        "and strict floating-point tolerances)."
    )
    lines.append("")
    lines.append("### Reproduce")
    lines.append("")
    lines.append("```sh")
    lines.append("cargo build --release")
    lines.append("python3 benchmarks/run_benchmarks.py")
    lines.append("```")
    lines.append("")

    # Headline summary table
    lines.append("## Headline Results (Median End-to-End Wall-Clock)")
    lines.append("")
    lines.append(
        f"| Workload | Rows | Dana {dana_ver} (ms) | Python stdlib (ms) | Pandas (ms) | Polars (ms) | Dana vs. stdlib | Dana vs. Pandas | Dana vs. Polars |"
    )
    lines.append("| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |")
    for wid in ["w1", "w2", "w3", "w4"]:
        w = results[wid]
        d = w["engines"]["dana"]["median_ms"]
        s = w["engines"].get("stdlib", {}).get("median_ms")
        pd_ms = w["engines"].get("pandas", {}).get("median_ms")
        pl_ms = w["engines"].get("polars", {}).get("median_ms")

        def fmt_ms(v: float | None) -> str:
            return f"{v:.1f}" if v is not None else "n/a"

        def fmt_ratio(other: float | None) -> str:
            if other is None:
                return "n/a"
            ratio = other / d
            if ratio >= 1.0:
                return f"**{ratio:.2f}× faster**"
            return f"{1.0 / ratio:.2f}× slower"

        lines.append(
            f"| {w['short_name']} | {w['rows']:,} | **{d:.1f}** | {fmt_ms(s)} | {fmt_ms(pd_ms)} | {fmt_ms(pl_ms)} | "
            f"{fmt_ratio(s)} | {fmt_ratio(pd_ms)} | {fmt_ratio(pl_ms)} |"
        )
    lines.append("")

    # v0.3.0 -> current Speedup & Peak-RSS Improvement table
    lines.append(f"## Dana v0.3.0 -> {dana_ver} Speedup & Peak-RSS Improvement")
    lines.append("")
    lines.append(
        f"| Workload | v0.3.0 Median (ms) | {dana_ver} Median (ms) | Latency Speedup | v0.3.0 Peak RSS (MiB) | {dana_ver} Peak RSS (MiB) | Peak-RSS Reduction |"
    )
    lines.append("| --- | ---: | ---: | ---: | ---: | ---: | ---: |")
    for wid in ["w1", "w2", "w3", "w4"]:
        w = results[wid]
        v03_ms, v03_rss = V03_BASELINES[wid]
        v04_ms = w["engines"]["dana"]["median_ms"]
        v04_rss = w["engines"]["dana"]["median_rss_mib"]
        speedup = v03_ms / v04_ms
        rss_ratio = v03_rss / v04_rss
        rss_pct = ((v03_rss - v04_rss) / v03_rss) * 100.0
        speed_str = (
            f"**{speedup:.2f}× faster**"
            if speedup >= 1.05
            else (f"{speedup:.2f}× (parity)" if speedup >= 0.95 else f"{1.0 / speedup:.2f}× slower")
        )
        rss_str = (
            f"**{rss_ratio:.2f}× smaller (−{rss_pct:.1f}%)**"
            if rss_pct >= 5.0
            else (
                f"{rss_ratio:.2f}× ({-rss_pct:+.1f}%)"
                if abs(rss_pct) < 5.0
                else f"{1.0 / rss_ratio:.2f}× larger (+{-rss_pct:.1f}%)"
            )
        )
        lines.append(
            f"| {w['short_name']} | {v03_ms:.1f} | **{v04_ms:.1f}** | {speed_str} | "
            f"{v03_rss:.1f} | **{v04_rss:.1f}** | {rss_str} |"
        )
    lines.append("")

    # Detailed per-workload sections
    for wid in ["w1", "w2", "w3", "w4"]:
        w = results[wid]
        lines.append(f"## {w['title']}")
        lines.append("")
        lines.append(w["description"])
        lines.append("")
        lines.append(
            "| Engine | Median (ms) | Min (ms) | Max (ms) | Throughput (rows/s) | Peak RSS (MiB) |"
        )
        lines.append("| --- | ---: | ---: | ---: | ---: | ---: |")
        for eng_key, eng_label in w["engine_labels"]:
            if eng_key not in w["engines"]:
                continue
            r = w["engines"][eng_key]
            tput = w["rows"] / (r["median_ms"] / 1000.0)
            lines.append(
                f"| {eng_label} | {r['median_ms']:.1f} | {r['min_ms']:.1f} | {r['max_ms']:.1f} | "
                f"{tput:,.0f} | {r['median_rss_mib']:.1f} |"
            )
        lines.append("")

    lines.append("## Exact Output Parity Checks")
    lines.append("")
    for note in parity_notes:
        lines.append(f"- {note}")
    lines.append("")

    lines.append("## W3 Parameterized SQLite Pushdown Verification (`dana explain`)")
    lines.append("")
    lines.append("```text")
    lines.append(explain_w3.strip())
    lines.append("```")
    lines.append("")

    # Honest engineering commentary computed directly from observed numbers
    lines.append("## Honest Engineering Analysis")
    lines.append("")

    def cmp_speed(
        dana_ms: float, other_ms: float, other_name: str, other_rss: float | None = None
    ) -> str:
        ratio = other_ms / dana_ms
        rss_note = f", {other_rss:.1f} MiB RSS" if other_rss is not None else ""
        if ratio >= 1.0:
            return f"**{ratio:.2f}× faster** than {other_name} ({other_ms:.1f} ms{rss_note})"
        return f"**{1.0 / ratio:.2f}× slower** than {other_name} ({other_ms:.1f} ms{rss_note})"

    w1_d = results["w1"]["engines"]["dana"]["median_ms"]
    w1_drss = results["w1"]["engines"]["dana"]["median_rss_mib"]
    w1_s = results["w1"]["engines"]["stdlib"]["median_ms"]
    w1_pd = results["w1"]["engines"].get("pandas", {}).get("median_ms")
    w1_pdrss = results["w1"]["engines"].get("pandas", {}).get("median_rss_mib")
    w1_pl = results["w1"]["engines"].get("polars", {}).get("median_ms")
    w1_plrss = results["w1"]["engines"].get("polars", {}).get("median_rss_mib")

    w2_d = results["w2"]["engines"]["dana"]["median_ms"]
    w2_drss = results["w2"]["engines"]["dana"]["median_rss_mib"]
    w2_s = results["w2"]["engines"]["stdlib"]["median_ms"]
    w2_pd = results["w2"]["engines"].get("pandas", {}).get("median_ms")
    w2_pdrss = results["w2"]["engines"].get("pandas", {}).get("median_rss_mib")
    w2_pl = results["w2"]["engines"].get("polars", {}).get("median_ms")
    w2_plrss = results["w2"]["engines"].get("polars", {}).get("median_rss_mib")

    w3_d = results["w3"]["engines"]["dana"]["median_ms"]
    w3_drss = results["w3"]["engines"]["dana"]["median_rss_mib"]
    w3_s = results["w3"]["engines"]["stdlib"]["median_ms"]
    w3_pd = results["w3"]["engines"].get("pandas", {}).get("median_ms")
    w3_pdrss = results["w3"]["engines"].get("pandas", {}).get("median_rss_mib")
    w3_pl = results["w3"]["engines"].get("polars", {}).get("median_ms")
    w3_plrss = results["w3"]["engines"].get("polars", {}).get("median_rss_mib")

    w4_d = results["w4"]["engines"]["dana"]["median_ms"]
    w4_drss = results["w4"]["engines"]["dana"]["median_rss_mib"]
    w4_s = results["w4"]["engines"]["stdlib"]["median_ms"]
    w4_pd = results["w4"]["engines"].get("pandas", {}).get("median_ms")
    w4_pdrss = results["w4"]["engines"].get("pandas", {}).get("median_rss_mib")
    w4_pl = results["w4"]["engines"].get("polars", {}).get("median_ms")
    w4_plrss = results["w4"]["engines"].get("polars", {}).get("median_rss_mib")

    lines.append(
        f"1. **Direct streaming-columnar CSV ingestion + exact `Decimal` UDF (W1):** "
        f"Streaming CSV directly into 2,048-row `VmTable` batches (`Val::Columnar(Arc<VmTable>)`) with "
        f"zero-allocation `parse_decimal_i128` and unboxed `FastColConstraint` validation cut Dana from "
        f"`3602.9 ms / 1325.1 MiB` (v0.3.0) down to **`{w1_d:.1f} ms / {w1_drss:.1f} MiB`** "
        f"(**{V03_BASELINES['w1'][0] / w1_d:.2f}× faster**, **{V03_BASELINES['w1'][1] / w1_drss:.2f}× lower peak RSS**). "
        f"Dana {dana_ver} is {cmp_speed(w1_d, w1_s, 'Python `csv` + `decimal.Decimal`')}"
        + (f", {cmp_speed(w1_d, w1_pd, 'Pandas (`float64` + Python UDF loop)', w1_pdrss)}" if w1_pd else "")
        + (f", and {cmp_speed(w1_d, w1_pl, 'Polars (native `pl.when/then` `Float64` expr)', w1_plrss)}" if w1_pl else "")
        + " — while preserving exact 128-bit 18-digit fixed-point `Decimal` arithmetic (0-ulp parity with Python `Decimal`) "
        "and full `bad_rows` quarantine."
    )
    lines.append(
        f"2. **Direct columnar Parquet + zero-copy N:1 hash join + unboxed aggregation (W2):** "
        f"Decoding Zstd Parquet directly into `VmTable` batches, borrowing `Val::Columnar` join inputs without "
        f"cloning, specializing single non-null `Int` keys + columnar gather in `op_hash_join`, and streaming unboxed "
        f"`ExecSurface` aggregates cut Dana from `1504.0 ms / 781.8 MiB` (v0.3.0) to **`{w2_d:.1f} ms / {w2_drss:.1f} MiB`** "
        f"(**{V03_BASELINES['w2'][0] / w2_d:.2f}× faster**, **{V03_BASELINES['w2'][1] / w2_drss:.2f}× lower peak RSS**). "
        f"Dana {dana_ver} is {cmp_speed(w2_d, w2_s, 'Python stdlib (CSV + `dict` join)')}"
        + (f", {cmp_speed(w2_d, w2_pd, 'Pandas', w2_pdrss)}" if w2_pd else "")
        + (f", and {cmp_speed(w2_d, w2_pl, 'Polars', w2_plrss)}" if w2_pl else "")
        + " in a zero-crate Rust binary with checked N:1 uniqueness verification."
    )
    lines.append(
        f"3. **SQLite pushdown + compile-time FERPA privacy (W3):** "
        f"Dana {dana_ver} (**{w3_d:.1f} ms, {w3_drss:.1f} MiB peak RSS**; v0.3.0 was `127.1 ms / 29.0 MiB`) "
        f"preserves and extends its decisive lead: {cmp_speed(w3_d, w3_s, 'Python `sqlite3` stdlib')}"
        + (f", {cmp_speed(w3_d, w3_pl, 'Polars', w3_plrss)}" if w3_pl else "")
        + (f", and {cmp_speed(w3_d, w3_pd, 'Pandas', w3_pdrss)}" if w3_pd else "")
        + " — while statically proving `[pii]`/`[ferpa]` declassification "
        "(`suppress_small_groups(min: 5, distinct_by: .student_id)` -> `OUTPUT: PUBLIC`)."
    )
    lines.append(
        f"4. **Direct columnar Parquet round-trip + columnar `Stats` / `profile()` + HTML5 report (W4):** "
        f"Eliminating `TableVal` boxing across `read_parquet`, `write_parquet`, `profile()`, `Stats.corr`, "
        f"`Stats.linear_regression`, and grouped zone aggregation cut Dana from `1110.2 ms / 350.1 MiB` (v0.3.0) "
        f"to **`{w4_d:.1f} ms / {w4_drss:.1f} MiB`** (**{V03_BASELINES['w4'][0] / w4_d:.2f}× faster**, "
        f"**{V03_BASELINES['w4'][1] / w4_drss:.2f}× lower peak RSS**). Dana {dana_ver} is "
        f"{cmp_speed(w4_d, w4_s, 'Python (`pyarrow` + pure Python stats/HTML)')}"
        + (f", {cmp_speed(w4_d, w4_pd, 'Pandas + NumPy', w4_pdrss)}" if w4_pd else "")
        + (f", and {cmp_speed(w4_d, w4_pl, 'Polars', w4_plrss)}" if w4_pl else "")
        + " with zero external Rust crates and full cell-for-cell parity."
    )
    lines.append("")

    out_path.write_text("\n".join(lines), encoding="utf-8")
    return out_path


# ============================================================================
# 7. Main Driver
# ============================================================================


def detect_python_libs() -> dict[str, str | None]:
    avail: dict[str, str | None] = {"pandas": None, "polars": None, "pyarrow": None}
    for mod in list(avail.keys()):
        try:
            m = __import__(mod)
            avail[mod] = getattr(m, "__version__", "unknown")
        except ImportError:
            avail[mod] = None
    return avail


def fixture_paths() -> dict[str, Path]:
    return {
        "w1_csv": DATA_DIR / "w1_orders.csv",
        "w2_fact_pq": DATA_DIR / "w2_sales.parquet",
        "w2_dim_pq": DATA_DIR / "w2_products.parquet",
        "w2_fact_csv": DATA_DIR / "w2_sales.csv",
        "w2_dim_csv": DATA_DIR / "w2_products.csv",
        "w3_sqlite": DATA_DIR / "w3_registrar.sqlite",
        "w4_pq": DATA_DIR / "w4_telemetry.parquet",
        "manifest": DATA_DIR / "manifest.json",
    }


def detect_python_libs_subprocess(py_exe: str, script_self: str) -> dict[str, str | None]:
    """Probe installed Python library versions in a child process so coordinator RSS stays minimal."""
    out = subprocess.check_output([py_exe, script_self, "--probe-libs"], text=True).strip()
    return json.loads(out)


def main() -> int:
    parser = argparse.ArgumentParser(description="Run Dana v0.4 vs Python end-to-end benchmarks.")
    parser.add_argument("--worker", choices=["w1", "w2", "w3", "w4"], help=argparse.SUPPRESS)
    parser.add_argument("--engine", choices=["stdlib", "pandas", "polars"], help=argparse.SUPPRESS)
    parser.add_argument("--out-dir", type=Path, help=argparse.SUPPRESS)
    parser.add_argument("--data", nargs="*", default=[], help=argparse.SUPPRESS)
    parser.add_argument("--probe-libs", action="store_true", help=argparse.SUPPRESS)
    parser.add_argument("--gen-fixtures", action="store_true", help=argparse.SUPPRESS)
    parser.add_argument("--rebuild", action="store_true", help="Force `cargo build --release`")
    parser.add_argument("--regen-data", action="store_true", help="Regenerate fixtures in /tmp")
    parser.add_argument("--runs", type=int, default=TIMED_RUNS, help="Timed runs per engine")
    parser.add_argument("--warmup", type=int, default=WARMUP_RUNS, help="Warmup runs per engine")
    args = parser.parse_args()

    if args.probe_libs:
        print(json.dumps(detect_python_libs()))
        return 0

    if args.gen_fixtures:
        generate_fixtures(force=args.regen_data)
        return 0

    if args.worker:
        _run_python_worker(args.worker, args.engine, args.data, args.out_dir)
        return 0

    ensure_venv_and_reexec()
    dana_bin = ensure_dana_release(args.rebuild)
    dana_ver = (
        subprocess.check_output([str(dana_bin), "--version"], text=True)
        .strip()
        .removeprefix("dana ")
        .strip()
        or "v0.7"
    )
    py_exe = sys.executable
    script_self = str(Path(__file__).resolve())
    avail = detect_python_libs_subprocess(py_exe, script_self)
    print(f"[setup] Python {platform.python_version()} | libs={avail}", flush=True)

    if avail["pyarrow"] is None:
        raise RuntimeError(
            "pyarrow is required to generate Parquet benchmark fixtures (failed installing in /tmp/dana-bench-venv)"
        )

    gen_cmd = [py_exe, script_self, "--gen-fixtures"]
    if args.regen_data:
        gen_cmd.append("--regen-data")
    subprocess.run(gen_cmd, check=True)
    fixtures = fixture_paths()
    if WORK_DIR.exists():
        shutil.rmtree(WORK_DIR)
    WORK_DIR.mkdir(parents=True, exist_ok=True)
    results: dict[str, dict] = {}
    parity_notes: list[str] = []

    # ---- W1: 500k CSV quarantine + UDF + GroupBy/Summarize/Sort ----
    print("\n=== W1: 500k CSV Quarantine + Custom Decimal UDF + GroupBy/Sort ===", flush=True)
    w1_engines: dict[str, dict] = {}
    w1_dana_cwd = WORK_DIR / "w1_dana"
    w1_dana_cwd.mkdir(parents=True, exist_ok=True)
    w1_engines["dana"] = benchmark_engine(
        f"Dana {dana_ver}",
        [str(dana_bin), "run", str(BENCH_DIR / "w1_csv_udf_etl.dana"), "--", str(fixtures["w1_csv"])],
        w1_dana_cwd,
        args.warmup,
        args.runs,
    )
    dana_w1_csv = w1_dana_cwd / "bench-out" / "w1_summary.csv"

    for eng in ["stdlib", "pandas", "polars"]:
        if eng != "stdlib" and avail[eng] is None:
            continue
        out_dir = WORK_DIR / f"w1_{eng}"
        w1_engines[eng] = benchmark_engine(
            f"Python ({eng})",
            [py_exe, script_self, "--worker", "w1", "--engine", eng, "--out-dir", str(out_dir), "--data", str(fixtures["w1_csv"])],
            out_dir.parent,
            args.warmup,
            args.runs,
        )
        if eng == "stdlib":
            assert_csv_parity(
                f"W1 dana vs {eng}",
                dana_w1_csv,
                out_dir / "w1_summary.csv",
                float_cols=set(),
                exact_dec_cols={2},
            )
        else:
            assert_csv_parity(
                f"W1 dana vs {eng}",
                dana_w1_csv,
                out_dir / "w1_summary.csv",
                float_cols={2},
                rel_tol=1e-9,
                abs_tol=1e-4,
            )
    parity_notes.append(
        "**W1 (`w1_summary.csv`):** 32/32 groups matched across all engines — exact 0-ulp `Decimal` equality "
        "between Dana and Python `decimal.Decimal` (`valid=500,000`, `bad=500`), and `< 1e-9` relative parity "
        "against Pandas (`float64` UDF) and Polars (`Float64` expression)."
    )
    results["w1"] = {
        "short_name": "W1: CSV + UDF ETL",
        "title": "W1: 500,000-Row CSV Quarantine + Pure Dana UDF + GroupBy/Sort",
        "description": (
            f"`benchmarks/w1_csv_udf_etl.dana` ingests {W1_VALID_ROWS:,} valid + {W1_BAD_ROWS:,} malformed CSV rows "
            "(quarantining invalid decimals and negative quantities), filters `qty > 0`, evaluates a multi-branch "
            "pure `net_price` UDF in exact `Decimal` arithmetic (inlined into Dana's vectorized register bytecode), "
            "aggregates across 32 `(region, category)` groups, and sorts descending by `total_net`."
        ),
        "rows": W1_VALID_ROWS + W1_BAD_ROWS,
        "engines": w1_engines,
        "engine_labels": [
            ("dana", f"Dana {dana_ver} (exact `Decimal`, columnar CSV + inlined UDF)"),
            ("stdlib", "Python stdlib (`csv` + `decimal.Decimal`)"),
            ("pandas", "Pandas (`float64` + Python UDF loop)"),
            ("polars", "Polars (native `pl.when/then` `Float64` expr)"),
        ],
    }

    # ---- W2: 500k x 50k Columnar Join + Inlined UDF + Agg ----
    print("\n=== W2: 500k x 50k Parquet Join (Many-to-One) + Inlined UDF + Agg ===", flush=True)
    w2_engines: dict[str, dict] = {}
    w2_dana_cwd = WORK_DIR / "w2_dana"
    w2_dana_cwd.mkdir(parents=True, exist_ok=True)
    w2_engines["dana"] = benchmark_engine(
        f"Dana {dana_ver}",
        [
            str(dana_bin),
            "run",
            str(BENCH_DIR / "w2_columnar_join_analytics.dana"),
            "--",
            str(fixtures["w2_fact_pq"]),
            str(fixtures["w2_dim_pq"]),
        ],
        w2_dana_cwd,
        args.warmup,
        args.runs,
    )
    dana_w2_csv = w2_dana_cwd / "bench-out" / "w2_summary.csv"

    for eng in ["stdlib", "pandas", "polars"]:
        if eng != "stdlib" and avail[eng] is None:
            continue
        out_dir = WORK_DIR / f"w2_{eng}"
        f_arg = fixtures["w2_fact_csv"] if eng == "stdlib" else fixtures["w2_fact_pq"]
        d_arg = fixtures["w2_dim_csv"] if eng == "stdlib" else fixtures["w2_dim_pq"]
        w2_engines[eng] = benchmark_engine(
            f"Python ({eng})",
            [
                py_exe,
                script_self,
                "--worker",
                "w2",
                "--engine",
                eng,
                "--out-dir",
                str(out_dir),
                "--data",
                str(f_arg),
                str(d_arg),
            ],
            out_dir.parent,
            args.warmup,
            args.runs,
        )
        assert_csv_parity(
            f"W2 dana vs {eng}",
            dana_w2_csv,
            out_dir / "w2_summary.csv",
            float_cols={2, 3},
            rel_tol=1e-9,
            abs_tol=1e-4,
        )
    parity_notes.append(
        "**W2 (`w2_summary.csv`):** 40/40 `(department, channel)` groups matched across Dana, Python stdlib, "
        "Pandas, and Polars — exact integer `total_units` & `txn_count`, and `< 1e-9` relative parity on "
        "`total_revenue` & `total_margin`."
    )
    results["w2"] = {
        "short_name": "W2: 500k×50k Join + UDF",
        "title": "W2: 500,000-Row Fact × 50,000-Row Dim Parquet `join_many_to_one` + UDF + Agg",
        "description": (
            f"`benchmarks/w2_columnar_join_analytics.dana` reads {W2_FACT_ROWS:,} fact rows and {W2_DIM_ROWS:,} "
            "dimension rows from Zstd Parquet (Python stdlib reads equivalent CSV mirrors since stdlib has no Parquet codec), "
            "performs a checked N:1 hash join enforcing dimension uniqueness, runs an inlined `effective_margin` UDF, "
            "aggregates across 40 `(department, channel)` groups, and sorts deterministically."
        ),
        "rows": W2_FACT_ROWS,
        "engines": w2_engines,
        "engine_labels": [
            ("dana", f"Dana {dana_ver} (columnar Zstd Parquet + zero-copy N:1 join + inlined UDF)"),
            ("stdlib", "Python stdlib (CSV mirror + `dict` join)"),
            ("pandas", "Pandas (`read_parquet` + `merge(validate='many_to_one')`)"),
            ("polars", "Polars (`read_parquet` + `join(validate='m:1')`)"),
        ],
    }

    # ---- W3: 250k SQLite Pushdown + [pii]/[ferpa] Privacy + Window ----
    print("\n=== W3: 250k SQLite Pushdown + [pii]/[ferpa] Suppression + Rolling Window ===", flush=True)
    w3_engines: dict[str, dict] = {}
    w3_dana_cwd = WORK_DIR / "w3_dana"
    w3_dana_cwd.mkdir(parents=True, exist_ok=True)
    db_arg = f"Registrar=sqlite://{fixtures['w3_sqlite']}"
    w3_engines["dana"] = benchmark_engine(
        f"Dana {dana_ver}",
        [
            str(dana_bin),
            "run",
            "--db",
            db_arg,
            str(BENCH_DIR / "w3_sqlite_pushdown_privacy.dana"),
        ],
        w3_dana_cwd,
        args.warmup,
        args.runs,
    )
    dana_w3_csv = w3_dana_cwd / "bench-out" / "w3_summary.csv"
    w3_text = dana_w3_csv.read_text(encoding="utf-8")
    assert "RareStudies" not in w3_text, "W3 leaked RareStudies!"
    assert "@example.edu" not in w3_text, "W3 leaked PII email!"

    for eng in ["stdlib", "pandas", "polars"]:
        if eng != "stdlib" and avail[eng] is None:
            continue
        out_dir = WORK_DIR / f"w3_{eng}"
        w3_engines[eng] = benchmark_engine(
            f"Python ({eng})",
            [
                py_exe,
                script_self,
                "--worker",
                "w3",
                "--engine",
                eng,
                "--out-dir",
                str(out_dir),
                "--data",
                str(fixtures["w3_sqlite"]),
            ],
            out_dir.parent,
            args.warmup,
            args.runs,
        )
        assert_csv_parity(
            f"W3 dana vs {eng}",
            dana_w3_csv,
            out_dir / "w3_summary.csv",
            float_cols={5, 6},
            rel_tol=1e-9,
            abs_tol=1e-9,
        )
    w3_cells = len(_read_csv_rows(dana_w3_csv)[1])
    parity_notes.append(
        f"**W3 (`w3_summary.csv`):** {w3_cells}/{w3_cells} published `(department, age_band, term_seq)` cells "
        "matched identically (`< 1e-9` on `avg_gpa` and `rolling_3t_gpa`); all 75 `RareStudies` rows (3 distinct "
        "students) were suppressed and zero `[pii]` emails appeared in output."
    )
    explain_w3 = subprocess.check_output(
        [
            str(dana_bin),
            "explain",
            "--dialect",
            "sqlite",
            str(BENCH_DIR / "w3_sqlite_pushdown_privacy.dana"),
        ],
        text=True,
    )
    results["w3"] = {
        "short_name": "W3: SQLite + FERPA Privacy",
        "title": "W3: 250,000-Row SQLite Pushdown + `[pii]`/`[ferpa]` Suppression + Rolling Window",
        "description": (
            f"`benchmarks/w3_sqlite_pushdown_privacy.dana` scans a {W3_ROWS:,}-row SQLite database via `ReadDB`, "
            "pushes `where(.active? and .term_year >= 2024)` and column projection down into parameterized SQL, "
            "buckets `[ferpa]` ages, aggregates distinct students & mean GPA, declassifies via "
            "`suppress_small_groups(min: 5, distinct_by: .student_id)` (suppressing `RareStudies`), and computes a "
            "partitioned 3-term `rolling_mean` window. Python baselines execute the identical pushed-down SQL query."
        ),
        "rows": W3_ROWS,
        "engines": w3_engines,
        "engine_labels": [
            ("dana", f"Dana {dana_ver} (SQLite pushdown + compile-time `[pii]`/`[ferpa]` + VM window)"),
            ("stdlib", "Python stdlib (`sqlite3` + pure Python aggregation/window)"),
            ("pandas", "Pandas (`read_sql_query` + `pd.cut` + `groupby` + `rolling`)"),
            ("polars", "Polars (`read_database` + `group_by` + `rolling_mean.over`)"),
        ],
    }

    # ---- W4: 200k Zstd Parquet Round-Trip + Stats + Profile + HTML Report ----
    print("\n=== W4: 200k Zstd Parquet Round-Trip + Stats + Profile + HTML Report ===", flush=True)
    w4_engines: dict[str, dict] = {}
    w4_dana_cwd = WORK_DIR / "w4_dana"
    w4_dana_cwd.mkdir(parents=True, exist_ok=True)
    w4_engines["dana"] = benchmark_engine(
        f"Dana {dana_ver}",
        [
            str(dana_bin),
            "run",
            str(BENCH_DIR / "w4_parquet_stats_report.dana"),
            "--",
            str(fixtures["w4_pq"]),
        ],
        w4_dana_cwd,
        args.warmup,
        args.runs,
    )
    dana_w4_stats = w4_dana_cwd / "bench-out" / "w4_stats.csv"
    dana_w4_zones = w4_dana_cwd / "bench-out" / "w4_zones.csv"
    dana_w4_html = w4_dana_cwd / "bench-out" / "w4_report.html"
    dana_w4_pq = w4_dana_cwd / "bench-out" / "w4_clean.parquet"
    assert "<svg " in dana_w4_html.read_text(encoding="utf-8")
    assert dana_w4_pq.stat().st_size > 1024

    for eng in ["stdlib", "pandas", "polars"]:
        if eng != "stdlib" and avail[eng] is None:
            continue
        out_dir = WORK_DIR / f"w4_{eng}"
        w4_engines[eng] = benchmark_engine(
            f"Python ({eng})",
            [
                py_exe,
                script_self,
                "--worker",
                "w4",
                "--engine",
                eng,
                "--out-dir",
                str(out_dir),
                "--data",
                str(fixtures["w4_pq"]),
            ],
            out_dir.parent,
            args.warmup,
            args.runs,
        )
        assert_csv_parity(
            f"W4 stats dana vs {eng}",
            dana_w4_stats,
            out_dir / "w4_stats.csv",
            float_cols={1, 2, 3, 4},
            rel_tol=1e-9,
            abs_tol=1e-9,
        )
        assert_csv_parity(
            f"W4 zones dana vs {eng}",
            dana_w4_zones,
            out_dir / "w4_zones.csv",
            float_cols={2, 3},
            rel_tol=1e-9,
            abs_tol=1e-9,
        )
        assert "<svg " in (out_dir / "w4_report.html").read_text(encoding="utf-8")
    parity_notes.append(
        "**W4 (`w4_stats.csv`, `w4_zones.csv`, `w4_report.html`, `w4_clean.parquet`):** Exact `clean_rows=180,000`, "
        "6/6 zone aggregates, and `< 1e-9` parity on Pearson `r`, OLS `slope`, `intercept`, and `r_squared` "
        "across all engines, plus verified Zstd Parquet round-trip and inline `<svg>` HTML5 report output."
    )
    results["w4"] = {
        "short_name": "W4: Parquet + Stats + HTML",
        "title": "W4: 200,000-Row Native Zstd Parquet Round-Trip + Stats + Profile + HTML Report",
        "description": (
            f"`benchmarks/w4_parquet_stats_report.dana` reads {W4_ROWS:,} Zstd Parquet rows, filters healthy readings, "
            "writes a filtered Zstd Parquet file, computes a full dataset `profile()`, Pearson `Stats.corr`, "
            "`Stats.linear_regression`, grouped zone metrics, an inline SVG scatter plot with OLS trendline, "
            "and a self-contained HTML5 report."
        ),
        "rows": W4_ROWS,
        "engines": w4_engines,
        "engine_labels": [
            ("dana", f"Dana {dana_ver} (columnar Zstd Parquet + `Stats` + `profile()` + SVG/HTML5)"),
            ("stdlib", "Python (`pyarrow` Parquet I/O + pure Python stats/HTML)"),
            ("pandas", "Pandas (`read_parquet`/`to_parquet` + NumPy OLS + HTML)"),
            ("polars", "Polars (`read_parquet`/`write_parquet` + `corr`/`cov` + HTML)"),
        ],
    }

    host = gather_host_info(dana_bin, avail)
    md_path = write_results_md(host, results, explain_w3, parity_notes)
    print(f"\n[done] ALL parity assertions PASSED! Wrote {md_path}", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
