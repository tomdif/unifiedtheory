#!/usr/bin/env python3
"""Merge independently written feature-cache indexes with strict coverage checks."""

from __future__ import annotations

import argparse
import glob
from pathlib import Path

import pandas as pd


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input-glob", required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--expected-studies", type=int, required=True)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    paths = [Path(path) for path in sorted(glob.glob(args.input_glob))]
    if not paths:
        raise ValueError("input glob resolved to no cache indexes")
    frames = [pd.read_csv(path, dtype={"StudyInstanceUID": str}) for path in paths]
    merged = pd.concat(frames, ignore_index=True)
    required = {"StudyInstanceUID", "cache_file"}
    if missing := required.difference(merged.columns):
        raise ValueError(f"cache indexes are missing columns: {sorted(missing)}")
    duplicates = merged[merged["StudyInstanceUID"].duplicated(keep=False)]
    if len(duplicates):
        values = sorted(duplicates["StudyInstanceUID"].unique())[:5]
        raise ValueError(f"duplicate studies across cache shards: {values}")
    if len(merged) != args.expected_studies:
        raise ValueError(
            f"merged {len(merged)} studies; expected {args.expected_studies}"
        )
    absent = [path for path in merged["cache_file"].map(Path) if not path.is_file()]
    if absent:
        raise FileNotFoundError(f"{len(absent)} indexed cache files are absent")
    merged = merged.sort_values("StudyInstanceUID").reset_index(drop=True)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    merged.to_csv(args.output, index=False)
    print(
        f"merged {len(paths)} shards and {len(merged)} unique studies into {args.output}"
    )


if __name__ == "__main__":
    main()
