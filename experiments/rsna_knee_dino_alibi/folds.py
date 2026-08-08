#!/usr/bin/env python3
"""Create deterministic scanner-grouped, multilabel-balanced fold assignments."""

from __future__ import annotations

import argparse
from pathlib import Path

import numpy as np
import pandas as pd

try:
    from .constants import TARGETS
except ImportError:
    from constants import TARGETS


def grouped_multilabel_folds(
    frame: pd.DataFrame,
    group_column: str,
    n_folds: int,
    seed: int,
) -> np.ndarray:
    """Greedily allocate whole scanner groups while balancing label mass.

    Missing labels contribute neither positive nor negative mass.  The
    objective balances positives, observed examples, and study count.  This is
    deliberately deterministic after the seeded group tie-break.
    """

    if group_column not in frame:
        raise ValueError(f"missing group column {group_column!r}")
    if frame[group_column].isna().any():
        raise ValueError("scanner groups must not be missing")
    if frame[group_column].nunique() < n_folds:
        raise ValueError("fewer scanner groups than folds")
    labels = frame.reindex(columns=TARGETS).apply(pd.to_numeric, errors="coerce")
    groups = frame[group_column].astype(str)
    unique = groups.unique().tolist()
    rng = np.random.default_rng(seed)
    tie = {group: float(rng.random()) for group in unique}

    records = []
    for group in unique:
        rows = groups == group
        y = labels.loc[rows]
        records.append(
            {
                "group": group,
                "count": int(rows.sum()),
                "positive": np.nansum(y.to_numpy(dtype=float), axis=0),
                "observed": np.isfinite(y.to_numpy(dtype=float)).sum(axis=0),
                "rarity": float(
                    np.nansum(y.to_numpy(dtype=float) / np.maximum(labels.sum(axis=0).to_numpy(), 1))
                ),
            }
        )
    records.sort(key=lambda row: (-row["rarity"], -row["count"], tie[row["group"]]))

    global_positive = sum((row["positive"] for row in records), np.zeros(len(TARGETS)))
    global_observed = sum((row["observed"] for row in records), np.zeros(len(TARGETS)))
    target_positive = global_positive / n_folds
    target_observed = global_observed / n_folds
    target_count = len(frame) / n_folds
    fold_positive = np.zeros((n_folds, len(TARGETS)), dtype=float)
    fold_observed = np.zeros((n_folds, len(TARGETS)), dtype=float)
    fold_count = np.zeros(n_folds, dtype=float)
    allocation: dict[str, int] = {}

    for order, record in enumerate(records):
        # Seed every fold before optimizing, preventing an early zero-fold
        # degeneracy when group label vectors are similar.
        candidates = [order] if order < n_folds else list(range(n_folds))
        scores = []
        for fold in candidates:
            candidate_positive = fold_positive.copy()
            candidate_observed = fold_observed.copy()
            candidate_count = fold_count.copy()
            candidate_positive[fold] += record["positive"]
            candidate_observed[fold] += record["observed"]
            candidate_count[fold] += record["count"]
            positive_error = np.mean(
                ((candidate_positive - target_positive) / np.maximum(target_positive, 1)) ** 2
            )
            observed_error = np.mean(
                ((candidate_observed - target_observed) / np.maximum(target_observed, 1)) ** 2
            )
            count_error = np.mean(((candidate_count - target_count) / max(target_count, 1)) ** 2)
            scores.append((positive_error + 0.25 * observed_error + 0.5 * count_error, fold))
        _, chosen = min(scores, key=lambda pair: (pair[0], pair[1]))
        allocation[record["group"]] = chosen
        fold_positive[chosen] += record["positive"]
        fold_observed[chosen] += record["observed"]
        fold_count[chosen] += record["count"]
    return groups.map(allocation).to_numpy(dtype=np.int64)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cache-index", type=Path, required=True)
    parser.add_argument("--labels-csv", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--group-column", default="scanner_group")
    parser.add_argument("--folds", type=int, default=5)
    parser.add_argument("--seed", type=int, default=2026)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    cache = pd.read_csv(args.cache_index)
    labels = pd.read_csv(args.labels_csv)
    frame = cache.merge(labels, on="StudyInstanceUID", how="inner", validate="one_to_one")
    frame["fold"] = grouped_multilabel_folds(
        frame, args.group_column, args.folds, args.seed
    )
    output_columns = ["StudyInstanceUID", "fold"]
    labels = labels.merge(frame[output_columns], on="StudyInstanceUID", how="left", validate="one_to_one")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    labels.to_csv(args.output, index=False)
    summary = frame.groupby("fold").agg(
        studies=("StudyInstanceUID", "size"),
        scanner_groups=(args.group_column, "nunique"),
    )
    print(summary.to_string())
    print(f"wrote {args.output}")


if __name__ == "__main__":
    main()
