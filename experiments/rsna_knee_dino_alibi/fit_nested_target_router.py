#!/usr/bin/env python3
"""Fit a conservative target-wise model router from expert OOF labels.

Unlike a free convex stack, this router chooses one complete model family per
pathology.  Every held-out fold is scored using a choice made on the other
folds, and a candidate must beat the anchor by both a minimum AUC margin and a
paired stratified-bootstrap probability.  Small expert subsets therefore
shrink automatically to the required anchor.
"""

from __future__ import annotations

import argparse
import glob
import json
from pathlib import Path

import numpy as np
import pandas as pd
from sklearn.metrics import roc_auc_score

try:
    from .constants import TARGETS
except ImportError:
    from constants import TARGETS


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--labels-csv", type=Path, required=True)
    parser.add_argument("--member", action="append", required=True, help="NAME=OOF_GLOB")
    parser.add_argument("--anchor", required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--fold-column", default="fold")
    parser.add_argument("--minimum-target-gain", type=float, default=0.01)
    parser.add_argument("--minimum-nested-gain", type=float, default=0.005)
    parser.add_argument("--minimum-selection-probability", type=float, default=0.70)
    parser.add_argument("--minimum-class-count", type=int, default=4)
    parser.add_argument("--bootstrap-samples", type=int, default=2000)
    parser.add_argument("--seed", type=int, default=2026)
    return parser.parse_args()


def load_member(specification: str) -> tuple[str, pd.DataFrame, list[str]]:
    if "=" not in specification:
        raise ValueError("member must be NAME=OOF_GLOB")
    name, pattern = specification.split("=", 1)
    paths = sorted(glob.glob(pattern))
    if not name or not paths:
        raise ValueError(f"member {specification!r} resolved to no OOF files")
    frames = [pd.read_csv(path, dtype={"StudyInstanceUID": str}) for path in paths]
    frame = pd.concat(frames, ignore_index=True)
    if missing := {"StudyInstanceUID", *TARGETS}.difference(frame.columns):
        raise ValueError(f"member {name!r} is missing {sorted(missing)}")
    if frame["StudyInstanceUID"].duplicated().any():
        raise ValueError(f"member {name!r} contains duplicate OOF studies")
    return name, frame[["StudyInstanceUID", *TARGETS]], paths


def finite_auc(labels: np.ndarray, prediction: np.ndarray) -> float:
    valid = np.isfinite(labels) & np.isfinite(prediction)
    if np.unique(labels[valid]).size != 2:
        return float("nan")
    return float(roc_auc_score(labels[valid], prediction[valid]))


def paired_probability(
    labels: np.ndarray,
    anchor: np.ndarray,
    candidate: np.ndarray,
    samples: int,
    rng: np.random.Generator,
) -> float:
    positive = np.flatnonzero(labels > 0.5)
    negative = np.flatnonzero(labels <= 0.5)
    if not len(positive) or not len(negative):
        return 0.0

    def pair_credit(score: np.ndarray) -> np.ndarray:
        difference = score[positive, None] - score[negative][None, :]
        return (difference > 0).astype(float) + 0.5 * (difference == 0)

    anchor_credit = pair_credit(anchor)
    candidate_credit = pair_credit(candidate)
    positive_draw = rng.integers(len(positive), size=(samples, len(positive)))
    negative_draw = rng.integers(len(negative), size=(samples, len(negative)))
    anchor_auc = anchor_credit[
        positive_draw[:, :, None], negative_draw[:, None, :]
    ].mean(axis=(1, 2))
    candidate_auc = candidate_credit[
        positive_draw[:, :, None], negative_draw[:, None, :]
    ].mean(axis=(1, 2))
    return float(np.mean(candidate_auc > anchor_auc))


def choose_member(
    labels: np.ndarray,
    predictions: np.ndarray,
    anchor_index: int,
    args: argparse.Namespace,
    rng: np.random.Generator,
) -> tuple[int, dict[str, float | int]]:
    positive = int((labels > 0.5).sum())
    negative = int((labels <= 0.5).sum())
    anchor_auc = finite_auc(labels, predictions[:, anchor_index])
    evidence: dict[str, float | int] = {
        "positive": positive,
        "negative": negative,
        "anchor_auc": anchor_auc,
        "selected_gain": 0.0,
        "selection_probability": 0.0,
    }
    if min(positive, negative) < args.minimum_class_count:
        return anchor_index, evidence
    best = anchor_index
    best_score = anchor_auc
    best_probability = 0.0
    for candidate in range(predictions.shape[1]):
        if candidate == anchor_index:
            continue
        score = finite_auc(labels, predictions[:, candidate])
        gain = score - anchor_auc
        if not np.isfinite(gain) or gain < args.minimum_target_gain:
            continue
        probability = paired_probability(
            labels,
            predictions[:, anchor_index],
            predictions[:, candidate],
            args.bootstrap_samples,
            rng,
        )
        if probability < args.minimum_selection_probability:
            continue
        if (score, probability, -candidate) > (best_score, best_probability, -best):
            best, best_score, best_probability = candidate, score, probability
    if best != anchor_index:
        evidence["selected_gain"] = best_score - anchor_auc
        evidence["selection_probability"] = best_probability
    return best, evidence


def main() -> None:
    args = parse_args()
    if args.bootstrap_samples < 1:
        raise ValueError("bootstrap_samples must be positive")
    loaded = [load_member(specification) for specification in args.member]
    names = [name for name, _, _ in loaded]
    if len(set(names)) != len(names):
        raise ValueError("member names must be unique")
    if args.anchor not in names:
        raise ValueError("anchor must name one supplied member")
    anchor_index = names.index(args.anchor)
    labels = pd.read_csv(args.labels_csv, dtype={"StudyInstanceUID": str})
    if args.fold_column not in labels:
        raise ValueError("labels must contain precomputed leakage-safe folds")
    gold = [column for column in labels if column.endswith("__gold")]
    merged = labels[["StudyInstanceUID", args.fold_column, *TARGETS, *gold]].copy()
    for name, frame, _ in loaded:
        merged = merged.merge(
            frame.rename(columns={target: f"{name}::{target}" for target in TARGETS}),
            on="StudyInstanceUID",
            how="inner",
            validate="one_to_one",
        )
    if not len(merged):
        raise ValueError("labels and OOF members have no shared studies")

    folds = sorted(pd.unique(merged[args.fold_column]))
    nested_rows = []
    final_weights: dict[str, list[float]] = {}
    final_choice: dict[str, str] = {}
    final_evidence: dict[str, dict[str, float | int]] = {}
    rng = np.random.default_rng(args.seed)
    for target in TARGETS:
        target_labels = pd.to_numeric(merged[target], errors="coerce").to_numpy(float)
        predictions = np.column_stack(
            [
                pd.to_numeric(merged[f"{name}::{target}"], errors="coerce")
                .to_numpy(float)
                for name in names
            ]
        )
        expert = np.isfinite(target_labels) & np.isfinite(predictions).all(axis=1)
        marker = f"{target}__gold"
        if marker in merged:
            expert &= (
                pd.to_numeric(merged[marker], errors="coerce").fillna(0).to_numpy() > 0
            )
        for held_fold in folds:
            training = expert & (merged[args.fold_column].to_numpy() != held_fold)
            held = expert & (merged[args.fold_column].to_numpy() == held_fold)
            selected, evidence = choose_member(
                target_labels[training], predictions[training], anchor_index, args, rng
            )
            nested_rows.append(
                {
                    "fold": int(held_fold),
                    "target": target,
                    "selected": names[selected],
                    **evidence,
                    "selected_auc": finite_auc(
                        target_labels[held], predictions[held, selected]
                    ),
                    "anchor_held_auc": finite_auc(
                        target_labels[held], predictions[held, anchor_index]
                    ),
                }
            )
        selected, evidence = choose_member(
            target_labels[expert], predictions[expert], anchor_index, args, rng
        )
        final_choice[target] = names[selected]
        final_evidence[target] = evidence
        final_weights[target] = [float(index == selected) for index in range(len(names))]

    nested = pd.DataFrame(nested_rows)
    nested_macro = float(nested["selected_auc"].mean())
    anchor_macro = float(nested["anchor_held_auc"].mean())
    nested_gain = nested_macro - anchor_macro
    promote = bool(nested_gain >= args.minimum_nested_gain)
    if not promote:
        final_choice = {target: args.anchor for target in TARGETS}
        final_weights = {
            target: [float(index == anchor_index) for index in range(len(names))]
            for target in TARGETS
        }
    artifact = {
        "schema_version": 1,
        "method": "nested expert-only target router with paired bootstrap shrinkage",
        "members": names,
        "anchor": args.anchor,
        "weights": final_weights,
        "target_choice": final_choice,
        "target_evidence": final_evidence,
        "nested_macro_auc": nested_macro,
        "nested_anchor_macro_auc": anchor_macro,
        "nested_gain": nested_gain,
        "minimum_nested_gain": args.minimum_nested_gain,
        "minimum_target_gain": args.minimum_target_gain,
        "minimum_selection_probability": args.minimum_selection_probability,
        "router_promoted": promote,
        "studies": len(merged),
        "source_files": {name: paths for name, _, paths in loaded},
        "fold_results": nested_rows,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(artifact, indent=2, allow_nan=True) + "\n")
    nested.to_csv(args.output.with_suffix(".fold_targets.csv"), index=False)
    print(
        json.dumps(
            {
                "nested_macro_auc": nested_macro,
                "nested_anchor_macro_auc": anchor_macro,
                "nested_gain": nested_gain,
                "router_promoted": promote,
                "target_choice": final_choice,
            },
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
