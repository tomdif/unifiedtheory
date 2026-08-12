#!/usr/bin/env python3
"""Run the preregistered knee-native SSL -> supervised fold-0 experiment."""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--data-root", type=Path, required=True)
    parser.add_argument("--labels-csv", type=Path, required=True)
    parser.add_argument("--model-name", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--pretrain-epochs", type=int, default=3)
    parser.add_argument("--finetune-epochs", type=int, default=3)
    parser.add_argument("--seed", type=int, default=2026)
    parser.add_argument("--workers", type=int, default=4)
    parser.add_argument("--limit-studies", type=int, default=0)
    return parser.parse_args()


def run(command: list[str]) -> None:
    print(" ".join(command), flush=True)
    subprocess.run(command, check=True)


def main() -> None:
    args = parse_args()
    here = Path(__file__).resolve().parent
    ssl = args.output / "ssl"
    supervised = args.output / "supervised"
    ssl_checkpoint = ssl / "knee_native_backbone.pt"
    if not ssl_checkpoint.is_file():
        command = [
            sys.executable,
            str(here / "pretrain_knee_native.py"),
            "--data-root",
            str(args.data_root),
            "--output",
            str(ssl),
            "--study-list-csv",
            str(args.labels_csv),
            "--exclude-fold",
            "0",
            "--model-name",
            str(args.model_name),
            "--local-files-only",
            "--image-size",
            "224",
            "--slices",
            "8",
            "--batch-size",
            "2",
            "--workers",
            str(args.workers),
            "--epochs",
            str(args.pretrain_epochs),
            "--lora-rank",
            "8",
            "--encoder-batch-size",
            "8",
            "--seed",
            str(args.seed),
        ]
        if args.limit_studies:
            command.extend(["--limit-studies", str(args.limit_studies)])
        run(command)
    checkpoint = supervised / "dinov2_copas_lora8_336_fold0.pt"
    if not checkpoint.is_file():
        command = [
            sys.executable,
            str(here / "train_raw_mil.py"),
            "--data-root",
            str(args.data_root),
            "--labels-csv",
            str(args.labels_csv),
            "--output",
            str(supervised),
            "--backbone",
            "dinov2",
            "--model-name",
            str(args.model_name),
            "--backbone-checkpoint",
            str(ssl_checkpoint),
            "--local-files-only",
            "--architecture",
            "copas",
            "--fold",
            "0",
            "--image-size",
            "336",
            "--train-slices",
            "6",
            "--val-slices",
            "16",
            "--max-series-per-plane",
            "2",
            "--trainable-blocks",
            "0",
            "--lora-rank",
            "8",
            "--encoder-batch-size",
            "12",
            "--batch-size",
            "1",
            "--accumulate",
            "4",
            "--workers",
            str(args.workers),
            "--epochs",
            str(args.finetune_epochs),
            "--patience",
            "2",
            "--branch-loss-weight",
            "0.25",
            "--clinical-branch-mask",
            "--specialist-bottleneck",
            "64",
            "--seed",
            str(args.seed),
        ]
        if args.limit_studies:
            command.extend(["--limit-studies", str(args.limit_studies)])
        run(command)
    contract = {
        "schema_version": 1,
        "experiment": "knee_native_ssl_clinical_specialist_fold0",
        "pretraining_data": "competition train images only",
        "pretraining_fold_policy": "exclude supervised held-out fold 0",
        "fold": 0,
        "seed": args.seed,
        "pretrain_epochs": args.pretrain_epochs,
        "finetune_epochs": args.finetune_epochs,
        "minimum_macro_auc_gain": 0.02,
        "maximum_materially_worsened_targets": 4,
        "full_cv_automatically_authorized": False,
        "ssl_checkpoint": str(ssl_checkpoint),
        "supervised_checkpoint": str(checkpoint),
    }
    args.output.mkdir(parents=True, exist_ok=True)
    (args.output / "contract.json").write_text(json.dumps(contract, indent=2) + "\n")
    print(json.dumps(contract, indent=2))


if __name__ == "__main__":
    main()
