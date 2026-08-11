#!/usr/bin/env python3
"""Smoke-test that the adaptive review packet never authorizes full CV."""

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path
from tempfile import TemporaryDirectory

import torch


def main() -> None:
    here = Path(__file__).resolve().parent
    with TemporaryDirectory() as directory:
        root = Path(directory)
        (root / "stage2.json").write_text(
            json.dumps(
                {
                    "candidate_gain": 0.006,
                    "fixed_rank_blend_gain": 0.007,
                    "promote_candidate": True,
                    "promote_fixed_rank_blend": True,
                    "minimum_preregistered_gain": 0.005,
                }
            )
        )
        (root / "history.json").write_text(
            json.dumps(
                [
                    {
                        "train_loss": 0.5,
                        "macro_auc": 0.6,
                        "train_seconds": 10.0,
                        "evaluation_seconds": 2.0,
                        "peak_cuda_gib": 3.0,
                    }
                ]
            )
        )
        (root / "exit").write_text("0\n")
        torch.save(
            {
                "args": {"architecture": "copas", "limit_studies": 32},
                "backbone_lora_modules": ["encoder.layer.0.attention.attention.query"],
                "trainable_parameters": 100,
                "total_parameters": 1000,
            },
            root / "pilot.pt",
        )
        output = root / "review.json"
        subprocess.run(
            [
                sys.executable,
                str(here / "adaptive_review_gate.py"),
                "--stage2-audit",
                str(root / "stage2.json"),
                "--pilot-history",
                str(root / "history.json"),
                "--pilot-checkpoint",
                str(root / "pilot.pt"),
                "--pilot-exit",
                str(root / "exit"),
                "--output",
                str(output),
            ],
            check=True,
            capture_output=True,
            text=True,
        )
        artifact = json.loads(output.read_text())
        if artifact["state"] != "manual_review_required":
            raise AssertionError("review gate did not stop at manual review")
        if artifact["full_cv_authorized"]:
            raise AssertionError("a systems pilot incorrectly authorized full CV")
        if not artifact["system_pilot"]["passed"]:
            raise AssertionError("valid systems pilot did not pass its systems gate")
    print("adaptive review gate smoke passed")


if __name__ == "__main__":
    main()
