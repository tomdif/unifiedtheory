#!/usr/bin/env python3
"""Assemble Stage-2 and adaptive system-pilot evidence for manual review.

This gate deliberately cannot authorize full cross-validation. Its output is
an evidence packet whose terminal state is always ``manual_review_required``.
"""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any

import torch


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--stage2-audit", type=Path, required=True)
    parser.add_argument("--pilot-history", type=Path, required=True)
    parser.add_argument("--pilot-checkpoint", type=Path, required=True)
    parser.add_argument("--pilot-exit", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    return parser.parse_args()


def read_json(path: Path) -> Any:
    if not path.is_file():
        raise FileNotFoundError(path)
    return json.loads(path.read_text())


def load_checkpoint(path: Path) -> dict[str, Any]:
    if not path.is_file():
        raise FileNotFoundError(path)
    try:
        payload = torch.load(path, map_location="cpu", weights_only=True)
    except TypeError:
        payload = torch.load(path, map_location="cpu")
    if not isinstance(payload, dict):
        raise ValueError("pilot checkpoint is not a dictionary")
    return payload


def main() -> None:
    args = parse_args()
    stage2 = read_json(args.stage2_audit)
    history = read_json(args.pilot_history)
    checkpoint = load_checkpoint(args.pilot_checkpoint)
    exit_code = int(args.pilot_exit.read_text().strip())
    if not isinstance(stage2, dict):
        raise ValueError("Stage-2 audit must be a JSON object")
    required_stage2 = {
        "candidate_gain",
        "fixed_rank_blend_gain",
        "promote_candidate",
        "promote_fixed_rank_blend",
        "minimum_preregistered_gain",
    }
    if missing := required_stage2.difference(stage2):
        raise ValueError(f"Stage-2 audit is missing {sorted(missing)}")
    if not isinstance(history, list) or not history:
        raise ValueError("system-pilot history must contain at least one epoch")
    final_epoch = history[-1]
    if not isinstance(final_epoch, dict):
        raise ValueError("system-pilot epoch record must be an object")
    train_loss = float(final_epoch["train_loss"])
    if not math.isfinite(train_loss):
        raise ValueError("system-pilot loss is not finite")
    saved_args = checkpoint.get("args")
    if not isinstance(saved_args, dict):
        raise ValueError("pilot checkpoint has no saved argument contract")
    if saved_args.get("architecture") != "copas":
        raise ValueError("pilot checkpoint is not the adaptive co-plane family")
    if int(saved_args.get("limit_studies", 0)) <= 0:
        raise ValueError("this gate accepts only a limited systems pilot")
    lora_modules = checkpoint.get("backbone_lora_modules")
    if not isinstance(lora_modules, list) or not lora_modules:
        raise ValueError("pilot checkpoint has no certified LoRA injection list")
    trainable = int(checkpoint["trainable_parameters"])
    total = int(checkpoint["total_parameters"])
    if not 0 < trainable < total:
        raise ValueError("pilot trainable-parameter footprint is invalid")
    system_pass = exit_code == 0
    stage2_supports_detail = bool(
        stage2["promote_candidate"] or stage2["promote_fixed_rank_blend"]
    )
    recommendation = (
        "retain high-resolution patch detail in the adaptive configuration review"
        if stage2_supports_detail
        else "reconsider resolution and local-detail budget before full adaptive CV"
    )
    artifact = {
        "schema_version": 1,
        "contract": "adaptive_manual_review_gate_v1",
        "state": "manual_review_required",
        "full_cv_authorized": False,
        "reason": "a limited systems pilot cannot promote a leaderboard family",
        "stage2": {
            "candidate_gain": float(stage2["candidate_gain"]),
            "fixed_rank_blend_gain": float(stage2["fixed_rank_blend_gain"]),
            "minimum_preregistered_gain": float(stage2["minimum_preregistered_gain"]),
            "supports_high_resolution_detail": stage2_supports_detail,
            "source": str(args.stage2_audit),
        },
        "system_pilot": {
            "passed": system_pass,
            "exit_code": exit_code,
            "final_train_loss": train_loss,
            "reported_macro_auc": final_epoch.get("macro_auc"),
            "train_seconds": final_epoch.get("train_seconds"),
            "evaluation_seconds": final_epoch.get("evaluation_seconds"),
            "peak_cuda_gib": final_epoch.get("peak_cuda_gib"),
            "trainable_parameters": trainable,
            "total_parameters": total,
            "lora_module_count": len(lora_modules),
            "source": str(args.pilot_history),
        },
        "recommendation": recommendation,
        "required_next_action": (
            "inspect this packet, choose one frozen configuration, then create a separate "
            "promotion audit before launching five-fold CV"
        ),
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(artifact, indent=2, allow_nan=False) + "\n")
    print(json.dumps(artifact, indent=2, allow_nan=False))


if __name__ == "__main__":
    main()
