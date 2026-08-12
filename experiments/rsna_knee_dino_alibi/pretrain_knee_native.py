#!/usr/bin/env python3
"""Pretrain DINO adapters on competition knee MRI without diagnosis labels."""

from __future__ import annotations

import argparse
import json
import math
import time
from pathlib import Path
from typing import Any

import pandas as pd
import torch
from torch.utils.data import DataLoader

try:
    from .external_asset_compliance import DEFAULT_MANIFEST, require_competition_asset
    from .knee_pretrain import KneeNativePretrainer
    from .raw_mil import (
        RawStudyDataset,
        SliceFeatureBackbone,
        build_study_manifest,
        collate_raw_studies,
        normalize_pixels,
    )
    from .train import seed_everything
except ImportError:
    from external_asset_compliance import DEFAULT_MANIFEST, require_competition_asset
    from knee_pretrain import KneeNativePretrainer
    from raw_mil import (
        RawStudyDataset,
        SliceFeatureBackbone,
        build_study_manifest,
        collate_raw_studies,
        normalize_pixels,
    )
    from train import seed_everything


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--data-root", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument(
        "--study-list-csv",
        type=Path,
        help="optional UID/fold table used to keep SSL outside held-out folds",
    )
    parser.add_argument("--fold-column", default="fold")
    parser.add_argument("--exclude-fold", type=int, action="append", default=[])
    parser.add_argument("--model-name", default="facebook/dinov2-base")
    parser.add_argument(
        "--external-asset-identifier",
        default="facebook/dinov2-base",
        help="licensed manifest identifier when --model-name is a local snapshot",
    )
    parser.add_argument("--external-assets-manifest", type=Path, default=DEFAULT_MANIFEST)
    parser.add_argument("--local-files-only", action="store_true")
    parser.add_argument("--image-size", type=int, default=224)
    parser.add_argument("--slices", type=int, default=8)
    parser.add_argument("--crop-mm", type=float, default=160.0)
    parser.add_argument("--max-series-per-plane", type=int, default=1)
    parser.add_argument("--lora-rank", type=int, default=8)
    parser.add_argument("--lora-alpha", type=float, default=16.0)
    parser.add_argument("--lora-dropout", type=float, default=0.05)
    parser.add_argument("--hidden-dim", type=int, default=256)
    parser.add_argument("--common-dim", type=int, default=128)
    parser.add_argument("--alibi-heads", type=int, default=8)
    parser.add_argument("--batch-size", type=int, default=2)
    parser.add_argument("--encoder-batch-size", type=int, default=8)
    parser.add_argument("--workers", type=int, default=4)
    parser.add_argument("--epochs", type=int, default=5)
    parser.add_argument("--limit-studies", type=int, default=0)
    parser.add_argument("--seed", type=int, default=2026)
    parser.add_argument("--backbone-lr", type=float, default=2e-5)
    parser.add_argument("--head-lr", type=float, default=2e-4)
    parser.add_argument("--weight-decay", type=float, default=1e-3)
    parser.add_argument("--mask-fraction", type=float, default=0.35)
    parser.add_argument(
        "--amp-dtype",
        choices=("auto", "bfloat16", "float16"),
        default="auto",
        help="auto prefers bfloat16 on supported GPUs to avoid first-step overflow",
    )
    parser.add_argument("--reconstruction-weight", type=float, default=1.0)
    parser.add_argument("--cross-series-weight", type=float, default=0.25)
    parser.add_argument("--metadata-weight", type=float, default=0.10)
    parser.add_argument("--variance-weight", type=float, default=1.0)
    parser.add_argument("--covariance-weight", type=float, default=0.04)
    parser.add_argument("--device", default="cuda" if torch.cuda.is_available() else "cpu")
    return parser.parse_args()


def augment(pixels: torch.Tensor) -> torch.Tensor:
    """MRI-safe intensity augmentation without geometric relabeling."""

    count = pixels.shape[0]
    gain = 0.85 + 0.30 * torch.rand(count, 1, 1, 1, device=pixels.device)
    bias = 0.06 * (2 * torch.rand(count, 1, 1, 1, device=pixels.device) - 1)
    gamma = 0.80 + 0.40 * torch.rand(count, 1, 1, 1, device=pixels.device)
    noise = 0.015 * torch.randn_like(pixels)
    return ((pixels.clamp_min(1e-5).pow(gamma) * gain + bias) + noise).clamp(0, 1)


def move(batch: dict[str, Any], device: torch.device) -> dict[str, Any]:
    return {
        key: value.to(device, non_blocking=True) if torch.is_tensor(value) else value
        for key, value in batch.items()
    }


def weighted_total(losses: dict[str, torch.Tensor], args: argparse.Namespace) -> torch.Tensor:
    return (
        losses["invariance"]
        + args.variance_weight * losses["variance"]
        + args.covariance_weight * losses["covariance"]
        + args.reconstruction_weight * losses["reconstruction"]
        + args.cross_series_weight * losses["cross_series"]
        + args.metadata_weight * losses["metadata"]
    )


def main() -> None:
    args = parse_args()
    if args.lora_rank < 1:
        raise ValueError("knee-native pretraining requires a positive LoRA rank")
    require_competition_asset(
        args.external_asset_identifier, args.external_assets_manifest
    )
    seed_everything(args.seed)
    torch.set_float32_matmul_precision("high")
    args.output.mkdir(parents=True, exist_ok=True)
    manifest = build_study_manifest(args.data_root / "train_series.csv", args.data_root, "train")
    if args.exclude_fold and args.study_list_csv is None:
        raise ValueError("--exclude-fold requires --study-list-csv")
    if args.study_list_csv is None:
        studies = pd.DataFrame({"StudyInstanceUID": sorted(manifest)})
    else:
        studies = pd.read_csv(args.study_list_csv, dtype={"StudyInstanceUID": str})
        if "StudyInstanceUID" not in studies:
            raise ValueError("study list must contain StudyInstanceUID")
        if studies["StudyInstanceUID"].duplicated().any():
            raise ValueError("study list contains duplicate study identifiers")
        if args.exclude_fold:
            if args.fold_column not in studies:
                raise ValueError(f"study list has no {args.fold_column!r} column")
            studies = studies[
                ~pd.to_numeric(studies[args.fold_column], errors="raise").isin(
                    args.exclude_fold
                )
            ]
        studies = studies[
            studies["StudyInstanceUID"].isin(manifest)
        ][["StudyInstanceUID"]].sort_values("StudyInstanceUID")
        if not len(studies):
            raise ValueError("fold filtering left no studies for pretraining")
    if args.limit_studies:
        studies = studies.head(args.limit_studies)
    dataset = RawStudyDataset(
        studies,
        manifest,
        targets=[],
        image_size=args.image_size,
        slices_per_plane=args.slices,
        crop_mm=args.crop_mm,
        training=True,
        max_series_per_plane=args.max_series_per_plane,
    )
    loader = DataLoader(
        dataset,
        batch_size=args.batch_size,
        shuffle=True,
        num_workers=args.workers,
        pin_memory=torch.cuda.is_available(),
        persistent_workers=args.workers > 0,
        collate_fn=collate_raw_studies,
        drop_last=len(dataset) >= args.batch_size,
    )
    backbone = SliceFeatureBackbone(
        "dinov2",
        args.model_name,
        trainable_blocks=0,
        local_files_only=args.local_files_only,
        pretrained=True,
        checkpoint=None,
        lora_rank=args.lora_rank,
        lora_alpha=args.lora_alpha,
        lora_dropout=args.lora_dropout,
    )
    model = KneeNativePretrainer(
        backbone,
        hidden_dim=args.hidden_dim,
        common_dim=args.common_dim,
        alibi_heads=args.alibi_heads,
    )
    model.encoder_batch_size = args.encoder_batch_size
    device = torch.device(args.device)
    model.to(device)
    optimizer = torch.optim.AdamW(
        model.parameter_groups(args.backbone_lr, args.head_lr),
        weight_decay=args.weight_decay,
    )
    scheduler = torch.optim.lr_scheduler.CosineAnnealingLR(
        optimizer, T_max=max(1, args.epochs * len(loader))
    )
    amp = device.type == "cuda"
    use_bfloat16 = amp and (
        args.amp_dtype == "bfloat16"
        or (args.amp_dtype == "auto" and torch.cuda.is_bf16_supported())
    )
    amp_dtype = torch.bfloat16 if use_bfloat16 else torch.float16
    scaler = torch.amp.GradScaler("cuda", enabled=amp and not use_bfloat16)
    history = []
    best = math.inf
    for epoch in range(1, args.epochs + 1):
        started = time.monotonic()
        model.train()
        sums: dict[str, float] = {}
        for batch in loader:
            batch = move(batch, device)
            first = augment(batch["pixels"])
            second = augment(batch["pixels"])
            optimizer.zero_grad(set_to_none=True)
            with torch.autocast(device_type=device.type, dtype=amp_dtype, enabled=amp):
                losses = model(
                    normalize_pixels(first),
                    normalize_pixels(second),
                    batch["plane"],
                    batch["fluid"],
                    batch["fatsat"],
                    batch["position"],
                    batch["series_index"],
                    batch["series_study_index"],
                    batch["num_series"],
                    args.mask_fraction,
                )
                total = weighted_total(losses, args)
            scaler.scale(total).backward()
            scaler.unscale_(optimizer)
            torch.nn.utils.clip_grad_norm_(model.parameters(), 1.0)
            scale_before = scaler.get_scale()
            scaler.step(optimizer)
            scaler.update()
            step_skipped = scaler.is_enabled() and scaler.get_scale() < scale_before
            if not step_skipped:
                scheduler.step()
            for name, value in {"total": total, **losses}.items():
                sums[name] = sums.get(name, 0.0) + float(value.detach())
        record = {
            "epoch": epoch,
            **{name: value / max(1, len(loader)) for name, value in sums.items()},
            "seconds": time.monotonic() - started,
            "peak_cuda_gib": (
                torch.cuda.max_memory_allocated(device) / 2**30 if amp else 0.0
            ),
        }
        if not math.isfinite(record["total"]):
            raise RuntimeError("non-finite knee-native pretraining loss")
        history.append(record)
        print(json.dumps(record), flush=True)
        if record["total"] < best:
            best = record["total"]
            torch.save(
                {
                    "state_dict": backbone.model.state_dict(),
                    "contract": "competition_only_knee_native_dino_lora_v1",
                    "model_name": args.model_name,
                    "lora_modules": list(backbone.lora_modules),
                    "args": {
                        key: str(value) if isinstance(value, Path) else value
                        for key, value in vars(args).items()
                    },
                    "pretrain_loss": best,
                    "pretraining_studies": len(studies),
                    "excluded_folds": args.exclude_fold,
                },
                args.output / "knee_native_backbone.pt",
            )
            torch.save(
                {"model": model.state_dict(), "epoch": epoch, "pretrain_loss": best},
                args.output / "knee_native_pretrainer.pt",
            )
    (args.output / "history.json").write_text(
        json.dumps(history, indent=2, allow_nan=False) + "\n"
    )
    print(f"best pretraining loss={best:.6f}", flush=True)


if __name__ == "__main__":
    main()
