#!/usr/bin/env python3
"""Round-trip an adaptive DINO-LoRA checkpoint through offline inference."""

from __future__ import annotations

from pathlib import Path
from tempfile import TemporaryDirectory

import torch
from transformers import Dinov2Config, Dinov2Model

try:
    from .infer_raw_mil import build_model
    from .raw_mil import AdaptiveCoPlaneMILModel, SliceFeatureBackbone
except ImportError:
    from infer_raw_mil import build_model
    from raw_mil import AdaptiveCoPlaneMILModel, SliceFeatureBackbone


def main() -> None:
    with TemporaryDirectory() as directory:
        path = Path(directory)
        Dinov2Model(
            Dinov2Config(
                image_size=32,
                patch_size=8,
                num_channels=3,
                hidden_size=32,
                num_hidden_layers=1,
                num_attention_heads=4,
                intermediate_size=64,
            )
        ).save_pretrained(path)
        backbone = SliceFeatureBackbone(
            "dinov2", str(path), 0, True, True, None, 2, 4.0, 0.0
        )
        original = AdaptiveCoPlaneMILModel(
            backbone,
            12,
            hidden_dim=24,
            dropout=0.0,
            encoder_batch_size=8,
            alibi_heads=6,
        )
        payload = {
            "model": original.state_dict(),
            "args": {
                "backbone": "dinov2",
                "model_name": str(path),
                "trainable_blocks": 0,
                "lora_rank": 2,
                "lora_alpha": 4.0,
                "lora_dropout": 0.0,
                "architecture": "copas",
                "hidden_dim": 24,
                "alibi_heads": 6,
                "report_dim": 0,
                "no_pretrained": False,
                "external_asset_identifier": "facebook/dinov2-base",
            },
        }
        restored = build_model(payload, str(path), 8)
        if set(original.state_dict()) != set(restored.state_dict()):
            raise AssertionError("checkpoint reconstruction changed parameter names")
        for key, value in original.state_dict().items():
            if not value.equal(restored.state_dict()[key]):
                raise AssertionError(f"checkpoint reconstruction changed {key}")
        restored.eval()
        with torch.inference_mode():
            logits = restored(
                torch.rand(2, 3, 32, 32),
                torch.ones(2, dtype=torch.long),
                torch.ones(2, dtype=torch.long),
                torch.ones(2, dtype=torch.long),
                torch.tensor([-0.5, 0.5]),
                torch.zeros(2, dtype=torch.long),
                torch.zeros(2, dtype=torch.long),
                1,
                1,
            )
        if logits.shape != (1, 12) or not torch.isfinite(logits).all():
            raise AssertionError("restored adaptive DINO checkpoint failed a real forward pass")
    print("adaptive checkpoint reconstruction passed")


if __name__ == "__main__":
    main()
