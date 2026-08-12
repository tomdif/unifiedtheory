#!/usr/bin/env python3
"""CPU regression checks for competition-native knee pretraining."""

from __future__ import annotations

import torch
from torch import nn

try:
    from .knee_pretrain import KneeNativePretrainer, supervised_series_contrastive, vicreg_loss
except ImportError:
    from knee_pretrain import KneeNativePretrainer, supervised_series_contrastive, vicreg_loss


class TinyBackbone(nn.Module):
    output_dim = 12

    def forward(self, pixels: torch.Tensor) -> torch.Tensor:
        mean = pixels.mean(dim=(2, 3))
        spread = pixels.std(dim=(2, 3))
        return torch.cat([mean, spread, mean + spread, mean - spread], dim=1)


def main() -> None:
    torch.manual_seed(31)
    first = torch.randn(24, 16)
    second = first + 0.05 * torch.randn_like(first)
    vicreg = vicreg_loss(first, second)
    if not all(torch.isfinite(value) for value in vicreg.values()):
        raise AssertionError("VICReg emitted a non-finite term")

    series = torch.tensor([[1.0, 0.0], [0.9, 0.1], [-1.0, 0.0], [-0.9, 0.1]])
    studies = torch.tensor([0, 0, 1, 1])
    good = supervised_series_contrastive(series, studies)
    bad = supervised_series_contrastive(series[[0, 2, 1, 3]], studies)
    if not good < bad:
        raise AssertionError("cross-series contrastive loss did not reward matching knees")

    slices = 12
    pixels = torch.rand(slices, 3, 10, 10)
    model = KneeNativePretrainer(
        TinyBackbone(), hidden_dim=16, common_dim=8, alibi_heads=4, dropout=0.0
    )
    losses = model(
        pixels,
        (pixels + 0.01 * torch.randn_like(pixels)).clamp(0, 1),
        plane=torch.tensor([1] * 4 + [2] * 4 + [3] * 4),
        fluid=torch.arange(slices) % 3,
        fatsat=(torch.arange(slices) + 1) % 3,
        position=torch.tensor([0.0, 1.0, 2.0, 3.0] * 3),
        series_index=torch.tensor([0] * 4 + [1] * 4 + [2] * 4),
        series_study_index=torch.tensor([0, 0, 1]),
        num_series=3,
        mask_fraction=0.4,
    )
    total = sum(losses.values())
    total.backward()
    if not torch.isfinite(total) or model.mask_token.grad is None:
        raise AssertionError("pretraining graph is invalid")
    print("knee-native pretraining smoke tests passed")


if __name__ == "__main__":
    main()
