#!/usr/bin/env python3
"""CPU checks for the adaptive co-plane model and DINO LoRA injection."""

from __future__ import annotations

import torch
from torch import nn

try:
    from .raw_mil import (
        AdaptiveCoPlaneMILModel,
        LoRAConv2d,
        LoRALinear,
        collate_raw_studies,
        inject_dino_lora,
    )
except ImportError:
    from raw_mil import (
        AdaptiveCoPlaneMILModel,
        LoRAConv2d,
        LoRALinear,
        collate_raw_studies,
        inject_dino_lora,
    )


class TinyBackbone(nn.Module):
    output_dim = 8

    def forward(self, pixels: torch.Tensor) -> torch.Tensor:
        value = pixels.mean(dim=(2, 3))
        return torch.cat([value, value[:, :2], value], dim=1)[:, : self.output_dim]


def item(uid: str, series_lengths: list[int], planes: list[int]) -> dict[str, object]:
    if len(series_lengths) != len(planes):
        raise ValueError("one plane is required per synthetic series")
    series = torch.cat(
        [torch.full((length,), index) for index, length in enumerate(series_lengths)]
    ).long()
    plane = torch.cat(
        [torch.full((length,), planes[index]) for index, length in enumerate(series_lengths)]
    ).long()
    slices = int(series.numel())
    return {
        "uid": uid,
        "pixels": torch.rand(slices, 3, 12, 12),
        "plane": plane,
        "fluid": torch.arange(slices) % 3,
        "fatsat": (torch.arange(slices) + 1) % 3,
        "position": torch.cat(
            [torch.arange(length).float() for length in series_lengths]
        ),
        "series_index": series,
        "labels": torch.zeros(12),
        "label_mask": torch.ones(12, dtype=torch.bool),
        "confidence": torch.ones(12),
        "gold_mask": torch.ones(12, dtype=torch.bool),
    }


class FakeAttentionInner(nn.Module):
    def __init__(self) -> None:
        super().__init__()
        self.query = nn.Linear(4, 4)
        self.key = nn.Linear(4, 4)
        self.value = nn.Linear(4, 4)


class FakeAttentionOutput(nn.Module):
    def __init__(self) -> None:
        super().__init__()
        self.dense = nn.Linear(4, 4)


class FakeAttention(nn.Module):
    def __init__(self) -> None:
        super().__init__()
        self.attention = FakeAttentionInner()
        self.output = FakeAttentionOutput()


class FakePatch(nn.Module):
    def __init__(self) -> None:
        super().__init__()
        self.projection = nn.Conv2d(3, 4, 2, 2)


class FakeEmbeddings(nn.Module):
    def __init__(self) -> None:
        super().__init__()
        self.patch_embeddings = FakePatch()


class FakeDino(nn.Module):
    def __init__(self) -> None:
        super().__init__()
        self.embeddings = FakeEmbeddings()
        self.attention = FakeAttention()


def check_lora() -> None:
    fake = FakeDino()
    vector = torch.randn(2, 4)
    image = torch.randn(2, 3, 8, 8)
    linear_before = fake.attention.attention.query(vector).detach()
    conv_before = fake.embeddings.patch_embeddings.projection(image).detach()
    names = inject_dino_lora(fake, rank=2, alpha=4.0, dropout=0.0)
    assert len(names) == 5
    assert isinstance(fake.attention.attention.query, LoRALinear)
    assert isinstance(fake.embeddings.patch_embeddings.projection, LoRAConv2d)
    torch.testing.assert_close(fake.attention.attention.query(vector), linear_before)
    torch.testing.assert_close(fake.embeddings.patch_embeddings.projection(image), conv_before)


def main() -> None:
    torch.manual_seed(7)
    batch = collate_raw_studies(
        [item("a", [3, 2, 2], [1, 1, 3]), item("b", [2, 3], [2, 3])]
    )
    model = AdaptiveCoPlaneMILModel(
        TinyBackbone(), 12, hidden_dim=24, dropout=0.0, encoder_batch_size=3, report_dim=10
    ).eval()
    arguments = (
        batch["pixels"],
        batch["plane"],
        batch["fluid"],
        batch["fatsat"],
        batch["position"],
        batch["study_index"],
        batch["series_index"],
        batch["num_studies"],
        batch["num_series"],
    )
    output = model(*arguments, return_aux=True)
    assert isinstance(output, dict)
    assert output["logits"].shape == (2, 12)
    assert output["branch_logits"].shape == (2, 4, 12)
    assert output["branch_mask"].tolist() == [
        [False, True, False, True],
        [False, False, True, True],
    ]
    assert output["report_embedding"].shape == (2, 10)

    permutation = torch.randperm(batch["pixels"].shape[0])
    permuted = [value[permutation] for value in arguments[:7]] + list(arguments[7:])
    permuted_output = model(*permuted, return_aux=True)
    assert isinstance(permuted_output, dict)
    torch.testing.assert_close(output["logits"], permuted_output["logits"], atol=1e-6, rtol=1e-5)
    position_blind = list(arguments)
    position_blind[4] = torch.zeros_like(batch["position"])
    position_blind_output = model(*position_blind)
    assert torch.is_tensor(position_blind_output)
    if torch.allclose(output["logits"], position_blind_output):
        raise AssertionError("physical ALiBi did not affect the synthetic prediction")

    model.train()
    trained = model(*arguments, return_aux=True)
    assert isinstance(trained, dict)
    (trained["logits"].sum() + trained["branch_logits"].sum()).backward()
    assert model.target_query.grad is not None
    assert model.label_fusion.weight.grad is not None
    check_lora()
    print("adaptive co-plane and LoRA smoke tests passed")


if __name__ == "__main__":
    main()
