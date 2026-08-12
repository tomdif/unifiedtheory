"""Competition-native self-supervision for multi-sequence knee MRI.

The representation is trained without diagnosis labels.  It combines four
signals that are available in the competition images themselves:

* invariance to safe intensity perturbations of the same slice;
* masked reconstruction from physically ordered neighboring slices;
* cross-series agreement for different acquisitions of the same knee;
* explicit retention of acquisition plane/contrast metadata.

The last two objectives prevent the common representation from becoming
either sequence-specific noise or an indiscriminate invariant collapse.
"""

from __future__ import annotations

from typing import Any

import torch
from torch import Tensor, nn
import torch.nn.functional as F

try:
    from .raw_mil import PhysicalAlibiEncoder, SliceFeatureBackbone
except ImportError:
    from raw_mil import PhysicalAlibiEncoder, SliceFeatureBackbone


def off_diagonal(matrix: Tensor) -> Tensor:
    if matrix.ndim != 2 or matrix.shape[0] != matrix.shape[1]:
        raise ValueError("off_diagonal expects a square matrix")
    size = matrix.shape[0]
    if size < 2:
        return matrix.new_empty(0)
    return matrix.flatten()[:-1].view(size - 1, size + 1)[:, 1:].flatten()


def vicreg_loss(first: Tensor, second: Tensor) -> dict[str, Tensor]:
    """VICReg terms over slice representations, with no negative mining."""

    if first.shape != second.shape or first.ndim != 2:
        raise ValueError("VICReg views must be equal two-dimensional tensors")
    invariance = F.mse_loss(first, second)
    if first.shape[0] < 2:
        zero = invariance * 0
        return {"invariance": invariance, "variance": zero, "covariance": zero}
    centered_first = first - first.mean(dim=0)
    centered_second = second - second.mean(dim=0)
    std_first = torch.sqrt(centered_first.var(dim=0, unbiased=False) + 1e-4)
    std_second = torch.sqrt(centered_second.var(dim=0, unbiased=False) + 1e-4)
    variance = (F.relu(1 - std_first).mean() + F.relu(1 - std_second).mean()) / 2
    denominator = max(1, first.shape[0] - 1)
    cov_first = centered_first.T @ centered_first / denominator
    cov_second = centered_second.T @ centered_second / denominator
    covariance = (
        off_diagonal(cov_first).square().mean()
        + off_diagonal(cov_second).square().mean()
    ) / 2
    return {
        "invariance": invariance,
        "variance": variance,
        "covariance": covariance,
    }


def supervised_series_contrastive(
    representations: Tensor,
    study_index: Tensor,
    temperature: float = 0.10,
) -> Tensor:
    """Pull acquisitions of one knee together against other knees in-batch."""

    if representations.ndim != 2 or len(representations) != len(study_index):
        raise ValueError("series representations and study indices are incompatible")
    if representations.shape[0] < 2 or torch.unique(study_index).numel() < 2:
        return representations.sum() * 0
    normalized = F.normalize(representations, dim=-1)
    logits = normalized @ normalized.T / temperature
    identity = torch.eye(len(representations), dtype=torch.bool, device=logits.device)
    positive = study_index[:, None].eq(study_index[None, :]) & ~identity
    usable = positive.any(dim=1)
    if not bool(usable.any()):
        return representations.sum() * 0
    logits = logits.masked_fill(identity, -torch.inf)
    log_probability = logits - torch.logsumexp(logits, dim=1, keepdim=True)
    per_anchor = -(log_probability.masked_fill(~positive, 0).sum(dim=1))
    per_anchor = per_anchor / positive.sum(dim=1).clamp_min(1)
    return per_anchor[usable].mean()


class KneeNativePretrainer(nn.Module):
    """Lightweight SSL heads around the trainable portion of a slice encoder."""

    def __init__(
        self,
        backbone: SliceFeatureBackbone,
        hidden_dim: int = 256,
        common_dim: int = 128,
        alibi_heads: int = 8,
        dropout: float = 0.1,
    ) -> None:
        super().__init__()
        if hidden_dim < 8 or common_dim < 8:
            raise ValueError("pretraining dimensions must be at least 8")
        self.backbone = backbone
        self.hidden_dim = hidden_dim
        self.encoder_batch_size = 8
        self.slice_projection = nn.Sequential(
            nn.LayerNorm(backbone.output_dim),
            nn.Linear(backbone.output_dim, hidden_dim),
            nn.GELU(),
        )
        self.common_projection = nn.Sequential(
            nn.LayerNorm(hidden_dim),
            nn.Linear(hidden_dim, common_dim),
        )
        self.context = PhysicalAlibiEncoder(hidden_dim, alibi_heads, dropout)
        self.mask_token = nn.Parameter(torch.zeros(hidden_dim))
        self.reconstruction = nn.Sequential(
            nn.LayerNorm(hidden_dim),
            nn.Linear(hidden_dim, backbone.output_dim),
        )
        self.plane_head = nn.Linear(hidden_dim, 4)
        self.fluid_head = nn.Linear(hidden_dim, 3)
        self.fatsat_head = nn.Linear(hidden_dim, 3)
        nn.init.normal_(self.mask_token, std=hidden_dim**-0.5)

    def encode(self, pixels: Tensor) -> Tensor:
        chunks = []
        for start in range(0, pixels.shape[0], self.encoder_batch_size):
            chunks.append(self.backbone(pixels[start : start + self.encoder_batch_size]))
        return torch.cat(chunks)

    def forward(
        self,
        first_view: Tensor,
        second_view: Tensor,
        plane: Tensor,
        fluid: Tensor,
        fatsat: Tensor,
        position: Tensor,
        series_index: Tensor,
        series_study_index: Tensor,
        num_series: int,
        mask_fraction: float = 0.35,
    ) -> dict[str, Tensor]:
        if not 0 < mask_fraction < 1:
            raise ValueError("mask_fraction must be strictly between zero and one")
        raw_first = self.encode(first_view)
        raw_second = self.encode(second_view)
        hidden_first = self.slice_projection(raw_first)
        hidden_second = self.slice_projection(raw_second)
        common_first = self.common_projection(hidden_first)
        common_second = self.common_projection(hidden_second)
        losses = vicreg_loss(common_first, common_second)

        reconstructed: list[Tensor] = []
        reconstruction_target: list[Tensor] = []
        series_common: list[Tensor] = []
        for index in range(num_series):
            selected = series_index == index
            if not bool(selected.any()):
                raise ValueError("every packed series must contain slices")
            values = hidden_first[selected]
            count = values.shape[0]
            mask = torch.rand(count, device=values.device) < mask_fraction
            if not bool(mask.any()):
                mask[torch.randint(count, (1,), device=values.device)] = True
            masked = torch.where(mask[:, None], self.mask_token[None], values)
            contextual = self.context(masked, position[selected])
            reconstructed.append(self.reconstruction(contextual[mask]))
            reconstruction_target.append(raw_first[selected][mask].detach())
            series_common.append(common_first[selected].mean(dim=0))
        losses["reconstruction"] = F.smooth_l1_loss(
            torch.cat(reconstructed), torch.cat(reconstruction_target)
        )
        losses["cross_series"] = supervised_series_contrastive(
            torch.stack(series_common), series_study_index
        )
        losses["metadata"] = (
            F.cross_entropy(self.plane_head(hidden_first), plane)
            + F.cross_entropy(self.fluid_head(hidden_first), fluid)
            + F.cross_entropy(self.fatsat_head(hidden_first), fatsat)
        ) / 3
        return losses

    def parameter_groups(self, backbone_lr: float, head_lr: float) -> list[dict[str, Any]]:
        backbone = [parameter for parameter in self.backbone.parameters() if parameter.requires_grad]
        backbone_ids = {id(parameter) for parameter in backbone}
        head = [
            parameter
            for parameter in self.parameters()
            if parameter.requires_grad and id(parameter) not in backbone_ids
        ]
        groups = []
        if backbone:
            groups.append({"params": backbone, "lr": backbone_lr})
        if head:
            groups.append({"params": head, "lr": head_lr})
        return groups
