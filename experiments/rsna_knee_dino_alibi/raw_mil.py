"""Raw-DICOM, high-resolution multiple-instance models for knee MRI.

The cached-feature experiments establish a cheap baseline. This module is the
deliberately different family used for the expensive stage: one selected
series per anatomical plane, stratified physical slices, trainable image
features, and target-wise pooling over slices.
"""

from __future__ import annotations

from dataclasses import dataclass
from functools import lru_cache
from pathlib import Path
from typing import Any, Sequence

import numpy as np
import pandas as pd
import torch
from torch import Tensor, nn
import torch.nn.functional as F
from torch.utils.data import Dataset

try:
    from .constants import PLANE_TO_ID, TARGETS, TARGET_FAMILIES
    from .dino_adapter import freeze_except_last_blocks
    from .extract_features import (
        _crop_physical,
        _laterality,
        _normal_and_position,
        _pixel_array,
        _plane_id,
        _tristate,
    )
except ImportError:
    from constants import PLANE_TO_ID, TARGETS, TARGET_FAMILIES
    from dino_adapter import freeze_except_last_blocks
    from extract_features import (
        _crop_physical,
        _laterality,
        _normal_and_position,
        _pixel_array,
        _plane_id,
        _tristate,
    )


@dataclass(frozen=True)
class SeriesRecord:
    uid: str
    plane: int
    fluid: int
    fatsat: int
    directory: str


@lru_cache(maxsize=16384)
def _directory_paths(directory: str) -> tuple[str, ...]:
    paths = tuple(str(path) for path in sorted(Path(directory).glob("*.dcm")))
    if not paths:
        raise FileNotFoundError(f"series directory contains no DICOMs: {directory}")
    return paths


def build_study_manifest(
    series_csv: Path, data_root: Path, split: str = "train"
) -> dict[str, tuple[SeriesRecord, ...]]:
    table = pd.read_csv(series_csv)
    required = {"StudyInstanceUID", "SeriesInstanceUID", "Anatomical_Plane"}
    if missing := required.difference(table.columns):
        raise ValueError(f"series table is missing columns: {sorted(missing)}")
    studies: dict[str, tuple[SeriesRecord, ...]] = {}
    for study_uid, rows in table.groupby("StudyInstanceUID", sort=True):
        records: list[SeriesRecord] = []
        for _, row in rows.iterrows():
            series_uid = str(row["SeriesInstanceUID"])
            directory = data_root / f"{split}_series" / str(study_uid) / series_uid
            records.append(
                SeriesRecord(
                    uid=series_uid,
                    plane=_plane_id(row.get("Anatomical_Plane")),
                    fluid=_tristate(row.get("Fluid_Sensitive")),
                    fatsat=_tristate(row.get("Fat_Suppression")),
                    directory=str(directory),
                )
            )
        if records:
            studies[str(study_uid)] = tuple(records)
    return studies


@lru_cache(maxsize=8192)
def _ordered_headers(directory: str) -> tuple[tuple[str, float], ...]:
    import pydicom

    rows: list[tuple[float, int, str]] = []
    physical = True
    for ordinal, path in enumerate(_directory_paths(directory)):
        ds = pydicom.dcmread(path, stop_before_pixels=True, force=True)
        _, position = _normal_and_position(ds)
        if position is None:
            physical = False
            try:
                position = float(ds.InstanceNumber)
            except (AttributeError, TypeError, ValueError):
                position = float(ordinal)
        rows.append((float(position), ordinal, path))
    rows.sort(key=lambda row: (row[0], row[1]))
    if not physical:
        return tuple((path, float(index)) for index, (_, _, path) in enumerate(rows))
    return tuple((path, position) for position, _, path in rows)


def _stratified_indices(length: int, count: int, training: bool) -> np.ndarray:
    if length <= count:
        return np.arange(length, dtype=np.int64)
    if not training:
        return np.unique(np.rint(np.linspace(0, length - 1, count)).astype(np.int64))
    edges = np.linspace(0, length, count + 1)
    indices = []
    for left, right in zip(edges[:-1], edges[1:]):
        lo = int(np.floor(left))
        hi = max(lo + 1, int(np.ceil(right)))
        indices.append(int(torch.randint(lo, min(hi, length), (1,)).item()))
    return np.asarray(indices, dtype=np.int64)


def _resize(array: np.ndarray, image_size: int) -> Tensor:
    tensor = torch.from_numpy(np.ascontiguousarray(array)).float()[None, None]
    return F.interpolate(
        tensor, size=(image_size, image_size), mode="bilinear", align_corners=False
    )[0, 0]


def _position_quanta(positions: Tensor) -> Tensor:
    """Center physical positions and express distances in slice spacings."""

    if positions.numel() < 2:
        return torch.zeros_like(positions)
    differences = (positions[1:] - positions[:-1]).abs()
    usable = differences[torch.isfinite(differences) & (differences > 1e-6)]
    spacing = usable.median() if usable.numel() else positions.new_tensor(1.0)
    return (positions - positions.median()) / spacing.clamp_min(1e-6)


def load_series_tensor(
    record: SeriesRecord,
    slices: int,
    crop_mm: float,
    image_size: int,
    training: bool,
) -> tuple[Tensor, Tensor]:
    import pydicom

    ordered = _ordered_headers(record.directory)
    centers = _stratified_indices(len(ordered), slices, training)
    needed = sorted(
        {
            max(0, min(len(ordered) - 1, int(index) + offset))
            for index in centers
            for offset in (-1, 0, 1)
        }
    )
    decoded: dict[int, tuple[Any, np.ndarray]] = {}
    for index in needed:
        try:
            ds = pydicom.dcmread(ordered[index][0], force=True)
            decoded[index] = (ds, _crop_physical(_pixel_array(ds), ds, crop_mm))
        except Exception as error:
            print(
                f"warning: skipping unreadable DICOM {ordered[index][0]}: "
                f"{type(error).__name__}: {error}",
                flush=True,
            )
    if not decoded:
        raise RuntimeError(f"all selected frames are unreadable in {record.directory}")
    readable = np.asarray(sorted(decoded), dtype=np.int64)

    def nearest(index: int) -> int:
        return int(readable[np.abs(readable - index).argmin()])

    centers = np.asarray([nearest(int(index)) for index in centers], dtype=np.int64)
    arrays = [value[1] for value in decoded.values()]
    low = float(np.median([np.percentile(array, 1) for array in arrays]))
    high = float(np.median([np.percentile(array, 99) for array in arrays]))
    if not np.isfinite(high - low) or high - low < 1e-6:
        low = float(min(array.min() for array in arrays))
        high = float(max(array.max() for array in arrays))
    scale = max(high - low, 1e-6)

    def normalized(index: int) -> Tensor:
        array = np.clip((decoded[index][1] - low) / scale, 0.0, 1.0)
        return _resize(array, image_size)

    images = []
    for center in centers:
        triplet = [
            normalized(nearest(max(0, int(center) - 1))),
            normalized(int(center)),
            normalized(nearest(min(len(ordered) - 1, int(center) + 1))),
        ]
        images.append(torch.stack(triplet))
    pixels = torch.stack(images)
    positions = torch.tensor([ordered[int(index)][1] for index in centers], dtype=torch.float32)

    first_ds = decoded[int(centers[0])][0]
    if _laterality(first_ds) == "R":
        if record.plane in {PLANE_TO_ID["coronal"], PLANE_TO_ID["axial"]}:
            pixels = pixels.flip(-1)
        elif record.plane == PLANE_TO_ID["sagittal"]:
            pixels = pixels.flip(0)
            positions = positions.flip(0)
    if training:
        gain = 0.9 + 0.2 * torch.rand(1)
        bias = 0.04 * (2 * torch.rand(1) - 1)
        pixels = (pixels * gain + bias).clamp(0, 1)
    return pixels, positions


class RawStudyDataset(Dataset[dict[str, Any]]):
    """Decode one series per available plane without creating a pixel cache."""

    def __init__(
        self,
        frame: pd.DataFrame,
        manifest: dict[str, tuple[SeriesRecord, ...]],
        targets: Sequence[str],
        image_size: int,
        slices_per_plane: int,
        crop_mm: float,
        training: bool,
        max_series_per_plane: int = 1,
        report_embeddings: dict[str, Tensor] | None = None,
    ) -> None:
        self.frame = frame.reset_index(drop=True).copy()
        self.manifest = manifest
        self.targets = list(targets)
        self.image_size = image_size
        self.slices_per_plane = slices_per_plane
        self.crop_mm = crop_mm
        self.training = training
        if max_series_per_plane < 1:
            raise ValueError("max_series_per_plane must be positive")
        self.max_series_per_plane = max_series_per_plane
        self.report_embeddings = report_embeddings
        missing = [uid for uid in self.frame["StudyInstanceUID"].astype(str) if uid not in manifest]
        if missing:
            raise ValueError(f"{len(missing)} labeled studies have no readable series manifest")

    def __len__(self) -> int:
        return len(self.frame)

    def _choose_series(self, uid: str) -> list[SeriesRecord]:
        by_plane: dict[int, list[SeriesRecord]] = {}
        for record in self.manifest[uid]:
            by_plane.setdefault(record.plane, []).append(record)
        selected = []
        for plane in sorted(by_plane):
            candidates = sorted(
                by_plane[plane],
                key=lambda record: (
                    record.fluid + record.fatsat,
                    len(_directory_paths(record.directory)),
                    record.uid,
                ),
                reverse=True,
            )
            count = min(self.max_series_per_plane, len(candidates))
            if self.training and len(candidates) > count:
                extra = torch.randperm(len(candidates) - 1)[: count - 1].tolist()
                selected.extend(
                    [candidates[0], *[candidates[1 + index] for index in extra]]
                )
            else:
                selected.extend(candidates[:count])
        return selected

    def __getitem__(self, index: int) -> dict[str, Any]:
        row = self.frame.iloc[index]
        uid = str(row["StudyInstanceUID"])
        pixels: list[Tensor] = []
        planes: list[Tensor] = []
        fluids: list[Tensor] = []
        fatsats: list[Tensor] = []
        positions: list[Tensor] = []
        series_indices: list[Tensor] = []
        for series_index, record in enumerate(self._choose_series(uid)):
            images, physical_positions = load_series_tensor(
                record,
                self.slices_per_plane,
                self.crop_mm,
                self.image_size,
                self.training,
            )
            pixels.append(images)
            planes.append(torch.full((images.shape[0],), record.plane, dtype=torch.long))
            fluids.append(torch.full((images.shape[0],), record.fluid, dtype=torch.long))
            fatsats.append(torch.full((images.shape[0],), record.fatsat, dtype=torch.long))
            positions.append(_position_quanta(physical_positions))
            series_indices.append(
                torch.full((images.shape[0],), series_index, dtype=torch.long)
            )
        labels = torch.tensor(
            [float(row[target]) if pd.notna(row[target]) else 0.0 for target in self.targets],
            dtype=torch.float32,
        )
        mask = torch.tensor([pd.notna(row[target]) for target in self.targets], dtype=torch.bool)
        confidence = torch.tensor(
            [float(row.get(f"{target}__conf", 1.0)) for target in self.targets], dtype=torch.float32
        )
        gold = torch.tensor(
            [bool(row.get(f"{target}__gold", pd.notna(row[target]))) for target in self.targets],
            dtype=torch.bool,
        )
        item = {
            "uid": uid,
            "pixels": torch.cat(pixels),
            "plane": torch.cat(planes),
            "fluid": torch.cat(fluids),
            "fatsat": torch.cat(fatsats),
            "position": torch.cat(positions),
            "series_index": torch.cat(series_indices),
            "labels": labels,
            "label_mask": mask,
            "confidence": confidence,
            "gold_mask": gold,
        }
        if self.report_embeddings is not None:
            embedding = self.report_embeddings.get(uid)
            if embedding is None:
                raise ValueError(f"missing report embedding for {uid}")
            item["report_embedding"] = embedding.float()
        return item


def collate_raw_studies(items: Sequence[dict[str, Any]]) -> dict[str, Any]:
    study_index = []
    series_index = []
    series_study_index = []
    series_offset = 0
    for index, item in enumerate(items):
        study_index.append(torch.full((item["pixels"].shape[0],), index, dtype=torch.long))
        local_series = item.get("series_index")
        if local_series is None:
            local_series = torch.zeros(item["pixels"].shape[0], dtype=torch.long)
        local_series = torch.as_tensor(local_series, dtype=torch.long)
        if local_series.numel() != item["pixels"].shape[0]:
            raise ValueError("series_index must contain one entry per slice")
        count = int(local_series.max().item()) + 1 if local_series.numel() else 0
        series_index.append(local_series + series_offset)
        series_study_index.extend([index] * count)
        series_offset += count
    batch = {
        "uid": [item["uid"] for item in items],
        "pixels": torch.cat([item["pixels"] for item in items]),
        "plane": torch.cat([item["plane"] for item in items]),
        "fluid": torch.cat([item["fluid"] for item in items]),
        "fatsat": torch.cat([item["fatsat"] for item in items]),
        "position": torch.cat(
            [
                torch.as_tensor(
                    item.get("position", torch.zeros(item["pixels"].shape[0])),
                    dtype=torch.float32,
                )
                for item in items
            ]
        ),
        "study_index": torch.cat(study_index),
        "series_index": torch.cat(series_index),
        "series_study_index": torch.tensor(series_study_index, dtype=torch.long),
        "num_series": series_offset,
        "num_studies": len(items),
        "labels": torch.stack([item["labels"] for item in items]),
        "label_mask": torch.stack([item["label_mask"] for item in items]),
        "confidence": torch.stack([item["confidence"] for item in items]),
        "gold_mask": torch.stack([item["gold_mask"] for item in items]),
    }
    if all("report_embedding" in item for item in items):
        batch["report_embedding"] = torch.stack(
            [item["report_embedding"] for item in items]
        )
    return batch


class LoRALinear(nn.Module):
    """A frozen linear layer with a trainable low-rank residual."""

    def __init__(
        self, base: nn.Linear, rank: int, alpha: float, dropout: float = 0.0
    ) -> None:
        super().__init__()
        if rank < 1:
            raise ValueError("LoRA rank must be positive")
        self.base = base
        for parameter in self.base.parameters():
            parameter.requires_grad = False
        self.down = nn.Linear(base.in_features, rank, bias=False)
        self.up = nn.Linear(rank, base.out_features, bias=False)
        self.dropout = nn.Dropout(dropout)
        self.scale = float(alpha) / rank
        nn.init.kaiming_uniform_(self.down.weight, a=np.sqrt(5))
        nn.init.zeros_(self.up.weight)

    def forward(self, inputs: Tensor) -> Tensor:
        return self.base(inputs) + self.up(self.down(self.dropout(inputs))) * self.scale


class LoRAConv2d(nn.Module):
    """Low-rank residual for a frozen 2-D patch-embedding convolution."""

    def __init__(
        self, base: nn.Conv2d, rank: int, alpha: float, dropout: float = 0.0
    ) -> None:
        super().__init__()
        if rank < 1:
            raise ValueError("LoRA rank must be positive")
        self.base = base
        for parameter in self.base.parameters():
            parameter.requires_grad = False
        self.down = nn.Conv2d(
            base.in_channels,
            rank,
            kernel_size=base.kernel_size,
            stride=base.stride,
            padding=base.padding,
            dilation=base.dilation,
            groups=1,
            bias=False,
        )
        self.up = nn.Conv2d(rank, base.out_channels, kernel_size=1, bias=False)
        self.dropout = nn.Dropout2d(dropout)
        self.scale = float(alpha) / rank
        nn.init.kaiming_uniform_(self.down.weight, a=np.sqrt(5))
        nn.init.zeros_(self.up.weight)

    @property
    def weight(self) -> nn.Parameter:
        """Expose the frozen base weight for transparent Conv2d consumers."""

        return self.base.weight

    @property
    def bias(self) -> nn.Parameter | None:
        return self.base.bias

    @property
    def in_channels(self) -> int:
        return self.base.in_channels

    @property
    def out_channels(self) -> int:
        return self.base.out_channels

    @property
    def kernel_size(self) -> tuple[int, int]:
        return self.base.kernel_size

    @property
    def stride(self) -> tuple[int, int]:
        return self.base.stride

    @property
    def padding(self) -> tuple[int, int]:
        return self.base.padding

    @property
    def dilation(self) -> tuple[int, int]:
        return self.base.dilation

    @property
    def groups(self) -> int:
        return self.base.groups

    def forward(self, inputs: Tensor) -> Tensor:
        return self.base(inputs) + self.up(self.down(self.dropout(inputs))) * self.scale


def inject_dino_lora(
    module: nn.Module, rank: int, alpha: float, dropout: float = 0.0
) -> tuple[str, ...]:
    """Inject LoRA into DINO attention projections and patch embedding.

    Matching is deliberately allow-listed. If a future Transformers model
    changes its module names, training fails instead of silently adapting the
    wrong layers.
    """

    replacements: list[tuple[str, nn.Module]] = []
    attention_suffixes = (
        ".attention.attention.query",
        ".attention.attention.key",
        ".attention.attention.value",
        ".attention.output.dense",
        ".attn.qkv",
        ".attn.proj",
    )
    patch_suffixes = (
        ".embeddings.patch_embeddings.projection",
        ".patch_embed.proj",
    )
    for name, child in list(module.named_modules()):
        if isinstance(child, nn.Linear) and any(
            name == value.removeprefix(".") or name.endswith(value)
            for value in attention_suffixes
        ):
            replacements.append((name, LoRALinear(child, rank, alpha, dropout)))
        elif isinstance(child, nn.Conv2d) and any(
            name == value.removeprefix(".") or name.endswith(value)
            for value in patch_suffixes
        ):
            replacements.append((name, LoRAConv2d(child, rank, alpha, dropout)))
    if not replacements:
        raise ValueError("no allow-listed DINO attention or patch modules were found for LoRA")
    for name, replacement in replacements:
        parent = module
        pieces = name.split(".")
        for piece in pieces[:-1]:
            parent = getattr(parent, piece)
        setattr(parent, pieces[-1], replacement)
    return tuple(name for name, _ in replacements)


def _load_external_state(module: nn.Module, path: Path) -> dict[str, Any]:
    try:
        payload = torch.load(path, map_location="cpu", weights_only=True)
    except TypeError:
        payload = torch.load(path, map_location="cpu")
    state = payload.get("state_dict", payload.get("model", payload)) if isinstance(payload, dict) else payload
    cleaned = {
        str(key).removeprefix("module.").removeprefix("backbone."): value
        for key, value in state.items()
    }
    result = module.load_state_dict(cleaned, strict=False)
    loaded = len(cleaned) - len(result.unexpected_keys)
    fraction = loaded / max(1, len(module.state_dict()))
    if fraction < 0.5:
        raise ValueError(f"external backbone checkpoint matched only {fraction:.1%} of parameters")
    return {
        "loaded_fraction": fraction,
        "missing": result.missing_keys,
        "unexpected": result.unexpected_keys,
    }


class SliceFeatureBackbone(nn.Module):
    def __init__(
        self,
        name: str,
        model_name: str | None,
        trainable_blocks: int,
        local_files_only: bool,
        pretrained: bool,
        checkpoint: Path | None,
        lora_rank: int = 0,
        lora_alpha: float = 16.0,
        lora_dropout: float = 0.05,
    ) -> None:
        super().__init__()
        self.name = name
        self.load_report: dict[str, Any] | None = None
        self.lora_modules: tuple[str, ...] = ()
        if lora_rank < 0:
            raise ValueError("LoRA rank cannot be negative")
        if lora_rank and trainable_blocks:
            raise ValueError("choose either LoRA or fully trainable backbone blocks, not both")
        if lora_rank and name != "dinov2":
            raise ValueError("LoRA is currently implemented only for the DINO backbone")
        if name == "dinov2":
            from transformers import AutoConfig, AutoModel

            if not model_name:
                raise ValueError("dinov2 requires --model-name")
            if pretrained:
                self.model = AutoModel.from_pretrained(
                    model_name, local_files_only=local_files_only
                )
            else:
                config = AutoConfig.from_pretrained(
                    model_name, local_files_only=local_files_only
                )
                self.model = AutoModel.from_config(config)
            hidden = int(self.model.config.hidden_size)
            self.output_dim = 2 * hidden
            freeze_except_last_blocks(self.model, trainable_blocks)
            if lora_rank:
                self.lora_modules = inject_dino_lora(
                    self.model, lora_rank, lora_alpha, lora_dropout
                )
            self.num_register_tokens = int(getattr(self.model.config, "num_register_tokens", 0) or 0)
        elif name == "efficientnet_b3":
            from torchvision.models import EfficientNet_B3_Weights, efficientnet_b3

            weights = EfficientNet_B3_Weights.DEFAULT if pretrained and checkpoint is None else None
            model = efficientnet_b3(weights=weights)
            self.output_dim = int(model.classifier[1].in_features)
            model.classifier = nn.Identity()
            self.model = model
            self.num_register_tokens = 0
            for parameter in self.model.parameters():
                parameter.requires_grad = False
            stages = list(self.model.features)
            if trainable_blocks > len(stages):
                raise ValueError(f"EfficientNet exposes only {len(stages)} feature stages")
            for stage in stages[-trainable_blocks:] if trainable_blocks else []:
                for parameter in stage.parameters():
                    parameter.requires_grad = True
        elif name == "radimagenet_resnet50":
            from torchvision.models import resnet50

            resnet = resnet50(weights=None)
            self.model = nn.Sequential(*list(resnet.children())[:-1])
            self.output_dim = int(resnet.fc.in_features)
            self.num_register_tokens = 0
            if checkpoint is not None:
                self.load_report = _load_external_state(self.model, checkpoint)
            for parameter in self.model.parameters():
                parameter.requires_grad = False
            stages = [stage for stage in self.model if any(True for _ in stage.parameters())]
            if trainable_blocks > len(stages):
                raise ValueError(f"RadImageNet ResNet exposes only {len(stages)} parameter stages")
            for stage in stages[-trainable_blocks:] if trainable_blocks else []:
                for parameter in stage.parameters():
                    parameter.requires_grad = True
        else:
            raise ValueError(f"unsupported backbone {name}")
        if checkpoint is not None and name != "radimagenet_resnet50":
            self.load_report = _load_external_state(self.model, checkpoint)

    def forward(self, pixels: Tensor) -> Tensor:
        if self.name == "dinov2":
            hidden = self.model(
                pixel_values=pixels, interpolate_pos_encoding=True
            ).last_hidden_state
            patches = hidden[:, 1 + self.num_register_tokens :]
            return torch.cat([hidden[:, 0], patches.mean(dim=1)], dim=-1)
        return self.model(pixels).flatten(1)


class RawStudyMILModel(nn.Module):
    def __init__(
        self,
        backbone: SliceFeatureBackbone,
        num_targets: int,
        hidden_dim: int = 512,
        dropout: float = 0.2,
        pool: str = "max",
        encoder_batch_size: int = 12,
        topk: int = 3,
        report_dim: int = 0,
    ) -> None:
        super().__init__()
        if pool not in {"max", "topk", "logmeanexp"}:
            raise ValueError("pool must be max, topk, or logmeanexp")
        if topk < 1:
            raise ValueError("topk must be positive")
        self.backbone = backbone
        self.pool = pool
        self.topk = topk
        self.report_dim = report_dim
        self.encoder_batch_size = encoder_batch_size
        self.plane_embedding = nn.Embedding(len(PLANE_TO_ID), 16)
        self.plane_target_bias = nn.Embedding(len(PLANE_TO_ID), num_targets)
        self.fluid_target_bias = nn.Embedding(3, num_targets)
        self.fatsat_target_bias = nn.Embedding(3, num_targets)
        nn.init.zeros_(self.plane_target_bias.weight)
        nn.init.zeros_(self.fluid_target_bias.weight)
        nn.init.zeros_(self.fatsat_target_bias.weight)
        self.head = nn.Sequential(
            nn.LayerNorm(backbone.output_dim + 16),
            nn.Linear(backbone.output_dim + 16, hidden_dim),
            nn.GELU(),
            nn.Dropout(dropout),
            nn.Linear(hidden_dim, num_targets),
        )
        self.report_projection = (
            nn.Sequential(
                nn.LayerNorm(backbone.output_dim),
                nn.Linear(backbone.output_dim, report_dim),
            )
            if report_dim > 0
            else None
        )

    def forward(
        self,
        pixels: Tensor,
        plane: Tensor,
        fluid: Tensor,
        fatsat: Tensor,
        study_index: Tensor,
        num_studies: int,
        return_aux: bool = False,
    ) -> Tensor | dict[str, Tensor]:
        features = []
        for start in range(0, pixels.shape[0], self.encoder_batch_size):
            features.append(self.backbone(pixels[start : start + self.encoder_batch_size]))
        features_all = torch.cat(features)
        slice_logits = self.head(
            torch.cat([features_all, self.plane_embedding(plane)], dim=-1)
        )
        slice_logits = (
            slice_logits
            + self.plane_target_bias(plane)
            + self.fluid_target_bias(fluid)
            + self.fatsat_target_bias(fatsat)
        )
        studies = []
        for index in range(num_studies):
            values = slice_logits[study_index == index]
            if values.numel() == 0:
                raise ValueError("every study must contain at least one decoded slice")
            if self.pool == "max":
                studies.append(values.max(dim=0).values)
            elif self.pool == "topk":
                count = min(self.topk, values.shape[0])
                studies.append(values.topk(count, dim=0).values.mean(dim=0))
            else:
                studies.append(torch.logsumexp(values, dim=0) - np.log(values.shape[0]))
        logits = torch.stack(studies)
        if not return_aux:
            return logits
        output = {"logits": logits}
        if self.report_projection is not None:
            study_features = torch.stack(
                [features_all[study_index == index].mean(dim=0) for index in range(num_studies)]
            )
            output["report_embedding"] = self.report_projection(study_features)
        return output

    def parameter_groups(self, backbone_lr: float, head_lr: float) -> list[dict[str, Any]]:
        backbone = [parameter for parameter in self.backbone.parameters() if parameter.requires_grad]
        backbone_ids = {id(parameter) for parameter in backbone}
        head = [
            parameter
            for parameter in self.parameters()
            if parameter.requires_grad and id(parameter) not in backbone_ids
        ]
        return [{"params": backbone, "lr": backbone_lr}, {"params": head, "lr": head_lr}]


def _alibi_slopes(heads: int) -> Tensor:
    if heads < 1:
        raise ValueError("ALiBi requires at least one attention head")
    return torch.pow(2.0, -torch.linspace(1.0, 8.0, heads))


class PhysicalAlibiEncoder(nn.Module):
    """One self-attention block biased by physical inter-slice distance."""

    def __init__(self, hidden_dim: int, heads: int, dropout: float) -> None:
        super().__init__()
        if hidden_dim % heads:
            raise ValueError("hidden_dim must be divisible by alibi_heads")
        self.heads = heads
        self.head_dim = hidden_dim // heads
        self.normalization = nn.LayerNorm(hidden_dim)
        self.qkv = nn.Linear(hidden_dim, 3 * hidden_dim, bias=False)
        self.output = nn.Linear(hidden_dim, hidden_dim, bias=False)
        self.feed_forward_norm = nn.LayerNorm(hidden_dim)
        self.feed_forward = nn.Sequential(
            nn.Linear(hidden_dim, 4 * hidden_dim),
            nn.GELU(),
            nn.Dropout(dropout),
            nn.Linear(4 * hidden_dim, hidden_dim),
        )
        self.dropout = nn.Dropout(dropout)
        self.register_buffer("slopes", _alibi_slopes(heads), persistent=True)

    def forward(self, hidden: Tensor, positions: Tensor) -> Tensor:
        count, width = hidden.shape
        normalized = self.normalization(hidden)
        qkv = self.qkv(normalized).reshape(count, 3, self.heads, self.head_dim)
        query, key, value = qkv.unbind(dim=1)
        query = query.transpose(0, 1)
        key = key.transpose(0, 1)
        value = value.transpose(0, 1)
        scores = torch.matmul(query, key.transpose(-1, -2)) * self.head_dim**-0.5
        distance = (positions[:, None] - positions[None, :]).abs()
        scores = scores - self.slopes[:, None, None].to(scores) * distance[None]
        attention = torch.softmax(scores, dim=-1)
        context = torch.matmul(attention, value).transpose(0, 1).reshape(count, width)
        hidden = hidden + self.dropout(self.output(context))
        return hidden + self.dropout(self.feed_forward(self.feed_forward_norm(hidden)))


class AdaptiveCoPlaneMILModel(nn.Module):
    """Target-query, series-aware, co-plane multiple-instance model.

    The model is invariant to slice order within a series and to series order
    within a plane. It retains the three acquisition planes as supervised
    branches before a learned, target-specific cross-plane fusion. An explicit
    unknown-plane branch keeps malformed metadata from being silently mapped
    to one of the three anatomical planes.
    """

    def __init__(
        self,
        backbone: SliceFeatureBackbone,
        num_targets: int,
        hidden_dim: int = 384,
        dropout: float = 0.2,
        encoder_batch_size: int = 12,
        report_dim: int = 0,
        alibi_heads: int = 6,
        specialist_bottleneck: int = 0,
    ) -> None:
        super().__init__()
        if hidden_dim < 8:
            raise ValueError("hidden_dim must be at least 8")
        self.backbone = backbone
        self.num_targets = num_targets
        self.num_planes = len(PLANE_TO_ID)
        self.encoder_batch_size = encoder_batch_size
        self.report_dim = report_dim
        self.plane_embedding = nn.Embedding(self.num_planes, 16)
        self.fluid_embedding = nn.Embedding(3, 4)
        self.fatsat_embedding = nn.Embedding(3, 4)
        input_dim = backbone.output_dim + 24
        self.slice_projection = nn.Sequential(
            nn.LayerNorm(input_dim),
            nn.Linear(input_dim, hidden_dim),
            nn.GELU(),
            nn.Dropout(dropout),
        )
        self.slice_key = nn.Linear(hidden_dim, hidden_dim, bias=False)
        self.slice_value = nn.Linear(hidden_dim, hidden_dim, bias=False)
        self.physical_alibi = PhysicalAlibiEncoder(hidden_dim, alibi_heads, dropout)
        self.target_query = nn.Parameter(torch.empty(num_targets, hidden_dim))
        self.series_gate_query = nn.Parameter(torch.empty(num_targets, hidden_dim))
        self.plane_gate_query = nn.Parameter(torch.empty(num_targets, hidden_dim))
        self.branch_weight = nn.Parameter(torch.empty(num_targets, hidden_dim))
        self.final_weight = nn.Parameter(torch.empty(num_targets, hidden_dim))
        self.branch_bias = nn.Parameter(torch.zeros(num_targets))
        self.final_bias = nn.Parameter(torch.zeros(num_targets))
        self.plane_target_bias = nn.Parameter(torch.zeros(self.num_planes, num_targets))
        self.label_fusion = nn.Linear(
            self.num_planes * num_targets * 2, num_targets, bias=False
        )
        nn.init.zeros_(self.label_fusion.weight)
        if specialist_bottleneck < 0:
            raise ValueError("specialist_bottleneck cannot be negative")
        if num_targets != len(TARGETS) and specialist_bottleneck:
            raise ValueError("pathology specialists require the canonical target list")
        self.specialist_bottleneck = specialist_bottleneck
        self.specialists = nn.ModuleDict()
        if specialist_bottleneck:
            target_index: list[int] = []
            for family, members in TARGET_FAMILIES.items():
                indices = [TARGETS.index(target) for target in members]
                target_index.extend(indices)
                head = nn.Sequential(
                    nn.LayerNorm(hidden_dim),
                    nn.Linear(hidden_dim, specialist_bottleneck),
                    nn.GELU(),
                    nn.Dropout(dropout),
                    nn.Linear(specialist_bottleneck, len(indices)),
                )
                # A warm-started specialist model is exactly the established
                # co-plane model before optimization.
                nn.init.zeros_(head[-1].weight)
                nn.init.zeros_(head[-1].bias)
                self.specialists[family] = head
            if sorted(target_index) != list(range(num_targets)):
                raise ValueError("target families must partition every target exactly once")
        for value in (
            self.target_query,
            self.series_gate_query,
            self.plane_gate_query,
            self.branch_weight,
            self.final_weight,
        ):
            nn.init.normal_(value, std=hidden_dim**-0.5)
        self.dropout = nn.Dropout(dropout)
        self.report_projection = (
            nn.Sequential(nn.LayerNorm(hidden_dim), nn.Linear(hidden_dim, report_dim))
            if report_dim > 0
            else None
        )

    def _encode(self, pixels: Tensor, plane: Tensor, fluid: Tensor, fatsat: Tensor) -> Tensor:
        features = []
        for start in range(0, pixels.shape[0], self.encoder_batch_size):
            features.append(self.backbone(pixels[start : start + self.encoder_batch_size]))
        image = torch.cat(features)
        metadata = torch.cat(
            [
                self.plane_embedding(plane),
                self.fluid_embedding(fluid),
                self.fatsat_embedding(fatsat),
            ],
            dim=-1,
        )
        return self.slice_projection(torch.cat([image, metadata], dim=-1))

    def forward(
        self,
        pixels: Tensor,
        plane: Tensor,
        fluid: Tensor,
        fatsat: Tensor,
        position: Tensor,
        study_index: Tensor,
        series_index: Tensor,
        num_studies: int,
        num_series: int,
        return_aux: bool = False,
    ) -> Tensor | dict[str, Tensor]:
        hidden = self._encode(pixels, plane, fluid, fatsat)
        scale = hidden.shape[-1] ** -0.5
        series_tokens: list[Tensor] = []
        series_planes: list[int] = []
        series_studies: list[int] = []
        for index in range(num_series):
            selected = series_index == index
            if not bool(selected.any()):
                raise ValueError("every packed series must contain at least one slice")
            contextual = self.physical_alibi(hidden[selected], position[selected])
            keys = self.slice_key(contextual)
            values = self.slice_value(contextual)
            attention = torch.softmax(
                self.target_query @ keys.transpose(0, 1) * scale, dim=-1
            )
            series_tokens.append(attention @ values)
            plane_values = plane[selected]
            study_values = study_index[selected]
            if not bool((plane_values == plane_values[0]).all()):
                raise ValueError("one series cannot span multiple planes")
            if not bool((study_values == study_values[0]).all()):
                raise ValueError("one series cannot span multiple studies")
            series_planes.append(int(plane_values[0].item()))
            series_studies.append(int(study_values[0].item()))
        stacked_series = torch.stack(series_tokens)
        series_plane = torch.tensor(series_planes, device=plane.device)
        series_study = torch.tensor(series_studies, device=study_index.device)

        all_logits: list[Tensor] = []
        all_branches: list[Tensor] = []
        all_branch_masks: list[Tensor] = []
        report_features: list[Tensor] = []
        for study in range(num_studies):
            branch_tokens = hidden.new_zeros(
                (self.num_planes, self.num_targets, hidden.shape[-1])
            )
            branch_logits = hidden.new_zeros((self.num_planes, self.num_targets))
            branch_mask = torch.zeros(self.num_planes, dtype=torch.bool, device=hidden.device)
            for plane_id in range(self.num_planes):
                selected = (series_study == study) & (series_plane == plane_id)
                if not bool(selected.any()):
                    continue
                candidates = stacked_series[selected]  # series x target x hidden
                gates = torch.einsum(
                    "th,nth->nt", self.series_gate_query, candidates
                ) * scale
                weights = torch.softmax(gates, dim=0)
                token = torch.einsum("nt,nth->th", weights, candidates)
                branch_tokens[plane_id] = token
                branch_logits[plane_id] = (
                    torch.einsum("th,th->t", self.branch_weight, self.dropout(token))
                    + self.branch_bias
                    + self.plane_target_bias[plane_id]
                )
                branch_mask[plane_id] = True
            if not bool(branch_mask.any()):
                raise ValueError("every study must contain at least one decoded plane")
            present_tokens = branch_tokens[branch_mask]
            present_logits = branch_logits[branch_mask]
            present_planes = torch.arange(self.num_planes, device=hidden.device)[branch_mask]
            gates = (
                torch.einsum("th,pth->pt", self.plane_gate_query, present_tokens) * scale
                + self.plane_target_bias[present_planes]
            )
            weights = torch.softmax(gates, dim=0)
            study_token = torch.einsum("pt,pth->th", weights, present_tokens)
            base_logits = (
                torch.einsum("pt,pt->t", weights, present_logits)
                + torch.einsum("th,th->t", self.final_weight, self.dropout(study_token))
                + self.final_bias
            )
            fusion_input = torch.cat(
                [
                    branch_logits.flatten(),
                    branch_mask[:, None]
                    .expand(self.num_planes, self.num_targets)
                    .to(branch_logits.dtype)
                    .flatten(),
                ]
            )
            all_logits.append(base_logits + self.label_fusion(fusion_input))
            if self.specialists:
                specialist_delta = base_logits.new_zeros(self.num_targets)
                for family, members in TARGET_FAMILIES.items():
                    indices = torch.tensor(
                        [TARGETS.index(target) for target in members],
                        device=study_token.device,
                    )
                    family_token = study_token.index_select(0, indices)
                    values = self.specialists[family](family_token)
                    # Each row is target-conditioned.  Use only the matching
                    # diagonal output so one family's findings cannot leak
                    # into another member through a shared scalar token.
                    specialist_delta = specialist_delta.index_add(
                        0, indices, values.diagonal().to(specialist_delta.dtype)
                    )
                all_logits[-1] = all_logits[-1] + specialist_delta
            all_branches.append(branch_logits)
            all_branch_masks.append(branch_mask)
            report_features.append(study_token.mean(dim=0))
        logits = torch.stack(all_logits)
        if not return_aux:
            return logits
        output = {
            "logits": logits,
            "branch_logits": torch.stack(all_branches),
            "branch_mask": torch.stack(all_branch_masks),
        }
        if self.report_projection is not None:
            output["report_embedding"] = self.report_projection(torch.stack(report_features))
        return output

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


def normalize_pixels(pixels: Tensor) -> Tensor:
    mean = pixels.new_tensor([0.485, 0.456, 0.406])[None, :, None, None]
    std = pixels.new_tensor([0.229, 0.224, 0.225])[None, :, None, None]
    return (pixels - mean) / std
