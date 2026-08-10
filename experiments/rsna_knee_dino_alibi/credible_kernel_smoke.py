#!/usr/bin/env python3
"""Smoke-test the hash-pinned credible Kaggle-kernel builder."""

from __future__ import annotations

import json
import subprocess
import sys
import tempfile
from pathlib import Path

try:
    from .constants import TARGETS
except ImportError:
    from constants import TARGETS


def main() -> None:
    here = Path(__file__).resolve().parent
    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory)
        anchor_oof = root / "patch_mean_fold0_oof.csv"
        raw_oof = root / "efficientnet_b3_topk_336_fold0_oof.csv"
        anchor_oof.touch()
        raw_oof.touch()
        anchor_oof.with_name("patch_mean_fold0.pt").write_bytes(b"anchor checkpoint")
        raw_oof.with_name("efficientnet_b3_topk_336_fold0.pt").write_bytes(b"raw checkpoint")
        blend = {
            "anchor": "consensus_patch",
            "members": ["consensus_patch", "efficientnet_routed"],
            "weights": {target: [0.5, 0.5] for target in TARGETS},
            "source_files": {
                "consensus_patch": [str(anchor_oof)],
                "efficientnet_routed": [str(raw_oof)],
            },
        }
        registry = {
            "families": {
                "efficientnet_routed": {
                    "inference_slices": 16,
                    "train_args": ["--backbone", "efficientnet_b3"],
                }
            }
        }
        blend_path, registry_path = root / "blend.json", root / "registry.json"
        blend_path.write_text(json.dumps(blend))
        registry_path.write_text(json.dumps(registry))
        output = root / "kernel"
        subprocess.run(
            [
                sys.executable,
                str(here / "build_kaggle_credible_kernel.py"),
                "--blend", str(blend_path),
                "--registry", str(registry_path),
                "--output", str(output),
            ],
            check=True,
            capture_output=True,
            text=True,
        )
        metadata = json.loads((output / "kernel-metadata.json").read_text())
        contract = json.loads((output / "checkpoint_contract.json").read_text())
        notebook = json.loads((output / metadata["code_file"]).read_text())
        code = "".join(notebook["cells"][1]["source"])
        assert not metadata["enable_internet"] and metadata["enable_gpu"]
        assert not metadata["is_private"]
        assert set(contract) == {"consensus_patch", "efficientnet_routed"}
        assert all(len(row["sha256"]) == 64 for rows in contract.values() for row in rows)
        assert "BUDGET_SECONDS = 8.75 * 3600" in code
        assert "hash mismatch" in code
        assert 'WORKING / "submission.csv"' in code
    print("credible Kaggle kernel smoke passed")


if __name__ == "__main__":
    main()
