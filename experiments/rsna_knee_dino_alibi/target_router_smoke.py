#!/usr/bin/env python3
"""Synthetic leakage and shrinkage test for the nested target router."""

from __future__ import annotations

import json
import subprocess
import sys
import tempfile
from pathlib import Path

import numpy as np
import pandas as pd

try:
    from .constants import TARGETS
except ImportError:
    from constants import TARGETS


def main() -> None:
    here = Path(__file__).resolve().parent
    rng = np.random.default_rng(19)
    with tempfile.TemporaryDirectory() as temporary:
        root = Path(temporary)
        count = 240
        labels = pd.DataFrame(
            {
                "StudyInstanceUID": [f"study-{index}" for index in range(count)],
                "fold": np.arange(count) % 5,
            }
        )
        anchor = labels[["StudyInstanceUID"]].copy()
        specialist = labels[["StudyInstanceUID"]].copy()
        for index, target in enumerate(TARGETS):
            y = ((np.arange(count) + index) % 4 == 0).astype(int)
            labels[target] = y
            labels[f"{target}__gold"] = 1
            anchor[target] = y + rng.normal(0, 0.75, count)
            if index < 6:
                specialist[target] = y + rng.normal(0, 0.15, count)
            else:
                specialist[target] = rng.normal(0, 1, count)
        labels.to_csv(root / "labels.csv", index=False)
        anchor.to_csv(root / "anchor.csv", index=False)
        specialist.to_csv(root / "specialist.csv", index=False)
        subprocess.run(
            [
                sys.executable,
                str(here / "fit_nested_target_router.py"),
                "--labels-csv",
                str(root / "labels.csv"),
                "--member",
                f"anchor={root / 'anchor.csv'}",
                "--member",
                f"specialist={root / 'specialist.csv'}",
                "--anchor",
                "anchor",
                "--output",
                str(root / "router.json"),
                "--bootstrap-samples",
                "200",
                "--minimum-selection-probability",
                "0.65",
            ],
            check=True,
            capture_output=True,
            text=True,
        )
        artifact = json.loads((root / "router.json").read_text())
        for index, target in enumerate(TARGETS):
            expected = "specialist" if index < 6 else "anchor"
            if artifact["target_choice"][target] != expected:
                raise AssertionError(f"{target} routed to the wrong synthetic member")
        if not artifact["router_promoted"] or artifact["nested_gain"] <= 0:
            raise AssertionError("useful synthetic router was not promoted")
        print("nested target router smoke test passed")


if __name__ == "__main__":
    main()
