#!/usr/bin/env python3
"""Infer selected raw families and create an offline heterogeneous submission."""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path
from typing import Any

import numpy as np
import pandas as pd

try:
    from .constants import TARGETS
except ImportError:
    from constants import TARGETS


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--blend", type=Path, required=True)
    parser.add_argument("--registry", type=Path, required=True)
    parser.add_argument("--data-root", type=Path, required=True)
    parser.add_argument("--sample-submission", type=Path, required=True)
    parser.add_argument("--existing-member", action="append", default=[], help="NAME=CSV")
    parser.add_argument("--work-dir", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--workers", type=int, default=4)
    parser.add_argument("--dry-run", action="store_true")
    return parser.parse_args()


def parse_existing(values: list[str]) -> dict[str, Path]:
    result = {}
    for value in values:
        if "=" not in value:
            raise ValueError("existing member must be NAME=CSV")
        name, path = value.split("=", 1)
        if name in result:
            raise ValueError(f"duplicate existing member {name!r}")
        result[name] = Path(path)
    return result


def main() -> None:
    args = parse_args()
    blend: dict[str, Any] = json.loads(args.blend.read_text())
    registry: dict[str, Any] = json.loads(args.registry.read_text())
    selected = list(blend["members"])
    families = registry["families"]
    paths = parse_existing(args.existing_member)
    args.work_dir.mkdir(parents=True, exist_ok=True)
    commands = []
    here = Path(__file__).resolve().parent
    for name in selected:
        if name in paths:
            if not paths[name].is_file():
                raise FileNotFoundError(paths[name])
            continue
        if name not in families:
            raise ValueError(f"selected member {name!r} is neither existing nor registered")
        family = families[name]
        checkpoint_glob = str(
            Path(family["output"]) / str(family["checkpoint_pattern"]).replace("{fold}", "*")
        )
        destination = args.work_dir / f"{name}.csv"
        command = [
            sys.executable,
            str(here / "infer_raw_mil.py"),
            "--data-root", str(args.data_root),
            "--sample-submission", str(args.sample_submission),
            "--checkpoint-glob", checkpoint_glob,
            "--output", str(destination),
            "--slices-per-plane", str(family.get("inference_slices", 16)),
            "--workers", str(args.workers),
        ]
        commands.append(command)
        paths[name] = destination
    blend_command = [
        sys.executable,
        str(here / "blend_submission_files.py"),
        "--blend", str(args.blend),
        "--sample-submission", str(args.sample_submission),
        "--output", str(args.output),
    ]
    for name in selected:
        blend_command += ["--member", f"{name}={paths[name]}"]
    manifest = {
        "schema_version": 1,
        "selected": selected,
        "inference_commands": commands,
        "blend_command": blend_command,
        "uploaded": False,
        "submitted": False,
        "state": "dry_run" if args.dry_run else "running",
    }
    manifest_path = args.output.with_suffix(".manifest.json")
    manifest_path.parent.mkdir(parents=True, exist_ok=True)
    manifest_path.write_text(json.dumps(manifest, indent=2) + "\n")
    if args.dry_run:
        print(json.dumps(manifest, indent=2))
        return
    for command in commands:
        subprocess.run(command, check=True)
    subprocess.run(blend_command, check=True)
    sample = pd.read_csv(args.sample_submission, dtype={"StudyInstanceUID": str})
    output = pd.read_csv(args.output, dtype={"StudyInstanceUID": str})
    if output.columns.tolist() != sample.columns.tolist():
        raise ValueError("output columns differ from sample submission")
    if output["StudyInstanceUID"].tolist() != sample["StudyInstanceUID"].tolist():
        raise ValueError("output study order differs from sample submission")
    if not np.isfinite(output[TARGETS].to_numpy(float)).all():
        raise ValueError("output contains non-finite predictions")
    manifest["state"] = "offline_inference_complete"
    manifest["rows"] = len(output)
    manifest["output"] = str(args.output)
    manifest_path.write_text(json.dumps(manifest, indent=2) + "\n")
    print(json.dumps(manifest, indent=2))


if __name__ == "__main__":
    main()
