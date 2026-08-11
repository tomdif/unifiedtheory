#!/usr/bin/env python3
"""Fail-closed validation of externally sourced competition assets."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any


DEFAULT_MANIFEST = Path(__file__).with_name("external_assets.json")


def load_asset_manifest(path: Path = DEFAULT_MANIFEST) -> dict[str, dict[str, Any]]:
    payload = json.loads(path.read_text())
    if payload.get("schema_version") != 1 or not isinstance(payload.get("assets"), list):
        raise ValueError(f"unsupported external asset manifest: {path}")
    records: dict[str, dict[str, Any]] = {}
    for asset in payload["assets"]:
        required = {"name", "identifier", "url", "license", "role", "competition_eligible"}
        missing = required.difference(asset)
        if missing:
            raise ValueError(f"asset is missing {sorted(missing)}: {asset}")
        identifier = str(asset["identifier"])
        if identifier in records:
            raise ValueError(f"duplicate external asset identifier: {identifier}")
        if not str(asset["url"]).startswith("https://"):
            raise ValueError(f"external asset URL must be public HTTPS: {identifier}")
        if asset["competition_eligible"] and str(asset["license"]).strip().upper().startswith(
            "NO LICENSE"
        ):
            raise ValueError(f"unlicensed asset cannot be competition eligible: {identifier}")
        records[identifier] = asset
    return records


def require_competition_asset(identifier: str, path: Path = DEFAULT_MANIFEST) -> dict[str, Any]:
    assets = load_asset_manifest(path)
    if identifier not in assets:
        raise ValueError(
            f"external asset {identifier!r} is not disclosed in {path}; add and audit it first"
        )
    asset = assets[identifier]
    if not asset["competition_eligible"]:
        raise ValueError(
            f"external asset {identifier!r} is blocked: license={asset['license']!r}"
        )
    return asset


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    parser.add_argument("--require", action="append", default=[])
    args = parser.parse_args()
    assets = load_asset_manifest(args.manifest)
    for identifier in args.require:
        require_competition_asset(identifier, args.manifest)
    eligible = sum(bool(asset["competition_eligible"]) for asset in assets.values())
    print(f"external asset compliance passed: {eligible}/{len(assets)} eligible")


if __name__ == "__main__":
    main()
