#!/usr/bin/env python3
"""Validate the frozen Gate 4--6 attack ledger without inventing evidence."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any


REQUIRED_ATTACK_FIELDS = {
    "id",
    "gate",
    "claim_class",
    "formal_source",
    "locked_claim",
    "acceptance_rule",
    "falsification_rule",
    "evidence_required",
    "result",
    "verdict",
}


def load_json(path: Path) -> dict[str, Any]:
    with path.open("rb") as stream:
        value = json.load(stream)
    if not isinstance(value, dict):
        raise ValueError("ledger root must be a JSON object")
    return value


def validate(ledger: dict[str, Any]) -> None:
    if ledger.get("status") != "preregistered_no_results":
        raise ValueError("ledger must remain preregistered_no_results")
    attacks = ledger.get("attacks")
    if not isinstance(attacks, list) or not attacks:
        raise ValueError("attacks must be a nonempty array")

    seen: set[str] = set()
    for index, attack in enumerate(attacks):
        if not isinstance(attack, dict):
            raise ValueError(f"attack {index} must be an object")
        missing = REQUIRED_ATTACK_FIELDS.difference(attack)
        if missing:
            raise ValueError(f"attack {index} missing {sorted(missing)}")
        attack_id = attack["id"]
        if not isinstance(attack_id, str) or not attack_id:
            raise ValueError(f"attack {index} has an invalid id")
        if attack_id in seen:
            raise ValueError(f"duplicate attack id {attack_id}")
        seen.add(attack_id)
        if attack["result"] is not None or attack["verdict"] != "pending":
            raise ValueError(
                f"{attack_id}: preregistration may not contain a result or verdict"
            )
        if not attack["formal_source"] or not attack["evidence_required"]:
            raise ValueError(f"{attack_id}: sources and evidence must be explicit")


def canonical_digest(ledger: dict[str, Any]) -> str:
    payload = json.dumps(
        ledger, sort_keys=True, separators=(",", ":"), ensure_ascii=False
    ).encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "ledger",
        nargs="?",
        type=Path,
        default=Path("TOE_GATE456_ATTACK_LEDGER.json"),
    )
    args = parser.parse_args()
    ledger = load_json(args.ledger)
    validate(ledger)
    print(f"valid: {len(ledger['attacks'])} frozen attacks")
    print(f"canonical_sha256: {canonical_digest(ledger)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
