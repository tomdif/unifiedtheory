#!/usr/bin/env python3
"""Validate the initial requirements ledger; success is not a Clay certificate."""
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
LEDGER = ROOT / "data/yang_mills_requirements.json"


def check_ledger():
    data = json.loads(LEDGER.read_text())
    required = {f"YM{i:02d}" for i in range(1, 13)}
    items = data["requirements"]
    ids = [item["id"] for item in items]
    if len(ids) != len(set(ids)) or set(ids) != required:
        raise RuntimeError("Missing or duplicate full-target requirement")
    dependencies = {item["id"]: item["depends_on"] for item in items}
    visited, active = set(), set()

    def visit(node):
        if node in active:
            raise RuntimeError("Cyclic requirement dependencies")
        if node in visited:
            return
        active.add(node)
        for parent in dependencies[node]:
            if parent not in required:
                raise RuntimeError("Unknown requirement dependency")
            visit(parent)
        active.remove(node)
        visited.add(node)

    for node in ids:
        visit(node)
    declarations = []
    for item in items:
        if not set(item["depends_on"]) <= required or item["id"] in item["depends_on"]:
            raise RuntimeError("Unknown or self-referential requirement dependency")
        if item["proof_status"] != "open" or item["target_proof"] is not None:
            raise RuntimeError("This initial framework has no full-target proof certificate")
        declarations.extend(item["interface_declarations"])
    declarations += [item["declaration"] for item in data["verified_auxiliary_evidence"]]
    for declaration in declarations:
        module, name = declaration.rsplit(".", 1)
        source = ROOT / (module.replace(".", "/") + ".lean")
        pattern = rf"^(?:def|abbrev|theorem|structure|instance)\s+{re.escape(name)}\b"
        if not source.is_file() or not re.search(pattern, source.read_text(), re.M):
            raise RuntimeError(f"Unresolved evidence reference: {declaration}")
    if data["claim_status"] != "framework_only_no_clay_certificate":
        raise RuntimeError("Framework status must not claim a solution")
    if data["continuum_yang_mills_candidate_constructed"] or data["complete_formal_axiom_set_encoded"]:
        raise RuntimeError("Unsupported construction or full-specification claim")
    result = {
        "ledger_consistent": True,
        "full_target_requirements_open": len(items),
        "verified_auxiliary_references": len(data["verified_auxiliary_evidence"]),
        "clay_certificate_present": False,
    }
    return result


if __name__ == "__main__":
    print(json.dumps(check_ledger(), indent=2))
