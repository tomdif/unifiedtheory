#!/usr/bin/env python3
"""Check the declarations explicitly listed in CheckYangMillsTwisted.lean.

Build their library modules first, for example with audit_repository.py --build.
This is an axiom-dependency check, not a physical Yang–Mills certificate.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
CHECKER = ROOT / "scripts/CheckYangMillsTwisted.lean"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def validate_output(source: str, log: str) -> dict:
    expected = re.findall(r"^#print axioms (\S+)", source, re.M)
    if not expected or len(set(expected)) != len(expected):
        raise ValueError("Missing or duplicate declaration requests")
    records = re.findall(
        r"'([^\n]+?)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", log
    )
    found = {name: sorted(x.strip() for x in axioms.split(",") if x.strip())
             for name, axioms in records}
    if len(found) != len(records) or set(found) != set(expected):
        raise ValueError("Axiom output does not match the requested declarations")
    forbidden = {name: axioms for name, axioms in found.items() if not set(axioms) <= ALLOWED}
    if forbidden:
        raise ValueError(f"Unexpected axiom dependencies: {forbidden}")
    return {"passed": True, "checked_declarations": len(found),
            "allowed_axioms": sorted(ALLOWED), "declarations": found}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--log", type=Path)
    args = parser.parse_args()
    proc = subprocess.run(["lake", "env", "lean", str(CHECKER.relative_to(ROOT))],
                          cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if args.log: args.log.write_text(proc.stdout)
    if proc.returncode:
        print(proc.stdout)
        return proc.returncode
    report = validate_output(CHECKER.read_text(), proc.stdout)
    if args.output: args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: v for k, v in report.items() if k != "declarations"}, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
