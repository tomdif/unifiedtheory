#!/usr/bin/env python3
"""Audit the actual free Hamiltonian form and domain bridge.

Builds genuine Lake source targets without a dependency overlay. Checks exact
declaration names and their axioms, and fingerprints the local import closure.
This does not claim a full-project build or the joint Hermite/Fourier spectral theorem.
"""
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

from free_balanced_hamiltonian_audit import ROOT, STANDARD_AXIOMS, local_dependencies, sha256


TARGETS = [
    "UnifiedTheory.Audit.KFCausalClockFloorFreeFormDomain",
    "UnifiedTheory.Audit.KFCausalClockFloorFreeHamiltonianFormSum",
]
CHECK = "scripts/CheckFreeFormBridge.lean"


def main():
    env = os.environ.copy()
    env.pop("LEAN_PATH", None)
    env.setdefault("LEAN_NUM_THREADS", "6")
    logs = Path(tempfile.mkdtemp(prefix="unifiedtheory-free-form-bridge-audit-"))
    local_sources = sorted({path for target in TARGETS for path in local_dependencies(target)})
    sources = local_sources + [
        CHECK, "scripts/free_form_bridge_audit.py",
        "scripts/free_balanced_hamiltonian_audit.py", "UnifiedTheory.lean",
        "lakefile.toml", "lake-manifest.json", "lean-toolchain",
    ]
    hashes = {path: sha256(ROOT / path) for path in sources}
    expected = re.findall(r"^#print axioms (\S+)$", (ROOT / CHECK).read_text(), re.M)
    if len(expected) != 23 or len(set(expected)) != len(expected):
        raise RuntimeError("Expected 23 distinct axiom checks")
    commands = [
        ["lake", "--rehash", "build", *TARGETS],
        ["lake", "env", "lean", CHECK],
    ]
    checks = []
    for index, command in enumerate(commands):
        log = logs / f"{index}.log"
        with log.open("w") as output:
            result = subprocess.run(command, cwd=ROOT, env=env, stdout=output,
                                    stderr=subprocess.STDOUT)
        if result.returncode:
            raise RuntimeError(f"Command failed: {command}; inspect {log}")
        checks.append({"command": command, "exit_code": 0,
                       "log": str(log), "log_sha256": sha256(log)})
        print("Passed:", " ".join(command), flush=True)
    audit_text = Path(checks[1]["log"]).read_text()
    audits = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", audit_text)
    if [name for name, _ in audits] != expected:
        raise RuntimeError("Axiom output does not match the expected declarations")
    declarations = {}
    for name, raw in audits:
        axioms = {part.strip() for part in raw.split(",") if part.strip()}
        if not axioms <= STANDARD_AXIOMS:
            raise RuntimeError(f"Unexpected axioms in {name}: {axioms}")
        declarations[name] = sorted(axioms)
    if re.search(r"\bsorryAx\b|: error|: warning", audit_text):
        raise RuntimeError(f"Unexpected diagnostic in {checks[1]['log']}")
    changed = [path for path, digest in hashes.items() if sha256(ROOT / path) != digest]
    if changed:
        raise RuntimeError(f"Sources changed during verification: {changed}")
    if not all(f"import {target}\n" in (ROOT / "UnifiedTheory.lean").read_text() for target in TARGETS):
        raise RuntimeError("Missing root import")
    report = {
        "checks": checks,
        "audited_declarations": declarations,
        "source_sha256": hashes,
        "local_lean_dependency_count": len(local_sources),
        "root_imports_present": TARGETS,
        "root_build_checked": False,
        "uses_temporary_dependency_overlay": False,
        "scope": (
            "The actual free joint energy graph is already closed; on the zero-charge "
            "sector its form domain is exactly the five active factor domains. "
            "For epsilon>0, h!=0 and |h|<=pi*epsilon/3, the full averaged free form "
            "domain is the intersection of the explicit maximal static and radial "
            "root domains. Its Hamiltonian graph is precisely the variational graph "
            "of their form sum, and its energy equals the explicit Fourier kinetic "
            "and radial position integrals. No joint Hermite/Fourier diagonalization, "
            "fiber energy multiplicity or Watson/R1 physical identification is claimed."
        ),
    }
    target = ROOT / "data/free_form_bridge_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print(f"23 standard-axiom audits; {len(local_sources)} local Lean sources fingerprinted.")
    print(target)


if __name__ == "__main__":
    main()
