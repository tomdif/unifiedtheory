#!/usr/bin/env python3
"""Audit the derived scalar Hermite transform and physical packet compatibility.

Builds genuine Lake source targets without a dependency overlay. Checks exact
declaration names and their axioms, and fingerprints the local import closure.
This does not claim a full-project build or the joint physical spectral theorem.
"""
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

from free_balanced_hamiltonian_audit import ROOT, STANDARD_AXIOMS, local_dependencies, sha256


TARGETS = [
    "UnifiedTheory.Audit.KFCausalHermiteHilbertBasis",
    "UnifiedTheory.Audit.KFCausalNeutralHermiteDomain",
]
CHECK = "scripts/CheckHermiteSpectralBridge.lean"


def main():
    env = os.environ.copy()
    env.pop("LEAN_PATH", None)
    env.setdefault("LEAN_NUM_THREADS", "6")
    logs = Path(tempfile.mkdtemp(prefix="unifiedtheory-hermite-spectral-audit-"))
    local_sources = sorted({path for target in TARGETS for path in local_dependencies(target)})
    sources = local_sources + [
        CHECK, "scripts/hermite_spectral_bridge_audit.py",
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
    if f"import {TARGETS[0]}\n" not in (ROOT / "UnifiedTheory.lean").read_text():
        raise RuntimeError("Missing root import")
    report = {
        "checks": checks,
        "audited_declarations": declarations,
        "source_sha256": hashes,
        "local_lean_dependency_count": len(local_sources),
        "root_imports_present": [TARGETS[0]],
        "root_build_checked": False,
        "uses_temporary_dependency_overlay": False,
        "scope": (
            "Derived polynomial-Gaussian L2 totality, Hermite differential equations, "
            "orthogonality, a scalar Hermite Hilbert basis and unitary expansion, "
            "and diagonalization of the oscillator on the polynomial-Gaussian domain. "
            "Rebuilds the original physical packet-domain module with the same "
            "extracted polynomial definitions. Does not establish the full joint "
            "charge/Fourier representation, maximal physical operator domain, "
            "physical energy multiplicities, or Watson/R1 physical identification."
        ),
    }
    target = ROOT / "data/hermite_spectral_bridge_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print(f"23 standard-axiom audits; {len(local_sources)} local Lean sources fingerprinted.")
    print(target)


if __name__ == "__main__":
    main()
