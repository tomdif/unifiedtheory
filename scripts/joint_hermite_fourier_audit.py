#!/usr/bin/env python3
"""Source-build and audit the joint Hermite/Fourier and charge representation.

Checks exact declarations and their axioms, and fingerprints the local import
closure. No dependency overlay, full-project build, circular charge eigenbasis,
or physical Hamiltonian diagonalization is claimed.
"""
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

from free_balanced_hamiltonian_audit import ROOT, STANDARD_AXIOMS, local_dependencies, sha256


TARGET = "UnifiedTheory.Audit.KFCausalJointHermiteFourierTransform"
CHECK = "scripts/CheckJointHermiteFourier.lean"
EXPECTED_COUNT = 37


def main():
    env = os.environ.copy()
    env.pop("LEAN_PATH", None)
    env.setdefault("LEAN_NUM_THREADS", "6")
    logs = Path(tempfile.mkdtemp(prefix="unifiedtheory-joint-hermite-fourier-audit-"))
    local_sources = local_dependencies(TARGET)
    sources = local_sources + [
        CHECK, "scripts/joint_hermite_fourier_audit.py",
        "scripts/free_balanced_hamiltonian_audit.py", "UnifiedTheory.lean",
        "lakefile.toml", "lake-manifest.json", "lean-toolchain",
    ]
    hashes = {path: sha256(ROOT / path) for path in sources}
    expected = re.findall(r"^#print axioms (\S+)$", (ROOT / CHECK).read_text(), re.M)
    if len(expected) != EXPECTED_COUNT or len(set(expected)) != len(expected):
        raise RuntimeError(f"Expected {EXPECTED_COUNT} distinct axiom checks")
    commands = [
        ["lake", "--rehash", "build", TARGET],
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
    if f"import {TARGET}\n" not in (ROOT / "UnifiedTheory.lean").read_text():
        raise RuntimeError("Missing root import")
    report = {
        "checks": checks,
        "audited_declarations": declarations,
        "source_sha256": hashes,
        "local_lean_dependency_count": len(local_sources),
        "root_imports_present": [TARGET],
        "root_build_checked": False,
        "uses_temporary_dependency_overlay": False,
        "scope": (
            "A derived complete four-dimensional Cartesian Hermite basis and a "
            "surjective physical transform into l2(N^4; L2(clock, neutral frequency)), "
            "with exact norm-convergent reconstruction. The actual physical circle "
            "action splits into charged and spectator factors and is intertwined "
            "with an explicit convergent Hermite matrix series. The entire maximal "
            "standing-charge graph, its domain, fixed sector and zero projection "
            "are identified in this representation. No diagonal occupation-charge "
            "law, maximal spectral Hamiltonian domain, fiber energy multiplicity, "
            "or Watson/R1 physical identification is claimed."
        ),
    }
    target = ROOT / "data/joint_hermite_fourier_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print(f"{EXPECTED_COUNT} standard-axiom audits; {len(local_sources)} local Lean sources fingerprinted.")
    print(target)


if __name__ == "__main__":
    main()
