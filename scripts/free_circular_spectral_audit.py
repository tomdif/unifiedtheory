#!/usr/bin/env python3
"""Source-build and audit circular charge and the actual free Hamiltonian.

Checks named declarations, standard axioms, and unchanged source fingerprints.
No temporary dependency overlay or full-project root build is used.
"""
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

from free_balanced_hamiltonian_audit import ROOT, STANDARD_AXIOMS, local_dependencies, sha256


TARGET = "UnifiedTheory.Audit.KFCausalFreeCircularSpectralDomain"
CHECK = "scripts/CheckFreeCircularSpectral.lean"
EXPECTED_COUNT = 51


def main():
    env = os.environ.copy()
    env.pop("LEAN_PATH", None)
    env.setdefault("LEAN_NUM_THREADS", "6")
    logs = Path(tempfile.mkdtemp(prefix="unifiedtheory-free-circular-spectral-audit-"))
    local_sources = local_dependencies(TARGET)
    sources = local_sources + [
        CHECK, "scripts/free_circular_spectral_audit.py",
        "scripts/free_balanced_hamiltonian_audit.py", "UnifiedTheory.lean",
        "lakefile.toml", "lake-manifest.json", "lean-toolchain",
        "UnifiedTheory/QSeries/README.md",
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
            "Derived complete circular charged basis, actual standing-charge "
            "occupation differences and full maximal domain. Actual polynomial "
            "differential oscillator, its Fourier kinetic/potential identities, "
            "and both two- and four-dimensional closed oscillator domains. "
            "The already constructed physical free Hamiltonian (zero couplings), "
            "for epsilon>0 and 0<h<=pi*epsilon/3, is identified on its entire "
            "operator graph with diagonal energy multiplication over continuous "
            "clock/neutral-frequency fibers. Explicit graph cores justify the "
            "extension from packets. The exact weighted-integral domain and "
            "zero-charge level count (p+1)^2 are proved. No interacting spectrum, "
            "global trace-class heat kernel, Watson/R1 physical trace identity, "
            "or Clay-prize theorem is claimed."
        ),
    }
    target = ROOT / "data/free_circular_spectral_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print(f"{EXPECTED_COUNT} standard-axiom audits; {len(local_sources)} local Lean sources fingerprinted.")
    print(target)


if __name__ == "__main__":
    main()
