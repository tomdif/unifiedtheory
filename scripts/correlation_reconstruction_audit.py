#!/usr/bin/env python3
"""Source-build and audit the interacting resolvent correlation reconstruction.

Retains the complete previous free spectral audit and checks every new theorem.
No temporary dependency overlay or full-project root build is used.
"""
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

from free_balanced_hamiltonian_audit import ROOT, STANDARD_AXIOMS, local_dependencies, sha256


TARGETS = [
    "UnifiedTheory.Audit.KFCausalResolventReflectionKernel",
    "UnifiedTheory.Audit.KFCausalResolventStationaryCovariance",
    "UnifiedTheory.Audit.KFCausalInteractingCorrelationReconstruction",

    "UnifiedTheory.Audit.KFCausalZeroSectorCoreObstruction",
    "UnifiedTheory.Audit.KFCausalInteractingEnergyFloor",
    "UnifiedTheory.Audit.KFCausalPhysicalIdentificationObstructions",
    "UnifiedTheory.Audit.KFCausalThermalDensityClockObstruction",
    "UnifiedTheory.Audit.KFCausalInteractionRegularityCriterion",
]
CHECK = "scripts/CheckCorrelationReconstruction.lean"
EXPECTED_COUNT = 165


def main():
    env = os.environ.copy()
    env.pop("LEAN_PATH", None)
    env.setdefault("LEAN_NUM_THREADS", "2")
    logs = Path(tempfile.mkdtemp(prefix="unifiedtheory-correlation-reconstruction-audit-"))
    local_sources = sorted({path for target in TARGETS for path in local_dependencies(target)})
    sources = local_sources + [
        CHECK, "scripts/correlation_reconstruction_audit.py",
        "scripts/free_balanced_hamiltonian_audit.py", "UnifiedTheory.lean",
        "lakefile.toml", "lake-manifest.json", "lean-toolchain",
        "UnifiedTheory/QSeries/README.md",
    ]
    hashes = {path: sha256(ROOT / path) for path in sources}
    expected = re.findall(r"^#print axioms (\S+)$", (ROOT / CHECK).read_text(), re.M)
    if len(expected) != EXPECTED_COUNT or len(set(expected)) != len(expected):
        raise RuntimeError(f"Expected {EXPECTED_COUNT} distinct axiom checks")
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
    root_text = (ROOT / "UnifiedTheory.lean").read_text()
    if not all(f"import {target}\n" in root_text for target in TARGETS):
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
            "Retains the preceding 129 named checks. Constructs a positive-time "
            "resolvent reflection kernel, its null-history quotient and exact "
            "Hilbert-space isometry, the descended discrete transfer, and a "
            "stationary positive two-point covariance. Constructs the inverse-"
            "transfer partial operator and proves equality of its entire graph "
            "with the actual interacting Hamiltonian under the isometry. "
            "Proves strict transfer contraction and absence of nonzero fixed "
            "vectors before a vacuum-energy normalization. Discrete time uses "
            "(H+1)^(-1), not exp(-s H). No spacetime-local gauge fields, field "
            "measure, physical vacuum, continuum Yang--Mills model, physical "
            "parameter identification, or Clay mass gap is constructed by these "
            "Lean modules. The README also gives analytical Fock/Pauli--Fierz "
            "and spectral-measure generalized-free-field extensions, including "
            "a small-coupling ground-state argument for the former and locality "
            "for the latter. Those larger constructions are not Lean-formalized "
            "or certified by this audit."
        ),
    }
    target = ROOT / "data/correlation_reconstruction_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print(f"{EXPECTED_COUNT} standard-axiom audits; {len(local_sources)} local Lean sources fingerprinted.")
    print(target)


if __name__ == "__main__":
    main()
