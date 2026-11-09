#!/usr/bin/env python3
"""Source-build and audit the attacks on the remaining analytic and identification gaps.

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
    "UnifiedTheory.Audit.KFCausalZeroSectorCoreObstruction",
    "UnifiedTheory.Audit.KFCausalInteractingEnergyFloor",
    "UnifiedTheory.Audit.KFCausalPhysicalIdentificationObstructions",
    "UnifiedTheory.Audit.KFCausalThermalDensityClockObstruction",
    "UnifiedTheory.Audit.KFCausalInteractionRegularityCriterion",
]
CHECK = "scripts/CheckOpenGapAttack.lean"
EXPECTED_COUNT = 129


def main():
    env = os.environ.copy()
    env.pop("LEAN_PATH", None)
    env.setdefault("LEAN_NUM_THREADS", "2")
    logs = Path(tempfile.mkdtemp(prefix="unifiedtheory-open-gap-attack-audit-"))
    local_sources = sorted({path for target in TARGETS for path in local_dependencies(target)})
    sources = local_sources + [
        CHECK, "scripts/open_gap_attack_audit.py",
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
            "Retains the preceding 98 declaration checks. Proves a zero-charge "
            "operator-core obstruction for the full Hilbert space, an exact "
            "bounded-resolvent certificate equivalent to strong potential-domain "
            "regularity, the interacting energy floor epsilon/2 and sharpened "
            "positive shifted-resolvent bound, obstructions to simple Watson "
            "regradings and to deriving the proposed Higgs coupling from the "
            "mass relation, clipping of nonpositive quadratic energy weights, "
            "a signed quartic square completion with exact two-minimum structure, "
            "and clock nonintegrability after neutral-frequency integration. "
            "The bounded regularity certificate is not constructed. Interacting "
            "eigenvalues, a vacuum-subtracted mass gap, a physical Watson "
            "observable, empirical identifications, and Clay consequences "
            "remain unproved. No external announced theorem is imported."
        ),
    }
    target = ROOT / "data/open_gap_attack_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print(f"{EXPECTED_COUNT} standard-axiom audits; {len(local_sources)} local Lean sources fingerprinted.")
    print(target)


if __name__ == "__main__":
    main()
