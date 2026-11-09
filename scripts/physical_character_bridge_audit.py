#!/usr/bin/env python3
"""Source-build and audit the physical character, thermal sums and interaction.

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
    "UnifiedTheory.Audit.KFCausalPhysicalChargedCharacter",
    "UnifiedTheory.Audit.KFCausalFreeThermalDensity",
    "UnifiedTheory.Audit.KFCausalCircularInteractingBridge",
]
CHECK = "scripts/CheckPhysicalCharacterBridge.lean"
EXPECTED_COUNT = 86


def main():
    env = os.environ.copy()
    env.pop("LEAN_PATH", None)
    env.setdefault("LEAN_NUM_THREADS", "6")
    logs = Path(tempfile.mkdtemp(prefix="unifiedtheory-physical-character-bridge-audit-"))
    local_sources = sorted({path for target in TARGETS for path in local_dependencies(target)})
    sources = local_sources + [
        CHECK, "scripts/physical_character_bridge_audit.py",
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
            "Retains the derived complete circular charge and free-Hamiltonian "
            "full-domain spectral identification. Identifies the actual zero-charge "
            "level character with the Euler series and disproves equality with the "
            "unmodified Watson chiA, F0w, P0w, and R1 combination by their first "
            "coefficients. Proves convergence and value of the charged-fiber thermal "
            "sum, nonintegrability over the full clock line, neutral-frequency "
            "Gaussian integration, and integrability of that density on finite "
            "clock intervals. For positive vacuum coupling, proves the entire "
            "interacting form-domain intersection and the exact free-plus-potential "
            "operator graph in circular coordinates on the common potential domain. "
            "No full interacting operator-domain regularity, interacting spectrum, "
            "global Hilbert-space heat trace, alternative Watson observable, "
            "empirical physical identification, or Clay-prize theorem is claimed."
        ),
    }
    target = ROOT / "data/physical_character_bridge_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print(f"{EXPECTED_COUNT} standard-axiom audits; {len(local_sources)} local Lean sources fingerprinted.")
    print(target)


if __name__ == "__main__":
    main()
