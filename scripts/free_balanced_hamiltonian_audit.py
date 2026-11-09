#!/usr/bin/env python3
"""Build the actual sources with Lake and audit the balanced-domain theorems.

No temporary dependency overlay is used. The report fingerprints every local
Lean source in this target's import closure. This checks the named target,
not the entire UnifiedTheory root or the proposed Hermite spectral theorem.
"""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[1]
TARGET = "UnifiedTheory.Audit.KFCausalClockFloorFreeBalancedEnergy"
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def local_dependencies(module):
    pending, seen = [module], set()
    while pending:
        name = pending.pop()
        if name in seen:
            continue
        path = ROOT / (name.replace(".", "/") + ".lean")
        if not path.is_file():
            raise RuntimeError(f"Missing local source: {path}")
        seen.add(name)
        pending.extend(re.findall(r"^import\s+(UnifiedTheory\.\S+)", path.read_text(), re.M))
    return sorted(name.replace(".", "/") + ".lean" for name in seen)


def main():
    env = os.environ.copy()
    # Lake constructs the project's own search path; do not inherit an overlay.
    env.pop("LEAN_PATH", None)
    env.setdefault("LEAN_NUM_THREADS", "6")
    logs = Path(tempfile.mkdtemp(prefix="unifiedtheory-balanced-domain-audit-"))
    sources = local_dependencies(TARGET) + [
        "scripts/CheckFreeBalancedHamiltonian.lean",
        "scripts/free_balanced_hamiltonian_audit.py",
        "lakefile.toml", "lake-manifest.json", "lean-toolchain",
    ]
    hashes = {path: sha256(ROOT / path) for path in sources}
    commands = [
        ["lake", "--rehash", "build", TARGET],
        ["lake", "env", "lean", "scripts/CheckFreeBalancedHamiltonian.lean"],
    ]
    checks = []
    audit_text = ""
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
        if index == 1:
            audit_text = log.read_text()
    audits = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", audit_text)
    if len(audits) != 12:
        raise RuntimeError(f"Expected 12 axiom audits, found {len(audits)}")
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
    imports = ["UnifiedTheory.Audit.KFCausalClockFloorBalancedHamiltonian", TARGET]
    if not all(f"import {name}\n" in root_text for name in imports):
        raise RuntimeError("Missing root import")
    report = {
        "checks": checks,
        "audited_declarations": declarations,
        "source_sha256": hashes,
        "local_lean_dependency_count": len(local_dependencies(TARGET)),
        "root_imports_present": imports,
        "root_build_checked": False,
        "uses_temporary_dependency_overlay": False,
        "scope": (
            "Exact fixed-time graph and domain correspondence for the actual closed "
            "averaged clock-floor Hamiltonian and its explicit balanced reference form; "
            "zero-charge kernel preserved; inactive zero-coupling outputs vanish on "
            "the completed form. The Hermite/Fourier joint spectral representation, "
            "fiber energy multiplicities and physical identifications remain unproved."
        ),
    }
    target = ROOT / "data/free_balanced_hamiltonian_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print(f"12 standard-axiom audits; {report['local_lean_dependency_count']} local Lean sources fingerprinted.")
    print(target)


if __name__ == "__main__":
    main()
