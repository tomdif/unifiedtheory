#!/usr/bin/env python3
"""Audit forward lifted-domain propagation and strong physical Schrodinger dynamics."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalWeakResolventGraphLimit', 'KFCausalEventualVelocityControl', 'KFCausalApproximationDomainLimit', 'KFCausalClockFloorLimitDomain', 'KFCausalPropagatedStrongEquation', 'KFCausalClockFloorForwardStrongDynamics']
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--overlay", required=True, type=Path)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    overlay = args.overlay.resolve()
    assert overlay.is_dir() and "LEAN_PATH" in os.environ
    env = os.environ.copy()
    env["LEAN_PATH"] = str(overlay) + os.pathsep + env["LEAN_PATH"]
    logs = overlay / "quantum-forward-strong-dynamics-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_state_physical_identification_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "abdb31740fb9658689e576f5327623f4f1c89c921d7e64aea502e2833c63d545"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_forward_strong_dynamics_audit.py",
        "scripts/verify_quantum_forward_strong_dynamics.py",
    ]
    hashes = dict(previous["source_sha256"])
    assert all(sha(root / p) == h for p, h in hashes.items())
    assert not set(additions) & set(hashes)
    hashes.update({p: sha(root / p) for p in additions})
    evidence = previous["numerical_evidence"]
    for item in evidence.values():
        if isinstance(item, dict) and "path" in item:
            assert sha(root / item["path"]) == item["sha256"]
    root_text = (root / "UnifiedTheory.lean").read_text()
    suffix = "".join("import UnifiedTheory.Audit." + n + "\n" for n in MODULES)
    assert root_text.endswith(suffix)
    assert hashlib.sha256(root_text[:-len(suffix)].encode()).hexdigest() == previous["root_check"]["source_sha256"]
    root_hash = sha(root / "UnifiedTheory.lean")
    checks = []
    for name in MODULES:
        source = "UnifiedTheory/Audit/" + name + ".lean"
        text = (root / source).read_text()
        assert not re.search(r"\b(sorry|admit|axiom|unsafe)\b", text)
        command = ["lean", "-j1", "-o", str(overlay / "UnifiedTheory/Audit" / (name + ".olean")), source]
        result = subprocess.run(command, cwd=root, env=env, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        log = logs / (name + ".log")
        log.write_text(result.stdout)
        assert result.returncode == 0 and not re.search(r": error|: warning|sorryAx", result.stdout), str(log)
        parsed = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", result.stdout)
        audits = {n: sorted(s.strip() for s in xs.split(",") if s.strip()) for n, xs in parsed}
        expected = {"UnifiedTheory.Audit." + name + "." + n for n in re.findall(r"^#print axioms (\S+)", text, re.M)}
        declared = {"UnifiedTheory.Audit." + name + "." + n for n in re.findall(r"^theorem (\S+)", text, re.M)}
        assert len(parsed) == len(audits) and set(audits) == expected == declared
        assert all(set(xs) <= ALLOWED for xs in audits.values())
        checks.append(dict(source=source, command=command, exit_code=0,
                           log_sha256=sha(log), audited_declarations=audits))
        print(name + ": clean; " + str(len(audits)) + " theorem dependency lists", flush=True)
    result = subprocess.run(["lean", "-j1", "UnifiedTheory.lean"], cwd=root, env=env,
                            text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    log = logs / "root-import.log"
    log.write_text(result.stdout)
    assert result.returncode == 0 and not result.stdout.strip(), str(log)
    assert sha(root / "UnifiedTheory.lean") == root_hash and sha(previous_path) == previous_hash
    assert all(sha(root / p) == h for p, h in hashes.items())
    for item in evidence.values():
        if isinstance(item, dict) and "path" in item:
            assert sha(root / item["path"]) == item["sha256"]
    for name in MODULES:
        assert not (root / ".lake/build/lib/lean/UnifiedTheory/Audit" / (name + ".olean")).exists()
    report = dict(
        new_lean_theorem_count=sum(len(c["audited_declarations"]) for c in checks),
        modules=checks, source_sha256=hashes, numerical_evidence=evidence,
        previous_report=dict(path=str(previous_path.relative_to(root)), sha256=previous_hash),
        root_check=dict(command=["lean", "-j1", "UnifiedTheory.lean"], exit_code=0,
                        empty_log=True, source_sha256=root_hash, log_sha256=sha(log),
                        appended_imports=MODULES),
        lean_toolchain=(root / "lean-toolchain").read_text().strip(),
        scope='At the existing fixed positive physical regulator, the identified full-generator state limit preserves the fixed generator domain for initial domain data on every finite forward interval. Its graph output has one derived norm bound over the interval. Strong convergence of the smoothed states and eventual uniform velocity bounds yield weakly convergent output subsequences in the separable completed form space. The exact left and right bounded resolvent identities pass the graph to the limit without assuming strong output convergence. Bounded-equation uniqueness transfers the previously constructed velocity-energy witnesses to the approximation family identified with the physical evolution. Reversing coordinate transport proves formFlow(s,t) preserves the lifted Hamiltonian domain for t>=s. The physical graph identification then proves physical Hamiltonian-domain membership for these evolved states. The existing exact initial Hamiltonian derivative and physical propagator composition law give the full strong physical derivative at every t>=s: d/dr U(s,r)x at r=t is (-i/h) H(t) U(s,t)x. Covered initial physical states are embedded lifted-domain states. Equivalently, the supplied physical-input theorem requires x in the physical Hamiltonian domain and H(s)x in the embedded completed form space. The embedded lifted-domain initial states are proved dense in the physical Hilbert space. Density is not asserted to remove the output-regularity condition. The derivative is HasDerivAt in physical Hilbert norm, including at the initial time, even though domain propagation has only been proved forward. Full physical Hamiltonian-domain propagation, backward lifted-domain propagation, strong convergence of approximate generator outputs, and the strong equation in the completed form norm remain open. This result supplies no separate two-time approximation convergence theorem or corrected auxiliary evolution convergence. The physical regulator has not been removed. Quantum momentum propagation, clock escape, controlled physical limits, SM/GR identification, octonion necessity and a physical TOE remain unproved. No necessary physical model revision or new numerical evidence is asserted.')
    target = root / "data/quantum_forward_strong_dynamics_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()
