#!/usr/bin/env python3
"""Audit full physical Hamiltonian-domain propagation and forward strong dynamics."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalEmbeddedAdjointBound', 'KFCausalClosedGraphLift', 'KFCausalEmbeddedGraphExtension', 'KFCausalLiftedToPhysicalDomain', 'KFCausalClockFloorPhysicalGraphEvolution', 'KFCausalClockFloorFullDomainDynamics']
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
    logs = overlay / "quantum-full-domain-dynamics-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_forward_strong_dynamics_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "0c8588b5b57a286555484afae46c44208758c24e96b34ec8e68875c651a107ea"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_full_domain_dynamics_audit.py",
        "scripts/verify_quantum_full_domain_dynamics.py",
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
        scope='At the existing fixed positive physical regulator, the actual unitary propagator now preserves the full physical Hamiltonian domain forward in time: U(s,t)D(H(s)) is contained in D(H(t)) whenever s<=t. The extra condition that the initial Hamiltonian output belongs to the embedded completed form space has been removed. For every initial x in D(H(s)) and every t>=s, HasDerivAt in physical Hilbert norm gives d/dr U(s,r)x at r=t equal to (-i/h)H(t)U(s,t)x, including t=s. The theorem does not assert continuity of that derivative. The proof derives a physical norm bound from bounded operators on the completed form space that are adjoint with respect to the physical inner product. A log-convexity and exponential-growth argument proves the embedded symmetric-operator bound; applying it to S*T gives the paired-operator bound. Closed graph arguments make the form flow and its lifted Hamiltonian action bounded. The shifted lifted evolution has an explicitly bounded physical adjoint on form space, so it extends to a bounded operator on the full physical Hilbert space. The physical Hamiltonian closed graph identity passes from the dense embedding to all physical inputs after the initial shifted resolvent. The left resolvent identity then covers every initial Hamiltonian-domain state. An additional theorem gives one nonnegative constant C, for each fixed forward time pair, bounding the evolved Hamiltonian output by C times the sum of the initial state norm and initial Hamiltonian-output norm. This constant is obtained through closed graph boundedness; no explicit numerical value or compact-time-uniform bound is supplied. The existing exact initial derivative and physical propagator composition law give the strong equation. No strong convergence of approximate generator outputs is assumed or proved. Backward physical or lifted-domain propagation, strong approximate output convergence, the strong equation in completed form norm, and corrected auxiliary evolution convergence remain open. The physical clock regulator remains fixed. Quantum momentum propagation, quantum clock recovery, controlled physical limits, SM/GR identification, octonion necessity and a physical TOE remain unproved. No necessary physical model revision or new numerical evidence is asserted.')
    target = root / "data/quantum_full_domain_dynamics_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()
