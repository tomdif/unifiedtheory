#!/usr/bin/env python3
"""Audit actual moving-domain identifications and the closed generator on a fixed form-operator domain."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalInverseDomainTransport', 'KFCausalMassFormOperator', 'KFCausalClosedFixedDomainPerturbation', 'KFCausalClockFloorFormSecondDerivative', 'KFCausalClockFloorFormDomainTransport', 'KFCausalClockFloorLiftedHamiltonian', 'KFCausalClockFloorFixedFormGenerator', 'KFCausalStrongEvolutionReconstruction', 'KFCausalClockFloorStrongSolutionIdentification', 'KFCausalClockFloorFixedDomainReconstruction']
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
    logs = overlay / "quantum-fixed-domain-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_domain_schrodinger_audit.json"
    previous_hash = sha(previous_path)
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_fixed_domain_audit.py",
        "scripts/verify_quantum_fixed_domain.py",
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
        scope='For the existing fixed-regulator Hamiltonian, the actual common form and shifted inverse have checked second operator-norm time derivatives. The map S(a,s,t)=(a M+Q(t))^-1 (a M+Q(s)), a>0, is a differentiable bounded invertible map on the reference form space, with proved composition and inverse identities. Its physical action bijectively identifies D(H(s)) and D(H(t)) and preserves the shifted Hamiltonian output. This auxiliary transport is not asserted equal to physical evolution. The form-space operator Lambda(t), defined by M Lambda(t)w=Q(t)w, is proved closed and densely defined; its graph embeds exactly into the actual physical Hamiltonian graph. This lifted domain has extra regularity: both the physical state and its Hamiltonian output lie in the embedded form space; it is not the entire physical Hamiltonian domain. S also identifies these lifted domains. Including the explicit connection Gamma=P(a,s) Qprime(t) S(a,s,t), the transformed generator has a fixed dense domain D(Lambda(s)), a closed graph, differentiable bounded coefficients with continuous derivatives, and an exact transported mass-equation identity. A separate reconstruction theorem shows that a strong fixed-domain solution, if constructed, gives a strong solution for the actual physical Hamiltonian. The proved backward equation identifies every global strong physical solution with the existing full propagator, so any constructed global strong fixed-domain solution reconstructs that same propagator. Existence and domain preservation of the transformed flow, propagation of D(H(s)) under physical evolution, and the forward strong equation along all domain-state trajectories remain unproved. Pure-momentum propagation, the cutoff-uniform absolute-momentum response estimate, quantum clock escape, physical regulator removal, SM/GR identification, octonion necessity and the physical TOE remain unproved. No new numerical claim or necessary model change is asserted.')
    target = root / "data/quantum_fixed_domain_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()
