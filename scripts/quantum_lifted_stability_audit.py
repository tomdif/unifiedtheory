#!/usr/bin/env python3
"""Audit constructed lifted Schrodinger resolvents, consistent bounded generators and uniform forward energy estimates."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalAccretiveInverse', 'KFCausalComplexMassPencil', 'KFCausalWeightedMassEnergy', 'KFCausalComplexMassResolvent', 'KFCausalMassResolventStability', 'KFCausalDenseResolventConvergence', 'KFCausalComplexMassCurve', 'KFCausalClockFloorLiftedResolvent', 'KFCausalClockFloorLiftedRegularization', 'KFCausalDissipativeFormGrowth', 'KFCausalClockFloorLiftedEnergyStability', 'KFCausalMovingGeneratorApproximation', 'KFCausalClockFloorFixedDomainApproximation']
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
    logs = overlay / "quantum-lifted-stability-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_fixed_domain_audit.json"
    previous_hash = sha(previous_path)
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_lifted_stability_audit.py",
        "scripts/verify_quantum_lifted_stability.py",
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
        scope='For the existing fixed-regulator model, the actual lifted Schrodinger resolvent R(b,t)=(b M-c Q(t))^-1 M is constructed for every b>0, where c=-i/h. Multiplication by 1-i h turns its real diagonal into the existing coercive positive shift b M+Q(t); bounded invertibility is proved, not assumed. Both resolvent identities hold on the actual lifted Hamiltonian graph. In every positive shifted-form energy E(a,t,x)=Re<x,(a M+Q(t))x>, b R(b,t) is contractive, with a reference-form norm bound independent of b. The scaled resolvents converge strongly to the identity on the whole reference form space. The bounded generators A(b,t)=b*(b R(b,t)-I) converge strongly to c Lambda(t) on its actual domain and have continuous first time derivatives. Their exact dissipation equals -b*normSq(c)*E(a,t,Lambda(t)R(b,t)f), hence is nonpositive. For every global strong solution u of the bounded approximate equation, the derived forward estimate is E(a,t,u(t)) <= exp(2*(t-s))*E(a,s,u(s)) for s<=t, uniformly in b. This is a conditional trajectory estimate; this checkpoint does not construct those solutions. Transporting the bounded approximants using the previously constructed S and connection Gamma produces bounded continuous approximations of the actual fixed-domain generator G, with strong convergence on D(Lambda(s)), exact derivative cancellation, and the same cutoff-uniform forward transported-energy estimate. These are consistency and stability results, not a convergence or existence theorem for the approximate evolutions. The energy bound controls the form norm, not the norm of Lambda(t)u(t); the stronger graph-norm estimate remains missing. Constructing the bounded flows, proving the limit and its operator-domain regularity, and extending from the higher-regularity lifted domain to all physical D(H(s)) remain open in this route. The previous conditional identification of any global strong physical solution with the existing propagator remains proved. The full propagator already exists; its Hamiltonian-domain propagation and full forward strong equation remain unproved. The lifted domain requires the Hamiltonian output as well as the state to lie in the embedded form space. The cutoff b is auxiliary and does not remove the physical clock floor. Pure-momentum propagation, the uniform absolute-momentum response bound, quantum clock escape, physical regulator removal, SM/GR identification, octonion necessity and the physical TOE remain unproved. No necessary model change or new numerical result is asserted.')
    target = root / "data/quantum_lifted_stability_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()
