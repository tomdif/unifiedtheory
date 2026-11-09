#!/usr/bin/env python3
"""Audit the full fixed-domain generator resolvent, its time regularity and domain-preserving bounded approximations."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalPartialResolventPerturbation', 'KFCausalConjugatedPartialResolvent', 'KFCausalEventualResolventApproximation', 'KFCausalPartialResolventGraphRegularization', 'KFCausalPerturbedResolventCurve', 'KFCausalClockFloorFixedGeneratorResolvent', 'KFCausalClockFloorFullGeneratorApproximation', 'KFCausalClockFloorFixedResolventCurve', 'KFCausalClockFloorFixedResolventWindow']
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
    logs = overlay / "quantum-full-resolvent-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_lifted_stability_audit.json"
    previous_hash = sha(previous_path)
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_full_resolvent_audit.py",
        "scripts/verify_quantum_full_resolvent.py",
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
        scope='For the existing fixed-regulator model, the resolvent of the FULL fixed-domain generator G(s,t), including the connection Gamma(s,t), is constructed above a derived spectral threshold. With R0(b;s,t)=S(a,t,s) R(b,t) S(a,s,t), K=norm(S(a,t,s))*sqrt(norm(F(a,t))/lowerConstant(a,t))*norm(S(a,s,t)), and q=norm(Gamma)*K, the formula is R_G=R0*(I-Gamma*R0)^(-1). For b>0 and b>q the Neumann factor is proved invertible. R_G maps into the actual fixed domain D(Lambda(s)); its graph output is b R_G f-f, and its left inverse identity holds on that domain. Its norm is at most K/(b-q); for b>2q the scaled resolvent has norm at most 2K. K and q are continuous in time, so a single positive threshold and scaled norm bound work uniformly throughout every compact time interval. Resolvents are differentiable at every admissible time; derivatives are continuous on the open admissible region. Scaled resolvents converge strongly to the identity on V. The new bounded approximation A_G(b)=b*(b R_G-I) converges strongly to G on the actual domain and preserves that domain at every fixed time, with exact commutation G A_G x=A_G G x. Scaled resolvent approximations converge simultaneously in state and generator output, giving graph approximation at a fixed time. These are resolvent and generator statements, NOT trajectory estimates. The previous energy estimate for conjugated approximants with the connection added afterward does not automatically transfer to this new full-generator regularization. Uniform evolution stability, construction and convergence of approximate flows, graph regularity along trajectories, and extension to all physical D(H(s)) remain unproved. The lifted domain still requires both state and Hamiltonian output to lie in embedded form space. The existing full physical propagator and conditional identification of global strong solutions with it remain proved; its full domain propagation and forward strong equation remain open. The auxiliary spectral limit does not remove the physical clock floor. Momentum propagation, quantum clock escape, controlled physical limits, SM/GR identification, octonion necessity and the physical TOE remain unproved. No necessary model change or new numerical evidence is asserted.')
    target = root / "data/quantum_full_resolvent_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()
