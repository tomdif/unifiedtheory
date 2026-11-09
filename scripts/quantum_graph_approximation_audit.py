#!/usr/bin/env python3
"""Audit full-generator approximate domain propagation and uniform graph-output energy bounds."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalCommonDomainResolvent', 'KFCausalPartialResolventCommutation', 'KFCausalResolventDomainTrajectories', 'KFCausalTransportedPerturbedGrowth', 'KFCausalUniformGraphTrajectories', 'KFCausalClockFloorGeneratorGraphDerivative', 'KFCausalClockFloorDomainApproximateSolutions', 'KFCausalClockFloorGraphEnergyStability', 'KFCausalClockFloorUniformGraphApproximations']
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
    logs = overlay / "quantum-graph-approximation-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_full_stability_audit.json"
    previous_hash = sha(previous_path)
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_graph_approximation_audit.py",
        "scripts/verify_quantum_graph_approximation.py",
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
        scope='For the existing fixed physical regulator, the full-generator bounded approximations now have unique finite-interval solutions and preserve the actual fixed operator domain along those trajectories. A positive reference spectral parameter lam exists above the derived resolvent threshold on every compact interval. With G(t)=Acoef(t)T+Bcoef(t) on T=Lambda(s), the bounded output TR_lam is constructed from the principal inverse and the full resolvent graph identity. The bounded continuous correction D_lam=Aprime*TR_lam+Bprime*R_lam is the action of the coefficient derivative after resolvent smoothing. The common-domain resolvent difference identity proves Rprime_lam=R_lam*D_lam; different spectral resolvents commute, hence R_lam commutes with every admissible full approximation A_b. Constructing zprime=(A_b-D_lam)z and w=R_lam*z proves wprime=A_b*w, with (w,lam*w-z) in the actual graph of G at every time. For initial graph pair (x,y), z(l)=lam*x-y. Uniqueness identifies this reconstruction with every approximate solution having the same initial state. No domain preservation of the bounded connection or graph correction is assumed. In transported energy E_t(v)=Re<S(t)v,F(t)S(t)v>, the bounded correction has derived rate eta=norm(F)*norm((S*(-D_lam))*U)/d; the auxiliary growth rate is rho+2eta. Compactness gives b0>0 and kappa>=0, independent of b>=b0 and initial data, so constructed trajectories satisfy E_t(w)<=exp(kappa*(t-l))*E_l(x), E_t(z)<=exp(kappa*(t-l))*E_l(lam*x-y), and E_t(G(t)w)<=exp(kappa*(t-l))*(2*lam^2*E_l(x)+2*E_l(lam*x-y)) on the entire finite forward interval. These are actual trajectory domain propagation and uniform graph-output energy bounds for the bounded approximations. They do not prove convergence of these trajectories, convergence of generator outputs, a limiting strong fixed-domain evolution, or extension to the full physical Hamiltonian domain. The reference domain still requires both physical state and Hamiltonian output to lie in embedded form space. The existing full physical propagator and conditional identification of global strong physical solutions remain proved; its full domain propagation and forward strong equation remain open. Neither spectral parameter removes the physical clock floor. Momentum propagation, quantum clock escape, controlled physical limits, SM/GR identification, octonion necessity and the physical TOE remain unproved. No necessary model revision or new numerical evidence is asserted.')
    target = root / "data/quantum_graph_approximation_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()
