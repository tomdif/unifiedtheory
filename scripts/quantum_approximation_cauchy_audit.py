#!/usr/bin/env python3
"""Audit quantitative Cauchy estimates and uniform form-norm state limits of full-generator trajectories."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalQuasiResolventVelocity', 'KFCausalWeightedCauchyPairing', 'KFCausalForcedEnergyGrowth', 'KFCausalClockFloorApproximationComparison', 'KFCausalClockFloorApproximationCauchy', 'KFCausalGraphVelocityFamily', 'KFCausalCauchyApproximationFamily', 'KFCausalClockFloorCauchyApproximationFamily', 'KFCausalCoerciveCauchyLimit', 'KFCausalApproximationStateLimit', 'KFCausalClockFloorUniformNormControl', 'KFCausalClockFloorApproximationStateLimit']
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
    logs = overlay / "quantum-approximation-cauchy-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_graph_approximation_audit.json"
    previous_hash = sha(previous_path)
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_approximation_cauchy_audit.py",
        "scripts/verify_quantum_approximation_cauchy.py",
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
        scope='For the existing fixed positive physical clock regulator, actual full fixed-domain generator approximations now have a quantitative energy-Cauchy family on every finite forward interval for initial graph data. The velocity bound E_t(A_b x)<=4 E_t(G(t)x) is derived from resolvent identities and quasi-dissipativity. The predecessor uniform graph-output estimates supply a common velocity budget M for trajectories; it is not an additional model assumption. With b,c>=2, delta=1/b+1/c, the smoothed resolvent graph identities and positive-form Young inequality bound the difference pairing. A forced energy inequality yields E_t(w_b-w_c)<=exp(kappa*(t-l))*(6+kappa)*M*delta*(t-l). Compactness selects B>=2 and a family with spectral parameters B+n, having one energy-Cauchy constant on the whole interval. Invertible coordinate transport and positive shifted-form coercivity give a uniform bound of the completed form norm by the transported energy. Completeness and the quantitative Cauchy bound construct a continuous uniform state limit u with u(l)=x and norm(w_n(t)-u(t))^2<=C/(B+n) for all times in the interval. The reference spectral parameter exists and is eliminated from the final model theorem. This proves convergence of actual approximation states in the completed form norm, with a uniform square-norm rate; it does not yet prove convergence of generator outputs, membership of the limit in the fixed generator domain, or the limiting strong differential equation. Initial data still require the fixed lifted domain, which imposes extra form regularity of the Hamiltonian output. Extension to the full physical Hamiltonian domain and identification of this new state limit with the existing full physical propagator remain open. The full physical propagator and the conditional identification of global strong physical solutions were already proved. No spectral parameter removes the physical clock floor. Momentum propagation, quantum clock escape, controlled physical limits, SM/GR identification, octonion necessity and the physical TOE remain unproved. No necessary model revision or new numerical evidence is asserted.')
    target = root / "data/quantum_approximation_cauchy_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()
