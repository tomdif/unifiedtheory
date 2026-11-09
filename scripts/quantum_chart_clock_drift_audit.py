#!/usr/bin/env python3
"""Audit exact unbounded chart-clock transport and the dense initial moment class."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ["KFCausalClockFloorInverseGapMoment","KFCausalClockFloorChartMomentDomain","KFCausalClockFloorChartPhasePairing","KFCausalClockFloorChartPhaseEhrenfest","KFCausalClockFloorChartPhaseContinuity","KFCausalClockFloorChartTransportLimit","KFCausalClockFloorChartCharacteristicMoment","KFCausalClockFloorChartEhrenfest","KFCausalClockFloorChartMomentInitialStates","KFCausalClockFloorChartStrictDrift"]
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
    logs = overlay / "quantum-chart-clock-drift-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_gauge_weak_dynamics_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "16ec2cf2bc877180fef24d694b60ff07474d8718daf1d6688566db9acf8309b3"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_chart_clock_drift_audit.py",
        "scripts/verify_quantum_chart_clock_drift.py",
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
        scope="For the actual full charge-averaged clock-floor propagator, epsilon>0, h!=0 and abs(h)<=2*pi*epsilon/3, define D(s)=epsilon/(exp(s)+epsilon) and Q(s)=exp(s)+epsilon*s. Initial data w belong to the completed reference energy form and have finite integral of (1-D(s)^2)^(-1)*abs(Jw)^2. This initial left-moment condition is proved for the existing total coherent span; the allowed physical initial states are Hilbert-dense. Bounded inverse-order barriers and Fatou prove that this unbounded inverse-gap moment stays finite and is nonincreasing at every forward time. The existing energy clock bound then proves absolute first-moment integrability of Q along the actual evolution. No evolved-state chart-domain or Hamiltonian operator-domain assumption is used. The exact law is <Q>_b-<Q>_a=integral_a^b ||P_ordered A_t U(s,t)Jw||^2 dt for all a,b>=s; A_t denotes the actual completed weighted energy output and P_ordered selects outputs 5,6,7, including both matter factors and vacuum. The mean chart coordinate has this derivative for t>s and is nondecreasing on [s,infinity). For positive vacuum coupling and nonzero initial state the drift is strictly positive, and the mean is strictly increasing, with no zero-charge restriction. The proof derives bounded chart-characteristic dynamics from the actual weak equation and phase/form covariance, then takes the zero-frequency limit using dominated convergence and the proved first moments. All eight original factors are retained: the five clock/kinetic factors cancel in this commutator, rather than being removed from the Hamiltonian. Arbitrary real mass/quartic/vacuum coefficients retain the existing Real.sqrt convention; positive vacuum is needed only for strict positivity. The moment assumption is stronger than finite energy alone; arbitrary finite-energy initial first-moment propagation, chart operator-domain propagation, divergent mean growth, a uniform drift rate, positive-clock probability escape, quantum clock-error decay and momentum propagation are not proved. Neither regulator removal nor controlled physical limits, Standard Model/GR identification, octonion necessity or a physical TOE is proved. No necessary Hamiltonian revision or new numerical evidence is asserted.")
    target = root / "data/quantum_chart_clock_drift_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

