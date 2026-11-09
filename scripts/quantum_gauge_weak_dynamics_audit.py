#!/usr/bin/env python3
"""Audit the actual transformed weak quantum dynamics and dense chart tests."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalMovingTestDerivative', 'KFCausalL2PhaseDerivative', 'KFCausalClockFloorGaugeDerivative', 'KFCausalClockFloorReferenceChartModulation', 'KFCausalClockFloorGaugePairing', 'KFCausalClockFloorGaugeWeakDynamics', 'KFCausalClockFloorGaugeTestDensity']
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
    logs = overlay / "quantum-gauge-weak-dynamics-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_chart_gauge_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "f1b74d39b31b4dffea175ddafd0b22d9d1d1248aac4cae65e6428439434aadc6"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_gauge_weak_dynamics_audit.py",
        "scripts/verify_quantum_gauge_weak_dynamics.py",
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
        scope='Actual finite-energy trajectories of the constructed charge-averaged clock-floor propagator satisfy the transformed weak Schrodinger equation for every real time. Let Q(clock)=exp(clock)+epsilon*clock, M_t=exp(-2*i*t*Q/h), phi(t)=M_t^(-1)*U(s,t)*Jw, and let v belong to the full completed reference energy form with Jv in the maximal self-adjoint chart-multiplier domain and chart output g=Q*Jv. The proved scalar derivative is d<phi(t),Jv>/dt=(i/h)*(<P_F*A0*phi_form(t),P_F*A0*v>+exp(2*t)*<P_K*A0*phi_form(t),P_K*A0*v>-2*<phi(t),g>), with inner products conjugate-linear in the first argument, P_K selecting energy outputs 3,4 and P_F the remaining six. The transformed reference form state is constructed and its embedding equals phi(t). The phase preserves the actual physical density, and the initial transformed state is M_s^(-1)*Jw. The moving-test chain rule and phase derivative are proved by difference quotients and dominated L2 convergence; chart-domain membership or a Hamiltonian operator domain is not assumed for the evolving state. The unbounded -2Q term is derived on tests, not omitted. Explicit coherent states prove that the allowed physical test vectors are Hilbert-dense. Density in the energy or transformed operator graph norm is not claimed. Existing hypotheses epsilon>0,h!=0,abs(h)<=2*pi*epsilon/3 are retained, with arbitrary real mass/quartic/vacuum coefficients under the existing Real.sqrt convention and no zero-charge restriction. Initial data lie in the completed energy form; the density identity itself covers all physical Hilbert initial states. This promotes the previous instantaneous full-energy gauge identity to an equation along the actual physical evolution. It does not construct a new self-adjoint transformed operator or prove strong transformed dynamics, chart-moment propagation, positive-clock escape, momentum propagation or clock recovery. The two exp(2t) transverse kinetic contributions remain. Regulator removal, controlled physical limits, Standard Model/GR identification, octonion necessity and a physical TOE remain unproved. No necessary Hamiltonian revision or new numerical evidence is asserted.')
    target = root / "data/quantum_gauge_weak_dynamics_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()
