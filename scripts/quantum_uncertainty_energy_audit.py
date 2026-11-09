#!/usr/bin/env python3
"""Audit maximal-domain uncertainty and actual quantum energy divergence."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalCanonicalUncertainty', 'KFCausalChargeDualMomentumDomain', 'KFCausalMultiplierMomentBound', 'KFCausalClockFloorWeightedUncertainty', 'KFCausalClockFloorUncertaintyEnergy', 'KFCausalClockFloorQuantumEnergyGrowth']
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
    logs = overlay / "quantum-uncertainty-energy-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_chart_clock_drift_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "c51e52f659a93fbb37e4124c2736c808f5d4a11c4b56358328df22ed69d518c3"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_uncertainty_energy_audit.py",
        "scripts/verify_quantum_uncertainty_energy.py",
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
        scope='For the actual full charge-averaged clock-floor dynamics with epsilon>0, h!=0, abs(h)<=2*pi*epsilon/3 and arbitrary real m/g/k under the existing Real.sqrt weight convention, every initial vector w in the completed reference energy form satisfies E(s,t,w)>=sqrt(abs(h)/8)*exp(t/2)*norm(Jw)^2 for all real s,t. Thus every nonzero physical initial state in this form domain has energy tending to infinity as t tends to infinity. There is no zero-charge restriction, positive-vacuum premise, initial left/chart moment premise or Hamiltonian operator-domain premise. A full-domain canonical uncertainty inequality is proved using translation covariance; no domain for products of position and momentum operators is assumed. The reverse maximal momentum graph characterization in the complementary partial Fourier representation follows from proved self-adjointness. Previously derived charged and complementary moment integrability constructs an actual canonical pair on C^(-1/2)f. This yields abs(h)*norm(C^(-1/2)f)^2<=4*exp(-t)*E_t(f) on every completed energy-form state, and abs(h)*exp(t)*norm(f)^4<=8*E_t(f)^2 by the actual half-clock factor. The full original energy is used and no factors are removed. The long-time energy lower bound is unconditional on this class, but it is not probability escape, divergence of mean clock, quantum clock-error decay, a sharp energy asymptotic, pure momentum propagation or regulator removal. In particular no sub-exp(t) energy upper bound is proved; the previously proved upper bound permits exp(2t) growth. Physical limits, Standard Model/GR identification, octonion necessity and a physical TOE remain unproved. No necessary Hamiltonian revision or new numerical evidence is asserted.')
    target = root / "data/quantum_uncertainty_energy_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

