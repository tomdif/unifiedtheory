#!/usr/bin/env python3
"""Audit full quantum energy-clock work and the classical fast-energy diagnostic."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalClockFloorVacuumEnergyGrowth', 'KFCausalClassicalVacuumFastEnergy', 'KFCausalClockFloorGrowingEnergySplit', 'KFCausalClockFloorEnergyClockWork', 'KFCausalClockFloorQuantumWorkAlternative']
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
    logs = overlay / "quantum-energy-clock-work-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_uncertainty_energy_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "e769fc5efd603ed97b72e4d391e9e9826a97ab23ab5eafe5f5d6b72681f1071a"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_energy_clock_work_audit.py",
        "scripts/verify_quantum_energy_clock_work.py",
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
        scope='For the actual full charge-averaged clock-floor propagator, with epsilon>0, h!=0, abs(h)<=2*pi*epsilon/3 and arbitrary real m/g/k under the existing Real.sqrt convention, every reference energy-form initial state with finite initial inverse-gap left moment satisfies (E(b)-2<Q>(b))-(E(a)-2<Q>(a))=2*integral_a^b K(t) dt for a,b>=s. Here K is precisely the squared norm of both actual growing transverse kinetic outputs (indices 3 and 4); Q is the existing chart coordinate exp(clock)+epsilon*clock. All eight energy factors remain in the original dynamics. The corrected energy has derivative 2K for t>s and is nondecreasing on [s,infinity). The output split and power identity hold on all reference form states without a moment restriction. Combining this identity with the previously proved unconditional energy divergence yields, for nonzero states in the moment class, the alternative <Q>(t)->infinity or integral_s^t K->infinity. If the mean clock is bounded by B, accumulated transverse work has the explicit lower bound (sqrt(abs(h)/8)*exp(t/2)*norm(Jw)^2-(E(s)-2<Q>(s))-2B)/2. Conversely, bounded accumulated transverse work would force mean-clock divergence; that boundedness is not proved. Separately, actual global zero-transverse classical vacuum trajectories at epsilon>0 and kappa>0 recover the clock defect while exp(-t)E(t)->infinity, with amplitude at least A(0)*exp(3t/2) for t>=0. This proves a classical diagnostic against treating sub-exp(t) total energy growth as necessary for recovery, not a quantum counterexample or a semiclassical correspondence. Neither branch of the quantum alternative is excluded; mean-clock divergence by itself does not prove probability escape. Quantum clock-error decay, a full matter shear/virial sign estimate, pure momentum propagation, regulator removal, physical limits, Standard Model/GR identification, octonion necessity and a physical TOE remain unproved. No necessary Hamiltonian revision or new numerical evidence is asserted.')
    target = root / "data/quantum_energy_clock_work_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

