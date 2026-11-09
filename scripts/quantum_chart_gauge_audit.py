#!/usr/bin/env python3
"""Audit exact chart-phase covariance of the full averaged energy form."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalClockFloorChartModulation', 'KFCausalClockFloorExponentialModulation', 'KFCausalClockFloorFactorChartModulation', 'KFCausalClockFloorClosedChartModulation', 'KFCausalClockFloorAveragedChartModulation', 'KFCausalClockFloorGaugeEnergy']
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
    logs = overlay / "quantum-chart-gauge-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_left_clock_tightness_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "40a39622eec153e1715be699e51431b0193996cd834d49edfca16365737de949"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_chart_gauge_audit.py",
        "scripts/verify_quantum_chart_gauge.py",
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
        scope='Exact chart-phase covariance of the full completed charge-averaged eight-factor energy form, at fixed positive regulator epsilon, nonzero Planck parameter h and abs(h)<=pi*epsilon. The physical phase M_r multiplies by exp(2*pi*i*r*(exp(clock)+epsilon*clock)); it is unitary, preserves the physical clock density, and commutes with the constructed charge action. Its exact Fourier translation and maximal exponential graph covariance imply ordered-factor scaling exp(pi*h*r), while clock and transverse kinetic outputs have unitary covariance. These identities pass through the simultaneous joint graph closure, including zero energy coefficients, and through the actual charge-averaged form. With r=-t/(pi*h), all ordered matter and vacuum exp(t) output weights cancel exactly. For every state in the completed averaged energy form at time zero, the phase-transformed physical state is in the actual energy domain at t, with energy equal to the squared norm of its time-zero outputs in indices 0,1,2,5,6,7 plus exp(2*t) times the squared norm of the outputs in indices 3,4. The theorem covers the full form, not only trial states, the vacuum sector, or zero charge. Mass, quartic and vacuum parameters may be arbitrary real numbers with the existing Real.sqrt coefficient convention. This is an instantaneous form-domain and energy identity, not a transformed Schrodinger evolution theorem. The two transverse kinetic terms remain time dependent; a time-dependent phase also contributes an unbounded chart-coordinate term to the evolution generator, whose domain and propagation have not been proved here. The phase does not move clock probability and cannot by itself prove clock recovery. The preceding uniform negative-clock tail control and full-time zero-charge weak escape remain preserved with their own hypotheses. Positive-clock escape, quantum momentum propagation, regulator removal, controlled physical limits, Standard Model/GR identification, octonion necessity and a physical TOE remain unproved. No necessary Hamiltonian revision or new numerical evidence is asserted.')
    target = root / "data/quantum_chart_gauge_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()
