#!/usr/bin/env python3
"""Audit full-time spectral decay, physical variation and the Hilbert-state escape alternative."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalExponentialSquareNoSpikes', 'KFCausalClockFloorPhysicalVariation', 'KFCausalDenseObservationDecay', 'KFCausalClockFloorFullTimeSpectrum', 'KFCausalClockFloorFullTimeNegativeEscape']
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
    logs = overlay / "quantum-full-time-spectrum-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_pointwise_spectral_escape_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "92e06f5b6ed5249ad02f7ba14c62c97ea0e417e94f1c8727c36abc71c7f15a03"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_full_time_spectrum_audit.py",
        "scripts/verify_quantum_full_time_spectrum.py",
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
        scope='The new result derives FULL-TIME decay of every fixed bounded localized upper coupled spectral observation along the ACTUAL full dynamics, and extends it from finite-energy initial data to every physical Hilbert initial vector. A generic no-revival theorem allows squared variation bounded by K exp(2b)(b-a); a finite tail dissipation budget and exp(2t)-scaled detection then force decay. For actual finite-energy trajectories, restarting the established weak pairing variation estimate at each earlier time and using decreasing rescaled energy yields ||E(s,b)Jv-E(s,a)Jv||^2 <= C(s,v) exp(2b)(b-a), s<=a<=b, with C=2|1/h|exp(-2s)(2 timeEnergy(s,v)+1). No strong physical derivative, Hamiltonian operator-domain preservation or propagated momentum moment is used. Exact rescaling proves actual dissipation d(s,t,v)=2 exp(2t) detector(formFlow(s,t,v)). The existing spectral observation bound therefore gives exp(2t)||B_R E(s,t)Jv||^2 <= (64 epsilon exp(-R)/k) d(s,t,v). This supplies detection in the no-revival theorem and proves B_R E(s,t)Jv->0 at ALL late physical times. A separate bounded-observation density argument using unitarity removes finite initial energy from the decay conclusion. For any Hilbert initial f, lower mass ||N_R E(s,t)f||^2 minus total weighted mass ||H E(s,t)f||^2 tends to zero for every fixed R. If the actual residual is positive, one c>0 gives total weighted mass>=2c at all forward times and lower mass below every fixed R>=c for all sufficiently late physical times. The eventual time may depend on R; c does not. Final alternative: clock recovery OR full-time negative spectral escape, for arbitrary Hilbert initial data and arbitrary real initial physical time s. The exact eventual-negative-tail-tightness criterion is accordingly extended to arbitrary Hilbert data, and recovery is also equivalent to decay of the lower observation at some single fixed threshold. None of these theorems proves that the dynamics supplies the needed lower-tail decay. All observations retain the full physical charge-angle L2 orbit and H=C^(-1/2)D(1-D) before the actual coupled Fourier restriction. This is neither raw probability nor pure-clock/canonical-momentum escape. It is no longer merely averaged or subsequential, but no threshold-uniform convergence or quantitative escape rate is asserted. Assumptions epsilon>0,h!=0,|h|<=2pi epsilon/3,k>0,arbitrary real m,g; all static factors retained. The Hilbert variation and detection estimates themselves are on full finite-energy states; only the bounded observation limits and alternatives are extended by density. The coherent-span vacuum shear sign was already proved; no new extension of it or signed matter control is assumed here. Clock recovery without a tail premise, an actual failing trajectory, necessary model revision, regulator removal, controlled physical limits, SM/GR identification, octonion necessity and physical TOE remain unproved. All 2015 predecessor source/script hashes and numerical evidence preserved; no new numerical evidence or .lake artifacts.')
    target = root / "data/quantum_full_time_spectrum_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

