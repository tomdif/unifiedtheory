#!/usr/bin/env python3
"""Audit bounded observation averages and spectral escape along the actual trajectory."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalUniformObservationAverages', 'KFCausalClockFloorActualObservationAverages', 'KFCausalClockFloorActualSpectralEscape']
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
    logs = overlay / "quantum-actual-spectral-escape-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_negative_momentum_escape_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "f53513293c616c296d8411d7dede9b4b9a79b8acbf9e4f285fdfe799a3bea854"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_actual_spectral_escape_audit.py",
        "scripts/verify_quantum_actual_spectral_escape.py",
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
        scope='The spectral escape alternative is transferred from frozen comparison trajectories to the ACTUAL full physical trajectory. A generic bounded-observation estimate proves abs(norm(Ax)^2-norm(Ay)^2)<=norm(A)^2*(norm(x)+norm(y))*norm(x-y). Uniform Hilbert-space comparison and uniform norm bounds therefore imply convergence to zero of the difference of normalized squared-norm observation averages on [0,1]. The actual trajectory is proved continuous on each positive fast-time window, and the full frozen trajectory is continuous. Exact change of variables identifies the normalized integral in r with (1/L) times the integral in fast-time offset t in [0,L]. This is valid for any fixed bounded complex-linear observation and any physical Hilbert initial state when the comparison hypotheses hold. Applying the parent selected-window construction to full finite-energy data gives, for k>0, one pair U_n,L_n with U_n,L_n tending to infinity,L_n^2/U_n tending to infinity,L_n/U_n tending to zero. For every fixed real R, the ACTUAL upper coupled-longitudinal spectral observation average tends to zero. If the actual clock residual is positive, there is one c>0, independent of R, such that for every fixed R the ACTUAL lower spectral observation average is at least c for all sufficiently large n. The eventual index may depend on R, while U,L,c do not. The observations retain the full physical charge orbit and apply C^(-1/2)D(1-D) before the existing coupled Fourier half-space restriction. The final theorem gives actual clock recovery OR this actual-trajectory spectral escape on the derived windows. It does not select a branch. Assumptions are epsilon>0,h!=0,abs(h)<=2*pi*epsilon/3,k>0, arbitrary real m,g, positive initial fast time a, and arbitrary full finite-energy initial data. No normalization, momentum moment or evolved Hamiltonian-domain assumption is added. The averages are normalized FAST-time averages, not physical-time averages or new total-integral decay statements for the actual flow. Full static factors remain; physical window durations still shrink. No unweighted-probability, pure-clock/canonical-momentum, pointwise-in-time or threshold-uniform spectral limit is proved. Excluding the negative spectral behavior, clock recovery, a necessary model revision, regulator removal, controlled physical limits, SM/GR identification, octonion necessity and the physical TOE remain unproved. A possible shear-exponential factorization route is a research direction only and is not used in any theorem. All 2004 predecessor source/script hashes and numerical evidence are preserved; no new numerical evidence or .lake artifacts.')
    target = root / "data/quantum_actual_spectral_escape_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

