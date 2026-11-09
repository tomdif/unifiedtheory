#!/usr/bin/env python3
"""Audit persistent weighted clock mass and necessary negative spectral escape."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalClockFloorWeightedClockControl', 'KFCausalClockFloorPersistentWeightedClock', 'KFCausalClockFloorLocalizedSpectralSplit', 'KFCausalClockFloorSelectedWeightedClock', 'KFCausalClockFloorSelectedNegativeEscape']
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
    logs = overlay / "quantum-negative-momentum-escape-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_localized_spectral_detection_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "a8ecb969755b4d545dc480d7a536be9e37f3ee14a014846f6df7df35484600a8"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_negative_momentum_escape_audit.py",
        "scripts/verify_quantum_negative_momentum_escape.py",
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
        scope='For the actual bounded weight H=C^(-1/2)D(1-D), the new physical multiplier identity proves its scalar coefficient strictly positive and continuous. Its positive minimum on a finite clock band gives a defect-control inequality with both clock tails retained. Combining the existing uniform negative-clock-tail bound, the large-clock decay of the defect, and the actual residual lower bound proves: for EVERY physical Hilbert-space initial state with positive residual, there is eta>0 such that norm(H psi(t))>=eta at every forward physical time. This result does not need finite energy, normalization, moments or positive vacuum coupling. The weight H commutes with the physical charge action, derived from the actual defect and inverse-half-clock intertwinings. No charge invariance of the coupled momentum is used. The bounded upper and lower coupled-Fourier half-space observations on the full angle-L2 charge orbit have an exact squared-norm sum equal to norm(H f)^2. The lower observation has the exact orbit-integral interpretation on symbol<R. Uniform actual-versus-full-frozen physical comparison transfers the derived positive H-norm lower bound to selected frozen windows. For every full finite-energy initial state, positive initial fast time a, epsilon>0,h!=0,abs(h)<=2*pi*epsilon/3,k>0 and arbitrary real m,g, a positive actual residual implies one sequence U_n,L_n and one c>0, independent of the threshold R, with U_n,L_n tending to infinity,L_n^2/U_n tending to infinity,L_n/U_n tending to zero, and uniform actual-versus-full-frozen physical error tending to zero. On these SAME windows the TOTAL upper spectral mass tends to zero for each fixed real R, while for every real R the lower spectral mass averaged over [0,L_n] is at least c for all sufficiently large n. The threshold for n may depend on R. A final theorem gives the derived alternative: actual clock recovery OR this selected-window negative spectral escape. This establishes a necessary consequence of failure, not occurrence or exclusion of failure. The mass is inverse-half-clock times D(1-D) weighted coupled momentum, with all charge angles retained; it is not unweighted probability, canonical momentum or pure-clock momentum. The lower average is over fast time of the full frozen flow, whose inputs are actual evolved states; it is not a proved actual-flow average. Full static factors remain and physical window durations still shrink. No pointwise spectral escape, universal rate, threshold-uniform convergence, negative-tail propagation exclusion, clock recovery, necessary model revision, regulator removal, controlled physical limit, SM/GR identification, octonion necessity or physical TOE is established. All 1997 parent source/script hashes and inherited numerical evidence remain unchanged; no new numerical evidence or .lake artifacts.')
    target = root / "data/quantum_negative_momentum_escape_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

