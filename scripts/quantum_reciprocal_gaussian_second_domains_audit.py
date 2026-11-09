#!/usr/bin/env python3
"""Audit reciprocal Gaussian second-factor domains and the exact strong-Hamiltonian reduction."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalClockFloorVacuumSquare', 'KFCausalGaussianVacuumSquare', 'KFCausalGaussianMomentumVacuumSquare', 'KFCausalReciprocalGaussianVacuumSquare', 'KFCausalGaussianSecondMomentum', 'KFCausalClockFloorKineticSquare', 'KFCausalGaussianKineticSquare', 'KFCausalGaussianClockSquare', 'KFCausalKineticSquareClockOutput', 'KFCausalReciprocalGaussianClockKineticSquare', 'KFCausalJointSecondPairing', 'KFCausalEnergyReverseFactors', 'KFCausalFixedStrongHamiltonian', 'KFCausalReciprocalGaussianStrongReduction']
NUMERICAL_SOURCES = {'scripts/neutral_hermite_response_probe.py': '5eb4b34486dd823ebdac3f167b60da0abe1723b3d2a72c6feafd6ced4195ec21', 'scripts/verify_neutral_hermite_response.py': '4d774c57ed1c8a251ceb493314b951edf734e8ccc26d829e902026b5fb60de2d'}
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
    logs = overlay / "quantum-reciprocal-gaussian-second-domains-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_reciprocal_gaussian_response_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "7dbe15a5d5d278f524c29caf7597a09a73ba5b3919bcf89081fed8dab7e0ee5a"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_reciprocal_gaussian_second_domains_audit.py",
        "scripts/verify_quantum_reciprocal_gaussian_second_domains.py",
    ]
    assert all(sha(root / p) == h for p, h in NUMERICAL_SOURCES.items())
    hashes = dict(previous["source_sha256"])
    assert all(sha(root / p) == h for p, h in hashes.items())
    assert not set(additions) & set(hashes)
    hashes.update({p: sha(root / p) for p in additions})
    evidence = dict(previous["numerical_evidence"])
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
        scope='The actual reciprocal charged Gaussian with w>=1 and its actual zero-charge clock momentum have constructed second graphs for the clock factor, all four transverse kinetic factors and the ordered vacuum exponential under epsilon>0, positive Gaussian clock width, nonzero h and the sufficient tighter condition abs(h)<=pi*epsilon/3. The vacuum proof uses the full longitudinal exponential: the natural reverse product D Ehalf Ehalf D is characterized by Efull acting on Df, and is included in the actual T-adjoint T graph. The doubled-parameter Gaussian Fourier theorem supplies the full exponential graph; clock momentum is handled by its explicit output map. Kinetic second graphs are derived from actual first and second directional Gaussian derivatives and L2 polynomial moments, then transported by the reciprocal squeeze together with the second clock graphs. A general zero-charge strong-Hamiltonian criterion extends exact forward/reverse pairings through the joint graph closure and the full charge-averaged form using the bounded mean map. Its Hamiltonian output is the charge projection of the weighted sum of second factor outputs. For the actual reciprocal state and its actual momentum, this sufficient criterion leaves exactly two unproved reverse matter graph obligations each, for factors 5 and 6. These individual reverse graph conditions are not claimed necessary for membership in the sum Hamiltonian domain. These obligations are stated explicitly as premises; no complete interacting Hamiltonian operator-domain membership is claimed. The ordered expressions still requiring graph proofs are D Ehalf Phi^2 Ehalf D and D Ehalf Phi^4 Ehalf D, with operator order retained. Pointwise L2 decay alone does not prove these exponential domains. The earlier individual-packet uniform response bound is preserved, including its original weaker strip abs(h)<=2*pi*epsilon/3; no state-uniform estimate for superpositions of distinct widths is added. The tighter sufficient strip is not asserted necessary or optimal. Matter second domains, interference between widths, graph-core density, evolution invariance, trajectory momentum regularity and response identity, unconditional clock recovery, controlled physical/regulator limits, SM/GR identification, octonion necessity and a physical TOE remain open. No necessary model revision is established. All 73 public theorem dependency lists in 14 modules use only standard axioms. All 2306 parent source/script hashes are preserved in 2322 entries. Exactly 14 imports extend the 8104-line parent root to 8118 lines; inherited numerical evidence is unchanged and no new .lake artifacts are generated.')
    target = root / "data/quantum_reciprocal_gaussian_second_domains_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

