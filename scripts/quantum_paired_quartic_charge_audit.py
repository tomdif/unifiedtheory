#!/usr/bin/env python3
"""Audit the corrected quartic charge state, source domains and completed Hamiltonian form."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalGaussianQuarticFourier', 'KFCausalQuarticChargeAlgebra', 'KFCausalFiniteLpRepresentatives', 'KFCausalQuarticTensorStates', 'KFCausalQuarticChargeProfiles', 'KFCausalContinuousChargeDetection', 'KFCausalPairedQuarticCharge', 'KFCausalPairedQuarticPolarization', 'KFCausalPairedQuarticDomain', 'KFCausalPairedQuarticIndependence', 'KFCausalPairedQuarticHamiltonian']
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
    logs = overlay / "quantum-paired-quartic-charge-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_paired_span_mixed_clock_full_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "5f9b8e59b855ce219590042330ccf4de66e1560ff04e6bb965e0e411f8cda642"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_paired_quartic_charge_audit.py",
        "scripts/verify_quantum_paired_quartic_charge.py",
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
        scope='Lean constructs the actual nonzero quartic state Q4(q)*psi0, where P(q)=q0*q1-q2*q3, S(q)=q0^2+q1^2+q2^2+q3^2, alpha=1/(2*abs(h)) and Q4=P^2-S/(4*alpha)+1/(8*alpha^2). Exact Gaussian Fourier moments through degree four and finite tensor representatives identify its actual physical charge coordinates. The resulting polynomial multiplier is imbalance^2/4-radius/(4*alpha)+1/(8*alpha^2), which is invariant under the physical charge circle. The state therefore has zero standing charge and is fixed by the charge projection. The bare P^2 Gaussian state instead has a proved nonzero quarter-turn defect and does not belong to the zero-charge sector. A continuous-representative criterion connects these pointwise computations to actual Hilbert-space charge invariance. The corrected state is not any complex linear combination of the centered and paired packets with the same clock profile. A proved 21-term directional polarization identifies the corrected tensor state with actual source-integral states, constructs its pure-clock momentum, all eight state and momentum factor graphs, and the clock composition graph. Momentum also has zero charge. Both states lift into the completed charge-averaged Hamiltonian form, with exact eight-factor energy and signed-response identities. Charge and Hilbert statements require epsilon>0, a>0 and h!=0; the factor and completed-form statements also require abs(h)<=2*pi*epsilon/3. No domain membership or desired charge conclusion is assumed. No lower response bound for the quartic or its superpositions has been proved here, and no dense or dynamically invariant larger class is claimed. Orthogonality to or exclusion from the previous independent-clock response closure is not claimed. Higher-degree control, actual trajectory momentum regularity, the moving-test response identity, negative-tail tightness, unconditional clock recovery, controlled physical/regulator limits, SM/GR identification, octonion necessity and the physical TOE remain open. This corrects a trial-state extension; no necessary revision of the physical model is established. Sixty-six public theorem dependency checks in eleven modules use only standard axioms. All 2246 predecessor source/script hashes and inherited numerical evidence are preserved in 2259 entries. Exactly eleven imports extend the 8054-line parent root to 8065 lines; no new .lake artifacts are generated.')
    target = root / "data/quantum_paired_quartic_charge_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

