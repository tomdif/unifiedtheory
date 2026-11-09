#!/usr/bin/env python3
"""Audit the neutral Fourier response split, frequency domains and actual moving marginal."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalNeutralFourierPairing', 'KFCausalNeutralFourierMomentum', 'KFCausalNeutralFourierResponseSplit', 'KFCausalNeutralFourierMovingJet', 'KFCausalNeutralFourierMovingEnvelope', 'KFCausalNeutralFourierMovingIntegral', 'KFCausalJointNeutralFourierMarginal']
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
    logs = overlay / "quantum-neutral-fourier-response-split-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_joint_neutral_fourier_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "6a3efba712b5bb7489ce1a94182ca86943017e5ce5e0ce9b9f78781fdd3fb176"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_neutral_fourier_response_split_audit.py",
        "scripts/verify_quantum_neutral_fourier_response_split.py",
    ]
    hashes = dict(previous['source_sha256'])
    assert len(hashes) == 2751
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
        scope='Fifty-two Lean theorems prove the weighted neutral Fourier field symmetry, frequency-moment domains and exact moving neutral marginal response for arbitrary finite Gaussian exponential-polynomial families. Complex cross-Plancherel is justified by actual L1 and L2 domains. The weighted field operator is symmetric on the packet spectra, and the integrated imaginary adjacent-field term vanishes. Spatial packet derivatives put k times the field spectrum in L2 and k times its squared norm in L1. The neutral response integral splits exactly into charged coefficient motion, real adjacent-field motion and a frequency moment, with no coefficient term discarded or bounded by assumption. Actual pointwise clock jets retain the charged chart derivative, real field shift and imaginary translation. Common local L2 envelopes for moving coefficients and geometry are constructed from the packet Gaussian decay and compactness; these may depend on the state and parameter interval and are not uniform response constants. Dominated differentiation proves the derivative of each neutral field energy and its Fourier representation. The original charged coefficients c_i*w_i*exp(-w_i*z(t)) are instantiated with their actual derivatives. The three quartic field powers combine to a rigorous derivative formula for the actual clock neutral marginal. This is a neutral-marginal integral theorem: passage through the outer charged integrations and identification with the full positive cooling form remain open. Existing full correlated-family BH and HB domain and strong commutator theorems remain unchanged; no graph-core or evolution-invariance assertion is added. The general state-independent energy-relative response estimate is still unproved, and no model revision or TOE is claimed. No numerical probe was run. All 2751 parent source hashes and 23 numerical files are preserved; seven successor modules and two scripts give 2760 hashes. Seven imports extend the root from 8447 to 8454 lines. Standard axioms only and no new .lake artifacts.')
    target = root / "data/quantum_neutral_fourier_response_split_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

