#!/usr/bin/env python3
"""Audit mixed field estimates and actual clustered quartic intermediate graph limits."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalShiftedNeutralCoercivity', 'KFCausalShiftedPolynomialClockWeights', 'KFCausalMixedFieldClockBounds', 'KFCausalMixedFieldClockCoefficients', 'KFCausalCorrelatedClusteredNeutralPowers', 'KFCausalCorrelatedClusteredMixedFieldTransfer', 'KFCausalCorrelatedClusteredMixedFieldLimits', 'KFCausalCorrelatedClusteredInputPotentialProfiles', 'KFCausalCorrelatedClusteredQuarticIntermediates', 'KFCausalCorrelatedClusteredQuarticLimit', 'KFCausalMixedFieldEstimateScope']
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
    logs = overlay / "quantum-correlated-clustered-quartic-intermediates-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_correlated_clustered_vacuum_seconds_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "5351c6b88884beeafd4406717d5060f4b05f1a3aa1a6f697a3a92cd540d166e2"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_correlated_clustered_quartic_intermediates_audit.py",
        "scripts/verify_quantum_correlated_clustered_quartic_intermediates.py",
    ]
    hashes = dict(previous['source_sha256'])
    assert len(hashes) == 2664
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
        scope='Sixty-three Lean theorems derive mixed field-power Cauchy estimates and close all four field-multiplication intermediate graphs for the two remaining matter reverse actions on the existing correlated clustered physical state and its actual pure-clock momentum. The reciprocal imaginary scale is bounded explicitly from the actual complex clock inverse. Every fixed polynomial clock weight is absorbed by the actual shifted Gaussian and momentum amplitudes; weighted continuity and L2 integrability are derived. Multiplication by a neutral-coordinate power is exactly a change of the neutral polynomial, preserving the full correlated width sum and its cancellations. A mixed shifted field is bounded by that neutral coordinate with a derived clock-dependent weight. The whole-clock Gram error then proves strong convergence of any actual finite Hilbert vectors with those exact representatives. This generic finite-representative premise is discharged for the new quartic intermediates: their domains follow from the existing original finite strong-Hamiltonian reverse graphs, and their physical representatives are proved explicitly. Both quartic sequences converge strongly; closed field-square graphs identify the limiting actions on the quadratic first outputs of psi and B psi. The linear reverse field steps are also identified, with the quadratic first outputs as their intermediate vectors. All four field-step domains are therefore proved. The subsequent longitudinal exponential on these intermediates, the two complete ordered matter second actions, their original finite-output limits, and the full interacting Hamiltonian graph remain open. The new field-domination coefficient is proved to be at least epsilon*pi/abs(y); direct domination by the neutral coordinate at real scale is disproved by an explicit transverse configuration. These are limitations of this comparison method, not counterexamples to the general Hamiltonian response estimate. The existing state-independent absolute clock/kinetic response bound remains proved, while the general-family uniform potential-response bound remains open. H B/B H convergence, graph-core density, dynamics, controlled physical limits, physical identification and the physical TOE remain unproved. No forced model revision or response-divergent sequence is claimed. All 2664 parent source hashes and all 23 numerical file hashes remain unchanged; thirteen additions give 2677 source entries. Eleven imports extend the root from 8376 to 8387 lines. Only standard axioms; no new .lake artifacts. No numerical result is a proof premise.')
    target = root / "data/quantum_correlated_clustered_quartic_intermediates_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

