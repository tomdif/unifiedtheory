#!/usr/bin/env python3
"""Audit full joint L2 Fourier limits and normalized clock derivative estimates."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalShiftedNarrowJointGaussian', 'KFCausalShiftedNarrowJointMoments', 'KFCausalShiftedNarrowControlledFactors', 'KFCausalShiftedNarrowWeightedProfiles', 'KFCausalShiftedNarrowWeightedLimits', 'KFCausalShiftedNarrowNormalizedCoefficients', 'KFCausalCorrelatedClusteredJointFourierDecomposition', 'KFCausalCorrelatedClusteredJointFourierL2Data', 'KFCausalCorrelatedClusteredJointFourierL2Limit']
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
    logs = overlay / "quantum-correlated-clustered-joint-fourier-l2-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_correlated_clustered_potential_fourier_clock_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "06b1799fe952800fb7b01d19b2e795d67c877b880f535b053b39ac96102d1ed6"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_correlated_clustered_joint_fourier_l2_audit.py",
        "scripts/verify_quantum_correlated_clustered_joint_fourier_l2.py",
    ]
    hashes = dict(previous['source_sha256'])
    assert len(hashes) == 2713
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
        scope='Eighty-eight Lean theorems prove full joint L2 domination and strong convergence of the exact narrow Fourier integrals of the original correlated clustered mixed-shift physical profiles and their normalized clock derivative including the half-density correction. The exact common Gaussian retains the moving neutral source and shear; its broad/neutral factor is identified with the existing shear bound at a reconstructed configuration. A positive minimum width gives a fixed five-dimensional isotropic Gaussian throughout the full real clock and admissible imaginary strip. Every polynomial moment is square integrable. Normalized radius, field, neutral and normalization rates are controlled polynomial multipliers. The exact normalized coefficient separates the sole unbounded clock term into one actual shifted Gaussian clock moment, whose L2 integrability is proved. Charged difference quotients and their jets have spacing-independent joint L2 majorants. Actual independent Gaussian clock widths and frequencies discharge the generic hypotheses. Exact algebraic identities retain all correlated amplitudes, arbitrary neutral complex sources, polynomials and field powers, as well as distinct Gaussian and field shifts; no interaction or interference is discarded. Explicit finite and limiting Hilbert vectors represent the actual slice Fourier profiles and normalized clock expressions almost everywhere, and both sequences converge strongly as positive width spacing tends to zero. All integrability and domination conditions are derived from alpha>0, beta>0, 32*beta<=alpha, epsilon>0, the two original admissible shift bounds and positive clock widths. This closes the full joint L2 estimate left by the parent checkpoint. It does not yet identify these vectors with the actual mixedCoordinates unitary transform of the original Hamiltonian outputs or prove the required pure-clock generator graph commutation. Those operator identifications and the final bounded inverse-half factor are needed to apply the existing projected potential-remainder theorem and close full B H. The general-family uniform energy-relative potential response, graph-core density, dynamics, physical limits, physical identification and TOE remain open. The derived Gaussian constants may depend on the family, degree and source and are not a uniform response constant. Existing H and H B domains and five B-second-action domains are preserved. No model revision is inferred. No numerical evidence is used as a proof premise. All 2713 parent source hashes and 23 numerical files are preserved; eleven successor sources/scripts give 2724 hashes. Nine imports extend the root from 8417 to 8426 lines. Standard axioms only and no new .lake artifacts.')
    target = root / "data/quantum_correlated_clustered_joint_fourier_l2_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

