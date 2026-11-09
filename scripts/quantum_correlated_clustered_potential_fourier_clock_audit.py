#!/usr/bin/env python3
"""Audit exact potential Fourier slices, full clock jets and charged Gaussian envelopes."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalShiftedNarrowFourierGeometry', 'KFCausalShiftedNarrowFourierSlices', 'KFCausalCorrelatedClusteredShiftedNarrowProfiles', 'KFCausalShiftedNarrowFourierClockDerivative', 'KFCausalCorrelatedClusteredShiftedNarrowJet', 'KFCausalCorrelatedClusteredPotentialFourierClock', 'KFCausalShiftedNarrowFourierClockBounds', 'KFCausalShiftedNarrowFourierChargedEnvelope']
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
    logs = overlay / "quantum-correlated-clustered-potential-fourier-clock-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_correlated_clustered_clock_kinetic_second_derivatives_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "26fdddd3798f381d94c5cd67554cde103690cf97abfaa865b2202864b0340bab"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_correlated_clustered_potential_fourier_clock_audit.py",
        "scripts/verify_quantum_correlated_clustered_potential_fourier_clock.py",
    ]
    hashes = dict(previous['source_sha256'])
    assert len(hashes) == 2703
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
        scope='Fifty-six Lean theorems give the exact two-dimensional narrow Fourier integrals of the original correlated clustered mixed-shift physical profiles, including arbitrary neutral complex sources and polynomials, arbitrary field powers and independent Gaussian clock amplitudes and frequencies. The complex Gaussian coefficient has positive real part throughout the original admissible imaginary strip. Its exact normalization is pi/(alpha*r^2) times the original reciprocal width. After summing the original clustered width coefficients, the Fourier integral is an explicit charged difference quotient times the full neutral and mixed-field coefficient. The pointwise limit and the full clock derivative are proved, retaining derivatives of normalization, charged radius, neutral profile and distinct field shift. Actual shifted clock amplitudes and scale velocities discharge every generic derivative hypothesis. The derivative of the original finite Fourier integral and the derivative of the limiting explicit profile converge pointwise; the normalized clock expression retains the half-density correction. Spacing-independent pointwise envelopes are derived. The charged Fourier radius obeys a uniform lower bound L*R on its real part and upper bound M*R on its norm, with L=exp(-pi/3)/2 and M=exp(pi/3), throughout the entire real clock and imaginary strip. Its normalized clock derivative is bounded by (2/epsilon)*M*R. Gaussian absorption yields explicit envelopes for the clustered charged factor and its normalized clock derivative, independent of clock position and spacing, with degree-dependent constants. These are Fourier integrals on transverse slices and pointwise differentiated limits, not a new full-Hilbert B H graph theorem. The remaining steps include the full joint L2 estimate with the moving neutral and field factors, the general partial-Fourier representative and differentiation bridge for actual Hilbert vectors, and convergence of the projected joint potential derivative remainder. The arbitrary-neutral-profile uniform energy-relative response, graph-core density, dynamics, physical limits, physical identification and TOE remain open. Existing H and H B domains and five B-second-action domains are preserved. No interaction is removed, no model revision is inferred, no numerical evidence is used as a proof premise. All 2703 parent source hashes and 23 numerical files are preserved; ten successor sources/scripts give 2713 hashes. Eight imports extend the root from 8409 to 8417 lines. Standard axioms only and no new .lake artifacts.')
    target = root / "data/quantum_correlated_clustered_potential_fourier_clock_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

