#!/usr/bin/env python3
"""Audit full Hamiltonian square domains and exact confluent cooling moments."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalIndependentRadialCoordinateMoments', 'KFCausalIndependentRadialBareMultiplier', 'KFCausalIndependentRadialMomentClock', 'KFCausalJointSourceConfluenceIntegrability', 'KFCausalConfluentThreePhysicalClockLoss', 'KFCausalIndependentRadialMomentInput', 'KFCausalIndependentRadialShiftedField', 'KFCausalFiniteSecondHamiltonianColumns', 'KFCausalChargedCoolingConfluentThreeCoercivity', 'KFCausalChargeProfileMomentumGraph', 'KFCausalFiniteMonomialDerivative', 'KFCausalChargeRepresentativeAlgebra', 'KFCausalIndependentRadialInsertions', 'KFCausalChargedCoolingConfluentThreeDissipation', 'KFCausalChargedCoolingConfluentMoments', 'KFCausalIndependentRadialMonomialDerivative', 'KFCausalIndependentRadialMomentMultiplier', 'KFCausalIndependentRadialPolynomialMomentum', 'KFCausalIndependentRadialMomentRegularity', 'KFCausalIndependentRadialPolynomialKinetic', 'KFCausalIndependentRadialMomentExponential', 'KFCausalIndependentRadialMomentKinetic', 'KFCausalIndependentRadialKineticRepresentatives', 'KFCausalIndependentRadialMomentMatterGraph', 'KFCausalIndependentRadialProjectedKinetic', 'KFCausalIndependentRadialMomentHamiltonian', 'KFCausalIndependentRadialKineticOutputIdentity', 'KFCausalFiniteKineticHamiltonianColumns', 'KFCausalFiniteHamiltonianSquare']
NAMESPACES = {}
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--overlay", required=True, type=Path)
    parser.add_argument("--baseline-overlay", required=True, type=Path)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    overlay = args.overlay.resolve()
    baseline = args.baseline_overlay.resolve()
    assert baseline.is_dir() and baseline != overlay
    assert overlay.is_dir() and "LEAN_PATH" in os.environ
    env = os.environ.copy()
    env["LEAN_PATH"] = str(overlay) + os.pathsep + str(baseline) + os.pathsep + env["LEAN_PATH"]
    logs = overlay / "quantum-radial-hamiltonian-confluent-cooling-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_clock_domain_joint_confluence_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "dcebd5c79260e07528e513c9d3f08ed8d9cf1f6fc0a91b994104b65d777f47cc"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_radial_hamiltonian_confluent_cooling_audit.py",
        "scripts/verify_quantum_radial_hamiltonian_confluent_cooling.py",
    ]
    hashes = dict(previous['source_sha256'])
    assert len(hashes) == 3067
    assert all(sha(root / p) == h for p, h in hashes.items())
    assert not set(additions) & set(hashes)
    hashes.update({p: sha(root / p) for p in additions})
    analytic_path = root / "data/quantum_fixed_v_charged_cooling_analytic.txt"
    analytic_hash = sha(analytic_path)
    assert analytic_hash == "38bb567709bcba710996d3b1d8302facb8df7cb7063723189bb642040c99225d"
    obstruction_path = root / "data/quantum_quartic_imaginary_contraction_obstruction.txt"
    obstruction_hash = sha(obstruction_path)
    assert obstruction_hash == "c2b84b9d756700d949ebc9687144f4812bf8cf151d0fa7715c9f1491ea4556df"
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
        # English in the opening module comment is not executable Lean.
        source_body = re.sub(r'\A/-.*?-/', '', text, count=1, flags=re.S)
        assert not re.search(r'\b(sorry|admit|axiom|unsafe)\b', source_body)
        command = ["lean", "-j1", "-o", str(overlay / "UnifiedTheory/Audit" / (name + ".olean")), source]
        result = subprocess.run(command, cwd=root, env=env, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        log = logs / (name + ".log")
        log.write_text(result.stdout)
        assert result.returncode == 0 and not re.search(r": error|: warning|sorryAx|PANIC", result.stdout), str(log)
        parsed = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", result.stdout)
        audits = {n: sorted(s.strip() for s in xs.split(",") if s.strip()) for n, xs in parsed}
        expected = {"UnifiedTheory.Audit." + NAMESPACES.get(name, name) + "." + n for n in re.findall(r"^#print axioms (\S+)", text, re.M)}
        declared = {"UnifiedTheory.Audit." + NAMESPACES.get(name, name) + "." + n for n in re.findall(r"^theorem (\S+)", text, re.M)}
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
    assert sha(analytic_path) == analytic_hash
    assert sha(obstruction_path) == obstruction_hash
    for name in MODULES:
        assert not (root / ".lake/build/lib/lean/UnifiedTheory/Audit" / (name + ".olean")).exists()
    report = dict(
        new_lean_theorem_count=sum(len(c["audited_declarations"]) for c in checks),
        modules=checks, source_sha256=hashes, numerical_evidence=evidence,
        analytic_evidence=dict(path=str(analytic_path.relative_to(root)), sha256=analytic_hash,
                               status="Analytic derivation; not a Lean-verified theorem; moving field estimate remains open"),
        analytic_obstruction=dict(path=str(obstruction_path.relative_to(root)), sha256=obstruction_hash,
            status="Exact analytic counterexample to pure quartic imaginary contraction; not Lean verified; not a counterexample to the uniform response bound"),
        previous_report=dict(path=str(previous_path.relative_to(root)), sha256=previous_hash),
        root_check=dict(command=["lean", "-j1", "UnifiedTheory.lean"], exit_code=0,
                        empty_log=True, source_sha256=root_hash, log_sha256=sha(log),
                        appended_imports=MODULES),
        lean_toolchain=(root / "lean-toolchain").read_text().strip(),
        scope='179 Lean theorems in 29 successor modules. The original finite sourced reciprocal packet family now lies in the actual full interacting averaged Hamiltonian square domain: H psi is in Dom(H), with an actual composition H H graph witness. All eight projected natural second outputs have derived Hamiltonian domains, including the four previously missing kinetic inputs. Assumptions are epsilon>0, h nonzero, positive clock Gaussian widths, charged widths at least one, and abs(h)<=epsilon/10; arbitrary complex neutral sources and packet coefficients, neutral polynomials, real clock frequencies, and all original coupling/time parameters are retained. The larger independent-width family has actual coordinate-polynomial kinetic graphs, complete matter and vacuum graphs for every radial degree, and full Hamiltonian graphs for its left/right radial moments and their physical clock and inverse-clock multiples. Exact projected kinetic identities retain the neutral second derivative and both inverse half-clock factors. Separately a repeated-width charged jet of order at most two has a quantitative one-sixteenth finite matrix cooling lower bound and its full nonnegative remainder; every Gram entry is identified with an actual Gaussian times positive-halfline moment integral. The genuine fixed-order joint confluence density and response have derived full-Joint integrability, and the associated scalar physical-clock loss obeys (48+331776/alpha)*fraction. These matrix, moment and scalar results do not yet establish the full integrated N=2 response inequality; polynomial marginal/derivative and dilation attachment are subsequent work. The unrestricted-width response inequality, a bound uniform in confluent order, evolved BH/HB control, graph-core and controlled physical limits, independent physical identification and the physical TOE remain open. No necessary model revision is established. All 3067 parent source/script hashes and 23 numerical evidence files are preserved; 29 modules and 2 scripts give 3098 hashes and the root extends 8719 to 8748 lines. Standard axioms only.')
    target = root / "data/quantum_radial_hamiltonian_confluent_cooling_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

