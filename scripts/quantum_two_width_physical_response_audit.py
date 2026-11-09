#!/usr/bin/env python3
"""Audit full two-width spatial response, the three-width obstruction and physical field graphs."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalTwoWidthPhysicalClockLoss', 'KFCausalFiniteNeutralResponseIntegrability', 'KFCausalComplexVectorPolynomialAbsorption', 'KFCausalChargedCoolingMarginalDerivative', 'KFCausalChargedCoolingResponseMoments', 'KFCausalChargedCoolingThreeWidthObstruction', 'KFCausalChargedMarginalReordering', 'KFCausalUnboundedSpectatorFourier', 'KFCausalChargedCoolingResponseMarginal', 'KFCausalPhysicalSpectatorGraph', 'KFCausalPhysicalCoolingMarginal', 'KFCausalSourcedWidthFirstField', 'KFCausalTwoWidthCoolingMarginalBound', 'KFCausalFiniteSourcedFirstField', 'KFCausalTwoWidthIntegratedResponse']
NAMESPACES = {}
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
    logs = overlay / "quantum-two-width-physical-response-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_finite_sourced_mixed_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "6f7b515549f831a30af27d7ffc15723024f1d1207810e5a047b88ed9a9bb4bef"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_two_width_physical_response_audit.py",
        "scripts/verify_quantum_two_width_physical_response.py",
    ]
    hashes = dict(previous['source_sha256'])
    assert len(hashes) == 2924
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
        assert result.returncode == 0 and not re.search(r": error|: warning|sorryAx", result.stdout), str(log)
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
        scope='88 Lean theorems in 15 successor modules. The full original spatial quartic geometry response at the actual clock velocity is bounded above by (48+82944/alpha)*fraction(epsilon,s) times the original positive-density integral, for arbitrary finite complex coefficients, neutral sources and neutral polynomials whose charged widths take at most two values, both at least one, with positive alpha,beta and32*beta<=alpha. The fixed packet coefficients are held constant during the geometry derivative. Full response integrability, charged moments, exact original cooling marginal, measure-preserving Fubini reordering, dilation identity and physical clock loss are all proved or discharged by frozen theorems; no remaining integral assumption is substituted for the claim. Separately, an exact three-width actual-kernel quadratic form is negative for B-K/4 at widths1,21/20,11/10 and coefficients1,-2,1 with alpha=a=1,b=v=0, refuting extension of that pointwise constant, not the integrated response or the model. Arbitrary finite-vector polynomial/source factors are absorbed by the actual Gaussian strip margin. Exact maximal physical symmetric-position graphs under the mixed Fourier transform and actual L after Q graphs for every physical linear field and the original finite sourced packet family are constructed. No QLQ, full H^2, evolving BH/HB, confluent mixed-graph convergence, unrestricted-distinct-width global response or varying-longitudinal-amplitude totalResponse bound is asserted. Together with the preceding checkpoint this continuation adds229theorems in38modules. All2924parent source/script hashes and23numerical files are preserved;15modules and2scripts give2941source hashes and root extends8590to8605lines. Standard axioms only; no numerical data, .lake artifacts, harness changes, commit or push. Independent physical evidence and controlled limits remain open. No physical TOE or necessary model change is claimed.')
    target = root / "data/quantum_two_width_physical_response_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

