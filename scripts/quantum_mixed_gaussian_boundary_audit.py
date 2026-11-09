#!/usr/bin/env python3
"""Audit actual mixed Gaussian square domains and the Gamma boundary form."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalComplexShearGroup', 'KFCausalBroadPairedGaussianSecondInput', 'KFCausalChargeRotatedSecondInput', 'KFCausalSingleGaussianSecondInput', 'KFCausalGaussianPhysicalShearIdentity', 'KFCausalMixedStripTailAttachment', 'KFCausalSingleGaussianHolomorphicQuotient', 'KFCausalSingleGaussianHolomorphicContinuity', 'KFCausalSingleGaussianNormalizedDensity', 'KFCausalBroadPairedHolomorphicBaseline', 'KFCausalSingleGaussianMixedSquare', 'KFCausalSingleGaussianCharge', 'KFCausalSingleGaussianTwoAngleSquare', 'KFCausalJointFourierBoundaryGammaForm', 'KFCausalJointFourierBoundaryGammaPositive']
NAMESPACES = {'KFCausalSingleGaussianHolomorphicContinuity': 'KFCausalSingleGaussianHolomorphicQuotient'}
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
    logs = overlay / "quantum-mixed-gaussian-boundary-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_boundary_clock_ratio_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "87653cd8bf8f81c0026b4ef20d6b9de33ee7dc9b66e240a502c394cba9939bd3"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_mixed_gaussian_boundary_audit.py",
        "scripts/verify_quantum_mixed_gaussian_boundary.py",
    ]
    hashes = dict(previous['source_sha256'])
    assert len(hashes) == 2875
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
        scope='78 Lean theorems in fifteen successor modules. For the actual unsourced width-one singleton Gaussian with zero clock frequency and abs(h)<=epsilon/10, construct Q(U_theta Q psi), its full natural exponential graph and the composition of two independently charge-conjugated vacuum squares at arbitrary angles. The direct multiplier is holomorphic without Re(q) in its definition, uniformly bounded, and matched exactly to the physical second input and broader paired Gaussian baseline. The physical Gamma(shape 3/2) normal-boundary integral is identified and nonnegative for every complex polynomial of degree at most two, using the proved actual-clock ratio. This is a local normal-boundary result, not the global signed response estimate. With the two preceding checkpoints this continuation adds 201 theorems in 34 modules. All 2875 parent source/script hashes and all 23 numerical files are preserved; fifteen modules and two scripts give 2892 source hashes, and the root extends from 8547 to 8562 lines. Standard axioms only; no new numerical evidence, .lake artifacts, harness changes, commit or push. Full mixed Hamiltonian H^2 domains, evolved BH/HB control, arbitrary-family uniform response, physical limits and external physical evidence remain open. No physical TOE or necessary model change is claimed.')
    target = root / "data/quantum_mixed_gaussian_boundary_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

