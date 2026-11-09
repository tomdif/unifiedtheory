#!/usr/bin/env python3
"""Audit actual potential-output Hamiltonian domains and full source-labelled kernels."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalMixedInverseRepresentative', 'KFCausalSymmetricMixedTranslation', 'KFCausalSymmetricNormalizedDirection', 'KFCausalSymmetricInsertionAffine', 'KFCausalSymmetricDirectionBounds', 'KFCausalSymmetricDirectionRegularity', 'KFCausalSymmetricNumeratorJets', 'KFCausalTwoPolynomialSourceAbsorption', 'KFCausalSymmetricJetBounds', 'KFCausalSymmetricPhysicalJets', 'KFCausalSymmetricPhysicalJetMultiplier', 'KFCausalSymmetricPhysicalJetRegularity', 'KFCausalSymmetricMixedDerivativeGraph', 'KFCausalSymmetricKineticGraphAssembly', 'KFCausalSymmetricJetAction', 'KFCausalOuterSymmetricVacuumMatter', 'KFCausalFiniteOuterSymmetricVacuumMatter', 'KFCausalNaturalSecondHamiltonianGraph', 'KFCausalFinitePotentialHamiltonianDomain', 'KFCausalGaussianSourcePlaneKernel', 'KFCausalGaussianSourceJointKernel', 'KFCausalGaussianSourceKernelDerivative']
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
    logs = overlay / "quantum-potential-hamiltonian-source-kernel-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_clock_kinetic_hermite_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "13b8d8125aba65819f2b5d0018b5d6b482d8afd50130ab73670df82aa45ff9be"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_potential_hamiltonian_source_kernel_audit.py",
        "scripts/verify_quantum_potential_hamiltonian_source_kernel.py",
    ]
    hashes = dict(previous['source_sha256'])
    assert len(hashes) == 3015
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
        scope='132 Lean theorems in 22 successor modules. On the original finite sourced reciprocal packet families with epsilon>0, h nonzero, all clock widths positive, charged widths at least one and abs(h)<=epsilon/10, both symmetric kinetic squares after T=Q,S5,S6 have actual forward, reverse and composite graphs, including charge projection and independent angles. Their complete numerator is differentiated twice, retaining the neutral derivative in the second symmetric direction, and joint Gaussian bounds give actual L2 representatives. Projection uses closed primitive momentum graphs. Combining all eight natural second-component graphs proves that P0(T psi) lies in the original averaged Hamiltonian domain for each T=Q,S5,S6, with its output constructed and all original couplings retained. No full H-squared domain is asserted: component outputs after clock and kinetic inputs are still needed. Constants in these domain constructions may depend on packet data; uniform confluent graph limits and evolved BH/HB remain open. Separately the complete integrated sourced quartic Gaussian energy equals an exact finite source-labelled kernel for arbitrary finite charged widths and complex sources with neutral polynomial P=1. Its derivative along the actual clock and the exact dilation/cooling split retain every interference term. Energy positivity is proved, but the state-independent response positivity inequality and its polynomial-source extension remain open. The previously established integrated response bound still covers at most two distinct charged widths. Controlled physical limits and independent physical identification remain open; no physical TOE or necessary model revision is established. All 3015 parent source/script hashes and 23 numerical evidence files are preserved; 22 modules and 2 scripts give 3039 hashes and the root extends 8671 to 8693 lines. Standard axioms only.')
    target = root / "data/quantum_potential_hamiltonian_source_kernel_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

