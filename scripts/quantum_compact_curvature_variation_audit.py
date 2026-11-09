#!/usr/bin/env python3
"""Audit actual compact curvature variations and growing-sector graph cores."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalClockFloorGrowingProjection', 'KFCausalGrowingCoreProjectedCoherent', 'KFCausalBDG4DCompactTensorFactors', 'KFCausalBDG4DCompactSymmetricTensor', 'KFCausalBDG4DQuadraticEulerProfiles', 'KFCausalMinkowski4DEulerQuadrant', 'KFCausalMinkowski4DVariationCone', 'KFCausalConformal4DRegularVolume', 'KFCausalBDG4DQuadraticVariationLimit', 'KFCausalBDG4DTemporalCurvatureLimit', 'KFCausalConformal4DRegularVolumeSmoothness', 'KFCausalConformal4DCompactKernelDerivative', 'KFCausalBDG4DActualTemporalVariation']
NAMESPACES = {}
FACTOR_THEOREMS = {'first_smooth', 'second_smooth', 'value_derivative', 'first_derivative',
                   'compact', 'outside_support', 'exists_bound', 'uniform_bound'}


def declaration_name(module, theorem):
    inner = 'Factor.' if module == 'KFCausalBDG4DCompactTensorFactors' and theorem in FACTOR_THEOREMS else ''
    return 'UnifiedTheory.Audit.' + NAMESPACES.get(module, module) + '.' + inner + theorem

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
    logs = overlay / "quantum-compact-curvature-variation-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_common_domains_lorentzian_variation_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "b1bf0a99c7f02b808f5b83415a934f3df0b3a7f6fe6d454c4b601e26edb349fe"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_compact_curvature_variation_audit.py",
        "scripts/verify_quantum_compact_curvature_variation.py",
    ]
    hashes = dict(previous['source_sha256'])
    assert len(hashes) == 3139
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
    frontier_path = root / "data/quantum_whole_response_mellin_frontier_20261021.txt"
    frontier_hash = sha(frontier_path)
    assert frontier_hash == 'f9e28fb65eb823d0ec5f9d8b44b4984e50580e05bd679e4d7a7b688742ca7390'
    pairing_path = root / 'data/quantum_charged_mellin_pairing_20261021.txt'
    pairing_hash = sha(pairing_path)
    assert pairing_hash == 'b6b472c6af208ccdd67214c196016de5439e98457a014e5380b5182063755d8a'
    extra_analytic = {'analytic_matrix_curvature': {'path': 'data/quantum_whole_response_matrix_curvature_20261021.txt', 'sha256': 'f6f4119d5f5736dd4a679addad5c548e1c8c6d372e277d56d6f4baa2ad4fbafd', 'status': 'Independently reviewed analytic identities, not Lean verified. Exact positive full-quartic Gram and connection decomposition retains all linked neutral derivatives. The required combined clock matrix inequality remains open.'}, 'analytic_width_floor_obstruction': {'path': 'data/quantum_width_floor_cooling_obstruction_20261021.txt', 'sha256': 'cdf4e33e91731885c718d4dee77b8fef418334dc29627e6fc7875c4ce11be459', 'status': 'Independently reviewed analytic obstruction, not Lean verified. Actual finite real-width families disprove the stronger uniform v-squared cooling comparison. The actual zero-shift clock response cancels exactly; this is not a counterexample to the full response bound.'}}
    for item in extra_analytic.values():
        assert sha(root / item["path"]) == item["sha256"]
    root_text = (root / "UnifiedTheory.lean").read_text()
    suffix = "".join("import UnifiedTheory.Audit." + n + "\n" for n in MODULES)
    assert root_text.endswith(suffix)
    assert hashlib.sha256(root_text[:-len(suffix)].encode()).hexdigest() == previous["root_check"]["source_sha256"]
    root_hash = sha(root / "UnifiedTheory.lean")
    checks = []
    for name in MODULES:
        source = "UnifiedTheory/Audit/" + name + ".lean"
        output = overlay / "UnifiedTheory/Audit" / (name + ".olean")
        assert not output.exists() and not output.is_symlink()
        output.parent.mkdir(parents=True, exist_ok=True)
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
        declared = {declaration_name(name,n) for n in re.findall(r"^theorem (\S+)", text, re.M)}
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
    assert sha(frontier_path) == frontier_hash
    assert sha(pairing_path) == pairing_hash
    for item in extra_analytic.values():
        assert sha(root / item["path"]) == item["sha256"]
    report = dict(
        **extra_analytic,
        analytic_charged_pairing=dict(path=str(pairing_path.relative_to(root)), sha256=pairing_hash,
            status='Analytic proof only; not Lean verified. Charged-density coercivity and a full linked polarized-pair bound retain n=0 without a separate negative-index norm. Conversion to the full quartic charged form and the unrestricted physical response bound remain open.'),
        analytic_frontier=dict(path=str(frontier_path.relative_to(root)), sha256=frontier_hash,
            status='Analytic research only; not Lean verified. Exact linked full-response formulation and scoped strategy obstructions; unrestricted response bound and admissible counterexample remain open.'),
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
        scope='94 Lean theorems in thirteen successor modules. The actual growing resolvent commutes with zero-charge projection, the actual growing graph preserves that sector, and resolvent-smoothed projected coherent states are a graph core for its restriction. This is not a common H/G operator core or forward growing-domain propagation. Constructed compact factors and finite symmetric tensors supply actual derivatives, bounds and support for the permissive BDG split interface. Explicit quadratic profiles and their global Euler companions retain cutoff derivatives, with their ordinary limits proved. Exact quadrant integration by parts and the original retarded-cone change of variables give the actual xi*f-prime compact quadratic limit with its minus-three-halves factor. A polynomial fixed-box extension removes apparent null denominators from the conformal interval parameter integral. Joint continuity, actual parameter derivatives, compact domination and Fubini prove differentiation through the actual finite-density cone integral. For the temporal conformal family and the original compact test field, the normalized operator at zero curvature equals the previous flat density operator, and the limit of its actual first derivatives is -6, equal to minus one-half of the actual scalar-curvature derivative. Both density and interval terms are retained, contributing -8 and +2. No derivative is interchanged with a continuum limit. The fixed-nonzero-curvature continuum limit, identification of the explicit parameter integral with geometric chronological-diamond volume, general curved limit and variational Einstein dynamics remain unproved. Two new separately hashed research notes give a positive full-quartic matrix decomposition and an admissible obstruction to a stronger width-floor v-squared cooling comparison; neither is Lean verified and neither establishes or refutes the full response bound. Unrestricted response, a common Hamiltonian/growing operator core and evolved stronger domains, microscopic law/phase selection, same-model interacting QFT/Standard Model, physical regulator limits and empirical identification remain open. The earlier phase/harmonic identification still requires revision. A physical TOE is not proved. All 3139 parent source/script hashes and 23 numerical evidence files are preserved; thirteen modules and two scripts give 3154 hashes, and the root extends 8781 to 8794 lines. Standard axioms only.')
    target = root / "data/quantum_compact_curvature_variation_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

