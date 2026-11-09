#!/usr/bin/env python3
"""Audit physical growing-Hamiltonian domains and the conformal metric-curvature benchmark."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalClockFloorGrowingDerivativeDomain', 'KFCausalFiniteGrowingHamiltonianOutput', 'KFCausalConformal4DDiamondBenchmark', 'KFCausalConformal4DConnection', 'KFCausalConformal4DCurvatureExpansion']
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
    logs = overlay / "quantum-growing-hamiltonian-conformal-curvature-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_second_dynamics_charged_obstruction_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "d7e10b73e1665b312353e27e86ab15e129d6170bff01232ca3a9700ecd3a80a5"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_growing_hamiltonian_conformal_curvature_audit.py",
        "scripts/verify_quantum_growing_hamiltonian_conformal_curvature.py",
    ]
    hashes = dict(previous['source_sha256'])
    assert len(hashes) == 3123
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
    assert sha(frontier_path) == frontier_hash
    report = dict(
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
        scope='38 Lean theorems in 5 successor modules. The physical range condition for the time derivative of the reference form is proved equivalent to membership in the existing positive self-adjoint operator G associated with the growing part of the reference form. For the original finite sourced reciprocal states, the actual growing output is constructed as one half of the derivative of H(t)psi at t=0, with its G graph and membership in every instantaneous Dom H(s). The original clock-strip, width and source hypotheses are retained. This does not establish preservation of Dom G or Dom H(t)^2 by the full nonautonomous propagator, a physical relative graph bound, or BH/HB propagation. The geometric successors calculate first and second metric coordinate derivatives for g=Omega^2 diag(-1,1,1,1), Omega=1+att*t^2/2+spatial*|x|^2/2. They compute its determinant density, actual inverse metric and Levi-Civita Christoffel formula, actual Christoffel derivatives and curvature in an explicit sign convention. Ricci00=-3*att+3*spatial and R=6*att-18*spatial are contractions of that calculated connection curvature. The actual metric density is attached to the existing spherical coordinate-region integral. Under T>0, lambda>0, |att|,|spatial|<=lambda^(-2), T<=lambda/2, conformal positivity and actual central curve length are derived, including signed parameters. The normalized volume remainder with coefficient -R/180+Ricci00/30 is bounded by 1557*tau^4/lambda^4. This is an explicit conformal spherical-reduced coordinate-region benchmark. No manifold-measure/polar change-of-variables identity, geodesic-diamond/maximal-proper-time identification or general curved BDG limit is proved. Signed Lorentzian curvature is computed directly; transport of the existing unweighted Bianchi package is not asserted. The independent measure correction, uniform localization and remainder estimates, curved operator coefficient and first-variation transfer remain open. Unrestricted response, microscopic law/phase selection, same-model interacting QFT/Standard Model and independent physical identification remain open. An additional separately hashed analytic Mellin/holomorphic response handoff records the exact linked estimate still to prove and scoped failures of simpler comparisons; it is not Lean verified and adds no theorem. No physical TOE is proved. All 3123 parent source/script hashes and 23 numerical evidence files are preserved; 5 modules and 2 scripts give 3130 hashes and the root extends 8769 to 8774 lines. Standard axioms only.')
    target = root / "data/quantum_growing_hamiltonian_conformal_curvature_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

