#!/usr/bin/env python3
"""Audit autonomous square evolution, nonautonomous endpoint derivatives and charged marginal obstruction."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalClockFloorFrozenSquareEvolution', 'KFCausalFiniteHamiltonianSquareEvolution', 'KFCausalConfluentAllOrderCoercivityObstruction', 'KFCausalConfluentAllOrderChargedNormalization', 'KFCausalFiniteHamiltonianTimeDerivative', 'KFCausalFiniteBackwardSecondDynamics']
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
    logs = overlay / "quantum-second-dynamics-charged-obstruction-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_quadratic_response_physical_bridge_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "b877431c42db9945847852cc7c8e8034a76473f2ef2e90c47794176d0ea3385f"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_second_dynamics_charged_obstruction_audit.py",
        "scripts/verify_quantum_second_dynamics_charged_obstruction.py",
    ]
    hashes = dict(previous['source_sha256'])
    assert len(hashes) == 3115
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
        scope='46 Lean theorems in 6 successor modules. The autonomous group of the same full averaged self-adjoint Hamiltonian preserves its natural square domain and has first and second strong derivatives, with continuous second derivative. Original finite sourced reciprocal states supply the actual first and second outputs; epsilon>0, h nonzero, abs(h)<=epsilon/10, positive clock widths, charged widths>=1, arbitrary finite complex amplitudes/sources and neutral polynomials, original mass/quartic/vacuum parameters retained. For genuine nonautonomous evolution, the original fixed input has an explicitly differentiated H(s)psi, and both H(s)psi and Hprime(s)psi lie in Dom H(t) for arbitrary s,t. Second differentiation in the INITIAL endpoint is derived as -h^(-2) U(s,t)H(s)^2 psi + (i/h)U(s,t)Hprime(s)psi. For s<=t the initial-time derivative lies in the final Hamiltonian domain, and the mixed derivative in final-after-initial order is derived. No forward nonautonomous square-domain invariance, physical Hprime bound on evolved vectors, or BH/HB propagation is asserted. Separately, exact Gamma and original charged-plane monomial integrals give positive energy and cooling/energy=2/(4N+1) at every order, ruling out a fixed positive all-order marginal coercivity coefficient. All integrability and the factor-two plane normalization are proved. This is a proof-method obstruction, not a counterexample to the complete physical response inequality, whose clock derivative vanishes at the zero-phase test. Unrestricted response, evolved operator compositions, microscopic law/phase selection, curved continuum and first-variation limits, same-model interacting QFT/Standard Model and independent physical identification remain open. No physical TOE is proved. All 3115 parent source/script hashes and 23 numerical evidence files are preserved; 6 modules and 2 scripts give 3123 hashes and the root extends 8763 to 8769 lines. Standard axioms only.')
    target = root / "data/quantum_second_dynamics_charged_obstruction_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

