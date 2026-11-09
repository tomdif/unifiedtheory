#!/usr/bin/env python3
"""Audit actual quadratic/quartic matter-to-vacuum graphs and linked Hermite uncertainty."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalComplexSpectatorFourier', 'KFCausalMatterInsertionCoordinate', 'KFCausalSourcedWidthMatterSecondInput', 'KFCausalSourcedWidthMatterMultiplier', 'KFCausalSourcedWidthMatterRegularity', 'KFCausalSourcedWidthMatterSquare', 'KFCausalSourcedWidthMatterContinuity', 'KFCausalSourcedWidthMatterProjected', 'KFCausalFiniteSourcedMatterSquare', 'KFCausalSingleWidthHermiteMoments']
NAMESPACES = {'KFCausalSourcedWidthMatterRegularity': 'KFCausalSourcedWidthMatterMultiplier'}
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
    logs = overlay / "quantum-matter-vacuum-hermite-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_physical_field_insertion_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "1f159123b1c17ce3b23564afa62ed2b8d71ae9b7936ac490fc6088326f033afb"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_matter_vacuum_hermite_audit.py",
        "scripts/verify_quantum_matter_vacuum_hermite.py",
    ]
    hashes = dict(previous['source_sha256'])
    assert len(hashes) == 2962
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
        scope='62 Lean theorems in 10 successor modules. For every original finite sourced reciprocal packet family on epsilon>0, h nonzero, positive clock widths, charged widths at least one and abs(h)<=epsilon/10, the actual state lies in Dom(Q S5) and Dom(Q S6), where S5=D E Phi^2 E D and S6=D E Phi^4 E D are the original reverseFactor-composed-energyFactor Hamiltonian components, E=longitudinalExponential(h,1/2) and Q=D E^2 D. Their field half-shift -h/2 and Gaussian full-shift -h are identified exactly through a maximal complex spectator-Fourier relation. Explicit Q U(theta) S5/S6 outputs are continuous and uniformly bounded in theta; the closed exponential graph supplies Q P0 S5/S6 and independent charge angles Q_phi S_j,theta. All original sources, neutral polynomials, frequencies, widths and finite-sum interference are retained. These are actual Hamiltonian component words, not replacements by Q Phi^k Q. Separately, Gaussian Hermite norm identities, covariant frequency integration by parts, exact gauge polynomial normalization and E2>=3*sigma^2*E1 are proved for genuine Gaussian-polynomial frequency packets with positive Gaussian widths. This is a scalar normal-form component; the original physical Fourier-to-Hermite bridge and arbitrary correlated-width matrix estimate remain open. Full H^2, outer matter/kinetic/clock mixed graphs, evolving BH/HB, uniform confluent limits, unrestricted-width integrated response and physical identification remain open. All 2962 parent source/script hashes and 23 numerical evidence files are preserved; 10 modules and 2 scripts give 2974 hashes and root extends 8624 to 8634 lines. Combined with the preceding checkpoint this continuation adds 155 theorems in 29 modules. Standard axioms only. No physical TOE or necessary model revision is claimed.')
    target = root / "data/quantum_matter_vacuum_hermite_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

