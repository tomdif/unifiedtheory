#!/usr/bin/env python3
"""Audit common Hamiltonian domains, signed metric jets and exact conformal variation."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalClockFloorGrowingCommonDomain', 'KFCausalClockFloorTwoTimeGrowingGraph', 'KFCausalFiniteGrowingMixedDomains', 'KFCausalLorentzianContractedBianchi', 'KFCausalConformal4DBoostedMoments', 'KFCausalConformal4DTemporalVariation', 'KFCausalMinkowski4DEulerIBP']
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
    logs = overlay / "quantum-common-domains-lorentzian-variation-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_growing_hamiltonian_conformal_curvature_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "34e32692274788d61858c20280d4e751f0337d78e79fe34ff27b3e1328a09a43"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_common_domains_lorentzian_variation_audit.py",
        "scripts/verify_quantum_common_domains_lorentzian_variation.py",
    ]
    hashes = dict(previous['source_sha256'])
    assert len(hashes) == 3130
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
    assert sha(pairing_path) == pairing_hash
    report = dict(
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
        scope='51 Lean theorems in seven successor modules. The actual averaged H(s) and growing G graphs transport affinely to H(t), and Dom H(t) intersect Dom G is time independent. For distinct times, Dom H(s) intersect Dom H(t) equals Dom H(s) intersect Dom G. The actual G output is the Hamiltonian-output difference quotient, with an explicit two-time graph norm bound. Original finite sourced states have actual GH(t), H(t)G and G-squared graphs with constructed outputs under the original clock-strip, width and source conditions. No single-instantaneous-graph estimate, common operator core, or preservation of the stronger domains by nonautonomous evolution is proved. Both Bianchi contractions retain arbitrary diagonal inverse-metric weights. Signed Einstein divergence and Ricci derivative symmetry are derived from commuting metric-jet partials; the Lorentzian specialization matches the actual previously computed conformal curvature. These are normal-coordinate metric-jet identities, not a global covariant-derivative construction, Einstein field equation or variational derivation. A Lorentz boost has its actual linear derivative, preserved quadratic form and determinant one. An explicit compact spherical parameter integral has proved mass and second time moment. The actual conformal determinant density gives an exact polynomial volume and finite-density first variation, retaining both the point-density and interval-volume corrections. No manifold-measure or chronological-diamond identification is assumed or proved. Exact finite-box integration by parts replaces the actual xi*f-prime curvature kernel by the original BDG kernel acting on the Euler derivative of a C1 test profile. This does not differentiate a continuum limit; cutoff estimates, integration-domain identification, the curved operator limit and first-variation transfer remain open. Unrestricted response, microscopic law/phase selection, same-model interacting QFT/Standard Model and empirical identification remain open. The previous Mellin formulation and a new separately hashed charged-density and linked-pairing proof remain analytic research, not Lean verified. The new pairing bound includes the n=0 boundary, but its conversion to the full quartic charged form is unproved. A physical TOE is not proved. All 3130 parent source/script hashes and 23 numerical evidence files are preserved; seven modules and two scripts give 3139 hashes and the root extends 8774 to 8781 lines. Standard axioms only.')
    target = root / "data/quantum_common_domains_lorentzian_variation_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

