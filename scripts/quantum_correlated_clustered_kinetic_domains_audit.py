#!/usr/bin/env python3
"""Audit actual clustered kinetic domains, all first-factor limits and uniform clock/kinetic response bounds."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalNarrowGaussianMoments', 'KFCausalNarrowFourierMomentStates', 'KFCausalNarrowPacketDifferential', 'KFCausalNarrowPacketMomentumGraphs', 'KFCausalClusteredChargedJetIdentity', 'KFCausalClusteredPacketDerivativeCoordinates', 'KFCausalNarrowBlockDerivativeLimit', 'KFCausalCorrelatedClusteredTransverseGraphs', 'KFCausalCorrelatedClusteredInverseHalfLimit', 'KFCausalCorrelatedClusteredKineticGraphs', 'KFCausalCorrelatedClusteredInputKineticLimit', 'KFCausalCorrelatedClusteredMomentumKineticLimit', 'KFCausalCorrelatedClusteredAllFactorLimit', 'KFCausalCorrelatedClusteredKineticResponseLimit', 'KFCausalCorrelatedClusteredFormBounds']
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
    logs = overlay / "quantum-correlated-clustered-kinetic-domains-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_correlated_clustered_narrow_fourier_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "69c9485435972d0c5b241c8587ba21e95d8f17cd2b41af1790b56e2f85af043e"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_correlated_clustered_kinetic_domains_audit.py",
        "scripts/verify_quantum_correlated_clustered_kinetic_domains.py",
    ]
    hashes = dict(previous['source_sha256'])
    assert len(hashes) == 2621
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
        scope='Eighty-seven Lean theorems identify the actual transverse momentum outputs of reciprocal packets and correlated clustered families, prove strong L2 output limits, and close all four natural kinetic-factor graphs on both the existing physical limiting state and its actual pure-clock momentum. First Gaussian moments have exact physical and narrow Fourier representatives with checked signs and constants. Actual physical line derivatives identify the maximal transverse momentum graphs. An exact differentiated finite-sum identity supplies the additional broad-direction width factor; direction one retains the neutral polynomial derivative. Bounded inverse-half-clock dressing preserves independent continuous L2 clock coefficients, and its actual closed multiplier graph is passed to the limit separately from each closed transverse graph. No closedness of an arbitrary composition is assumed. The physical state and its pure-clock momentum now belong to the common natural domain of all eight energy factors. The original sixteen finite factor outputs converge strongly, giving convergence of all factor energies and form responses and of their arbitrary finite real weighted sums. Both kinetic/pure-clock composition orders act on the physical state. Each actual kinetic form response satisfies 0<=R_j<=(1/(4*epsilon))*||K_j psi||^2. Together with the parent clock response bound, any nonnegative weighted sum of the five clock/kinetic responses has absolute value at most 1/(4*epsilon) times the corresponding weighted energy; this constant is independent of family size, charged degrees, neutral sources, neutral polynomials, clock widths and frequencies. Generic physical transverse and kinetic graphs use alpha>0,beta>0,32*beta<=alpha and continuous L2 clock coefficients; the dressing additionally uses epsilon>0. Identification with the original input and clock momentum uses h!=0 and positive independent clock widths. The common eight-factor result and original-output convergence retain the established strip bound |h|<=2*pi*epsilon/3. The kinetic response alone does not need that strip bound. These are actual first-factor domains and clock/kinetic composition results, not strong-Hamiltonian second actions on the limiting family. Strong Hamiltonian graph convergence, graph-core density, a general-family uniform potential response estimate, full Hamiltonian dynamics, controlled physical limits, physical identification and the physical TOE remain open. No model change is forced. All 2621 parent source hashes and all 23 numerical file hashes are preserved; seventeen source additions give 2638 entries. Exactly fifteen imports extend the root from 8339 to 8354 lines. Only standard axioms; no new .lake artifacts. No numerical result is a proof premise.')
    target = root / "data/quantum_correlated_clustered_kinetic_domains_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

