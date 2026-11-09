#!/usr/bin/env python3
"""Audit full-clock limits of the actual correlated clustered potential energy and response."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalCorrelatedClusteredGlobalEnvelope', 'KFCausalCorrelatedClusteredClockBounds', 'KFCausalCorrelatedClusteredClockContinuity', 'KFCausalCorrelatedClusteredWholeClock', 'KFCausalCorrelatedClusteredReducedClock', 'KFCausalCorrelatedClusteredPhysicalClockLimit']
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
    logs = overlay / "quantum-correlated-clustered-whole-clock-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_correlated_clustered_response_limit_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "f83d4c044b1381e4a0c0231f1e252f5d7a735a16363fa8226991e075b1a176d7"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_correlated_clustered_whole_clock_audit.py",
        "scripts/verify_quantum_correlated_clustered_whole_clock.py",
    ]
    numerical_path = root / 'data/correlated_polynomial_growth_probe.json'
    numerical_sha = '804e88c584989dd552cbbdc79f1526aed6445ef452399ddd5a8b79f9ad551709'
    assert sha(numerical_path) == numerical_sha
    numerical = json.loads(numerical_path.read_text())
    assert numerical['formal_parent'] == dict(path=str(previous_path.relative_to(root)), sha256=previous_hash)
    hashes = dict(numerical['source_sha256'])
    assert len(hashes) == 2566
    assert all(hashes[p] == h for p, h in previous['source_sha256'].items())
    assert all(sha(root / p) == h for p, h in hashes.items())
    assert not set(additions) & set(hashes)
    hashes.update({p: sha(root / p) for p in additions})
    evidence = dict(previous["numerical_evidence"])
    evidence.update({'correlated_polynomial_scan': {'path': 'data/correlated_polynomial_response_probe.json', 'sha256': '9de058e5d6ccf4f28e4f61df41f83958a4654c52a5371c4498fd2d4624e8956b'}, 'correlated_polynomial_verification': {'path': 'data/correlated_polynomial_response_verification.json', 'sha256': '5ba7bdc44d4b78ab341f9487f603c55df7769c0039189563fa9a7ac3dd436619'}, 'correlated_polynomial_growth_scan': {'path': 'data/correlated_polynomial_growth_probe.json', 'sha256': '804e88c584989dd552cbbdc79f1526aed6445ef452399ddd5a8b79f9ad551709'}, 'correlated_polynomial_growth_verification': {'path': 'data/correlated_polynomial_growth_verification.json', 'sha256': 'e4533090914679905b5b09f23df9480151e9de7c2469313b641d713988b3563a'}})
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
        scope='Forty-three Lean theorems prove full-clock convergence of the existing ordered-potential energy and momentum response for finite correlated charged-polynomial limits, with independently chosen positive clock widths, real frequencies, charged degrees, neutral complex sources, neutral polynomials and amplitudes. Compact normalized clock geometry yields one transverse integrable envelope valid for all clock positions and positive width spacings. Reweighting controls arbitrary finite clock coefficients by their squared-norm sum; square integrability is proved for the actual independent clock amplitudes. Joint continuity, product-measure domination, dominated convergence and Fubini justify the full clock integrals. The actual reduced response includes the coefficient times energy and the negative transport divided by the clock; both scalar multiplier bounds are derived from existing model theorems. The new integral quantities are identified with existing potentialEnergy and potentialResponse for the actual admissible finite packets, retaining all interference and exact pi/4 normalization. Positive-spacing finite functions are extended by zero outside their required positive-spacing domain solely to state the one-sided limit. The response limit is the reduced full-clock integral, not a total derivative with moving state coefficients silently frozen. These close the full-clock ordered-potential energy and response confluence gaps. Envelope constants depend on the finite family; no state-uniform relative estimate, arbitrary-family divergence, Hamiltonian graph convergence, graph-core density, evolution, controlled physical identification or physical TOE is asserted. All 2566 preceding source hashes (including the four numerical scripts added after the formal parent) are preserved in 2574 entries. Four numerical reports are added explicitly to all prior evidence, giving 23 preserved numerical file hashes. Exactly six imports extend the root from 8296 to 8302 lines. Standard axioms only; no new .lake artifacts. Numerical results are not proof premises.')
    target = root / "data/quantum_correlated_clustered_whole_clock_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

