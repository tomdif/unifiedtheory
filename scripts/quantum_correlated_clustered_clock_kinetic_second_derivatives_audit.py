#!/usr/bin/env python3
"""Audit actual clock derivatives of clustered clock/kinetic second outputs and the full Hamiltonian remainder."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalClockFloorPureClockKineticSquare', 'KFCausalClockFloorPureClockClockSquare', 'KFCausalCorrelatedClusteredFiniteSecondPureClock', 'KFCausalCorrelatedClusteredClockKineticSecondPureLimit', 'KFCausalCorrelatedClusteredClockKineticSecondCommutator', 'KFCausalProjectedSecondClockDecomposition', 'KFCausalCorrelatedClusteredHamiltonianClockRemainder']
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
    logs = overlay / "quantum-correlated-clustered-clock-kinetic-second-derivatives-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_correlated_clustered_hamiltonian_limits_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "70757dfa4c7afe5ae06e9e66374ac524696d7231aeeefdebdd6b2b5cc1b00f64"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_correlated_clustered_clock_kinetic_second_derivatives_audit.py",
        "scripts/verify_quantum_correlated_clustered_clock_kinetic_second_derivatives.py",
    ]
    hashes = dict(previous['source_sha256'])
    assert len(hashes) == 2694
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
        scope='Forty-one Lean theorems construct and control the pure-clock derivatives of the original clock and four kinetic second outputs on the full correlated clustered limiting family. The natural kinetic square D P P D has a pure-clock graph whenever the state and its actual clock momentum have its natural second graphs; its commutator equals twice the existing bounded clock correction. The clock-square derivative is identified on the previously proved finite output domain, and all finite-domain premises are discharged from the frozen sourced polynomial and reciprocal family results. All five original finite derivative sequences converge strongly, so closedness of the pure-clock graph proves the limiting derivative domains and compositions. Their commutator output norm is bounded by abs(h)/(4*epsilon) times the corresponding second-output norm, uniformly over the full family. The existing interacting Hamiltonian retains every original coupling and all eight terms. Its original finite B H outputs are constructed by finite graph sums and the actual zero-charge projection. The projected clock/kinetic part and its derivatives converge. Membership of H psi in the pure-clock domain is proved equivalent to membership of the projected three-term potential remainder, and convergence of the full original B H sequence is equivalent to convergence of its potential derivative remainder after subtracting the constructed clock/kinetic limit. A conditional closed-graph lemma records how a future potential derivative limit would identify that action; the remaining limit is not assumed or claimed proved. The full B H limit, general interacting commutator, arbitrary-neutral-profile uniform potential response, graph-core density, dynamics, controlled physical limits, physical identification and physical TOE remain open. The previous full H and H B graph limits and scoped uniform full strong response remain proved. No coupling is set to zero to replace the model, no response divergence or forced model revision is claimed, and no numerical evidence is a proof premise. All 2694 parent source hashes and 23 numerical files remain unchanged; nine additions give 2703 source entries. Seven imports extend the root from 8402 to 8409 lines. Standard axioms only; no new .lake artifacts.')
    target = root / "data/quantum_correlated_clustered_clock_kinetic_second_derivatives_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

