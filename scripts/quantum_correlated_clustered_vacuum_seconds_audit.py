#!/usr/bin/env python3
"""Audit actual clustered vacuum second actions and their original finite-output limits."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalVacuumParameterRescale', 'KFCausalReciprocalNeutralVacuumParameter', 'KFCausalReciprocalNeutralDoubleVacuum', 'KFCausalCorrelatedClusteredDoubleVacuumProfiles', 'KFCausalCorrelatedClusteredDoubleVacuumLimit', 'KFCausalCorrelatedClusteredVacuumSecondLimit']
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
    logs = overlay / "quantum-correlated-clustered-vacuum-seconds-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_correlated_clustered_clock_kinetic_seconds_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "987fe6e859f85fcebc14dd40fc61086ebbe46d3fd6b9bb19d6a47e57c4e750d6"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_correlated_clustered_vacuum_seconds_audit.py",
        "scripts/verify_quantum_correlated_clustered_vacuum_seconds.py",
    ]
    hashes = dict(previous['source_sha256'])
    assert len(hashes) == 2656
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
        scope='Forty-three Lean theorems construct the natural second vacuum action on the existing correlated clustered physical state and its actual pure-clock momentum, and prove strong convergence of the two corresponding original finite strong-Hamiltonian second outputs. The pure-clock momentum parameter scaling is derived from its generator. Polynomial and reciprocal packet constructions allow the longitudinal exponential parameter to vary independently of the fixed physical charged and neutral widths. The doubled exponential outputs therefore retain the original state, clock parameters, source and polynomial. For the original B psi, one half of the output constructed with parameter 2*h compensates the proved doubling of pure-clock momentum; this factor is derived by graph uniqueness. Exact physical representatives retain every finite correlated term. At doubled shift -h, existing shifted input and momentum clock coefficients have derived continuity and L2 integrability, so the physical Gram error estimate gives actual Hilbert limits. The proved closed ordered-exponential graph and exact spectral-rescaling equivalence identify these limits with the full longitudinal exponential acting on inverseL psi and inverseL B psi. The bounded left inverseL then gives D E_h D in the natural reversed-vacuum composition. Original finite second outputs are identified by graph uniqueness and converge strongly, with graph-pair limits and natural-domain test pairing identities. Hypotheses remain epsilon>0, h!=0, positive independent clock widths and the existing strong strip |h|<=pi*epsilon/3; physical transverse widths remain groundWidth h and neutralWidth h. Combined with the parent checkpoint, six of eight second factors now act on both psi and B psi, and twelve corresponding original finite outputs converge. The two ordered matter second factors and their limits remain open. Full interacting Hamiltonian graph convergence on this limiting family, H B/B H convergence, graph-core density, a general-family uniform potential response estimate, dynamics, controlled physical limits, physical identification and the physical TOE remain open. The state-independent absolute clock/kinetic response bound remains proved; no new general potential response bound, divergent sequence or forced model revision is claimed. All 2656 parent source hashes and all 23 numerical file hashes remain unchanged; eight source additions give 2664 entries. Exactly six imports extend the root from 8370 to 8376 lines. Only standard axioms; no new .lake artifacts. No numerical result is a proof premise.')
    target = root / "data/quantum_correlated_clustered_vacuum_seconds_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

