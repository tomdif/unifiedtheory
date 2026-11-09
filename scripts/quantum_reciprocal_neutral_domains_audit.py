#!/usr/bin/env python3
"""Audit joint reciprocal and neutral polynomial Hamiltonian form domains."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalVariableWidthFieldContinuity', 'KFCausalVariableWidthSourceCurves', 'KFCausalVariableWidthPolynomialDomain', 'KFCausalVariableWidthPolynomialMomentum', 'KFCausalReciprocalNeutralPackets', 'KFCausalReciprocalNeutralCharge', 'KFCausalReciprocalNeutralSuperposition', 'KFCausalReciprocalNeutralHamiltonian']
NUMERICAL_SOURCES = {'scripts/neutral_hermite_response_probe.py': '5eb4b34486dd823ebdac3f167b60da0abe1723b3d2a72c6feafd6ced4195ec21', 'scripts/verify_neutral_hermite_response.py': '4d774c57ed1c8a251ceb493314b951edf734e8ccc26d829e902026b5fb60de2d'}
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
    logs = overlay / "quantum-reciprocal-neutral-domains-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_reciprocal_closure_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "74a41606b1530496b68063d7c95f8d00907627a8043d79aa625c25e7f5b169ac"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_reciprocal_neutral_domains_audit.py",
        "scripts/verify_quantum_reciprocal_neutral_domains.py",
    ]
    assert all(sha(root / p) == h for p, h in NUMERICAL_SOURCES.items())
    hashes = dict(previous["source_sha256"])
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
        scope='The state class is enlarged to arbitrary finite superpositions of reciprocal charged Gaussians multiplied by independent neutral exponential-polynomial profiles and real clock phases. Each summand has the actual physical representative C_i*exp(i*p_i*s)*exp(b_i*q4)*P_i(q4)*psi(epsilon,a_i,h,w_i), where a_i>0,w_i>=1,p_i is real,b_i and C_i are complex,and P_i is any finite complex polynomial. Variable-width source-circle integration derives all eight natural energy-factor graphs for polynomial sourced Gaussians and their actual pure-clock momenta. Reciprocal squeeze transport rescales both the neutral source and polynomial argument, retaining the actual physical neutral profile. The enlarged packets and momenta have zero charge. Their finite sums have explicit actual momentum graphs, all eight natural factor graphs, and completed Hamiltonian form lifts at every fixed time and all real model couplings, under epsilon>0,h!=0,abs(h)<=2*pi*epsilon/3. Exact energy and signed form-response identities retain every pair of summands, including all charged-width, clock-profile, neutral-source and polynomial interference. Finite-family identities recover both the preceding reciprocal superpositions and the older mixed-clock neutral polynomial family. The even quadratic neutral witness previously excluded from the reciprocal Hilbert closure is an exact member of the enlarged packet family. This checkpoint proves actual domains and form identities; it does not prove a uniform response estimate on the joint class, strong Hamiltonian or commutator domains for all its states, graph-core density, evolution invariance or coverage, trajectory momentum regularity or an expectation derivative along the actual propagator. The earlier reciprocal response and commutator theorems are preserved. Necessary physical-model revision, unconditional clock recovery, controlled physical limits, physical identification and the physical TOE remain unproved. All 56 public theorem dependency lists in eight new modules use only standard axioms. All 2396 parent source/script hashes are preserved in 2406 entries, and exactly eight imports extend the 8176-line root to 8184 lines. Inherited numerical evidence is unchanged and no new .lake artifacts are generated.')
    target = root / "data/quantum_reciprocal_neutral_domains_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

