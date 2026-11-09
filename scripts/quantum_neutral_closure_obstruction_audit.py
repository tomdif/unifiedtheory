#!/usr/bin/env python3
"""Audit the strict neutral closure obstruction and regular charge-zero excitations."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalChargedPlaneSwap', 'KFCausalNeutralSwapConstraint', 'KFCausalChargeZeroSwapWitness', 'KFCausalNeutralClosureObstruction', 'KFCausalChargedOddCoherentPackets']
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
    logs = overlay / "quantum-neutral-closure-obstruction-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_neutral_full_response_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "1ded05abfef779621db9dfe902d97183f724028e404edc0312a3026d59698af7"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_neutral_closure_obstruction_audit.py",
        "scripts/verify_quantum_neutral_closure_obstruction.py",
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
        scope='The finite neutral mixed-clock polynomial family covered by the uniform full Hamiltonian-form response bound has a proved extra symmetry: it is fixed by the actual physical unitary obtained by interchanging the two charged planes in mixed charge coordinates. The fixed subspace is closed, contains the Hilbert closure of all these finite neutral states, and contains the first physical embedding of every pair in their completed-form graph closure. Total standing charge zero does not impose this symmetry. An explicit bounded radial-imbalance multiplier of the actual mixed-coordinate Gaussian produces a nonzero charge-zero Hilbert vector that changes sign under the interchange. Its Hamiltonian-form regularity is not assumed. Existing density of the full projected coherent family then proves that some projected coherent packet lies outside the neutral Hilbert closure. That projected packet and its actual pure-clock momentum have constructed completed Hamiltonian-form lifts for every time and every potential coupling. The interchange commutes with actual charge rotation and zero-charge projection, and sends an actual coherent packet to the packet with its two charged-plane parameters interchanged. Therefore the difference of two such projected packets gives a nonzero charge-zero excitation orthogonal to the entire neutral Hilbert closure, with actual state/momentum completed-form lifts at every time. The two-packet construction is explicit; existence of a parameter giving a nonzero difference follows from the proved totality argument, without choosing a numerical parameter. This disproves density of the restricted neutral response family even in the physical zero-charge Hilbert sector, and shows that its completed-form closure misses regular physical state/momentum pairs. Thus the full dynamical response estimate cannot follow from that restricted bound by a density argument. This does not prove that the full propagator leaves the restricted class, that its response inequality fails on the larger class, or that the physical model must change. Exact Hamiltonian coupling, a bound on the required enlarged response domain, momentum regularity along evolution, negative-tail tightness, unconditional clock recovery, controlled physical/regulator limits, Standard Model/general-relativity identification, octonion necessity and a physical TOE remain unproved. Forty-eight public theorem checks in five modules use only standard axioms. All 2156 predecessor source hashes and inherited numerical evidence are preserved in 2163 entries. Exactly five imports extend the 7986-line parent root; no new .lake artifacts are generated.')
    target = root / "data/quantum_neutral_closure_obstruction_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

