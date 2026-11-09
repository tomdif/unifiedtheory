#!/usr/bin/env python3
"""Audit the positive joint neutral/reciprocal energy integral and integrability."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalReciprocalNeutralSliceIntegrability', 'KFCausalReciprocalNeutralPlaneIntegrability', 'KFCausalReciprocalNeutralLaplace', 'KFCausalReciprocalNeutralPositiveForm', 'KFCausalReciprocalNeutralActualPositive', 'KFCausalReciprocalNeutralPositiveEnergy', 'KFCausalReciprocalNeutralHolomorphic']
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
    logs = overlay / "quantum-reciprocal-neutral-positive-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_reciprocal_neutral_kernel_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "eb7c7b5321c6c4ab660b205da12f0f3f2746f195e43edfae9c13928f18b243d4"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_reciprocal_neutral_positive_audit.py",
        "scripts/verify_quantum_reciprocal_neutral_positive.py",
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
        scope='The full finite joint neutral/reciprocal Gram form equals a nonnegative joint integral retaining every interference term, all charged widths and arbitrary neutral exponential-polynomial profiles. Fixed-clock transverse factor L2 membership and absolute cross-density integrability are derived by the actual squeeze map. Removing three nonzero Gaussian spectator integrals proves absolute integrability of the retained two-dimensional neutral marginal at every clock position. A common half-line Laplace lift is absolutely integrable; summing it gives the squared norm of one common finite profile sum. All generic representation hypotheses are discharged for the actual packet family with positive clock widths, epsilon>0, h!=0, abs(h)<=2*pi*epsilon/3 and charged widths w_i>=1. Independent clock widths/frequencies, neutral sources, polynomial degrees and exact cancellations are retained. The actual ordered potential energy of the finite superposed state equals the clock integral of the positive slice, which is proved integrable. Absorbing the neutral Gaussian into entire profiles isolates the positive quartic weight. Positivity and this holomorphic identity do not establish a uniform clock comparison or a signed-response bound for the full joint family. Strong Hamiltonian and commutator domains for that family, graph-core density, evolution coverage, trajectory momentum regularity and expectation derivatives remain open. Earlier domain and response theorems are preserved. No necessary model revision, controlled physical limit, physical identification or physical TOE is established. All 36 public theorem dependency lists in seven new modules use only standard axioms. All 2414 parent source/script hashes are preserved in 2423 entries, and exactly seven imports extend the 8190-line root to 8197 lines. Inherited numerical evidence is unchanged and no new .lake artifacts are generated.')
    target = root / "data/quantum_reciprocal_neutral_positive_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

