#!/usr/bin/env python3
"""Audit the complete pointwise angular clock-transport obstruction."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalCompactAngularFDeriv', 'KFCausalNeutralRadialClockFamily', 'KFCausalJointNeutralAngularClockJet', 'KFCausalJointNeutralAngularClockObstruction']
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
    logs = overlay / "quantum-joint-angular-clock-obstruction-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_common_width_neutral_response_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "3c387a8fbbd229baf4806d6d1575604abf46a3cf00759782953c903323705db5"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_joint_angular_clock_obstruction_audit.py",
        "scripts/verify_quantum_joint_angular_clock_obstruction.py",
    ]
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
        scope='One fixed physical coherent profile at epsilon=1,h=-1/64,alpha=32,beta=1,charged width1,degree0 has an unbounded complete frozen-coefficient angular clock derivative relative to its angular energy at clock position0. There exists a fixed positive squared radius X such that varying the second charged wedge coordinate over positive values makes this ratio arbitrarily large, with positive energy and an interior wedge point in every witness. The theorem includes the actual changing neutral geometry, the moving squared radius and the actual wedge Jacobian; it is stronger than the previous isolated radial-term obstruction. The coherent source 4+i*((2/3)/(2*geometry.im)) is fixed along the entire clock curve. Exact integration of the neutral real coordinate identifies the actual jointSlice and jointArea with an explicit coherent Gaussian quartic marginal. A compact angular derivative envelope is derived from joint C1 regularity. The canonical Frechet derivative then gives every clock term without a finite-difference approximation or an assumed derivative identity. At fixed charged coordinate z the derivative is the positive factor jacobian*exp(-2*Re(z)) times 2*drift*area(X)+clockJet(X)+area_prime(X)*(drift*X-shrink*Y). The existing strictly negative area_prime at a positive X and positive shrink force unbounded growth as Y increases; the remaining geometry terms depend only on that fixed X. This rules out a family-independent pointwise upper comparison for the complete Jacobian-weighted angular energy. It does not disprove the integral estimate over charged coordinates, the actual full-clock ordered-potential response bound, or the full Hamiltonian response bound. Indeed the preserved common-width response theorem applies to this profile. No unequal-width integrated counterexample or necessary model revision follows. All 27 public theorem dependency lists in four new modules use only standard axioms. All 2524 parent source/script hashes are preserved in 2530 entries; exactly four imports extend the 8272-line root to 8276 lines. All numerical evidence is unchanged and is not used as a proof premise. The unequal-width relative integral estimate, full eight-factor Hamiltonian response, graph-core density, evolution coverage, trajectory regularity, controlled physical limits, physical identification and a physical TOE remain unproved. No new .lake artifacts are generated.')
    target = root / "data/quantum_joint_angular_clock_obstruction_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

