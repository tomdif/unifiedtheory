#!/usr/bin/env python3
"""Audit full-time weak escape for all physical zero-charge states."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalGraphDetectionModulus', 'KFCausalExponentialNoSpikes', 'KFCausalClockFloorExponentialVariation', 'KFCausalClockFloorDissipationTail', 'KFCausalClockFloorFullTimeWeakEscape', 'KFCausalClockFloorZeroSectorWeakEscape']
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
    logs = overlay / "quantum-full-time-weak-escape-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_weak_escape_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "29866476de0f28db93dacaa40f4194667158191b5bd27590d629f3adfe022148"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_full_time_weak_escape_audit.py",
        "scripts/verify_quantum_full_time_weak_escape.py",
    ]
    hashes = dict(previous["source_sha256"])
    assert all(sha(root / p) == h for p, h in hashes.items())
    assert not set(additions) & set(hashes)
    hashes.update({p: sha(root / p) for p in additions})
    evidence = previous["numerical_evidence"]
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
        scope='For the actual fixed-regulator full quantum propagator, every physical Hilbert-space state in the zero-charge sector converges weakly to zero as forward time tends to infinity, provided the vacuum coupling is positive and the existing nonzero Planck parameter and regulator bound hold. Every fixed finite family of physical test-vector overlaps has a vanishing sum of squared magnitudes in the full-time limit. No initial finite-energy or momentum-domain assumption remains in the final theorem. The argument first treats finite-energy initial data. A graph detector modulus controls each fixed test vector on bounded state/output graph balls without norm coercivity. The actual weak Schrodinger equation and forward energy bounds imply physical form-test variation bounded by K*exp(2b)*(b-a) for s<=a<=b, with K independent of a and b. The actual dissipation budget has uniformly vanishing tails, derived from a nonnegative monotone defect expectation with possibly positive limit. A general exponential no-spike argument excludes persistent fixed-test revivals. Actual closed-vacuum graph and drift detection estimates supply its hypotheses. Density first extends the test vectors and then the initial states within the zero-charge sector, using the already proved zero-sector energy-domain density and unitarity. All bounds and convergence statements are derived rather than added as assumptions on the actual evolution. This strengthens the preceding subsequence result to full-time weak convergence but does not prove physical norm decay, decay of the noncompact clock-defect operator, or escape in clock position alone. Quantum momentum propagation, zero quantum clock error, physical regulator removal, controlled physical limits, Standard Model/GR identification, octonion necessity and a physical TOE remain unproved. No necessary physical Hamiltonian revision or new numerical evidence is asserted.')
    target = root / "data/quantum_full_time_weak_escape_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()
