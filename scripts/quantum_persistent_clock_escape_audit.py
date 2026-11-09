#!/usr/bin/env python3
"""Audit persistent clock escape and reduction to the physical Gaussian family."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalClockFloorResidualDefect', 'KFCausalClockFloorPersistentClockLeakage', 'KFCausalClockFloorCoherentRecoveryCriterion']
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
    logs = overlay / "quantum-persistent-clock-escape-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_windowed_clock_criterion_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "87e0394e52063fb75fb7de9d5d95eca400931bbcdcabce04ca721882c2c1f73e"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_persistent_clock_escape_audit.py",
        "scripts/verify_quantum_persistent_clock_escape.py",
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
        scope='For the actual full regulated unitary evolution, epsilon>0, h!=0 and abs(h)<=2*pi*epsilon/3, the norm of the bounded clock defect converges for every physical L2 initial state to its nonnegative infimum over time. This residual is 1-Lipschitz in the initial physical norm and vanishes exactly when clock recovery holds. Any failure would persist for finite-energy initial states arbitrarily close to the failing state; equivalently all-state recovery is equivalent to recovery on the completed averaged finite-energy form domain. The recovery states form a closed complex linear subspace. Recovery for any total family implies recovery for every physical state, with no uniform convergence rate assumed on the family. In particular, for any fixed positive Gaussian width parameter a, all-state recovery is equivalent to recovery of every member of the explicit existing six-real-parameter physical Gaussian modulation family. Any failure would therefore have an individual member of that family as a witness; no finite ansatz evolution or Gaussian preservation is assumed. For normalized initial state and fixed normalized L2 window, a strictly positive residual gives fixed positive windowed mass below one fixed clock threshold at every time. Combining this with the proved uniform negative-clock-tail control and, for positive vacuum k, full-time escape from bounded phase-space regions gives a strengthened alternative: either the defect norm tends to zero or there are fixed real L<S and eta>0 such that for every fixed phase-space ball radius R, all sufficiently late times have more than eta windowed probability in the finite clock band L<clock<=S outside that ball. The eventual time may depend on R; no moving-cutoff/time-limit interchange is asserted. The alternative now says persistent escape, not only arbitrarily late recurrence. None of these results establishes that a failing trajectory exists or proves recovery of the Gaussian family. The existing energy estimate does not supply the missing one-sided momentum or transverse tail control. All eight factors and prior checkpoints are preserved. Clock-error decay itself, full-domain longitudinal matter response, physical limits, regulator removal, SM/GR identification, octonion necessity and a physical TOE remain unproved. No necessary model revision or new numerical evidence is asserted.')
    target = root / "data/quantum_persistent_clock_escape_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

