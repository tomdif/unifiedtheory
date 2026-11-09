#!/usr/bin/env python3
"""Audit exact full frozen clock loss and vanishing total ordered dissipation."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalMassObservableDerivative', 'KFCausalClockFloorDissipationRescaling', 'KFCausalClockFloorFrozenClockLoss', 'KFCausalClockFloorMovingDissipation']
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
    logs = overlay / "quantum-frozen-dissipation-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_moving_frozen_clock_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "5609db9c1058eb8da06e62f2969de9df2406ed6a0f898a7f6a5006daeff01bbf"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_frozen_dissipation_audit.py",
        "scripts/verify_quantum_frozen_dissipation.py",
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
        scope='The actual full frozen evolution has an exact clock-defect expectation derivative on every full reference form state, proved from its strong mass-dual derivative and form continuity without assuming physical strong differentiability of arbitrary form trajectories. A generic form-preserving bounded-observable derivative and quadratic difference bound are proved. In exponential time, the full frozen expectation rate dominates a nonnegative ordered-output dissipation with factor 1/32, giving an exact expectation integral and a total dissipation budget by 32 times the clock expectation drop. The classical output selects only factors 5,6,7. Its actual averaged pairing scales exactly by exp(2*(t-s)) under output time transport, so the denominator 2U in fast-time dissipation cancels exactly. The resulting detector on the full reference form is independent of U and is minus one half the classical output pairing at reference time 0. Along every actual full finite-energy trajectory started at a>0 in exponential time, the TOTAL integral of this nonnegative detector along the frozen evolution from its actual moving state tends to zero on any eventually nonnegative window ell(U) with ell(U)^2/U tending to zero. In particular this holds on the proved diverging window sqrt(sqrt U). The proof uses the actual expectation monotonicity and existence of its limit, the previously proved moving-state physical comparison, unitarity, and a bounded quadratic-observable difference estimate. No rate of asymptotic clock recovery is assumed, and no frozen-to-growing limit is applied to moving states. These are all-charge finite-form-state dissipation statements; no evolved momentum moment or operator-domain restriction is added. Model parameter assumptions remain epsilon>0,h!=0,abs(h)<=2*pi*epsilon/3 with arbitrary real m,g,k. Positive vacuum coupling is not required for these bounds. All static factors remain in the full frozen and actual evolutions. The total detector integral tends to zero, not merely its average or a quantity suppressed by a leftover 1/U coefficient. This strengthens the reachable-state plateau condition but does not exclude a positive clock residual, establish a uniform detector lower bound, or prove quantum clock recovery. Growing fast-time windows still have shrinking physical durations. Global scattering, a needed model revision, regulator removal, controlled physical limits, SM/GR identification, octonion necessity and a physical TOE remain unproved. All parent source/script hashes and numerical evidence are preserved; no numerical evidence or .lake artifacts are added.')
    target = root / "data/quantum_frozen_dissipation_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

