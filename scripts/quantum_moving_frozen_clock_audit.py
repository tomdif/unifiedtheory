#!/usr/bin/env python3
"""Audit growing-window full-flow freezing and the clock-defect plateau."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalGrowingTimeWindows', 'KFCausalClockFloorMovingFreeze', 'KFCausalClockFloorFrozenDefectPlateau', 'KFCausalClockFloorGrowingDefect']
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
    logs = overlay / "quantum-moving-frozen-clock-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_late_time_autonomy_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "6dc3e19b71251a5fd8b38d85dae344ffe73d51047f1bae8417fca04e6160b2f9"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_moving_frozen_clock_audit.py",
        "scripts/verify_quantum_moving_frozen_clock.py",
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
        scope='The actual full time-dependent physical evolution is compared with the full frozen Hamiltonian along its own moving states. For initial fast time a>0, full reference form state v, U>=a and t>=0, the squared physical error between P(log(a)/2,log(U+t)/2)Jv and F_U(t)P(log(a)/2,log(U)/2)Jv is at most q_a(v)*t^2/(2*abs(h)*U). Scaled-energy monotonicity bounds the moving input energy by the original energy; physical propagator composition identifies the restarted state. For every eventually nonnegative window length ell(U) with ell(U)^2/U tending to zero, the comparison error tends to zero uniformly for t=r*ell(U), 0<=r<=1. Density and unitarity extend this to every fixed initial physical Hilbert-space state, with no energy, moment, charge or normalization restriction; the input at U is the actual evolved state and is not fixed. The explicit window sqrt(sqrt(U)) diverges and satisfies the required ratio limit. The full actual clock-defect norm converges uniformly over all forward windows to its existing asymptotic residual, using monotonicity. On the above admissible windows, the full frozen defect norm has the same uniform limit and its change from the actual starting defect tends uniformly to zero. Consequently failure of clock recovery forces a positive frozen defect plateau on these growing windows. This is a necessary condition for failure, not a proof of failure or recovery. Separately, the actual growing-Hamiltonian unitary group inherits defect norm monotonicity from the already proved local full-flow limit; its residual limit and zero-residual recovery equivalence are proved. Existing parameter assumptions remain epsilon>0,h!=0,abs(h)<=2*pi*epsilon/3 and arbitrary real m,g,k. All full static factors are retained. Growing fast-time windows in this result still have shrinking physical duration. No comparison with the growing group on arbitrary moving states or unbounded windows is proved, and the positive residual is not excluded. Global scattering, quantum clock recovery, necessity of a model revision, regulator removal, controlled physical limits, SM/GR identification, octonion necessity and the physical TOE remain open. All earlier source/script hashes and numerical evidence are preserved; no numerical evidence or .lake artifacts are added.')
    target = root / "data/quantum_moving_frozen_clock_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

