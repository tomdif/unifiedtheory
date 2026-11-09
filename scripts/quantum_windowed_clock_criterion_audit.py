#!/usr/bin/env python3
"""Audit the exact windowed clock marginal and physical recovery criterion."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalBornLocalization', 'KFCausalWindowedPositionMarginal', 'KFCausalProbabilityWindowEscape', 'KFCausalPhysicalWindowedClock', 'KFCausalClockFloorSharpEscapeCriterion', 'KFCausalClockFloorWindowedRecovery']
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
    logs = overlay / "quantum-windowed-clock-criterion-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_phase_space_escape_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "43cc5dd1a2f7ed8f6481fe5d6103e12f4ecf2f1a870689c64ff0ca720dff43a4"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_windowed_clock_criterion_audit.py",
        "scripts/verify_quantum_windowed_clock_criterion.py",
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
        scope='The existing physical positive windowed phase-space law now has an exact clock marginal and a proved recovery criterion. For arbitrary L2 vectors, the position marginal equals the difference of independent configuration Born variables, derived from sharp spectator projections commuting with the actual partial Fourier unitary and measure-preserving shear coordinates. The physical log-clock marginal is exactly the difference law of the sharp physical clock Born law and the fixed window clock Born law. For normalized state f and fixed normalized L2 window w, each clock half-line probability is bounded by the other law at a threshold shifted by R plus the window mass outside [-R,R]. Fixed window tails vanish without moment assumptions, giving equivalence of escape to positive clock infinity for sharp and windowed laws. For every uniformly norm-bounded physical L2 family, sharp clock-half-line escape is equivalent to decay of the actual bounded clock-defect norm. The explicit cutoff estimate is norm(D_epsilon f)<=norm(P_{clock<=S} f)+defect(epsilon,S)*norm(f); the reverse localized bound is inherited. For the actual full regulated physical evolution with epsilon>0, h!=0 and abs(h)<=2*pi*epsilon/3, every normalized initial state and fixed normalized L2 window therefore has windowed clock-half-space escape if and only if the actual clock-defect norm tends to zero, equivalently the defect expectation tends to zero. No energy, charge-sector, state moment, window moment or positive vacuum hypothesis is needed for these equivalences. Any two fixed normalized windows give the same recovery criterion. The known uniform negative-clock-tail bound transfers to the actual windowed clock law for every forward time. With positive vacuum k, the previous full-time bounded phase-space escape yields a proved alternative: either the actual clock-defect norm tends to zero, or there are fixed finite real clock cutoffs L,S and a positive mass threshold eta such that, for every phase-space ball radius R and every time threshold T, some t>=T has more than eta windowed mass in {L<clock<=S} outside that ball. Thus any failure must use unbounded matter or momentum while retaining a fixed positive mass in a bounded clock interval; escape to negative clock infinity is excluded. The alternative does not select a branch and is not a trajectory counterexample. No interchange of phase cutoff and time limits is assumed. Full-domain longitudinal matter response, clock-error decay itself, controlled physical limits, regulator removal, Standard Model/GR identification, octonion necessity and the physical TOE remain unproved. No necessary model revision or new numerical evidence is asserted. All earlier checkpoints remain intact.')
    target = root / "data/quantum_windowed_clock_criterion_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

