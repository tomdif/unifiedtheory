#!/usr/bin/env python3
"""Audit uniform negative-clock tail tightness for every physical initial state."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalUnitaryInverseOrder', 'KFCausalClockFloorLeftBarrier', 'KFCausalClockFloorLeftBarrierEvolution', 'KFCausalClockFloorLeftTightness']
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
    logs = overlay / "quantum-left-clock-tightness-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_full_time_weak_escape_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "0ef3cfae67c368d05b710d88057ad3f30cbff959099f1a61c9c00643d78ecaa9"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_left_clock_tightness_audit.py",
        "scripts/verify_quantum_left_clock_tightness.py",
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
        scope='For the actual fixed-regulator full quantum propagator, each physical Hilbert-space initial state has uniformly small sufficiently negative log-clock tails at every forward time. For every eta>0 there is S, depending on the initial state and tolerance, such that norm(lowProjection(S) U(s,t) f)^2<eta for all t>=s. For normalized states this is a probability bound. The existing positive regulator, nonzero Planck parameter and bound abs(h)<=2*pi*epsilon/3 are retained. No initial finite-energy or momentum-domain assumption, zero-charge condition, or positive vacuum coupling is needed; mass, quartic and vacuum parameters may be arbitrary real numbers. The proof uses the previously derived all-Hilbert defect-norm monotonicity. A general variational argument reverses positive quadratic-form order under a unitary when taking the supplied bounded inverse. With D=epsilon/(exp(clock)+epsilon), A_b=(1+b)I-D^2 and B_b=b*A_b^(-1), the actual multiplier weight is b/(1-D^2+b). Its expectation is nonincreasing under the actual evolution. On clock<=S with 2*exp(S)<=b*epsilon, B_b>=1/2, giving the initial-state tail bound. Dominated convergence makes the initial barrier expectation vanish as b decreases to zero, since D<1 pointwise. All inverse identities and evolution inequalities are proved rather than assumed. The cutoff is not uniform over initial states. This rules out migration of a fixed positive probability to arbitrarily negative clock values but does not prove positive-clock escape, decay of the noncompact clock-defect expectation, quantum momentum propagation, or clock recovery. The previous full-time weak-escape theorem is preserved with its distinct zero-charge and positive-vacuum hypotheses. Physical regulator removal, controlled physical limits, Standard Model/GR identification, octonion necessity and a physical TOE remain unproved. No necessary physical Hamiltonian revision or new numerical evidence is asserted.')
    target = root / "data/quantum_left_clock_tightness_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()
