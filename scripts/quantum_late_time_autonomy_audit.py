#!/usr/bin/env python3
"""Audit the actual late-time unitary dynamics limit in exponential time."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalStrongOperatorCompactLimit', 'KFCausalResolventUnitaryResidual', 'KFCausalStrongResolventFlowComparison', 'KFCausalStrongResolventFlowLimit', 'KFCausalClockFloorResolventFlowData', 'KFCausalClockFloorFrozenGrowingLimit', 'KFCausalDenseUnitaryUniformComparison', 'KFCausalClockFloorLateTimeAutonomy']
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
    logs = overlay / "quantum-late-time-autonomy-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_frozen_full_comparison_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "39e04fbdad4add59742b836daef6c84502fc3cd3dd488920586500372a9d5c3d"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_late_time_autonomy_audit.py",
        "scripts/verify_quantum_late_time_autonomy.py",
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
        scope='Strong convergence of the actual rescaled positive shifted resolvents is upgraded to strong convergence of the actual frozen full unitary groups to the actual growing-Hamiltonian group, uniformly on every bounded positive and negative fast-time interval for each fixed physical Hilbert input. A compact-uniform strong-operator lemma, a moving unitary derivative rule and a resolvent-smoothed residual estimate are proved. The smoothed growing comparison curve is R_U V(t) R0 x, with initial dense inputs R0 squared x; its residual is c times (R_U-R0)V(t)x for c=-i/(2h). This uses derivatives on the actual resolvent ranges, not a shared generator domain or bounded generators. Strong resolvent convergence and common contraction bounds control both comparison errors uniformly over the compact growing orbits. Density of the squared limiting-resolvent range and physical unitarity extend the result to every fixed Hilbert input. All generic derivative and domain hypotheses are discharged for the actual full frozen and growing Hamiltonians. The previous finite-energy actual-to-frozen comparison is also upgraded to a uniform forward-window bound and then extended to every physical input using density of the full form embedding and unitarity. Consequently, for every fixed f in H and L>=0, the actual full evolution from physical time log(U)/2 to log(U+t)/2 applied to f converges to the growing group at fast time t applied to f, uniformly for 0<=t<=L as U tends to infinity. There is no finite-energy, charge-sector, normalization or moment hypothesis on f. Model parameter assumptions remain epsilon>0,h!=0,abs(h)<=2*pi*epsilon/3 and arbitrary real m,g,k. The original static factors remain in the actual full evolution and in the full frozen comparison. The result is a local late-time strong limit in exponential time. It does not prove operator-norm convergence, convergence on arbitrary moving input families, convergence on unbounded growing time windows, global scattering, clock recovery, a necessary model revision, regulator removal, controlled physical limits, SM/GR identification, octonion necessity or a physical TOE. The static 1/U coefficient must not be discarded in a global argument solely because of this local result. Earlier source hashes and numerical evidence are preserved. No numerical evidence or .lake artifacts are added.')
    target = root / "data/quantum_late_time_autonomy_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

