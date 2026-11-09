#!/usr/bin/env python3
"""Audit identification of actual full-generator state limits with the physical evolution."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalUniformResolventLimit', 'KFCausalCompactMovingLimit', 'KFCausalClockFloorUniformResolventLimit', 'KFCausalTransportedMassLimit', 'KFCausalClockFloorStateMassEquation', 'KFCausalContinuousMassUniqueness', 'KFCausalClockFloorStateLimitIdentification', 'KFCausalIdentifiedStateOperatorAssembly', 'KFCausalClockFloorPhysicalStateApproximation']
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
    logs = overlay / "quantum-state-physical-identification-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_form_state_operators_audit.json"
    previous_hash = sha(previous_path)
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_state_physical_identification_audit.py",
        "scripts/verify_quantum_state_physical_identification.py",
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
        scope='At the existing fixed positive physical regulator, full-generator state limits are now identified with the already constructed physical evolution. The scaled full resolvents converge strongly to the identity uniformly over compact time windows for each fixed form vector. A common dense domain, exact left resolvent identity, and continuous generator outputs provide the uniform estimate; compactness and eventual uniform bounds extend it to continuous moving states and uniformly converging state families along any spectral sequence tending to infinity. For admissible positive spectral parameters, the exact smoothed graph identity gives the transported mass equation for the bounded approximations with a bounded error term. Uniform convergence passes this equation to the limit: M(S_t u(t)) has derivative (-i/h) Q(t) S_t u(t) on the open interval. This does not assert a strong derivative of u or of its physical embedding. A separate norm differentiation theorem uses only form-state continuity and the strong derivative of the mass-applied curve. The skew diagonal pairing then proves uniqueness on the closed interval, including its endpoints by continuity. Applying uniqueness to the existing physical form flow identifies S_t u(t)=formFlow(l,t)(S_l u(l)); after the embedding this equals the existing unitary physical evolution. Reversing the coordinate transport gives the explicit fixed-coordinate formula for u(t). The final existence theorem combines this identification with the predecessor bounded state operators: for every completed form-space initial state x, actual bounded full-generator approximations P_n(t)x, with one common threshold B>=2 and one operator-norm bound L, converge uniformly in time to S(a,t,s) formFlow(l,t)(S(a,s,l)x). Their bounded approximate differential equations, initial identity and spectral admissibility are retained. The final conclusion covers every finite forward interval including a singleton. Convergence is strong and statewise uniform in time, not operator-norm convergence or convergence uniformly over the unit ball. Identification makes every admissible continuous uniform state limit with a given initial state agree with the physical form flow. A separate two-time approximate convergence or cocycle theorem is not supplied. Corrected auxiliary evolution convergence, strong convergence of unbounded generator outputs, limiting generator-domain propagation, the limiting strong equation and full physical Hamiltonian-domain propagation remain open. The completed form space is not the full physical Hilbert space. Neither approximation limit removes the physical clock regulator. Quantum momentum propagation, clock escape, controlled physical limits, SM/GR identification, octonion necessity and a physical TOE remain unproved. No necessary physical model revision or new numerical evidence is asserted.')
    target = root / "data/quantum_state_physical_identification_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()
