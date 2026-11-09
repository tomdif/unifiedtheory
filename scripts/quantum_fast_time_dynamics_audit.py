#!/usr/bin/env python3
"""Audit the actual exponential-time equation and its square-integrable remainder."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalClockFloorRescaledEnergy', 'KFCausalClockFloorFastTimeEnergy', 'KFCausalClockFloorFastTimeDynamics', 'KFCausalClockFloorFastTimeDualError']
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
    logs = overlay / "quantum-fast-time-dynamics-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_persistent_clock_escape_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "c19beee66f18e48ba891f554ceae818d80099d4b35c140fe444e690f1c5a59e6"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_fast_time_dynamics_audit.py",
        "scripts/verify_quantum_fast_time_dynamics.py",
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
        scope='Actual full regulated quantum evolution admits an exact exponential-time weak equation with a controlled remainder. Parameters are epsilon>0, h!=0 and abs(h)<=2*pi*epsilon/3, arbitrary model coefficients and initial vector in the completed averaged finite-energy form domain. Write A and B for the actual static and growing reference energy-output maps, and psi(t) for the reference-form trajectory whose embedding is the physical state. The exact energy E(t)=norm(A psi(t))^2+exp(2t)*norm(B psi(t))^2 obeys dE/dt=2*exp(2t)*norm(B psi(t))^2. The proved rescaled energy exp(-2t)*E(t) is nonnegative and antitone, has a nonnegative limit, and its derivative is -2*exp(-2t)*norm(A psi(t))^2. An exact finite-interval identity yields a finite forward budget for this weighted static energy. Exponential time u=exp(2t), t=log(u)/2, is treated only on u>0. The rescaled energy in u has derivative -norm(A psi(log(u)/2))^2/u^2; this nonnegative loss is integrable on every ray u>a>0. For each fixed reference form test z, the derivative of inner(psi(log(u)/2),J z) is exactly (i/(2h))*inner(B psi,B z) plus the retained remainder (i/(2h*u))*inner(A psi,A z), with the convention for inner products used by the existing weak evolution. The squared remainder is bounded by norm(A z)^2/(4h^2) times the fast-time loss. Therefore it has a finite square-integral budget on finite intervals, vanishing uniform tail budgets, is integrable in squared norm on each positive ray, and tends to zero pointwise as u tends to infinity. The retained remainder is also represented by an actual Riesz vector in the reference form Hilbert space. Its pairing equals the scalar weak remainder, uniformly bounded by the vector norm times the test form norm. Its norm squared is bounded by 1/(4*h^2) times the fast-time loss, has the corresponding interval budget, is integrable on each positive ray, and tends to zero. Thus the remainder is controlled in form-dual norm, uniformly on the unit ball of form tests. These results do not assert a physical Hilbert-norm or physical operator-norm perturbation estimate, L1 time integrability, a constructed autonomous limiting propagator, wave operators or scattering. No Hamiltonian term has been dropped, and the full evolution remains the one previously constructed with all eight factors. These results provide an actual asymptotic weak equation and a finite error budget, but do not exclude the previously proved persistent bounded-clock escape alternative. Clock-error decay, necessary model revision, full-domain longitudinal matter response, regulator removal, controlled physical limits, SM/GR identification, octonion necessity and a physical TOE remain unproved. All previous checkpoints and numerical evidence are preserved; no new numerical claims are introduced.')
    target = root / "data/quantum_fast_time_dynamics_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

