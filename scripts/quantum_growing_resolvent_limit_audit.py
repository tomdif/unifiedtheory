#!/usr/bin/env python3
"""Audit the actual positive-shift strong resolvent limit after rescaling."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalPenaltyVariationalLimit', 'KFCausalClockFloorFastResolvent', 'KFCausalClockFloorFastResolventIdentification', 'KFCausalClockFloorGrowingResolventLimit']
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
    logs = overlay / "quantum-growing-resolvent-limit-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_growing_hamiltonian_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "8e86d5c5907fe323e44e0e7043c1284d87941a523ef6b34bc17b88b8bbdf4a2e"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_growing_resolvent_limit_audit.py",
        "scripts/verify_quantum_growing_resolvent_limit.py",
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
        scope='The actual full regulated Hamiltonians have a proved positive-shift strong resolvent limit after exponential-time rescaling. For u>0 and t=log(u)/2, R_u is exactly u times the previously constructed shiftedResolvent with shift a=u and physical time t, hence the two-sided inverse of 1+H(t)/u on the actual physical operator domain. R_0 is the two-sided inverse of 1+Hgrow, where Hgrow is the previously constructed positive self-adjoint growing Hamiltonian. Let I be the proved dense continuous inclusion of the full reference form V into its growing graph-form completion W, A the actual static output, r_u the existing scaled full resolvent form lift, and r_0=J_W.adjoint f. The actual resolvent variational equation is inner(I r_u,I v)+(1/u)*inner(A r_u,A v)=inner(r_0,I v) for every original full reference-form test v. A general variational identity proves that the sum of the squared W-error and the nonnegative static penalty is bounded by the same expression at any fixed reference vector. The proved density of I, followed by u tending to infinity with each approximant fixed, makes that total error tend to zero. Therefore I r_u converges strongly in the completed growing form to r_0, R_u f converges strongly in physical Hilbert space to R_0 f, the growing outputs converge strongly, and the static penalty norm(A r_u)^2/u tends to zero. These hold for every fixed physical Hilbert input f, without energy or moment assumptions on f. Parameters are epsilon>0, h!=0, abs(h)<=2*pi*epsilon/3 and arbitrary existing real coefficients; no additional charge or positive-vacuum condition is used. The limit is proved at positive shift one with explicit inverse identities. No operator-norm convergence, uniform rate, interchange with time-dependent inputs, convergence of full time-dependent propagators, autonomous comparison evolution, scattering, or clock recovery is asserted. The full dynamical equation retains the static remainder; the resolvent penalty limit is not substituted for its accumulated trajectory error. Necessary model revision, regulator removal, physical limits, SM/GR identification, octonion necessity and a physical TOE remain unproved. All previous checkpoint sources and numerical evidence are preserved, and no numerical evidence or .lake artifacts are added.')
    target = root / "data/quantum_growing_resolvent_limit_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

