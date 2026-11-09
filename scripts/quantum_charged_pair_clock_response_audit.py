#!/usr/bin/env python3
"""Audit the paired-state clock-momentum regularity and full response identities."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalDirectionalClockMomentum', 'KFCausalChargedPairClockMomentum', 'KFCausalDirectionalClockComposition', 'KFCausalChargedPairFactorResponse', 'KFCausalChargedPairHamiltonianResponse', 'KFCausalChargedPairOrderedMomentumDensity', 'KFCausalChargedPairPotentialResponse']
NUMERICAL_SOURCES = {'scripts/neutral_hermite_response_probe.py': '5eb4b34486dd823ebdac3f167b60da0abe1723b3d2a72c6feafd6ced4195ec21', 'scripts/verify_neutral_hermite_response.py': '4d774c57ed1c8a251ceb493314b951edf734e8ccc26d829e902026b5fb60de2d'}
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
    logs = overlay / "quantum-charged-pair-clock-response-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_charged_pair_evolution_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "290dbcdc6fd76e7b4851bfa50256a76a56537e79aebd9c46317b5bdd9b0e9150"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_charged_pair_clock_response_audit.py",
        "scripts/verify_quantum_charged_pair_clock_response.py",
    ]
    assert all(sha(root / p) == h for p, h in NUMERICAL_SOURCES.items())
    hashes = dict(previous["source_sha256"])
    assert all(sha(root / p) == h for p, h in hashes.items())
    assert not set(additions) & set(hashes)
    hashes.update({p: sha(root / p) for p in additions})
    evidence = dict(previous["numerical_evidence"])
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
        scope='Lean constructs actual pure-clock momentum and all eight natural energy-factor outputs for every directional polynomial Gaussian, with arbitrary real transverse direction and polynomial degree, using closed graph source-circle integration. Polarization gives the actual momentum of the existing paired quadratic state P(q)*clockFunction(epsilon,a,s)*Gaussian(q), P=q0*q1-q2*q3, whose dynamically relevant full Hamiltonian coupling and evolution escape were proved in the predecessor. Charge-projection commutation proves zero charge of this momentum. Both the state and its momentum now lift into the completed charge-averaged Hamiltonian form for every time and coupling; the pair is proved outside the previous restricted neutral completed-pair closure. Exact clock-half composition graphs establish the clock response and its energy bound. All four kinetic responses are nonnegative and bounded by their respective factor energies. Their physically weighted clock/kinetic sum satisfies Rkin(t)>=-(1/(4*epsilon))*Ekin(t), uniformly in a and physical time under epsilon>0, a>0, h!=0 and abs(h)<=2*pi*epsilon/3. The full form energy and signed response decompose into all eight natural factors with the original physical weights. The unbounded complex clock-slope multiplication relation is proved through source-circle integration and polarization, identifying all three ordered momentum-output densities. Their actual L2 outputs prove absolute integrability of the signed full-clock potential response. For unit couplings, fullResponse(t)=Rkin(t)+exp(2*t)*integral potentialDensity, where potentialDensity is the sum with weights 1,1/2,1/4 of 2*Re(weakSlope)*norm(pairedShifted_n)^2. No integrability, operator identity, regularity or response bound is inserted as a premise. No numerical quadrature or cutoff enters. The remaining potential-response lower estimate and its extension including interference on an enlarged state class are not proved. These are fixed-state form identities, not a moving-trajectory clock-response derivative theorem. Trajectory clock-momentum regularity, negative-tail tightness, unconditional clock recovery, controlled physical/regulator limits, Standard Model/general-relativity identification, octonion necessity and a physical TOE remain open. Neither failure of an enlarged response bound nor a necessary physical-model revision is established. Forty-three public theorem checks in seven modules use only standard axioms. All 2201 predecessor hashes and inherited numerical evidence are preserved in 2210 source/script entries. Exactly seven imports extend the 8019-line parent root; no new .lake artifacts are generated.')
    target = root / "data/quantum_charged_pair_clock_response_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

