#!/usr/bin/env python3
"""Audit the actual paired-squeeze unitary and full unaveraged energy graph covariance."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalPairedSqueezeFlow', 'KFCausalPairedSqueezePullback', 'KFCausalPairedSqueezeTransport', 'KFCausalPairedSqueezeClockCommutation', 'KFCausalPairedSqueezeEuclidean', 'KFCausalPairedSqueezeFourier', 'KFCausalClockFloorSqueezeExponential', 'KFCausalClockFloorSqueezeMatter', 'KFCausalClockFloorSqueezeKinetic', 'KFCausalClockFloorSqueezeEnergy']
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
    logs = overlay / "quantum-paired-squeeze-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_all_charge_weak_escape_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "edae27d293efc92363a404154e337462e30b941a541dafcfebc1a4c1934223a3"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_paired_squeeze_audit.py",
        "scripts/verify_quantum_paired_squeeze.py",
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
        scope='The actual five-coordinate paired squeeze scales the two symmetric coordinate pairs and the neutral coordinate by exp(a), and the two antisymmetric coordinates by exp(-a). Its group law, determinant exp(a), exact commutation with the physical longitudinal shear, scaling of all four model directions and scaling of the full point field are proved. The inverse coordinate pullback with half-density exp(-a/2) defines an actual complex-linear unitary group on the full physical L2 space, with almost-everywhere representatives and exact clock-translation commutation. It commutes with the pure and coupled clock coordinates and transports, the bounded defect and inverse-half-clock multipliers, the full maximal longitudinal exponential graphs for every exponential parameter and the natural ordered vacuum graph. Fourier covariance and maximal transverse momentum graphs give exp(-a) output weights on the static kinetic pair and exp(a) on the growing pair. The full natural linear and quadratic matter graphs have output weights exp(a) and exp(2a), retaining the neutral field component. All eight factor graphs, their common natural domain, arbitrary weighted joint graphs and simultaneous graph closures are covariant. Under epsilon>0 and abs(h)<=pi*epsilon the actual unaveraged closed energy graph and domain are covariant for arbitrary real m, q, k, t, including zero coefficients under the existing Real.sqrt convention. The closed output is uniquely identified, and its exact norm-square is the sum over all eight outputs of exp(2*d_i*a)*norm(g_i)^2, with degrees (0,-1,-1,1,1,1,2,0). Differentiation of this exact output profile at zero gives 2*(-norm(g1)^2-norm(g2)^2+norm(g3)^2+norm(g4)^2+norm(g5)^2+2*norm(g6)^2). This is a static form variation, not a virial identity along the Hamiltonian evolution. Strong continuity and a self-adjoint squeeze generator, charge-circle commutation, charge-averaged form covariance, a signed dynamical virial estimate and clock probability escape remain to be proved. In particular the static kinetic contribution has a negative sign; no positivity or improved energy growth bound is inferred by dropping it. The prior all-charge weak escape, quantum energy-clock work and classical fast-energy diagnostic remain intact. Quantum clock-error recovery, regulator removal, controlled physical limits, Standard Model/GR identification, octonion necessity and the physical TOE remain unproved. No necessary Hamiltonian revision or new numerical evidence is asserted.')
    target = root / "data/quantum_paired_squeeze_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

