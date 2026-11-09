#!/usr/bin/env python3
"""Audit the exact charged-pair full Hamiltonian coupling."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalChargedPairDifferential', 'KFCausalChargedPairKineticOutputs', 'KFCausalChargedPairKineticPairing', 'KFCausalChargedPairKineticSymmetries', 'KFCausalChargedPairKineticCancellation', 'KFCausalChargedPairHamiltonianCoupling']
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
    logs = overlay / "quantum-charged-pair-hamiltonian-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_charged_pair_charge_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "8a43eec7ff0af990b5d90634807a67e2535311a77582ea587e0471373dc27448"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_charged_pair_hamiltonian_audit.py",
        "scripts/verify_quantum_charged_pair_hamiltonian.py",
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
        scope='Lean evaluates the complete charge-averaged Hamiltonian form pairing between the centered physical Gaussian and its explicit quadratic excitation with multiplier P(q)=q0*q1-q2*q3. The predecessor already proves that both are zero-charge states with all eight energy-factor outputs and completed form lifts, and that the quadratic state is orthogonal to the entire restricted neutral closure. Exact directional derivatives of P times the physical Gaussian, polynomial Gaussian L2 membership and the actual closed momentum graphs identify the four damped momentum outputs. Cross densities and their integrability are derived from these actual Hilbert outputs. Charged-plane interchange and neutral-coordinate reflection preserve the full configuration measure and the physical Gaussian. The clock-half cross integral vanishes; the equally weighted static pair cancels after four symmetry images, retaining the neutral component in the second physical direction; the growing pair cancels under plane interchange. Hence the full kinetic cross pairing is exactly zero. For unit potential couplings, positive epsilon and a, nonzero h and abs(h)<=2*pi*epsilon/3, the full completed Hamiltonian pairing at every time t equals exp(2*t) times the predecessor full-clock potential pairing. Its real part is strictly negative and it is nonzero. No cancellation, integrability, output identity or nonzero coupling is added as a premise; no numerical quadrature or cutoff enters. This proves a full form-level coupling to a state outside the restricted neutral closure. Actual evolution out of that closure still requires the weak-dynamics bridge. Clock-momentum regularity for this specific quadratic state, the enlarged response bound, trajectory momentum regularity, negative-tail tightness, unconditional clock recovery, controlled physical/regulator limits, Standard Model/general-relativity identification, octonion necessity and a physical TOE remain open. No response-inequality failure or necessary physical-model revision follows. Fifty-nine public theorem checks in six modules use only standard axioms. All 2188 predecessor hashes and inherited numerical evidence are preserved in 2196 source/script entries. Exactly six imports extend the 8010-line parent root; no new .lake artifacts are generated.')
    target = root / "data/quantum_charged_pair_hamiltonian_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

