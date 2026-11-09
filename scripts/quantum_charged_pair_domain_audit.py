#!/usr/bin/env python3
"""Audit the charged-pair natural domains and full-clock potential coupling."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalDirectionalGaussianStates', 'KFCausalDirectionalGaussianCoefficients', 'KFCausalDirectionalGaussianDomain', 'KFCausalChargedPairDomain', 'KFCausalL2ContinuousMean', 'KFCausalDirectionalShiftedCoefficients', 'KFCausalChargedPairOrderedOutputs', 'KFCausalChargedPairPotentialCoupling']
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
    logs = overlay / "quantum-charged-pair-domain-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_charged_pair_coupling_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "994f5234ea2bfe81eee3213938a78a3c9c71ac8cd39b5e7ea7f20af7032fcf93"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_charged_pair_domain_audit.py",
        "scripts/verify_quantum_charged_pair_domain.py",
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
        scope='Lean constructs every finite real directional power of the centered physical Gaussian as a Hilbert state in all eight natural energy-factor domains by exact source-circle coefficient extraction. Four quadratic directions give the explicit nonzero state P(q)*clockFunction(epsilon,a,s)*physicalGaussian(groundWidth(h),neutralWidth(h),q), where P(q)=q0*q1-q2*q3. All eight graph outputs are constructed under epsilon>0, a>0, h!=0 and abs(h)<=2*pi*epsilon/3, for arbitrary transverse kinetic directions and continuous real field. The three ordered potential outputs are identified almost everywhere: each is the centered shifted output times scale(epsilon,-h/2,s)^2*P(q). A continuous L2 mean theorem derives square integrability of these output representatives from the actual graph family, without assuming target integrability. For modelDirections, pointField and unit vacuum/mass/quartic weights, the unaveraged potential pairing between the centered state and this paired state equals its full clock-and-transverse integral. The predecessor local strict sign, nonvanishing clock amplitude and Fubini prove its real part strictly negative and hence the actual pairing nonzero. There is no finite cutoff, quadrature or assumed nonzero coupling. This proves unprojected natural-domain membership and an unaveraged potential-factor coupling. Actual zero-charge and plane-interchange identification of this specific state, its completed charge-averaged Hamiltonian-form lift, clock-momentum regularity, kinetic cross terms, full Hamiltonian pairing and evolution out of the neutral closure remain to be proved. No failure of the response inequality or necessary physical-model revision follows. Enlarged-domain response control, dynamical momentum regularity, negative-tail tightness, unconditional clock recovery, controlled physical/regulator limits, Standard Model/general-relativity identification, octonion necessity and a physical TOE remain unproved. Forty-seven public theorem checks in eight modules use only standard axioms. All 2170 predecessor source hashes and inherited numerical evidence are preserved in 2180 entries. Exactly eight imports extend the 7996-line parent root; no new .lake artifacts are generated.')
    target = root / "data/quantum_charged_pair_domain_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

