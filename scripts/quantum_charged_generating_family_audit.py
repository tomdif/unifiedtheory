#!/usr/bin/env python3
"""Audit actual reciprocal-width charged Gaussian states and their generating profile."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalReciprocalGaussianFourier', 'KFCausalReciprocalGaussianStates', 'KFCausalReciprocalGaussianCharge', 'KFCausalChargedGeneratingProfile', 'KFCausalReciprocalGaussianIndependence']
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
    logs = overlay / "quantum-charged-generating-family-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_one_sided_clock_response_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "d5c9516fc5d8fe55eed4f05407563bf31269c9c07ee80bc160758ac979fa9ca4"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_charged_generating_family_audit.py",
        "scripts/verify_quantum_charged_generating_family.py",
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
        scope='Lean constructs actual Hilbert states with reciprocal charged Gaussian widths alpha*w and alpha/w for every w>0, with alpha=1/(2*abs(h)), h!=0, the existing positive clock width and neutral width. The paired-coordinate construction derives both configuration and actual partial Fourier representatives; the two-dimensional Fourier normalization is pi/alpha independent of w. In charge coordinates the exponent is alpha*(R1/w+w*R2), where R1 and R2 are the invariant standing-plane radii. Every such state is proved nonzero and has zero standing charge, and every finite complex superposition has zero charge with an explicit configuration representative. At w=1 the state is exactly the existing centered packet. For every w!=1 the state is proved not to be any complex combination of the centered, paired quadratic and corrected-quartic packets with the same clock profile. Three radial evaluations prove this independence by distinguishing an exponential from an affine function of squared radius. Setting w=(1+t)/(1-t), abs(t)<1, and multiplying by 1/(1-t^2) gives an actual nonzero zero-charge generating state. Its exact configuration multiplier is exp((4*alpha*t*P-2*alpha*t^2*S)/(1-t^2))/(1-t^2), P=q0*q1-q2*q3, S=sum of the four charged coordinate squares. Lean verifies that the first pointwise parameter derivative at zero is 4*alpha*P, and the second is 16*alpha^2*Q4, where Q4 is the established corrected quartic polynomial. No convergence of its full series, all-degree configuration-to-charge polynomial correspondence, Hilbert or energy-graph parameter differentiability, ordered-energy domains, clock-momentum domains, completed-form lifts or response bounds for this new family are asserted. In particular, zero charge and L2 membership do not imply all Hamiltonian domains. The previously proved actual quartic-span response bound and one-sided full-clock criterion remain intact. Exploratory generating-function Gram matrices through high finite cutoffs are outside the audit; no numerical cutoff establishes a degree-uniform response bound or physical counterexample. The larger evolution class, trajectory momentum regularity, unbounded moving-test identity, negative-tail tightness, unconditional clock recovery, controlled physical/regulator limits, SM/GR identification, octonion necessity and physical TOE remain open. No necessary model revision is established. Forty-one public theorem dependency checks in five modules use only standard axioms. All 2274 parent source/script hashes are preserved in 2281 entries. Exactly five imports extend the 8076-line parent root to 8081 lines; inherited numerical evidence is unchanged and no new .lake artifacts are generated.')
    target = root / "data/quantum_charged_generating_family_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

