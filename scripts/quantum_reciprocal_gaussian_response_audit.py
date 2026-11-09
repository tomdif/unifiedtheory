#!/usr/bin/env python3
"""Audit actual reciprocal Gaussian form domains and uniform full Hamiltonian response."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalReciprocalSqueezeFlow', 'KFCausalReciprocalSqueezePullback', 'KFCausalReciprocalSqueezeTransport', 'KFCausalReciprocalSqueezeClockCommutation', 'KFCausalReciprocalSqueezeEuclidean', 'KFCausalReciprocalSqueezeFourier', 'KFCausalReciprocalSqueezeExponential', 'KFCausalReciprocalSqueezeKinetic', 'KFCausalReciprocalSqueezeMatter', 'KFCausalReciprocalSqueezeEnergy', 'KFCausalReciprocalGaussianDomain', 'KFCausalReciprocalGaussianMomentum', 'KFCausalReciprocalGaussianHamiltonian', 'KFCausalReciprocalGaussianCoordinates', 'KFCausalReciprocalGaussianKernel', 'KFCausalGaussianClockResponseIntegrability', 'KFCausalReciprocalGaussianKernelBound', 'KFCausalReciprocalGaussianClockBound', 'KFCausalReciprocalGaussianOutputs', 'KFCausalReciprocalGaussianResponse', 'KFCausalReciprocalGaussianPotentialResponse', 'KFCausalReciprocalGaussianClockMarginal', 'KFCausalReciprocalGaussianUniformResponse']
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
    logs = overlay / "quantum-reciprocal-gaussian-response-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_charged_generating_family_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "2af86af73ffe8b4dc474f5c7b88759964c6013df1d0d83c1d9dd82e429978cbd"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_reciprocal_gaussian_response_audit.py",
        "scripts/verify_quantum_reciprocal_gaussian_response.py",
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
        scope='For every fixed nonzero h, the actual reciprocal charged Gaussian with w>=1 and every positive Gaussian clock width belongs to all eight natural energy-factor domains under the existing epsilon>0 and abs(h)<=2*pi*epsilon/3 strip condition. Its actual pure-clock momentum also has all eight factor graphs and zero charge. Both have explicit lifts into the completed charge-averaged Hamiltonian form, with exact energy and response decompositions. The proof constructs a reciprocal squeeze, with opposite signs in the two charged pairs and matching neutral scaling, proves its actual L2 unitary and Fourier representatives, and transports maximal ordered exponential, clock, kinetic and matter graphs. This is a form-domain result, not membership in the operator domain of the associated Hamiltonian or an evolution-invariance theorem. The transverse physical potential kernel is evaluated using a determinant-four change of variables and exact five-dimensional Gaussian moments. With k=1/sqrt(w), its marginal formula extends smoothly and positively to k=0. Compactness in k in [0,1] and the previously proved normalized clock region derives one derivative constant independent of w, epsilon, and clock position. Gaussian clock energy and weak-response integrability are proved rather than assumed. The full-clock potential response lower bound also allows arbitrary real clock frequency at the density level. Actual zero-frequency factor output and momentum representatives identify that kernel with the constructed operator energy and response. Combining it with the exact clock and kinetic inequalities proves one C(h)>=0 such that fullResponse(t,w)>=-((C(h)+2)/epsilon)*fullEnergy(t,w), for every w>=1, every positive Gaussian clock width, every admissible epsilon, and all Hamiltonian times, with unit couplings. No state-uniform conclusion is claimed for arbitrary complex superpositions of distinct widths: interference terms and extension along actual evolution remain open. The sufficient width range w>=1 is not claimed sharp. Widths below one, Hamiltonian operator domains, graph-core density, Hilbert or graph Taylor-series convergence, trajectory momentum regularity, unbounded moving-test identity, negative-tail tightness, unconditional clock recovery, controlled physical/regulator limits, SM/GR identification, octonion necessity and a physical TOE remain open. No necessary model revision is established. All 170 public theorem dependency lists in 23 modules use only standard axioms. All 2281 parent source/script hashes are preserved in 2306 entries. Exactly 23 imports extend the 8081-line parent root to 8104 lines; inherited numerical evidence is unchanged and no new .lake artifacts are generated.')
    target = root / "data/quantum_reciprocal_gaussian_response_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

