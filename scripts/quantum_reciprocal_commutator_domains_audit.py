#!/usr/bin/env python3
"""Audit actual reciprocal Hamiltonian clock domains and strong commutator response."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalRadialMultipliers', 'KFCausalShiftedGaussianRadialMoments', 'KFCausalMixedFieldPhysicalProfile', 'KFCausalShiftedGaussianPureDifferential', 'KFCausalMixedFieldPureClockDifferential', 'KFCausalMixedFieldPureClockDomain', 'KFCausalGaussianSecondPureClockDomain', 'KFCausalFullClockPureDomain', 'KFCausalKineticSecondPureDomain', 'KFCausalReciprocalHamiltonianPureDomain', 'KFCausalReciprocalStrongCommutator']
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
    logs = overlay / "quantum-reciprocal-commutator-domains-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_reciprocal_superposition_response_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "c41a1045d54f44d407995372411af9da8b3c5ff7ff9a653fbfca1a1a5d6e0786"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_reciprocal_commutator_domains_audit.py",
        "scripts/verify_quantum_reciprocal_commutator_domains.py",
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
        scope='The actual Hamiltonian output H_t psi of every finite complex reciprocal Gaussian superposition is proved to lie in the pure-clock momentum domain. Together with the parent domains of psi and Bpsi, both H_t Bpsi and B H_t psi are actual unbounded operator applications, and their difference defines the strong commutator. The exact identity Re[(i/h)*inner(psi,(H_t B-B H_t)psi)]=(-2/h)*Im inner(H_t psi,Bpsi) is derived from the proved operator graphs and self-adjointness. The parent universal bound therefore becomes a bound on this actual commutator expectation: it is at least -((C+2)/epsilon)*Re inner(H_t psi,psi), with one universal C>=0. Domain and identity statements cover all real model couplings at every fixed time; the uniform lower bound is at unit couplings. The finite family allows arbitrary complex coefficients, independent positive clock widths and charged widths w_i>=1, with epsilon>0,h!=0,abs(h)<=pi*epsilon/3. Coincident widths and exact cancellation remain included. The constant is independent of packet count, coefficients, widths and separation, h, epsilon and Hamiltonian time. The domain proof constructs the pure-clock differential of the mixed-shift field/Gaussian state, retaining the different shifts and the half-density correction. All transverse polynomial moments and one clock moment are L2 on the existing closed strip, with no strict-strip restriction or additional domain premise. Actual second matter and vacuum outputs inherit their clock domains through the bounded inverse-clock graph. Full-clock and kinetic second outputs have separately proved differential domains. Squeeze transport, finite sums and actual charge projection give the full Hamiltonian result. This closes B H_t psi and the strong commutator domain for this finite zero-clock-frequency reciprocal Gaussian family. It does not prove invariance under Hamiltonian evolution, trajectory momentum regularity, a response estimate on the entire energy-form domain, graph-core density or an expectation derivative along evolved states. Unconditional clock recovery, controlled physical limits, Standard Model or gravity identification, octonion necessity, necessary model revision and a physical TOE remain open. All 74 public theorem dependency lists in eleven new modules use only standard axioms. All 2378 parent source/script hashes are preserved in 2391 entries, and exactly eleven imports extend the 8162-line root to 8173 lines. Inherited numerical evidence is unchanged and no new .lake artifacts are generated.')
    target = root / "data/quantum_reciprocal_commutator_domains_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

