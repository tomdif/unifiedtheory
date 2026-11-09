#!/usr/bin/env python3
"""Audit Hamiltonian graph cores, forward domain limits and full Fourier response."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalJointNeutralFourierOuterDensity', 'KFCausalJointNeutralFourierOuterFubini', 'KFCausalCorrelatedClusteredFourierResponse', 'KFCausalCorrelatedClusteredFourierResponsePhysical', 'KFCausalJointFourierDilationJet', 'KFCausalJointFourierDilationPath', 'KFCausalJointFourierDissipationClock', 'KFCausalHamiltonianCoreFromSources', 'KFCausalHamiltonianCoreProjectedCoherent', 'KFCausalCorrelatedHamiltonianDomainEvolution', 'KFCausalCorrelatedHamiltonianDomainLimit']
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
    logs = overlay / "quantum-hamiltonian-core-fourier-response-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_neutral_fourier_response_split_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "60e0cab59e573416b80f05586fd7d94ce49aad6dcb4000c4d766e3ed8e01c6cd"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_hamiltonian_core_fourier_response_audit.py",
        "scripts/verify_quantum_hamiltonian_core_fourier_response.py",
    ]
    hashes = dict(previous['source_sha256'])
    assert len(hashes) == 2760
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
        scope='Seventy Lean theorems advance Hamiltonian domains and the full correlated response. For the constructed arbitrary finite correlated clustered family at every positive spacing, original totalResponse equals the ordered integral of the explicit quartic Fourier response over Y>0,u,v,k. Physical transport, reduced response and whole-clock potential response are identified, with whole-clock integrability. Outer signed marginal integrability is derived from full physical response L1; arbitrary frequency/charged swaps or global absolute integrability of separated frequency terms are not asserted. The exact coordinate-dilation correction cancels neutral imaginary translation and leaves a pure-real charged cooling jet plus real field jet (-2*delta-3*lambda)*v. Its actual coordinate-path derivative is proved. Normalized cooling lies between 1/8 and 10, normalized dilation between -12 and 0, and the corrected normalized field jet has square at most 1296, giving algebraic absorption remainder 10368*t*c^2. These are ingredients, not a uniform response constant. The charged dilation divergence identity and integrated dissipative coercivity are not assumed. Constructed states and initial clock momenta are explicitly connected to the same averaged Hamiltonian forward evolution and strong Schrodinger equation. Original finite approximants retain convergence of states and Hamiltonian outputs after evolution. Resolvent images of the independently proved dense projected-coherent source span form a graph core for the zero-charge Hamiltonian restriction. This smoothed core is not identified with the explicit BH/HB response family or shown to lie in its clock-composition domains. Full Dom(H) forward invariance was already proved; the remaining domain gap is preservation of Dom(BH) intersect Dom(HB) and graph density/regularity of the response family. The general state-independent energy-relative response estimate, controlled physical limits and physical identification remain open. No TOE or forced model revision is claimed. All 2760 parent source/script hashes and 23 numerical files are preserved; eleven modules and two audit scripts give 2773 hashes. Eleven imports extend the root from 8454 to 8465 lines. Standard axioms only; no numerical probe, new .lake artifact, harness change, commit or push.')
    target = root / "data/quantum_hamiltonian_core_fourier_response_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

