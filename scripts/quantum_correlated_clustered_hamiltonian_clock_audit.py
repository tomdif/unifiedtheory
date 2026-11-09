#!/usr/bin/env python3
"""Audit full Hamiltonian-clock domains, original graph limits and the actual commutator response."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalPartialFourierFiberFormula', 'KFCausalNarrowFourierGeneralCoordinates', 'KFCausalCorrelatedClusteredFourierOperatorBridge', 'KFCausalCorrelatedClusteredPotentialFourierIdentification', 'KFCausalCorrelatedClusteredFourierPureClock', 'KFCausalCorrelatedClusteredFourierClockGraphs', 'KFCausalNarrowFourierClockCoordinates', 'KFCausalNarrowFourierPureClockGraph', 'KFCausalCorrelatedClusteredPotentialSpectralClock', 'KFCausalCorrelatedClusteredPotentialSecondClock', 'KFCausalCorrelatedClusteredHamiltonianClockLimit', 'KFCausalCorrelatedClusteredStrongCommutatorResponse']
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
    logs = overlay / "quantum-correlated-clustered-hamiltonian-clock-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_correlated_clustered_joint_fourier_l2_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "c796f639259710aa829d06504ff59368a2972b375ae436b12a16081d24692476"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_correlated_clustered_hamiltonian_clock_audit.py",
        "scripts/verify_quantum_correlated_clustered_hamiltonian_clock.py",
    ]
    hashes = dict(previous['source_sha256'])
    assert len(hashes) == 2724
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
        scope='One hundred five Lean theorems identify the actual unitary narrow Fourier images of the original three potential spectral endpoints, prove full pure-clock generator graphs of the Fourier representatives, and transfer them back through an all-L2 unitary commutation theorem. A generic slice formula is proved from joint L2, almost-everywhere slice L1 and joint L2 Fourier data using Fubini, Plancherel and tensor density; these conditions are discharged for the original profiles. Both exact measure-preserving coordinate charts preserve the spectator clock and intertwine its actual weighted coordinate unitary and translations. The resulting narrow Fourier unitary commutes with pure-clock transport and preserves its full maximal momentum graph. The finite and limiting Fourier profiles are differentiable on the complete configuration space; their normalized derivatives retain the half-density correction. The parent joint L2 results give actual generator graph pairs and strong convergence. The physical potential endpoints have powers zero, two and four and distinct physical shifts. The final bounded inverse-half-clock commutator is included explicitly, and uniqueness identifies the constructed finite derivatives with the original finite second-output derivatives. Consequently all eight input second actions lie in the pure-clock domain and all eight original derivatives converge strongly. The full averaged interacting Hamiltonian output H psi lies in Dom B; psi lies in both Dom(B H) and Dom(H B), retaining the original couplings and zero-charge projection. Original finite B H, H B and commutator outputs converge strongly. The full response is exactly (1/h) times the imaginary quadratic form of the actual B H-H B commutator. The source-free neutral-vacuum zero-frequency subclass at unit couplings inherits the already-proved uniform lower bound for this actual commutator. The general family-independent energy-relative response estimate remains open: the new norm bound involves the commutator norm and does not supply such a constant. The isolated radial cross-term obstruction remains valid and is not a counterexample to the full integrated response; complete charged/neutral cancellations must be retained. No new uniform constant, graph-core density, evolution invariance, regulator/continuum limits, physical identification or TOE is claimed. No model revision is inferred. All 2724 parent source hashes and 23 numerical files are preserved; twelve successor modules and two scripts give 2738 hashes. Twelve imports extend the root from 8426 to 8438 lines. Standard axioms only, no new .lake artifacts, and no numerical evidence used as a proof premise.')
    target = root / "data/quantum_correlated_clustered_hamiltonian_clock_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

