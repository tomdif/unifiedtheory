#!/usr/bin/env python3
"""Audit actual clustered Hamiltonian graph limits and the scoped uniform strong response."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalCoherentMatterSpectralProfile', 'KFCausalPolynomialMatterSpectral', 'KFCausalInverseClockSpectralRecovery', 'KFCausalReciprocalNeutralMatterSpectral', 'KFCausalCorrelatedClusteredMatterSpectralProfiles', 'KFCausalCorrelatedClusteredMatterSecondLimit', 'KFCausalCoherentMomentumMatterSpectralProfile', 'KFCausalPolynomialMomentumMatterSpectral', 'KFCausalReciprocalNeutralMomentumMatterSpectral', 'KFCausalCorrelatedClusteredMomentumMatterSpectralProfiles', 'KFCausalCorrelatedClusteredMomentumMatterSecondLimit', 'KFCausalCorrelatedClusteredAllSecondLimit', 'KFCausalCorrelatedClusteredStrongHamiltonianLimit', 'KFCausalCorrelatedClusteredStrongResponseLimit', 'KFCausalCorrelatedClusteredUniformStrongResponse']
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
    logs = overlay / "quantum-correlated-clustered-hamiltonian-limits-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_correlated_clustered_quartic_intermediates_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "0ca9e792dc578d8fa33c72457674537be1f5cab8122d04f9cd7d88da4b73a6cb"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_correlated_clustered_hamiltonian_limits_audit.py",
        "scripts/verify_quantum_correlated_clustered_hamiltonian_limits.py",
    ]
    hashes = dict(previous['source_sha256'])
    assert len(hashes) == 2677
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
        scope='Eighty-six Lean theorems close both complete matter second actions on the existing correlated clustered physical state and its actual pure-clock momentum. Actual mixed spectral endpoints are identified through coherent, source-circle polynomial and reciprocal-squeeze constructions, preserving field shift -h/2, Gaussian shift -h and the momentum factor one half at doubled clock parameter. A closed unbounded-multiplier relation passes through the existing Bochner integrals; inverse-half-clock injectivity recovers each actual exponential graph. Derived mixed-field estimates give strong convergence of all four original matter second outputs. Together with the frozen clock, kinetic and vacuum results, all eight natural second actions and all sixteen original second-output limits now hold. The full interacting averaged Hamiltonian acts on both limiting vectors for epsilon>0, h nonzero, abs(h)<=pi*epsilon/3 and positive clock widths, with arbitrary finite correlated charged degrees, neutral sources, neutral polynomials, amplitudes and real frequencies. Original finite Hamiltonian graphs converge to H psi and H B psi; the actual composition H B is constructed. Exact full-energy and full-response identities identify the limiting form values with strong Hamiltonian pairings for all original real model coupling parameters. A single universal one-sided lower response bound is proved for the actual full Hamiltonian on the source-free neutral-vacuum, zero-frequency clustered subclass at unit couplings, independently of charged degrees, family size, complex coefficients, positive clock widths, admissible h and epsilon, and time. This transfers the existing finite bound through actual graph limits; it is not a general neutral-profile estimate. The general-family uniform potential response estimate, B H psi domain and convergence, the full commutator, graph-core density, evolution regularity and invariance, controlled physical limits, physical identification and the physical TOE remain open. The earlier singular field-domination coefficient is only a limitation of that comparison method; neither response divergence nor a forced model revision is claimed. All 2677 parent source hashes and 23 numerical file hashes are preserved; seventeen additions give 2694 source entries. Fifteen imports extend the root from 8387 to 8402 lines. Only standard axioms; no new .lake artifacts. No numerical result is a proof premise.')
    target = root / "data/quantum_correlated_clustered_hamiltonian_limits_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

