#!/usr/bin/env python3
"""Audit the full charged dilation identity and mixed diffusion square."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalJointFourierDilationMeasure', 'KFCausalCorrelatedDilationIntegral', 'KFCausalCorrelatedDilationEnvelope', 'KFCausalCorrelatedDilationPolynomials', 'KFCausalCorrelatedDilationDifferentiation', 'KFCausalCorrelatedDilationDivergence', 'KFCausalJointFourierDilationRepresentation', 'KFCausalJointFourierDilationResponse', 'KFCausalJointFourierDilationQuartic', 'KFCausalCorrelatedFourierCoolingResponse', 'KFCausalJointFourierDissipationKernel', 'KFCausalJointFourierDissipationVacuum', 'KFCausalJointFourierDissipationMixedBoundary', 'KFCausalJointFourierDissipationMixedSquare', 'KFCausalJointFourierDissipationMixedPackets', 'KFCausalJointFourierDissipationMixedHessian']
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
    logs = overlay / "quantum-charged-dilation-mixed-diffusion-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_hamiltonian_core_fourier_response_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "ed1220944796107b889ad75ba2bae3ca044704b9bfa221714e1dd0778c6fd7ca"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_charged_dilation_mixed_diffusion_audit.py",
        "scripts/verify_quantum_charged_dilation_mixed_diffusion.py",
    ]
    hashes = dict(previous['source_sha256'])
    assert len(hashes) == 2773
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
        scope='One hundred six Lean theorems close the full charged dilation integration step and sharpen the unresolved mixed dissipation estimate. For arbitrary finite exponential-polynomial packets with arbitrary charged degrees, neutral polynomials, sources, amplitudes and field powers, Gaussian/Laplace width floors give a derived local L1 envelope for both squared value and squared derivative. Differentiation under the full charged/neutral joint integral is proved. Exact changes of variables on the positive Y half-line then give integral(dilationResponse)=-4*ell*integral(energyDensity), without endpoint-flux assumptions. The common neutral Gaussian phase is retained until norms are taken, so the actual finite Fourier family and its quartic field weights are identified without discarding interference. Its full dilation response is integrable and has the same exact Jacobian contribution. For the original constructed correlated family at every positive spacing and actual admissible clock scale, totalResponse=-4*ell*totalEnergy+(pi/4)*integral(cooling), where cooling has pure-real charged velocity Re(r_prime)-ell*Re(r), corrected real field velocity (-2*delta-3*ell)*v and zero neutral imaginary velocity. This is an exact decomposition, not the uniform inequality. Separately the charged diffusion matrix is positive and its holomorphic symbol cancels second complex derivatives. Opposite imaginary translations contract the field-free neutral energy when their squared shift decreases, for arbitrary finite neutral profiles; this excludes quadratic/quartic field weights. Neutral integration by parts and exact mixed square completion retain the complete correlated charged-neutral profile and explicitly retain the Y-weighted logarithmic-curvature term. Actual finite-profile regularity and the full Cartesian jet algebra are proved. These neutral integrals and algebraic identities do not assert the remaining charged integration by parts or replace the unbounded Y moment by a uniform energy constant. The general state-independent response estimate, clock-composition evolution/core regularity, controlled physical limits and physical identification remain open; neither a TOE nor a forced model revision is claimed. All 2773 parent source/script hashes and 23 numerical files are preserved. Sixteen successor modules and two scripts give 2791 hashes; sixteen imports extend the root from 8465 to 8481 lines. Standard axioms only; no new numerical probe, .lake artifact, harness change, commit or push.')
    target = root / "data/quantum_charged_dilation_mixed_diffusion_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

