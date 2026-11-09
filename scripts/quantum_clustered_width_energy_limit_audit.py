#!/usr/bin/env python3
"""Audit actual clustered-width energy limits and charged derivative envelopes."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalJointPolynomialIntegrability', 'KFCausalClusteredWidthDensityIntegrability', 'KFCausalClusteredWidthEnergyLimit', 'KFCausalClusteredWidthChargedJet']
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
    logs = overlay / "quantum-clustered-width-energy-limit-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_clustered_width_profiles_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "18f12694f072edfdc4e1a132dacc950ee1fca26a60fddc2e9d469123b6918b79"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_clustered_width_energy_limit_audit.py",
        "scripts/verify_quantum_clustered_width_energy_limit.py",
    ]
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
        scope='Twenty-nine Lean theorems derive genuine Gaussian/Laplace polynomial integrability, identify the actual clustered-width limiting density, pass the positive-width limit through the actual energy integral, and bound the charged holomorphic derivative independently of width spacing. For every finite charged degree n and arbitrary fixed neutral coherent source b and polynomial P, widths 1+i*delta with the previously derived binomial coefficients approach the charged profile exp(-z)*z^n times exp(b*zeta)*P(zeta). All polynomial degrees and complex sources are allowed; one neutral profile is shared across the n+1 charged widths in each statement. Generic integrability holds whenever beta>0, alpha*area(r)>0, and alpha*area(r)-8*beta*Im(r)^2>0. These inequalities are discharged at actual clock scales under alpha>0,beta>0,32*beta<=alpha,epsilon>0,abs(y)<=pi*epsilon/3. The exact canonical quartic potential density decomposes into three squared multivariate polynomials times a product of three Gaussian factors with linear sources and one half-line exponential factor. Dominated convergence uses the already proved spacing-independent limiting density envelope, whose integrability is now derived. The existing Gram pairing and actual totalEnergy converge to pi/4 times the integral of that density. The result is at each fixed clock position, not a full-clock integral limit or a Hamiltonian graph limit. Separately, the exact charged derivative jet is exp(-z)*(n*q_delta(z)^(n-1)*exp(-delta*z)-q_delta(z)^n), tends to the polynomial derivative, and has norm at most exp(-Re(z))*(n*norm(z)^(n-1)+norm(z)^n) on Re(z)>=0. A chain rule covers any differentiable moving charged coordinate. This does not yet pass the complete clock derivative through the confluence limit: changing neutral geometry, the full weight derivative and an integrable local clock envelope remain to be assembled. No uniform response estimate, divergent sequence, full Hamiltonian response bound or required model change is established. All 2535 parent source hashes are preserved in 2541 entries; exactly four imports extend the 8277-line root to 8281 lines. All numerical evidence is unchanged and is not a proof premise. All public theorem dependencies are standard Lean axioms, and no new .lake artifacts are generated. Unequal-width uniform response, full Hamiltonian response, graph-core density, evolution coverage, trajectory regularity, controlled physical limits, physical identification and a physical TOE remain unproved.')
    target = root / "data/quantum_clustered_width_energy_limit_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

