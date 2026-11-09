#!/usr/bin/env python3
"""Audit complete clustered clock density derivatives and their integral limits."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalClusteredClockFactors', 'KFCausalClusteredClockDensity', 'KFCausalClusteredClockEnvelope', 'KFCausalClusteredClockDerivativeLimit']
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
    logs = overlay / "quantum-clustered-clock-derivative-limit-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_clustered_width_energy_limit_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "effb5147e7556690ed74f7a300bd77fc48b35a7c98fcb8e3f38f4416da083085"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_clustered_clock_derivative_limit_audit.py",
        "scripts/verify_quantum_clustered_clock_derivative_limit.py",
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
        scope='Thirty-six Lean theorems derive the complete clock derivative of the actual clustered joint potential density, prove a spacing-independent integrable envelope at every fixed geometry and velocity, and pass the positive-width-spacing limit through the integral of that derivative. The charged chart, neutral coordinate, coherent profile, Gaussian amplitude and all three canonical potential factors are differentiated. The formula is identified with deriv in the existing positiveDensity, and the limiting formula is identified with deriv in existing limitDensity. For each charged degree n and arbitrary fixed neutral complex source b and polynomial P, one neutral exponential-polynomial profile is shared across the n+1 widths. The envelope retains all interference and is a sum of squared multivariate polynomials times the exact positive Gaussian/Laplace weight. Its integrability is derived under beta>0,alpha*area(r)>0,alpha*area(r)-8*beta*Im(r)^2>0, with no assumed response bound or floating premise. It is independent of positive width spacing delta, but can depend on degree, polynomial, source, fixed geometry and velocity. The actual clock theorem discharges the derivative and width conditions at scale(epsilon,y,s) under alpha>0,beta>0,32*beta<=alpha,epsilon>0,abs(y)<=pi*epsilon/3. It proves lim_delta integral_p deriv_s positiveDensity(delta,s,p) equals integral_p deriv_s limitDensity(s,p), at each fixed clock position. It does not move the clock derivative outside the integral, identify these integrals with existing totalResponse, or assert convergence of the Hamiltonian response. A common integrable bound on a clock neighborhood and the corresponding Leibniz identification remain to be established. General finite correlated combinations of charged degrees and different neutral sources also remain beyond this confluence theorem. All 2541 parent source hashes are preserved in 2547 entries; exactly four imports extend the 8281-line root to 8285. Numerical evidence is unchanged and not a proof premise. All theorem dependencies are standard axioms; no new .lake artifacts. The unequal-width state-uniform relative response estimate, full Hamiltonian bound, graph-core density, evolution coverage, trajectory regularity, controlled physical limits, physical identification and a physical TOE remain unproved. No divergence or required model revision follows.')
    target = root / "data/quantum_clustered_clock_derivative_limit_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

