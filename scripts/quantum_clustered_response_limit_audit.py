#!/usr/bin/env python3
"""Audit the clock-neighborhood envelope, Leibniz identity and actual response limit."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalJointCompactPolynomialBounds', 'KFCausalJointUniformWeightEnvelope', 'KFCausalClusteredClockCompactEnvelope', 'KFCausalClusteredClockLeibniz', 'KFCausalClusteredResponseLimit']
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
    logs = overlay / "quantum-clustered-response-limit-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_clustered_clock_derivative_limit_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "3c3fcde33a24b0fa9556a9fd87cb96c13c19ad92a5689e695143945bafb946ab"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_clustered_response_limit_audit.py",
        "scripts/verify_quantum_clustered_response_limit.py",
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
        scope='Thirty-two Lean theorems derive polynomial majorants on compact parameter sets, a common integrable Gaussian/Laplace envelope throughout every compact clock interval and for all positive width spacings, and differentiation under the actual joint density integral. The old fixed-clock derivative limit is thereby identified with convergence of the existing totalResponse to the derivative of the limiting potential energy, retaining the exact pi/4 normalization and every charged interference term. The actual curve discharges the derivative and uniform width floors under alpha>0,beta>0,32*beta<=alpha,epsilon>0,abs(y)<=pi*epsilon/3. All charged degrees n and arbitrary fixed neutral complex source b and polynomial P are allowed; one neutral profile is shared across the n+1 clustered widths. The envelope can depend on n,P,b and the compact clock interval, so it is not the missing state-uniform relative response estimate. Conditional transfer theorems show absolute or upper relative bounds for all positive spacings pass to the polynomial limit, and a strict limiting upper-bound violation persists for sufficiently small positive spacings. No such violation or global bound is asserted or assumed for the convergence proof. General correlated finite sums of different charged degrees and neutral profiles, full-clock limits, Hamiltonian graph limits, graph-core density, evolution regularity, controlled physical limits and physical identification remain open. All 2547 parent source hashes are preserved in 2554 entries; exactly five imports extend the root from 8285 to 8290 lines. Numerical evidence is unchanged and is not a proof premise. All new theorem dependencies are standard axioms, with no new .lake artifacts. The physical TOE remains unproved and no required model revision follows.')
    target = root / "data/quantum_clustered_response_limit_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

