#!/usr/bin/env python3
"""Audit half-clock and pure-momentum graph limits and the neutral-vacuum uniform lower response bound."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalCorrelatedClusteredPhysicalTransfer', 'KFCausalCorrelatedClusteredClockVectors', 'KFCausalCorrelatedClusteredMomentumAmplitudes', 'KFCausalCorrelatedClusteredClockDifferential', 'KFCausalCorrelatedClusteredPureMomentumLimit', 'KFCausalCorrelatedClusteredHalfClockLimit', 'KFCausalReciprocalNeutralVacuumResponse', 'KFCausalCorrelatedClusteredVacuumUniformLimit']
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
    logs = overlay / "quantum-correlated-clustered-clock-domains-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_correlated_clustered_input_graph_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "9b2b2460cab8db5926d484cefc3df9bb083540f28e8cfaa0c3d1c3265c666f0e"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_correlated_clustered_clock_domains_audit.py",
        "scripts/verify_quantum_correlated_clustered_clock_domains.py",
    ]
    hashes = dict(previous['source_sha256'])
    assert len(hashes) == 2589
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
        scope='Forty-eight Lean theorems extend the clustered-width construction. A general positive-Gram transfer proves convergence of actual Hilbert vectors with arbitrary continuous square-integrable independent clock coefficients and exact finite physical representatives. At zero shift, product integrability constructs these physical vectors directly. The actual half-clock outputs converge, and closedness proves the natural half-clock graph and domain at the already constructed physical input limit. Pure-clock momentum coefficients are derived by differentiation: bounded inverse-clock and density terms plus a proved square-integrable Gaussian chart moment. Differentiating the actual reciprocal physical wave, with all transverse widths and correlations retained, identifies the existing finite pureMomentum output by graph uniqueness. Its Hilbert limit closes the pureMomentum graph at the same input; graph pairs converge and zero charge is preserved. Pure-momentum convergence requires epsilon>0, h!=0 and positive independent clock widths. The half-clock theorem uses the existing finite eight-output construction and hence retains abs(h)<=2*pi*epsilon/3. These results do not establish any of the four transverse kinetic output limits or the full Hamiltonian domain. Separately, graph uniqueness identifies the source-free, constant-neutral-polynomial, zero-frequency specialization with the previously audited reciprocal model. The previously proved uniform one-sided lower potential-response bound transfers to this subclass and its physical clustered limit. One constant is independent of charged degrees, family size, amplitudes and independent positive clock widths; the bound is R>=-((C+2)/epsilon)*E and requires abs(h)<=pi*epsilon/3. It includes zero or cancelling limits without dividing by energy. The limiting response is the proved scalar limit of finite potential responses; an operator-pairing identity for that response at the limiting state is not asserted. It is not a two-sided absolute bound, and the extension to arbitrary neutral polynomials, sources and frequencies is unproved. Hamiltonian second actions, graph-core density, full general-family response, evolution coverage, controlled physical limits and identification, and the physical TOE remain unproved. All 2589 parent source hashes and 23 numerical file hashes are preserved; ten new source entries give 2599. Exactly eight imports extend the root from 8313 to 8321 lines. Standard axioms only; no new .lake artifacts. Numerical results are not proof premises.')
    target = root / "data/quantum_correlated_clustered_clock_domains_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

