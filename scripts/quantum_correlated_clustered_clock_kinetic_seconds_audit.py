#!/usr/bin/env python3
"""Audit actual clustered clock and kinetic second actions and their original finite-output limits."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalNarrowGaussianSecondMoments', 'KFCausalNarrowFourierSecondMomentStates', 'KFCausalNarrowPacketSecondDifferential', 'KFCausalNarrowPacketSecondStates', 'KFCausalNarrowPacketSecondMomentumGraphs', 'KFCausalClusteredWidthSecondJet', 'KFCausalNarrowFourierSecondJetLimit', 'KFCausalClusteredPacketSecondCoordinates', 'KFCausalNarrowFourierQuadraticWeights', 'KFCausalNarrowBlockSecondLimit', 'KFCausalCorrelatedClusteredSecondTransverseGraphs', 'KFCausalCorrelatedClusteredKineticSecondLimit', 'KFCausalCorrelatedClusteredPhysicalKineticSeconds', 'KFCausalCorrelatedClusteredOriginalKineticSeconds', 'KFCausalFullMomentumClockAmplitude', 'KFCausalCorrelatedClusteredClockSecondLimit']
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
    logs = overlay / "quantum-correlated-clustered-clock-kinetic-seconds-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_correlated_clustered_kinetic_domains_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "2200d97782aaceadf6bda1f03996871599173bb9a6911ef36f9485db7833926e"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_correlated_clustered_clock_kinetic_seconds_audit.py",
        "scripts/verify_quantum_correlated_clustered_clock_kinetic_seconds.py",
    ]
    hashes = dict(previous['source_sha256'])
    assert len(hashes) == 2638
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
        scope='One hundred five Lean theorems construct and identify all five natural clock and kinetic second actions on the existing correlated clustered physical state and its actual pure-clock momentum, and prove strong convergence of the corresponding ten original finite strong-Hamiltonian second outputs. Quadratic Gaussian moments have derived L1/L2 integrability and exact physical and narrow Fourier representatives. Complete second physical directional derivatives retain the broad-neutral cross term and second neutral polynomial derivative. These constructed L2 vectors are identified with successive actions of the actual maximal transverse momenta. The second charged jet is derived by differentiating the first jet; its exact width-cube sum, polynomial limit and spacing-independent envelope for 0<delta<=1 are proved. Weighted second-jet L2 convergence and quadratic coordinate growth bounds give all four complete second-derivative block limits. Both successive transverse graph steps and their strong limits are explicit. The natural kinetic second action is D P_j P_j D, with D the bounded inverse half-clock; no arbitrary composition is presumed closed. The original finite second kinetic outputs are identified by graph uniqueness, and converge to the constructed second actions on both psi and B psi. Their form pairing identities hold on the natural energy-factor test domains. Full-clock input and momentum amplitudes have derived continuous L2 representatives, using chart Gaussian moments; they identify the actual second half-clock action and the limits of the original finite second clock outputs. Generic kinetic construction uses alpha>0,beta>0,32*beta<=alpha,epsilon>0 and independent continuous L2 clock coefficients. Physical identification uses h!=0 and positive independent clock widths. The kinetic limiting second graphs themselves need no imaginary-clock strip bound; identification with the existing finite strong-Hamiltonian second outputs retains |h|<=pi*epsilon/3. The clock second checkpoint is also stated under this narrower strip. This proves the five clock/kinetic second factors, not the three ordered potential second factors. The general potential second-action limits, full interacting Hamiltonian graph convergence on this limiting family, H B/B H convergence, graph-core density, a general-family uniform potential response estimate, dynamics, controlled physical limits, physical identification and the physical TOE remain open. The parent uniform clock/kinetic response bound remains proved; the new second-derivative domination constants depend on charged degree and fixed family and are not a new uniform potential estimate. No model change or divergent sequence is proved. All 2638 parent source hashes and all 23 numerical file hashes remain unchanged; eighteen source additions give 2656 entries. Exactly sixteen imports extend the root from 8354 to 8370 lines. Only standard axioms; no new .lake artifacts. No numerical result is a proof premise.')
    target = root / "data/quantum_correlated_clustered_clock_kinetic_seconds_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

