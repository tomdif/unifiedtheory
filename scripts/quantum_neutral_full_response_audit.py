#!/usr/bin/env python3
"""Audit the full Hamiltonian-form neutral response bound and its graph closure."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalPolynomialClockComposition', 'KFCausalNeutralMixedClockFactorResponse', 'KFCausalFixedCommonEnergyPairing', 'KFCausalNeutralMixedClockHamiltonian', 'KFCausalNeutralMixedClockFullBound', 'KFCausalNeutralResponseGraphClosure']
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
    logs = overlay / "quantum-neutral-full-response-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_neutral_mixed_clock_response_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "f6a0b022b93b9302385eb19614aa2b1acbc9251311f63c913eabea97d951deca"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_neutral_full_response_audit.py",
        "scripts/verify_quantum_neutral_full_response.py",
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
        scope='The actual completed charge-averaged Hamiltonian form now has a uniform lower bound for its full signed pure-clock-momentum response on every finite mixed-clock neutral exponential-polynomial state, with unit potential couplings, and on the explicitly defined closure of their state/momentum pairs in the product of completed form spaces. For fixed nonzero h there exists M>=0 depending only on groundWidth(h), such that for every epsilon>0 with |h|<=2*pi*epsilon/3, every independent positive clock width a_i, every real clock frequency p_i, every complex neutral source b_i and amplitude C_i, every finite polynomial P_i, every source count N and every physical time t, fullResponse_t>=-((M+2)/epsilon)*fullEnergy_t. Here fullEnergy_t is the squared norm of the actual completed averaged energy output of the constructed state lift, and fullResponse_t=(-2/h)*Im(inner(energyOutput_t(stateLift),energyOutput_t(momentumLift))). Both embeddings are the existing physical state and its actual pure-clock momentum. All eight factors and their physical time weights are retained. A missing clock-half/momentum composition is derived for arbitrary polynomial Gaussian packets from smooth Gaussian representatives, closed-graph source-circle integration and finite sums, and then for the mixed neutral state. The clock response is bounded below by -(1/(4*epsilon))*its unscaled clock-factor energy. The four kinetic responses are nonnegative by the existing generic graph theorem. A general charge-zero common-domain lift identifies exact averaged energy and response pairings with the eight weighted factor sums. These are mapped into the completed Hamiltonian form used by the model. The already proved potential-relative estimate and the clock/kinetic bounds combine without a residual input-norm term; the same M controls every time. The product-form closure is explicit: limits must converge in both the state and momentum completed form norms. Closedness of the actual pure-clock momentum graph and the charge-zero sector proves that such limits remain actual charge-zero momentum pairs. Continuity of energy and response extends the bound to that closure with one constant for all times. No density of this neutral closure in the full physical response domain is asserted, and no invariance under the actual Hamiltonian propagator or time-derivative/Ehrenfest identity on that closure is proved. Charged excitations, a response bound on the required full dynamical domain, general potential couplings, negative-tail tightness, unconditional clock recovery, controlled regulator/physical limits, Standard Model/general-relativity identification, octonion necessity and a physical TOE remain open. No necessary model revision follows. Thirty-five public theorem checks in six modules use only standard axioms. All 2148 predecessor source hashes and inherited numerical evidence are preserved in 2156 entries. Exactly six imports extend the 7980-line parent root; no new .lake artifacts are generated.')
    target = root / "data/quantum_neutral_full_response_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

