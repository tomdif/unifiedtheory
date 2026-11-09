#!/usr/bin/env python3
"""Audit pointwise subsequential spectral escape and the exact negative-tail criterion."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalSmallAverageSelection', 'KFCausalClockFloorSpectralThresholds', 'KFCausalClockFloorPointwiseSpectralEscape', 'KFCausalClockFloorNegativeTailCriterion']
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
    logs = overlay / "quantum-pointwise-spectral-escape-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_actual_spectral_escape_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "3db3d30de54ef4259a4cd4f82e72e23c7598457965ad570618cd62160d84de86"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_pointwise_spectral_escape_audit.py",
        "scripts/verify_quantum_pointwise_spectral_escape.py",
    ]
    hashes = dict(previous["source_sha256"])
    assert all(sha(root / p) == h for p, h in hashes.items())
    assert not set(additions) & set(hashes)
    hashes.update({p: sha(root / p) for p in additions})
    evidence = previous["numerical_evidence"]
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
        scope='A single sequence of actual physical times now realizes the necessary negative coupled-spectral escape. A continuous unit-interval observation with average below delta has a value below delta. Threshold monotonicity is proved for the bounded localized observation and its full physical charge orbit. For full finite-energy data with positive vacuum coupling k, actual upper spectral mass can be arbitrarily small at arbitrarily late physical times. A diagonal construction selects tau_n tending to infinity, tau_n at least the initial physical time, with upper mass above -n less than 1/(n+1). For every fixed real threshold R the upper mass on this SAME sequence tends to zero. Positive clock residual supplies one c>0, independent of R, such that the analytic clock-weighted norm squared is at least 2c at every selected time; lower mass below -n is eventually at least c, and lower mass below each fixed R is eventually at least c. This is subsequential escape along individual ACTUAL physical times, not a full-time spectral limit or an unweighted probability claim. The observation remains the full charge-angle L2 orbit after C^(-1/2)D(1-D), followed by the actual coupled Fourier spectral restriction. An exact criterion is proved: clock recovery holds if and only if for every delta>0 there is a real threshold R with lower localized spectral mass below delta for all sufficiently late physical times. The eventual time may depend on delta and R. No tail propagation premise is assumed in the escape theorem, and no proof of the criterion condition is asserted for the dynamics. Recovery also implies decay of every fixed lower spectral observation for arbitrary Hilbert initial data. The reverse criterion uses full finite-energy data and k>0. Parameters remain epsilon>0,h!=0,abs(h)<=2*pi*epsilon/3,arbitrary real m,g,positive initial fast time. All static Hamiltonian factors remain. The report also corrects the previous research narrative: charge-averaged vacuum shear nonnegativity, actual imaginary-shear interpolation and initial norm comparison were ALREADY proved on the coherent span in preserved modules. Their extension to the required evolution domain and full signed matter control remain open; rederiving the coherent vacuum sign would not close those gaps. Clock recovery without a tail premise, a failing actual trajectory, necessary model revision, regulator removal, controlled physical limits, SM/GR identification, octonion necessity and the physical TOE remain unproved. All 2009 predecessor source/script hashes and numerical evidence are preserved; no new numerical evidence or .lake artifacts.')
    target = root / "data/quantum_pointwise_spectral_escape_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

