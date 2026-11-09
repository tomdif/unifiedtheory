#!/usr/bin/env python3
"""Audit the exact neutral Fourier representation of the full correlated energy and transport response."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalNeutralFourierShift', 'KFCausalNeutralFourierField', 'KFCausalNeutralFourierEnergy', 'KFCausalJointNeutralFourierIntegral', 'KFCausalJointNeutralFourierResponse']
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
    logs = overlay / "quantum-joint-neutral-fourier-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_exact_clock_region_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "4e4ff79bfe57ab4c5f12bdf1d63baeabdb1ba629893790d0f46cda151f7c33b6"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_joint_neutral_fourier_audit.py",
        "scripts/verify_quantum_joint_neutral_fourier.py",
    ]
    hashes = dict(previous['source_sha256'])
    assert len(hashes) == 2744
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
        scope='Forty-six Lean theorems give the exact neutral Fourier representation of the complete finite correlated charged/neutral potential-energy integral. All neutral complex sources, arbitrary polynomial degrees, amplitudes and charged interference are retained. Derived Gaussian strip envelopes, L1 and L2 domains justify contour translation with multiplier exp(-2*pi*k*y). The physical field x+d becomes the frequency operator I/(2*pi)*deriv+(d-I*y), with a proved recursion for every natural field power. Plancherel identifies the original quartic energy with three nonnegative frequency squares with weights 1, 1/2, 1/4 and the common exp(-4*pi*k*y) multiplier. Fubini and an exact finite-coordinate measure equivalence identify the original full positive joint integral and Gram pairing with an iterated charged/neutral Fourier integral. The original integration order is retained; no frequency/charged reordering or singular moving-domain comparison is assumed. Slice Fourier integrability is proved and the original full joint integrability hypotheses are discharged for the actual admissible clock region and widths. The Fourier energy agrees with the existing totalEnergy, and its clock derivative is the existing totalResponse for arbitrary C1 clock coefficients. For the physical packet coefficients, the original positive slice equals the Fourier energy and the actual transport response equals its frozen-coefficient clock derivative. The exact reduced-response expression and the complete physical potential response integrated over clock are identified with this Fourier energy and its frozen derivative. This is the derivative of the full integral, not an unproved interchange with the Fourier integrand derivative. The representation exposes a new route to charged/neutral cancellations, but does not identify the previous positive cooling form with a full dissipative response form and does not establish a state-uniform response bound. Existing domain results, exact clock bounds, cooling estimates, angular obstructions and all numerical evidence remain unchanged. No numerical probe was run. General uniform response, graph-core density, evolution/domain invariance, controlled physical limits and physical identification remain open; no TOE or forced model revision is claimed. All 2744 parent source hashes and 23 numerical files are preserved; five successor modules and two scripts give 2751 hashes. Five imports extend the root from 8442 to 8447 lines. Standard axioms only and no new .lake artifacts.')
    target = root / "data/quantum_joint_neutral_fourier_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

