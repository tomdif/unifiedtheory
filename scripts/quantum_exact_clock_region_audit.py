#!/usr/bin/env python3
"""Audit the exact physical clock region, joint cooling coercivity and neutral form bounds."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalClockFloorExactScaleRegion', 'KFCausalJointClockCoolingCoercivity', 'KFCausalJointNeutralExactRegionBound', 'KFCausalJointClockJetAbsorption']
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
    logs = overlay / "quantum-exact-clock-region-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_correlated_clustered_hamiltonian_clock_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "cbed8d34c7d5e18e423d92880ab97886a6a05e9e1a1e6452d65d8e150eb5db00"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_exact_clock_region_audit.py",
        "scripts/verify_quantum_exact_clock_region.py",
    ]
    hashes = dict(previous['source_sha256'])
    assert len(hashes) == 2738
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
        scope='Thirty-three Lean theorems derive a sharper exact region for the actual complex relative clock scale and quantitative estimates for the joint cooling and neutral form. The real part of the exact inverse-clock equation is proved, not imposed as a region hypothesis. It forces nonnegative real clock displacement, 1/2<=Re(r^2)<=1, 1<=|r|^2<=2, |Re(r)-1|<=Im(r)^2 and Im(r)^2<=1/2 throughout the original admissible strip, including zero shift. The physical field slope lies between 1/2 and 2, and its squared joint field/neutral direction lies between 1 and 6. The normalized clock denominator lies between 1/4 and 4. The simultaneous charged cooling quadratic form splits exactly into two nonnegative squares and is bounded below by t/4 times the Euclidean square, with t the normalized clock fraction. The corrected derivative of the complex charged Gaussian width is identified with the same cooling coefficients, with no division by the imaginary shift. The exact region gives the neutral second-form and curvature defect constant 24 and the fixed-charged-coordinate radial derivative bound -12 times the angular energy. The normalized field/neutral velocity has squared norm at most 32. A proved completion of squares absorbs its mixed jet into the simultaneous charged cooling form with remainder 128*t*c^2, regularly through t=0 and zero imaginary shift. The actual physical field/neutral derivative is identified with this jet. This is a local algebraic absorption bound; its variables have not yet been identified with all integrated response terms. The joint versions retain arbitrary finite correlated charged coefficients and arbitrary neutral complex sources and polynomials. These are quantitative ingredients for the missing integrated response inequality, not a proof of a full family-independent energy-relative response bound. The isolated and complete fixed-coordinate angular obstructions remain valid; a complete charged integral and its boundary/cancellation terms must still be controlled. No Gaussian probe, finite-degree computation, Bergman-space theorem or numerical evidence is used as a proof premise. The previous B H/H B domain and graph-limit results are preserved. The general uniform response, graph-core density, dynamics, physical limits and physical identification remain open, and no TOE or forced model revision is claimed. All 2738 parent source hashes and 23 numerical files are preserved; four successor modules and two scripts give 2744 hashes. Four imports extend the root from 8438 to 8442 lines. Standard axioms only and no new .lake artifacts.')
    target = root / "data/quantum_exact_clock_region_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

