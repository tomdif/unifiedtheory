#!/usr/bin/env python3
"""Audit clustered-width profile limits and finite response diagnostics."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalClusteredWidthProfiles']
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
    logs = overlay / "quantum-clustered-width-profiles-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_joint_angular_clock_obstruction_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "b980893bfaf538b30cc5c8896e71099f5ccd5d63fa6a27504749c5a863aff0c3"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_clustered_width_profiles_audit.py",
        "scripts/verify_quantum_clustered_width_profiles.py",
        "scripts/joint_neutral_clustered_response_probe.py",
        "scripts/verify_joint_neutral_clustered_response.py",
    ]
    hashes = dict(previous["source_sha256"])
    assert all(sha(root / p) == h for p, h in hashes.items())
    assert not set(additions) & set(hashes)
    hashes.update({p: sha(root / p) for p in additions})
    evidence = dict(previous["numerical_evidence"])
    for key, path in [("joint_neutral_clustered_scan", "data/joint_neutral_clustered_response_probe.json"),
                      ("joint_neutral_clustered_verification", "data/joint_neutral_clustered_response_verification.json")]:
        assert key not in evidence
        evidence[key] = dict(path=path, sha256=sha(root/path))
    scan = json.loads((root/evidence["joint_neutral_clustered_scan"]["path"]).read_text())
    verified = json.loads((root/evidence["joint_neutral_clustered_verification"]["path"]).read_text())
    assert verified["passed"] and verified["report_sha256"] == evidence["joint_neutral_clustered_scan"]["sha256"]
    assert scan["test_count"] == verified["test_count"] == 44
    assert verified["independently_integrated_witness_count"] == 2
    assert scan["rank_truncation"] is False and verified["rank_truncation"] is False
    assert scan["parent_report"] == dict(path=str(previous_path.relative_to(root)), sha256=previous_hash)
    assert scan["root_sha256"] == previous["root_check"]["source_sha256"]
    assert scan["source_sha256"] == verified["source_sha256"]
    assert all(sha(root/p) == h for p, h in scan["source_sha256"].items())
    assert verified["verifier_sha256"] == sha(root/"scripts/verify_joint_neutral_clustered_response.py")
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
        scope='Twelve Lean theorems derive an exact admissible clustered-width Laplace sum and its pointwise charged-polynomial limit, with a spacing-independent bound on the closed right half-plane. Widths are 1+i*delta for delta>0, and binomial coefficients divided by delta^n and by the width give exp(-z)*((1-exp(-delta*z))/delta)^n. The limit is exp(-z)*z^n. The mean-value theorem yields quotient norm at most norm(z) whenever Re(z)>=0. The existing joint profileSum with any fixed neutral profile inherits the limit and norm bound. The actual positive joint density converges pointwise to limitDensity and is dominated by that same nonnegative limiting density on the Laplace half-line when alpha*area(r)>=0. Integrability of that envelope, exchange of limits with the integrated kernel or its clock derivative, and Hamiltonian graph convergence are not asserted. Separately, 44 complete finite clustered-width Gram matrices at h=epsilon=100, clock offset 1, physical alpha=1/200 and beta=1/6400 are computed at 120 decimal digits with all modes and complex interference retained. The scan reaches 15 widths, neutral degree 8 and dimension 99; the largest observed logarithmic derivative is approximately 0.15223344823714652067, normalized by epsilon/clock approximately 0.04094187994895376332. Two selected fixed witnesses are independently integrated and differentiated at 160 digits using Gaussian quadrature orders 11 and 13, agreeing with saved quotients within 1e-60. These are finite floating computations, not a uniform estimate, an interval certificate, a continuous confluent limit, or a divergence proof. All 2530 parent source hashes are preserved in 2535 entries; exactly one import extends the 8276-line root to 8277. All previous numerical evidence is retained. No new .lake artifacts or nonstandard Lean axioms are introduced. Unequal-width uniform integrated response, full Hamiltonian response, density/core and evolution coverage, controlled physical limits, physical identification and a physical TOE remain unproved.')
    target = root / "data/quantum_clustered_width_profiles_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

