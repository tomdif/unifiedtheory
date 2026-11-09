#!/usr/bin/env python3
"""Audit the actual isolated radial transport obstruction and record separate finite coupled-kernel diagnostics."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalNeutralRadialNegativeDerivative', 'KFCausalJointNeutralRadialTransportObstruction']
NUMERICAL_SOURCES = {'scripts/neutral_hermite_response_probe.py': '5eb4b34486dd823ebdac3f167b60da0abe1723b3d2a72c6feafd6ced4195ec21', 'scripts/verify_neutral_hermite_response.py': '4d774c57ed1c8a251ceb493314b951edf734e8ccc26d829e902026b5fb60de2d'}
NEW_EVIDENCE = {'joint_neutral_coherent_scan': {'path': 'data/joint_neutral_coherent_response_probe.json', 'sha256': 'c3f2fa4f3f1199876ddd902f77e07245645ec417acb22d7fb68e9f9ddc6f0d1f', 'scope': 'Floating finite coherent-span transverse-kernel diagnostic, P_i=1. 900 tested matrices, 833 accepted, 67 rejected whole matrices for conditioning. No rank truncation, uniform theorem, full-Hamiltonian test or evolution claim.'}, 'joint_neutral_coherent_verification': {'path': 'data/joint_neutral_coherent_response_verification.json', 'sha256': 'be2e908e1f14a1999e125cc8c6aa14066792c297096438a1e8d1d172a7f4e138', 'scope': 'Independent 80-digit recomputation of two selected finite witnesses through a fresh clock solve and Gaussian moment recurrence. No interval certificate or full uniform estimate.'}}
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
    logs = overlay / "quantum-joint-radial-transport-obstruction-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_neutral_commutator_domains_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "047e2d5021bd9db56d086d4bde86c593bfd113751493caf4cfc70ba778c35598"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_joint_radial_transport_obstruction_audit.py",
        "scripts/verify_quantum_joint_radial_transport_obstruction.py",
        "scripts/joint_neutral_coherent_response_probe.py",
        "scripts/verify_joint_neutral_coherent_response.py",
    ]
    assert all(sha(root / p) == h for p, h in NUMERICAL_SOURCES.items())
    hashes = dict(previous["source_sha256"])
    assert all(sha(root / p) == h for p, h in hashes.items())
    assert not set(additions) & set(hashes)
    hashes.update({p: sha(root / p) for p in additions})
    evidence = dict(previous["numerical_evidence"])
    evidence.update(NEW_EVIDENCE)
    diagnostic = json.loads((root / "data/joint_neutral_coherent_response_probe.json").read_text())
    verification = json.loads((root / "data/joint_neutral_coherent_response_verification.json").read_text())
    assert diagnostic["test_count"] == 900 and diagnostic["rejected_cases"] == 67
    assert diagnostic["rank_truncation"] is False
    assert verification["passed"] is True and verification["mpmath_precision"] == 80
    assert verification["report_sha256"] == NEW_EVIDENCE["joint_neutral_coherent_scan"]["sha256"]
    assert all(sha(root / p) == h for p, h in diagnostic["source_sha256"].items())

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
        scope='One fixed physical coherent profile at epsilon=1, h=-1/64 and s=0 has a strictly negative squared-radius derivative at some positive radius, with strictly positive angular energy. Its actual joint angular energy factors exactly into the positive charged Laplace weight times the neutral angular energy. On the actual wedge, the isolated radial transport contribution (-shrink*Y)*J_X has no uniform upper bound relative to J: for every real M there is a charged coordinate, at the same fixed positive X and for the same state family, with M*J less than that contribution. This strengthens the preserved unbounded-coefficient result to an obstruction for the actual isolated term. It does not disprove the full integrated clock response, whose other terms are retained. All 13 public theorem dependency lists in two new modules use only standard axioms. All 2497 parent source/script hashes are preserved in 2503 entries; exactly two imports extend the 8257-line root to 8259 lines. A separate floating diagnostic evaluates the complete coherent cross kernel with all complex interference and P_i=1: 900 physical finite cases are attempted, 833 accepted, and 67 rejected as whole matrices for conditioning, with no rank truncation. The largest accepted local kernel logarithmic derivative is about 0.04976645549, independently recomputed at 80-digit precision. The earlier radial-obstruction profile has a negative full transverse-kernel logarithmic derivative at the tested clock point, about -0.000108236332367, also independently recomputed. These finite observations do not establish a uniform bound or a full-Hamiltonian or evolution statement. The coupled uniform estimate, graph-core density, evolution coverage and regularity, controlled physical limits and identification, necessary model revision and physical TOE remain unproved. All parent numerical evidence is unchanged; two new diagnostic artifacts are recorded separately. No new .lake artifacts are generated.')
    target = root / "data/quantum_joint_radial_transport_obstruction_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

