#!/usr/bin/env python3
"""Audit the exact weighted Hermite response hierarchy and its uniform-bound equivalence."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalNeutralHermiteBasis', 'KFCausalPolynomialLocalSuperposition', 'KFCausalPolynomialLocalGram', 'KFCausalWeightedPolynomialLocalResponse', 'KFCausalHermiteResponseHierarchy']
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
    logs = overlay / "quantum-hermite-response-hierarchy-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_polynomial_local_response_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "bad7108a599b113a5e01746c11b2087919a61ae69629603b0619c4d4dbbf58cf"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_hermite_response_hierarchy_audit.py",
        "scripts/verify_quantum_hermite_response_hierarchy.py",
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
        scope='The normalized shifted physicists Hermite polynomials at every positive width form a complex polynomial basis. Every finite neutral polynomial is a finite Hermite truncation; no Hilbert-space or operator-graph completeness is asserted. Actual projected local polynomial kernels and their derivatives admit exact finite complex double-sum expansions retaining all interference. Two independent charge-angle integrals identify the local kernel as a transverse Gram integral, deriving Hermitian symmetry, a real nonnegative diagonal and finite Gram quadratic nonnegativity. For arbitrary real weights on the three ordered factors, the weighted kernel and its actual clock derivative yield the exact reduced response. Physical weights are vacuum, mass2/2 and quartic/4. The clock-weighted response is integrable for positive clock width and its diagonal clock integral equals the weighted sum of actual existing factorRates. Exact Hermite drift and reduced-response entries are defined by these physical integrals and proved Hermitian; their finite quadratic forms equal the actual corresponding polynomial-superposition values. For a fixed displaced base and admissible epsilon,h, a relative lower bound at a clock position for every finite polynomial is equivalent to that same bound on every finite Hermite cutoff. A nonnegative constant uniform in clock position and polynomial degree exists if and only if one common constant works at every clock position and cutoff; no such existence is proved. The cutoff inequality is exactly nonnegativity of the quadratic form of R+kappa*T. This is an exact reformulation, not a bound, computed Gaussian-moment recurrence, certified numerical matrix, or proof that finite samples control higher degrees. Base displacement and regulator uniformity, arbitrary-source superpositions, positive definiteness, graph-core completeness and extension along actual evolution are not established. The predecessor zero clock displacement condition remains for interpreting projected packet graph outputs. Negative-tail tightness, unconditional clock recovery, necessary model revision, controlled physical limits, SM/GR identification, octonion necessity and TOE remain unproved. Forty-three public theorem checks in five modules use only standard axioms. All 2096 predecessor hashes and numerical evidence are preserved in 2103 entries, with exactly five root imports appended and no new .lake artifacts.')
    target = root / "data/quantum_hermite_response_hierarchy_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

