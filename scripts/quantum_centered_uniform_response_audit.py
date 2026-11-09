#!/usr/bin/env python3
"""Audit the actual centered projected response bound uniform in clock and polynomial degree."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalNeutralPlaneNormalizedGeometry', 'KFCausalNeutralPlanePrefactorScore', 'KFCausalNeutralPlaneUniformScore', 'KFCausalNeutralPlaneIntegrability', 'KFCausalNeutralPlaneUniformGrowth', 'KFCausalCenteredPolynomialKernel', 'KFCausalCenteredPolynomialResponseBound']
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
    logs = overlay / "quantum-centered-uniform-response-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_neutral_plane_bound_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "007e7805ca2469dce5970c8953fc1f0c2065cce0b7ba078e2ef873fca0e527da"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_centered_uniform_response_audit.py",
        "scripts/verify_quantum_centered_uniform_response.py",
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
        scope='For centered sources q=k=0 and physical potential weights vacuum=mass2=quartic=1, an actual relative signed-response lower bound uniform in clock position and all finite neutral polynomials is now proved. The unbounded clock variable is normalized to E/(epsilon+E) in (0,1); exact rational velocity and shear identities cancel inverse powers of Im(r). A proved Gaussian-prefactor invariant yields its actual logarithmic derivative. The actual pointwise score equals a rational expression continuous on a fixed compact region containing all admissible clock geometries, including real-scale and endpoint limits. This produces a finite nonnegative constant C depending only on the positive charged width, uniform in clock position, admissible epsilon and imaginary shift, beta and polynomial degree. Original centered factors are L2, their centered potential density is integrable, and the exact real-coordinate map and Gaussian spectator products transfer integrability to the two-dimensional marginal. The pointwise differential bound implies exponential finite-clock growth; integral monotonicity transfers this to the original centered transverse energy without assuming derivative-integral interchange. Zero source and unit amplitude are proved for every charge angle at q=k=0, identifying the marginal exactly with the existing projected weighted kernel. Its existing actual derivative and the growth inequality give Tprime<=C*T. Combining this with the proved coefficient lower bound and clock>=epsilon yields R>=-((C+2)/epsilon)*T. Hence one nonnegative kappa works for every clock position and finite polynomial in the centered family, and the prior exact equivalence gives the same bound at every finite Hermite cutoff and every real Hermite basis center. Constants are existence results, not evaluated sharp numerical bounds. General potential couplings, displaced source interference, arbitrary-source superpositions, necessary domain/core and state uniformity, preservation or extension along actual physical evolution, regulator/physical limits, negative-tail tightness and unconditional clock recovery remain unproved. Centered-family membership is not claimed to be preserved by the full dynamics. No necessary model revision, SM/GR identification, octonion necessity or physical TOE is proved. Forty-five public theorem checks in seven modules use only standard axioms. All 2111 predecessor source hashes and numerical evidence are preserved in 2120 entries, with exactly seven root imports appended and no new .lake artifacts.')
    target = root / "data/quantum_centered_uniform_response_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

