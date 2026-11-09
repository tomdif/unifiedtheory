#!/usr/bin/env python3
"""Audit the centered neutral-plane coordinates, exact marginal and actual degree-independent pointwise bound."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalNeutralPlaneCoordinates', 'KFCausalQuarticPlaneDomination', 'KFCausalNeutralPlaneClockGeometry', 'KFCausalNeutralPlaneMeasure', 'KFCausalNeutralPlaneMarginal', 'KFCausalNeutralPlaneActualBound']
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
    logs = overlay / "quantum-neutral-plane-bound-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_hermite_response_hierarchy_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "7d49842ac63d00524b345b848fcae7cc6e6e35f7d1314b27b0c6c19874bc288b"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_neutral_plane_bound_audit.py",
        "scripts/verify_quantum_neutral_plane_bound.py",
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
        scope='A real five-dimensional linear change of coordinates fixes the shifted neutral polynomial argument at X+iY. Its explicit inverse, field shear, centered Gaussian exponent and determinant -4*Im(r) are proved. The exact volume Jacobian and Gaussian spectator integrals identify the original centered transverse density with a two-dimensional marginal, for V(t)=1+t^2/2+t^4/4. These are Bochner integral identities; no integrability or differentiation under the integral is inferred merely from their unconditional form. For the actual relative clock scale, real-part positivity, nonzero imaginary part at nonzero admissible shift, its rational differential equation and the exact strictly positive imaginary-plane width derivative are proved. The plane width itself is positive when alpha>0, beta>=0 and 32*beta<=alpha. A quartic slope bound and Gaussian square completion give an upper clock derivative bound with a coefficient independent of the polynomial and its degree. The actual centered marginal is differentiable pointwise and obeys this estimate at every clock point. Its finite coefficient is Dprime/D+Lprime^2/lambdaprime, using actual derivatives, not assumed slope data. Forty-two public theorem checks in six modules use only standard axioms. The coefficient has not been bounded uniformly in clock position. Integrability of the new marginal and its derivative, differentiation under that integral, a full normalization/charge-projection bridge to the existing weighted kernel, displaced source interference, general couplings, state/domain uniformity and evolution extension remain open. There is no proof yet of the Hermite hierarchy uniform bound or its failure. Negative-tail tightness, unconditional clock recovery, necessary model revision, controlled physical limits, SM/GR identification, octonion necessity and TOE remain unproved. All 2103 predecessor source hashes and numerical evidence are preserved in 2111 entries, with exactly six root imports appended and no new .lake artifacts.')
    target = root / "data/quantum_neutral_plane_bound_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

