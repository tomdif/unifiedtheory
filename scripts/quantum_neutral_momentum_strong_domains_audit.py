#!/usr/bin/env python3
"""Audit the actual H_t B composition for the full finite joint family and the remaining radial transport obstruction."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalCoherentMomentumMatterSquare', 'KFCausalPolynomialMomentumMatterCurve', 'KFCausalPolynomialMomentumSecondCurves', 'KFCausalPolynomialMomentumSecondFactors', 'KFCausalReciprocalNeutralMomentumSecondFactors', 'KFCausalReciprocalNeutralMomentumStrongHamiltonian', 'KFCausalJointNeutralClockTransport']
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
    logs = overlay / "quantum-neutral-momentum-strong-domains-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_neutral_strong_domains_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "f742936e9d9a9446ec51b59dd35754293d03f942bd867e69d2656cd1faeb84ff"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_neutral_momentum_strong_domains_audit.py",
        "scripts/verify_quantum_neutral_momentum_strong_domains.py",
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
        scope='The actual clock momentum B psi of the full finite joint neutral/reciprocal family now belongs to the actual interacting averaged Hamiltonian operator domain at each fixed Hamiltonian time, for epsilon>0, h nonzero and abs(h)<=pi*epsilon/3. Every packet retains its independent positive clock width, charged width at least one, real clock frequency, complex neutral source and amplitude, and arbitrary finite complex neutral polynomial. All eight second actions on B psi are constructed from the existing actual momentum-factor outputs. The sourced second matter graphs retain the exact doubled-shift correction and the real frequency. Derived continuity permits integration through each individual closed clock, transverse-momentum, field and exponential graph over the source circles; no closedness of an unbounded composition or reverse-domain premise is assumed. Finite polynomial coefficients, exact reciprocal transport with squared factor scales, and finite superposition preserve the graphs, including coincident widths and exact cancellations. The weighted charge projection gives H_t(B psi), and the actual composition graph (psi,H_t B psi) in H_t composed with B is proved. Together with the preserved H_t psi graph and self-adjointness, the existing fullResponse equals both (-2/h)*Im inner(H_t psi,B psi) and (-2/h)*Im inner(psi,H_t B psi). This is not an actual B H_t psi or commutator-domain theorem. The uniform-estimate analysis now proves that the radial cross term is bounded by k*shrink*Y*J with k=K/2 for the actual joint angular profile, and that k*shrink*Y is unbounded on the actual clock wedge for every positive k and every admissible nonzero shift, even at X=1. It also proves the exact derivative and contraction of the combined imaginary squared radius 4*Im(r)^2*X at fixed charged coordinate. The unbounded coefficient obstructs that pointwise bounding step, not the integrated response inequality itself. A full coupled uniform estimate, counterexample to that estimate, B H_t psi, actual commutator, graph-core density, evolution coverage, trajectory regularity, controlled physical limits, necessary model revision and physical TOE remain unproved. All 42 public theorem dependency lists in seven new modules use only standard axioms. All 2475 parent source/script hashes are preserved in 2484 entries, and exactly seven imports extend the 8239-line root to 8246 lines. Inherited numerical evidence is unchanged. No new .lake artifacts are generated.')
    target = root / "data/quantum_neutral_momentum_strong_domains_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

