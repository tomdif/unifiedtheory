#!/usr/bin/env python3
"""Audit actual narrow Fourier representatives and coordinate-weighted charged derivative limits."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalNarrowFourierCoordinates', 'KFCausalNarrowFourierPackets', 'KFCausalCorrelatedClusteredNarrowFourier', 'KFCausalNarrowFourierChargedBounds', 'KFCausalDominatedRepresentedL2Limit', 'KFCausalNarrowFourierWeightedBounds', 'KFCausalNarrowFourierModelDirections', 'KFCausalNarrowFourierWeightedLimit', 'KFCausalCorrelatedClusteredNarrowLimit']
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
    logs = overlay / "quantum-correlated-clustered-narrow-fourier-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_correlated_clustered_momentum_response_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "22407afb1319271ee0c1e2d5640154b966572fefc80b6de3dbc04e2a09a090cd"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_correlated_clustered_narrow_fourier_audit.py",
        "scripts/verify_quantum_correlated_clustered_narrow_fourier.py",
    ]
    hashes = dict(previous['source_sha256'])
    assert len(hashes) == 2610
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
        scope='Sixty-six Lean theorems establish an actual unitary partial Fourier transform of the two narrow reciprocal charged modes, exact finite and limiting physical representatives, and coordinate-weighted L2 convergence of the charged quotient and its first charged derivative. The clock and neutral coordinate remain spectators; the two broad charged positions remain untransformed. Exact Gaussian Fourier normalization is pi*w/alpha, so its width factor cancels the reciprocal clustered coefficient. Every finite correlated physical vector with independent continuous L2 clock coefficients is identified with its actual transformed representative. All complex amplitudes, charged degrees, neutral sources and neutral polynomials are retained. The transformed polynomial limit is L2, and equals the unitary image of the previously constructed physical limitingVector. The charged quadratic radius is nonnegative for alpha>0; half-width Gaussian envelopes derived using factorial constants control every charged power. For any continuous weight bounded by C*(1+chargedRadius), with C>=0, the charged quotient and first charged derivative are proved L2 at every positive spacing and converge strongly in L2 to their explicit polynomial limits. Bounds for both narrow frequency coordinates and broad position coordinates verify this growth condition. The actual four model direction vectors are computed in the new coordinates, including the neutral component of direction one. These are analytic and coordinate results; identification of the weighted vectors with actions of the actual physical transverse momenta still needs proof. No transverse kinetic graph limit is asserted, and strong Hamiltonian second actions, graph-core density, general-family uniform potential response, full Hamiltonian response/evolution, controlled physical limits, physical identification and the physical TOE remain open. Envelope constants depend on degree and the fixed family, so these are not state-uniform relative response estimates. Physical-vector identification uses alpha>0,beta>0,32*beta<=alpha and continuous L2 clock coefficients; Gaussian and weighted derivative bounds only require positive alpha and beta plus the stated weight bound. All 2610 parent source hashes and all 23 numerical file hashes are preserved; eleven source additions give 2621 entries. Exactly nine imports extend the root from 8330 to 8339 lines. Only standard axioms; no new .lake artifacts. No numerical result is a proof premise.')
    target = root / "data/quantum_correlated_clustered_narrow_fourier_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

