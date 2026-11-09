#!/usr/bin/env python3
"""Audit arbitrary-degree polynomial Gaussian domains and neutral Hermite packets."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalSourceCircleCoefficients', 'KFCausalL2IntegralRepresentative', 'KFCausalSourcedCurveDomain', 'KFCausalPolynomialGaussianStates', 'KFCausalPolynomialGaussianDomain', 'KFCausalNeutralHermiteDomain']
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
    logs = overlay / "quantum-polynomial-gaussian-domain-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_charge_conservation_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "92d8a58152c531a2ef9c797d482650717bb8a448e3b1f76d4c1b8050e72174b0"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_polynomial_gaussian_domain_audit.py",
        "scripts/verify_quantum_polynomial_gaussian_domain.py",
    ]
    additions += list(NUMERICAL_SOURCES)
    assert all(sha(root / p) == h for p, h in NUMERICAL_SOURCES.items())
    hashes = dict(previous["source_sha256"])
    assert all(sha(root / p) == h for p, h in hashes.items())
    assert not set(additions) & set(hashes)
    hashes.update({p: sha(root / p) for p in additions})
    evidence = dict(previous["numerical_evidence"])
    evidence["neutral_hermite_response_probe"] = dict(
        path="data/neutral_hermite_response_probe.json",
        sha256="88a16fa151758e3bfea71f1ebcd92b46a255a75e51c0bf36562c3db9993a768d",
        status="Unchanged floating numerical research; projected response identification and uniform bound remain open.")
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
        scope='For epsilon>0, a>0, h!=0 and |h|<=2pi epsilon/3, arbitrary complex-sourced physical Gaussians of widths alpha=1/(2|h|), beta=1/(64|h|), multiplied by any finite complex polynomial in any one of the five physical transverse coordinates, belong to all eight natural ordered energy-factor domains. Every factor output is constructed as a finite sum of normalized source-circle integrals. Source-circle coefficient extraction at every natural degree follows from Cauchy integration, and a weak Fubini theorem identifies the Hilbert integral with the physical pointwise polynomial. Matter compositions are integrated through their closed intermediate exponential and multiplication graphs; closedness of the composed natural matter factors is not assumed. The neutral Hermite specialization uses the explicit physicists recurrence and the same sqrt(2w)*(x4-B) and sqrt(2^n n!) factors as the numerical profiles, before charge projection. This proves natural factor and unaveraged energy-form admissibility, not Hamiltonian operator-domain membership, projected numerical response identification, graph-core density, response bounds uniform in degree, evolution-domain control, unconditional clock recovery, a necessary model change, controlled physical limits, SM/GR identification, octonion necessity or a TOE. Thirty-four public theorem dependency lists use only standard axioms. All 2039 predecessor source/script hashes are preserved; the unchanged numerical Hermite report and its two scripts are added to the evidence chain. The root appends six imports; no new .lake artifacts.')
    target = root / "data/quantum_polynomial_gaussian_domain_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

