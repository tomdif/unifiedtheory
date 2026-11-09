#!/usr/bin/env python3
"""Audit the actual finite neutral-superposition potential-response bound."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalNeutralCrossKernel', 'KFCausalNeutralFiniteGram', 'KFCausalNeutralFiniteResponse', 'KFCausalNeutralCrossDensity', 'KFCausalNeutralCrossPairing', 'KFCausalNeutralFinitePhysicalState', 'KFCausalNeutralFinitePairing', 'KFCausalNeutralFinitePotential', 'KFCausalNeutralFinitePhysicalBound', 'KFCausalNeutralFiniteCharge']
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
    logs = overlay / "quantum-neutral-superposition-response-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_neutral_displaced_response_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "20aac7d34d6613b6f31d09702c53f37d74ca058e1868d4db675a08afb37528b8"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_neutral_superposition_response_audit.py",
        "scripts/verify_quantum_neutral_superposition_response.py",
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
        scope='A relative lower bound is proved for the actual signed ordered-potential response of every finite neutral exponential-polynomial Hilbert state, with unit vacuum, quadratic and quartic potential couplings. For fixed nonzero h there exists M>=0 depending only on groundWidth(h), such that for every epsilon>0 with |h|<=2*pi*epsilon/3, every positive common Gaussian clock width a, every finite number N of sources, arbitrary complex b_i and C_i and finite complex polynomials P_i, the actual response satisfies R>=-((M+2)/epsilon)*E. Here the state is the finite sum of the existing PolynomialGaussianDomain.input states with neutralSource(b_i), amplitude C_i, clock frequency zero and polynomial coordinate4. Its pure-clock momentum is constructed and both state and momentum belong to all eight actual energy-factor domains. E is the weighted sum of squared norms of the vacuum, field and field-square ordered outputs with weights1,1/2,1/4. R is the corresponding weighted signed pairing (-2/h)*Im(inner(output,momentumOutput)). Their full clock integrals are identified exactly with the local kernels. Cross-source kernels and their actual derivatives are obtained from the existing dominated integral derivative theorem, retaining every complex coefficient and off-diagonal term. Finite Gram expansion identifies the kernel with the full squared norm of sum_i C_i exp(b_i z) P_i(z). The previously proved finite-clock growth yields a uniform derivative bound and a local reduced-response lower bound. All cross-source energy and response densities are absolutely integrable; Fubini and the previously proved clock integration by parts identify their integrals with actual ordered-operator pairings. Multiplication by the nonnegative common clock weight and integral monotonicity transfer the local lower bound to the full actual ordered-potential response. The full state and its pure-clock momentum are proved to lie in the actual zero-charge sector; projection fixes the state and the standing charge graph contains (state,0). This closes the finite neutral-source interference and physical response bridge at a common clock width. The bound is uniform in that width, but superpositions with different clock widths or frequencies within one state are not covered. No claim is made of density of this neutral family in the required full dynamical domain or of preservation by full physical evolution. Charged excitations and displacements, general couplings, full Hamiltonian response control, dynamical domain extension, negative-tail tightness, unconditional clock recovery and controlled regulator/physical limits remain open. No necessary model revision, SM/GR identification, octonion necessity or physical TOE is proved. Sixty-seven public theorem checks in ten modules use only standard axioms. All 2128 predecessor source hashes and numerical evidence are preserved in 2140 entries, with exactly ten root imports appended and no new .lake artifacts.')
    target = root / "data/quantum_neutral_superposition_response_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

