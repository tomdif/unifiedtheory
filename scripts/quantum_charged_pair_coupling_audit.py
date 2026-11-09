#!/usr/bin/env python3
"""Audit the exact local transverse charged-pair coupling certificate."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalPolynomialGaussianIntegrals', 'KFCausalChargedPairIntegral', 'KFCausalChargedPairCoordinates', 'KFCausalChargedPairTransverseCoupling', 'KFCausalChargedPairLocalCertificate']
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
    logs = overlay / "quantum-charged-pair-coupling-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_neutral_closure_obstruction_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "0de4562d288e99bec6336d844eb00fa6b3b09dc941dbc08d45b7395d7c56d15b"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_charged_pair_coupling_audit.py",
        "scripts/verify_quantum_charged_pair_coupling.py",
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
        scope='Lean proves a strictly nonzero transverse cross integral for the actual centered complex shifted Gaussian, the transported paired quadratic multiplier P(q)=q0*q1-q2*q3, and the unit quartic potential W(F)=1+F^2/2+F^4/4. A real sum/difference and shear transformation has determinant minus two and exactly diagonalizes the Gaussian norm. Its paired widths are A=alpha*Re(r^2)-8*beta*Im(r)^2 and B=alpha*Re(r^2). At every admissible nonzero imaginary clock shift, the existing clock geometry and 32*beta<=alpha imply 0<A<B. Reflection of the real field coordinate removes the odd quartic terms; interchanging the paired coordinates then gives a pointwise nonnegative symmetrized integrand, strictly positive on an open set. Polynomial Gaussian integrability is proved for arbitrary finite dimension and polynomial. Exact spectator integration proves that the real transverse integral against P is strictly negative. The actual shifted polynomial contributes r^2, whose real part is positive, so the complex ordered-density integral has strictly negative real part and is nonzero. This specializes to the physical widths alpha=groundWidth(h), beta=neutralWidth(h), and shift y=-h/2 at every clock position under h!=0, epsilon>0 and abs(h)<=2*pi*epsilon/3. The proof uses no quadrature, finite cutoff or assumed nonzero coupling. This is a local transverse integral certificate. Operator-factor graphs and completed-form membership of this specific quadratic excited state, its actual zero-charge and plane-interchange identification, the full clock integral, kinetic cross terms, and identification with the full Hamiltonian form pairing remain to be proved. It therefore does not yet prove that evolution leaves the restricted neutral class, that the response inequality fails, or that the physical model must change. Enlarged-domain response control, dynamical momentum regularity, negative-tail tightness, unconditional clock recovery, controlled physical/regulator limits, Standard Model/general-relativity identification, octonion necessity and a physical TOE remain unproved. Fifty-three public theorem checks in five modules use only standard axioms. All 2163 predecessor source hashes and inherited numerical evidence are preserved in 2170 entries. Exactly five imports extend the 7991-line parent root; no new .lake artifacts are generated.')
    target = root / "data/quantum_charged_pair_coupling_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

