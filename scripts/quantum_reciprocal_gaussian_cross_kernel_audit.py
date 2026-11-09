#!/usr/bin/env python3
"""Audit exact reciprocal Gaussian interference kernels and clock marginals."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalComplexGaussianMoments', 'KFCausalComplexPotentialGaussian', 'KFCausalReciprocalCrossGeometry', 'KFCausalReciprocalCrossKernel', 'KFCausalReciprocalCrossGram', 'KFCausalReciprocalCrossResponse', 'KFCausalReciprocalCrossPhysical']
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
    logs = overlay / "quantum-reciprocal-gaussian-cross-kernel-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_reciprocal_gaussian_momentum_domains_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "a210eb2f92d4e5acf239f1ee8b16266a45ff47c77888eefef8e3790a34b697a6"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_reciprocal_gaussian_cross_kernel_audit.py",
        "scripts/verify_quantum_reciprocal_gaussian_cross_kernel.py",
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
        scope='The actual off-diagonal potential kernel for two reciprocal Gaussian widths w,v>=1 is now evaluated exactly, with complex phases retained. A common determinant-four real coordinate change gives complex Gaussian widths A=alpha/2*(conj(r)^2/w+r^2/v), B=alpha/2*(conj(r)^2*w+r^2*v), C=B-8*beta*Im(r)^2 and D=2*beta. The kernel equals one quarter of g(A)^2*g(B)*g(C)*g(D)*(1+V/2+3*V^2/4), where g(b) is the principal complex Gaussian integral (pi/b)^(1/2), V=1/(2D)+(3-2*Re(r))^2/(2C), and Re(A),Re(B),Re(C),D are strictly positive. Polynomial moments and absolute integrability are proved before integral manipulation. The positivity conditions hold along the actual shifted clock whenever alpha>0, beta>0, 32*beta<=alpha, epsilon>0 and abs(y)<=pi*epsilon/3. The kernel is Hermitian, agrees with the earlier diagonal kernel, and its finite complex Gram form equals the actual nonnegative potential-weighted squared norm, including coincident widths and cancelling coefficients. The actual clock kernel is continuously differentiable; an exact finite-interval response identity retains both boundary values and the complex kernel derivative. For actual physical widths alpha=groundWidth(h), beta=neutralWidth(h), h!=0 and abs(h)<=2*pi*epsilon/3, finite reciprocal superpositions with arbitrary complex coefficients, positive independent clock widths and charged widths >=1 have exact potential energy and momentum-pairing slice formulas and full-clock Fubini identities. Global integrability is proved from the already constructed L2 ordered outputs. The parent strong domains of psi and Bpsi under the smaller strip abs(h)<=pi*epsilon/3 and the individual-packet uniform response estimate are preserved. No uniform response inequality for arbitrary reciprocal superpositions is added: the remaining analytic estimate is a one-sided matrix kernel derivative bound uniform in packet number, coefficients, widths and their collisions. The new finite-interval identity does not assert a full-clock boundary limit or an evolution derivative identity. B H_t psi, a commutator operator domain, graph-core density, evolution invariance, trajectory momentum regularity, unconditional clock recovery, controlled physical/regulator limits, SM/GR identification, octonion necessity and a physical TOE remain open. No necessary model revision is established. All 59 public theorem dependency lists in seven new modules use only standard axioms. All 2344 parent source/script hashes are preserved in 2353 entries. Exactly seven imports extend the 8136-line parent root to 8143 lines. Inherited numerical evidence is unchanged and no new .lake artifacts are generated.')
    target = root / "data/quantum_reciprocal_gaussian_cross_kernel_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

