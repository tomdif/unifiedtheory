#!/usr/bin/env python3
"""Audit reciprocal wedge geometry and uniform positive-weight comparison."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalReciprocalWedgeGeometry', 'KFCausalReciprocalWedgeVelocity', 'KFCausalReciprocalWedgeNesting', 'KFCausalReciprocalWedgePrefactor', 'KFCausalReciprocalWedgeWeight', 'KFCausalReciprocalWedgeComparison', 'KFCausalReciprocalWedgeLaplace']
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
    logs = overlay / "quantum-reciprocal-wedge-comparison-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_reciprocal_gaussian_cross_kernel_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "f35468e05117a42cfc33e2739a5770168e8a47c98d39bb11ef613b412e64a352"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_reciprocal_wedge_comparison_audit.py",
        "scripts/verify_quantum_reciprocal_wedge_comparison.py",
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
        scope='A new geometric route to the reciprocal superposition response estimate is established. With gamma=alpha*r^2/2, B=conj(gamma)*w+gamma*v and A*w*v=conj(B), the broad Gaussian factor equals pi*w*v/conj(B); its reciprocal denominator is an actual absolutely integrable positive-half-line complex Laplace transform. Products of finite modes combine exactly into the squared norm of the single Laplace sum F(z)=sum_i c_i*w_i*exp(-w_i*z). The real-linear chart z=gamma*x+conj(gamma)*y maps x,y>=0 to a wedge, with explicitly inverse coordinates and absolute inverse Jacobian J=abs(1/(alpha^2*area(r)*Re(r)*Im(r))). The aperture squared is 4*Re(r)^2*Im(r)^2/area(r)^2. Its actual clock derivative is -4*shrink*aperture with shrink>=0, giving nested wedges as clock time increases. At fixed z the first inverse coordinate X has derivative drift*X-shrink*Y; the neutral exponent 8*beta*Im(r)^2*X has a proved nonpositive derivative throughout the wedge for beta>=0. The Jacobian logarithmic derivative is 2*drift. A compact smaller-strip region proves a positive field slope d=3-2*Re(r) and uniform drift and field logarithmic-slope bounds, including limits where Im(r)=0. This gives one universal C>=0 for the one-sided derivative bound of the positive weight J*exp(eta*8*beta*Im(r)^2*X)*(c0+c1*T+c2*T^2), T=eta*d^2*X, for all alpha>0,beta>=0,eta>=0,c0,c1,c2>=0,epsilon>0,0<abs(y)<=pi*epsilon/6 and z in the actual wedge. The integrated-in-clock comparison is proved, including zero extension outside each moving wedge: W_t(z)<=exp(C*(t-s))*W_s(z) for all z and s<=t. This comparison is independent of packet number, coefficients, charged widths and separation; it uses no Gram spectral gap. The exact representation of the physical cross-kernel Gram form as an integral of this positive wedge weight remains unproved. In particular this checkpoint does not yet give a uniform matrix kernel derivative bound, full-clock superposition response bound, B H_t psi, commutator operator domain, graph-core density or evolution regularity. The parent actual strong Hamiltonian domains of psi and Bpsi and individual-packet response bound are preserved. The smaller strip y=-h/2 corresponds to the existing strong-domain condition abs(h)<=pi*epsilon/3. Unconditional clock recovery, controlled physical/regulator limits, SM/GR identification, octonion necessity and a physical TOE remain open; no necessary model revision is established. All 49 public theorem dependency lists in seven new modules use only standard axioms. All 2353 parent source/script hashes are preserved in 2362 entries. Exactly seven imports extend the 8143-line parent root to 8150 lines. Inherited numerical evidence is unchanged; exploratory high-precision calculations are not included as certified evidence. No new .lake artifacts are generated.')
    target = root / "data/quantum_reciprocal_wedge_comparison_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

