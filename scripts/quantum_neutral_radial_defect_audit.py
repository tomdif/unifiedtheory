#!/usr/bin/env python3
"""Audit actual neutral integral derivatives, corrected convexity and the uniform radial defect."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalNeutralTranslationEnvelope', 'KFCausalNeutralTransportDomination', 'KFCausalNeutralIntegralDerivatives', 'KFCausalNeutralCorrectedConvexity', 'KFCausalNeutralTranslatedMarginal', 'KFCausalCorrectedAngularComparison', 'KFCausalNeutralUniformRadialDefect', 'KFCausalJointNeutralRadialEstimate']
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
    logs = overlay / "quantum-neutral-radial-defect-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_neutral_quartic_defect_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "4fc7e570280b6f78ff0f48f67ff776985ea61acd37ed38d74a996d3222aeec34"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_neutral_radial_defect_audit.py",
        "scripts/verify_quantum_neutral_radial_defect.py",
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
        scope='The first two parameter derivatives of the actual neutral energy now pass through the unbounded real-line integral. For every finite complex Gaussian exponential-polynomial family with beta>0 and every complex translation, compact translation sets have derived common Gaussian L2 envelopes, including multiplication by the quartic potential. Products of these envelopes give integrable common bounds on the first and second transport derivatives. No domination or derivative-interchange hypothesis is supplied. The actual energy U(v)=integral_x V(x)*norm(G(x+z+(-L+i*eta)*v))^2 has derivatives equal to the previously proved B and Q forms, and (Uprime)^2-4*(L^2+eta^2)*U^2<=U*Usecond. An exact real translation identifies U(v) with the physical neutral marginal integral V(x+L*v)*norm(G(x+z+i*eta*v))^2. Retaining the square-completion remainder proves exp(a*v^2)*U(v) convex whenever a>=2*(L^2+eta^2), without division by energy or a nonzero-profile hypothesis. Its symmetric sum is nondecreasing on nonnegative radii. Exact angular symmetrization then proves exp(a*rho^2)*A(rho) nondecreasing for the actual angular marginal, with A_prime(rho)>=-2*a*rho*A(rho) for rho>0. For J(X)=A(sqrt(X)), Lean derives J_prime(X)>=-a*J(X) for X>0. At r=scale(epsilon,-h/2,s), eta=2*Im(r), L=3-2*Re(r), epsilon>0 and abs(h)<=2*pi*epsilon/3, the single constant K=4*(18+8*exp(pi/6)^2) allows a=K/2. The exact absorbed joint Laplace profile at each fixed charged coordinate is identified with this family using coefficients c_i*w_i*exp(-w_i*z), so the uniform bound J_prime(X)>=-(K/2)*J(X) includes all complex interference, arbitrary finite degrees, complex sources and coefficients, all charged widths, coincident widths and exact cancellation. No width or degree cutoff and no Gram eigenvalue division is used. The radius and area derivatives hold the clock geometry and charged coordinate fixed. They are not the full moving-clock derivative; combining this quantitative defect with charged transport, the changing geometry and wedge remains open. Strong Hamiltonian and commutator domains for the entire enlarged joint family, graph-core density, evolution coverage, trajectory regularity and expectation derivatives remain open. No necessary model revision, controlled physical limit, physical identification or physical TOE is established. All 67 public theorem dependency lists in eight new modules use only standard axioms. All 2441 parent source/script hashes are preserved in 2451 entries, and exactly eight imports extend the 8211-line root to 8219 lines. Inherited numerical evidence is unchanged. No new .lake artifacts are generated.')
    target = root / "data/quantum_neutral_radial_defect_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

