#!/usr/bin/env python3
"""Audit polynomial neutral domains and the universal quartic transport-form defect."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalQuarticNeutralDefect', 'KFCausalNeutralLinePackets', 'KFCausalNeutralLineDomain', 'KFCausalNeutralQuarticBoundary', 'KFCausalNeutralQuarticFormBound', 'KFCausalNeutralJointCurvatureForm', 'KFCausalNeutralQuarticTransportForms', 'KFCausalNeutralUniformDefect']
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
    logs = overlay / "quantum-neutral-quartic-defect-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_neutral_radial_obstruction_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "4b10ee89fa38e73919990146e31fd3a56f248ea92ffd419243c6cc17951a81f5"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_neutral_quartic_defect_audit.py",
        "scripts/verify_quantum_neutral_quartic_defect.py",
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
        scope='A quantitative quartic defect replaces the disproved neutral radius-monotonicity step. For V(x)=1+x^2/2+x^4/4 and every finite family G(zeta)=sum_i c_i exp(-beta*zeta^2+b_i*zeta) P_i(zeta), beta>0, Lean proves all polynomially weighted real-line L2 domains at every complex translation. Derivatives are explicit exponential-polynomial profiles with step(P)=P.derivative+(b-2*beta*X)*P, so the first and second derivatives have the same domains. Every real-line integration-by-parts integrability hypothesis follows from these domains; no endpoint limit is assumed. Set E=integral V*norm(f)^2, B=integral (L*V1*norm(f)^2-2*eta*V*Im(conj(f)*g)), and Q=integral (4*eta^2*V*norm(g)^2-4*L*eta*V1*Im(conj(f)*g)+(L^2-eta^2)*V2*norm(f)^2), with g=f derivative. A pointwise square completion and integral Gram argument prove B^2-4*(L^2+eta^2)*E^2<=E*Q, including zero profiles and exact cancellations. At the actual r=scale(epsilon,-h/2,s), eta=2*Im(r), L=3-2*Re(r), epsilon>0 and abs(h)<=2*pi*epsilon/3, one universal K=4*(18+8*exp(pi/6)^2) bounds the defect coefficient, giving B^2-K*E^2<=E*Q independently of packet count, complex sources and coefficients, degrees, charged widths, complex translation, h, epsilon and clock position. The actual absorbed joint Laplace profile is identified with this finite family with coefficients c_i*w_i*exp(-w_i*z). Its cross terms are retained inside the full sum, without dividing by energy or a Gram eigenvalue. Lean also proves exact pointwise first and second translation derivatives for G(x+z+(-L+i*eta)*v), and integration by parts identifies their real-line integrals with B and Q. These are integrated pointwise jets at fixed clock geometry: differentiation of the parameter-dependent unbounded real-line integral has not yet been justified, and the full moving-clock response including charged transport is not proved. Strong Hamiltonian and commutator domains for the entire enlarged joint family, graph-core density, evolution coverage, trajectory regularity and expectation derivatives remain open. No necessary model revision, controlled physical limit, physical identification or physical TOE is established. All 66 public theorem dependency lists in eight new modules use only standard axioms. All 2431 parent source/script hashes are preserved in 2441 entries, and exactly eight imports extend the 8203-line root to 8211 lines. Inherited numerical evidence is unchanged. No new .lake artifacts are generated.')
    target = root / "data/quantum_neutral_quartic_defect_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

