#!/usr/bin/env python3
"""Audit the quartic angular-radius obstruction, including an actual clock scale."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalNeutralRadialCoherentKernel', 'KFCausalCompactAngularDerivative', 'KFCausalNeutralRadialCurvature', 'KFCausalNeutralRadialObstruction', 'KFCausalNeutralRadialActualGeometry', 'KFCausalNeutralRadialActualObstruction']
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
    logs = overlay / "quantum-neutral-radial-obstruction-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_reciprocal_neutral_positive_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "35f58cb35198813e76e9a4f475d6daa5afe6abd0c3d731ee29736273135751ab"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_neutral_radial_obstruction_audit.py",
        "scripts/verify_quantum_neutral_radial_obstruction.py",
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
        scope='A proposed quartic angular-radius monotonicity step is disproved for an actual admissible clock scale. Exact Gaussian moments evaluate a coherent neutral marginal, and compact-interval differentiation derives its first and second angular-radius derivatives with a proved dominating bound. An explicit rational-geometry example has normalized curvature -47889/64000. The actual-clock example uses epsilon=1, h=-1/64, clock position s=0, groundWidth=32, neutralWidth=1, and r=scale(1,1/128,0). Lean proves norm(r-1)<=1/128, eta=2*Im(r) nonzero with abs(eta)<=1/64, and L=3-2*Re(r) with abs(L-1)<=1/64. Its fixed coherent source is b=4+i*(2/3)/eta. The neutral Gaussian is G(zeta)=exp(-zeta^2+b*zeta), already in the enlarged exponential-polynomial family. The actual neutral slice is identified inside the proved positive joint integrand. Its normalized angular average has curvature 555*eta^2/32+185/24-46*L/3+55*L^2/8, proved strictly negative throughout the stated box. Lean proves there exist nonnegative radii a<b for which the larger-radius actual neutral angular integral is smaller. Thus analyticity, positive charged Gaussian widths and shrinking radius alone do not establish monotonicity of the quartic weighted neutral angular average. The comparison holds the clock scale fixed while varying radius; no counterexample to the actual clock derivative, the full integrated joint response bound, evolution or the physical model is claimed. The uniform joint response bound, strong Hamiltonian and commutator domains for the entire enlarged family, graph-core density, evolution coverage, trajectory regularity and expectation derivatives remain open. No necessary model revision, controlled physical limit, physical identification or physical TOE is established. All 50 public theorem dependency lists in six new modules use only standard axioms. All 2423 parent source/script hashes are preserved in 2431 entries, and exactly six imports extend the 8197-line root to 8203 lines. Inherited numerical evidence is unchanged; exploratory Fourier-jet probes are not used as proof or added to the evidence chain. No new .lake artifacts are generated.')
    target = root / "data/quantum_neutral_radial_obstruction_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

