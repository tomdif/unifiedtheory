#!/usr/bin/env python3
"""Audit physical Hilbert confluence, closed potential graphs, and nonzero-limit relative response."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalCorrelatedClusteredL2Error', 'KFCausalReciprocalNeutralDifference', 'KFCausalSquaredErrorCompleteness', 'KFCausalCorrelatedClusteredPhysicalCauchy', 'KFCausalCorrelatedClusteredPotentialGraphLimit', 'KFCausalCorrelatedClusteredNonzeroResponseLimit']
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
    logs = overlay / "quantum-correlated-clustered-potential-graph-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_correlated_clustered_whole_clock_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "29ddfe936ee4149ae2f2fea0e68c9a2452c8d2cc845a571c55d615997f68fa28"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_correlated_clustered_potential_graph_audit.py",
        "scripts/verify_quantum_correlated_clustered_potential_graph.py",
    ]
    hashes = dict(previous['source_sha256'])
    assert len(hashes) == 2574
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
        scope='Forty-six Lean theorems establish actual physical Hilbert limits of the three ordered potential outputs for every fixed finite correlated charged-polynomial family with independent positive clock widths, real frequencies, neutral complex sources, polynomials and amplitudes. A vanishing full-clock squared-error mass bounds differences at two independent positive width spacings. Exact finite-packet subtraction and the existing positive-energy identity transfer this Gram estimate to physical Hilbert norms, retaining all cross terms and pi/4 normalization; completeness supplies the vector limits. Closed physical-field and field-square graphs identify the limiting linear and quadratic outputs as actions on the limiting vacuum output. The old limiting scalar energy equals the weighted sum of these three physical output norms. Its positivity is equivalent to the limiting vacuum output being nonzero. Under exactly this nonvanishing hypothesis the actual full-clock potential-response/energy ratio converges and has a family-dependent bound for sufficiently small positive spacings. Conditional transfer of bounds and strict violations is also proved for these full-clock quantities, without assuming a universal bound as a conclusion. The reduced Laplace Gram representation is never identified pointwise with the physical wavefunction. These results do not establish input-state convergence, the ordered-exponential graph of a limiting input, kinetic or second-action Hamiltonian graph convergence, graph-core density, a family-independent relative response estimate, evolution, controlled physical identification or a physical TOE. The nonzero-limit bound does not cover vanishing limiting outputs or variation of degree, family size, sources, clock profiles or other family parameters. All 2574 parent source hashes and 23 numerical file hashes are preserved, with eight new source entries giving 2582. Exactly six imports extend the root from 8302 to 8308 lines. Standard axioms only; no new .lake artifacts. Numerical results are not proof premises.')
    target = root / "data/quantum_correlated_clustered_potential_graph_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

