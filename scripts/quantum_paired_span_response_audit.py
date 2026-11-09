#!/usr/bin/env python3
"""Audit the centered/paired complex superposition full Hamiltonian response bound."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalPairedSpanMoments', 'KFCausalPairedSpanKernel', 'KFCausalPairedSpanGrowth', 'KFCausalPairedSpanDomain', 'KFCausalPairedSpanOrderedOutputs', 'KFCausalPairedSpanHamiltonian', 'KFCausalPairedSpanClockMarginal', 'KFCausalPairedSpanUniformResponse']
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
    logs = overlay / "quantum-paired-span-response-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_charged_pair_uniform_response_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "b937b4bd1eeafd422253c0a4ee58bee14c393348e87e0dd3e375f0c9a1df258c"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_paired_span_response_audit.py",
        "scripts/verify_quantum_paired_span_response.py",
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
        scope='Lean proves the full completed-Hamiltonian relative lower response bound for every complex superposition c0*psi0+c1*psiP of the centered physical Gaussian packet and its paired quadratic excitation P(q)=q0*q1-q2*q3. For each fixed h!=0 there exists C(h)>=0 such that for every epsilon>0, common Gaussian clock width a>0, abs(h)<=2*pi*epsilon/3, c=(c0,c1) in C^2 and Hamiltonian time t, fullResponse(t,c)>=-((C(h)+2)/epsilon)*fullEnergy(t,c), with unit physical potential couplings. The constant is uniform over all relative amplitudes and constant phases, including destructive interference and the zero vector, all admissible epsilon, common clock widths and Hamiltonian times. The kernel uses the complete squared modulus of c0+c1*r^2*P(q). Its exact finite Gaussian moment expression retains the cross term linear in P, which need not vanish. Positivity for nonzero coefficients is proved from two explicit transverse evaluations and strict positive Gaussian/potential weights. Joint smoothness in scale and coefficients is derived from the finite moment formula. Compact admissible scale geometry times the coefficient unit sphere bounds the absolute logarithmic derivative; exact quadratic homogeneity extends this to every coefficient vector. Actual superposed states, momenta, all eight natural factor graphs, charge-zero membership, clock composition graphs and completed charge-averaged Hamiltonian lifts are constructed by linearity of the established operators. Exact ordered-output and momentum densities retain the full superposition, proving absolute integrability and Fubini for the energy and signed response. The previously verified full-line clock integration by parts then yields the potential bound; the clock/kinetic bound gives the full eight-factor physical estimate. No response inequality, derivative bound, positivity, operator regularity or endpoint limit is assumed in the final theorem. No numerical quadrature or truncation enters. The two components share the same clock width and zero clock phase; arbitrary independent clock profiles are not covered. This controls the centered/paired complex span, not the whole neutral-plus-charged state class, the charged polynomial hierarchy, h tending to zero, or the actual evolving trajectory. Dynamic invariance of this finite enlargement, trajectory pure-clock momentum regularity, the moving-test response identity, negative-tail tightness, unconditional clock recovery, physical/regulator limits, SM/GR identification, octonion necessity and a physical TOE remain open. No necessary model revision is established. Seventy-four public theorem dependency checks in eight modules use only standard axioms. All 2219 predecessor hashes and numerical evidence are preserved in 2229 source/script entries. Exactly eight imports extend the 8033-line parent root to 8041 lines; no new .lake artifacts are generated.')
    target = root / "data/quantum_paired_span_response_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

