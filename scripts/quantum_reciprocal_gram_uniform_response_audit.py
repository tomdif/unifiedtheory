#!/usr/bin/env python3
"""Audit the positive physical wedge representation and uniform matrix response."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalReciprocalWedgeMeasure', 'KFCausalReciprocalWedgePlane', 'KFCausalReciprocalWedgeCartesian', 'KFCausalReciprocalWedgePolar', 'KFCausalReciprocalWedgeRepresentation', 'KFCausalReciprocalGramUniformResponse']
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
    logs = overlay / "quantum-reciprocal-gram-uniform-response-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_reciprocal_wedge_comparison_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "dd01274075aa4d089b250322015f7d3f9c7b7d9972f373589380511671c04178"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_reciprocal_gram_uniform_response_audit.py",
        "scripts/verify_quantum_reciprocal_gram_uniform_response.py",
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
        scope='The exact positive wedge representation of the actual physical reciprocal cross-kernel Gram form is proved, including all finite complex interference terms, coincident widths, the quartic potential, absolute integrability in Cartesian coordinates, Tonelli changes of order, polar radius-squared substitution, Complex Lebesgue measure normalization and the real-linear wedge Jacobian. The prefactor is pi/8 times sqrt(pi/(2*beta)); the weight coefficients are c0=1+1/(8*beta)+3/(64*beta^2), c1=1/2+3/(8*beta), c2=1/4. There is one universal nonnegative C such that the physical Gram form G(t)<=exp(C*(t-s))*G(s) for s<=t, and its actual clock derivative satisfies Gprime(s)<=C*G(s), for every finite complex coefficient vector and widths w_i>=1, alpha,beta,epsilon>0, 32*beta<=alpha, 0<abs(y)<=pi*epsilon/6. The same constant is independent of packet count, coefficients, width separation, alpha,beta,epsilon,y and clock position. This follows from the proved positive representation and nested wedge comparison, with no Gram eigenvalue lower bound or response premise. The derivative is the real part of the full finite sum of actual off-diagonal kernel derivatives. The smaller strip y=-h/2 corresponds to abs(h)<=pi*epsilon/3. This closes the positive-integral representation and uniform matrix response gaps. The full-clock potential response for arbitrary superpositions with independently varying clock widths, and the corresponding full Hamiltonian response, still require transport and integral arguments; they are not asserted here. Parent strong domains psi in Dom(H_t), Bpsi in Dom(H_t), finite-sum domains and the individual-packet strong response are preserved. B H_t psi, the operator commutator domain, graph-core density, evolution invariance and trajectory momentum regularity remain open. No unconditional clock recovery, controlled physical limits, Standard Model or gravity identification, octonion necessity, necessary model change or physical TOE is proved. All 45 public theorem dependency lists in six new modules use only standard axioms. All 2362 parent source/script hashes are preserved in 2370 entries; exactly six imports extend the 8150-line root to 8156 lines. Inherited numerical evidence is unchanged and no new .lake artifacts are generated.')
    target = root / "data/quantum_reciprocal_gram_uniform_response_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

