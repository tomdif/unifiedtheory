#!/usr/bin/env python3
"""Audit the uniform completed Hamiltonian response of the centered/paired/corrected-quartic span."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalQuarticSpanMoments', 'KFCausalQuarticSpanKernel', 'KFCausalQuarticSpanGrowth', 'KFCausalPairedQuarticOrderedOutputs', 'KFCausalQuarticTripleDomain', 'KFCausalQuarticTripleHamiltonian', 'KFCausalQuarticTripleOrderedOutputs', 'KFCausalQuarticTripleClockMarginal', 'KFCausalQuarticTripleUniformResponse']
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
    logs = overlay / "quantum-quartic-triple-response-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_paired_quartic_charge_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "038847b3f0c73a295a5d8b520101637da868798ae4d912726d6c8d81fd49503e"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_quartic_triple_response_audit.py",
        "scripts/verify_quantum_quartic_triple_response.py",
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
        scope='Lean proves the full completed charge-averaged Hamiltonian response bound for every complex superposition of the centered physical Gaussian packet, the paired excitation P*psi0 and the corrected quartic Q4*psi0, with a common positive Gaussian clock width. P=q0*q1-q2*q3 and Q4=P^2-S/(4*alpha)+1/(8*alpha^2), with S=q0^2+q1^2+q2^2+q3^2 and alpha=1/(2*abs(h)). For each fixed h!=0, one nonnegative C(h) gives fullResponse(t,c)>=-((C(h)+2)/epsilon)*fullEnergy(t,c) for all epsilon>0 with abs(h)<=2*pi*epsilon/3, all common positive clock widths, all complex coefficients and all Hamiltonian times, with unit potential couplings. The proof retains every interference term. An exact Hermitian double-sum Gaussian formula treats the larger four-term transverse span 1,P,P^2,S. Four explicit evaluations prove nonzero coefficient vectors yield positive kernels; compactness of the coefficient sphere and physical shift region yields a uniform logarithmic derivative bound. The corrected three-state family embeds explicitly into this larger kernel. Exact complex polarization of the 21 directional source terms identifies the actual quartic ordered outputs, and the unbounded multiplier relation gives their actual clock-momentum representatives. All actual states and momenta have zero charge and all eight energy-factor graphs and lift into the completed Hamiltonian form. Energy and response integrability are derived from actual L2 outputs. Full-clock integration by parts removes both endpoints from proved integrability and the kernel derivative estimate, not from assumed endpoint limits. The clock/kinetic response inequality completes the full Hamiltonian estimate. No desired response bound, domain membership, trajectory regularity or integrability is assumed in the final theorem. The four-term kernel estimate does not assert all four unprojected physical states have zero charge; the earlier bare-square obstruction remains valid. The new physical result uses a common clock profile with zero additional clock frequency; independent clock widths/frequencies for this three-state family and its product-form closure are not proved here. No bound uniform as charged polynomial degree grows, density of this family, or dynamical invariance is claimed. Actual trajectory momentum regularity, the unbounded moving-test response identity, negative-tail tightness, unconditional clock recovery, controlled physical/regulator limits, SM/GR identification, octonion necessity and the physical TOE remain open. No necessary model revision is established. Eighty-seven public theorem dependency checks in nine modules use only standard axioms. All 2259 predecessor source/script hashes and inherited numerical evidence are preserved in 2270 entries. Exactly nine imports extend the 8065-line parent root to 8074 lines; no new .lake artifacts are generated.')
    target = root / "data/quantum_quartic_triple_response_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

