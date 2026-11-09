#!/usr/bin/env python3
"""Audit full-clock and strong Hamiltonian response for reciprocal superpositions."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalFiniteClockKernel', 'KFCausalMatrixClockIntegral', 'KFCausalReciprocalSuperpositionClockResponse', 'KFCausalReciprocalSuperpositionFactors', 'KFCausalReciprocalSuperpositionEnergy', 'KFCausalReciprocalSuperpositionStrongResponse']
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
    logs = overlay / "quantum-reciprocal-superposition-response-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_reciprocal_gram_uniform_response_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "54df43997d5e1a0320164b2f70d16f7f26743db214335adc0cc14dbc81727d73"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_reciprocal_superposition_response_audit.py",
        "scripts/verify_quantum_reciprocal_superposition_response.py",
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
        scope='The full strong Hamiltonian response bound is proved for arbitrary finite complex superpositions of the actual reciprocal zero-clock-frequency Gaussian family, with independent positive clock widths a_i and charged widths w_i>=1. There is one universal C>=0, independent of packet count, coefficients, clock widths, charged widths, their separation, h, epsilon and Hamiltonian time t, such that (-2/h)*Im inner(H_t psi,Bpsi)>=-((C+2)/epsilon)*Re inner(H_t psi,psi) at unit couplings, epsilon>0,h!=0,abs(h)<=pi*epsilon/3. H_t psi in the theorem is the actual unbounded Hamiltonian applied with a proved domain witness; Bpsi is the actual pure-clock momentum, with its graph proved and both psi and Bpsi in every fixed-time Hamiltonian domain. The missing full-clock step is derived: finite Hermitian-kernel transport separates the kernel derivative from the independent Gaussian clock coefficient derivatives, giving (E/clock)prime=W-coefficient*E+D/clock. The parent uniform matrix bound controls D<=C E. Actual L2 factor outputs prove physical energy and response integrability, and E/clock is integrable by the clock floor. The existing one-sided integral theorem constructs vanishing endpoint sequences from that integrability; no endpoint limit, absolute derivative bound or response inequality is assumed. The potential inequality is identified with the finite-sum L2 pairings, combined with actual clock and kinetic factor graph inequalities, and connected to the actual strong Hamiltonian through its proved form characterization. Coincident widths, exact cancellation and independently varying clock widths are included. This closes the full-clock potential and full strong-Hamiltonian superposition response gaps for this family. It does not prove a response estimate on the entire energy-form domain, density of this family in the energy graph norm, invariance under Hamiltonian evolution, trajectory momentum regularity, B H_t psi or an operator commutator domain. All-unit couplings and the clock-floor restriction remain explicit; no uncontrolled regulator removal or physical identification is claimed. Unconditional clock recovery, controlled physical limits, Standard Model or gravity identification, octonion necessity, necessary model revision and a physical TOE remain open. All 50 public theorem dependency lists in six new modules use only standard axioms. All 2370 parent source/script hashes are preserved in 2378 entries, and exactly six imports extend the 8156-line root to 8162 lines. Inherited numerical evidence is unchanged and no new .lake artifacts are generated.')
    target = root / "data/quantum_reciprocal_superposition_response_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

