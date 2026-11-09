#!/usr/bin/env python3
"""Audit momentum potential domains, actual response pairings, and both clock composition graphs."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalReciprocalNeutralFieldSliceNorm', 'KFCausalCorrelatedClusteredFieldTransfer', 'KFCausalShiftedMomentumClockAmplitude', 'KFCausalCorrelatedClusteredMomentumPotentialProfiles', 'KFCausalCorrelatedClusteredMomentumPotentialLimit', 'KFCausalCorrelatedClusteredPhysicalResponsePairing', 'KFCausalHalfMomentumClockAmplitude', 'KFCausalCorrelatedClusteredHalfMomentumLimit', 'KFCausalCorrelatedClusteredClockCompositionLimit']
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
    logs = overlay / "quantum-correlated-clustered-momentum-response-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_correlated_clustered_clock_domains_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "693868216831f131ec4d8726a48ed378b17e22dfa9217bb92b6a0034fa879ab0"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_correlated_clustered_momentum_response_audit.py",
        "scripts/verify_quantum_correlated_clustered_momentum_response.py",
    ]
    hashes = dict(previous['source_sha256'])
    assert len(hashes) == 2599
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
        scope='Sixty-three Lean theorems close further natural operator domains and identify actual response pairings for arbitrary fixed finite correlated clustered families with independent positive clock widths and real frequencies, charged degrees, neutral complex sources, neutral polynomials and amplitudes. Field-weighted physical slice norms of powers zero, one and two are controlled by the same exact positive Gram integral. This yields a Cauchy transfer for actual finite Hilbert representatives with arbitrary continuous L2 clock coefficients. The shifted pure-momentum clock coefficient is proved L2 by bounded inverse clocks and a derived Gaussian chart-moment estimate. Existing finite momentum potential outputs are identified exactly with these representatives; all three converge. Closed ordered-exponential, physical-field and field-square graphs identify the natural potential actions on the limiting pure momentum and the compositions of those factors after pure momentum at the limiting input. Consequently the previous scalar full-clock potential-response limit equals the actual potential form pairing of the limiting input and its pure momentum. Zero limiting input implies zero response, without a quotient argument. The previously proved one-sided vacuum-subclass uniform lower response bound is now an inequality for this actual potential form pairing; it remains restricted to source zero, neutral polynomial one, zero frequency and abs(h)<=pi*epsilon/3. Half-clock weighted momentum coefficients are also proved L2, so the half-clock action on momentum converges. Physical differentiation constructs the reverse finite clock-momentum composition; closedness and the bounded density correction pass it to the limit. Both orders of half-clock and pure momentum therefore act on the same limiting input. The actual clock response converges, equals the established operator response, and lies between -(1/(4*epsilon))*norm(halfClock(input))^2 and zero, with the additional bound by minus norm(input)^2. These clock-piece bounds apply to all admitted profiles, but do not control the general potential response. All general-domain statements require epsilon>0, h!=0, positive clock widths and abs(h)<=2*pi*epsilon/3. They establish natural mixed compositions, not Hamiltonian second actions or a strong Hamiltonian pairing formula. Four transverse kinetic output limits and their momentum counterparts, strong Hamiltonian second actions, graph-core density, a uniform general-family potential response bound, full Hamiltonian response and dynamics, controlled physical limits and identification, and the physical TOE remain unproved. All 2599 parent source hashes and 23 numerical file hashes are preserved; eleven new source entries give 2610. Exactly nine imports extend the root from 8321 to 8330 lines. Standard axioms only; no new .lake artifacts. Numerical results are not proof premises.')
    target = root / "data/quantum_correlated_clustered_momentum_response_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

