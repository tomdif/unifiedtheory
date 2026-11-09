#!/usr/bin/env python3
"""Audit the completed Hamiltonian response and form closure with independent clock profiles."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalChargedPairFrequencyDomain', 'KFCausalPairedSpanMixedClockDomain', 'KFCausalPairedSpanMixedClockHamiltonian', 'KFCausalPairedSpanMixedClockOrderedBridge', 'KFCausalPairedSpanMixedClockFullBound', 'KFCausalPairedSpanResponseClosure']
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
    logs = overlay / "quantum-paired-span-mixed-clock-full-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_paired_span_mixed_clock_response_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "820df05125b662bfe7ffb71313633d87daab8b380424364d96912bfc7ac5b31b"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_paired_span_mixed_clock_full_audit.py",
        "scripts/verify_quantum_paired_span_mixed_clock_full.py",
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
        scope='Lean proves the full completed charge-averaged Hamiltonian response lower bound for the centered physical Gaussian packet and its paired quadratic excitation P(q)=q0*q1-q2*q3 with independent positive clock widths a,b, arbitrary real frequencies p,q and arbitrary complex coefficients c. For each fixed h!=0, one C(h)>=0 gives fullResponse(t,c)>=-((C(h)+2)/epsilon)*fullEnergy(t,c) for every epsilon>0 with abs(h)<=2*pi*epsilon/3, both widths, both frequencies, coefficients and Hamiltonian time t, with unit potential couplings. Actual directional source states identify frequency modulation with the bounded clock phase multiplier; its proved charge commutation preserves the zero-charge sector. The paired state, actual pure-clock momentum, all eight state/momentum factor graphs and clock composition graph are constructed by source polarization. Complex superposition with the independently clocked centered packet preserves these graphs and charge. Both inputs lift to the completed Hamiltonian form, with exact eight-factor energy and response decompositions. The three ordered output representatives equal the previously estimated mixed shifted densities. Their momentum representatives are (-I*h) times the sum with each component retaining its own weak clock slope; no common slope is imposed. Exact L1 inner-product identities connect the full potential contribution to the already proved independent-clock potential bound. The clock/kinetic lower estimate supplies the remaining full-Hamiltonian bound. No response inequality, domain membership, regularity, integrability or endpoint limit is assumed in the final theorem. All interference terms are retained and no numerical approximation is used. The estimate extends to the explicitly defined closure of packet/momentum pairs in the product of completed form norms. Closedness of pure-clock momentum and charge proves that every such limit remains an actual momentum pair in the zero-charge sector. This closure is of the specified packet-pair set, not an asserted linear span, the full zero-charge sector, or a dynamically invariant class. Finite sums with additional independent clock profiles, arbitrary sums with the whole neutral class, larger charged polynomial directions and control as that class grows remain open. No uniformity in h tending to zero is claimed. Actual trajectory momentum regularity, the moving-test response identity, negative-tail tightness, unconditional clock recovery, controlled physical/regulator limits, SM/GR identification, octonion necessity and the physical TOE remain open. No necessary model revision is established. Forty-six public theorem dependency checks in six modules use only standard axioms. All 2238 predecessor source/script hashes and inherited numerical evidence are preserved in 2246 entries. Exactly six imports extend the 8048-line parent root to 8054 lines; no new .lake artifacts are generated.')
    target = root / "data/quantum_paired_span_mixed_clock_full_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

