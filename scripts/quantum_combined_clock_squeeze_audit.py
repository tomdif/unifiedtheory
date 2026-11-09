#!/usr/bin/env python3
"""Audit the simultaneous chart/squeeze dynamics with constructed common tests."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalSqueezeChartCommutation', 'KFCausalClockFloorCombinedTestDensity', 'KFCausalClockFloorCombinedUnitary', 'KFCausalClockFloorCombinedOutput', 'KFCausalClockFloorCombinedReference', 'KFCausalClockFloorCombinedDynamics']
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
    logs = overlay / "quantum-combined-clock-squeeze-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_balanced_squeeze_frame_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "85be30943c4851bf4caaceb7c38040a1a0e12a6cd1472f79534c6f8119ad12da"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_combined_clock_squeeze_audit.py",
        "scripts/verify_quantum_combined_clock_squeeze.py",
    ]
    hashes = dict(previous["source_sha256"])
    assert all(sha(root / p) == h for p, h in hashes.items())
    assert not set(additions) & set(hashes)
    hashes.update({p: sha(root / p) for p in additions})
    evidence = previous["numerical_evidence"]
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
        scope='The actual paired squeeze preserves the entire closed chart-operator graph and commutes with chart modulation; chart modulation preserves the entire squeeze-generator graph. The actual completed-form actions commute. Form-space squeeze averages of finite-energy chart-domain vectors retain the chart graph and acquire squeeze-generator regularity. This constructs a Hilbert-dense common finite-energy/chart/squeeze test class; no form-norm density of this triple intersection is asserted. The simultaneous group C(a,t)=G(t)S(a*t) is strongly continuous and its strong test derivative is (i/h) C(a,t)(a*A_h-2*Q) on the common first-generator graphs, without a mixed operator-product premise. Its reference-form realization has exact full polarized energy covariance with weights exp(2*d_i*a*t+2*t*indicator(kinetic_i)), where d=(0,-1,-1,1,1,1,2,0) and kinetic indices are 3,4. For epsilon>0, h!=0, abs(h)<=2*pi*epsilon/3, arbitrary real mass, quartic and vacuum parameters under the existing square-root convention, every reference energy-form initial state, every real initial time and speed a, the actual transformed state C(a,-t)U(s,t)Jw satisfies the derived weak equation with that energy pairing plus a*A_h-2*Q acting on the test. No initial or evolved state generator moment, chart moment, Hamiltonian operator domain, charge restriction or positive vacuum is assumed. Finite initial completed-form energy and both test graphs are explicit. At a=-1/2, the eight time-zero output weights are (1,exp(t),exp(t),exp(t),exp(t),exp(-t),exp(-2*t),1). Both added terms -A_h/2 and -2*Q remain. The transformed physical norm and actual clock-defect norm equal their original values at every time. This is an exact equation for the original regulated physical evolution, not merely an energy substitution or a revised Hamiltonian. It proves neither a long-time propagation estimate nor state generator-domain propagation. Decaying scalar coefficients alone do not bound the corresponding unbounded forms along evolving states. Clock-probability escape, vanishing clock defect, regulator removal, controlled physical limits, Standard Model/GR identification, octonion necessity and the physical TOE remain unproved. Prior balanced squeeze, relative virial, all-charge weak escape and energy-clock work remain intact. No necessary model revision or new numerical evidence is asserted.')
    target = root / "data/quantum_combined_clock_squeeze_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

