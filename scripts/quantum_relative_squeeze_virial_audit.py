#!/usr/bin/env python3
"""Audit the strong small-squeeze limit and actual relative virial balance."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalHilbertLpContinuity', 'KFCausalSqueezeNormalizedCoefficients', 'KFCausalSqueezeOutputContinuity', 'KFCausalSqueezeNormalizedOutput', 'KFCausalClockFloorSqueezeNormalizedRate', 'KFCausalClockFloorSqueezeRelativeVirial', 'KFCausalClockFloorSqueezeGeneratorBalance']
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
    logs = overlay / "quantum-relative-squeeze-virial-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_squeeze_dynamics_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "eb0a603f533a3b7ca087de01adcba6452adb65b7d7b445e7a33dabe8023a86ca"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_relative_squeeze_virial_audit.py",
        "scripts/verify_quantum_relative_squeeze_virial.py",
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
        scope='For the actual paired physical squeeze, its pure coordinatewise unitary action lifts strongly and jointly continuously to the full angle-L2 energy output. The scalar divided commutator coefficients have a proved removable extension at zero, equal to twice the exact output degrees (0,-1,-1,1,1,1,2,0). The normalized full-output operator N_a is jointly strongly continuous in parameter and output, satisfies B_a=a*N_a for every real a, and converges strongly to the diagonal operator with entries 2*d_i. Its zero pairing is exactly the real signed full-energy variation, with both negative static kinetic terms, both positive growing kinetic terms and both ordered matter terms retained. Under epsilon>0, h!=0, abs(h)<=2*pi*epsilon/3, arbitrary real mass, quartic and vacuum parameters under the existing square-root convention, every initial reference energy-form state w, every initial time s and finite real interval b..c, the actual normalized physical rate is jointly continuous in squeeze parameter and time. Compact-interval integration therefore preserves its zero-parameter limit. The bounded characteristic increment chi_a(c)-chi_a(b) has a derivative in squeeze parameter at zero equal to (i/h)*integral_b^c variation(q_t) dt. This is an unconditional relative regulated virial for all covered finite-energy states, in every charge sector, without a positive-vacuum assumption or initial/evolved clock, momentum, squeeze-generator moment or Hamiltonian operator-domain premise. A separate conditional corollary identifies the integral with the difference of squeeze-generator expectations when both actual endpoint generator graphs are explicitly supplied. It does not assert propagation or existence of those endpoint domains or absolute moments. The small-squeeze and finite-time-integral-limit gaps from the preceding checkpoint are closed. A signed propagation estimate, generator moment propagation, clock-probability escape, vanishing clock defect, regulator removal, controlled physical limits, Standard Model/GR identification, octonion necessity and the physical TOE remain unproved. No necessary Hamiltonian change or new numerical evidence is asserted.')
    target = root / "data/quantum_relative_squeeze_virial_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

