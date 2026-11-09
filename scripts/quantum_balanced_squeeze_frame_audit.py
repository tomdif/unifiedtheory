#!/usr/bin/env python3
"""Audit dense energy/generator tests and the actual balanced squeeze-frame dynamics."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalSqueezeEnergyContinuity', 'KFCausalClockFloorSqueezeTestDensity', 'KFCausalClockFloorSqueezeMovingPairing', 'KFCausalPairedSqueezeTimeDerivative', 'KFCausalClockFloorSqueezeMovingDynamics', 'KFCausalClockFloorBalancedSqueeze']
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
    logs = overlay / "quantum-balanced-squeeze-frame-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_relative_squeeze_virial_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "535884d0cbd68b893f378cb1f95e9b2a973f077efdc9b033a62cc7db95da351c"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_balanced_squeeze_frame_audit.py",
        "scripts/verify_quantum_balanced_squeeze_frame.py",
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
        scope='The physical squeeze acts jointly strongly continuously on the full completed energy-form space. Orbit averages inside that form converge in form norm, retain finite energy and belong to the actual maximal squeeze-generator domain. Thus the common energy/generator test class is dense in form norm and its physical embeddings are Hilbert-dense. Exact full angle-L2 bilinear energy covariance retains every output degree. For epsilon>0, h!=0, abs(h)<=2*pi*epsilon/3, arbitrary real mass, quartic and vacuum parameters under the existing square-root convention, any reference energy-form initial state, every real initial time and every real squeeze speed a, the actual moving state S_{-a*t} U(s,t)Jw satisfies a derived weak evolution equation on that dense common test class. The full transformed form is the weighted energy pairing with weights exp(2*d_i*a*t) on the actual time-t outputs, plus a times the squeeze-generator pairing on the test. The generator term is obtained by differentiating the moving test, not assumed or omitted. The state requires no initial or evolved squeeze-generator moment/domain, charge restriction, positive vacuum or Hamiltonian operator-domain premise. Initial finite completed-form energy and the stated test graph are explicit. The transformed physical norm and the actual clock-defect norm equal their original values at every time. At speed a=-1/2, both kinetic pairs and the linear matter term acquire the same exp(t) weight relative to the time-zero outputs. The clock and quartic terms have weight one, vacuum has exp(2*t), and the additional generator term is -A_h/2 on the test. This is an exact weak moving-frame equation for the original regulated dynamics, not merely an energy substitution and not a new Hamiltonian model. It proves neither a long-time propagation estimate nor endpoint generator-domain/moment propagation. Clock-probability escape, vanishing clock defect, regulator removal, controlled physical limits, Standard Model/GR identification, octonion necessity and the physical TOE remain unproved. Prior relative virial, all-charge weak escape and energy-clock work remain intact. No necessary Hamiltonian revision or new numerical evidence is asserted.')
    target = root / "data/quantum_balanced_squeeze_frame_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

