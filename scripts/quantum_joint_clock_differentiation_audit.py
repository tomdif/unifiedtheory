#!/usr/bin/env python3
"""Audit differentiation through the full reciprocal neutral transverse energy and its actual kernel identification."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalReciprocalNeutralClockEnvelope', 'KFCausalTransverseClockDifferentiation', 'KFCausalReciprocalNeutralClockDerivative', 'KFCausalReciprocalNeutralKernelDerivative']
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
    logs = overlay / "quantum-joint-clock-differentiation-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_joint_radial_transport_obstruction_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "5b1eb7794f5e19b5f15200c2117da7c63ccd7469dabe0ca81e4e30f25825f2ac"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_joint_clock_differentiation_audit.py",
        "scripts/verify_quantum_joint_clock_differentiation.py",
    ]
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
        scope='Actual reciprocal neutral transverse factors and their clock derivatives have derived common L2 envelopes after reciprocal squeezing. The envelope constants may depend on the packet, width, source and polynomial degree; they are domination bounds, not a uniform response estimate. A local L2 differentiation calculus retains entire finite sums before squaring and allows C1 clock coefficients. The complete ordered-potential transverse energy is C1 and its derivative is the integral of twice the real conjugate-amplitude times amplitude-derivative, summed with weights 1, 1/2 and 1/4. Every interference term is retained, including coincident widths and exact cancellation. The energy is identified exactly with the existing reciprocal neutral Gram pairing, and the actual positiveSlice and clockPairing have the proved derivative with the actual independent clock amplitudes. Constant coefficients are covered separately by fixed_pairing_derivative. The slice hypotheses are epsilon>0, absolute y<=pi*epsilon/3, alpha>0, beta>0, 32*beta<=alpha and all widths>=1. Actual physical slices use h!=0 and absolute h<=2*pi*epsilon/3; positive clock widths are needed for the preserved global physical states but not the local slice regularity. All 32 public theorem dependency lists in four new modules use only standard axioms. All 2503 parent source/script hashes are preserved in 2509 entries, and exactly four imports extend the 8259-line root to 8263 lines. Parent numerical evidence is unchanged and no new numerical claims are made. The parent already proves both actual Hamiltonian/clock composition domains in the stronger sufficient strip. This successor closes differentiation under the complete transverse integral, not a uniform upper bound on the combined derivative, a full clock integration-by-parts response bound, graph-core density, evolution coverage or trajectory regularity. The isolated radial obstruction remains valid, so future estimates must retain coupled terms. Controlled physical limits, physical identification, necessary model revision and a physical TOE remain unproved. No new .lake artifacts are generated.')
    target = root / "data/quantum_joint_clock_differentiation_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

