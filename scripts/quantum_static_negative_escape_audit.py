#!/usr/bin/env python3
"""Audit bounded-energy static negative spectral escape and preserved clock density."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalClockFloorStaticNegativeEscape']
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
    logs = overlay / "quantum-static-negative-escape-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_full_time_spectrum_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "6931e5e3ee971108a12a4bcfeb44100bce3ae19e74a343d1cfaf858f410c8470"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_static_negative_escape_audit.py",
        "scripts/verify_quantum_static_negative_escape.py",
        "scripts/nested_clock_response_probe.py",
        "scripts/verify_nested_clock_response.py",
    ]
    hashes = dict(previous["source_sha256"])
    assert all(sha(root / p) == h for p, h in hashes.items())
    assert not set(additions) & set(hashes)
    hashes.update({p: sha(root / p) for p in additions})
    evidence = dict(previous["numerical_evidence"])
    for name in ["nested_clock_response_probe", "nested_clock_response_validation"]:
        path = "data/" + name + ".json"
        evidence[name] = dict(path=path, sha256=sha(root / path))
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
        scope='At fixed physical time zero, every nonzero full energy-form state generates an actual admissible chart-phase family with unchanged Hilbert norm, unchanged pointwise probability density and unchanged weighted clock norm. All eight factors are retained. Its energy never exceeds the original energy for nonnegative family parameter u. The family parameter is NOT physical time. The phase is exp(-2 i u chart/h), using the existing rate=-u/(pi h). The three ordered factor outputs shrink by exp(-u); the other five factor norms are preserved. The vacuum output norm is exactly exp(-u) times its initial value. The localized upper coupled spectral mass has an explicit exp(-2u) bound from the actual vacuum graph. Hence it tends to zero above every fixed threshold, while the lower mass tends to the original positive weighted norm squared. The theorem no_uniform_lower_tail proves that a fixed positive amount of lower mass can occur below every prescribed threshold among states with that same norm, no larger energy and the same clock density. Thus energy and clock-density bounds alone cannot imply uniform tightness of these negative tails. Any charge invariance of the original state is preserved. This is NOT a failing Hamiltonian trajectory and does not prove that the dynamics enters this family. Assumptions epsilon>0, h!=0, |h|<=2pi epsilon/3, k>0 for the spectral bound, arbitrary real m,g. No new propagation premise, unconditional clock recovery, necessary model change, physical limit, SM/GR identification, octonion necessity or TOE is proved. Sixteen new Lean theorem dependency checks use only standard axioms. The separate new floating response test retains five nested spaces of 3,15,39,75,99 complex modes, two refined clock/angle grids and all eight energy factors. Independent saved-matrix verification checks generalized eigenvalues, witnesses, nesting, energy-scaled direct/reduced and refinement discrepancies. It is not certified quadrature or a uniform response estimate. All 2022 predecessor source hashes and prior numerical evidence are preserved; the root adds one import; no new .lake artifacts.')
    target = root / "data/quantum_static_negative_escape_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

