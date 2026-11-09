#!/usr/bin/env python3
"""Audit the full-clock transport identity and its actual ordered-potential response identification."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalReciprocalNeutralCrossDifferentiation', 'KFCausalFiniteMatrixClockTransport', 'KFCausalReciprocalNeutralCrossBounds', 'KFCausalFiniteMatrixWholeClock', 'KFCausalReciprocalNeutralWholeClock', 'KFCausalReciprocalNeutralPotentialTransport']
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
    logs = overlay / "quantum-joint-whole-clock-transport-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_joint_clock_differentiation_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "00fda634a15153da3300a9a65f695c1a9c196f8afe94420fa448800299b8b4ca"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_joint_whole_clock_transport_audit.py",
        "scripts/verify_quantum_joint_whole_clock_transport.py",
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
        scope='The complete complex reciprocal neutral cross kernel is C1 by polarization, and its derivative is also identified with the integrated product rule for actual transverse factors. Derived L2 envelopes provide packet-dependent absolute bounds on K and K_prime/clock at every clock position; the inverse-clock cancellation is proved, not assumed. These bounds and the actual positive-width clock amplitudes discharge all full-line integrability conditions for finite sums with independent clock widths/frequencies, complex sources/amplitudes, arbitrary neutral polynomials, unequal or coincident reciprocal widths and exact cancellation. The boundary positiveSlice/clock and its derivative are integrable, so the boundary term vanishes in the full-clock integral without an assumed endpoint limit or relative response bound. The actual ordered-potential response equals the integral of coefficient*positiveSlice minus transportResponse/clock. transportResponse is exactly the derivative of the full Gram pairing with the instantaneous clock coefficients frozen. Hermitian symmetry identifies the weak response with (-2/h) times the imaginary part of the actual ordered momentum pairing, retaining every cross term. The physical assumptions are epsilon>0, all clock widths positive, h!=0, all reciprocal widths>=1 and absolute h<=2*pi*epsilon/3. The preserved strong Hamiltonian composition domains use the stronger sufficient strip absolute h<=pi*epsilon/3. All 47 public theorem dependency lists in six new modules use only standard axioms. All 2509 parent source/script hashes are preserved in 2517 entries, and exactly six imports extend the 8263-line root to 8269 lines. All parent numerical evidence is unchanged. This closes the full-clock integration and actual ordered-potential response identification gaps. It does not prove a family-independent upper bound on the coupled transport term relative to positiveSlice, a uniform full-Hamiltonian response estimate, graph-core density, evolution coverage or trajectory expectation regularity. The absolute bounds depend on the fixed packets and must not be substituted for the missing relative bound. The isolated radial obstruction remains valid. Controlled physical limits, physical identification, necessary model revision and a physical TOE remain unproved. No new .lake artifacts are generated.')
    target = root / "data/quantum_joint_whole_clock_transport_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

