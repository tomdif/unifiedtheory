#!/usr/bin/env python3
"""Audit the common-width joint neutral response bound with independent clock packets."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalNeutralWidthUniformGrowth', 'KFCausalReciprocalNeutralCommonWidthKernel', 'KFCausalReciprocalNeutralCommonWidthResponse']
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
    logs = overlay / "quantum-common-width-neutral-response-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_joint_whole_clock_transport_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "66969ec1f3595c57cca7a83ea8381bb100f0995f54798b54391b7aba0f6307f5"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_common_width_neutral_response_audit.py",
        "scripts/verify_quantum_common_width_neutral_response.py",
        "scripts/joint_neutral_hermite_response_probe.py",
        "scripts/verify_joint_neutral_hermite_response.py",
    ]
    hashes = dict(previous["source_sha256"])
    assert all(sha(root / p) == h for p, h in hashes.items())
    assert not set(additions) & set(hashes)
    hashes.update({p: sha(root / p) for p in additions})
    evidence = dict(previous["numerical_evidence"])
    evidence.update({'joint_neutral_hermite_scan': {'path': 'data/joint_neutral_hermite_response_probe.json', 'sha256': '43a1276e2c2041947dbf8adfadf5c0a83a39a48e1037794c0fca8d1c83325b9d'}, 'joint_neutral_hermite_verification': {'path': 'data/joint_neutral_hermite_response_verification.json', 'sha256': 'd9e0ffde47fe633518cd5f68f478aefda0969fac69f6abdba3687504d0ec31bb'}})
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
        scope='At every fixed nonzero h, one nonnegative constant M bounds the actual common-charged-width neutral ordered-potential response by -((M+2)/epsilon) times its positive energy. The constant is independent of the common reciprocal width w>=1, the number of packets, all complex neutral sources/amplitudes, all finite polynomial degrees, independent positive clock widths, real clock frequencies, epsilon and clock position in the admissible strip abs(h)<=2*pi*epsilon/3. It may depend on h. The regular neutral score decreases as the charged Gaussian parameter increases; one existing compact-geometry bound thus works for all alpha>=alpha0>0. Exact cross-kernel algebra identifies the common-width Gram pairing with w^2 times the unit-width neutral pairing at parameter alpha*w, including every neutral cross term and exact cancellation. The derivative bound is on the full pairing with instantaneous clock coefficients frozen, and the existing actual full-clock transport identity transfers it to the canonical ordered-potential pairing. No assumed relative estimate, endpoint limit, Gram-eigenvalue bound, degree cutoff or mode truncation is used. The response and energy are the existing U7/U5/U6 ordered-potential outputs with weights 1,1/2,1/4; this is not the full eight-factor Hamiltonian response. Unequal charged-width interference remains open. The preserved actual Hamiltonian composition domains use the stronger sufficient strip abs(h)<=pi*epsilon/3. All 19 public theorem dependency lists in three new modules use only standard axioms. All 2517 parent source/script hashes are preserved in 2524 entries. Exactly three imports extend the 8269-line root to 8272 lines. The two Hermite diagnostic scripts and two finite-evidence records from the preceding research turn are newly pinned without changing them; they are not proof premises. All older numerical evidence is preserved. Graph-core density, evolution coverage, trajectory regularity, full-Hamiltonian response control, controlled physical limits, physical identification, necessary model revision and a physical TOE remain unproved. No new .lake artifacts are generated.')
    target = root / "data/quantum_common_width_neutral_response_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

