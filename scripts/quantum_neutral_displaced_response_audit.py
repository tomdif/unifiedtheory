#!/usr/bin/env python3
"""Audit the neutral-displaced uniform response and finite-profile growth bounds."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalNeutralProfileMarginal', 'KFCausalNeutralProfileGrowth', 'KFCausalNeutralExponentialProfiles', 'KFCausalNeutralDisplacedSources', 'KFCausalNeutralDisplacedKernel', 'KFCausalNeutralDisplacedResponseBound']
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
    logs = overlay / "quantum-neutral-displaced-response-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_centered_uniform_response_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "8c4e695195715f0191254b4c0f822d2dc2c37949282d7f4fa4ddb33b74e85ff1"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_neutral_displaced_response_audit.py",
        "scripts/verify_quantum_neutral_displaced_response.py",
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
        scope='For fixed nonzero h, positive epsilon with |h|<=2*pi*epsilon/3 and physical potential vacuum=mass2=quartic=1, an actual relative signed-response lower bound is proved uniformly over all neutral position and momentum displacements Q,K, all clock positions, and every finite complex neutral polynomial. The same constant works for every Hermite basis center and cutoff. The exact neutral parameter is zero in all other joint coordinates. Its charge orbit, explicit source b=-2*neutralWidth(h)*Q+2*pi*i*K and normalization exp(-neutralWidth(h)*Q^2) are proved, identifying the existing projected weighted kernel with the neutral profile energy including its actual derivative. The response bound is R>=-((C(groundWidth(h))+2)/epsilon)*T; it is independent of Q,K and polynomial degree but is not claimed uniform in a regulator limit. More generally, the exact plane marginal and finite-clock growth bound hold for every fixed complex neutral profile with proved energy integrability at both endpoints. Integrability is established unconditionally under the existing width and strip conditions for every finite superposition sum_i C_i*exp(b_i*z)*P_i(z), retaining all interference. One growth constant works for all sources, coefficients, degrees and numbers of summands. This is finite-clock growth of the actual transverse energy; the existing physical projected response-kernel bridge is completed for one neutral displaced base and all its polynomial multipliers. A physical response-kernel bridge for superpositions of different neutral bases is not claimed here. Charged displacements and their charge-projection interference, general potential couplings, extension to the required state/domain class along the full evolution, negative-tail tightness, unconditional clock recovery and controlled physical limits remain open. Neutral-profile membership is not proved invariant under the full dynamics. The earlier numerical charged displaced cases are not covered. No new numerical evidence, necessary model revision, SM/GR identification, octonion necessity or physical TOE is proved. Thirty-five public theorem checks in six modules use only standard axioms. All 2120 predecessor source hashes and numerical evidence are preserved in 2128 entries, with exactly six root imports appended and no new .lake artifacts.')
    target = root / "data/quantum_neutral_displaced_response_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

