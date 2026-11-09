#!/usr/bin/env python3
"""Audit the closed growing-output restriction and its physical Hamiltonian."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalClockFloorOrbitFactorGraphs', 'KFCausalClockFloorGrowingOutputClosure', 'KFCausalClockFloorGrowingHamiltonian']
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
    logs = overlay / "quantum-growing-hamiltonian-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_fast_time_dynamics_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "e22eb4fe3d451ed06bd218170bbcff88e58b50084bcffcf6f7dca5bf078e28df"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_growing_hamiltonian_audit.py",
        "scripts/verify_quantum_growing_hamiltonian.py",
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
        scope='The actual growing output B on the completed full reference energy form V has a canonical densely defined closed extension on physical Hilbert space: its graph is exactly the closure of {(Jv,Bv): v in V}. This is proved through the actual closed factor graphs along the full charge orbit. Each factor coordinate belongs to its original lifted closed factor graph; this property survives graph closure and excludes nonzero vertical limits. No assumption that projection preserves closedness, no Gaussian graph core, and no equality with a larger maximal natural growing-factor domain is used. The closed operator is minimal among closed extensions of the reference growing output. Its completed graph form has the original reference form as a proved dense subset in the norm squared ||Jv||^2+||Bv||^2. A positive self-adjoint densely defined physical Hamiltonian is constructed from this form. Its pairing agrees with the original growing form, and its domain on embedded reference vectors is characterized using only the original full form tests, with density proved. The leading term in the previously proved exact exponential-time weak equation is identified with this completed growing form. The actual full trajectory is uniformly bounded for all forward times in this completed growing form: its squared norm is at most the conserved initial physical norm squared plus the initial rescaled full energy. This uses the previously proved exact energy identity, not a new propagation assumption. The parameter assumptions are epsilon>0, h!=0, abs(h)<=2*pi*epsilon/3, and arbitrary existing real model coefficients. This constructs the physical operator associated with the candidate leading form, but does not prove convergence of the full dynamics, strong resolvent convergence, a comparison propagator, scattering, L1 time-integrability of the retained remainder, clock recovery, a necessary model revision, regulator removal, SM/GR identification, octonion necessity or a physical TOE. The previous exact full equation and form-dual L2 remainder remain intact. All previous checkpoint sources and numerical evidence are preserved; no numerical claims are added.')
    target = root / "data/quantum_growing_hamiltonian_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

