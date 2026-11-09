#!/usr/bin/env python3
"""Audit the actual evolution out of the restricted neutral closure."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalClockFloorTransitionDerivative', 'KFCausalChargedPairTransitionInitial', 'KFCausalChargedPairEvolutionEscape']
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
    logs = overlay / "quantum-charged-pair-evolution-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_charged_pair_hamiltonian_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "3fbdabc6b69340ebe6b3a0668e4ca82647d65240bb125a04d3f05277c1479490"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_charged_pair_evolution_audit.py",
        "scripts/verify_quantum_charged_pair_evolution.py",
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
        scope='Lean proves that the actual nonautonomous completed-form evolution of the centered physical Gaussian leaves the restricted neutral packet closure at every sufficiently nearby noninitial time, for every initial time s, unit potential couplings, positive epsilon and a, nonzero h and abs(h)<=2*pi*epsilon/3. The predecessor proves the complete Hamiltonian form pairing with the explicit paired quadratic state has strictly negative real part at every time. The new general transition-amplitude theorem derives scalar differentiability for all completed-form initial and test states from the existing weak Schrodinger integral equation, strong continuity of the constructed form flow and differentiability of the bounded reference form operator. No operator-domain trajectory regularity is assumed. The centered state is explicitly identified with a one-term neutral polynomial packet, hence belongs to the restricted neutral closure. Both explicit form lifts commute with the proved time-transfer maps, identifying the reference-space pairing with the full physical form pairing. The transition amplitude to the paired state initially vanishes and its derivative is the inverse of -I*h times the strictly nonzero Hamiltonian pairing. The nonzero derivative implies a nonzero amplitude throughout a punctured neighborhood of the initial time. Since the paired state is orthogonal to every state in the restricted neutral closure, the actual evolution is outside that closure at all those times. Thus that restricted response class is not dynamically invariant, and its response estimate alone cannot cover the evolution even of the centered packet. This requires enlarging the response proof domain within the candidate model; it does not establish failure of the enlarged response inequality or a necessary physical-model revision. Trajectory clock-momentum regularity, a uniform response bound on the enlarged class, negative-tail tightness, unconditional clock recovery, controlled physical/regulator limits, Standard Model/general-relativity identification, octonion necessity and a physical TOE remain open. Eighteen public theorem checks in three modules use only standard axioms. All 2196 predecessor hashes and inherited numerical evidence are preserved in 2201 source/script entries. Exactly three imports extend the 8016-line parent root; no new .lake artifacts are generated.')
    target = root / "data/quantum_charged_pair_evolution_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

