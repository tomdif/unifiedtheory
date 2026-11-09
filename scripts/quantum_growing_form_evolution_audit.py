#!/usr/bin/env python3
"""Audit the actual growing evolution on its complete energy form."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalUnitaryFormLift', 'KFCausalUnitaryFormWeakEquation', 'KFCausalClockFloorGrowingFormEvolution']
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
    logs = overlay / "quantum-growing-form-evolution-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_growing_evolution_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "595bae49707f6504b7ea014cb43075a1ca6606b04f7023cc54022f8e4be3a902"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_growing_form_evolution_audit.py",
        "scripts/verify_quantum_growing_form_evolution.py",
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
        scope='The already constructed actual growing Hamiltonian evolution is lifted to its entire completed energy form W, including finite-energy vectors outside the Hamiltonian operator domain. The linear lift of the operator domain into W is proved dense in the form norm by the existing form representation theorem. Its exact norm identity is ||Lx||^2=||x||^2+Re<Hgrow x,x>. Actual physical unitarity and proved Hamiltonian commutation make the domain evolution preserve that norm; the dense isometric extension constructs a unitary form group. Intertwining with the actual physical group, group initial and composition identities, form-norm preservation and strong form continuity are proved. Consequently both the physical norm and the actual growing-output norm are conserved; the full growing-output sesquilinear pairing is also conserved when both arguments evolve. Uniform convergence of domain approximants in the form norm holds for all real times. The weak derivatives against each fixed form test also converge uniformly, so every initial vector v and test z in W satisfy d/dt inner(U(t)Jv,Jz)=(i/(2h))*inner(BW E(t)v,BW z). This equation is established for all form states, without an operator-domain hypothesis on v or z. Every evolution and domain hypothesis of the generic form-lifting construction is discharged by the previously constructed actual growing evolution. Parameter assumptions remain epsilon>0, h!=0, abs(h)<=2*pi*epsilon/3 and arbitrary real coefficients m,g,k, with no extra charge or vacuum positivity condition. This is the autonomous growing evolution in fast time. It does not construct the frozen full-Hamiltonian evolution, prove a comparison with the original nonautonomous full evolution, control its accumulated static remainder in physical norm, prove scattering or clock recovery, establish necessary model revision, remove the regulator, identify physical limits or SM/GR, derive octonion necessity, or prove a physical TOE. Earlier source hashes and numerical evidence are preserved. No numerical evidence or .lake artifacts are added.')
    target = root / "data/quantum_growing_form_evolution_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

