#!/usr/bin/env python3
"""Audit frozen full dynamics and its finite-window physical comparison."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalPositiveResolventCommutation', 'KFCausalClockFloorFrozenEvolution', 'KFCausalClockFloorFrozenFormEvolution', 'KFCausalFormCrossDerivative', 'KFCausalClockFloorFrozenReferenceEvolution', 'KFCausalSplitFormComparison', 'KFCausalClockFloorFrozenFastEvolution', 'KFCausalClockFloorFrozenComparison', 'KFCausalClockFloorFrozenErrorBound']
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
    logs = overlay / "quantum-frozen-full-comparison-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_growing_form_evolution_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "409e1c3f4fabecd25d7083c0cf0aaffc3eb715944d64c818e25b285b72617b1d"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_frozen_full_comparison_audit.py",
        "scripts/verify_quantum_frozen_full_comparison.py",
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
        scope='The actual full Hamiltonian frozen at any physical time r has a constructed strongly continuous unitary group, obtained from its positive shifted resolvents and commuting Yosida approximations. Resolvent commutation, generator convergence, preservation of the original operator domain and the strong Schrodinger equation with arbitrary real rate eta are proved. The group lifts unitarily to the complete full energy form at r, and conjugation by the actual form transfers yields a strongly continuous evolution on the common full reference form. Its full frozen energy is conserved; the weak equation and strong mass-dual derivative hold for every finite-energy input. At positive exponential-time start U, choose r=log(U)/2 and eta=1/(2*h*U); the conserved form is q_U(v)=||Bv||^2+||Av||^2/U. All static and growing factors remain. A product rule for form-continuous curves with strong mass-dual derivatives justifies differentiating the physical cross pairing without assuming physical strong derivatives of arbitrary finite-energy trajectories. For the actual full evolution starting from Jv at physical time log(U)/2, and the full frozen evolution from that same input, the squared physical error after fast-time interval T>=0 satisfies error^2 <= q_U(v)*T^2/(2*abs(h)*U). This applies to every full-reference form state v. The actual static-energy bound follows from the previously proved rescaled energy monotonicity; the frozen bound follows from full energy conservation. For each fixed v and T>=0, the squared error tends to zero as U tends to infinity. The frozen flow depends on U. This is not a proof of convergence of frozen full propagators to the growing propagator, nor uniform convergence on moving inputs with uncontrolled full energy, global scattering, clock recovery, necessary model revision, regulator removal, controlled physical limits, SM/GR identification, octonion necessity or a physical TOE. Parameter assumptions remain epsilon>0, h!=0, abs(h)<=2*pi*epsilon/3 and arbitrary real coefficients m,g,k. Earlier source hashes and numerical evidence are preserved. No numerical evidence or .lake artifacts are added.')
    target = root / "data/quantum_frozen_full_comparison_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

