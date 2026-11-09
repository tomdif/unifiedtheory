#!/usr/bin/env python3
"""Audit the constructed autonomous evolution of the actual growing Hamiltonian."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalShiftedResolventFromOne', 'KFCausalCommutingSkewFlows', 'KFCausalCommutingSkewFlowLimit', 'KFCausalCommutingSkewFlowGenerator', 'KFCausalClockFloorGrowingYosida', 'KFCausalClockFloorGrowingEvolution']
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
    logs = overlay / "quantum-growing-evolution-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_growing_resolvent_limit_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "ca2b80477f612314768228bf3bd739a4f686908228e487997da1ea0fe82145d1"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_growing_evolution_audit.py",
        "scripts/verify_quantum_growing_evolution.py",
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
        scope='Constructed a strongly continuous unitary group on the actual physical Hilbert space for the previously identified growing Hamiltonian Hgrow, with no assumption of its evolution or generator. Starting from the actual shift-one inverse R=JW*JW.adjoint, the bounded operator F_a=1+(a-1)*R is proved coercive with constant min(1,a) for every a>0. S_a=R*F_a^(-1) is constructed and proved to satisfy both inverse identities for a+Hgrow on the original partial-operator domain. The actual positive shifted resolvents commute, as do their bounded self-adjoint Yosida operators H_a=a*(1-a*S_a). Their strong convergence to Hgrow on its dense domain is proved. Bounded skew-adjoint approximants A_n=(-i/(2h))*H_(n+1) generate actual unitary flows. Commutation yields a statewise flow difference bound using ||(A_n-A_m)x|| times the interval length; density and unitarity extend the Cauchy property to every physical input. Their limit is constructed as a linear isometry equivalence at each real time, with group composition, inverse and strong continuity proved, and approximant convergence uniform on every bounded time interval for each fixed physical input. Uniform convergence of derivatives identifies the strong derivative for every initial vector in the original Hgrow domain. The limiting evolution commutes with the actual shift-one resolvent; this constructs the domain lift, proves domain invariance, and proves Hgrow commutes with the evolution on that domain. The resulting strong equation is dU(t)x/dt=(-i/(2h))*Hgrow(U(t)x), with U(0)x=x. It is the autonomous growing evolution in fast time, not the original time-dependent full evolution. Parameters remain epsilon>0, h!=0, abs(h)<=2*pi*epsilon/3 and arbitrary real coefficients m,g,k. No charge or extra vacuum positivity condition is added. The generic construction hypotheses are discharged for the actual growing Hamiltonian. The abstract moving-input lemma requires the input sequence to converge; it does not supply convergence of the actual physical trajectory. No full nonautonomous-to-autonomous comparison, accumulated static-remainder bound in physical norm, scattering, clock recovery, necessary model revision, regulator removal, controlled physical limit, SM/GR identification, octonion necessity, or physical TOE is established. Previous source hashes and numerical evidence are preserved. No numerical evidence or .lake artifacts are added.')
    target = root / "data/quantum_growing_evolution_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

