#!/usr/bin/env python3
"""Audit compact-time physical graph bounds and continuous strong forward dynamics."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalCompactLiftedGraphBound', 'KFCausalClockFloorUniformLiftedOutput', 'KFCausalUniformEmbeddedOperators', 'KFCausalUniformPhysicalGraphAssembly', 'KFCausalUniformGraphDynamics', 'KFCausalClockFloorCompactGraphDynamics', 'KFCausalMassOutputContinuity', 'KFCausalContinuousGraphOutputs', 'KFCausalClockFloorContinuousStrongDynamics']
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
    logs = overlay / "quantum-continuous-strong-dynamics-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_full_domain_dynamics_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "0454a69ee315b94246e1832a00f931c4d091c8b1347e69a73330bbc7b67a2db1"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_continuous_strong_dynamics_audit.py",
        "scripts/verify_quantum_continuous_strong_dynamics.py",
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
        scope='At the existing fixed positive physical regulator, one constant now bounds the physical Hamiltonian output for every terminal time t in a finite forward interval [s,r] and every initial x in the full physical Hamiltonian domain D(H(s)): norm(H(t) U(s,t)x) <= C*(norm(x)+norm(H(s)x)). The previously proved coordinate generator-output bound is transferred through the exact mass equation and continuous coordinate coefficients to a uniform lifted-Hamiltonian output bound. Closed graph constructions and Banach-Steinhaus give uniform form-space operator bounds. The embedded physical adjoint estimate then constructs physical graph operators E_a(t)=H(t)U(s,t)R_a(s) with one operator-norm bound on the whole interval. The left initial resolvent identity gives the full-domain output estimate. Combined with the exact strong equation and the convex mean value theorem, this gives a trajectory Lipschitz bound proportional to the initial Hamiltonian graph norm. The constants are existence bounds, not explicit numerical formulas. They are uniform in terminal time and initial state on a fixed-start finite interval, not uniform over all starting times or on the physical unit ball without a graph-norm bound. A separate mass-pairing estimate proves physical output continuity: bounded form-space outputs with continuous mass images have continuous physical embeddings, by norm(J(x-y))^2 <= 2*C*norm(M(x-y)). The mass images of lifted graph outputs are Q(t)formFlow(s,t)x and are continuous. Closed graph uniqueness identifies these with E_a(t) on dense embedded inputs; the uniform physical operator bound extends strong continuity to every physical input. For every initial x in D(H(s)), the final actual theorem supplies a continuous Hamiltonian-output curve y(t), with (U(s,t)x,y(t)) in graph(H(t)) and HasDerivAt of U(s,.)x at t equal to (-i/h)y(t). The ordinary physical derivative, restricted to the closed interval, is continuous, including its endpoints. No strong form-norm output continuity, operator-norm time continuity, or convergence of approximate generator outputs is asserted. Backward physical and lifted-domain propagation, the strong equation in completed form norm, and corrected auxiliary evolution convergence remain open. The physical clock regulator remains fixed. Quantum momentum propagation, quantum clock recovery, controlled physical limits, SM/GR identification, octonion necessity and a physical TOE remain unproved. No necessary physical model revision or new numerical evidence is asserted.')
    target = root / "data/quantum_continuous_strong_dynamics_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()
