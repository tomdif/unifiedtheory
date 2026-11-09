#!/usr/bin/env python3
"""Audit constructed full-generator approximate solutions and uniform forward energy stability."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalQuasiDissipativeResolvent', 'KFCausalTransportedEnergyForm', 'KFCausalTransportedQuasiGrowth', 'KFCausalRadialBallClipping', 'KFCausalBoundedLinearIntervalFlow', 'KFCausalClockFloorFullGeneratorDissipation', 'KFCausalClockFloorFullApproximationStability', 'KFCausalClockFloorFullApproximateSolutions']
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
    logs = overlay / "quantum-full-stability-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_full_resolvent_audit.json"
    previous_hash = sha(previous_path)
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_full_stability_audit.py",
        "scripts/verify_quantum_full_stability.py",
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
        scope="For the existing fixed physical regulator, actual solutions of the bounded full-generator equations w'=A_G(b;s,t)w are constructed on every finite forward interval for every initial vector in the completed form space V, once b exceeds a derived interval threshold. Existence follows from a globally bounded Lipschitz ball clipping, the Picard theorem and a Gronwall bound proving the constructed solution stays inside the identity region of the clipping. The approximation includes the connection in its resolvent, as in the predecessor checkpoint. With F the positive shifted form, S the domain transport, U its inverse, W=S.adjoint*F*S and d the positive coercivity constant, omega=norm(F)*norm((S*Gamma)*U)/d bounds Re<x,W G x> on the actual graph. Positivity and the full resolvent identities give Re<f,W A_G(b)f> <= 4*omega*E(W,f) for b>0 and 2*omega<=b. No connection-domain-preservation hypothesis is added. The time-dependent energy E(F(t),S(s,t)w(t)) has derivative at most rho(t) times itself, where theta=norm(F)*norm(Sprime*U)/d and rho=2+2*theta+8*omega. Continuity and compactness give one positive b0 and nonnegative kappa for each finite interval, independently of b>=b0 and the initial vector, with E(F(t),S(s,t)w(t)) <= exp(kappa*(t-l))*E(F(l),S(s,l)x) for every t in [l,r]. These are actual approximate-solution existence and uniform forward energy stability results. They do not prove convergence of these trajectories, a generator-output bound along them, their preservation of the unbounded generator domain, uniqueness or a two-parameter flow law for this newly constructed family, or a limiting strong fixed-domain evolution. Fixed-time graph preservation and generator convergence proved earlier remain distinct from these missing trajectory statements. The lifted domain requires both physical state and Hamiltonian output to lie in embedded form space. The existing full physical propagator and conditional identification of global strong physical solutions with it remain proved; its full domain propagation and forward strong equation remain open. The auxiliary spectral parameter is not the physical clock-floor regulator. Momentum propagation, quantum clock escape, controlled physical limits, SM/GR identification, octonion necessity and the physical TOE remain unproved. No necessary model change or new numerical evidence is asserted.")
    target = root / "data/quantum_full_stability_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()
