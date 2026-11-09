#!/usr/bin/env python3
"""Audit charge-averaged squeeze covariance, its generator and actual bounded-squeeze dynamics."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalChargeSqueezePairedFlow', 'KFCausalChargeSqueezePartialFourier', 'KFCausalChargeSqueezeJointFlow', 'KFCausalClockFloorAveragedSqueeze', 'KFCausalClockFloorAveragedSqueezeEnergy', 'KFCausalPairedSqueezeContinuity', 'KFCausalPairedSqueezeGenerator', 'KFCausalClockFloorReferenceSqueeze', 'KFCausalClockFloorSqueezePairing', 'KFCausalClockFloorSqueezeEhrenfest', 'KFCausalClockFloorSqueezeBalance']
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
    logs = overlay / "quantum-squeeze-dynamics-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_paired_squeeze_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "408893c3b1a1461238e92c0ef4a5f3b21e86d03d20e3cd589377a7af7240467a"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_squeeze_dynamics_audit.py",
        "scripts/verify_quantum_squeeze_dynamics.py",
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
        scope='The actual paired squeeze commutes with every physical charge-circle action on all Hilbert states. Its physical partial Fourier representative is derived through Schwartz functions, the exact two-dimensional Fourier Jacobian and density: in mixed charge coordinates it is uniform dilation of the five transverse coordinates, with fixed clock and half-density exp(-5a/2). All-L2 charge commutation gives the actual bounded action on the full completed charge-averaged energy form, exact transformed output and two-sided domain invariance. All eight outputs retain degrees (0,-1,-1,1,1,1,2,0); their exact angle-L2 norm-square and squeeze-parameter derivative are proved for every averaged form state. Separately compact test pairings, fixed-support integration, unitarity and physical density prove strong continuity of the physical squeeze. Its actual maximal strong-derivative momentum is densely defined, self-adjoint for nonzero Planck parameter, closed, has the proved time-average graph core and commutes with charge on its whole graph. The form action on the reference graph used by the physical evolution commutes with reference-time transfer. For epsilon>0, h!=0, abs(h)<=2*pi*epsilon/3, arbitrary real m,g,k under the existing square-root convention, every reference energy-form initial w, every real initial time s and every real squeeze parameter a, the actual squeeze expectation chi(a,s,t)=inner(U(s,t)Jw,S_a U(s,t)Jw) has a continuous physical-time derivative at every real t and an exact integral balance on every finite real interval. Its rate is (i/h)*inner(q_t,B_a q_t), where q_t is the actual full angle-dependent energy output and B_a applies (exp(d_i*a)-exp(-d_i*a))*S_a to coordinate i. Both kinetic signs and both matter terms are retained; degree-zero clock and vacuum terms cancel by their proved invariance. No initial charge restriction, positive-vacuum assumption, chart or momentum moment, squeeze-generator domain or Hamiltonian operator domain is required for this finite-energy bounded-observable balance. This is a finite-squeeze physical-time identity, not yet an unbounded-generator expectation law or a signed propagation estimate. The small-squeeze limit, control or propagation of generator moments, clock-probability escape and vanishing clock error remain open. Prior weak escape, energy-clock work and classical fast-energy diagnostics remain intact. Regulator removal, controlled physical limits, Standard Model/GR identification, octonion necessity and the physical TOE remain unproved. No necessary Hamiltonian change or new numerical evidence is asserted.')
    target = root / "data/quantum_squeeze_dynamics_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

