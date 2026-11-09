#!/usr/bin/env python3
"""Audit positive phase-space probability escape along the full physical evolution."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalPartialFourierIntegrableSlices', 'KFCausalWindowedPhaseSpaceProbe', 'KFCausalWindowedPhaseSpaceEscape', 'KFCausalClockFloorPhaseSpaceEscape']
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
    logs = overlay / "quantum-phase-space-escape-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_squeeze_regularity_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "0cd203b8e5b5121595bf8397ab702ae9268210d5557aecd576eff213da67554d"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_phase_space_escape_audit.py",
        "scripts/verify_quantum_phase_space_escape.py",
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
        scope='For the existing positive physical windowed phase-space law, every fixed bounded phase-space set has mass tending to zero along the actual full regulated quantum propagator. For normalized initial states and normalized fixed L2 windows, the complement of every measurable bounded phase-space set has probability tending to one. Hypotheses are epsilon>0, h!=0, abs(h)<=2*pi*epsilon/3 and strictly positive vacuum coefficient k. Initial physical states and windows are arbitrary L2 vectors, with no finite-energy, charge-sector, clock-moment or momentum-moment restriction. All eight energy factors remain in the inherited physical evolution. The proof first identifies the actual partial Fourier unitary with its integral for measurable joint L2 functions with almost-everywhere L1 slices; joint L1 and continuity are not assumed. It then proves the existing tensor/shear/partial-Fourier windowed state equals almost everywhere the fixed-probe amplitude inner(T_q^(-1) M_k conjugate(window), state), and proves the probe norm equals the window norm and the amplitude bound is norm(state)*norm(window). These are identities for the original probability law, not a replacement detector. For any norm-bounded weakly escaping L2 family, dominated convergence gives mass decay on every measurable finite-volume raw phase-space region; the physical-coordinate result applies to every measurable region with finite-volume coordinate preimage. The nonzero-h phase-coordinate homeomorphism proves compact-region decay, and measure monotonicity proves bounded-region decay even without a measurability assumption on the bounded set. The application uses the previously proved full-time all-charge weak escape and exact unitarity. This is qualitative full-time phase-space probability escape, with no convergence rate. It does not identify which coordinate escapes: clock half-spaces leave matter and momenta unbounded and are outside the proved bounded-region result. In particular it does not establish low-clock projection norm decay, clock-error decay, or a trajectory counterexample requiring a change of model. Structured-state longitudinal positivity still needs extension to the full energy form and observable evolution. No such extension, form-core claim or evolved momentum domain is assumed here. Regulator removal, controlled physical limits, Standard Model/GR identification, octonion necessity and the physical TOE remain unproved. No new numerical evidence or necessary model revision is asserted. All earlier checkpoints remain intact.')
    target = root / "data/quantum_phase_space_escape_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

