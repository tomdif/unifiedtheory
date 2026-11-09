#!/usr/bin/env python3
"""Audit selected longer frozen windows, physical comparison and total dissipation."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalLossSensitiveComparison', 'KFCausalClockFloorLossSensitiveFreeze', 'KFCausalVanishingLossWindows', 'KFCausalClockFloorSelectedFreeze', 'KFCausalClockFloorSelectedDissipation']
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
    logs = overlay / "quantum-selected-clock-windows-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_frozen_dissipation_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "3fc4cd40e9c7f083aa2fcf83d8fcce172597df990ab83b65c62eb7c75785ae3a"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_selected_clock_windows_audit.py",
        "scripts/verify_quantum_selected_clock_windows.py",
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
        scope='The full actual finite-energy trajectory admits selected arbitrarily late frozen windows with L_n^2/U_n tending to infinity, L_n/U_n tending to zero, and U_n tending to infinity. The physical actual-versus-full-frozen error tends uniformly to zero for tau in [0,L_n], using the actual moving state as frozen input. All static factors remain. The new comparison bound retains the actual fast-energy loss: squared error at every 0<=tau<=L is at most L*(e(U)-e(U+L))/(2*abs(h)*eta)+eta*e(U)*L^2/(2*abs(h)*U), for every eta>0. The actual trace e has its previously proved finite limit. A finite telescoping partition of a late block selects an interval with small energy drop; no rate of convergence or uniform small loss at every starting time is assumed. For any positive target ratio C, error tolerance beta, lower starting threshold R, and natural M, the construction gives U,L>0 with U>=R,U>=a,L^2>=C*U,L/U<=1/(M+1), and uniform squared error<=beta. A diagonal choice proves the stated limits. Along these selected frozen windows the clock-defect norm tends uniformly to the actual residual, and the TOTAL integral of the fixed nonnegative ordered-output detector Delta tends to zero. Delta is the existing minus one-half classical output pairing on the full reference form at time zero, without a starting-time denominator. Exact frozen dissipation rescaling and its budget by 32 times the clock-expectation drop are inherited, while the new sequence argument proves the required drop from actual expectation convergence and physical closeness. There is no prescribed rate, no assertion for every late starting time, and no frozen-to-growing comparison for moving inputs. The theorem concerns each fixed full finite-energy initial state; no normalization, evolved momentum moment, or Hamiltonian operator-domain hypothesis is added. Parameters remain epsilon>0,h!=0,abs(h)<=2*pi*epsilon/3 with arbitrary real m,g,k. Positive vacuum coupling is not required. The windows grow faster than the square root of starting fast time, but their relative fast duration tends to zero and physical duration still shrinks. The positive clock residual is not excluded; proving restricted integrated detection or negative-frequency propagation remains open. Clock recovery, a necessary model revision, global scattering, regulator removal, controlled physical limits, SM/GR identification, octonion necessity and the physical TOE remain unproved. All parent source/script hashes and numerical evidence are preserved; no numerical evidence or .lake artifacts are added.')
    target = root / "data/quantum_selected_clock_windows_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

