#!/usr/bin/env python3
"""Audit clock-localized longitudinal spectral detection and selected-window decay."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalClockFloorLocalizedVacuumScalar', 'KFCausalClockFloorLocalizedVacuum', 'KFCausalClockFloorLocalizedSpectrum', 'KFCausalClockFloorSelectedSpectrum']
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
    logs = overlay / "quantum-localized-spectral-detection-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_selected_clock_windows_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "70e4972a4ccde70f49ef42ab855eec49f716a76a5433a9efa3828161c39c25fc"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_localized_spectral_detection_audit.py",
        "scripts/verify_quantum_localized_spectral_detection.py",
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
        scope='The analytic clock weight W=D-D^2 localizes both clock tails. For a complex chart value q in the established one-third strip, exp(Re inverse(q)) is at most twice exp(real inverse(Re q)), the shifted response norm is at most four times the real response, and the shifted W symbol has squared modulus at most 64*epsilon times minus the physical drift. On the full natural graph of the actual ordered vacuum operator T=exp(L/2)C^(-1/2), localization sends (f,g) to (Wf,(Z-Z^2)g), where Z is the existing shifted defect. Therefore the coupled longitudinal spectral mass above any real threshold R of C^(-1/2)Wf is at most 64*epsilon*exp(-R) times the existing vacuum output detector. A bounded Fourier half-space observation is lifted to L2 of the entire physical charge orbit. For every full reference form state v and positive vacuum coupling k, its squared norm is bounded by (128*epsilon*exp(-R)/k)*Delta(v), with Delta the inherited fixed total reference detector. The exact orbit integral is proved; no charge invariance of the coupled longitudinal generator or replacement by a mean output is assumed. Integrating and applying the parent selected-window theorem gives one sequence U_n,L_n, independent of R, with U_n,L_n tending to infinity, L_n^2/U_n tending to infinity, L_n/U_n tending to zero, physical actual-versus-full-frozen uniform error tending to zero, frozen clock defect norm tending uniformly to the actual residual, total Delta tending to zero, and total upper spectral observation tending to zero for EVERY FIXED real R. All full static factors remain, and initial states are arbitrary full finite-energy states. New spectral conclusions require k>0; epsilon>0,h!=0,abs(h)<=2*pi*epsilon/3 remain, with arbitrary real m,g. The observation measures inverse-half-clock times D(1-D), followed by coupled Fourier spectral restriction, angle by angle. It is not unweighted state mass, canonical momentum, pure-clock momentum, or a theorem uniform in R. No pointwise-in-time spectral limit, nonvanishing localized mass, negative-momentum propagation exclusion, actual-flow integrated spectral limit, clock recovery, model revision, physical limit, SM/GR identification, octonion necessity or physical TOE is proved. The selected windows have shrinking physical durations. All 1991 parent source/script hashes and numerical evidence are preserved; no numerical evidence or .lake artifacts are added.')
    target = root / "data/quantum_localized_spectral_detection_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

