#!/usr/bin/env python3
"""Audit the actual strong Hamiltonian domain and response pairing for the full finite joint state family."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalSourcedDirectionalMoments', 'KFCausalSourcedSecondCalculus', 'KFCausalSourcedSecondMomentum', 'KFCausalCoherentSecondCurves', 'KFCausalPolynomialSecondFactors', 'KFCausalReciprocalSecondFactorTransport', 'KFCausalReciprocalNeutralSecondFactors', 'KFCausalReciprocalNeutralStrongHamiltonian', 'KFCausalReciprocalNeutralStrongResponse']
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
    logs = overlay / "quantum-neutral-strong-domains-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_neutral_matter_domains_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "a10271bf4991dd2e0972daf3963178f44af2ec151b41940448e675ee27436a22"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_neutral_strong_domains_audit.py",
        "scripts/verify_quantum_neutral_strong_domains.py",
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
        scope='The full finite joint neutral/reciprocal state family now belongs to the actual interacting averaged Hamiltonian operator domain at every fixed Hamiltonian time in the sufficient strip epsilon>0, h nonzero, abs(h)<=pi*epsilon/3. Every packet may have an independent positive clock width, charged width at least one, real clock frequency, complex neutral source, complex amplitude and arbitrary finite complex neutral polynomial. The proof constructs sourced directional moments, the exact second transverse derivative including all complex-source terms, its L2 representative and two actual maximal transverse-momentum graphs. Derived Gaussian majorants establish continuity of these outputs along bounded source curves. The remaining clock, kinetic and vacuum second graphs are integrated through the individual closed intermediate operators; the earlier constructed matter graphs complete all eight reverse factors. Source-circle coefficients and finite linearity give all polynomial degrees without a cutoff or assumed reverse-domain premise. Exact reciprocal-squeeze transport retains the square of each factor scaling, and the resulting graphs apply to the existing actual packets and natural factor outputs. Finite superpositions retain all eight reverse graphs. The existing strong-Hamiltonian criterion identifies H_t psi with the charge projection of the weighted sum of these constructed second outputs. Strong operator membership and the actual Hamiltonian action are proved, including coincident widths and exact cancellations. The existing completed-form energy equals Re inner(H_t psi,psi), and its full response equals (-2/h)*Im inner(H_t psi,B psi), with B psi the actual clock momentum. The response identity uses the proved form domain of B psi; its full strong Hamiltonian domain, B H_t psi, the actual commutator, graph-core density, evolution coverage and trajectory regularity for this enlarged family remain open. The inherited neutral radial estimate remains valid, but a uniform bound on the full coupled moving-clock response is not proved. No trajectory expectation derivative, controlled physical limit, physical identification, necessary model revision or physical TOE is established. All 37 public theorem dependency lists in nine new modules use only standard axioms. All 2464 parent source/script hashes are preserved in 2475 entries, and exactly nine imports extend the 8230-line root to 8239 lines. Inherited numerical evidence is unchanged. No new .lake artifacts are generated.')
    target = root / "data/quantum_neutral_strong_domains_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

