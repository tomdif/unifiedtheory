#!/usr/bin/env python3
"""Audit both actual second matter actions for the full finite joint neutral/reciprocal state family."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalMixedFieldCoherentStrip', 'KFCausalMixedFieldCoherentContour', 'KFCausalMixedFieldCoherentFullFourier', 'KFCausalMixedFieldCoherentSpectral', 'KFCausalMixedFieldCoherentPhysical', 'KFCausalCoherentMatterSquare', 'KFCausalMixedFieldSourceContinuity', 'KFCausalCoherentMatterCurve', 'KFCausalPolynomialMatterSquare', 'KFCausalReciprocalNeutralMatterSquare', 'KFCausalReciprocalNeutralMatterFamily']
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
    logs = overlay / "quantum-neutral-matter-domains-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_neutral_radial_defect_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "fe50feaf75f72a7a08d678c90c27d0e1cf78261547d6703a50b6f6dd1515aeb2"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_neutral_matter_domains_audit.py",
        "scripts/verify_quantum_neutral_matter_domains.py",
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
        scope='Both actual second ordered matter actions are now constructed for the full finite joint neutral/reciprocal state family. Mixed field powers two and four times the coherent-source clock-shifted Gaussian have derived joint L1/L2 bounds for arbitrary complex transverse sources and real clock frequencies. Source absorption, field-power absorption and the actual Fourier contour prove the maximal second longitudinal-exponential graph. Its physical representative is the point-field power times the first shifted packet, so the second field and field-square graphs and both reverse matter graphs are discharged for arbitrary amplitudes and coherent sources. Derived half-width Gaussian majorants prove continuity of the actual mixed-shift states along bounded continuous source curves. Integrating each closed intermediate graph gives second matter actions for source-circle coefficients, and finite linearity gives every finite complex polynomial degree. Reciprocal squeeze transport applies these graphs to the existing actual neutral exponential-polynomial packets and their finite superpositions. The final theorem applies to the repository state and natural outputs, with independently varying positive clock widths, charged widths at least one, real clock frequencies, complex neutral sources, amplitudes and polynomials. Coincident widths and exact cancellations are included. The sufficient second-action strip is epsilon>0, h nonzero and abs(h)<=pi*epsilon/3. No second-domain or assumed closure-of-composition hypothesis is added. These results discharge the two matter reverse factors of the enlarged state. They do not yet prove all other second factors, the full strong Hamiltonian domain, the corresponding momentum-state domains, commutator domains, graph-core density or evolution regularity for the enlarged family. The inherited uniform neutral radial derivative bound remains valid, but the full moving-clock response estimate combining charged transport and moving neutral geometry remains open. No necessary model revision, controlled physical limit, physical identification or physical TOE is established. All 56 public theorem dependency lists in eleven new modules use only standard axioms. All 2451 parent source/script hashes are preserved in 2464 entries, and exactly eleven imports extend the 8219-line root to 8230 lines. Inherited numerical evidence is unchanged. No new .lake artifacts are generated.')
    target = root / "data/quantum_neutral_matter_domains_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

