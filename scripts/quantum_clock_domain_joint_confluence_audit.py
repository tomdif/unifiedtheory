#!/usr/bin/env python3
"""Audit actual clock-output domains, independent radial packets and joint confluence."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

MODULES = ['KFCausalAnalyticClockSecondTransport', 'KFCausalGaussianHolomorphicClockWeight', 'KFCausalClockWeightedOriginalHamiltonian', 'KFCausalIndependentRadialNormalization', 'KFCausalIndependentRadialHolomorphicQuotient', 'KFCausalIndependentRadialBaseline', 'KFCausalIndependentRadialShearIdentity', 'KFCausalPairedSqueezeKinetic', 'KFCausalPairedSqueezeMatter', 'KFCausalPairedSqueezeMatterSquare', 'KFCausalPairedSqueezeSecondTransport', 'KFCausalIndependentRadialPacketProfiles', 'KFCausalIndependentRadialPackets', 'KFCausalIndependentRadialDoubleSqueezeCoordinates', 'KFCausalIndependentRadialDoubleSqueeze', 'KFCausalIndependentRadialHamiltonian', 'KFCausalIndependentRadialPacketDerivatives', 'KFCausalIndependentRadialPacketMoments', 'KFCausalJointSourceConfluenceProfiles', 'KFCausalJointSourceConfluenceFactors', 'KFCausalJointSourceConfluenceEnvelope', 'KFCausalJointSourceConfluenceLimit', 'KFCausalJointSourceConfluenceFirstBound', 'KFCausalIndependentRadialMomentCharge', 'KFCausalClockWeightedIndependentHamiltonian', 'KFCausalIndependentRadialKineticProfiles']
NAMESPACES = {}
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
    logs = overlay / "quantum-clock-domain-joint-confluence-audit"
    logs.mkdir(exist_ok=True)
    previous_path = root / "data/quantum_potential_hamiltonian_source_kernel_audit.json"
    previous_hash = sha(previous_path)
    assert previous_hash == "a2f1aab92cac18ab332d3ed3f15702c8ef23b40fc36f4977d803b83e5e832aa0"
    previous = json.loads(previous_path.read_text())
    additions = ["UnifiedTheory/Audit/" + n + ".lean" for n in MODULES] + [
        "scripts/quantum_clock_domain_joint_confluence_audit.py",
        "scripts/verify_quantum_clock_domain_joint_confluence.py",
    ]
    hashes = dict(previous['source_sha256'])
    assert len(hashes) == 3039
    assert all(sha(root / p) == h for p, h in hashes.items())
    assert not set(additions) & set(hashes)
    hashes.update({p: sha(root / p) for p in additions})
    analytic_path = root / "data/quantum_fixed_v_charged_cooling_analytic.txt"
    analytic_hash = sha(analytic_path)
    assert analytic_hash == "38bb567709bcba710996d3b1d8302facb8df7cb7063723189bb642040c99225d"
    obstruction_path = root / "data/quantum_quartic_imaginary_contraction_obstruction.txt"
    obstruction_hash = sha(obstruction_path)
    assert obstruction_hash == "c2b84b9d756700d949ebc9687144f4812bf8cf151d0fa7715c9f1491ea4556df"
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
        # English in the opening module comment is not executable Lean.
        source_body = re.sub(r'\A/-.*?-/', '', text, count=1, flags=re.S)
        assert not re.search(r'\b(sorry|admit|axiom|unsafe)\b', source_body)
        command = ["lean", "-j1", "-o", str(overlay / "UnifiedTheory/Audit" / (name + ".olean")), source]
        result = subprocess.run(command, cwd=root, env=env, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        log = logs / (name + ".log")
        log.write_text(result.stdout)
        assert result.returncode == 0 and not re.search(r": error|: warning|sorryAx", result.stdout), str(log)
        parsed = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", result.stdout)
        audits = {n: sorted(s.strip() for s in xs.split(",") if s.strip()) for n, xs in parsed}
        expected = {"UnifiedTheory.Audit." + NAMESPACES.get(name, name) + "." + n for n in re.findall(r"^#print axioms (\S+)", text, re.M)}
        declared = {"UnifiedTheory.Audit." + NAMESPACES.get(name, name) + "." + n for n in re.findall(r"^theorem (\S+)", text, re.M)}
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
    assert sha(analytic_path) == analytic_hash
    assert sha(obstruction_path) == obstruction_hash
    for name in MODULES:
        assert not (root / ".lake/build/lib/lean/UnifiedTheory/Audit" / (name + ".olean")).exists()
    report = dict(
        new_lean_theorem_count=sum(len(c["audited_declarations"]) for c in checks),
        modules=checks, source_sha256=hashes, numerical_evidence=evidence,
        analytic_evidence=dict(path=str(analytic_path.relative_to(root)), sha256=analytic_hash,
                               status="Analytic derivation; not a Lean-verified theorem; moving field estimate remains open"),
        analytic_obstruction=dict(path=str(obstruction_path.relative_to(root)), sha256=obstruction_hash,
            status="Exact analytic counterexample to pure quartic imaginary contraction; not Lean verified; not a counterexample to the uniform response bound"),
        previous_report=dict(path=str(previous_path.relative_to(root)), sha256=previous_hash),
        root_check=dict(command=["lean", "-j1", "UnifiedTheory.lean"], exit_code=0,
                        empty_log=True, source_sha256=root_hash, log_sha256=sha(log),
                        appended_imports=MODULES),
        lean_toolchain=(root / "lean-toolchain").read_text().strip(),
        scope='174 Lean theorems in 26 successor modules. The original finite sourced reciprocal packet family now has actual Hamiltonian graphs after multiplication by the physical clock C and inverse clock C^-1=D^2, closing the clock input column on abs(h)<=epsilon/10. The holomorphic clock multiplier retains both longitudinal half steps and all primitive graph witnesses. A larger auxiliary state family with two independent charged radial widths at least one has exact physical and charge representatives, correct Fourier scalar normalization, and the original family as its diagonal. Paired and reciprocal unitary squeezes give all eight natural component graphs and the full original averaged Hamiltonian graph for every finite sum on abs(h)<=pi*epsilon/3, with all couplings retained. Its C and C^-1 multiples also have actual Hamiltonian graphs on abs(h)<=epsilon/10. Arbitrary radial polynomial moments are actual square-integrable zero-charge states; their pointwise width derivatives and exact symmetric kinetic profiles with four-angle averages are proved. These do not yet establish radial-moment Hamiltonian domains, strong graph differentiation, the four missing kinetic input columns, or full H-squared. Independent-width normalization and bounded holomorphic quotient estimates provide a next domain route. Separately simultaneous charged-width and neutral-source confluence has full integrated energy and actual spatial-response limits for every fixed order N and arbitrary common neutral polynomial P, with derived domination and all interference and linked derivatives retained. The N=1 limiting profile satisfies the existing state-independent response bound (48+82944/alpha)*fraction, uniformly in baseline width, sources, source increment and P. The domination constants may depend on N; no unrestricted-width response inequality or uniform-in-N bound follows. Evolved BH/HB domains, uniform graph limits, controlled physical limits and independent physical identification remain open. No physical TOE or necessary model revision is established. All 3039 parent source/script hashes and 23 numerical evidence files are preserved; 26 modules and 2 scripts give 3067 hashes and the root extends 8693 to 8719 lines. Standard axioms only.')
    target = root / "data/quantum_clock_domain_joint_confluence_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print("Root passed; " + str(report["new_lean_theorem_count"]) + " new theorem audits; "
          + str(len(hashes)) + " preserved/added source hashes.", flush=True)
    print(target, flush=True)


if __name__ == "__main__":
    main()

