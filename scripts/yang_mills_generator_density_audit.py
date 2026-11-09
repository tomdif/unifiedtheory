#!/usr/bin/env python3
"""Incremental OS generator, test-density and quantitative-concentration audit, retaining 2187 validated checks.

Every prior proof source and audit script must have its previously certified
hash. Only the integration root, two READMEs and requirements ledger may change. The new declarations
are checked afresh after a real dependency build; no dependency overlay is used.
"""
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

from free_balanced_hamiltonian_audit import ROOT, STANDARD_AXIOMS, local_dependencies, sha256
from yang_mills_direct_requirements_audit import TARGETS as PREVIOUS_TARGETS

NEW_TARGETS = [
    'UnifiedTheory.Clay.YangMills.ExplicitRescaledTrajectories',
    'UnifiedTheory.Clay.YangMills.FinitePartitionMass',
    'UnifiedTheory.Clay.YangMills.FullOSHamiltonianCandidate',
    'UnifiedTheory.Clay.YangMills.FullPositiveTimeDynamics',
    'UnifiedTheory.Clay.YangMills.FullPositiveTimeHamiltonian',
    'UnifiedTheory.Clay.YangMills.FullPositiveTimeHilbert',
    'UnifiedTheory.Clay.YangMills.FullPositiveTimeReflection',
    'UnifiedTheory.Clay.YangMills.OSGeneratorDomain',
    'UnifiedTheory.Clay.YangMills.OSHamiltonianCandidate',
    'UnifiedTheory.Clay.YangMills.OSHamiltonianVacuum',
    'UnifiedTheory.Clay.YangMills.OSLaplaceGenerator',
    'UnifiedTheory.Clay.YangMills.OSLaplaceHamiltonian',
    'UnifiedTheory.Clay.YangMills.OSLaplaceResolvent',
    'UnifiedTheory.Clay.YangMills.OSVacuumSector',
    'UnifiedTheory.Clay.YangMills.OSWeakCouplingHamiltonian',
    'UnifiedTheory.Clay.YangMills.PositiveTimeCutoff',
    'UnifiedTheory.Clay.YangMills.QuantitativeWilsonConcentration',
    'UnifiedTheory.Clay.YangMills.ReflectedDefectBound',
    'UnifiedTheory.Clay.YangMills.ReflectedGridRate',
    'UnifiedTheory.Clay.YangMills.UnitaryCoordinateGrid',
    'UnifiedTheory.Clay.YangMills.UnitaryEntryEstimates',
    'UnifiedTheory.Clay.YangMills.UnitaryHaarNeighborhood',
    'UnifiedTheory.Clay.YangMills.WilsonGridCouplingRate',
]
TARGETS = PREVIOUS_TARGETS + NEW_TARGETS
CHECK = "scripts/CheckYangMillsGeneratorDensity.lean"
PREVIOUS_REPORT = "data/yang_mills_direct_requirements_audit.json"
NEW_COUNT = 208
PREVIOUS_COUNT = 2187
REMAINING = [
    'Construct and justify the physical compact simple Lie-group setting, renormalized curvature field multiplets, physical coupling/scale prescription and operator mixing. The exact unitary holonomy defect and the proposed a^-4 normalization are not identified with continuum curvature.',
    'Actual matrix gridding proves a dimension-dependent polynomial Haar-mass bound and quantitative Wilson concentration. Actual centered fixed-Schwartz reflected two-point forms satisfy a sufficient a^-8 K^-2 upper bound. Explicit refining/expanding trajectories give uniformly bounded proposed rescaled forms, or force them to zero with a faster coefficient choice. These sufficient trajectories are not the physical running coupling; no nonzero rescaled limit, full renormalized hierarchy, ultraviolet stress tensor or operator-product behavior is proved.',
    'Unrestricted positive-time reflection positivity, Hilbert cutoff density, a proved unitary identification with the bounded-slab space, and exact forward shifts of all positive-time Schwartz labels are now constructed for the fixed-plane bare scalar hierarchy. Full Euclidean rotations, renormalized field-multiplet covariance, local quantum fields on a common invariant domain and the complete quantum-field axiom system remain open.',
    'The bare scalar Laplace resolvent and a densely defined nonnegative self-adjoint Hamiltonian are constructed, with exact range domain and maximal right-derivative generator graph, including on the unrestricted positive-time Hilbert space and one actual Wilson candidate. The functional-calculus identity T(t)=exp(-tH), physical renormalized Yang--Mills identification, spatial momentum generators, a physical Poincare representation and joint forward-cone spectrum remain unproved. No claim that the constructed partial operator must be unbounded is made.',
    'A normalized invariant vacuum, its zero-energy domain vector, and a bounded resolvent witness at -1 are proved for the normalized bare candidate. Vacuum uniqueness in a nontrivial theory, nonzero renormalized observable states and a finite positive physical excitation scale/mass gap remain open. Along the actual unscaled beta-to-infinity unitary real-character trajectory, H has full domain and zero action, and the existing finite-excitation/spectral-requirements predicates fail. This does not rule out a centered/rescaled Yang--Mills limit. All twelve full-target requirements remain open.',
    'The auxiliary Bose spectral bundle and separate S3 matter-coupled/physical-identification program remain distinct; their spectral gaps cannot certify this Yang--Mills construction.',
]


def main():
    previous = json.loads((ROOT / PREVIOUS_REPORT).read_text())
    prior_names = []
    for ledger in ["scripts/CheckParticleHamiltonians.lean", "scripts/CheckParticleEnergyGap.lean",
                   "scripts/CheckBosonicParticleSectors.lean", "scripts/CheckBosonicEnergyClayFramework.lean", "scripts/CheckYangMillsSwarm.lean",
                   "scripts/CheckYangMillsConstruction.lean",
                   "scripts/CheckYangMillsLatticeBridge.lean",
                   "scripts/CheckYangMillsReflectedHierarchy.lean",
                   "scripts/CheckYangMillsSchwingerBridge.lean",
                   "scripts/CheckYangMillsDirectRequirements.lean"]:
        prior_names += re.findall(r"^#print axioms (\S+)$", (ROOT / ledger).read_text(), re.M)
    if len(prior_names) != PREVIOUS_COUNT or list(previous["audited_declarations"]) != prior_names:
        raise RuntimeError("Previous declaration ledger does not match its certificate")
    permitted_integration_changes = {"UnifiedTheory.lean", "UnifiedTheory/QSeries/README.md",
                                     "UnifiedTheory/Clay/YangMills/README.md",
                                     "data/yang_mills_requirements.json"}
    retained = {p: h for p, h in previous["source_sha256"].items()
                if p not in permitted_integration_changes}
    changed = [p for p, h in retained.items() if sha256(ROOT / p) != h]
    if changed:
        raise RuntimeError(f"Prior proof sources changed; a full re-audit is required: {changed}")
    certificate = previous
    while True:
        for check in certificate["checks"]:
            if check["exit_code"] != 0 or sha256(Path(check["log"])) != check["log_sha256"]:
                raise RuntimeError("Previous successful verification log is missing or changed")
        predecessor = certificate.get("predecessor_report")
        if not predecessor:
            break
        if sha256(ROOT / predecessor) != certificate["predecessor_report_sha256"]:
            raise RuntimeError("Previous certificate chain has changed")
        certificate = json.loads((ROOT / predecessor).read_text())
    if any(not set(a) <= STANDARD_AXIOMS for a in previous["audited_declarations"].values()):
        raise RuntimeError("Unexpected prior axioms")
    actual_new_sources = sorted(
        str(p.relative_to(ROOT))
        for p in (ROOT / "UnifiedTheory/Clay/YangMills").glob("*.lean")
        if str(p.relative_to(ROOT)) not in previous["source_sha256"]
    )
    expected_new_sources = sorted(module.replace(".", "/") + ".lean" for module in NEW_TARGETS)
    if actual_new_sources != expected_new_sources:
        raise RuntimeError("Post-2187 Yang--Mills source inventory does not match NEW_TARGETS")
    expected = re.findall(r"^#print axioms (\S+)$", (ROOT / CHECK).read_text(), re.M)
    discovered = []
    for module in NEW_TARGETS:
        source = (ROOT / (module.replace(".", "/") + ".lean")).read_text()
        namespaces = re.findall(r"^namespace (\S+)", source, re.M)
        if len(namespaces) != 1:
            raise RuntimeError("Expected one explicit namespace per new module")
        discovered += [namespaces[0] + "." + n for n in re.findall(
            r"^(?:@\[[^\]]*\]\s*)?(?:def|abbrev|theorem|lemma|instance|structure)\s+(\w+)", source, re.M)]
    if expected != discovered or len(expected) != NEW_COUNT or len(set(expected)) != NEW_COUNT:
        raise RuntimeError("Every new public definition and theorem must be checked")
    local_sources = sorted({p for target in TARGETS for p in local_dependencies(target)})
    sources = sorted(set(local_sources + list(previous["source_sha256"]) + [
        CHECK, "scripts/yang_mills_generator_density_audit.py", PREVIOUS_REPORT,
        "data/yang_mills_requirements.json", "scripts/check_yang_mills_requirements.py",
        "UnifiedTheory/Clay/YangMills/README.md",
        "UnifiedTheory.lean", "UnifiedTheory/QSeries/README.md",
    ]))
    hashes = {p: sha256(ROOT / p) for p in sources}
    env = os.environ.copy()
    env.pop("LEAN_PATH", None)
    env["LEAN_NUM_THREADS"] = "2"
    logs = Path(tempfile.mkdtemp(prefix="unifiedtheory-yang-mills-generator-density-audit-"))
    checks = []
    for i, command in enumerate([
        ["lake", "--rehash", "build", *TARGETS],
        ["lake", "env", "lean", CHECK],
        ["python3", "scripts/check_yang_mills_requirements.py"],
    ]):
        log = logs / f"{i}.log"
        print("Running:", " ".join(command), "Log:", log, flush=True)
        with log.open("w") as output:
            result = subprocess.run(command, cwd=ROOT, env=env, stdout=output,
                                    stderr=subprocess.STDOUT)
        if result.returncode:
            raise RuntimeError(f"Command failed; inspect {log}")
        checks.append({"command": command, "exit_code": 0, "log": str(log),
                       "log_sha256": sha256(log)})
        print("Passed:", " ".join(command), flush=True)
    output = Path(checks[1]["log"]).read_text()
    audits = re.findall(
        r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", output)
    if [n for n, _ in audits] != expected or re.search(r"\bsorryAx\b|: error|: warning", output):
        raise RuntimeError("Unexpected axiom output or diagnostic")
    declarations = dict(previous["audited_declarations"])
    for name, raw in audits:
        axioms = {a.strip() for a in raw.split(",") if a.strip()}
        if not axioms <= STANDARD_AXIOMS or name in declarations:
            raise RuntimeError(f"Unexpected axioms or duplicate declaration: {name}")
        declarations[name] = sorted(axioms)
    changed = [p for p, h in hashes.items() if sha256(ROOT / p) != h]
    if changed:
        raise RuntimeError(f"Sources changed during verification: {changed}")
    root = (ROOT / "UnifiedTheory.lean").read_text()
    if not all(f"import {target}\n" in root for target in TARGETS):
        raise RuntimeError("Missing integration import")
    report = {
        "checks": checks,
        "verification_mode": "Incremental: 208 freshly checked declarations plus 2187 previous checks retained after verifying their proof-source, audit-script and verification-log hashes, including the full predecessor certificate chain.",
        "predecessor_report": PREVIOUS_REPORT,
        "predecessor_report_sha256": hashes[PREVIOUS_REPORT],
        "retained_verified_source_count": len(retained),
        "retained_declaration_count": PREVIOUS_COUNT,
        "new_public_declaration_count": NEW_COUNT,
        "new_module_count": len(NEW_TARGETS),
        "audited_declarations": declarations,
        "source_sha256": hashes,
        "local_lean_dependency_count": len(local_sources),
        "root_imports_present": TARGETS,
        "root_build_checked": False,
        "uses_temporary_dependency_overlay": False,
        "scope": "Post-2187 bare scalar OS generator, positive-time test-density and quantitative renormalization advances. Constructs explicit positive-time cutoffs with L1 convergence, extends actual mixed-order reflection positivity to all positive-time Schwartz tests, and proves unitary equivalence of the bounded-slab and unrestricted reflected Hilbert completions with exact translated-test evolution. Constructs the actual Bochner Laplace resolvent, its dense injective symmetric range, and a nonnegative self-adjoint inverse-shift Hamiltonian; proves that its graph is exactly the maximal negative right-derivative generator graph of the actual OS semigroup, with unitary transport to the unrestricted test space. One actual normalized vanishing-mesh/infinite-volume Wilson subsequence carries all four Euclidean translation identities, unrestricted positive-time reflection positivity, evolution and that constructed maximal generator. Constructs the invariant normalized vacuum and its zero energy, an actual bounded resolvent at -1, and proves that the collapsed unscaled beta-to-infinity Hamiltonian has full domain and zero action and fails finite excitation and the stated spectral requirements. Derives polynomial identity-neighborhood Haar mass from an actual finite unitary-matrix grid and finite-partition probability, quadratic holonomy-defect estimates, explicit normalized Wilson concentration and all-order fixed-Schwartz bounds independent of volume and spacing. Proves actual centered fixed-smear reflected two-point bounds and sufficient bounds after the proposed a^-4 normalization; explicit refining/expanding balanced trajectories give uniform upper bounds, while a faster coefficient trajectory forces these proposed rescaled forms to zero. No physical running-coupling prescription, nonzero renormalized limit, continuum curvature identification, full field reconstruction/covariance, functional-calculus exponential identity or positive physical mass gap is proved. All twelve full Clay requirements remain open.",
        "yang_mills_requirements_check": json.loads(Path(checks[2]["log"]).read_text()),
        "remaining_unformalized": REMAINING,
    }
    target = ROOT / "data/yang_mills_generator_density_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print(f"{NEW_COUNT} fresh standard-axiom checks; {len(declarations)} cumulative; "
          f"{len(local_sources)} local Lean sources fingerprinted.")
    print(target)


if __name__ == "__main__":
    main()
