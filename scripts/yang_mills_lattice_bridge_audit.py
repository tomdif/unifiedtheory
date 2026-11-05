#!/usr/bin/env python3
"""Incremental lattice-to-analysis bridge audit, retaining 1350 validated checks.

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
from yang_mills_construction_audit import TARGETS as PREVIOUS_TARGETS

NEW_TARGETS = ['UnifiedTheory.Clay.YangMills.BoundaryReflectionGluing', 'UnifiedTheory.Clay.YangMills.BoundedKernelDistribution', 'UnifiedTheory.Clay.YangMills.BoundedKernelL1', 'UnifiedTheory.Clay.YangMills.ConnectedGramLimit', 'UnifiedTheory.Clay.YangMills.GibbsCoordinateTransport', 'UnifiedTheory.Clay.YangMills.GibbsReflectionTransport', 'UnifiedTheory.Clay.YangMills.HaarCenteredFluctuation', 'UnifiedTheory.Clay.YangMills.KernelHilbertCompletion', 'UnifiedTheory.Clay.YangMills.KernelSymmetryUnitary', 'UnifiedTheory.Clay.YangMills.L1HierarchyCompactness', 'UnifiedTheory.Clay.YangMills.LocalGibbsComparison', 'UnifiedTheory.Clay.YangMills.LocalHaarGibbsVariance', 'UnifiedTheory.Clay.YangMills.PeriodicCellSampling', 'UnifiedTheory.Clay.YangMills.PeriodicHalfAction', 'UnifiedTheory.Clay.YangMills.PeriodicHalfGeometry', 'UnifiedTheory.Clay.YangMills.PeriodicHalfSplit', 'UnifiedTheory.Clay.YangMills.PeriodicPlaquetteReflection', 'UnifiedTheory.Clay.YangMills.PeriodicSiteReflection', 'UnifiedTheory.Clay.YangMills.PeriodicTimeReflection', 'UnifiedTheory.Clay.YangMills.PositiveKernelForm', 'UnifiedTheory.Clay.YangMills.SingleCoordinateProduct', 'UnifiedTheory.Clay.YangMills.UnitaryUniformVariance', 'UnifiedTheory.Clay.YangMills.WilsonCellCompactness', 'UnifiedTheory.Clay.YangMills.WilsonCellHierarchy', 'UnifiedTheory.Clay.YangMills.WilsonKernelHilbert', 'UnifiedTheory.Clay.YangMills.WilsonLocalOscillation', 'UnifiedTheory.Clay.YangMills.WilsonNontrivialHilbert', 'UnifiedTheory.Clay.YangMills.WilsonUniformVariance']
TARGETS = PREVIOUS_TARGETS + NEW_TARGETS
CHECK = "scripts/CheckYangMillsLatticeBridge.lean"
PREVIOUS_REPORT = "data/yang_mills_construction_audit.json"
NEW_COUNT = 320
PREVIOUS_COUNT = 1350
REMAINING = ['Physical compact simple Lie group/representation choice, scaling/coupling trajectory, renormalized curvature observables and mixing, ultraviolet behavior and stress tensor remain unconstructed. The proved hierarchy is bounded bare cell interpolation.', 'Regulator-uniform bounds and a strictly positive fixed Schwartz-smeared connected witness for the renormalized theory remain open. The new volume-independent plaquette variance floor assumes bounded coupling and can degenerate as its coupling bound grows.', 'The actual finite even-period Wilson law is now site-reflection positive. Its reflected support-restricted observables and mixed adjoints must still be identified with a common limiting hierarchy, with Euclidean covariance and reconstruction regularity. No link-reflection positivity or one-step positive transfer operator is asserted.', 'Ordinary Wilson Gram-kernel Hilbert reconstruction and its non-vacuum bounded-coupling plaquette state are constructed. They are not an OS reflection quotient; the non-vacuum state need not survive that quotient or fixed-test smearing. The Gram and distributional limits have not been identified as one candidate.', 'Complete OS/local quantum-field reconstruction, physical strongly continuous Poincare representation, invariant cyclic vacuum, tensor covariance, translation generators, joint forward-cone spectrum, and finite positive mass gap for that same reconstructed Hamiltonian remain open. All twelve full-target requirements remain open.', 'Higher Bose-sector domain/CCR identifications, full S3 matter-coupled Pauli--Fierz construction, coupled ground-state/gap results and numerical physical identifications remain separate open work; the auxiliary Bose gap is not a Yang--Mills gap.']


def main():
    previous = json.loads((ROOT / PREVIOUS_REPORT).read_text())
    prior_names = []
    for ledger in ["scripts/CheckParticleHamiltonians.lean", "scripts/CheckParticleEnergyGap.lean",
                   "scripts/CheckBosonicParticleSectors.lean", "scripts/CheckBosonicEnergyClayFramework.lean", "scripts/CheckYangMillsSwarm.lean",
                   "scripts/CheckYangMillsConstruction.lean"]:
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
    expected = re.findall(r"^#print axioms (\S+)$", (ROOT / CHECK).read_text(), re.M)
    discovered = []
    for module in NEW_TARGETS:
        source = (ROOT / (module.replace(".", "/") + ".lean")).read_text()
        namespaces = re.findall(r"^namespace (\S+)", source, re.M)
        if len(namespaces) != 1:
            raise RuntimeError("Expected one explicit namespace per new module")
        discovered += [namespaces[0] + "." + n for n in re.findall(
            r"^(?:@\[[^\]]*\]\s*)?(?:def|abbrev|theorem|instance|structure)\s+(\w+)", source, re.M)]
    if expected != discovered or len(expected) != NEW_COUNT or len(set(expected)) != NEW_COUNT:
        raise RuntimeError("Every new public definition and theorem must be checked")
    local_sources = sorted({p for target in TARGETS for p in local_dependencies(target)})
    sources = sorted(set(local_sources + list(previous["source_sha256"]) + [
        CHECK, "scripts/yang_mills_lattice_bridge_audit.py", PREVIOUS_REPORT,
        "data/yang_mills_requirements.json", "scripts/check_yang_mills_requirements.py",
        "UnifiedTheory/Clay/YangMills/README.md",
        "UnifiedTheory.lean", "UnifiedTheory/QSeries/README.md",
    ]))
    hashes = {p: sha256(ROOT / p) for p in sources}
    env = os.environ.copy()
    env.pop("LEAN_PATH", None)
    env["LEAN_NUM_THREADS"] = "2"
    logs = Path(tempfile.mkdtemp(prefix="unifiedtheory-yang-mills-lattice-bridge-audit-"))
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
        "verification_mode": "Incremental: 320 freshly checked declarations plus 1350 previous checks retained after verifying their proof-source, audit-script and verification-log hashes, including the predecessor certificate chain.",
        "predecessor_report": PREVIOUS_REPORT,
        "predecessor_report_sha256": hashes[PREVIOUS_REPORT],
        "retained_verified_source_count": len(retained),
        "retained_declaration_count": PREVIOUS_COUNT,
        "new_public_declaration_count": NEW_COUNT,
        "audited_declarations": declarations,
        "source_sha256": hashes,
        "local_lean_dependency_count": len(local_sources),
        "root_imports_present": TARGETS,
        "root_build_checked": False,
        "uses_temporary_dependency_overlay": False,
        "scope": "Constructs actual site reflection of even-period four-dimensional Wilson lattices, exact fixed-boundary/half Haar coordinates and action factorization, normalized-law transport and finite-lattice site-reflection positivity for continuous unitary characters (more generally class functions with inversion-invariant real part). Proves volume-independent local action oscillation and a strictly positive plaquette variance floor at bounded coupling, then constructs an ordinary limiting Wilson Gram Hilbert space with a state outside the vacuum span. Constructs explicit positive-kernel null quotients, Hilbert completions, dense canonical spans and unitaries for kernel-preserving label symmetries. Constructs measurable cell-smeared bare Wilson Schwartz distributions, uniform continuous L1 seminorm bounds, and a common subsequential hierarchy limit at all orders and every Schwartz test without a supplied dense family. These separate bare constructions do not supply renormalized continuum nontriviality, a reflection-compatible common hierarchy, OS/local-QFT reconstruction, physical covariance or a Yang--Mills spectral gap.",
        "yang_mills_requirements_check": json.loads(Path(checks[2]["log"]).read_text()),
        "remaining_unformalized": REMAINING,
    }
    target = ROOT / "data/yang_mills_lattice_bridge_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print(f"{NEW_COUNT} fresh standard-axiom checks; {len(declarations)} cumulative; "
          f"{len(local_sources)} local Lean sources fingerprinted.")
    print(target)


if __name__ == "__main__":
    main()
