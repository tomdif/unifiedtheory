#!/usr/bin/env python3
"""Incremental locality-cylinder audit, retaining 4979 validated checks.

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
from yang_mills_parallel_gap_audit import TARGETS as PREVIOUS_TARGETS

NEW_TARGETS = ['UnifiedTheory.Clay.YangMills.ContinuousBoundaryMoments', 'UnifiedTheory.Clay.YangMills.ContinuousUpdateContraction', 'UnifiedTheory.Clay.YangMills.CoordinateSupport', 'UnifiedTheory.Clay.YangMills.FiniteIncidenceInfluence', 'UnifiedTheory.Clay.YangMills.WilsonBoundaryTransfer', 'UnifiedTheory.Clay.YangMills.WilsonCylinderColors', 'UnifiedTheory.Clay.YangMills.WilsonCylinderCoordinates', 'UnifiedTheory.Clay.YangMills.WilsonCylinderGeometry', 'UnifiedTheory.Clay.YangMills.WilsonCylinderGluing', 'UnifiedTheory.Clay.YangMills.WilsonCylinderInfluenceGeometry', 'UnifiedTheory.Clay.YangMills.WilsonCylinderVacuum', 'UnifiedTheory.Clay.YangMills.WilsonDisjointDirichlet', 'UnifiedTheory.Clay.YangMills.WilsonFiniteCylinder', 'UnifiedTheory.Clay.YangMills.WilsonInteriorVacuum', 'UnifiedTheory.Clay.YangMills.WilsonLocalClustering', 'UnifiedTheory.Clay.YangMills.WilsonParallelL2', 'UnifiedTheory.Clay.YangMills.WilsonSourceClustering', 'UnifiedTheory.Clay.YangMills.WilsonSupportPropagation']
TARGETS = PREVIOUS_TARGETS + NEW_TARGETS
CHECK = 'scripts/CheckYangMillsLocalityCylinder.lean'
PREVIOUS_REPORT = 'data/yang_mills_parallel_gap_audit.json'
NEW_COUNT = 251
PREVIOUS_COUNT = 4979
REMAINING = ['The physical mass gap remains unproved. Original periodic4D SU2 Wilson covariance decay is proved at0<=beta<1/36 on even n>1, in the actual shared-plaquette graph metric. It is not yet a uniform physical-transfer spectral ratio.', 'Complete the open-cylinder conditional-law and product-color-update dictionaries. Derive actual influence from the local face action, bind its geometric coefficient and row estimate, and reproduce the actual norm contraction and locality-to-clustering argument uniformly in independent temporal length and spatial volume.', 'The raw full-cylinder interior correlation and connected covariance now have the exact original-transfer vacuum limit at fixed spatial cutoff and fixed separation. Combine this proved dictionary with an independently established uniform cylinder clustering estimate; the limit alone supplies no volume-uniform contraction.', 'Use uniform actual cylinder clustering and the constructed positive vacuum to bound the ORIGINAL full transfer on the vacuum-orthogonal sector, with its physical clock retained. Then derive a dense-test/all-domain spectral norm statement rather than estimating only selected observables.', 'Obtain control on an independently identified physical weak-coupling trajectory beta(a)->infinity. Even a completed small-beta physical transfer bound does not construct a nonzero renormalized four-dimensional continuum or finite physical-energy overlap.', 'Construct surviving renormalized fields, uniform all-order mixed-source Schwartz bounds, common domains, cyclicity, Poincare covariance, joint forward-cone spectrum and locality for every compact simple gauge group. All twelve full Clay requirements remain open.', 'No full-root build, completed continuum candidate or Clay certificate is claimed. All new proofs use real dependency builds and exhaustive named-symbol standard-axiom checks.']


def main():
    previous = json.loads((ROOT / PREVIOUS_REPORT).read_text())
    prior_names = []
    for ledger in ["scripts/CheckParticleHamiltonians.lean", "scripts/CheckParticleEnergyGap.lean",
                   "scripts/CheckBosonicParticleSectors.lean", "scripts/CheckBosonicEnergyClayFramework.lean", "scripts/CheckYangMillsSwarm.lean",
                   "scripts/CheckYangMillsConstruction.lean",
                   "scripts/CheckYangMillsLatticeBridge.lean",
                   "scripts/CheckYangMillsReflectedHierarchy.lean",
                   "scripts/CheckYangMillsSchwingerBridge.lean",
                   "scripts/CheckYangMillsDirectRequirements.lean",
                   "scripts/CheckYangMillsGeneratorDensity.lean",
                   "scripts/CheckYangMillsRenormalizedTuning.lean",
                   "scripts/CheckYangMillsTemperedDynamics.lean",
                   "scripts/CheckYangMillsLocalFluctuation.lean",
                   "scripts/CheckYangMillsContinuumWindow.lean",
                   "scripts/CheckYangMillsFullSlab.lean",
                   "scripts/CheckYangMillsSourceResponse.lean",
                   "scripts/CheckYangMillsLocalSource.lean",
                   "scripts/CheckYangMillsBlockSource.lean",
                   "scripts/CheckYangMillsSourceTower.lean",
                   "scripts/CheckYangMillsSeparatedSources.lean",
                   "scripts/CheckYangMillsSourceExpansion.lean",
                   "scripts/CheckYangMillsHaarSource.lean",
                   "scripts/CheckYangMillsClayAttack.lean",
                   "scripts/CheckYangMillsInteractionGap.lean",
                   "scripts/CheckYangMillsProbabilitySpectrum.lean",
                   "scripts/CheckYangMillsPhysicalObligations.lean",
                   "scripts/CheckYangMillsTransferConstruction.lean",
                   "scripts/CheckYangMillsSpectralRatio.lean",
                   "scripts/CheckYangMillsPhysicalMixing.lean",
                   "scripts/CheckYangMillsCollectiveSlab.lean",
                   "scripts/CheckYangMillsParallelGap.lean"]:
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
        raise RuntimeError("Post-4979 Yang--Mills source inventory does not match NEW_TARGETS")
    expected = re.findall(r"^#print axioms (\S+)$", (ROOT / CHECK).read_text(), re.M)
    discovered = []
    for module in NEW_TARGETS:
        source = (ROOT / (module.replace(".", "/") + ".lean")).read_text()
        if re.search(r"\b(?:sorry|admit|native_decide)\b|^\s*(?:private\s+)?axiom\s", source, re.M):
            raise RuntimeError(f"Forbidden proof shortcut or axiom in {module}")
        namespaces = re.findall(r"^namespace (\S+)", source, re.M)
        if len(namespaces) != 1:
            raise RuntimeError("Expected one explicit namespace per new module")
        declarations = re.findall(
            r"^(?:@\[[^\]]*\]\s*)?(?:local\s+)?(?:def|abbrev|theorem|lemma|instance|structure)\s+(\w+|:)",
            source, re.M)
        for name in declarations:
            if name == ":":
                if module.rsplit(".", 1)[1] not in {"WilsonSingleLinkStaples", "SU2WilsonMarginalTransport"}:
                    raise RuntimeError("Unexpected anonymous instance; identify and audit it explicitly")
                name = "instDecidableEqEdgeVertex"
            discovered.append(namespaces[0] + "." + name)
    if expected != discovered or len(expected) != NEW_COUNT or len(set(expected)) != NEW_COUNT:
        raise RuntimeError("Every new source definition, theorem and instance must be checked")
    local_sources = sorted({p for target in TARGETS for p in local_dependencies(target)})
    sources = sorted(set(local_sources + list(previous["source_sha256"]) + [
        CHECK, "scripts/yang_mills_locality_cylinder_audit.py", PREVIOUS_REPORT,
        "data/yang_mills_requirements.json", "scripts/check_yang_mills_requirements.py",
        "UnifiedTheory/Clay/YangMills/README.md",
        "UnifiedTheory.lean", "UnifiedTheory/QSeries/README.md",
    ]))
    hashes = {p: sha256(ROOT / p) for p in sources}
    env = os.environ.copy()
    env.pop("LEAN_PATH", None)
    env["LEAN_NUM_THREADS"] = "2"
    logs = Path(tempfile.mkdtemp(prefix="unifiedtheory-yang-mills-locality-cylinder-audit-"))
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
        "verification_mode": f"Incremental: {NEW_COUNT} freshly checked declarations plus {PREVIOUS_COUNT} previous checks retained after verifying their proof-source, audit-script and verification-log hashes, including the full predecessor certificate chain.",
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
        "scope": 'Proves actual periodic Wilson support propagation in the shared-plaquette graph, exact disjoint-support cross-Dirichlet cancellation, and continuous L2 norm contraction with no volume prefactor. These give original-Wilson covariance decay q^d sqrt(VarF VarG), q=1-(1-36 beta)/8, with geometric separation and0<=beta<1/36; actual sparse plaquette sources are included. Constructs open time-cylinder geometry at arbitrary temporal length and fixed spatial period, exact full/half endpoint action identities, temporal-Haar integration, normalized law and coordinate/Haar/action transport, actual boundary-message/transfer matrix identities, exact interior finite-chain gluing, and fixed-cutoff raw-cylinder correlation/covariance vacuum limits. The cylinder geometry, conditional-law estimates and physical-transfer uniform bound are kept distinct. No weak-coupling continuum or physical mass-gap theorem is asserted.',
        "yang_mills_requirements_check": json.loads(Path(checks[2]["log"]).read_text()),
        "remaining_unformalized": REMAINING,
    }
    target = ROOT / 'data/yang_mills_locality_cylinder_audit.json'
    target.write_text(json.dumps(report, indent=2) + "\n")
    print(f"{NEW_COUNT} fresh standard-axiom checks; {len(declarations)} cumulative; "
          f"{len(local_sources)} local Lean sources fingerprinted.")
    print(target)


if __name__ == "__main__":
    main()
