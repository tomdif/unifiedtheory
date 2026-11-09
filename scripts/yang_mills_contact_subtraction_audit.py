#!/usr/bin/env python3
"""Incremental contact-subtraction audit, retaining 5661 validated checks.

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
from yang_mills_smooth_noise_obstruction_audit import TARGETS as PREVIOUS_TARGETS

NEW_TARGETS = ['UnifiedTheory.Clay.YangMills.FiniteLocalContactFactor', 'UnifiedTheory.Clay.YangMills.FiniteSourceWickJets', 'UnifiedTheory.Clay.YangMills.QuadraticCumulantInvariance', 'UnifiedTheory.Clay.YangMills.SU2ExcessAllMoments', 'UnifiedTheory.Clay.YangMills.SU2WilsonAllMoments', 'UnifiedTheory.Clay.YangMills.SchwartzDiagonalTaylor', 'UnifiedTheory.Clay.YangMills.WilsonBlockNoiseKernel', 'UnifiedTheory.Clay.YangMills.WilsonCompactContactSubtraction', 'UnifiedTheory.Clay.YangMills.WilsonNoiseCellPairing', 'UnifiedTheory.Clay.YangMills.WilsonNoisePhysicalSupport', 'UnifiedTheory.Clay.YangMills.WilsonNoiseSourceJets', 'UnifiedTheory.Clay.YangMills.WilsonNoiseTubeMass', 'UnifiedTheory.Clay.YangMills.WilsonPhysicalStencilLocality']
TARGETS = PREVIOUS_TARGETS + NEW_TARGETS
CHECK = 'scripts/CheckYangMillsContactSubtraction.lean'
PREVIOUS_REPORT = 'data/yang_mills_smooth_noise_obstruction_audit.json'
NEW_COUNT = 190
PREVIOUS_COUNT = 5661
REMAINING = ['Control the actual retained interacting covariance after the constructed one-block contact subtraction, including a nonzero separated reflected signal and the physical logarithmic bracket signs. The proved O(a) remainder concerns the removed covariance only.', 'Iterate integration under the successive induced laws with uniform estimates. The eight original-law block noise matrices cannot simply be summed and subtracted as if they were a sequential decomposition.', 'Extend compact-test diagonal subtraction to full Schwartz distributions by proving weighted tails and periodic-image estimates; construct compatible derivative/position-dependent counterterms with reflection covariance and all necessary field symmetries.', 'Control higher connected source derivatives and their local counterterms. Deterministic quadratic subtraction leaves connected derivatives of order at least 3 unchanged. The local Gamma moments and cumulants do not prove macroscopic higher-cumulant divergence or supply uniform interacting all-order estimates.', 'Construct a common continuous full-Schwartz hierarchy with cutoff-independent bounds and prove its full reflection/translation/covariance properties. The new finite-source generating functions have every ordered mixed derivative, but are not an already constructed continuum hierarchy.', 'Establish relative physical transfer energy, nonzero continuum normalization, all remaining field/domain/cyclicity/spectrum/locality requirements and every required compact simple gauge group. All twelve full Clay requirements remain open; neither a physical mass gap nor a nonzero continuum theory is proved.']


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
                   "scripts/CheckYangMillsParallelGap.lean",
                   "scripts/CheckYangMillsLocalityCylinder.lean",
                   "scripts/CheckYangMillsCylinderTransferGap.lean",
                   "scripts/CheckYangMillsWeakLocalScaling.lean",
                   "scripts/CheckYangMillsPhysicalSourceBridge.lean",
                   "scripts/CheckYangMillsSmoothNoiseObstruction.lean"]:
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
        raise RuntimeError("Post-5661 Yang--Mills source inventory does not match NEW_TARGETS")
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
        CHECK, "scripts/yang_mills_contact_subtraction_audit.py", PREVIOUS_REPORT,
        "data/yang_mills_requirements.json", "scripts/check_yang_mills_requirements.py",
        "UnifiedTheory/Clay/YangMills/README.md",
        "UnifiedTheory.lean", "UnifiedTheory/QSeries/README.md",
    ]))
    hashes = {p: sha256(ROOT / p) for p in sources}
    env = os.environ.copy()
    env.pop("LEAN_PATH", None)
    env["LEAN_NUM_THREADS"] = "2"
    logs = Path(tempfile.mkdtemp(prefix="unifiedtheory-yang-mills-contact-subtraction-audit-"))
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
        "scope": 'Constructs a deterministic removed-noise covariance matrix C_S from actual original Wilson block conditional expectations. It is symmetric PSD; full covariance minus C_S equals the true retained covariance. Independent blocks give a finite stencil with at most 24 neighbors, |C_S(p,q)|<=16 and row absolute sum<=384. Actual floor/residue no-wrap geometry makes the sampled a^-8 kernel vanish outside distance 4a on each fixed compact region once the physical period is large. A hard near-diagonal tube has proved absolute mass at most M_R/a^4, M_R=2048*pi^2*volume(closedBall(0,R)). A fourth-order diagonal Taylor counterterm computed from that actual kernel leaves an O(a) remainder on compact two-point tests, uniformly in coupling and period under the stated no-wrap condition; the counterterm vanishes away from the diagonal. Exact finite-cell Fubini binds the physical tensor pairing to actual rescaled original-minus-retained covariance, yielding the repaired-covariance O(a) reduction. Separately constructs every ordered mixed derivative of finite-dimensional source generating functions with deterministic symmetric quadratic matrices, binds the actual C_S correction to the Wilson measure, and identifies corrected second derivatives with retained covariance. Higher corrected jets are not identified with retained moments. Quadratic factors alter only the second connected derivative at zero source, and leave every order>=3 connected derivative unchanged at any source. Every fixed natural moment of the actual microscopic one-link excess converges to the Gamma(3/2) rising-product moment uniformly in varying volumes; its third/fourth cumulant polynomials tend to 3 and 9. These are local noise moments, not physical continuum correlations. Retained estimates, repeated interacting integration, full Schwartz tails, generating reflection covariance and the continuum theory remain open.',
        "yang_mills_requirements_check": json.loads(Path(checks[2]["log"]).read_text()),
        "remaining_unformalized": REMAINING,
    }
    target = ROOT / 'data/yang_mills_contact_subtraction_audit.json'
    target.write_text(json.dumps(report, indent=2) + "\n")
    print(f"{NEW_COUNT} fresh standard-axiom checks; {len(declarations)} cumulative; "
          f"{len(local_sources)} local Lean sources fingerprinted.")
    print(target)


if __name__ == "__main__":
    main()
