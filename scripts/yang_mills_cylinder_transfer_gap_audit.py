#!/usr/bin/env python3
"""Incremental cylinder-transfer-gap audit, retaining 5230 validated checks.

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
from yang_mills_locality_cylinder_audit import TARGETS as PREVIOUS_TARGETS

NEW_TARGETS = ['UnifiedTheory.Clay.YangMills.ReversibleLocalClustering', 'UnifiedTheory.Clay.YangMills.WilsonCylinderBlockAction', 'UnifiedTheory.Clay.YangMills.WilsonCylinderClustering', 'UnifiedTheory.Clay.YangMills.WilsonCylinderConditionalInfluence', 'UnifiedTheory.Clay.YangMills.WilsonCylinderContraction', 'UnifiedTheory.Clay.YangMills.WilsonCylinderParallelKernel', 'UnifiedTheory.Clay.YangMills.WilsonCylinderSpectralBridge', 'UnifiedTheory.Clay.YangMills.WilsonCylinderUpdateLocality', 'UnifiedTheory.Clay.YangMills.WilsonStrongCouplingTransferGap']
TARGETS = PREVIOUS_TARGETS + NEW_TARGETS
CHECK = 'scripts/CheckYangMillsCylinderTransferGap.lean'
PREVIOUS_REPORT = 'data/yang_mills_locality_cylinder_audit.json'
NEW_COUNT = 121
PREVIOUS_COUNT = 5230
REMAINING = ['The ORIGINAL finite-cutoff SU2 transfer now has the proved full vacuum-orthogonal contraction and excited-to-top spectral ratio <=q(beta)=1-(1-36 beta)/8, uniformly in even spatial period. It is strict for0<=beta<1/36. This is a strong-coupling regulated lattice result; the nonzero continuum physical mass gap remains unproved.', 'Find control valid along an independently identified physical weak-coupling trajectory beta(a)->infinity, sufficient for ||A_a-P_vac||<=exp(-m a) with m>0 independent of the cutoff. The present q(beta) reaches1 at beta=1/36 and is not a contracting estimate beyond that range.', 'Prove nonzero rescaled excited-sector survival and finite-energy source overlap. A positive dimensionless lattice gap by itself does not supply a surviving finite physical mass; at fixed beta this lower bound divided by a diverges as a->0.', 'Construct and identify the infinite-spatial-volume and ultraviolet limits of the actual theory, with consistent Schwinger distributions and a nontrivial renormalized continuum. Finite-volume ratio uniformity alone does not perform these constructions.', 'Establish uniform all-order mixed-source Schwartz bounds, common-domain fields, cyclicity, Poincare covariance, joint forward-cone spectrum and locality, and extend the construction beyond SU2 to every compact simple gauge group required by the Clay problem.', 'All twelve full Clay requirements remain open; no nonzero continuum candidate, complete formal Clay axiom set, full-root build or Clay certificate is claimed.']


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
                   "scripts/CheckYangMillsLocalityCylinder.lean"]:
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
        raise RuntimeError("Post-5230 Yang--Mills source inventory does not match NEW_TARGETS")
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
        CHECK, "scripts/yang_mills_cylinder_transfer_gap_audit.py", PREVIOUS_REPORT,
        "data/yang_mills_requirements.json", "scripts/check_yang_mills_requirements.py",
        "UnifiedTheory/Clay/YangMills/README.md",
        "UnifiedTheory.lean", "UnifiedTheory/QSeries/README.md",
    ]))
    hashes = {p: sha256(ROOT / p) for p in sources}
    env = os.environ.copy()
    env.pop("LEAN_PATH", None)
    env["LEAN_NUM_THREADS"] = "2"
    logs = Path(tempfile.mkdtemp(prefix="unifiedtheory-yang-mills-cylinder-transfer-gap-audit-"))
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
        "scope": 'Derives actual open-cylinder one-coordinate conditional laws and their sharp bounded-test influence2 beta times shared-plaquette multiplicity, including diagonal erasure and full/local action constant cancellation. Proves genuine independent-block action decomposition, normalized product conditional/Dirac kernel equality, actual random-color stationarity/reversibility/locality and volume/time-length-independent norm contraction. These yield actual raw-cylinder covariance decay with q=1-(1-36 beta)/8. Exact interior gluing and fixed-cutoff vacuum limits convert that decay to moments of the ORIGINAL full Wilson transfer. Continuous eigenfunction representatives, real/imaginary component extraction, reversible-moment prefactor removal, positivity and compactness establish full complex vacuum-orthogonal norm contraction, all-step decay, and excited-to-top spectral ratio |rho/||T|||<=q without a supplied decay or spectral hypothesis in the final actual-model theorem. For even spatial n and0<=beta<1/36, q<1 and positive excited spectral values have lattice energy floor -log q>0, uniformly in spatial volume. No weak-coupling trajectory, surviving rescaled excitation or nonzero continuum Yang-Mills theory is constructed.',
        "yang_mills_requirements_check": json.loads(Path(checks[2]["log"]).read_text()),
        "remaining_unformalized": REMAINING,
    }
    target = ROOT / 'data/yang_mills_cylinder_transfer_gap_audit.json'
    target.write_text(json.dumps(report, indent=2) + "\n")
    print(f"{NEW_COUNT} fresh standard-axiom checks; {len(declarations)} cumulative; "
          f"{len(local_sources)} local Lean sources fingerprinted.")
    print(target)


if __name__ == "__main__":
    main()
