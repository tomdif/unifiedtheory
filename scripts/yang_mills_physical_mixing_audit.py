#!/usr/bin/env python3
"""Incremental physical-mixing audit, retaining 4493 validated checks.

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
from yang_mills_spectral_ratio_audit import TARGETS as PREVIOUS_TARGETS

NEW_TARGETS = ['UnifiedTheory.Clay.YangMills.HeatBathTwoEdge', 'UnifiedTheory.Clay.YangMills.SU2ConditionalInfluence', 'UnifiedTheory.Clay.YangMills.WilsonGaugeHeatBathComparison', 'UnifiedTheory.Clay.YangMills.WilsonGroundHeatBath', 'UnifiedTheory.Clay.YangMills.WilsonGroundHeatBathVariance', 'UnifiedTheory.Clay.YangMills.WilsonHeatBathComparison', 'UnifiedTheory.Clay.YangMills.WilsonTemporalGauge', 'UnifiedTheory.Clay.YangMills.WilsonTemporalInfluence']
TARGETS = PREVIOUS_TARGETS + NEW_TARGETS
CHECK = 'scripts/CheckYangMillsPhysicalMixing.lean'
PREVIOUS_REPORT = 'data/yang_mills_spectral_ratio_audit.json'
NEW_COUNT = 162
PREVIOUS_COUNT = 4493
REMAINING = ['Prove a quantitatively suitable collective variance/correlation estimate for the actual constructed ground law or its temporal-gauge row laws, uniformly in spatial volume and along an independently identified physical coupling trajectory. The physical mass gap remains unproved.', 'Exploit gauge-invariant collective cancellations or correctly normalized parallel/block dynamics. Exact conditional block updates, reversible ground edge law, conditional-variance identities, and actual two-edge transfer comparisons are now constructed; they do not establish mixing. Bounded local input ratios and rare bad staples do not supply the missing collective contraction.', 'Retain coverage and clocks when combining blocks: gamma Var_pi(f)<=C sum_B alpha_B E_QB(f), together with the actual comparison constants A_B, yields only gamma/(a C sum_B alpha_B A_B) as the linear physical energy floor. The required uniform behavior of this expression, or fixed-physical-time block contraction, remains open.', 'Extend finite-cutoff continuous real invariant-observable estimates to the required physical completion as needed; complete the trace-class/periodic Wilson trace dictionary, vacuum-limit comparison, source overlap and finite positive physical spectral-window survival.', 'Construct a nonzero renormalized four-dimensional continuum with all-order mixed-source Schwartz bounds, physical coupling/normalization identification, common-domain fields, cyclicity, Poincare covariance, joint forward-cone spectrum and locality for every compact simple gauge group.', 'The Euclidean single-link influence obstruction concerns a specific absolute-influence method, not failure of the physical transfer mass gap. Its actual Haar-response/proxy theorems are Lean-certified; the full 18-neighbor W1/Dobrushin interpretation and high-temperature criterion remain separately reviewed natural mathematics.', 'All twelve full Clay requirements remain open. No full-root build or Clay certificate is claimed.']


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
                   "scripts/CheckYangMillsSpectralRatio.lean"]:
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
        raise RuntimeError("Post-4493 Yang--Mills source inventory does not match NEW_TARGETS")
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
        CHECK, "scripts/yang_mills_physical_mixing_audit.py", PREVIOUS_REPORT,
        "data/yang_mills_requirements.json", "scripts/check_yang_mills_requirements.py",
        "UnifiedTheory/Clay/YangMills/README.md",
        "UnifiedTheory.lean", "UnifiedTheory/QSeries/README.md",
    ]))
    hashes = {p: sha256(ROOT / p) for p in sources}
    env = os.environ.copy()
    env.pop("LEAN_PATH", None)
    env["LEAN_NUM_THREADS"] = "2"
    logs = Path(tempfile.mkdtemp(prefix="unifiedtheory-yang-mills-physical-mixing-audit-"))
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
        "scope": 'Constructs the actual squared-ground-law conditional block update family, normalized conditional densities, exact disintegration, reversible edge measure with both actual stationary marginals, and its conditional-variance/projection-residual energy identities. An explicit two-edge conditional-density argument proves E_QB<=(1+exp(12 beta |B|))^2 E_P for continuous real observables. Exact Haar projection removal on gauge-invariant tests constructs an unaveraged representation with the same actual ground and physical action. Its actual normalized row laws have localized input likelihood tilts, exp(8 beta |B|) row comparison, exact reweighting/covariance response and detailed balance. Equality of physical invariant squared increments sharpens the heat-bath comparison to (1+exp(4 beta |B|))^2 against the ORIGINAL full transfer Dirichlet form with unchanged clock. Separately, actual SU2 Haar tangent response and an original-Wilson-law annealed lower proxy show why the usual absolute single-link influence route cannot be rescued just by rare bad staples. No collective variance-factorization, volume-uniform physical contraction, surviving continuum theory, or Clay theorem is asserted.',
        "yang_mills_requirements_check": json.loads(Path(checks[2]["log"]).read_text()),
        "remaining_unformalized": REMAINING,
    }
    target = ROOT / "data/yang_mills_physical_mixing_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print(f"{NEW_COUNT} fresh standard-axiom checks; {len(declarations)} cumulative; "
          f"{len(local_sources)} local Lean sources fingerprinted.")
    print(target)


if __name__ == "__main__":
    main()
