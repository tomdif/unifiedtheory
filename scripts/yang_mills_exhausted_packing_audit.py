#!/usr/bin/env python3
"""Incremental exhausted-packing audit, retaining 6577 validated checks.

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
from yang_mills_coarse_control_audit import TARGETS as PREVIOUS_TARGETS

NEW_TARGETS = [
    'UnifiedTheory.Clay.YangMills.GibbsExhaustedTower',
    'UnifiedTheory.Clay.YangMills.FiniteFactorPackingTower',
    'UnifiedTheory.Clay.YangMills.WilsonExtensiveSchedule',
    'UnifiedTheory.Clay.YangMills.SU2WilsonAlignedRealization',
    'UnifiedTheory.Clay.YangMills.MacroscopicContactObstruction',
]
TARGETS = PREVIOUS_TARGETS + NEW_TARGETS
CHECK = 'scripts/CheckYangMillsExhaustedPacking.lean'
PREVIOUS_REPORT = 'data/yang_mills_coarse_control_audit.json'
NEW_COUNT = 114
PREVIOUS_COUNT = 6577
REMAINING = [
    'Prove uniform physical-scale bounds for the exhausted coarse covariance sum exhaustedCoarseSum and exhibit a nonzero separated reflected signal. Eliminating the unintegrated final covariance by exhaustion does not by itself bound the intermediate coarse stage noise kernels.',
    'Extend the full-lattice aligned two-staple Gaussian approximation (-x*y/3 mixed interaction limit) to general non-aligned backgrounds, large-field probabilities, and multi-step renormalization group flow.',
    'Supply quantitative inter-scale decay or cancellation across coarse stages. The formalized rank-one PSD finite-range counterexample boxKernel proves that measurability, symmetry, positive semidefiniteness, a^(-8) amplitude bounds, and macroscopic finite range alone do not imply continuum convergence after degree-4 contact subtraction.',
    'Prove compatible all-order renormalized correlation bounds, including higher partial-diagonal counterterms and mixed retained/noise cumulants.',
    'Prove the physical logarithmic bracket signs, physical coupling trajectory and nonzero normalization; then establish continuum reconstruction, symmetry and reflection positivity, relative transfer-energy gap, domains/cyclicity/spectrum and every compact simple gauge group. All twelve full Clay requirements remain open.',
]


def proof_code(source):
    """Remove nested Lean comments, preserving code, strings and line positions."""
    out=[];i=0;depth=0;quoted=False
    while i<len(source):
        if depth:
            if source.startswith('/-',i):depth+=1;i+=2
            elif source.startswith('-/',i):depth-=1;i+=2
            else:
                if source[i]=='\n':out.append('\n')
                i+=1
        elif quoted:
            out.append(source[i])
            if source[i]=='\\' and i+1<len(source):
                i+=1;out.append(source[i])
            elif source[i]=='"':quoted=False
            i+=1
        elif source.startswith('/-',i):depth=1;out.append(' ');i+=2
        elif source.startswith('--',i):
            j=source.find('\n',i);i=len(source) if j<0 else j
        else:
            quoted=source[i]=='"';out.append(source[i]);i+=1
    if depth or quoted:raise RuntimeError('Unterminated comment or string')
    return ''.join(out)

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
                   "scripts/CheckYangMillsSmoothNoiseObstruction.lean",
                   "scripts/CheckYangMillsContactSubtraction.lean",
                   "scripts/CheckYangMillsSchwartzSuccessive.lean",
                   "scripts/CheckYangMillsInducedLocality.lean",
                   "scripts/CheckYangMillsGrowingTower.lean",
                   "scripts/CheckYangMillsCoarseControl.lean"]:
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
        raise RuntimeError("Post-6577 Yang--Mills source inventory does not match NEW_TARGETS")
    expected = re.findall(r"^#print axioms (\S+)$", (ROOT / CHECK).read_text(), re.M)
    discovered = []
    for module in NEW_TARGETS:
        source = (ROOT / (module.replace(".", "/") + ".lean")).read_text()
        if re.search(r"\b(?:sorry|admit|native_decide)\b|^\s*(?:private\s+)?axiom\s", proof_code(source), re.M):
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
        CHECK, "scripts/yang_mills_exhausted_packing_audit.py", PREVIOUS_REPORT,
        "data/yang_mills_coarse_control_2026_10_28.json",
        "data/yang_mills_requirements.json", "scripts/check_yang_mills_requirements.py",
        "UnifiedTheory/Clay/YangMills/README.md",
        "UnifiedTheory.lean", "UnifiedTheory/QSeries/README.md",
    ]))
    hashes = {p: sha256(ROOT / p) for p in sources}
    env = os.environ.copy()
    env.pop("LEAN_PATH", None)
    env["LEAN_NUM_THREADS"] = "2"
    logs = Path(tempfile.mkdtemp(prefix="unifiedtheory-yang-mills-exhausted-packing-audit-"))
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
        "scope": 'Iterates current-factor maximal packing (packedSchedule, wilsonSchedule) across arbitrary finite depths and proves active coordinate exhaustion by depth B.card, with an extensive initial Wilson block of size at least edgeCount n / 25. Proves that when active coordinates are exhausted, the evolved observable is constant and the unintegrated final covariance vanishes identically, reducing retainedCovariance and coarseCovariance to the pure finite sum exhaustedCoarseSum of coarse stage noise kernels. Realizes the two-staple aligned Gaussian approximation on the actual 4D periodic Wilson lattice (n > 1), proving exact cancellation of reference action terms in the 4-point mixed interaction rectangle and O(1/beta) convergence to -x*y/3 in beta^(-1/2) fluctuation coordinates. Formalizes the rank-one PSD finite-range continuum counterexample boxKernel and proves that its degree-4 contact-repaired pairing diverges as a -> 0+ on tests with nonzero box average, demonstrating that inter-scale cancellation or decay is necessary for continuum convergence of coarse kernels.',
        "yang_mills_requirements_check": json.loads(Path(checks[2]["log"]).read_text()),
        "remaining_unformalized": REMAINING,
    }
    target = ROOT / 'data/yang_mills_exhausted_packing_audit.json'
    target.write_text(json.dumps(report, indent=2) + "\n")
    print(f"{NEW_COUNT} fresh standard-axiom checks; {len(declarations)} cumulative; "
          f"{len(local_sources)} local Lean sources fingerprinted.")
    print(target)


if __name__ == "__main__":
    main()
