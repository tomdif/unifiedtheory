#!/usr/bin/env python3
"""Incremental actual Wilson tuning and renormalized-limit audit, retaining 2395 validated checks.

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
from yang_mills_generator_density_audit import TARGETS as PREVIOUS_TARGETS

NEW_TARGETS = [
    'UnifiedTheory.Clay.YangMills.ClassicalWilsonPlaquette',
    'UnifiedTheory.Clay.YangMills.CompactGibbsContinuity',
    'UnifiedTheory.Clay.YangMills.FullSchwartzReflection',
    'UnifiedTheory.Clay.YangMills.ProposedCouplingSelection',
    'UnifiedTheory.Clay.YangMills.ProposedCouplingTail',
    'UnifiedTheory.Clay.YangMills.RenormalizedFullOSLimit',
    'UnifiedTheory.Clay.YangMills.RenormalizedOSWitness',
    'UnifiedTheory.Clay.YangMills.RenormalizedSpacetimeTranslation',
    'UnifiedTheory.Clay.YangMills.RenormalizedWilsonHierarchy',
    'UnifiedTheory.Clay.YangMills.RenormalizedWilsonLimit',
    'UnifiedTheory.Clay.YangMills.RenormalizedWilsonUltrafilter',
    'UnifiedTheory.Clay.YangMills.SchwartzCutoffDensity',
    'UnifiedTheory.Clay.YangMills.SchwartzTensorContinuity',
    'UnifiedTheory.Clay.YangMills.TunedRenormalizedLimit',
    'UnifiedTheory.Clay.YangMills.UltrafilterHierarchyCompactness',
    'UnifiedTheory.Clay.YangMills.UnitaryExponentialPlaquette',
    'UnifiedTheory.Clay.YangMills.WilsonMeanSubtraction',
    'UnifiedTheory.Clay.YangMills.WilsonReflectedTuning',
]
TARGETS = PREVIOUS_TARGETS + NEW_TARGETS
CHECK = "scripts/CheckYangMillsRenormalizedTuning.lean"
PREVIOUS_REPORT = "data/yang_mills_generator_density_audit.json"
NEW_COUNT = 163
PREVIOUS_COUNT = 2395
REMAINING = [
    'Construct and justify the physical compact simple Lie-group setting, renormalized curvature-field multiplets, running coupling and scale prescription, and operator mixing. The new actual exponential-link and Wilson-action limits are classical constant-matrix-connection results; the explicit positive reference is U(2), without a formal determinant-one/SU(2) identification. They do not establish quantum local-field identification.',
    'At each fixed regulator the actual proposed rescaled reflected signal is continuous in beta and tends to zero at large beta, so the small tuning endpoint is now proved. A uniformly positive actual connected reflected reference endpoint along an admissible ultraviolet branch remains unproved. Its existence is a hypothesis of the one-sided coupling-selection theorem; a deterministic positive configuration, ordinary variance, or full finite Gibbs support does not discharge it.',
    'Actual cutoff-dependent affine insertions are evaluated under the original Wilson action. The actual finite one-point mean and its real-character specialization provide identity counterterms that set every smeared first moment to zero. Higher-order regulator-uniform bounds and a positive reflected covariance do not follow from this subtraction. Common ultrafilter extraction, normalization, translations, full positive-time reflection positivity and transfer of a positive connected floor to a nonzero vacuum-orthogonal state are proved from explicit regulator-uniform continuous Schwartz-seminorm bounds at every order and a positive reflected floor. Those analytic bounds and that floor are not proved for a physical renormalization trajectory; the ultrafilter construction is not a sequential-limit or uniqueness theorem. The tuning-to-limit connection remains conditional on its reference endpoint and uniform hierarchy bounds.',
    'The preceding bare scalar maximal nonnegative self-adjoint Hamiltonian and full-test evolution remain certified. This phase does not construct renormalized local quantum fields on a common invariant domain, renormalized dynamics or its generator, full Euclidean rotations, physical Poincare covariance or joint forward-cone spectrum. The functional-calculus identification of the earlier bare semigroup with exp(-tH) also remains separate.',
    'Physical short-distance singularities, stress tensor and operator-product behavior, nontrivial vacuum uniqueness, infinite-volume control in the renormalized theory, and a finite positive physical excitation scale or mass gap remain open. The bare weak-coupling collapse and explicit rapid rescaling-collapse trajectory are not no-go theorems for properly renormalized Yang--Mills theory. All twelve full Clay requirements remain open.',
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
                   "scripts/CheckYangMillsDirectRequirements.lean",
                   "scripts/CheckYangMillsGeneratorDensity.lean"]:
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
        raise RuntimeError("Post-2395 Yang--Mills source inventory does not match NEW_TARGETS")
    expected = re.findall(r"^#print axioms (\S+)$", (ROOT / CHECK).read_text(), re.M)
    discovered = []
    for module in NEW_TARGETS:
        source = (ROOT / (module.replace(".", "/") + ".lean")).read_text()
        if re.search(r"\b(?:sorry|admit|native_decide)\b|^\s*(?:private\s+)?axiom\s", source, re.M):
            raise RuntimeError(f"Forbidden proof shortcut or axiom in {module}")
        namespaces = re.findall(r"^namespace (\S+)", source, re.M)
        if len(namespaces) != 1:
            raise RuntimeError("Expected one explicit namespace per new module")
        discovered += [namespaces[0] + "." + n for n in re.findall(
            r"^(?:@\[[^\]]*\]\s*)?(?:def|abbrev|theorem|lemma|instance|structure)\s+(\w+)", source, re.M)]
    if expected != discovered or len(expected) != NEW_COUNT or len(set(expected)) != NEW_COUNT:
        raise RuntimeError("Every new public definition and theorem must be checked")
    local_sources = sorted({p for target in TARGETS for p in local_dependencies(target)})
    sources = sorted(set(local_sources + list(previous["source_sha256"]) + [
        CHECK, "scripts/yang_mills_renormalized_tuning_audit.py", PREVIOUS_REPORT,
        "data/yang_mills_requirements.json", "scripts/check_yang_mills_requirements.py",
        "UnifiedTheory/Clay/YangMills/README.md",
        "UnifiedTheory.lean", "UnifiedTheory/QSeries/README.md",
    ]))
    hashes = {p: sha256(ROOT / p) for p in sources}
    env = os.environ.copy()
    env.pop("LEAN_PATH", None)
    env["LEAN_NUM_THREADS"] = "2"
    logs = Path(tempfile.mkdtemp(prefix="unifiedtheory-yang-mills-renormalized-tuning-audit-"))
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
        "scope": "Post-2395 actual finite Wilson tuning, conditional renormalized-limit construction and classical plaquette normalization. Proves parameter continuity of normalized compact Gibbs expectations and actual centered reflected Wilson forms, including their beta-dependent means. Derives a high-beta small-signal endpoint from the previously proved quantitative Haar/grid concentration; one-sided tuning therefore requires only the still-explicit positive reference endpoint, with normalization fixed independently of beta. Constructs actual all-order cell-smeared moments for regulator-dependent observable characters under the original action character, with exact reflected tensor and connected-subtraction identities. Constructs the translation-invariant one-point mean, proves its coupling continuity, and proves that subtracting this actual complex or real-character mean makes every smeared first moment zero under the same Wilson law, without variance-based normalization. From regulator-uniform continuous Schwartz-seminorm bounds, constructs one common ultrafilter limit over all orders and all tests without a separability premise, and proves moving-test limits, normalization and all four Euclidean translation identities. Proves all-Schwartz-seminorm cutoff convergence, joint tensor continuity and extension from bounded-slab to unrestricted positive-time reflection positivity without a special bare L1 bound. A positive actual centered reflected floor produces a nonzero vacuum-orthogonal vector with preserved lower norm in the actual unrestricted reflected Hilbert completion. The tuned renormalized-candidate assembly remains conditional on the positive endpoint and all-order uniform bounds, rather than asserting these estimates. For actual skew-Hermitian matrix-exponential links, proves the four-link commutator expansion, fourth-order Wilson trace-defect coefficient, little-o remainder, and exact identification with the existing periodic lattice holonomy. An explicit two-by-two unitary reference has coefficient four and a deterministic lower bound uniform in period and site; the actual constant-connection Wilson action per physical lattice volume converges to the classical bracket energy at fixed beta, even for arbitrary varying period. These deterministic classical results do not establish a Wilson-measure covariance floor, a formal SU(2) reference, quantum curvature-field identification, physical running coupling, renormalized field reconstruction/dynamics, short-distance operator behavior or a positive physical mass gap. All twelve full Clay requirements remain open.",
        "yang_mills_requirements_check": json.loads(Path(checks[2]["log"]).read_text()),
        "remaining_unformalized": REMAINING,
    }
    target = ROOT / "data/yang_mills_renormalized_tuning_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print(f"{NEW_COUNT} fresh standard-axiom checks; {len(declarations)} cumulative; "
          f"{len(local_sources)} local Lean sources fingerprinted.")
    print(target)


if __name__ == "__main__":
    main()
