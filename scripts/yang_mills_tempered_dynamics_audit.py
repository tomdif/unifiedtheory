#!/usr/bin/env python3
"""Incremental tempered OS dynamics and direct Wilson insertion audit, retaining 2558 validated checks.

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
from yang_mills_renormalized_tuning_audit import TARGETS as PREVIOUS_TARGETS

NEW_TARGETS = [
    'UnifiedTheory.Clay.YangMills.FullSchwartzDynamics',
    'UnifiedTheory.Clay.YangMills.FullSchwartzHamiltonian',
    'UnifiedTheory.Clay.YangMills.FullSchwartzHilbert',
    'UnifiedTheory.Clay.YangMills.FullSchwartzVacuum',
    'UnifiedTheory.Clay.YangMills.MeanCenteredWilsonMoments',
    'UnifiedTheory.Clay.YangMills.NormalizedBoundaryResponse',
    'UnifiedTheory.Clay.YangMills.OSDampedKernelShift',
    'UnifiedTheory.Clay.YangMills.OSSubexponentialContraction',
    'UnifiedTheory.Clay.YangMills.OSTemperedDynamics',
    'UnifiedTheory.Clay.YangMills.RapidMeanCenteredBranch',
    'UnifiedTheory.Clay.YangMills.SchwartzTranslationGrowth',
    'UnifiedTheory.Clay.YangMills.TunedRenormalizedDynamics',
    'UnifiedTheory.Clay.YangMills.WilsonBoundaryResponse',
]
TARGETS = PREVIOUS_TARGETS + NEW_TARGETS
CHECK = "scripts/CheckYangMillsTemperedDynamics.lean"
PREVIOUS_REPORT = "data/yang_mills_renormalized_tuning_audit.json"
NEW_COUNT = 144
PREVIOUS_COUNT = 2558
REMAINING = [
    'Prove a physical ultraviolet tuning trajectory: the fixed reflected test and independently prescribed normalization need a positive actual connected reflected endpoint. The normalized boundary response dictionary identifies the finite response whose variance is needed; strict finite positivity or full support alone does not give a uniform rescaled floor.',
    'Prove regulator-uniform all-order bounds simultaneously with nonzero reflected fluctuations on that physical trajectory. Actual all-order mean-centered estimates and a rapidly concentrating branch are proved, but the constructed branch collapses at every positive order and cannot supply the positive endpoint.',
    'Construct the physical compact simple Lie-group setting, curvature-field multiplets and mixing, coupling/scale matching, local field operators on common domains, full Euclidean rotations, Poincare covariance and joint forward-cone spectrum. The conditional scalar hierarchy and its now-constructed maximal OS dynamics do not establish these physical identifications.',
    'Establish the required short-distance behavior, stress tensor/OPE properties, vacuum uniqueness and a finite positive physical excitation scale with a mass gap. The proved nonnegative self-adjoint maximal OS Hamiltonian and zero-energy vacuum do not imply a positive spectral gap.',
    'A common ultrafilter limit is not a sequential convergence or uniqueness result. The two missing nonzero-trajectory estimates remain explicit in the tuned candidate. All twelve full Clay requirements remain open; auxiliary Bose/S3 gaps and separate physical-identification programs cannot certify Yang--Mills.',
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
                   "scripts/CheckYangMillsGeneratorDensity.lean",
                   "scripts/CheckYangMillsRenormalizedTuning.lean"]:
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
        raise RuntimeError("Post-2558 Yang--Mills source inventory does not match NEW_TARGETS")
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
        CHECK, "scripts/yang_mills_tempered_dynamics_audit.py", PREVIOUS_REPORT,
        "data/yang_mills_requirements.json", "scripts/check_yang_mills_requirements.py",
        "UnifiedTheory/Clay/YangMills/README.md",
        "UnifiedTheory.lean", "UnifiedTheory/QSeries/README.md",
    ]))
    hashes = {p: sha256(ROOT / p) for p in sources}
    env = os.environ.copy()
    env.pop("LEAN_PATH", None)
    env["LEAN_NUM_THREADS"] = "2"
    logs = Path(tempfile.mkdtemp(prefix="unifiedtheory-yang-mills-tempered-dynamics-audit-"))
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
        "scope": "Post-2558 direct centered Wilson moment estimates, normalized boundary response, and tempered OS dynamics. Proves polynomial growth and exponentially damped decay of actual Schwartz translations, then derives OS contraction, null descent and strongly continuous symmetric positive evolution from continuous Schwartz correlations, stationarity and reflection positivity without a bare L1 bound. Proves bounded-slab/full-test Hilbert equivalence by full Schwartz cutoff density; transports the actual maximal nonnegative self-adjoint Hamiltonian, its exact right-derivative domain, the normalized zero-energy vacuum and a -1 resolvent. Attaches this dynamics to the existing actual tuned Wilson candidate while retaining the positive ultraviolet endpoint and all-order bounds as explicit unproved analytic inputs. Direct all-order mean-centered estimates apply to the original Wilson law, including repeated insertions. A rapidly concentrating branch has genuine all-order bounds for all beta above its starting threshold, but every positive-order centered correlation vanishes in the continuum and no positive tuning endpoint survives. The normalized boundary conditional-response dictionary exposes the actual connected fluctuation estimate; it does not supply a uniform ultraviolet positive response. This phase does not establish physical running, curvature-field identification, nontrivial Yang--Mills existence, locality/Poincare covariance, physical short-distance behavior, vacuum uniqueness or a positive mass gap. All twelve full Clay requirements remain open.",
        "yang_mills_requirements_check": json.loads(Path(checks[2]["log"]).read_text()),
        "remaining_unformalized": REMAINING,
    }
    target = ROOT / "data/yang_mills_tempered_dynamics_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print(f"{NEW_COUNT} fresh standard-axiom checks; {len(declarations)} cumulative; "
          f"{len(local_sources)} local Lean sources fingerprinted.")
    print(target)


if __name__ == "__main__":
    main()
