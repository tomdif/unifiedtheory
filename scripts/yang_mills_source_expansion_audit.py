#!/usr/bin/env python3
"""Incremental scalar source-expansion audit, retaining 3260 validated checks.

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
from yang_mills_separated_source_audit import TARGETS as PREVIOUS_TARGETS

NEW_TARGETS = ['UnifiedTheory.Clay.YangMills.GibbsReflectionResponse', 'UnifiedTheory.Clay.YangMills.WilsonBlockReflection', 'UnifiedTheory.Clay.YangMills.SqrtSourceRemainder', 'UnifiedTheory.Clay.YangMills.SU2SourceCoefficients', 'UnifiedTheory.Clay.YangMills.SU2SourceQuotient', 'UnifiedTheory.Clay.YangMills.FiniteSourceConvolution', 'UnifiedTheory.Clay.YangMills.OptimalSourceTruncation', 'UnifiedTheory.Clay.YangMills.SU2QuotientRemainder', 'UnifiedTheory.Clay.YangMills.HybridSourceApproximation', 'UnifiedTheory.Clay.YangMills.WilsonHybridSource', 'UnifiedTheory.Clay.YangMills.SU2QuaternionCoordinates', 'UnifiedTheory.Clay.YangMills.SU2ScalarTilt', 'UnifiedTheory.Clay.YangMills.SU2QuaternionEquivalence']
TARGETS = PREVIOUS_TARGETS + NEW_TARGETS
CHECK = "scripts/CheckYangMillsSourceExpansion.lean"
PREVIOUS_REPORT = "data/yang_mills_separated_source_audit.json"
NEW_COUNT = 272
PREVIOUS_COUNT = 3260
REMAINING = ['Prove the normalized first-coordinate slicing formula for unit-quaternion Haar measure; group equivalence and Haar transport do not by themselves establish the semicircle density.', 'Construct the actual six-staple action and weighted source dictionary on a nondegenerate lattice (n>=2), including rotational conditional means and the zero-staple extension. This is needed to instantiate the hybrid good-region hypothesis using the proved scalar remainder.', 'Complete the full checkerboard and fixed physical support-margin binding to the positive-half OS domain. The actual stable-block reflection and temporal-line results do not supply that entire geometry.', 'Control the exact retained small-staple contribution, generated interactions and new approximation errors through repeated integration; obtain bounded and strictly positive renormalized reflected norms on one physically identified trajectory.', 'Construct compatible all-order contact renormalization and distributional bounds, infinite-volume fields, covariance and spectrum, vacuum uniqueness and positive mass gap. All twelve full Clay requirements remain open.', 'The separate chessboard bad-event aggregation and actual smooth-smear ordinary variance lower bound remain natural-math derivations, not part of this new Lean count. Exact beta=b*t rescaling is proved; general beta/log(1/a) convergence and physical trajectory identification are not.']


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
                   "scripts/CheckYangMillsSeparatedSources.lean"]:
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
        raise RuntimeError("Post-3260 Yang--Mills source inventory does not match NEW_TARGETS")
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
        CHECK, "scripts/yang_mills_source_expansion_audit.py", PREVIOUS_REPORT,
        "data/yang_mills_requirements.json", "scripts/check_yang_mills_requirements.py",
        "UnifiedTheory/Clay/YangMills/README.md",
        "UnifiedTheory.lean", "UnifiedTheory/QSeries/README.md",
    ]))
    hashes = {p: sha256(ROOT / p) for p in sources}
    env = os.environ.copy()
    env.pop("LEAN_PATH", None)
    env["LEAN_NUM_THREADS"] = "2"
    logs = Path(tempfile.mkdtemp(prefix="unifiedtheory-yang-mills-source-expansion-audit-"))
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
        "scope": "Post-3260 scalar source expansion and concrete finite-cutoff geometric bridges. Proves the explicit square-root coefficient remainder, evaluated Euler Gamma moments and denominator bound, factorial source-coefficient growth and exact Gamma quotient identification, finite shifted cancellation, actual scalar quotient remainder and uniform optimal exponential estimate. Proves the actual one-dimensional semicircle-to-Gamma substitution for positive tilt and its separate zero endpoint. Constructs explicit quaternion/SU(2) matrix coordinates, a continuous multiplicative equivalence and bidirectional transport of normalized compact Haar. Constructs actual selected/retained Wilson reflections and Haar preservation for stable blocks, response equivariance and zero removed reflected pairing using geometric independence and reflected source separation; a nonempty temporal line has cardinality, stability, independence and time-support separation proved. Constructs continuous hybrid errors, exact logarithmic rescaling decay, and actual first/second Wilson marginal mean-square transport, with the actual good-region approximation input still explicit. The sphere first-coordinate Haar density and nondegenerate six-staple/weighted source dictionary are not proved, so the scalar estimate is not yet identified with the actual Wilson conditional source. No full checkerboard/fixed-support OS binding, positive retained correlation, physical trajectory, continuum candidate or mass gap is claimed.",
        "yang_mills_requirements_check": json.loads(Path(checks[2]["log"]).read_text()),
        "remaining_unformalized": REMAINING,
    }
    target = ROOT / "data/yang_mills_source_expansion_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print(f"{NEW_COUNT} fresh standard-axiom checks; {len(declarations)} cumulative; "
          f"{len(local_sources)} local Lean sources fingerprinted.")
    print(target)


if __name__ == "__main__":
    main()
