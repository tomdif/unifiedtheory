#!/usr/bin/env python3
"""Incremental Yang--Mills construction audit, retaining 1166 validated checks.

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
from yang_mills_swarm_audit import TARGETS as PREVIOUS_TARGETS

NEW_TARGETS = ['UnifiedTheory.Clay.YangMills.WilsonMomentBounds', 'UnifiedTheory.Clay.YangMills.GibbsFullSupport', 'UnifiedTheory.Clay.YangMills.PeriodicPlaquetteNontriviality', 'UnifiedTheory.Clay.YangMills.WilsonCrossingKernel', 'UnifiedTheory.Clay.YangMills.UnitaryCharacterObservables', 'UnifiedTheory.Clay.YangMills.WilsonReflectionForm', 'UnifiedTheory.Clay.YangMills.WilsonSplitMeasure', 'UnifiedTheory.Clay.YangMills.CountableCorrelationCompactness', 'UnifiedTheory.Clay.YangMills.SeminormWeakCompactness', 'UnifiedTheory.Clay.YangMills.HierarchyCompactness', 'UnifiedTheory.Clay.YangMills.WilsonMomentCompactness', 'UnifiedTheory.Clay.YangMills.ProbabilityGramCompactness', 'UnifiedTheory.Clay.YangMills.WilsonGramCompactness', 'UnifiedTheory.Clay.YangMills.SchwartzTranslationContinuity', 'UnifiedTheory.Clay.YangMills.SchwartzTranslationJoint', 'UnifiedTheory.Clay.YangMills.SchwartzLinearContinuity', 'UnifiedTheory.Clay.YangMills.PoincareStrongTestContinuity']
TARGETS = PREVIOUS_TARGETS + NEW_TARGETS
CHECK = "scripts/CheckYangMillsConstruction.lean"
PREVIOUS_REPORT = "data/yang_mills_swarm_audit.json"
NEW_COUNT = 184
PREVIOUS_COUNT = 1166
REMAINING = ['Actual reflected-edge, Haar-half/boundary and plaquette-action identification connecting PeriodicLattice4.wilsonLaw with the proved reflection-positive split measure. Reflection-positive split measures and unitary crossing kernels are constructed; full periodic-lattice reflection positivity is not yet proved.', 'Physical scaling and renormalized local gauge observables, including a Wilson-to-Schwartz hierarchy identification and regulator-uniform continuous seminorm bounds at every order. Bare Wilson moment bounds and common positive normalized subsequential Gram limits are proved; they do not supply these renormalized bounds.', 'Continuum nontriviality: identify a connected or centered correlation and prove a positive regulator-uniform lower bound. Strict finite-lattice plaquette variance is proved but may vanish in a limit. A nonzero selected hierarchy coordinate can be the normalization coordinate and does not suffice.', 'Complete OS reconstruction or direct Wightman construction, physical strongly continuous unitary representation, tensor covariance, translation generators and joint forward-cone spectrum for the same Yang--Mills candidate. Strong continuity of the genuine Poincare action on Schwartz tests is now proved.', 'Yang--Mills ultraviolet behavior, stress tensor and required operator-product behavior; finite physical spectral-gap estimates and identification of the reconstructed Hamiltonian. All twelve full-target requirements remain open.', 'Higher Bose-sector domain identifications and CCR compatibility, full S3 matter-coupled Pauli--Fierz construction, coupled ground-state and gap results, and proposed numerical physical identifications remain separate open work. The earlier auxiliary Bose spectral bundle is proved but not identified with Yang--Mills.']


def main():
    previous = json.loads((ROOT / PREVIOUS_REPORT).read_text())
    prior_names = []
    for ledger in ["scripts/CheckParticleHamiltonians.lean", "scripts/CheckParticleEnergyGap.lean",
                   "scripts/CheckBosonicParticleSectors.lean", "scripts/CheckBosonicEnergyClayFramework.lean", "scripts/CheckYangMillsSwarm.lean"]:
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
        CHECK, "scripts/yang_mills_construction_audit.py", PREVIOUS_REPORT,
        "data/yang_mills_requirements.json", "scripts/check_yang_mills_requirements.py",
        "UnifiedTheory/Clay/YangMills/README.md",
        "UnifiedTheory.lean", "UnifiedTheory/QSeries/README.md",
    ]))
    hashes = {p: sha256(ROOT / p) for p in sources}
    env = os.environ.copy()
    env.pop("LEAN_PATH", None)
    env["LEAN_NUM_THREADS"] = "2"
    logs = Path(tempfile.mkdtemp(prefix="unifiedtheory-yang-mills-construction-audit-"))
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
        "verification_mode": "Incremental: 184 freshly checked declarations plus 1166 previous checks retained after verifying their proof-source, audit-script and verification-log hashes, including the predecessor certificate chain.",
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
        "scope": "Proves regulator-independent bare Wilson moment bounds, explicit unitary-dimension bounds, equality of finite Gibbs/Haar null sets, actual plaquette holonomy surjectivity and strict finite-lattice variance for nonconstant characters. Constructs common subsequential limits and positive normalized Gram kernels from actual bare Wilson observables. Constructs a full continuous complex-linear Schwartz hierarchy subsequence conditional on uniform continuous seminorm bounds and countable dense tests, preserving supplied positivity/normalization and selected nonzero coordinates. Proves positive definiteness and integral reflection positivity for unitary-character crossing weights, and constructs a normalized swap-reflection-positive product-half Gibbs law. Proves unconditional strong continuity of genuine full Poincare pullbacks in Schwartz topology. The full periodic-lattice reflection factorization, renormalized continuum estimates, surviving connected witness, reconstruction, ultraviolet behavior and physical Yang--Mills spectral gap remain open.",
        "yang_mills_requirements_check": json.loads(Path(checks[2]["log"]).read_text()),
        "remaining_unformalized": REMAINING,
    }
    target = ROOT / "data/yang_mills_construction_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print(f"{NEW_COUNT} fresh standard-axiom checks; {len(declarations)} cumulative; "
          f"{len(local_sources)} local Lean sources fingerprinted.")
    print(target)


if __name__ == "__main__":
    main()
