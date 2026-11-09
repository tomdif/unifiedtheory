#!/usr/bin/env python3
"""Incremental Schwinger-function bridge audit, retaining 1827 validated checks.

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
from yang_mills_reflected_hierarchy_audit import TARGETS as PREVIOUS_TARGETS

NEW_TARGETS = ['UnifiedTheory.Clay.YangMills.AffineCellReflection', 'UnifiedTheory.Clay.YangMills.BareSchwingerCandidate', 'UnifiedTheory.Clay.YangMills.CellTranslationCovariance', 'UnifiedTheory.Clay.YangMills.ContinuumTimeTranslation', 'UnifiedTheory.Clay.YangMills.MovingTestLimit', 'UnifiedTheory.Clay.YangMills.PeriodicTimeTranslation', 'UnifiedTheory.Clay.YangMills.SchwartzConfigurationConjugation', 'UnifiedTheory.Clay.YangMills.SchwartzConfigurationTensor', 'UnifiedTheory.Clay.YangMills.SchwartzProductTensor', 'UnifiedTheory.Clay.YangMills.SchwartzTranslations', 'UnifiedTheory.Clay.YangMills.WilsonHierarchyReflectionPositivity', 'UnifiedTheory.Clay.YangMills.WilsonReflectedTensor', 'UnifiedTheory.Clay.YangMills.WilsonTensorProduct', 'UnifiedTheory.Clay.YangMills.WilsonTranslationUnitary', 'UnifiedTheory.Clay.YangMills.ZeroCouplingOSCollapse']
TARGETS = PREVIOUS_TARGETS + NEW_TARGETS
CHECK = "scripts/CheckYangMillsSchwingerBridge.lean"
PREVIOUS_REPORT = "data/yang_mills_reflected_hierarchy_audit.json"
NEW_COUNT = 143
PREVIOUS_COUNT = 1827
REMAINING = ['Choose and justify the physical compact simple Lie-group representation, renormalized coupling trajectory, curvature observables and mixing, ultraviolet behavior and stress tensor. Explicit mesh->0 and physical-volume->infinity scales are geometric data, not a Yang--Mills renormalization prescription.', 'Prove renormalized regulator-uniform estimates and a positive fixed Schwartz-smeared connected witness in the reflected continuum space. Bounded-coupling unsmeared boundary nontriviality does not provide this. At zero coupling, centered boundary-independent half-coordinate observables are proved reflection-null despite positive ordinary variance for supplied nonconstant observables; no gauge-invariance hypothesis is imposed on that witness.', 'The fixed-plane scalar real-character sector now has exact tensor and conjugate-reflected product hierarchy identities, measure-preserving affine reflections, full Schwartz pullbacks, moving-test convergence and finite mixed-order complex Gram reflection positivity. Extend bounded-positive-time/eventually closed-half-supported tests to arbitrary positive-time support by density, and extend the scalar sector to required renormalized field multiplets.', 'Actual lattice shifts induce ordinary Wilson-L2 cyclic unitaries and exact translated smeared states. Every real-valued Euclidean time translation preserves weak bare hierarchy limits as spacing vanishes. Full Euclidean covariance, OS/local field reconstruction, common field domains, invariant cyclic vacuum uniqueness and physical Poincare covariance remain open.', 'Construct OS time dynamics, a continuous contraction semigroup, its self-adjoint physical generator and joint forward-cone spectrum, then prove a finite positive mass gap for that same nontrivial renormalized Yang--Mills candidate. Ordinary L2 unitaries are not OS dynamics. All twelve full-target requirements remain open.', 'The earlier auxiliary Bose spectral bundle and separate S3 matter-coupled/physical-identification program remain distinct; their auxiliary gaps cannot certify this Yang--Mills candidate.']


def main():
    previous = json.loads((ROOT / PREVIOUS_REPORT).read_text())
    prior_names = []
    for ledger in ["scripts/CheckParticleHamiltonians.lean", "scripts/CheckParticleEnergyGap.lean",
                   "scripts/CheckBosonicParticleSectors.lean", "scripts/CheckBosonicEnergyClayFramework.lean", "scripts/CheckYangMillsSwarm.lean",
                   "scripts/CheckYangMillsConstruction.lean",
                   "scripts/CheckYangMillsLatticeBridge.lean",
                   "scripts/CheckYangMillsReflectedHierarchy.lean"]:
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
        CHECK, "scripts/yang_mills_schwinger_bridge_audit.py", PREVIOUS_REPORT,
        "data/yang_mills_requirements.json", "scripts/check_yang_mills_requirements.py",
        "UnifiedTheory/Clay/YangMills/README.md",
        "UnifiedTheory.lean", "UnifiedTheory/QSeries/README.md",
    ]))
    hashes = {p: sha256(ROOT / p) for p in sources}
    env = os.environ.copy()
    env.pop("LEAN_PATH", None)
    env["LEAN_NUM_THREADS"] = "2"
    logs = Path(tempfile.mkdtemp(prefix="unifiedtheory-yang-mills-schwinger-bridge-audit-"))
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
        "verification_mode": "Incremental: 143 freshly checked declarations plus 1827 previous checks retained after verifying their proof-source, audit-script and verification-log hashes, including the full predecessor certificate chain.",
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
        "scope": "Constructs exact Schwartz tensor products, configuration-volume factorization and actual Wilson smeared-product hierarchy identities. Constructs the measure-preserving affine cell-reflection pullback and proves convergence in full Schwartz topology. Identifies every scalar real-character reflected smeared pair with a conjugate-reflected tensor evaluation of the same limiting bare hierarchy, and proves full finite mixed-order complex Gram reflection positivity for eventually closed-half-supported tests. Proves exact finite Wilson-law translation symmetry, ordinary Wilson-L2 cyclic unitaries and their smeared-test action, then derives all real-valued Euclidean time translations as symmetries of actual weak bare hierarchy limits. On explicit refining and expanding lattices one common normalized bounded bare hierarchy has both time-translation invariance and finite-polynomial reflection positivity for fixed bounded positive-time slabs. Proves zero-coupling centered boundary-independent half-observables are reflected-null, with positive ordinary variance conditional on nonconstancy. This does not construct a nontrivial renormalized Yang--Mills field theory, unrestricted OS reconstruction, a physical Hamiltonian or a mass gap.",
        "yang_mills_requirements_check": json.loads(Path(checks[2]["log"]).read_text()),
        "remaining_unformalized": REMAINING,
    }
    target = ROOT / "data/yang_mills_schwinger_bridge_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print(f"{NEW_COUNT} fresh standard-axiom checks; {len(declarations)} cumulative; "
          f"{len(local_sources)} local Lean sources fingerprinted.")
    print(target)


if __name__ == "__main__":
    main()
