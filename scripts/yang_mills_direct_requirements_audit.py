#!/usr/bin/env python3
"""Incremental direct Clay-requirement attack audit, retaining 1970 validated checks.

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
from yang_mills_schwinger_bridge_audit import TARGETS as PREVIOUS_TARGETS

NEW_TARGETS = ['UnifiedTheory.Clay.YangMills.AffineWilsonSmearing', 'UnifiedTheory.Clay.YangMills.BareDefectHierarchy', 'UnifiedTheory.Clay.YangMills.CellSpacetimeTranslation', 'UnifiedTheory.Clay.YangMills.ContinuumSpacetimeTranslation', 'UnifiedTheory.Clay.YangMills.EuclideanTranslationCandidate', 'UnifiedTheory.Clay.YangMills.GibbsLowEnergyConcentration', 'UnifiedTheory.Clay.YangMills.InteriorCellSupport', 'UnifiedTheory.Clay.YangMills.OSBoundedOrbitContraction', 'UnifiedTheory.Clay.YangMills.OSFactorizedCollapse', 'UnifiedTheory.Clay.YangMills.OSInjectiveEvolution', 'UnifiedTheory.Clay.YangMills.OSKernelShift', 'UnifiedTheory.Clay.YangMills.OSPositiveTimeKernel', 'UnifiedTheory.Clay.YangMills.OSScalarDynamics', 'UnifiedTheory.Clay.YangMills.OSStrongContinuity', 'UnifiedTheory.Clay.YangMills.OSTestTranslation', 'UnifiedTheory.Clay.YangMills.OSWeakCouplingCollapse', 'UnifiedTheory.Clay.YangMills.PeriodicSpacetimeTranslation', 'UnifiedTheory.Clay.YangMills.ReflectedWilsonRenormalization', 'UnifiedTheory.Clay.YangMills.TranslationOSCandidate', 'UnifiedTheory.Clay.YangMills.UnitaryHolonomyDefect', 'UnifiedTheory.Clay.YangMills.WilsonAverageDefect', 'UnifiedTheory.Clay.YangMills.WilsonIdentityNeighborhood', 'UnifiedTheory.Clay.YangMills.WilsonWeakCouplingDefect', 'UnifiedTheory.Clay.YangMills.ZeroCouplingFactorization', 'UnifiedTheory.Clay.YangMills.ZeroCouplingSchwingerCollapse']
TARGETS = PREVIOUS_TARGETS + NEW_TARGETS
CHECK = "scripts/CheckYangMillsDirectRequirements.lean"
PREVIOUS_REPORT = "data/yang_mills_schwinger_bridge_audit.json"
NEW_COUNT = 217
PREVIOUS_COUNT = 1970
REMAINING = ['Construct and justify the physical compact simple Lie-group/representation setting, renormalized curvature field multiplets, physical coupling/scale prescription, operator mixing and required ultraviolet stress-tensor/operator-product behavior. The exact unitary holonomy defect is not yet a continuum curvature identification.', 'The current unscaled real unitary-character hierarchy is proved to collapse to the constant dimension hierarchy as beta tends to infinity for arbitrary periods/spacings; its actual OS Hilbert space is one vacuum line and evolution is identity. At beta=0 fixed strict-interior slab connected reflected forms vanish. Construct a nonzero centered/rescaled fixed-Schwartz witness in a renormalized hierarchy. The proposed a^-4 rescaling requires bare connected O(a^8) decay for bounded forms; the necessary spacing-dependent rate and nonzero rescaled limit remain unproved.', 'Extend bounded positive-time slab reflection positivity to unrestricted positive-time support, prove full rotation and field-multiplet covariance, construct local quantum fields on a common invariant domain and complete the required reconstruction/axiom system.', 'Actual all-four Euclidean hierarchy translations and a strongly continuous positive self-adjoint injective contraction semigroup on the bare scalar reflected Hilbert space are proved. A densely defined unbounded Hamiltonian H, its domain, T(t)=exp(-tH), spatial generators, physical Poincare representation, vacuum uniqueness in a nontrivial theory and joint forward-cone spectrum remain unconstructed.', 'Prove a finite positive physical mass gap and finite positive excitation scale for the same nontrivial renormalized Yang--Mills candidate. Bounded self-adjointness and injectivity of T(t) supply neither a bounded inverse nor a spectral gap, and the collapsed vacuum-only bare sector cannot satisfy the full target. All twelve full-target requirements remain open.', 'The earlier auxiliary Bose spectral bundle and separate S3 matter-coupled/physical-identification program remain distinct; their auxiliary spectral gaps cannot certify this Yang--Mills construction.']


def main():
    previous = json.loads((ROOT / PREVIOUS_REPORT).read_text())
    prior_names = []
    for ledger in ["scripts/CheckParticleHamiltonians.lean", "scripts/CheckParticleEnergyGap.lean",
                   "scripts/CheckBosonicParticleSectors.lean", "scripts/CheckBosonicEnergyClayFramework.lean", "scripts/CheckYangMillsSwarm.lean",
                   "scripts/CheckYangMillsConstruction.lean",
                   "scripts/CheckYangMillsLatticeBridge.lean",
                   "scripts/CheckYangMillsReflectedHierarchy.lean",
                   "scripts/CheckYangMillsSchwingerBridge.lean"]:
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
        CHECK, "scripts/yang_mills_direct_requirements_audit.py", PREVIOUS_REPORT,
        "data/yang_mills_requirements.json", "scripts/check_yang_mills_requirements.py",
        "UnifiedTheory/Clay/YangMills/README.md",
        "UnifiedTheory.lean", "UnifiedTheory/QSeries/README.md",
    ]))
    hashes = {p: sha256(ROOT / p) for p in sources}
    env = os.environ.copy()
    env.pop("LEAN_PATH", None)
    env["LEAN_NUM_THREADS"] = "2"
    logs = Path(tempfile.mkdtemp(prefix="unifiedtheory-yang-mills-direct-requirements-audit-"))
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
        "verification_mode": "Incremental: 217 freshly checked declarations plus 1970 previous checks retained after verifying their proof-source, audit-script and verification-log hashes, including the full predecessor certificate chain.",
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
        "scope": "Direct partial attacks on YM02/03/05/06/09/10/12. Constructs actual all-four lattice and continuum Euclidean translation identities and combines them with one bare scalar Wilson hierarchy and its OS time dynamics. Derives contraction and null-space descent from the reflected kernel, then constructs a strongly continuous positive self-adjoint contraction semigroup on the actual Hilbert quotient/completion, with finite-time injectivity. Proves exact connected reflected collapse of actual fixed strict-positive-time slab smearings at zero Wilson-action coefficient. Constructs actual unitary holonomy defects, a common low-energy product-Haar event of mass q^(4V), and volume-independent normalized Gibbs concentration; derives vanishing defect for arbitrary-period beta-to-infinity trajectories. Proves all unscaled real-character fixed-Schwartz correlations tend to d^m times the test integral for arbitrary spacings/periods. Identifies the resulting actual completed OS space with one normalized vacuum line and its evolution with identity. Proves exact affine smearing and connected reflected rescaling, including the necessary bare O(a^8) bound for bounded proposed a^-4-rescaled forms. Does not construct a nontrivial renormalized Yang--Mills field, full covariance/reconstruction, an unbounded physical generator or mass gap.",
        "yang_mills_requirements_check": json.loads(Path(checks[2]["log"]).read_text()),
        "remaining_unformalized": REMAINING,
    }
    target = ROOT / "data/yang_mills_direct_requirements_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print(f"{NEW_COUNT} fresh standard-axiom checks; {len(declarations)} cumulative; "
          f"{len(local_sources)} local Lean sources fingerprinted.")
    print(target)


if __name__ == "__main__":
    main()
