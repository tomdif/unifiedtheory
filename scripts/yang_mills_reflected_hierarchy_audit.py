#!/usr/bin/env python3
"""Incremental reflected-hierarchy bridge audit, retaining 1670 validated checks.

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
from yang_mills_lattice_bridge_audit import TARGETS as PREVIOUS_TARGETS

NEW_TARGETS = ['UnifiedTheory.Clay.YangMills.BoundaryAmplitudeRealization', 'UnifiedTheory.Clay.YangMills.BoundaryPlaquetteOS', 'UnifiedTheory.Clay.YangMills.CellReflectionCovariance', 'UnifiedTheory.Clay.YangMills.ClosedHalfSmearing', 'UnifiedTheory.Clay.YangMills.ExplicitLatticeScales', 'UnifiedTheory.Clay.YangMills.FiniteCellSmearing', 'UnifiedTheory.Clay.YangMills.JointHierarchyCoordinates', 'UnifiedTheory.Clay.YangMills.KernelHilbertRealization', 'UnifiedTheory.Clay.YangMills.PositiveCellSupport', 'UnifiedTheory.Clay.YangMills.ReflectedWilsonKernel', 'UnifiedTheory.Clay.YangMills.WilsonBoundaryHilbert', 'UnifiedTheory.Clay.YangMills.WilsonJointCompactness', 'UnifiedTheory.Clay.YangMills.WilsonJointNontrivial', 'UnifiedTheory.Clay.YangMills.WilsonReflectedJointLimit', 'UnifiedTheory.Clay.YangMills.WilsonSmearedJointLimit', 'UnifiedTheory.Clay.YangMills.WilsonSmearedObservable']
TARGETS = PREVIOUS_TARGETS + NEW_TARGETS
CHECK = "scripts/CheckYangMillsReflectedHierarchy.lean"
PREVIOUS_REPORT = "data/yang_mills_lattice_bridge_audit.json"
NEW_COUNT = 157
PREVIOUS_COUNT = 1670
REMAINING = ['Physical compact simple Lie group/representation choice, renormalized coupling trajectory, curvature observables and mixing, ultraviolet behavior and stress tensor remain open. Explicit mesh->0 and physical-volume->infinity geometric scales are constructed, but are not a Yang--Mills renormalization prescription.', 'Regulator-uniform estimates and a positive fixed Schwartz-smeared connected witness for the renormalized theory remain open. A spatial boundary plaquette now survives the actual reflection null quotient at bounded coupling; that unsmeared boundary witness does not establish nontriviality of the continuum test-generated field space.', 'The full bare hierarchy and selected actual smeared reflected kernels now share one subsequence, with exact vacuum-to-test matrix elements and reflected-pair expectation convergence. Complete reflected tensor/mixed-adjoint hierarchy identities, measure-preserving affine changes of variables, full Schwartz pullbacks and their limiting topology still need proof. The proved cell-reflection offset convergence is pointwise.', 'Actual finite reflected Hilbert completions now embed isometrically into explicit L2 boundary-amplitude spaces, with exact nullspace. Complete OS/local field reconstruction, common field domain, physical covariance, invariant cyclic vacuum uniqueness, time evolution, translation generators and joint forward-cone spectrum remain open.', 'A finite positive physical mass gap for the same reconstructed Yang--Mills Hamiltonian remains open. No one-step positive transfer operator, scaling spectral bound or generator is constructed here. All twelve full-target requirements remain open.', 'The earlier auxiliary Bose spectral bundle and separate S3 matter-coupled/physical-identification program remain distinct; those auxiliary gaps cannot certify this Yang--Mills candidate.']


def main():
    previous = json.loads((ROOT / PREVIOUS_REPORT).read_text())
    prior_names = []
    for ledger in ["scripts/CheckParticleHamiltonians.lean", "scripts/CheckParticleEnergyGap.lean",
                   "scripts/CheckBosonicParticleSectors.lean", "scripts/CheckBosonicEnergyClayFramework.lean", "scripts/CheckYangMillsSwarm.lean",
                   "scripts/CheckYangMillsConstruction.lean",
                   "scripts/CheckYangMillsLatticeBridge.lean"]:
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
        CHECK, "scripts/yang_mills_reflected_hierarchy_audit.py", PREVIOUS_REPORT,
        "data/yang_mills_requirements.json", "scripts/check_yang_mills_requirements.py",
        "UnifiedTheory/Clay/YangMills/README.md",
        "UnifiedTheory.lean", "UnifiedTheory/QSeries/README.md",
    ]))
    hashes = {p: sha256(ROOT / p) for p in sources}
    env = os.environ.copy()
    env.pop("LEAN_PATH", None)
    env["LEAN_NUM_THREADS"] = "2"
    logs = Path(tempfile.mkdtemp(prefix="unifiedtheory-yang-mills-reflected-hierarchy-audit-"))
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
        "verification_mode": "Incremental: 157 freshly checked declarations plus 1670 previous checks retained after verifying their proof-source, audit-script and verification-log hashes, including the full predecessor certificate chain.",
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
        "scope": "Constructs actual continuous cell-smeared Wilson configuration observables, exact expectation-to-hierarchy identities and uniform bounds. Proves physical positive-time slab support implies closed-half support, eventual support in expanding volume and an explicit simultaneous mesh-refinement/infinite-volume geometric sequence. Constructs actual reflected Wilson Gram Hilbert spaces, a non-vacuum boundary plaquette surviving the reflection null quotient at finite cutoff and in bounded-coupling kernel limits, and an explicit isometric L2 boundary-amplitude realization with exact nullspace. Constructs one strict subsequence for the entire bare hierarchy and selected actual smeared reflected-pair expectations, with normalized Hilbert vacuum and exact vacuum-to-test matrix elements equal to hierarchy values. Proves actual cell-sampler reflection almost everywhere, real-word/reflected-smearing integral identities and pointwise disappearance of the spatial reflection offset. This is not full continuum OS reconstruction: renormalized fixed-smeared nontriviality, full tensor/mixed-adjoint hierarchy identities, affine Schwartz pullbacks, physical covariance/time dynamics and a Yang--Mills mass gap remain open.",
        "yang_mills_requirements_check": json.loads(Path(checks[2]["log"]).read_text()),
        "remaining_unformalized": REMAINING,
    }
    target = ROOT / "data/yang_mills_reflected_hierarchy_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print(f"{NEW_COUNT} fresh standard-axiom checks; {len(declarations)} cumulative; "
          f"{len(local_sources)} local Lean sources fingerprinted.")
    print(target)


if __name__ == "__main__":
    main()
