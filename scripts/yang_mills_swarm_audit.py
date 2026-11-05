#!/usr/bin/env python3
"""Incremental parallel Clay-framework audit, retaining 936 validated checks.

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
from bosonic_energy_clay_framework_audit import TARGETS as PREVIOUS_TARGETS

NEW_TARGETS = ['UnifiedTheory.Audit.KFCausalPositiveFormResolvent', 'UnifiedTheory.Audit.KFCausalBoundedDirectSumMap', 'UnifiedTheory.Audit.KFCausalBosonicIntervalResolvent', 'UnifiedTheory.Audit.KFCausalPositiveFormSpectralPoint', 'UnifiedTheory.Audit.KFCausalBosonicFiniteExcitation', 'UnifiedTheory.Clay.YangMills.FieldAdjoints', 'UnifiedTheory.Clay.YangMills.FieldCorrelations', 'UnifiedTheory.Clay.YangMills.PoincareKinematics', 'UnifiedTheory.Clay.YangMills.PoincareTestAction', 'UnifiedTheory.Clay.YangMills.PoincareTopology', 'UnifiedTheory.Clay.YangMills.PoincareCovariance', 'UnifiedTheory.Clay.YangMills.RegulatedGauge', 'UnifiedTheory.Clay.YangMills.RegulatedGaugeMeasure', 'UnifiedTheory.Clay.YangMills.RegulatedGaugeOrientation', 'UnifiedTheory.Clay.YangMills.PeriodicLattice4']
TARGETS = PREVIOUS_TARGETS + NEW_TARGETS
CHECK = "scripts/CheckYangMillsSwarm.lean"
PREVIOUS_REPORT = "data/bosonic_energy_clay_framework_audit.json"
NEW_COUNT = 230
PREVIOUS_COUNT = 936
REMAINING = ['Full-domain identification of all higher Bose-sector Friedrichs operators with labelled tensor restrictions, occupation-space compatibility, and canonical field/CCR compatibility for the tensor ladder realization.', 'The full S3 matter-coupled Pauli--Fierz model and the ground state and excitation gap of coupled models. The new resolvent and finite-excitation theorems concern the uncoupled auxiliary Bose particle sum.', 'A physical strongly continuous Poincare representation compatible with the same field system, its generators and joint forward-cone spectrum. Group-parameter continuity in Schwartz topology and tensor observable covariance remain open.', 'A complete distributional field hierarchy and reconstruction. Gram positivity, adjoint/Hermiticity, local exchange and scalar covariance of vacuum words are proved conditionally on the corresponding field-system hypotheses.', 'Finite Wilson laws now exist on periodic four-dimensional lattices. Reflection positivity, observable renormalization, scaling prescriptions, regulator-uniform estimates, nontrivial continuum/infinite-volume limits and ultraviolet Yang--Mills behavior remain open.', 'Identification of a constructed continuum Yang--Mills Hamiltonian with physical time translations and proof of its positive finite spectral gap. All twelve full-target obligations remain open; the auxiliary spectral result does not supply this identification.', 'Physical numerical identifications and the full unified theory. These are not prerequisites for the stated Yang--Mills prize and remain unproved.']


def main():
    previous = json.loads((ROOT / PREVIOUS_REPORT).read_text())
    prior_names = []
    for ledger in ["scripts/CheckParticleHamiltonians.lean", "scripts/CheckParticleEnergyGap.lean",
                   "scripts/CheckBosonicParticleSectors.lean", "scripts/CheckBosonicEnergyClayFramework.lean"]:
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
        CHECK, "scripts/yang_mills_swarm_audit.py", PREVIOUS_REPORT,
        "data/yang_mills_requirements.json", "scripts/check_yang_mills_requirements.py",
        "UnifiedTheory/Clay/YangMills/README.md",
        "UnifiedTheory.lean", "UnifiedTheory/QSeries/README.md",
    ]))
    hashes = {p: sha256(ROOT / p) for p in sources}
    env = os.environ.copy()
    env.pop("LEAN_PATH", None)
    env["LEAN_NUM_THREADS"] = "2"
    logs = Path(tempfile.mkdtemp(prefix="unifiedtheory-yang-mills-swarm-audit-"))
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
        "verification_mode": "Incremental: 230 freshly checked declarations plus 936 previous checks retained after verifying their proof-source, audit-script and verification-log hashes, including the predecessor certificate chain.",
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
        "scope": "Closes the bounded-resolvent interval and finite-positive-excitation inputs for the actual auxiliary Bose direct-sum Hamiltonian, without assuming an eigenbasis. Constructs the affine Minkowski isometry group, proper orthochronous subgroup, coefficient topology, continuous Schwartz pullbacks and support transport; physical unitary covariance remains an explicit hypothesis. Proves conditional adjoint, Gram positivity, Hermiticity, local exchange and scalar covariance for vacuum-word correlations. Constructs compact-group normalized Haar link laws and gauge-invariant Wilson probability measures on explicit periodic four-dimensional lattices with inverse backward links. This is finite-regulator and auxiliary analytic progress, not a continuum Yang--Mills construction or a complete Clay axiom formalization.",
        "yang_mills_requirements_check": json.loads(Path(checks[2]["log"]).read_text()),
        "remaining_unformalized": REMAINING,
    }
    target = ROOT / "data/yang_mills_swarm_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print(f"{NEW_COUNT} fresh standard-axiom checks; {len(declarations)} cumulative; "
          f"{len(local_sources)} local Lean sources fingerprinted.")
    print(target)


if __name__ == "__main__":
    main()
