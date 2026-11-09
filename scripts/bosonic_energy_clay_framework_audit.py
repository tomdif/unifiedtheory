#!/usr/bin/env python3
"""Incremental Bose energy / Clay framework audit, retaining 811 validated checks.

Every prior proof source and audit script must have its previously certified
hash. Only the integration root and README may change. The new declarations
are checked afresh after a real dependency build; no dependency overlay is used.
"""
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

from free_balanced_hamiltonian_audit import ROOT, STANDARD_AXIOMS, local_dependencies, sha256
from bosonic_particle_sectors_audit import TARGETS as PREVIOUS_TARGETS

NEW_TARGETS = [
    'UnifiedTheory.Audit.KFCausalDirectSumEnergyForm',
    'UnifiedTheory.Audit.KFCausalDirectSumFormHamiltonian',
    'UnifiedTheory.Audit.KFCausalClosedFormLowerBound',
    'UnifiedTheory.Audit.KFCausalBosonicFullEnergyForm',
    'UnifiedTheory.Audit.KFCausalBosonicSectorLadders',
    'UnifiedTheory.Audit.KFCausalBosonicAnnihilationEnergy',
    'UnifiedTheory.Audit.KFCausalBosonicEnergyFieldHamiltonian',
    'UnifiedTheory.Audit.KFCausalInteractingBosonicEnergyField',
    'UnifiedTheory.Clay.YangMills.LocalFields',
    'UnifiedTheory.Clay.YangMills.SpectralGap',
    'UnifiedTheory.Clay.YangMills.ContinuumControl',
    'UnifiedTheory.Audit.KFCausalBosonicClayGapInterface',
]
TARGETS = PREVIOUS_TARGETS + NEW_TARGETS
CHECK = "scripts/CheckBosonicEnergyClayFramework.lean"
PREVIOUS_REPORT = "data/bosonic_particle_sectors_audit.json"
NEW_COUNT = 125
PREVIOUS_COUNT = 811
REMAINING = [
    'Full-domain identification of all higher Bose-sector Friedrichs operators with labelled tensor restrictions, occupation-space compatibility, and canonical field/CCR compatibility for the new tensor ladder realization.',
    'The full S3 matter-coupled Pauli--Fierz model, its ground-state existence, uniqueness and quantitative excitation gap. Full Bose energy forms, their Hamiltonian identification, gap-based annihilation bounds and a self-adjoint linear field perturbation are now proved; these do not prove a coupled gap.',
    'A common physical spacetime field family with complete distributional, adjoint, covariance, joint-spectrum, locality and cyclicity proofs. The new LocalFields module defines some necessary interfaces but is not a full Wightman specification.',
    'A compact-simple-Lie-group Yang--Mills candidate, renormalized gauge observables, ultraviolet matching, continuum/infinite-volume limits, and a positive finite spectral gap for its actual physical time generator. All twelve target obligations in data/yang_mills_requirements.json remain open.',
    'The stronger bounded-resolvent interval and finite-excitation input for the auxiliary spectral interface, and any identification of that auxiliary model with Yang--Mills.',
    'Physical numerical identifications and the full unified theory. These are not prerequisites for the stated Yang--Mills prize and are not proved by this framework.',
]


def main():
    previous = json.loads((ROOT / PREVIOUS_REPORT).read_text())
    prior_names = []
    for ledger in ["scripts/CheckParticleHamiltonians.lean", "scripts/CheckParticleEnergyGap.lean",
                   "scripts/CheckBosonicParticleSectors.lean"]:
        prior_names += re.findall(r"^#print axioms (\S+)$", (ROOT / ledger).read_text(), re.M)
    if len(prior_names) != PREVIOUS_COUNT or list(previous["audited_declarations"]) != prior_names:
        raise RuntimeError("Previous declaration ledger does not match its certificate")
    permitted_integration_changes = {"UnifiedTheory.lean", "UnifiedTheory/QSeries/README.md"}
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
        discovered += [module + "." + n for n in re.findall(
            r"^(?:@\[[^\]]*\]\s*)?(?:def|abbrev|theorem|instance|structure)\s+(\w+)", source, re.M)]
    if expected != discovered or len(expected) != NEW_COUNT or len(set(expected)) != NEW_COUNT:
        raise RuntimeError("Every new public definition and theorem must be checked")
    local_sources = sorted({p for target in TARGETS for p in local_dependencies(target)})
    sources = sorted(set(local_sources + list(previous["source_sha256"]) + [
        CHECK, "scripts/bosonic_energy_clay_framework_audit.py", PREVIOUS_REPORT,
        "data/yang_mills_requirements.json", "scripts/check_yang_mills_requirements.py",
        "UnifiedTheory/Clay/YangMills/README.md",
        "UnifiedTheory.lean", "UnifiedTheory/QSeries/README.md",
    ]))
    hashes = {p: sha256(ROOT / p) for p in sources}
    env = os.environ.copy()
    env.pop("LEAN_PATH", None)
    env["LEAN_NUM_THREADS"] = "2"
    logs = Path(tempfile.mkdtemp(prefix="unifiedtheory-bosonic-energy-clay-framework-audit-"))
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
        "verification_mode": "Incremental: 125 freshly checked declarations plus 811 previous checks retained after verifying their proof-source, audit-script and verification-log hashes, including the predecessor certificate chain.",
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
        "scope": "Constructs the full closed Bose energy form with exact domain and identifies its represented Hamiltonian with the maximal sector sum. Extends the number-weighted bound to the full form domain. Constructs symmetrized tensor creation and its Hilbert adjoint and proves the gap-based annihilation energy estimate. Uses it to construct a self-adjoint linear field perturbation of the actual Bose energy Hamiltonian, with full variational graph, lower bound and exact zero-coupling recovery. Instantiates these results for the original H(t). Adds initial four-dimensional smeared-field, bounded-resolvent spectral-gap and continuum-control interfaces, including nontriviality and collapsing-gap tests. These are not a complete formal Clay statement or a Yang--Mills construction; the requirements ledger keeps all twelve target obligations open.",
        "yang_mills_requirements_check": json.loads(Path(checks[2]["log"]).read_text()),
        "remaining_unformalized": REMAINING,
    }
    target = ROOT / "data/bosonic_energy_clay_framework_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print(f"{NEW_COUNT} fresh standard-axiom checks; {len(declarations)} cumulative; "
          f"{len(local_sources)} local Lean sources fingerprinted.")
    print(target)


if __name__ == "__main__":
    main()
