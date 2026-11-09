#!/usr/bin/env python3
"""Incremental Bose-sector audit, retaining the source-validated 701 checks.

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
from particle_energy_gap_audit import TARGETS as PREVIOUS_TARGETS

NEW_TARGETS = [
    'UnifiedTheory.Audit.KFCausalParticlePureTensors',
    'UnifiedTheory.Audit.KFCausalParticlePermutations',
    'UnifiedTheory.Audit.KFCausalBosonicSectorProjection',
    'UnifiedTheory.Audit.KFCausalParticleDomainTensors',
    'UnifiedTheory.Audit.KFCausalParticleCoreCovariance',
    'UnifiedTheory.Audit.KFCausalBosonicSectorHamiltonian',
    'UnifiedTheory.Audit.KFCausalBosonicSectorOneParticle',
    'UnifiedTheory.Audit.KFCausalBosonicFock',
    'UnifiedTheory.Audit.KFCausalBosonicEnergyGap',
    'UnifiedTheory.Audit.KFCausalInteractingBosonicHamiltonian',
]
TARGETS = PREVIOUS_TARGETS + NEW_TARGETS
CHECK = "scripts/CheckBosonicParticleSectors.lean"
PREVIOUS_REPORT = "data/particle_energy_gap_audit.json"
NEW_COUNT = 110
PREVIOUS_COUNT = 701
REMAINING = [
    'Full-domain identification of the new all-particle Bose Friedrichs operators with the corresponding labelled tensor restrictions beyond one particle, and compatibility with the earlier occupation-space realization. Completed permutation representations, averaging projections, self-adjoint Bose-sector operators, their actual symmetrized tensor-domain action, and exact one-particle recovery are now proved. The earlier separate two-boson restriction theorem remains valid.',
    'The full closed direct-sum bosonic energy form domain and energy-weighted annihilation estimate for the actual H(t). Every Bose sector now has the n*epsilon/2 floor; its uncoupled direct sum has the number-weighted operator-domain bound, one-dimensional zero-energy kernel, and epsilon/2 vacuum-relative energy gap.',
    "The completed S3 Pauli--Fierz interaction using these Bose energy sectors, and the coupled model's ground-state existence, uniqueness and quantitative small-coupling gap. The uncoupled gap does not prove a coupled gap.",
    'A common full-Hilbert-space smeared field family, invariant domains, Wick/Wightman correlations, and vacuum cyclicity.',
    'Lorentz boost covariance, test-map translation covariance under the precise Fourier convention, Klein--Gordon causal commutator support, and spacelike locality.',
    'A local interacting gauge-field model, continuum limit, physical particle identifications, and any Clay mass-gap theorem. Tensor copies of the interacting one-particle H(t) do not introduce interparticle interactions.',
]


def main():
    previous = json.loads((ROOT / PREVIOUS_REPORT).read_text())
    prior_names = []
    for ledger in ["scripts/CheckParticleHamiltonians.lean", "scripts/CheckParticleEnergyGap.lean"]:
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
            r"^(?:@\[[^\]]*\]\s*)?(?:def|abbrev|theorem|instance)\s+(\w+)", source, re.M)]
    if expected != discovered or len(expected) != NEW_COUNT or len(set(expected)) != NEW_COUNT:
        raise RuntimeError("Every new public definition and theorem must be checked")
    local_sources = sorted({p for target in TARGETS for p in local_dependencies(target)})
    sources = sorted(set(local_sources + list(previous["source_sha256"]) + [
        CHECK, "scripts/bosonic_particle_sectors_audit.py", PREVIOUS_REPORT,
        "UnifiedTheory.lean", "UnifiedTheory/QSeries/README.md",
    ]))
    hashes = {p: sha256(ROOT / p) for p in sources}
    env = os.environ.copy()
    env.pop("LEAN_PATH", None)
    env["LEAN_NUM_THREADS"] = "2"
    logs = Path(tempfile.mkdtemp(prefix="unifiedtheory-bosonic-particle-sectors-audit-"))
    checks = []
    for i, command in enumerate([
        ["lake", "--rehash", "build", *TARGETS],
        ["lake", "env", "lean", CHECK],
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
        "verification_mode": "Incremental: 110 freshly checked declarations plus 701 previous checks retained after verifying their proof-source, audit-script and verification-log hashes, including the predecessor certificate chain.",
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
        "scope": "Constructs completed unitary permutation actions for every finite tensor sector, proves their group law, and constructs the closed invariant spaces and normalized averaging projections. Proves permutation covariance of the actual iterated Hamiltonian sum on the Hilbert-dense tensor domain. Closes its symmetrized energy form to obtain positive self-adjoint Bose-sector operators, with exact variational domains and n*epsilon/2 lower bounds. Their maximal Hilbert direct sum has an exact operator domain, normalized stationary vacuum, number-weighted energy bound, one-dimensional zero-energy kernel and epsilon/2 energy gap on the vacuum orthogonal complement. Proves full graph/domain recovery of the original H(t) in the one-particle Bose sector. No energy eigenbasis, added interparticle interaction, full higher-sector restriction identification, coupled Pauli--Fierz gap, or local relativistic field theory is asserted.",
        "remaining_unformalized": REMAINING,
    }
    target = ROOT / "data/bosonic_particle_sectors_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print(f"{NEW_COUNT} fresh standard-axiom checks; {len(declarations)} cumulative; "
          f"{len(local_sources)} local Lean sources fingerprinted.")
    print(target)


if __name__ == "__main__":
    main()
