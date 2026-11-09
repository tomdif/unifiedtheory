#!/usr/bin/env python3
"""Build and audit the completed tensor-particle Hamiltonian construction.

Retains the complete preceding 528-declaration audit. Records remaining
model-construction obligations explicitly; this is not a full-root build.
"""
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

from free_balanced_hamiltonian_audit import ROOT, STANDARD_AXIOMS, local_dependencies, sha256
from field_dynamics_audit import TARGETS as PREVIOUS_TARGETS

NEW_TARGETS = [
    "UnifiedTheory.Audit.KFCausalEnergyCoreClosure",
    "UnifiedTheory.Audit.KFCausalCompletedTensor",
    "UnifiedTheory.Audit.KFCausalTensorSumHamiltonian",
    "UnifiedTheory.Audit.KFCausalTwoBosonHamiltonian",
    "UnifiedTheory.Audit.KFCausalHilbertDirectSumHamiltonian",
    "UnifiedTheory.Audit.KFCausalTensorParticleSectors",
    "UnifiedTheory.Audit.KFCausalInteractingParticleHamiltonians",
]
TARGETS = PREVIOUS_TARGETS + NEW_TARGETS
CHECK = "scripts/CheckParticleHamiltonians.lean"
EXPECTED_COUNT = 639
NEW_COUNT = 111

REMAINING = [
    "Permutation representations and Bose symmetry in all n >= 3 tensor sectors; identification of the completed two-boson Friedrichs form with the restriction of the full tensor-sum operator, including the full domains; compatibility with the earlier occupation-space realization.",
    "The quantitative n*epsilon/2 energy bound, the full energy-weighted bosonic form domain, and the annihilation estimate for the actual H(t). Positivity of the new all-sector Hamiltonian and a normalized stationary vacuum are proved; vacuum uniqueness and a vacuum-subtracted excitation gap are not.",
    "The completed S3 Pauli--Fierz interaction built from these actual energy sectors, and its ground-state existence, uniqueness and quantitative small-coupling gap.",
    "A common full-Hilbert-space smeared field family, invariant domains, Wick/Wightman correlations, and vacuum cyclicity.",
    "Lorentz boost covariance and Klein--Gordon causal commutator support, hence spacelike locality; test-map translation covariance under the precise Fourier convention.",
    "A local interacting gauge-field model, continuum limit, physical particle identifications, and any Clay mass-gap theorem. Taking tensor copies of the interacting one-particle H(t) does not introduce interactions between different particles."
]


def main():
    env = os.environ.copy()
    env.pop("LEAN_PATH", None)
    env["LEAN_NUM_THREADS"] = "2"
    logs = Path(tempfile.mkdtemp(prefix="unifiedtheory-particle-hamiltonians-audit-"))
    local_sources = sorted({path for target in TARGETS for path in local_dependencies(target)})
    sources = local_sources + [
        CHECK, "scripts/particle_hamiltonians_audit.py", "scripts/field_dynamics_audit.py",
        "scripts/CheckFieldDynamics.lean", "scripts/CheckFieldExtension.lean",
        "scripts/field_extension_audit.py", "scripts/correlation_reconstruction_audit.py",
        "scripts/CheckCorrelationReconstruction.lean", "scripts/free_balanced_hamiltonian_audit.py",
        "UnifiedTheory.lean", "lakefile.toml", "lake-manifest.json", "lean-toolchain",
        "UnifiedTheory/QSeries/README.md",
    ]
    hashes = {path: sha256(ROOT / path) for path in sources}
    expected = re.findall(r"^#print axioms (\S+)$", (ROOT / CHECK).read_text(), re.M)
    previous = re.findall(r"^#print axioms (\S+)$",
                          (ROOT / "scripts/CheckFieldDynamics.lean").read_text(), re.M)
    new = []
    for module in NEW_TARGETS:
        source = (ROOT / (module.replace(".", "/") + ".lean")).read_text()
        names = re.findall(r"^(?:@\[[^\]]*\]\s*)?(?:def|abbrev|theorem)\s+(\w+)", source, re.M)
        new.extend(module + "." + name for name in names)
    if len(previous) != 528 or len(new) != NEW_COUNT or expected != previous + new:
        raise RuntimeError("Audit must retain all previous checks and every new public declaration")
    if len(expected) != EXPECTED_COUNT or len(set(expected)) != EXPECTED_COUNT:
        raise RuntimeError(f"Expected {EXPECTED_COUNT} distinct axiom checks")
    checks = []
    for index, command in enumerate([
        ["lake", "--rehash", "build", *TARGETS],
        ["lake", "env", "lean", CHECK],
    ]):
        log = logs / f"{index}.log"
        print("Running:", " ".join(command), "Log:", log, flush=True)
        with log.open("w") as output:
            result = subprocess.run(command, cwd=ROOT, env=env, stdout=output,
                                    stderr=subprocess.STDOUT)
        if result.returncode:
            raise RuntimeError(f"Command failed; inspect {log}")
        checks.append({"command": command, "exit_code": 0,
                       "log": str(log), "log_sha256": sha256(log)})
        print("Passed:", " ".join(command), flush=True)
    audit_text = Path(checks[1]["log"]).read_text()
    audits = re.findall(
        r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",
        audit_text)
    if [name for name, _ in audits] != expected:
        raise RuntimeError("Axiom output does not match the expected declarations")
    declarations = {}
    for name, raw in audits:
        axioms = {part.strip() for part in raw.split(",") if part.strip()}
        if not axioms <= STANDARD_AXIOMS:
            raise RuntimeError(f"Unexpected axioms in {name}: {axioms}")
        declarations[name] = sorted(axioms)
    if re.search(r"\bsorryAx\b|: error|: warning", audit_text):
        raise RuntimeError(f"Unexpected diagnostic in {checks[1]['log']}")
    changed = [path for path, digest in hashes.items() if sha256(ROOT / path) != digest]
    if changed:
        raise RuntimeError(f"Sources changed during verification: {changed}")
    root_text = (ROOT / "UnifiedTheory.lean").read_text()
    if not all(f"import {target}\n" in root_text for target in TARGETS):
        raise RuntimeError("Missing root import")
    report = {
        "checks": checks, "audited_declarations": declarations,
        "source_sha256": hashes, "local_lean_dependency_count": len(local_sources),
        "root_imports_present": TARGETS, "root_build_checked": False,
        "uses_temporary_dependency_overlay": False, "new_public_declaration_count": NEW_COUNT,
        "scope": "Retains all 528 preceding checks and verifies 111 new public definitions and theorems. Closes an algebraic positive energy factorization and constructs its positive self-adjoint Friedrichs Hamiltonian with the exact core graph. Constructs completed Hilbert tensor products, dense tensor cores, and positive self-adjoint tensor sums with a full variational domain. Constructs the completed exchange-invariant two-boson sector and its positive self-adjoint Friedrichs Hamiltonian. Constructs arbitrary finite labelled tensor sectors and their maximal self-adjoint positive Hilbert direct sum, including the full square-summable-output domain and a normalized stationary vacuum. No eigenbasis or discrete spectrum of the actual H(t) is assumed.",
        "actual_interacting_applications": [
            "Instantiates the two-particle tensor sum and two-boson Hamiltonian with the full interacting averaged configuration-space H(t), preserving the exact H(t) tensor action on the indicated cores.",
            "Instantiates every labelled particle sector and the complete particle-number Hilbert direct sum with the actual H(t). The one-particle sector equals H(t), including its domain. Proves positivity and a norm-one zero-energy vacuum. This is not yet the all-sector bosonic dGamma construction, an interacting Pauli--Fierz model, or a local relativistic field theory."
],
        "remaining_unformalized": REMAINING,
    }
    target = ROOT / "data/particle_hamiltonians_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print(f"{EXPECTED_COUNT} standard-axiom audits; {len(local_sources)} local Lean sources fingerprinted.")
    print(target)


if __name__ == "__main__":
    main()

