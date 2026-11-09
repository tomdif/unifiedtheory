#!/usr/bin/env python3
"""Build the actual dependencies and audit every field-dynamics declaration.

Retains the complete preceding 331-declaration audit. Records remaining
model-construction obligations explicitly; this is not a full-root build.
"""
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

from free_balanced_hamiltonian_audit import ROOT, STANDARD_AXIOMS, local_dependencies, sha256
from field_extension_audit import TARGETS as PREVIOUS_TARGETS

NEW_TARGETS = [
    "UnifiedTheory.Audit.KFCausalCoerciveFormHamiltonian",
    "UnifiedTheory.Audit.KFCausalRelativeFormPerturbation",
    "UnifiedTheory.Audit.KFCausalBosonicNumberEstimate",
    "UnifiedTheory.Audit.KFCausalBosonicDiagonalHamiltonian",
    "UnifiedTheory.Audit.KFCausalRelativisticMassShell",
    "UnifiedTheory.Audit.KFCausalMassShellSchwartzRestriction",
    "UnifiedTheory.Audit.KFCausalMassShellTwoPoint",
    "UnifiedTheory.Audit.KFCausalInteractingMassShell",
    "UnifiedTheory.Audit.KFCausalMassShellTranslations",
    "UnifiedTheory.Audit.KFCausalMassShellStrongContinuity",
    "UnifiedTheory.Audit.KFCausalBosonicBoundedDiagonal",
    "UnifiedTheory.Audit.KFCausalBosonicNumberForm",
    "UnifiedTheory.Audit.KFCausalLinearFieldFormPerturbation",
    "UnifiedTheory.Audit.KFCausalBosonicForcedNumberHamiltonian",
    "UnifiedTheory.Audit.KFCausalInteractingComponentPerturbation",
    "UnifiedTheory.Audit.KFCausalLpHamiltonianAmplification",
    "UnifiedTheory.Audit.KFCausalInteractingTensorFactor",
    "UnifiedTheory.Audit.KFCausalInteractingComponentEnergyFloor"
]
TARGETS = PREVIOUS_TARGETS + NEW_TARGETS
CHECK = "scripts/CheckFieldDynamics.lean"
EXPECTED_COUNT = 528
NEW_COUNT = 197

REMAINING = [
    "Self-adjoint dGamma of the actual generally non-diagonal H(t): sums of the proved individual L2 tensor-factor actions, permutation symmetry, completed bosonic sectors and the particle-number direct sum, with full domains and energy floor. The forced-number model does not identify with this operator.",
    "The energy-weighted annihilation bound and completed S3 Pauli--Fierz form for that dGamma(H(t)). The general relative-form and linear-field theorems are proved, but their hypotheses still need this model-specific construction.",
    "Existence and uniqueness of the Pauli--Fierz ground state and the quantitative small-coupling excitation gap.",
    "A common full-Hilbert-space smeared field family, its invariant domains, Wick/Wightman correlations, and vacuum cyclicity. The continuous positive two-point form alone is not the full field theory.",
    "Lorentz boost covariance and Klein--Gordon causal commutator support, hence spacelike locality. Explicit strongly continuous spacetime translations and one-particle positive energy have been proved.",
    "A local interacting gauge-field model, continuum limit, physical particle identifications, and any Clay mass-gap theorem."
]


def main():
    env = os.environ.copy()
    env.pop("LEAN_PATH", None)
    env["LEAN_NUM_THREADS"] = "2"
    logs = Path(tempfile.mkdtemp(prefix="unifiedtheory-field-dynamics-audit-"))
    local_sources = sorted({path for target in TARGETS for path in local_dependencies(target)})
    sources = local_sources + [
        CHECK, "scripts/field_dynamics_audit.py", "scripts/CheckFieldExtension.lean",
        "scripts/field_extension_audit.py", "scripts/correlation_reconstruction_audit.py",
        "scripts/CheckCorrelationReconstruction.lean", "scripts/free_balanced_hamiltonian_audit.py",
        "UnifiedTheory.lean", "lakefile.toml", "lake-manifest.json", "lean-toolchain",
        "UnifiedTheory/QSeries/README.md",
    ]
    hashes = {path: sha256(ROOT / path) for path in sources}
    expected = re.findall(r"^#print axioms (\S+)$", (ROOT / CHECK).read_text(), re.M)
    previous = re.findall(r"^#print axioms (\S+)$",
                          (ROOT / "scripts/CheckFieldExtension.lean").read_text(), re.M)
    new = []
    for module in NEW_TARGETS:
        source = (ROOT / (module.replace(".", "/") + ".lean")).read_text()
        names = re.findall(r"^(?:@\[[^\]]*\]\s*)?(?:def|abbrev|theorem)\s+(\w+)", source, re.M)
        new.extend(module + "." + name for name in names)
    if len(previous) != 331 or len(new) != NEW_COUNT or expected != previous + new:
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
        "scope": "Retains all 331 preceding checks. Constructs a self-adjoint operator from an injective dense Hilbert form embedding and an invertible symmetric representing operator; derives invertibility under a relative form bound below one and proves the full variational graph. Derives the occupation annihilation-number estimate and maximal self-adjoint real diagonal operators. Constructs the completed number form, its weighted-l2 domain and extended annihilation estimate, and the self-adjoint forced-number Hamiltonian with its explicit core action and lower bound. Constructs the continuous-mass four-dimensional mass-shell measure and L2 space, self-adjoint energy and full domain, positive energy floor, continuous Schwartz restriction and Fourier test map, and continuous positive two-point form. Instantiates these with the actual interacting spectral mass law. Constructs explicit unitary spacetime translations, their group law, preservation of the energy graph, and strong continuity. These results do not complete the actual Pauli--Fierz model or a local relativistic field theory.",
        "actual_interacting_applications": [
            "For each of the eight actual averaged energy components, constructs a self-adjoint linear form perturbation of the full configuration-space H(t), preserving all original interacting form terms, with a full variational graph and lower bound -2*g^2. Proves exact equality with H(t), including the domain, at zero added coupling. In the original energy-floor parameter range, proves the full-domain lower bound epsilon/4-2*g^2, positive when g^2<epsilon/8; this is not an excitation gap.",
            "Constructs the actual H(t) on L2(Omega; X) for an arbitrary spectator measure. Proves self-adjointness, the exact almost-everywhere graph and full domain, and the original epsilon/2 energy floor. This is one completed tensor-factor action, not the many-factor sum or bosonic restriction."
        ],
        "remaining_unformalized": REMAINING,
    }
    target = ROOT / "data/field_dynamics_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print(f"{EXPECTED_COUNT} standard-axiom audits; {len(local_sources)} local Lean sources fingerprinted.")
    print(target)


if __name__ == "__main__":
    main()

