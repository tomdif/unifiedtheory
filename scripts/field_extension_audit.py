#!/usr/bin/env python3
"""Build and audit the formalized foundations of the two field extensions.

Retains all 165 correlation checks and checks every public declaration in the
new modules. Records the remaining unformalized field-theory statements.
"""
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

from free_balanced_hamiltonian_audit import ROOT, STANDARD_AXIOMS, local_dependencies, sha256
from correlation_reconstruction_audit import TARGETS as PREVIOUS_TARGETS


NEW_TARGETS = [
    "UnifiedTheory.Audit.KFCausalBosonicOccupationSpace",
    "UnifiedTheory.Audit.KFCausalBosonicCCR",
    "UnifiedTheory.Audit.KFCausalBosonicFieldClosure",
    "UnifiedTheory.Audit.KFCausalBosonicOneParticle",
    "UnifiedTheory.Audit.KFCausalResolventSpectralMeasure",
    "UnifiedTheory.Audit.KFCausalResolventMassMeasure",
    "UnifiedTheory.Audit.KFCausalInteractingMassMeasure",
    "UnifiedTheory.Audit.KFCausalMassEuclideanKernel",
    "UnifiedTheory.Audit.KFCausalInteractingFieldExtension",
    "UnifiedTheory.Audit.KFCausalPauliFierzMatterCore",
    "UnifiedTheory.Audit.KFCausalPauliFierzCouplingClosure"
]
TARGETS = PREVIOUS_TARGETS + NEW_TARGETS
CHECK = "scripts/CheckFieldExtension.lean"
EXPECTED_COUNT = 331


def main():
    env = os.environ.copy()
    env.pop("LEAN_PATH", None)
    env.setdefault("LEAN_NUM_THREADS", "2")
    logs = Path(tempfile.mkdtemp(prefix="unifiedtheory-field-extension-audit-"))
    local_sources = sorted({path for target in TARGETS for path in local_dependencies(target)})
    sources = local_sources + [
        CHECK, "scripts/field_extension_audit.py", "scripts/correlation_reconstruction_audit.py",
        "scripts/CheckCorrelationReconstruction.lean",
        "scripts/free_balanced_hamiltonian_audit.py", "UnifiedTheory.lean",
        "lakefile.toml", "lake-manifest.json", "lean-toolchain",
        "UnifiedTheory/QSeries/README.md",
    ]
    hashes = {path: sha256(ROOT / path) for path in sources}
    expected = re.findall(r"^#print axioms (\S+)$", (ROOT / CHECK).read_text(), re.M)
    if len(expected) != EXPECTED_COUNT or len(set(expected)) != len(expected):
        raise RuntimeError(f"Expected {EXPECTED_COUNT} distinct axiom checks")
    previous = re.findall(r"^#print axioms (\S+)$",
                          (ROOT / "scripts/CheckCorrelationReconstruction.lean").read_text(), re.M)
    new = []
    for module in NEW_TARGETS:
        source = (ROOT / (module.replace(".", "/") + ".lean")).read_text()
        names = re.findall(r"^(?:@\[[^\]]*\]\s*)?(?:def|abbrev|theorem)\s+(\w+)", source, re.M)
        new.extend(module + "." + name for name in names)
    if expected != previous + new or len(previous) != 165:
        raise RuntimeError("Audit must retain all previous checks and every new public declaration")
    commands = [
        ["lake", "--rehash", "build", *TARGETS],
        ["lake", "env", "lean", CHECK],
    ]
    checks = []
    for index, command in enumerate(commands):
        log = logs / f"{index}.log"
        with log.open("w") as output:
            result = subprocess.run(command, cwd=ROOT, env=env, stdout=output,
                                    stderr=subprocess.STDOUT)
        if result.returncode:
            raise RuntimeError(f"Command failed: {command}; inspect {log}")
        checks.append({"command": command, "exit_code": 0,
                       "log": str(log), "log_sha256": sha256(log)})
        print("Passed:", " ".join(command), flush=True)
    audit_text = Path(checks[1]["log"]).read_text()
    audits = re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", audit_text)
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
        "checks": checks,
        "audited_declarations": declarations,
        "source_sha256": hashes,
        "local_lean_dependency_count": len(local_sources),
        "root_imports_present": TARGETS,
        "root_build_checked": False,
        "uses_temporary_dependency_overlay": False,
        "new_public_declaration_count": 166,
        "scope": "Retains all 165 preceding correlation/spectral checks. Constructs a complete occupation Hilbert space and dense core, normalized mode creation and annihilation, their mixed canonical commutation and adjoint relations, and closed densely defined mode fields. Constructs an isometric copy of the complete original Hilbert space, and a Hilbert basis containing a prescribed unit resolvent-range seed. Constructs the actual interacting resolvent scalar spectral measure through continuous functional calculus and Riesz--Markov, its r^2-weighted mass-squared pushforward, probability normalization, threshold (epsilon/2)^2 and all resolvent moments. Constructs an integrable continuous-time Euclidean reflection-positive two-point kernel at fixed spatial momentum and identifies its mass-shell formula. Constructs the S3 sign/mean matter operators, nonzero matter commutator, symmetric bosonic mode coupling, gauge invariance, nonzero vacuum output, and a closed densely defined extension on the complete S3-by-occupation Hilbert space. These are foundations of the two analytical extensions; they do not complete either field model or establish physical identifications.",
        "remaining_unformalized": [
          "Self-adjoint second quantization dGamma of the actual generally non-diagonal H(t), with its full operator and form domains.",
          "Energy-weighted annihilation estimates and a closed semibounded Pauli--Fierz form for that dGamma(H(t)); a KLMN construction.",
          "Ground-state existence, uniqueness and the quantitative small-coupling excitation gap for the constructed Pauli--Fierz Hamiltonian.",
          "The four-dimensional mass-shell one-particle space, smeared fields, Wightman distributions and Wick correlations.",
          "Klein--Gordon causal commutator support, relativistic locality, Poincare covariance and positive energy for the generalized free field.",
          "A local interacting gauge-field model, continuum limit, physical particle identifications, and any Clay mass-gap theorem."
],
    }
    target = ROOT / "data/field_extension_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print(f"{EXPECTED_COUNT} standard-axiom audits; {len(local_sources)} local Lean sources fingerprinted.")
    print(target)


if __name__ == "__main__":
    main()

