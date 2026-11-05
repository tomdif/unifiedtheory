#!/usr/bin/env python3
"""Incremental local Wilson fluctuation and OS obstruction audit, retaining 2702 validated checks.

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
from yang_mills_tempered_dynamics_audit import TARGETS as PREVIOUS_TARGETS

NEW_TARGETS = ['UnifiedTheory.Clay.YangMills.DiagonalContactTerms', 'UnifiedTheory.Clay.YangMills.FourLinkWilsonTransfer', 'UnifiedTheory.Clay.YangMills.GibbsConditionalLower', 'UnifiedTheory.Clay.YangMills.LocalizedGibbsFluctuation', 'UnifiedTheory.Clay.YangMills.OSResolventWitnessState', 'UnifiedTheory.Clay.YangMills.SingleLinkWilsonLipschitz', 'UnifiedTheory.Clay.YangMills.SingleLinkWilsonOscillation', 'UnifiedTheory.Clay.YangMills.SpecialUnitaryTwoOscillation', 'UnifiedTheory.Clay.YangMills.StaticOSCounterexample', 'UnifiedTheory.Clay.YangMills.StaticSchwartzHierarchy', 'UnifiedTheory.Clay.YangMills.UnitaryGibbsTraceFluctuation', 'UnifiedTheory.Clay.YangMills.UnitaryHaarCaps', 'UnifiedTheory.Clay.YangMills.UnitaryTraceLocalOscillation', 'UnifiedTheory.Clay.YangMills.WilsonConditionalPolynomial', 'UnifiedTheory.Clay.YangMills.WilsonFeatureIntegral']
TARGETS = PREVIOUS_TARGETS + NEW_TARGETS
CHECK = "scripts/CheckYangMillsLocalFluctuation.lean"
PREVIOUS_REPORT = "data/yang_mills_tempered_dynamics_audit.json"
NEW_COUNT = 191
PREVIOUS_COUNT = 2702
REMAINING = ['Prove a positive rescaled reflected fluctuation for one pre-fixed strict-positive-time Schwartz test along a physically specified coupling/normalization trajectory. The new polynomial ordinary plaquette floor under full U(d) Wilson measure does not control a half-lattice conditional response or covariance cancellations in a fixed smear.', 'Bind the primitive four-link Wilson kinetic matrix element to the full periodic transfer/reflection geometry, spatial potential and gauge projection, and control propagation through a number of layers growing like inverse lattice spacing. Finite strict positivity alone is insufficient.', 'Construct compatible all-order renormalized Schwartz bounds, including any necessary local contact subtractions and higher-order consistency, on the nonzero physical branch. Finite two-point contact jets vanish on strictly separated reflected pairs, but their physical coefficients and all-order reflection-positive renormalization are not constructed.', 'Extend the local U(d) Haar/Gibbs argument to the chosen compact simple gauge group and representation. A determinant-one SU(2) trace perturbation is proved algebraically, but its conditional Haar/Gibbs attachment is not. Construct physical field/mixing identifications, scale matching and infinite-volume control.', 'Prove temporal clustering or a suitable exclusion of non-vacuum zero modes, then a finite positive excitation scale and gap. The explicit static random-sign Schwartz hierarchy has positive reflected variance, all-order bounds, full positivity and stationarity but its actual reconstructed Hamiltonian is zero. Resolvent regularization supplies a nonzero orthogonal domain vector, not positive energy.', 'Full rotations, local operator domains, Poincare covariance/joint spectrum, short-distance/OPE/stress-tensor properties and the other full Clay obligations remain open. Common-ultrafilter convergence is not sequential convergence or uniqueness. All twelve requirements remain open.']


def main():
    previous = json.loads((ROOT / PREVIOUS_REPORT).read_text())
    prior_names = []
    for ledger in ["scripts/CheckParticleHamiltonians.lean", "scripts/CheckParticleEnergyGap.lean",
                   "scripts/CheckBosonicParticleSectors.lean", "scripts/CheckBosonicEnergyClayFramework.lean", "scripts/CheckYangMillsSwarm.lean",
                   "scripts/CheckYangMillsConstruction.lean",
                   "scripts/CheckYangMillsLatticeBridge.lean",
                   "scripts/CheckYangMillsReflectedHierarchy.lean",
                   "scripts/CheckYangMillsSchwingerBridge.lean",
                   "scripts/CheckYangMillsDirectRequirements.lean",
                   "scripts/CheckYangMillsGeneratorDensity.lean",
                   "scripts/CheckYangMillsRenormalizedTuning.lean",
                   "scripts/CheckYangMillsTemperedDynamics.lean"]:
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
    actual_new_sources = sorted(
        str(p.relative_to(ROOT))
        for p in (ROOT / "UnifiedTheory/Clay/YangMills").glob("*.lean")
        if str(p.relative_to(ROOT)) not in previous["source_sha256"]
    )
    expected_new_sources = sorted(module.replace(".", "/") + ".lean" for module in NEW_TARGETS)
    if actual_new_sources != expected_new_sources:
        raise RuntimeError("Post-2702 Yang--Mills source inventory does not match NEW_TARGETS")
    expected = re.findall(r"^#print axioms (\S+)$", (ROOT / CHECK).read_text(), re.M)
    discovered = []
    for module in NEW_TARGETS:
        source = (ROOT / (module.replace(".", "/") + ".lean")).read_text()
        if re.search(r"\b(?:sorry|admit|native_decide)\b|^\s*(?:private\s+)?axiom\s", source, re.M):
            raise RuntimeError(f"Forbidden proof shortcut or axiom in {module}")
        namespaces = re.findall(r"^namespace (\S+)", source, re.M)
        if len(namespaces) != 1:
            raise RuntimeError("Expected one explicit namespace per new module")
        discovered += [namespaces[0] + "." + n for n in re.findall(
            r"^(?:@\[[^\]]*\]\s*)?(?:def|abbrev|theorem|lemma|instance|structure)\s+(\w+)", source, re.M)]
    if expected != discovered or len(expected) != NEW_COUNT or len(set(expected)) != NEW_COUNT:
        raise RuntimeError("Every new public definition and theorem must be checked")
    local_sources = sorted({p for target in TARGETS for p in local_dependencies(target)})
    sources = sorted(set(local_sources + list(previous["source_sha256"]) + [
        CHECK, "scripts/yang_mills_local_fluctuation_audit.py", PREVIOUS_REPORT,
        "data/yang_mills_requirements.json", "scripts/check_yang_mills_requirements.py",
        "UnifiedTheory/Clay/YangMills/README.md",
        "UnifiedTheory.lean", "UnifiedTheory/QSeries/README.md",
    ]))
    hashes = {p: sha256(ROOT / p) for p in sources}
    env = os.environ.copy()
    env.pop("LEAN_PATH", None)
    env["LEAN_NUM_THREADS"] = "2"
    logs = Path(tempfile.mkdtemp(prefix="unifiedtheory-yang-mills-local-fluctuation-audit-"))
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
        "verification_mode": f"Incremental: {NEW_COUNT} freshly checked declarations plus {PREVIOUS_COUNT} previous checks retained after verifying their proof-source, audit-script and verification-log hashes, including the full predecessor certificate chain.",
        "predecessor_report": PREVIOUS_REPORT,
        "predecessor_report_sha256": hashes[PREVIOUS_REPORT],
        "retained_verified_source_count": len(retained),
        "retained_declaration_count": PREVIOUS_COUNT,
        "new_public_declaration_count": NEW_COUNT,
        "new_module_count": len(NEW_TARGETS),
        "audited_declarations": declarations,
        "source_sha256": hashes,
        "local_lean_dependency_count": len(local_sources),
        "root_imports_present": TARGETS,
        "root_build_checked": False,
        "uses_temporary_dependency_overlay": False,
        "scope": "Post-2702 local fluctuation and OS obstruction results. Proves six-plaquette locality and a volume-independent entrywise Wilson action Lipschitz bound, actual unitary Haar cap mass estimates, uniform quadratic trace oscillation on U(d), and a separate determinant-one SU(2) perturbation. Derives a polynomial ordinary real-plaquette second-moment floor under the full interacting periodic U(d) Wilson law, for every center and all real beta, by exact fiber Gibbs averaging; no nonconstancy or fluctuation premise is supplied. Proves a concrete strictly positive centered plaquette matrix element for the primitive four-link U(2) kinetic kernel at positive beta. Constructs finite two-point contact distributions and all finite derivative jets, proving eventual invisibility on separated reflected pairs even with cutoff-dependent coefficients and orders. Regularizes actual nonzero orthogonal OS states into the maximal Hamiltonian domain and proves finite nonnegative energy bounds. Constructs an explicit static random-sign Schwartz hierarchy with full reflection positivity, all-order bounds and positive connected variance but zero reconstructed Hamiltonian, disproving the implication to positive excitation energy. These results do not establish the uniform reflected ultraviolet endpoint, a physical coupling trajectory, compatible nonzero all-order renormalized bounds, a simple-group continuum theory, physical field identifications or a mass gap. All twelve full Clay requirements remain open.",
        "yang_mills_requirements_check": json.loads(Path(checks[2]["log"]).read_text()),
        "remaining_unformalized": REMAINING,
    }
    target = ROOT / "data/yang_mills_local_fluctuation_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print(f"{NEW_COUNT} fresh standard-axiom checks; {len(declarations)} cumulative; "
          f"{len(local_sources)} local Lean sources fingerprinted.")
    print(target)


if __name__ == "__main__":
    main()
