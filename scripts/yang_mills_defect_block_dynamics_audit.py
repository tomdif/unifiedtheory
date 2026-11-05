#!/usr/bin/env python3
"""Check actual full defect-block coercivity, physical loss and approximation errors; preserve 8525 prior checks."""
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

from free_balanced_hamiltonian_audit import ROOT, STANDARD_AXIOMS, local_dependencies, sha256
from yang_mills_sparse_defect_mask_audit import TARGETS as PREVIOUS_TARGETS, proof_code

NEW_TARGETS = ['UnifiedTheory.Clay.YangMills.CompactWeightedCenter', 'UnifiedTheory.Clay.YangMills.WilsonLocalBlockCoercivity', 'UnifiedTheory.Clay.YangMills.WilsonPhysicalEnergyLoss', 'UnifiedTheory.Clay.YangMills.WilsonBlockVarianceRemainder', 'UnifiedTheory.Clay.YangMills.WilsonDefectBlockDynamics']
TARGETS = PREVIOUS_TARGETS + NEW_TARGETS
CHECK = 'scripts/CheckYangMillsDefectBlockDynamics.lean'
PREVIOUS_REPORT = 'data/yang_mills_sparse_defect_mask_audit.json'
PREVIOUS_COUNT = 8525
NEW_COUNT = 41
SCOPE = 'Full fixed-block updates now control local physical defects under the actual finite-cutoff SU(2) ground law. Support means dependence on a fixed set S of s link coordinates, not spatial energy support or membership in a field-dependent mask. A weighted-center lemma pays one density-oscillation ratio. For every continuous S-supported F, actual ground variance is <=exp(24*beta*s) times the actual S-block heat-bath energy, with no exterior-volume factor. Full S-block Haar refresh separately has the exact decomposition Var_pi(F)+Var_Haar(F_ref)+(mean_pi(F)-mean_Haar(F_ref))^2 and thus dominates Var_pi(F) with coefficient one; no ground-law stationarity of Haar refresh is claimed. The constructed full transfer operator is positive and its actual normalization is a contraction. On physical observables only, the established raw/full-step identification yields M(PF)<=<F,PF>_pi and the original full-transfer Dirichlet energy <=loss(F)=Var_pi(F)-Var_pi(PF). Combining the actual block heat-bath comparison gives Var_pi(F)<=Gamma(beta,s)*loss(F), where Gamma=exp(24*beta*s)*(1+exp(12*beta*s))^2<=4*exp(48*beta*s). Therefore one physical step contracts variance of an S-supported input by 1-1/Gamma. The exact law of total variance retains the correlated exterior conditional-mean variance. For a general physical F and any continuous S-supported approximation G, Var_pi(F)<=4*Gamma*loss(F)+(4*exp(24*beta*s)+2)*M(F-G), and the corresponding lower bound on every local approximation error is proved. The same physical plaquette bump (D-1)_+ that was invisible to good-mask updates is supported on an actual block of at most four links: its true full-block heat-bath energy is positive and Var_pi(bump)<=4*exp(192*beta)*loss(bump). These are actual dynamics bounds, not a reference-product substitution. They do not iterate automatically, because PF need not remain S-supported. The exponential coupling/block-size cost, source approximation or cluster-marginal control, actual distant mixed-ground or signed-form estimate, independent global coercivity, physical scaling and the nontrivial continuum construction remain open.'
REMAINING = ['The local support set S is fixed. A field-dependent small defect count does not imply that an arbitrary physical source depends on only those coordinates, or has a small ground-law L2 approximation error.', 'The one-step local contraction is not a spectral gap on an invariant subspace. The evolved source generally depends on links outside S, so the same constant cannot be iterated without a new locality or approximation estimate.', 'The heat-bath constant exp(24*beta*s) and the loss constant Gamma<=4*exp(48*beta*s) deteriorate at weak coupling and with block size. No uniform physical-time estimate follows merely from eliminating exterior-volume dependence.', 'The exact total-variance identity retains the exterior conditional-mean variance. The new supported-source comparison is not a global variance factorization over many correlated blocks or field-dependent defect clusters.', 'The physical Dirichlet-to-loss comparison uses the proved positivity of the full operator and the proved raw/full identification on gauge-invariant observables. It does not silently assume positivity of the raw transition on all nonphysical sources.', 'Full Haar refresh is used as a response form and an independent comparison draw. It is not asserted to preserve the actual ground law; the true heat-bath law and its exterior correlations are retained separately.', 'The plaquette bump witness here is G=(D-1)_+. The earlier retained-region source F_loc=(D-1)_+*(32-V)_+ depends on total energy and is not claimed to be supported on four links.', 'A domain functional inequality from good-region curvature, temporal-pinning source control, field-dependent boundary normalization, source-sensitive defect-cluster control, actual distant/signed-form bounds, compatible global lower coercivity and all twelve full Clay requirements remain open.']


def main():
    previous = json.loads((ROOT / PREVIOUS_REPORT).read_text())
    if len(previous["audited_declarations"]) != PREVIOUS_COUNT:
        raise RuntimeError("Unexpected predecessor declaration count")
    if any(not set(a) <= STANDARD_AXIOMS for a in previous["audited_declarations"].values()):
        raise RuntimeError("Unexpected predecessor axioms")
    permitted = {"UnifiedTheory.lean", "UnifiedTheory/QSeries/README.md",
                 "UnifiedTheory/Clay/YangMills/README.md", "data/yang_mills_requirements.json"}
    retained = {p: h for p, h in previous["source_sha256"].items() if p not in permitted}
    changed = [p for p, h in retained.items() if sha256(ROOT / p) != h]
    if changed:
        raise RuntimeError(f"Previously verified sources changed: {changed}")
    certificate = previous
    chain_count = 0
    while True:
        chain_count += 1
        for check in certificate["checks"]:
            if check["exit_code"] != 0 or sha256(Path(check["log"])) != check["log_sha256"]:
                raise RuntimeError("Missing or changed successful predecessor log")
        predecessor = certificate.get("predecessor_report")
        if not predecessor:
            break
        if sha256(ROOT / predecessor) != certificate["predecessor_report_sha256"]:
            raise RuntimeError("Changed predecessor certificate")
        certificate = json.loads((ROOT / predecessor).read_text())
    expected_sources = sorted(m.replace(".", "/") + ".lean" for m in NEW_TARGETS)
    actual_sources = sorted(str(p.relative_to(ROOT))
        for p in (ROOT / "UnifiedTheory/Clay/YangMills").glob("*.lean")
        if str(p.relative_to(ROOT)) not in previous["source_sha256"])
    if expected_sources != actual_sources:
        raise RuntimeError("New Yang-Mills source inventory mismatch")
    discovered = []
    for module in NEW_TARGETS:
        source = (ROOT / (module.replace(".", "/") + ".lean")).read_text()
        code = proof_code(source)
        if re.search(r"\b(?:sorry|admit|native_decide)\b|^\s*(?:private\s+)?axiom\s", code, re.M):
            raise RuntimeError(f"Unverified proof shortcut: {module}")
        namespaces = re.findall(r"^namespace (\S+)", code, re.M)
        if namespaces != [module]:
            raise RuntimeError("Unexpected namespace")
        names = re.findall(
            r"^(?:@\[[^\]]*\]\s*)?(?:local\s+)?(?:def|abbrev|theorem|lemma|instance|structure)\s+(\w+|:)",
            code, re.M)
        if ":" in names:
            raise RuntimeError("An anonymous instance needs a named audit entry")
        discovered.extend(module + "." + name for name in names)
    expected = re.findall(r"^#print axioms (\S+)$", (ROOT / CHECK).read_text(), re.M)
    if discovered != expected or len(expected) != NEW_COUNT or len(set(expected)) != NEW_COUNT:
        raise RuntimeError("Not all fresh declarations are audited")
    local_sources = sorted({p for target in TARGETS for p in local_dependencies(target)})
    sources = sorted(set(local_sources + list(previous["source_sha256"]) + [
        CHECK, "scripts/yang_mills_defect_block_dynamics_audit.py", PREVIOUS_REPORT,
        "data/yang_mills_defect_block_dynamics_2026_10_30.json",
        "data/yang_mills_bad_density_continuum_2026_10_29.json",
        "data/yang_mills_region_clusters_2026_10_29.json",
        "data/yang_mills_box_packing_2026_10_29.json",
        "data/yang_mills_balaban_deep_dive_2026_10_29.json",
        "data/yang_mills_mass_gap_attack_2026_10_29.json",
        "data/yang_mills_generated_mixing_2026_10_29.json",
        "data/yang_mills_mixed_stability_2026_10_29.json",
        "data/yang_mills_weighted_clustering_2026_10_29.json",
        "data/yang_mills_microscopic_margin_2026_10_29.json",
        "data/yang_mills_two_neighbor_2026_10_29.json",
        "data/yang_mills_gauge_response_2026_10_29.json",
        "data/yang_mills_stationary_response_2026_10_29.json",
        "data/yang_mills_variance_dissipation_2026_10_29.json",
        "data/yang_mills_collective_gram_2026_10_29.json",
        "data/yang_mills_near_far_gram_2026_10_29.json",
        "data/yang_mills_uniform_closure_attempt_2026_10_29.json",
        "data/yang_mills_gauge_residual_2026_10_29.json",
        "data/yang_mills_haar_response_2026_10_29.json",
        "data/yang_mills_physical_gram_2026_10_29.json",
        "data/yang_mills_haar_budget_2026_10_29.json",
        "data/yang_mills_normalized_response_2026_10_29.json",
        "data/yang_mills_haar_frame_2026_10_29.json",
        "data/yang_mills_plaquette_floor_2026_10_29.json",
        "data/yang_mills_direct_haar_2026_10_29.json",
        "data/yang_mills_ground_peak_2026_10_29.json",
        "data/yang_mills_joint_rotation_2026_10_29.json",
        "data/yang_mills_exterior_response_2026_10_29.json",
        "data/yang_mills_interior_response_2026_10_29.json",
        "data/yang_mills_variance_profile_2026_10_29.json",
        "data/yang_mills_middle_bridge_2026_10_29.json",
        "data/yang_mills_bridge_response_2026_10_29.json",
        "data/yang_mills_collective_obstruction_2026_10_29.json",
        "data/yang_mills_boundary_reduction_2026_10_29.json",
        "data/yang_mills_boundary_connected_2026_10_29.json",
        "data/yang_mills_small_field_curvature_2026_10_29.json",
        "data/yang_mills_antipodal_source_2026_10_29.json",
        "data/yang_mills_gauge_source_tail_2026_10_29.json",
        "data/yang_mills_spatial_source_obstruction_2026_10_29.json",
    ]))
    hashes = {p: sha256(ROOT / p) for p in sources}
    root = (ROOT / "UnifiedTheory.lean").read_text()
    if not all(f"import {target}\n" in root for target in TARGETS):
        raise RuntimeError("Missing root import")
    env = os.environ.copy()
    env.pop("LEAN_PATH", None)
    env["LEAN_NUM_THREADS"] = "2"
    logs = Path(tempfile.mkdtemp(prefix="unifiedtheory-yang-mills-defect-block-dynamics-audit-"))
    checks = []
    commands = [["lake", "--rehash", "build", *TARGETS],
                ["lake", "env", "lean", CHECK],
                ["python3", "scripts/check_yang_mills_requirements.py"]]
    for i, command in enumerate(commands):
        log = logs / f"{i}.log"
        print(f"Check {i + 1}/3: {' '.join(command[:3])}; log {log}", flush=True)
        with log.open("w") as output:
            result = subprocess.run(command, cwd=ROOT, env=env, stdout=output,
                                    stderr=subprocess.STDOUT)
        if result.returncode:
            raise RuntimeError(f"Command failed; inspect {log}")
        if i == 0:
            build_output = log.read_text()
            for module in NEW_TARGETS:
                source_path = re.escape(module.replace(".", "/") + ".lean")
                if re.search(r"warning: " + source_path + r":", build_output):
                    raise RuntimeError(f"Fresh-module build warning: {module}; inspect {log}")
        checks.append({"command": command, "exit_code": 0, "log": str(log),
                       "log_sha256": sha256(log)})
    output = Path(checks[1]["log"]).read_text()
    audits = re.findall(
        r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", output)
    if [n for n, _ in audits] != expected or re.search(r"\bsorryAx\b|: error|: warning", output):
        raise RuntimeError("Unexpected fresh axiom output or diagnostic")
    declarations = dict(previous["audited_declarations"])
    for name, raw in audits:
        axioms = {a.strip() for a in raw.split(",") if a.strip()}
        if not axioms <= STANDARD_AXIOMS or name in declarations:
            raise RuntimeError(f"Unexpected axioms or duplicate declaration: {name}")
        declarations[name] = sorted(axioms)
    if any(sha256(ROOT / p) != h for p, h in hashes.items()):
        raise RuntimeError("Sources changed during verification")
    report = {
        "checks": checks,
        "verification_mode": f"Incremental: {NEW_COUNT} fresh checks and {PREVIOUS_COUNT} "
            f"retained checks, with {chain_count} predecessor certificates and logs verified.",
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
        "scope": SCOPE,
        "yang_mills_requirements_check": json.loads(Path(checks[2]["log"]).read_text()),
        "remaining_unformalized": REMAINING,
    }
    target = ROOT / "data/yang_mills_defect_block_dynamics_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print(f"Passed: {NEW_COUNT} fresh checks; {len(declarations)} cumulative; {target}")


if __name__ == "__main__":
    main()
