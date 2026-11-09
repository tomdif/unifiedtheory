#!/usr/bin/env python3
"""Check actual sparse masks, retained sources and direct-coercivity obstruction; preserve 8449 prior checks."""
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

from free_balanced_hamiltonian_audit import ROOT, STANDARD_AXIOMS, local_dependencies, sha256
from yang_mills_joint_box_localization_audit import TARGETS as PREVIOUS_TARGETS, proof_code

NEW_TARGETS = ['UnifiedTheory.Clay.YangMills.WilsonDefectMask', 'UnifiedTheory.Clay.YangMills.WilsonMaskedCurvature', 'UnifiedTheory.Clay.YangMills.WilsonBoxDefectBudget', 'UnifiedTheory.Clay.YangMills.WilsonSparseRetainedWitness', 'UnifiedTheory.Clay.YangMills.WilsonMaskedCoercivityObstruction']
TARGETS = PREVIOUS_TARGETS + NEW_TARGETS
CHECK = 'scripts/CheckYangMillsSparseDefectMask.lean'
PREVIOUS_REPORT = 'data/yang_mills_joint_box_localization_audit.json'
PREVIOUS_COUNT = 8449
NEW_COUNT = 76
SCOPE = 'Actual finite-cutoff SU(2) defect masks, their source-weighted size and their coercivity obstruction are now formalized. For a spatial-link block S, bad internal plaquettes have squared chord defect D_p>delta^2. The good set removes all links touching those plaquettes or any crossing plaquette. Exact support counting gives delta^2*#removed<=4*V_S+4*delta^2*b. Every plaquette touching a good link is internal and has chord <=delta for delta>=0; the mask is gauge invariant and its removed count is measurable. For rotations equal to one off an arbitrary active set, the actual spatial second difference only needs small plaquettes touching that set. The temporal bounds likewise only need pinning on active links. At delta=1/32 and squared endpoint distances <=1/2 on good links, the actual middle-action second difference is >=2*beta*cost(q), with the corresponding normalized log-density bound. Outside the previously proved adaptive bad-box union, every translated box retains at least a 1-rho fraction of its 3*L^3 links, where rho=4*(768/L+96*e(beta))/(3*delta^2)+32/L. For fixed positive delta, rho tends to zero as beta and L grow. The measurable event that any box loses more than this fraction is contained in the adaptive bad union and has the same actual f-squared source bound 2*loss(F)+2*exp(-96*beta*L^2)*M(F) under the explicit volume budget. The corresponding approximate slow-mode concentration is proved for changing admissible regulators. A single -1 link has total spatial energy <=16 and a plaquette defect exactly four; it lies inside every positive-size adaptive retained region and violates axial flatness for delta<2. The separate physical source F_loc=(D-1)_+*(32-V)_+ is nonconstant, has positive actual variance and loss, and is supported entirely in the retained region. However, the physical bump G=(D-1)_+ is unchanged by every rotation supported on the good mask at delta=1/32 with each link displacement <=1/16. Hence every finite family of such state-dependent masked responses has zero energy on G despite positive actual ground variance: no direct all-physical variance comparison with that response form can hold for any finite constant. Without a size restriction, masked rotations make G nondecreasing; if each induced update preserves the actual ground law, stationarity forces almost-sure invariance and gives the same obstruction. This rules out discarding the defect directions, not the full Wilson gap or a comparison using full block/Haar updates. Pointwise masked curvature still needs an actual domain functional inequality and temporal-pinning source control. Defect-coordinate dynamics, actual distant mixed-ground summability, independent full physical coercivity and the continuum construction remain open.'
REMAINING = ['The worst-case boundary factor in the operator normalization has not been replaced by a field-dependent or small-field boundary factor. Such a replacement still needs a valid operator comparison over both kernel inputs.', 'The good-mask curvature estimate is pointwise and only controls rotations supported on the mask. It still requires temporal pinning on those links; no global Poincare or conditional-domain functional inequality follows from it alone.', 'The mask depends on the field and need not vary continuously or define a measure-preserving change of variables. No variable-rotation Haar or ground-law invariance is silently assumed.', 'The actual direct all-physical comparison using only small masked responses is false. Enlarging their rotation size does not repair a family whose individual updates preserve the ground law. Full physical defect directions or another justified comparison must be retained.', 'The obstruction concerns the stated direct variance response forms. It does not refute the full-Haar comparison, an independently proved time-evolved comparison, the original Wilson spectral gap, or the Yang-Mills mass gap.', 'The retained-region source F_loc and the invariant response witness G are different observables. Neither is constructed as an approximate eigenvector or a continuum excitation.', 'A vanishing fraction of removed links does not control their connectivity, capacity or source sensitivity. Sparse defects and defect-cluster dynamics remain essential even when most links have pointwise positive curvature.', 'The source-tail and slow-mode statements retain the explicit fit, volume, bounded-mass and vanishing-loss hypotheses. The middle bridge source law has not been replaced by this endpoint f-squared law; temporal-pinning and correlated bridge estimates remain open.', 'Actual distant mixed-ground or signed physical Haar-form control, compatible independent global lower coercivity, a physical coupling trajectory, nontrivial continuum survival and all twelve full Clay requirements remain open.']


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
        CHECK, "scripts/yang_mills_sparse_defect_mask_audit.py", PREVIOUS_REPORT,
        "data/yang_mills_sparse_defect_mask_2026_10_30.json",
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
    logs = Path(tempfile.mkdtemp(prefix="unifiedtheory-yang-mills-sparse-defect-mask-audit-"))
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
    target = ROOT / "data/yang_mills_sparse_defect_mask_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print(f"Passed: {NEW_COUNT} fresh checks; {len(declarations)} cumulative; {target}")


if __name__ == "__main__":
    main()
