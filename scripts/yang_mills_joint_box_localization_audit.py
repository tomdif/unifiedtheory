#!/usr/bin/env python3
"""Check joint actual box localization and adaptive density concentration; preserve 8372 prior checks."""
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

from free_balanced_hamiltonian_audit import ROOT, STANDARD_AXIOMS, local_dependencies, sha256
from yang_mills_spatial_cut_dynamics_audit import TARGETS as PREVIOUS_TARGETS, proof_code

NEW_TARGETS = ['UnifiedTheory.Clay.YangMills.CompactCutoffCover', 'UnifiedTheory.Clay.YangMills.WilsonCutoffCover', 'UnifiedTheory.Clay.YangMills.WilsonSpatialCutUnion', 'UnifiedTheory.Clay.YangMills.WilsonSpatialCutTranslate', 'UnifiedTheory.Clay.YangMills.WilsonBoxCover', 'UnifiedTheory.Clay.YangMills.WilsonAdaptiveBoxCover']
TARGETS = PREVIOUS_TARGETS + NEW_TARGETS
CHECK = 'scripts/CheckYangMillsJointBoxLocalization.lean'
PREVIOUS_REPORT = 'data/yang_mills_spatial_cut_dynamics_audit.json'
PREVIOUS_COUNT = 8372
NEW_COUNT = 77
SCOPE = 'Actual finite-cutoff SU(2) Wilson sources now admit joint localization on finite unions of high-energy blocks without charging the variance loss separately for each block. For continuous cutoffs chi_i, weights w_i=chi_i/sqrt(max(1,sum_j chi_j^2)) are continuous, inherit gauge invariance and support, have sum_i w_i^2<=1 everywhere, and sum_i w_i^2=1 wherever any chi_i=1. Actual reversibility and the two-step residual prove sum_i M(w_i*F)<=2*loss(F)+2*(sum_i q_i)*M(F) from the actual supported-input bounds. The block estimate is instantiated with q_i=exp(-beta*(R_i-8*b_i-4*(p_i+s_i)*e(beta))). For positive R_i, the actual weighted union event exists i:V_{S_i}>=2*R_i has the same bound. There is no independence or disjointness premise. Actual translation equivariance of four-link supports, internal plaquettes and crossing plaquettes transports the previous box bounds through the periodic seam. For L_i>=4096, L_i+1<=n and e(beta)<=1/96, arbitrary translated boxes, including different scales, have union error 2*sum_i exp(-beta*L_i^3/4)*M(F), while the loss coefficient remains two. All n^3 translates at a common scale have this explicit counting factor; if 3*log(n)<=beta*L^3/8 it is absorbed into 2*exp(-beta*L^3/8)*M(F). The adaptive threshold R(beta,L)=384*L^2+48*e(beta)*L^3 improves the retained density. For every beta>0, positive L and L+1<=n, actual box input rates at this threshold are <=exp(-192*beta*L^2). The union over all n^3 translates satisfies integral_bad F^2 dpi<=2*loss(F)+2*n^3*exp(-192*beta*L^2)*M(F). Under 3*log(n)<=96*beta*L^2 the error becomes 2*exp(-96*beta*L^2)*M(F). The hard threshold density 2*R/L^3=768/L+96*e(beta) tends to zero when L and beta tend to infinity. For bounded-mass approximate slow modes with loss tending to zero along an explicitly admissible regulator family, the actual weighted bad-union mass tends to zero as well. The adaptive event is nonempty at large L and weak coupling and excludes the flat field. This is an a priori concentration reduction, not a construction or exclusion of physical slow modes, nor a physical coupling trajectory or continuum limit. Sparse defects below the surface cost, retained-region physical coercivity and actual distant mixed-ground summability remain open.'
REMAINING = ['The adaptive threshold still contains a surface term. Isolated or sparse large plaquette defects can lie below it; the union theorem does not cover the whole axial FlatBox complement or prove every plaquette small.', 'Finite unions now pay actual loss only once. The mass errors still sum, and the all-translates result retains n^3 unless the explicit logarithmic-volume budget is supplied. This is not a fixed-beta, infinite-volume uniform estimate.', 'Different scales can be combined in any finite family. An infinite-scale or infinite-volume construction, summability over such a hierarchy and its physical scaling have not been established.', 'The square-partition weights are continuous and gauge invariant but generally depend on all cutoffs. No spatial locality of these weights or derivative/cutoff-energy bound is inferred.', 'The source estimate bounds f-squared L2 mass, paid by twice loss plus a small mass term. It is not the false loss-only variance-pair tail, and does not absorb the earlier local plaquette cutoff cost.', 'The slow-mode concentration theorem assumes bounded source mass, vanishing loss, growing beta and box size, geometric fit and the logarithmic-volume budget. It supplies no physical coupling trajectory and constructs no nontrivial continuum observable.', 'Approximate slow modes may remain in the region with low energy in every box. Prove a quantitative physical functional inequality there, including sparse defects and gauge geometry. Actual distant mixed-ground or signed physical Haar-form control and the independent global lower comparison remain open.', 'All twelve full Clay obligations, a nontrivial continuum Yang-Mills theory and its positive finite mass gap remain open.']


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
        CHECK, "scripts/yang_mills_joint_box_localization_audit.py", PREVIOUS_REPORT,
        "data/yang_mills_joint_box_localization_2026_10_30.json",
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
    logs = Path(tempfile.mkdtemp(prefix="unifiedtheory-yang-mills-joint-box-localization-audit-"))
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
    target = ROOT / "data/yang_mills_joint_box_localization_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print(f"Passed: {NEW_COUNT} fresh checks; {len(declarations)} cumulative; {target}")


if __name__ == "__main__":
    main()
