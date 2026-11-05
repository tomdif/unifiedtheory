#!/usr/bin/env python3
"""Check simultaneous planar patterns, original norm comparison and all-frame source counts; retain 8961 checks."""
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

from free_balanced_hamiltonian_audit import ROOT, STANDARD_AXIOMS, local_dependencies, sha256
from yang_mills_plaquette_localization_audit import TARGETS as PREVIOUS_TARGETS, proof_code

NEW_TARGETS = ['UnifiedTheory.Clay.YangMills.SpatialWilsonPatchWeights', 'UnifiedTheory.Clay.YangMills.SpatialWilsonPatchHistory', 'UnifiedTheory.Clay.YangMills.SpatialWilsonPatchNorm', 'UnifiedTheory.Clay.YangMills.WilsonPatchSourceDecay', 'UnifiedTheory.Clay.YangMills.WilsonPatchSourceTail', 'UnifiedTheory.Clay.YangMills.WilsonPatchCover', 'UnifiedTheory.Clay.YangMills.WilsonPatchCountTail', 'UnifiedTheory.Clay.YangMills.WilsonPatchSymmetry', 'UnifiedTheory.Clay.YangMills.WilsonAffinePatchCover', 'UnifiedTheory.Clay.YangMills.WilsonAllPatchCounts', 'UnifiedTheory.Clay.YangMills.WilsonPatchWitness']
TARGETS = PREVIOUS_TARGETS + NEW_TARGETS
CHECK = 'scripts/CheckYangMillsPlanarPatterns.lean'
PREVIOUS_REPORT = 'data/yang_mills_plaquette_localization_audit.json'
PREVIOUS_COUNT = 8961
NEW_COUNT = 114
SCOPE = 'Simultaneous deletion is proved for every finite set S of spatial plaquettes individually fixed by the same canonical midpoint reflection, with either periodic seam permitted. The whole omitted background is proved reflection invariant and its actual finite temporal history kernel is constructed. All other spatial plaquettes and every kinetic factor remain. Iterated exact SU(2) insertion gives m(s)^(card(T)*card(S))*Q_cut(f)<=Q_full(f), with the matching cap(s)^(card(T)*card(S)) removal bound, for arbitrary continuous complex half-history sources. The actual Haar partitions satisfy the same floor. The endpoint-chain dictionary and compact spectral-growth theorem then give m(beta)^card(S)*||T_cut,raw||<=||T_full|| and ||T_cut,raw||<=cap(beta)^card(S)*||T_full||. This is a simultaneous comparison against the original action; no unsupported iteration through nonsymmetric backgrounds occurs. For a source supported where every selected defect is >=R, M(PF)<=rho^card(S)*M(F), rho=cap(beta)^2*exp(-beta*R). The actual arbitrary-source hard-event bound is integral_(all D_p>=2R) F^2 dpi<=2*loss(F)+2*rho^card(S)*M(F). Square covers sum these pattern activities with one loss charge and give the matching supported-union one-step contraction. Counting every k-subset of an aligned reference set A gives the actual event of at least k hard defects with error choose(card(A),k)*rho^k. If card(A)<=b*k this is at most (2^b*rho)^k. Symmetry transport preserves the original full ground, source weight and loss, and an exact holonomy dictionary identifies every affine spatial translation/coordinate permutation. A common cover over all six permutations and all N^3 translations, N=2n, proves the full source tail with error 6*N^3*choose(card(A),k)*rho^k and one loss charge. Its density version has error 6*N^3*(2^b*rho)^k; at R=4*log(beta)/beta this is 6*N^3*(2^b*C/beta)^k with the previously proved constant C. The explicit activity/volume budget 2^b*rho<=exp(-c), log(6*N^3)+t<=c*k yields tail <=2*loss+2*exp(-t)*M and supported-source coercivity (1-exp(-t))*M<=loss. Nonvacuity is proved using an explicit field with every marked defect equal to four and a nonzero continuous gauge-invariant product bump supported in the simultaneous hard event for 0<R<2. Arbitrary noncoplanar three-dimensional cluster suppression, the actual distant mixed-ground sum or signed physical replacement, independent retained-region global coercivity, compatible physical scaling and nonzero continuum survival remain open; all twelve full Clay requirements remain open.'
REMAINING = ['All twelve full Clay requirements remain open. No full Yang-Mills construction, nonzero continuum limit or cutoff-uniform physical mass gap is claimed.', 'The simultaneous product activity rho^k is proved when all plaquettes in each pattern share one valid midpoint reflection; both periodic seams are allowed. Different patterns may be transported independently before taking their union. This does not give a product bound for a single arbitrary noncoplanar three-dimensional pattern.', 'The original full ground law and original full eigenvalue are retained. P is the actual raw stationary transition, with the established original-full agreement on physical sources. Raw and full kernels are not identified on arbitrary nonphysical sources.', 'The new bad-pattern lower bounds are one-step estimates on supported sources. Their supported space is not asserted invariant under P, and these estimates do not replace global lower coercivity for retained mean-zero physical sources.', 'All translations and orientations are controlled with one loss charge and an explicit 6*N^3 mass-error factor. The numeric activity/volume budget is proved sufficient, but a physical changing-regulator trajectory and appropriate patch sizes must still be established on the same continuum construction.', 'Nonzero physical supported sources exist for every nonempty marked patch when 0<R<2. The count event contains the explicit large field for k<=card(A), and excludes the flat field when R>0 and k>0. These are nonvacuity statements, not nonzero renormalized continuum survival.', 'Next prove an actual multicut reflection/chessboard or other original-action comparison for noncoplanar defect patterns and connected-cluster entropy. Do not multiply the separate plane estimates or silently delete through nonsymmetric backgrounds.', 'Actual distant mixed-ground summability or a compatible signed physical quadratic form, retained-region coercivity including global gauge/toron directions and source-dependent boundaries, and nonzero physical continuum survival remain independent targets.']


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
        CHECK, "scripts/yang_mills_planar_patterns_audit.py", PREVIOUS_REPORT,
        "data/yang_mills_planar_patterns_2026_10_30.json",
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
    logs = Path(tempfile.mkdtemp(prefix="unifiedtheory-yang-mills-planar-patterns-audit-"))
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
    target = ROOT / "data/yang_mills_planar_patterns_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print(f"Passed: {NEW_COUNT} fresh checks; {len(declarations)} cumulative; {target}")


if __name__ == "__main__":
    main()
