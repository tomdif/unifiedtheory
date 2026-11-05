#!/usr/bin/env python3
"""Check actual Haar-patch Gibbs fluctuations and covariance; retain 9881 checks."""
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

from free_balanced_hamiltonian_audit import ROOT, STANDARD_AXIOMS, local_dependencies, sha256
from yang_mills_patch_minimum_audit import TARGETS as PREVIOUS_TARGETS, proof_code

NEW_TARGETS = ['UnifiedTheory.Clay.YangMills.QuaternionRadialDoubling', 'UnifiedTheory.Clay.YangMills.QuaternionHaarDoubling', 'UnifiedTheory.Clay.YangMills.QuaternionCapContraction', 'UnifiedTheory.Clay.YangMills.FiniteProductContraction', 'UnifiedTheory.Clay.YangMills.CompactGibbsContractionMoment', 'UnifiedTheory.Clay.YangMills.WilsonChordPatchLaw', 'UnifiedTheory.Clay.YangMills.WilsonPatchFluctuation', 'UnifiedTheory.Clay.YangMills.WilsonPatchCovariance']
TARGETS = PREVIOUS_TARGETS + NEW_TARGETS
CHECK = 'scripts/CheckYangMillsPatchFluctuation.lean'
PREVIOUS_REPORT = 'data/yang_mills_patch_minimum_audit.json'
PREVIOUS_COUNT = 9881
NEW_COUNT = 75
SCOPE = 'The fixed-patch minimizer estimates now yield actual normalized Gibbs fluctuation and connected-covariance bounds. The proof constructs the homogeneous quaternion doubling map x -> norm(x)^(-1)*x*x and proves it is globally three-Lipschitz and norm-preserving. Hausdorff-measure image control and additive Haar uniqueness transfer this to the actual four-dimensional Euclidean volume with factor 81. The existing quaternion sphere/cone identification then proves that the inverse midpoint map q -> q*z^(-1)*q increases actual quaternion Haar image measure by at most 81. On a closed chord cap, midpoint contraction toward any cap point is continuous and injective, stays in the cap and has that map as its left inverse. The cap has positive Haar mass for positive radius; its normalization and boundary are retained. The normalized cap measure pushed through contraction is at most 81 times itself. This inequality tensorizes over the actual product of cap-coordinate measures, giving factor 81^|S|. The full sourced middle action is pulled back to these coordinates with the exterior fixed. Its unique constrained minimizer and the supported curvature coefficient kappa supply action decrease at least (kappa/4)*distanceSq under the same contracting map. Exact partition cancellation proves E(exp((kappa/4)*distanceSq))<=81^|S|, and Jensen gives E(distanceSq)<=4*|S|*log(81)/kappa. For the literal two-source action, kappa=2*beta-2 yields mean squared fluctuation<=2*|S|*log(81)/(beta-1). For the additionally transported source, kappa=2*beta-4 gives the same bound with beta-2. The proved local source difference bound and centered Cauchy-Schwarz give connected covariance<=8*|S|*log(81)/(beta-1) for the two original insertions under their actual normalized patch law, and <=8*|S|*log(81)/(beta-2) for the original/extra-source pair under the corresponding three-source patch law. The base hypotheses are unchanged: radius 1/256, incident base plaquette chords<=1/64, active base-to-endpoint chord distances<=1/2, beta-scaled rotations and source strengths in [0,1]; the original two source links are distinct and the extra source may overlap. The bounds are linear in patch cardinality and contain no total exterior-volume or boundary-depth factor. They do not decay in source separation. They concern the fixed capped Haar-coordinate Gibbs law, not the unrestricted middle or full boundary law. Controlling the cap complement, retained endpoint covariance, spatial propagation, independent global lower coercivity and continuum obligations remains open. All twelve full Clay requirements remain open.'
REMAINING = ['All twelve full Clay requirements remain open; no continuum Yang-Mills construction or uniform physical mass gap is proved.', 'The covariance bounds are for the normalized fixed-exterior Haar-cap Gibbs law with the actual sourced Wilson action. They do not bound the unrestricted middle or full boundary covariance.', 'The bound grows linearly with the number of active links and does not decay in source separation. It does not supply the spatial decay premise of the dyadic far-sum theorem.', 'The explicit base hypotheses still require small incident plaquette chords and active endpoint distances. Their coverage and the contribution of the cap complement remain to be controlled in the matching response-weighted energy.', 'The exact boundary recursion retains both averaged middle covariance and retained covariance of responses. The endpoint distribution retains spatialWeight(w), boundaryMessage_j(w) and the sourced middle partition.', 'The additionally transported source is included under the same capped law, even with overlapping links. A propagation estimate for the unrestricted source hierarchy is still missing.', 'The normalized fluctuation upper bounds do not establish the independent global lower coercivity inequality needed for transfer contraction, including the center-even physical sector.', 'This midpoint contraction argument is not a construction of Balaban gauge-covariant constrained block RG, its localized fluctuation expansion, or a full physical clustering theorem.', 'Existing averaged bad-bridge tails cannot simply replace uniform control for arbitrary boundary inputs or eliminate defective directions from global coercivity.', 'Controlled physical coupling/time scaling, a suitable overlap margin, reflected compactness and nonzero continuum survival remain open.']


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
        CHECK, "scripts/yang_mills_patch_fluctuation_audit.py", PREVIOUS_REPORT,
        "data/yang_mills_patch_fluctuation_2026_10_30.json",
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
    logs = Path(tempfile.mkdtemp(prefix="unifiedtheory-yang-mills-patch-fluctuation-audit-"))
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
    target = ROOT / 'data/yang_mills_patch_fluctuation_audit.json'
    target.write_text(json.dumps(report, indent=2) + "\n")
    print(f"Passed: {NEW_COUNT} fresh checks; {len(declarations)} cumulative; {target}")


if __name__ == "__main__":
    main()
