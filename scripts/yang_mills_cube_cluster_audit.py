#!/usr/bin/env python3
"""Check actual cube dissemination and arbitrary-pattern source activities; retain 9236 checks."""
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

from free_balanced_hamiltonian_audit import ROOT, STANDARD_AXIOMS, local_dependencies, sha256
from yang_mills_framed_chessboard_audit import TARGETS as PREVIOUS_TARGETS, proof_code

NEW_TARGETS = ['UnifiedTheory.Clay.YangMills.DyadicCellCoordinates', 'UnifiedTheory.Clay.YangMills.WilsonCubeCells', 'UnifiedTheory.Clay.YangMills.WilsonCubeReflection', 'UnifiedTheory.Clay.YangMills.WilsonCubeTransport', 'UnifiedTheory.Clay.YangMills.WilsonCubeChessboard', 'UnifiedTheory.Clay.YangMills.WilsonModifiedNormBounds', 'UnifiedTheory.Clay.YangMills.WilsonCubeNormBound', 'UnifiedTheory.Clay.YangMills.WilsonCubeCover', 'UnifiedTheory.Clay.YangMills.WilsonClusterNorm', 'UnifiedTheory.Clay.YangMills.WilsonClusterSourceDecay', 'UnifiedTheory.Clay.YangMills.WilsonClusterSourceTail', 'UnifiedTheory.Clay.YangMills.WilsonClusterCover', 'UnifiedTheory.Clay.YangMills.WilsonClusterActivity', 'UnifiedTheory.Clay.YangMills.WilsonClusterCountTail']
TARGETS = PREVIOUS_TARGETS + NEW_TARGETS
CHECK = 'scripts/CheckYangMillsCubeCluster.lean'
PREVIOUS_REPORT = 'data/yang_mills_framed_chessboard_audit.json'
PREVIOUS_COUNT = 9236
NEW_COUNT = 120
SCOPE = 'The actual Wilson six-plaquette cell family is encoded on fine spatial period 4*n, n>0. Exact dyadic coordinates prove disjointness, six plaquettes per cell, affine transport and the literal correspondence between fine plaquette half-copies and coarse binary-label half-copies. The previous finite block extremal theorem is now fully instantiated with the actual Wilson priced transfer norm, with all symmetry and Schwarz hypotheses discharged. The fully marked model is quantitatively bounded using the nonnegative modified kernel bound and the original full physical norm lower bound. An arbitrary collection of cells has actual deleted-transfer norm at most exp(48*beta*envelope(beta)*number_of_cells) times the original physical norm. Among eight parity shifts every plaquette is internal for exactly two, so any finite marked plaquette set S has a selected subset A with |S|<=4|A| and an actual translated cell cover C containing A whose norm price is at most exp(48*beta*envelope(beta)*|A|). The original full ground and eigenvalue give supported decay M(Pf)<=rho^|S| M(f), where rho=exp(-beta*(R-96*envelope(beta))/4), beta>0, R>=96*envelope(beta), and f vanishes whenever any marked plaquette defect is below R. This holds for arbitrary noncoplanar patterns with no alignment premise. For arbitrary continuous f, the source-weighted event that every marked defect is at least 2R has mass at most 2*loss(f)+2*rho^|S|*M(f). Arbitrary finite pattern families share one loss charge and sum their cardinality activities. Defect-count tails in any finite spatial region pay the explicit binomial entropy, with a density estimate (2^b*rho)^k when region cardinality<=b*k. At R=192*envelope(beta), R tends to zero and rho=exp(-24*beta*envelope(beta))<=1/(2*beta+5) tends to zero. These are finite-regulator actual-source statements. A connected-contour count and the required response/interaction expansions, distant mixed-ground sum or signed physical replacement, independent global coercivity, physical scale matching, nonzero continuum survival and all twelve full Clay requirements remain open.'
REMAINING = ['All twelve full Clay requirements remain open. No continuum Yang-Mills construction or cutoff-uniform physical mass gap is claimed.', 'The concrete six-plaquette Wilson block instantiation, fully disseminated norm comparison and bounded-loss arbitrary-plaquette cover are now proved; the previous framed-chessboard report listed these as open at that time.', 'The arbitrary-pattern suppression and source-weighted tails hold on fine spatial periods 4*n with n>0. No extension to every other finite period is silently asserted.', 'The source loss term is retained. Rare-event probability by itself does not control an arbitrary concentrated source; the new bound is 2*loss(f)+2*activity*M(f).', 'The finite pattern-family activity sum and binomial count estimates are proved. A uniform rooted connected-contour count and the response/interaction weights needed in the distant mixed-ground estimate are not supplied by cardinality suppression alone.', 'Independent retained-region/global coercivity remains open, including gauge/toron directions and source-dependent boundaries. The source decay on high-defect supports is not a coercivity theorem for every source.', 'Physical scaling, multiscale stability, normalized reflected-state compactness and nonzero renormalized continuum survival remain separate obligations.']


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
        CHECK, "scripts/yang_mills_cube_cluster_audit.py", PREVIOUS_REPORT,
        "data/yang_mills_cube_cluster_2026_10_30.json",
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
    logs = Path(tempfile.mkdtemp(prefix="unifiedtheory-yang-mills-cube-cluster-audit-"))
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
    target = ROOT / "data/yang_mills_cube_cluster_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print(f"Passed: {NEW_COUNT} fresh checks; {len(declarations)} cumulative; {target}")


if __name__ == "__main__":
    main()
