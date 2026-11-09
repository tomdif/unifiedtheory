#!/usr/bin/env python3
"""Check actual sourced patch-complement bounds; retain 10016 checks."""
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

from free_balanced_hamiltonian_audit import ROOT, STANDARD_AXIOMS, local_dependencies, sha256
from yang_mills_patch_disintegration_audit import TARGETS as PREVIOUS_TARGETS, proof_code

NEW_TARGETS = ['UnifiedTheory.Clay.YangMills.WilsonPatchLocalEnergy', 'UnifiedTheory.Clay.YangMills.CompactGibbsGaussianTail', 'UnifiedTheory.Clay.YangMills.WilsonPatchGaussianPartition', 'UnifiedTheory.Clay.YangMills.WilsonPatchComplementTail', 'UnifiedTheory.Clay.YangMills.WilsonPatchExponentialCovariance']
TARGETS = PREVIOUS_TARGETS + NEW_TARGETS
CHECK = 'scripts/CheckYangMillsPatchTail.lean'
PREVIOUS_REPORT = 'data/yang_mills_patch_disintegration_audit.json'
PREVIOUS_COUNT = 10016
NEW_COUNT = 39
SCOPE = 'The actual cap-complement probability in the unrestricted sourced middle interior law now has an explicit local energetic upper bound. The local middle energy L_S consists of every plaquette incident to S, including all crossings, and the two endpoint kinetic energies on S. The complementary exterior action is constant in the same interior coordinates and cancels exactly from the normalized estimate. Positivity of L_S and the previously proved global symmetric action bound yield L_S(v)<=2*L_S(v0)+36*D(v0,v) for any field with the same exterior, without a small-field assumption. The quaternion chord triangle inequality gives L_S(v)>=D(v0,v)-K_S(v0,u)-K_S(v0,w). Outside the radius-epsilon product cap, D>=epsilon^2. The centered reference Haar Gaussian has the exact partition mass(36*beta)^|S|, and the existing actual SU(2) Gaussian mass bound gives a per-active-link inverse factor C(beta)=cap(36*(beta+1))=864*scalarPartition(0)/Gamma(3/2)*(beta+1)*sqrt(beta+1). Only the reference Gaussian is factored. For a continuous perturbation R with |R|<=M, the full unrestricted interior cap-complement probability is at most exp(|S|*log C(beta)+beta*(2*V_incident(v0)+3*K_endpoints(v0,u,w)-epsilon^2)+2*M). This is proved for beta>=0, any nonnegative cap radius and every fixed exterior. The actual two Wilson insertions have M=4 and hence cost exp(8); the extra transported source has M=6 and cost exp(12), including overlaps. The existing unrestricted covariance transfer now gives explicit two-source and three-source covariance bounds with these exponential terms instead of an unevaluated complement probability, under the previous patch-curvature hypotheses. An additional explicit background-energy condition 2*V_incident+3*K_endpoints<=epsilon^2/2 yields exponent |S|*log C(beta)+2*M-beta*epsilon^2/2. That stronger eligibility condition is not asserted for all retained backgrounds and does not follow from the old cap-curvature hypotheses. No exterior-volume or boundary-depth term is introduced. The local covariance bound still grows with patch size and has no separation decay; retained exterior-response and endpoint-response covariances, background coverage in the matching response-weighted norm, the distant sum, global lower coercivity and all continuum obligations remain open. All twelve full Clay requirements remain open.'
REMAINING = ['All twelve full Clay requirements remain open; no continuum Yang-Mills construction or uniform physical mass gap is proved.', 'The new cap-complement bound is explicit but can exceed one on energetically ineligible backgrounds. The retained law has not been proved to give sufficient response-weighted coverage by eligible patches.', 'Small curvature defects on a fixed cap do not imply that the cap carries most unrestricted Gibbs mass. The new local background-energy cost is retained and must be controlled separately.', 'The previous cap covariance hypotheses are unchanged. Only after they and an adequate energetic margin hold is the new unrestricted covariance estimate quantitatively small.', 'The covariance bound grows with active patch cardinality and has no spatial-separation decay. It does not establish the dyadic far-sum premise.', 'Both exact retained covariance terms remain: spatial exterior responses inside the middle bridge and propagated endpoint responses. Their true partitions and messages remain in the measures.', 'The local kinetic lower energy bound is not a global lower coercivity or Poincare inequality for the physical transfer, including its center-even sector.', 'Existing stationary averaged bad-bridge estimates have not yet been connected to the new eligibility costs in the matching unrestricted source hierarchy.', 'Controlled physical coupling/time scaling, a suitable overlap margin, reflected compactness and nonzero continuum survival remain open.', 'No gauge-covariant Balaban block-RG construction, localized inverse decay estimate or full physical clustering theorem is claimed.']


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
        CHECK, "scripts/yang_mills_patch_tail_audit.py", PREVIOUS_REPORT,
        "data/yang_mills_patch_tail_2026_10_30.json",
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
    logs = Path(tempfile.mkdtemp(prefix="unifiedtheory-yang-mills-patch-tail-audit-"))
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
    target = ROOT / 'data/yang_mills_patch_tail_audit.json'
    target.write_text(json.dumps(report, indent=2) + "\n")
    print(f"Passed: {NEW_COUNT} fresh checks; {len(declarations)} cumulative; {target}")


if __name__ == "__main__":
    main()
