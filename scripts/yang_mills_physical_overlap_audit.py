#!/usr/bin/env python3
"""Check optimal physical contrast and harmonic-overlap contraction; retain 9711 checks."""
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

from free_balanced_hamiltonian_audit import ROOT, STANDARD_AXIOMS, local_dependencies, sha256
from yang_mills_averaged_seam_audit import TARGETS as PREVIOUS_TARGETS, proof_code

NEW_TARGETS = ['UnifiedTheory.Clay.YangMills.CompactPairedDensity', 'UnifiedTheory.Clay.YangMills.WilsonCenterContrast', 'UnifiedTheory.Clay.YangMills.WilsonContrastMoment', 'UnifiedTheory.Clay.YangMills.WilsonOverlapContraction', 'UnifiedTheory.Clay.YangMills.WilsonCenterFixedOrbit']
TARGETS = PREVIOUS_TARGETS + NEW_TARGETS
CHECK = 'scripts/CheckYangMillsPhysicalOverlap.lean'
PREVIOUS_REPORT = 'data/yang_mills_averaged_seam_audit.json'
PREVIOUS_COUNT = 9711
NEW_COUNT = 66
SCOPE = 'The earlier capped profile is replaced by the actual normalized contrast of the original full physical transition rows. Set p(v)=T(u,v), q(v)=T(Ju,v), s_u(v)=(p(v)-q(v))/(p(v)+q(v)), and theta(u)=integral p(v)*s_u(v)^2 d Haar(v). The full kernel and transition obey actual simultaneous center symmetry. The contrast is jointly continuous, gauge invariant in both variables, center-odd in each variable, symmetric under exchanging inputs, and strictly bounded in absolute value by one. Exact center symmetry cancels all ground factors from the contrast ratio, giving s_u(v)=(K(u,v)-K(Ju,v))/(K(u,v)+K(Ju,v)), with temporal Haar integration retained. A paired-density weighted Cauchy-Schwarz theorem gives (Pf(u))^2<=theta(u)*P(f^2)(u) for every continuous physical center-odd source. The contrast itself is an admissible source and satisfies P(s_u)(u)=P(s_u^2)(u)=theta(u). Consequently, for any C>=0, theta(u)<=C if and only if the corresponding row inequality holds for all continuous physical odd sources at that fixed input. This establishes exact optimality of the row coefficient, not of the global operator bound. Theta is continuous, gauge invariant and center-even, and is bounded above by the earlier profile r(u). Its complement is the exact harmonic overlap integral 2*p*q/(p+q). The explicit kernel H(u,v)=2*K(u,v)*K(Ju,v)/(K(u,v)+K(Ju,v)) is jointly continuous, pointwise strictly positive and symmetric, and 1-theta(u)=integral H(u,v)*g(v)/(lambda*g(u)) d Haar(v) with the original ground and eigenvalue. Reversibility gives actual physical odd-sector contraction with q_overlap=max(P theta), including iteration in the original clock and an explicit center-even remainder for arbitrary physical sources. The maximum is attained, 0<=q_overlap<=q_previous<1, and the margin is the attained least original-transfer average of harmonic overlap. No quantitative physical-scale lower bound for this margin is proved. An explicit flat seam carrying quaternion i is center-twisted into a gauge-equivalent field by constant quaternion j conjugation. Its contrast and theta vanish at every nonnegative coupling, and every positive theta threshold has a positive-ground-measure open neighborhood at finite cutoff. At positive coupling this theta value is strictly below the earlier positive base profile floor. Thus that pointwise floor is not intrinsic to the actual contrast moment; this example does not show the new global maximum lies below the old base rate. No uniform neighborhood mass, reflection positivity of H, or new multiscale estimate is assumed. The center-even sector, complete distant mixed-ground sum, retained propagation, bad-bridge complement, physical time/coupling scaling, nonzero continuum construction and all twelve full Clay requirements remain open.'
REMAINING = ['All twelve full Clay requirements remain open; no nonzero continuum Yang-Mills construction or uniform physical mass gap is proved.', 'The contrast moment is the exact optimal coefficient for the stated pointwise row inequality over continuous physical odd sources. It is not proved to equal the optimal global contraction factor or actual spectral radius.', 'The new global certificate is no worse than the previous averaged certificate. No strict improvement over that previous global certificate, or quantitative physical-scale margin, is established.', 'The flat fixed-orbit example proves theta=0 and refutes the previous positive pointwise profile floor for theta. It does not prove q_overlap<q_base, or exclude a global lower floor by other arguments.', 'Positive-ground-measure small-theta neighborhoods exist at each finite cutoff, but no probability lower bound uniform in coupling or volume is supplied.', 'The ground cancels from the contrast ratio, not from theta or the harmonic-overlap integral. Their original ground and transfer normalization remain present.', 'The harmonic kernel is continuous, symmetric and pointwise strictly positive. Positive semidefiniteness, reflection positivity, locality or a suitable multiscale representation for that new kernel is not established.', 'The extra transfer average in the coefficient follows from reversibility. The contraction theorem concerns one original physical step and does not replace its clock with an auxiliary chain.', 'The actual averaged overlap needs a quantitative lower bound on the physical time scale. A per-cutoff factor below one does not provide that scaling.', 'The center-even variance remains for arbitrary physical sources. Complete distant mixed-ground summation, retained propagation, bad-bridge-complement response and independent global coercivity remain open.', 'Compatible physical coupling/time scaling, normalized reflected-state compactness and nonzero renormalized continuum survival remain independent obligations.']


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
        CHECK, "scripts/yang_mills_physical_overlap_audit.py", PREVIOUS_REPORT,
        "data/yang_mills_physical_overlap_2026_10_30.json",
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
    logs = Path(tempfile.mkdtemp(prefix="unifiedtheory-yang-mills-physical-overlap-audit-"))
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
    target = ROOT / "data/yang_mills_physical_overlap_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print(f"Passed: {NEW_COUNT} fresh checks; {len(declarations)} cumulative; {target}")


if __name__ == "__main__":
    main()
