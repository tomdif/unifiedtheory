#!/usr/bin/env python3
"""Check transported bad-bridge response tails and finite-step scaled physical bounds; retain 9433 checks."""
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

from free_balanced_hamiltonian_audit import ROOT, STANDARD_AXIOMS, local_dependencies, sha256
from yang_mills_bridge_output_audit import TARGETS as PREVIOUS_TARGETS, proof_code

NEW_TARGETS = ['UnifiedTheory.Clay.YangMills.WilsonGroundEventTransport', 'UnifiedTheory.Clay.YangMills.WilsonBridgeRotationStability', 'UnifiedTheory.Clay.YangMills.WilsonBridgeResponseTail', 'UnifiedTheory.Clay.YangMills.WilsonBridgeScaledResponse']
TARGETS = PREVIOUS_TARGETS + NEW_TARGETS
CHECK = 'scripts/CheckYangMillsBridgeResponseTail.lean'
PREVIOUS_REPORT = 'data/yang_mills_bridge_output_audit.json'
PREVIOUS_COUNT = 9433
NEW_COUNT = 27
SCOPE = 'Actual squared finite-difference response on bad-bridge events is now controlled, with the original ground density and source retained. An exact change-of-variables formula transports a measurable event under a fixed single-link rotation. If the event and its rotated image lie in F, its restricted squared difference is bounded by 2*(exp(36*beta*displacement)+1) times the F-weighted source mass. Every actual spatial plaquette defect changes by at most eight times that displacement, including periodic degeneracies. A high-defect bridge at threshold 2*(R+4*r) survives any such rotation of displacement<=r as a bridge at threshold 2*R, with the same connected witness and endpoints. For a fixed root p, m>0 and one fixed link rotation per target plaquette z, define E_bad(f) as the sum over all z with graph distance(p,z)+1>=m of integral_[bridge p to z] (f(shift_z u)-f(u))^2 d(pi). At threshold 2*(R+4*r), E_bad(f)<=2*(exp(36*beta*r)+1)*C_m(f;R), where C_m is the proved summed bad-bridge source mass. Consequently E_bad(Pf)<=2*(exp(36*beta*r)+1)*B(2*rho,m)*M(f), for beta>0, R>0, R>=96*envelope(beta), 512*rho<1, on spatial periods 4*n. For beta>=512, rotations of displacement<=(36*beta)^(-1), and R=192*envelope(beta), the response event uses bufferedThreshold=R+4/(36*beta), which tends to zero. The full gauge-averaged transition version is explicit for gauge-invariant sources. Exact slow eigenfunctions Pf=sigma*f with sigma^2>=1/2 inherit the original-source bound. The entire preexisting WilsonCollectiveGram energy for this same family is exactly the sum of this bad-bridge response and its event-complement response. Keeping the power 224 in the exact activity exponent gives rho<=(2*beta+5)^(-224), hence E_bad(f)<=[16*(exp(1)+1)/(2*beta+5)^224]*(1/2)^(m-1)*M(f) for slow eigenfunctions. Even after multiplication by the inverse reference rotation scale squared, (36*beta)^2*E_bad(f)<=[20736*(exp(1)+1)/(2*beta+5)^222]*(1/2)^(m-1)*M(f), including an explicit physical-transition eigenfunction theorem. The root is fixed, rotations can depend on the target but not on the background configuration, and the scaling is the reference finite step rather than the actual displacement of every rotation. The event complement is not assumed to be entirely small-field: it can contain defects and disconnected bad clusters. No bound on that complement, the complete mixed-ground covariance sum, or independent global coercivity is proved. The finite-boundary covariance representation was already accepted. Relating its retained propagation and these source-energy estimates remains the next analytic task. No physical mass gap or nonzero continuum construction is claimed; all twelve full Clay requirements remain open.'
REMAINING = ['All twelve full Clay requirements remain open. No nonzero continuum Yang-Mills construction or cutoff-uniform physical mass gap is claimed.', 'The new estimate controls actual source finite-difference energy restricted to bad-bridge events. It is not a bound on the complete mixed logarithmic ground response or every off-diagonal Gram entry.', 'The exact energy split retains its entire complementary term. Absence of a bridge from the chosen root does not imply that all retained plaquettes are small-field; other defects and disconnected clusters can remain.', 'The root is fixed. Bounds uniform for each root do not by themselves justify summing over every root without another normalization or overlap argument.', 'Rotations are fixed per target and independent of the background configuration. No measure-preserving or bounded-Jacobian claim is made for adaptive masked rotations.', 'The arbitrary-source estimate applies to P f. Original-source estimates use an exact eigenfunction equation and sigma^2>=1/2. The general source-loss terms from earlier work are not discarded.', 'P denotes the normalized raw step with the original physical ground and eigenvalue. Full gauge-averaged transition statements explicitly require gauge invariance.', 'The factor (36*beta)^2 is the inverse reference finite-step scale squared. This does not establish an infinitesimal derivative estimate, a continuum normalization, or a functional inequality.', 'The analytic estimates hold on periods 4*n. Distance is discrete plaquette-graph distance. The buffered defect threshold tends to zero, but this alone supplies no physical scale matching.', 'Uniform retained-field response, a justified binding to the finite-boundary connected-covariance formula, and independent global coercivity with gauge/toron and boundary effects remain open.', 'Multiscale stability, a compatible physical coupling trajectory, normalized reflected-state compactness and nonzero renormalized continuum survival remain separate obligations.']


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
        CHECK, "scripts/yang_mills_bridge_response_tail_audit.py", PREVIOUS_REPORT,
        "data/yang_mills_bridge_response_tail_2026_10_30.json",
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
    logs = Path(tempfile.mkdtemp(prefix="unifiedtheory-yang-mills-bridge-response-tail-audit-"))
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
    target = ROOT / "data/yang_mills_bridge_response_tail_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print(f"Passed: {NEW_COUNT} fresh checks; {len(declarations)} cumulative; {target}")


if __name__ == "__main__":
    main()
