#!/usr/bin/env python3
"""Check all-input physical seam comparison and source-weighted response; retain 9590 checks."""
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

from free_balanced_hamiltonian_audit import ROOT, STANDARD_AXIOMS, local_dependencies, sha256
from yang_mills_flat_seam_audit import TARGETS as PREVIOUS_TARGETS, proof_code

NEW_TARGETS = ['UnifiedTheory.Clay.YangMills.WilsonSeamCommutatorGeometry', 'UnifiedTheory.Clay.YangMills.WilsonSeamCommutatorComparison', 'UnifiedTheory.Clay.YangMills.WilsonSeamGaugePenalty', 'UnifiedTheory.Clay.YangMills.WilsonPhysicalSeamResponse']
TARGETS = PREVIOUS_TARGETS + NEW_TARGETS
CHECK = 'scripts/CheckYangMillsSeamPenalty.lean'
PREVIOUS_REPORT = 'data/yang_mills_flat_seam_audit.json'
PREVIOUS_COUNT = 9590
NEW_COUNT = 66
SCOPE = 'The distributed-seam comparison is extended from the identity input gauge orbit to every input and output of the original full physical Wilson transition. For a fixed rotation q and fixed gauge h, the actual opposite fields gauge_h(Ju) and gauge_(h inverse)(Ju) have exactly the same full kernel and unchanged spatial potential. Their mismatch with q*u and q inverse*u is retained as the sum of two actual link inputCosts. The kinetic second difference is at most twice cost(q) plus twice this mismatch, and the temporal Haar midpoint inequality gives exp(-beta*(cost(q)+mismatch(u)))*K(u,v)<=K(Ju,v). Mismatch is center-invariant, yielding the reverse bound. The explicit distributed root has cost<=pi^2*n, so the full physical likelihood lies in exp(plus or minus beta*(pi^2*n+rootMismatch(u))) for all inputs and outputs, with the original ground retained. Every common-axis input has zero mismatch without a flatness requirement. Compactness constructs an attained minimum delta(u) of rootMismatch over spatial gauge representatives. This minimum value, not the chosen minimizer, is proved continuous, gauge invariant and center invariant. It vanishes on every orbit with a representative commuting linkwise with the root. The same likelihood bound holds with delta(u); the optimizer only evaluates an invariant transition and performs no adaptive change of integration variables. For each epsilon>0 the open set delta<epsilon has positive actual ground-law measure at every finite cutoff, with no quantitative uniform lower mass supplied. For physical sources, the full likelihood has mean one under the actual raw row law and reproduces the original full transition response. Its variance is at most (L(u)-1)^2/L(u), L(u)=exp(beta*(pi^2*n+delta(u))). Clipping this coefficient by the earlier global raw coefficient gives a continuous physical weight W(u). The same whole-seam energy now satisfies E_J(Pf)<=integral W(u)*Var_row_u(f) d pi(u)<=C_raw*loss(f). The exact odd-sector coercivity gives 4*Var(Pf)<=that source-weighted integral. If that integral is at most C*loss(f), with C>=0, the actual physical odd-sector contraction rate is C/(4+C). The weighted bound is a sufficient hypothesis, not a newly proved uniform estimate. In particular no unweighted mean penalty is substituted, the positive-measure neighborhood has no uniform probability estimate, and the remaining beta*pi^2*n cost still diverges on many trajectories even at zero mismatch. The complete distant mixed-ground sum, center-even coercivity, retained propagation, bad-bridge complement, cutoff-uniform physical gap, nonzero continuum construction and all twelve full Clay requirements remain open.'
REMAINING = ['All twelve full Clay requirements remain open; no cutoff-uniform physical mass gap or nonzero continuum construction is proved.', 'The all-input comparison retains an explicit noncommutation penalty. No small weighted ground-law average of its coefficient is proved.', 'The optimized penalty is continuous and has positive-measure small sublevel sets at each finite cutoff, but no quantitative lower mass uniform in volume or coupling is established.', 'The needed bound is integral W(u)*Var_row_u(f) d pi(u)<=C*loss(f), for the actual source. An unweighted mean of W or the penalty does not imply this bound.', 'Even zero penalty leaves the exponent beta*pi^2*n. Controlling only noncommutation cannot by itself make this pointwise coefficient cutoff-uniform. Source-weighted physical-score or multiscale estimates and physical time scaling remain necessary.', 'The odd-sector conditional rate C/(4+C) is proved only from the explicitly stated weighted estimate. No improved cutoff-uniform C is supplied, and the center-even sector is retained.', 'A continuous minimum value is proved; continuity of a chosen minimizer is not. The optimizer evaluates an invariant kernel and authorizes no adaptive Haar substitution.', 'Zero penalty is proved for inputs with a representative commuting linkwise with the chosen root, including nonflat common-axis fields. No classification of all flat holonomy moduli is supplied.', 'The whole-seam response is not identified with the earlier local finite-rotation energy. The complete distant mixed logarithmic ground sum, retained propagation and bad-bridge-complement response remain open.', 'Multiscale stability, a compatible physical coupling trajectory, normalized reflected-state compactness and nonzero renormalized continuum survival remain separate obligations.']


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
        CHECK, "scripts/yang_mills_seam_penalty_audit.py", PREVIOUS_REPORT,
        "data/yang_mills_seam_penalty_2026_10_30.json",
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
    logs = Path(tempfile.mkdtemp(prefix="unifiedtheory-yang-mills-seam-penalty-audit-"))
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
    target = ROOT / "data/yang_mills_seam_penalty_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print(f"Passed: {NEW_COUNT} fresh checks; {len(declarations)} cumulative; {target}")


if __name__ == "__main__":
    main()
