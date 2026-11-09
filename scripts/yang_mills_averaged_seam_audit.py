#!/usr/bin/env python3
"""Check averaged physical seam contraction and its certified floor; retain 9656 checks."""
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

from free_balanced_hamiltonian_audit import ROOT, STANDARD_AXIOMS, local_dependencies, sha256
from yang_mills_seam_penalty_audit import TARGETS as PREVIOUS_TARGETS, proof_code

NEW_TARGETS = ['UnifiedTheory.Clay.YangMills.WilsonGroundRowAveraging', 'UnifiedTheory.Clay.YangMills.WilsonSeamRateProfile', 'UnifiedTheory.Clay.YangMills.WilsonAveragedSeamContraction', 'UnifiedTheory.Clay.YangMills.WilsonSeamRateFloor']
TARGETS = PREVIOUS_TARGETS + NEW_TARGETS
CHECK = 'scripts/CheckYangMillsAveragedSeam.lean'
PREVIOUS_REPORT = 'data/yang_mills_seam_penalty_audit.json'
PREVIOUS_COUNT = 9656
NEW_COUNT = 55
SCOPE = 'The previous source-weighted sufficient condition is replaced by an unconditional improved finite-cutoff contraction rate in the physical center-odd sector. For W(u) equal to the clipped gauge-minimized seam coefficient, define the continuous physical profile r(u)=W(u)/(4+W(u)). The actual conditional response estimate, oddness of P f, and the exact row-variance formula give (P f(u))^2<=r(u)*P(f^2)(u). This requires no additional source-weighted bound. Detailed balance and Fubini for the original stationary ground law move the coefficient through the same physical transfer: Var(P f)<=integral f(v)^2*(P r)(v) d pi(v). Compactness constructs an attained maximum q_star=max_v(P r)(v). Consequently Var(P f)<=q_star*Var(f), with 0<=q_star<=q_raw<1 at every positive period and nonnegative coupling. Physical powers obey Var(P^k f)<=q_star^k*Var(f), and positive-variance physical odd eigenfunctions satisfy sigma^2<=q_star. For arbitrary physical sources the center-even variance remains explicitly in the partial-contraction bound. The new profile is strictly below q_raw at the identity whenever n>=4 and beta>0, because beta*pi^2*n<4*beta*n^2 there. Strict positivity of every actual transition row spreads this gain to every row, and compactness then proves q_star<q_raw unconditionally at each such finite cutoff. The certified margin equals the attained minimum over input rows of the actual full-transition expectation of 4/(4+W). No source is discarded and no auxiliary time step is substituted. The same construction has a proved limitation: for n>=4, beta>=0, nonnegative penalty and clipping imply r(u)>=q_base=((exp(beta*pi^2*n)-1)/(exp(beta*pi^2*n)+1))^2. The original Markov averaging preserves this floor, so q_star>=q_base and 1-q_star<=4*exp(-beta*pi^2*n). This is an upper bound on this certificate margin, not an upper bound on the actual spectral gap. It shows that averaging this particular likelihood-cap profile cannot remove the exponential linear-period cost; controlling the mismatch alone is insufficient. A physical-scale gap requires a stronger argument based on actual physical-score moments or multiscale response, plus center-even/global coercivity. The distant mixed-ground sum, retained propagation, bad-bridge complement, compatible physical scaling, nonzero continuum construction and all twelve full Clay requirements remain open.'
REMAINING = ['All twelve full Clay requirements remain open; no nonzero continuum Yang-Mills construction or uniform physical mass gap is proved.', 'The unconditional improvement is for continuous gauge-invariant center-odd sources. The center-even variance remains explicitly present for arbitrary physical sources.', 'The rate q_star is constructed as an attained maximum of the actual original physical transfer applied to a continuous geometric profile. No effective numerical or uniform lower bound on the size of its strict improvement is supplied.', 'Strict q_star<q_raw is proved for n>=4 and beta>0. The non-strict contraction and iteration hold for all positive periods and beta>=0.', 'The proved floor q_star>=q_base yields 1-q_star<=4*exp(-beta*pi^2*n). This caps the certified margin, not the actual spectral gap, and prevents this profile averaging from removing the linear-period exponential cost.', 'A physical gap need not require a contraction factor uniformly below one at each shrinking time step. It requires a suitable lower decay rate in physical time. This certificate does not supply that scaling and is inadequate on trajectories where exp(-beta*pi^2*n) is negligible compared with the physical time step.', 'An estimate of the actual physical likelihood/score variance or multiscale response is still needed to go beyond the capped profile. Further control of the noncommutation penalty alone cannot remove its zero-penalty floor.', 'The complete distant mixed logarithmic ground sum, retained propagation and bad-bridge-complement response remain open. The whole-seam form is not identified with the earlier local finite-rotation form.', 'Multiscale stability, physical coupling and time matching, normalized reflected-state compactness and nonzero renormalized continuum survival remain independent obligations.']


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
        CHECK, "scripts/yang_mills_averaged_seam_audit.py", PREVIOUS_REPORT,
        "data/yang_mills_averaged_seam_2026_10_30.json",
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
    logs = Path(tempfile.mkdtemp(prefix="unifiedtheory-yang-mills-averaged-seam-audit-"))
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
    target = ROOT / "data/yang_mills_averaged_seam_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print(f"Passed: {NEW_COUNT} fresh checks; {len(declarations)} cumulative; {target}")


if __name__ == "__main__":
    main()
