#!/usr/bin/env python3
"""Check temporal-history insertion, spatial column norm and isolated-defect source tails; retain 8742 checks."""
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

from free_balanced_hamiltonian_audit import ROOT, STANDARD_AXIOMS, local_dependencies, sha256
from yang_mills_spatial_reflection_audit import TARGETS as PREVIOUS_TARGETS, proof_code

NEW_TARGETS = ['UnifiedTheory.Clay.YangMills.SpatialTemporalLinkKernels', 'UnifiedTheory.Clay.YangMills.SpatialTemporalReflectionKernel', 'UnifiedTheory.Clay.YangMills.SpatialWilsonHistoryKernel', 'UnifiedTheory.Clay.YangMills.SU2FiniteInsertion', 'UnifiedTheory.Clay.YangMills.SpatialWilsonHistoryInsertion', 'UnifiedTheory.Clay.YangMills.FiniteKernelChain', 'UnifiedTheory.Clay.YangMills.FiniteKernelGrowth', 'UnifiedTheory.Clay.YangMills.KernelPartitionNorm', 'UnifiedTheory.Clay.YangMills.SpatialWilsonColumnTransfer', 'UnifiedTheory.Clay.YangMills.SpatialWilsonColumnNorm', 'UnifiedTheory.Clay.YangMills.WilsonPlaquetteColumnDecay', 'UnifiedTheory.Clay.YangMills.WilsonPlaquetteColumnTail']
TARGETS = PREVIOUS_TARGETS + NEW_TARGETS
CHECK = 'scripts/CheckYangMillsSpatialColumn.lean'
PREVIOUS_REPORT = 'data/yang_mills_spatial_reflection_audit.json'
PREVIOUS_COUNT = 8742
NEW_COUNT = 133
SCOPE = 'The actual raw temporal kinetic interaction is now a constructed positive kernel across the previously proved independent spatial midpoint halves, including both periodic seams. Each normal crossing temporal link is represented by two-time half-paths; all interior temporal factors are localized. Combining these factors with the actual spatial kernels proves reflection positivity for finite temporal Wilson networks, with arbitrary nonnegative reflection-invariant spatial couplings at each slice and arbitrary nonnegative kinetic couplings. Product half-history Haar measure pushes forward to the original coarse history Haar measure. Iterated exact SU(2) insertion gives m(s)^card(T)*Q_cut(f)<=Q_full(f), for every continuous complex half-history source, when one geometrically crossing spatial plaquette is omitted at all times; the polynomial removal price is cap(s)^card(T). The same inequality holds for actual coarse Haar partitions. A genuine finite-chain dictionary retains the full spatial endpoint weights. The compact positive cut transfer is constructed and its positivity is proved with continuous Hilbert features. A proved spectral-growth comparison uses a continuous complex top eigenfunction of the actual cut operator and the already constructed original full ground only for the upper comparison. Boundary prefactors disappear in the growth rate. This closes the previously open spatial column normalization: m(beta)*||T_cut,raw||<=||T_full|| and ||T_cut,raw||<=cap(beta)*||T_full|| for beta>=3/4, independently of spatial volume. No reflection premise or positive profile is supplied for the modified ground. For sources supported on the actual spatial plaquette defect D_p>=R, M(PF)<=cap(beta)^2*exp(-beta*R)*M(F). Reversibility and the existing two-step residual yield the arbitrary-source bound integral_(D_p>=2R) F^2 dpi<=2*loss(F)+2*cap(beta)^2*exp(-beta*R)*M(F), for R>0. Here pi is the actual full-ground law and P is the actual raw stationary transition, agreeing with the original full transition on the proved physical sector. This handles a single isolated spatial defect, without a defect-density threshold or exterior-volume cost. The distant mixed-ground/signed-form estimate, compatible independent global coercivity, physical scaling and nontrivial continuum survival remain open.'
REMAINING = ['The full Clay existence and mass-gap result is not proved; all twelve full requirements remain open. Neither a nonzero continuum limit nor a cutoff-uniform physical gap is constructed.', 'The new spatial column norm comparison is proved for a plaquette crossing the chosen spatial link-reflection plane on an even-period lattice. The theorem covers both periodic seams; extending it to every translated plaquette and orientation must use explicit spatial symmetry transport.', 'The raw cut transfer retains all temporal kinetic links and all spatial plaquettes except the same marked plaquette at every time. Its norm is compared to the original full gauge-averaged transfer norm. Raw and full kernels are not asserted identical on arbitrary nonphysical inputs.', 'The modified-ground reflection theorem has been bypassed for this norm comparison, not proved as a separate result. Do not reopen it as a prerequisite for the now-proved single-column price.', 'The source bound concerns the actual stationary squared mass, with the explicit loss coefficient two. It is not an arbitrarily small loss-only absorption bound and does not contradict the earlier physical plaquette-bump obstruction.', 'Finite families of bad-plaquette cutoffs need a justified joint cover and symmetry transport. An exponentially small one-plaquette mass error does not alone control an unbounded union or a physical changing-regulator trajectory.', 'The norm comparison for one reflection-fixed omitted column does not automatically iterate over arbitrary deleted columns: each subsequent background must satisfy the needed spatial reflection symmetry or have an independently proved replacement.', 'Actual distant mixed-ground summability or an appropriate signed physical form, retained-region physical coercivity including defect clusters, field-dependent boundary normalization beyond the proved single-column comparison, and nonzero physical continuum survival remain to be established.']


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
        CHECK, "scripts/yang_mills_spatial_column_audit.py", PREVIOUS_REPORT,
        "data/yang_mills_spatial_column_2026_10_30.json",
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
    logs = Path(tempfile.mkdtemp(prefix="unifiedtheory-yang-mills-spatial-column-audit-"))
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
    target = ROOT / "data/yang_mills_spatial_column_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print(f"Passed: {NEW_COUNT} fresh checks; {len(declarations)} cumulative; {target}")


if __name__ == "__main__":
    main()
