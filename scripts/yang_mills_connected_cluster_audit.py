#!/usr/bin/env python3
"""Check rooted connected-pattern entropy and actual source-weighted bad bridges; retain 9360 checks."""
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

from free_balanced_hamiltonian_audit import ROOT, STANDARD_AXIOMS, local_dependencies, sha256
from yang_mills_physical_cluster_audit import TARGETS as PREVIOUS_TARGETS, proof_code

NEW_TARGETS = ['UnifiedTheory.Clay.YangMills.FiniteConnectedTours', 'UnifiedTheory.Clay.YangMills.FiniteConnectedCount', 'UnifiedTheory.Clay.YangMills.WilsonPlaquetteGraph', 'UnifiedTheory.Clay.YangMills.WilsonConnectedActivity', 'UnifiedTheory.Clay.YangMills.FiniteConnectedDistance', 'UnifiedTheory.Clay.YangMills.WilsonConnectedSource', 'UnifiedTheory.Clay.YangMills.WilsonConnectedWeakCoupling', 'UnifiedTheory.Clay.YangMills.WilsonBadClusterBridge']
TARGETS = PREVIOUS_TARGETS + NEW_TARGETS
CHECK = 'scripts/CheckYangMillsConnectedCluster.lean'
PREVIOUS_REPORT = 'data/yang_mills_physical_cluster_audit.json'
PREVIOUS_COUNT = 9360
NEW_COUNT = 54
SCOPE = 'Every finite connected induced vertex set S containing a root has a closed walk visiting precisely S with length 2*(|S|-1). The proof constructs the tour by inserting adjacent unused vertices, using the actual induced-graph connectivity hypothesis. Fixed-endpoint walks of length L in a graph of degree at most D number at most D^L. Hence rooted connected k-sets number at most D^(2*(k-1)). The actual spatial Wilson plaquette graph is constructed with adjacency exactly shared spatial-link incidence between distinct plaquettes. Its degree is at most 16 for every positive period, including periodic degeneracies; thus at most 256^(k-1) connected k-plaquette sets contain a fixed plaquette, without an exterior-volume factor. An explicit finite size-indexed family includes every rooted connected set of size at least m. Its activity sum is bounded by B(rho,m)=rho*(256*rho)^(m-1)/(1-256*rho), for m>0, rho>=0 and 256*rho<1, independently of spatial period. On fine period 4*n this is combined with the previously proved actual arbitrary-pattern activity rho=exp(-beta*(R-96*envelope(beta))/4), beta>0 and R>=96*envelope(beta). The event of a rooted connected cluster of at least m plaquettes, all with defect>=2R, has original-ground squared-source mass at most 2*loss(f)+2*B(rho,m)*M(f). Sources supported on that event have normalized raw-step decay at most B(rho,m)*M(f), and lower loss (1-B)*M(f). All cluster sizes are summed with one loss charge. A finite connected set containing two plaquettes has cardinality greater than their actual plaquette-graph distance d; consequently the event of an all-high-defect connected cluster joining them has source mass at most 2*loss(f)+2*rho*(256*rho)^d/(1-256*rho)*M(f). For beta>=256 and R=192*envelope(beta), 256*rho<=1/2 and the bridge mass-error term is at most [4/(2*beta+5)]*(1/2)^d*M(f). This threshold vanishes at weak coupling by the preceding proved envelope limit. The normalized raw step and its loss use the original physical ground and eigenvalue. Full gauge-averaged transition corollaries are explicit for gauge-invariant sources. The connected bad-pattern count and its actual source activity are now proved; this does not represent or bound the distant mixed logarithmic ground response. The remaining response/interaction expansion or signed physical comparison, independent global coercivity, physical scaling and nonzero continuum survival are still open, as are all twelve full Clay requirements.'
REMAINING = ['All twelve full Clay requirements remain open. No continuum Yang-Mills construction or cutoff-uniform physical mass gap is claimed.', 'The uniform rooted connected-pattern count and summed actual bad-pattern activity are now proved; the preceding physical-cluster report listed the connected count as open at that time.', 'The graph is the actual spatial plaquette shared-link graph. Its distance is a discrete lattice graph distance, not a physical continuum distance. Analytic source estimates here hold on fine periods 4*n with n>0.', 'Arbitrary continuous sources use the normalized raw step with the original physical ground and eigenvalue; equality to the full gauge-averaged transfer is used only for gauge-invariant sources, with that hypothesis explicit.', 'The source-weighted tail retains 2*loss(f). Only its mass-error term decays exponentially with cluster size or distance. No bound on arbitrary-source correlations or global spectral gap follows by discarding the loss term.', 'The bad-cluster bridge event is not identified with the distant mixed logarithmic ground response. A proved response/interaction representation or a suitable signed physical comparison is still required before the new entropy bounds control that response.', 'Independent global retained-region coercivity, including gauge/toron and source-dependent boundary effects, is still open. High-defect-supported loss bounds are not coercivity for every physical source.', 'Multiscale stability, physical scale matching, normalized reflected-state compactness and nonzero renormalized continuum survival remain separate obligations.']


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
        CHECK, "scripts/yang_mills_connected_cluster_audit.py", PREVIOUS_REPORT,
        "data/yang_mills_connected_cluster_2026_10_30.json",
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
    logs = Path(tempfile.mkdtemp(prefix="unifiedtheory-yang-mills-connected-cluster-audit-"))
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
    target = ROOT / "data/yang_mills_connected_cluster_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print(f"Passed: {NEW_COUNT} fresh checks; {len(declarations)} cumulative; {target}")


if __name__ == "__main__":
    main()
