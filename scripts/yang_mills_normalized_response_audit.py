#!/usr/bin/env python3
"""Check normalized actual Wilson response and local factorization budget; preserve 7521 prior checks."""
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

from free_balanced_hamiltonian_audit import ROOT, STANDARD_AXIOMS, local_dependencies, sha256
from yang_mills_haar_budget_audit import TARGETS as PREVIOUS_TARGETS, proof_code

NEW_TARGETS = ['UnifiedTheory.Clay.YangMills.CompactNormalizedLikelihood', 'UnifiedTheory.Clay.YangMills.WilsonNormalizedResponse', 'UnifiedTheory.Clay.YangMills.WilsonGroundLocalBudget', 'UnifiedTheory.Clay.YangMills.WilsonNormalizedBudget']
TARGETS = PREVIOUS_TARGETS + NEW_TARGETS
CHECK = 'scripts/CheckYangMillsNormalizedResponse.lean'
PREVIOUS_REPORT = 'data/yang_mills_haar_budget_audit.json'
PREVIOUS_COUNT = 7521
NEW_COUNT = 40
SCOPE = 'Exact mean-one likelihood normalization improves the actual raw Wilson one-link response coefficient to (exp(4*beta*d)-1)^2/(4*exp(4*beta*d)), d=norm(q-1). The common partition ratio is retained to obtain an unnormalized range ratio exp(4*beta*d), and Bhatia-Davis plus Cauchy-Schwarz gives the result. It is propagated through the actual stationary variance loss, the same full-Haar family and the existing conditional slab contraction. The improved Haar cap is B(beta)=(exp(8*beta)-1)^2/(4*exp(8*beta)). Independently, conditional energy vanishes outside a source support, and an actual positive-variance four-link physical plaquette forces every valid nonnegative ground-law factorization constant to obey A>=1/4. On the diagnostic path beta_m=log(m+2)/8, k=m+1, B=k^2/(4*(k+1)), between k/8 and k/4. A cap r<1 on the improved summed proof coefficient requires (1-r)*N_links<=32*r. Therefore this improved summed bound still admits no uniform strict cap along unbounded spatial link counts, including n_m=m+2. The obstruction concerns a proved upper-bound coefficient, not the actual transfer spectral ratio. It does not disprove a mass gap. All twelve full Clay obligations remain open.'
REMAINING = ['The actual response upper estimate is sharper, but still pays a separate variance charge for every link. Collective physical correlations or another response family with matching lower control are still needed.', 'The new A>=1/4 lower constraint rules out canceling the link-count factor by an A of order 1/N_links. It does not prove any upper factorization bound for the actual ground law.', 'The bounded-budget sufficient cap C/(4+C) assumes A*N_links<=C. Such a common C cannot hold at unbounded spatial volume under the proved actual factorization constraint.', 'No lower bound on the actual transfer spectral ratio, vanishing actual gap, or nonexistence of Yang-Mills follows from failure of this proof coefficient.', 'The logarithmic path is diagnostic, not an independently established physical coupling trajectory. No obstruction for every logarithmic slope or for genuinely collective upper bounds is asserted.', 'The distant mixed-ground sum, a uniform canonical physical Gram estimate compatible with the Haar family, and actual ground-law factorization remain open.', 'No surviving continuum observable, nontrivial continuum Yang-Mills measure with full axioms, or uniform positive physical mass gap has been constructed. All twelve full Clay obligations remain open.']


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
        CHECK, "scripts/yang_mills_normalized_response_audit.py", PREVIOUS_REPORT,
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
    ]))
    hashes = {p: sha256(ROOT / p) for p in sources}
    root = (ROOT / "UnifiedTheory.lean").read_text()
    if not all(f"import {target}\n" in root for target in TARGETS):
        raise RuntimeError("Missing root import")
    env = os.environ.copy()
    env.pop("LEAN_PATH", None)
    env["LEAN_NUM_THREADS"] = "2"
    logs = Path(tempfile.mkdtemp(prefix="unifiedtheory-yang-mills-normalized-response-audit-"))
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
    target = ROOT / "data/yang_mills_normalized_response_audit.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print(f"Passed: {NEW_COUNT} fresh checks; {len(declarations)} cumulative; {target}")


if __name__ == "__main__":
    main()
