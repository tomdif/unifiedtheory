#!/usr/bin/env python3
"""Audit the global neutral spacetime force and weak balance on every real interval.

Run with the repository toolchain and verified dependency overlay:
  lake env python3 scripts/physical_clock_floor_neutral_global_spacetime_audit.py --overlay PATH

Sequential direct Lean checks rebuild six new modules, audit their axioms,
check the root import, and preserve the preceding source hash chain.
This does not invoke lake build and is not a TOE certificate.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess


MODULES = [('KFCausalCompatibleMeasureGluing', 7), ('KFCausalSpacetimeExhaustion', 8), ('KFCausalGlobalSpacetimeForce', 10), ('KFCausalGluedSpacetimeForce', 11), ('KFCausalNeutralGlobalForceLimit', 5), ('KFCausalNeutralGlobalSpacetimeDynamics', 1)]


STANDARD_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--overlay', required=True, type=Path)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    overlay = args.overlay.resolve()
    assert 'LEAN_PATH' in os.environ, 'Run with lake env python3.'
    assert overlay.is_dir(), 'Use the verified dependency overlay.'
    env = os.environ.copy()
    env['LEAN_PATH'] = str(overlay)+os.pathsep+env['LEAN_PATH']
    logs = overlay/'physical-clock-floor-neutral-global-spacetime-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_neutral_spacetime_consistency_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_neutral_global_spacetime_audit.py']
    hashes = {p: sha256(root/p) for p in sources}
    assert all(hashes[p] == h for p, h in previous['source_sha256'].items())
    root_hash = sha256(root/'UnifiedTheory.lean')
    root_text = (root/'UnifiedTheory.lean').read_text()
    appended_imports = ''.join('import UnifiedTheory.Audit.'+name+'\n' for name, _ in MODULES)
    assert root_text.endswith(appended_imports), 'Expected only the new appended root imports.'
    assert hashlib.sha256(root_text[:-len(appended_imports)].encode()).hexdigest() == previous['root_check']['source_sha256']
    for name, _ in MODULES:
        assert 'import UnifiedTheory.Audit.'+name in root_text

    checks = []
    for name, count in MODULES:
        source = 'UnifiedTheory/Audit/'+name+'.lean'
        command = ['lean', '-j1', '-o', str(overlay/'UnifiedTheory/Audit'/f'{name}.olean'), source]
        result = subprocess.run(command, cwd=root, env=env, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        log = logs/(name+'.log')
        log.write_text(result.stdout)
        assert result.returncode == 0, f'{name}: exit {result.returncode}; see {log}'
        assert not re.search(r': error|: warning|sorryAx', result.stdout), str(log)
        audits = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", result.stdout)
        assert len(audits) == count, (name, len(audits), count)
        declarations = {}
        for declaration, axioms in audits:
            used = {s.strip() for s in axioms.split(',') if s.strip()}
            assert used <= STANDARD_AXIOMS, (declaration, used)
            declarations[declaration] = sorted(used)
        checks.append(dict(source=source, command=command, exit_code=result.returncode,
                           log_sha256=sha256(log), audited_declarations=declarations))
        print(name, ': compiled;', count, 'standard-axiom audits', flush=True)

    result = subprocess.run(['lean', '-j1', 'UnifiedTheory.lean'], cwd=root, env=env, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    log = logs/'root-import.log'
    log.write_text(result.stdout)
    assert result.returncode == 0 and not result.stdout.strip(), str(log)
    assert root_hash == sha256(root/'UnifiedTheory.lean'), 'Root changed during verification.'
    assert previous_hash == sha256(previous_path), 'Previous report changed during verification.'
    assert all(sha256(root/p) == h for p, h in hashes.items()), 'Sources changed during verification.'
    report = dict(
        modules=checks, root_check=dict(command=['lean', '-j1', 'UnifiedTheory.lean'], exit_code=0,
            empty_log=True, source_sha256=root_hash, log_sha256=sha256(log)),
        audited_declaration_count=sum(n for _, n in MODULES), source_sha256=hashes,
        previous_report=dict(path=str(previous_path.relative_to(root)), sha256=previous_hash),
        lean_toolchain=(root/'lean-toolchain').read_text().strip(),
        scope='Compatible positive measures on a countable measurable cover are glued by summing their restrictions to disjoint pieces of that cover. The resulting measure is countably additive. Its restriction to each covering set agrees exactly with the corresponding local restriction. When the local measures are supported on their covering sets, each is recovered in full. This determines the global measure uniquely relative to the supplied compatible family. Finite local measures give sigma-finiteness; a cover containing a neighborhood of every point gives local finiteness. Nested restriction identities imply the overlap compatibility required for gluing. Explicit symmetric time windows [s-n,s+n] times all real momentum form a measurable increasing cover of real spacetime, contain every finite real time interval for a sufficiently large natural n, and contain a neighborhood of every spacetime point. A global force is represented by two positive real-spacetime measures finite on every bounded time window. Global total mass is NOT assumed finite; sigma-finiteness and local finiteness are derived. Restricting twice to nested time windows gives the smaller force exactly. Each interval force is the momentum projection of the restricted global pair and acts by half the difference of its two integrals. Constructed time cutoffs identify lifted spacetime tests with these interval actions. Applying the gluing construction separately to the actual consistent family on symmetric windows yields two positive sigma-finite locally finite global spacetime measures. Their restrictions exactly recover every member of the local family, and all smaller real windows are recovered by restriction. The global extension is unique for that particular limiting family; this is not uniqueness across different semiclassical subsequences. Each global component has a time marginal absolutely continuous with respect to Lebesgue measure. Every individual time slice has zero combined force mass. For any actual common compactified weak limits on the symmetric windows, restriction yields the actual positive and negative compactified limits on any ordered real subinterval. The actual spacetime force actions converge against all C0 spacetime tests on EVERY ordered real interval to the corresponding window of the same global pair. The actual integrated momentum force actions converge against every C0 momentum test to the momentum projection of that global window, using constructed time cutoffs and boundary-vanishing compactified tests. The original physical combined time-marginal bound passes to every real window: for endpoints within T of the initial time and every measurable time set A, the combined window force mass on A times all momentum is at most forceBudget(T) times the Lebesgue measure of A intersected with the window. This is the original budget for T, not an enlarged exhaustion-window budget. Combining C0 interval convergence, the actual force-mass bound and the existing Fourier response limit proves the Schwartz probability balance on EVERY ordered pair of real endpoints, using the restrictions of ONE global spacetime force and the SAME subsequence without interval-dependent extractions. The assembled actual-model theorem constructs that global force, its consistent compactified family and the all-real-time weakly continuous neutral probability curve together. It retains the initial Dirac law, characteristic convergence at every time and frequency, fixed-time weak probability convergence, exact local restrictions, relative extension uniqueness, time-marginal absolute continuity, absence of time atoms, C0 spacetime and interval convergence on all ordered real windows, the sharp physical time bound on every such window and the Schwartz balance at all real endpoints. The time bounds and convergence-identification lemmas allow nonnegative matter coefficients. The full probability/dynamics existence theorem and its Fourier balance retain fixed positive floor and width, strictly positive matter coefficients, an admissible nonzero hbar sequence tending to zero and any positive diverging resolvent scale. No global measure, limit existence, global consistency or arbitrary-endpoint weak balance is supplied as a new physical assumption in the assembled theorem. These results close global spacetime-force assembly and the common-force Schwartz balance for arbitrary real endpoints. The full weak continuity equation against general time-dependent spacetime tests remains unproved. Possible escaped momentum mass remains retained at compactification boundaries; global positive-force tightness and its absence are not assumed or proved. A closed classical force functional, independence across semiclassical subsequences, full phase-space dynamics, remaining canonical controls, neutral-position and negative-clock-momentum bounds, late-time zero clock defect, fixed-hbar recovery, floor removal, GR/QFT/Standard Model identification and empirical validity remain open. The positive-floor clock obstruction persists. No model or preceding operator changed and no necessity of a model change is established. All 994 predecessor source/script hashes are preserved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_neutral_global_spacetime_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
