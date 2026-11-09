#!/usr/bin/env python3
"""Audit the derived additive neutral interval forces and their physical mass control.

Run with the repository toolchain and verified dependency overlay:
  lake env python3 scripts/physical_clock_floor_neutral_consistent_dynamics_audit.py --overlay PATH

Sequential direct Lean checks rebuild five new modules, audit their axioms,
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


MODULES = [('KFCausalForceIntervalAdditivity', 6), ('KFCausalLocalForceConsistency', 7), ('KFCausalNeutralForceConsistency', 3), ('KFCausalConsistentForceIntervals', 6), ('KFCausalNeutralConsistentDynamics', 2)]


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
    logs = overlay/'physical-clock-floor-neutral-consistent-dynamics-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_neutral_weak_dynamics_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_neutral_consistent_dynamics_audit.py']
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
        scope='The actual integrated positive and negative force measures are additive over adjacent ordered real time intervals b<=c<=d, and vanish on zero-length intervals. The proof splits Lebesgue restrictions into disjoint half-open intervals, uses the zero mass of endpoints, and proves the kernel bind identity by evaluation and linearity of the nonnegative integral. It requires no force closure. The actual output-time kernels and actual boosted quantum trajectories inherit these identities for every admissible hbar and every positive resolvent scale. Compactification preserves addition. On any common subsequence of compactified positive/negative force limits, all indexed interval concatenation identities are inherited by continuity of addition and uniqueness of weak limits. Restriction to finite momentum and tangent pushforward preserve addition, so the actual finite positive real-line restrictions and their signed test actions remain additive. Total compactified mass is continuous under weak convergence. Consequently every eventual actual combined-mass bound passes to the sum of the compactified limiting masses, and bounds the combined mass of their finite real-line restrictions. For the actual model this gives, on each finite symmetric window around the initial time, mass <= interval length * 2*(1+norm(weightedLinear(energyWeight(m,g,k,0)))^2)*windowBudget. The mass theorem needs only nonnegative matter coefficients, admissible nonzero hbar tending to zero, and positive resolvent scales; scale divergence is not needed for these consistency and mass implications alone. An explicit interval-force family structure packages the two compactified positive measures, all indexed concatenation identities, and the physical mass bounds. Its local finite pair has derived positive/negative additivity, additive bounded-continuous test actions, zero compactified masses on zero-length intervals, and test-action bounds proportional to interval length. Adding one adjacent interval changes each local bounded-continuous test action by at most half the physical mass budget of that added interval times the test norm. The actual-model existence theorem CONSTRUCTS this family on the same subsequence as the weakly continuous all-real-time neutral probability curve, its initial Dirac law, original characteristic convergence at every time/frequency, fixed-time weak probability convergence, compactified force convergence, convergence on all C0 tests, and the integrated continuity equation for every complex Schwartz test. The full existence theorem retains fixed positive floor and width, strictly positive matter coefficients, an admissible nonzero hbar sequence tending to zero, and any positive diverging resolvent scale sequence. It applies to ANY chosen countable family of ordered real intervals, hence may be instantiated with all ordered rational-endpoint intervals. The construction proves every concatenation relation represented within the chosen family; no limiting additivity or mass law is assumed. The Schwartz observable increment is bounded by half the interval physical budget times the supremum norm of the derivative. These are derived consistent finite interval forces and weak dynamics of one neutral-momentum marginal. Extension of a common countable interval family to all real endpoints and a countably additive spacetime force measure remains unproved. The separately derived force extraction for every real interval from the predecessor may depend on the interval and has not yet been identified with such an extension. Global positive-force tightness and vanishing escaped endpoint mass are neither assumed nor proved. A closed classical force functional, uniqueness across semiclassical subsequences, full phase-space dynamics, the remaining canonical controls, neutral-position and negative-clock-momentum bounds, late-time zero clock defect, fixed-hbar recovery, floor removal, GR/QFT/Standard Model identification and empirical validity remain open. The positive-floor clock obstruction persists. No model or preceding operator changed and no necessity of a model change is established. All 970 predecessor source/script hashes are preserved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_neutral_consistent_dynamics_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
