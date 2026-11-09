#!/usr/bin/env python3
"""Audit the neutral weak equation under uniform limits of tests and both derivatives.

Run with the repository toolchain and verified dependency overlay:
  lake env python3 scripts/physical_clock_floor_neutral_uniform_tests_audit.py --overlay PATH

Sequential direct Lean checks rebuild four new modules, audit their axioms,
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


MODULES = [('KFCausalSpacetimeUniformTests', 7), ('KFCausalTensorTestClosure', 9), ('KFCausalTensorSeriesTests', 8), ('KFCausalNeutralUniformTestDynamics', 1)]


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
    logs = overlay/'physical-clock-floor-neutral-uniform-tests-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_neutral_time_dependent_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_neutral_uniform_tests_audit.py']
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
        scope='The neutral time-dependent weak equation is stable under simultaneous uniform convergence of the spacetime test function, its time derivative and its momentum derivative. Integration of bounded continuous complex tests against a finite measure is constructed as a continuous linear map. Restriction of a bounded continuous spacetime test to a fixed time is a continuous linear map of norm at most one. Probability expectations are bounded by the spacetime supremum norm, and endpoint expectations and finite-window force actions converge under uniform test convergence. If approximating time expectations are integrable, their limit is proved strongly measurable almost everywhere and integrable using the uniform probability bound. Dominated convergence then gives convergence of their time integrals; the dominating bound follows from boundedness of a norm-convergent sequence, rather than an added physical hypothesis. A finite tensor test packages bounded C1 time factors with bounded continuous derivatives and complex Schwartz momentum factors. Its value and both actual partial derivatives are bounded continuous spacetime functions. An approximable triple is explicitly defined by one sequence of finite tensor tests whose values, time derivatives and momentum derivatives all converge in the global supremum norm. Uniform derivative-limit theorems prove that the limiting derivative functions are the ACTUAL time and momentum derivatives of the limiting test. The finite-tensor weak equation passes to every such triple on EVERY ordered real interval, with both probability boundary terms. Time integrability is retained. When the limiting test vanishes at both endpoint time slices, the right side is zero; the approximants need not vanish there. Summable norm budgets construct explicit countably infinite tensor-series tests in this class. The three budgets are the sums of ||eta_n|| times ||f_n||, ||eta_n_prime|| times ||f_n||, and ||eta_n|| times ||f_n_prime||, using bounded-continuous momentum norms. Partial sums are explicit finite tensor tests; all three series converge in the bounded-continuous norm. Their partial derivatives and weak equation follow from the verified closure theorem. No assertion that arbitrary smooth compactly supported spacetime tests possess such an approximation or series representation is made: the full test-density theorem is still missing. The actual-model theorem constructs the SAME common semiclassical subsequence, all-real-time weakly continuous probability curve, compatible compactified local force family and global force as before, together with both the finite-tensor and uniform-closure weak equations. It retains the initial Dirac law, characteristic convergence at every time and frequency, fixed-time weak probability convergence, exact canonical-window restrictions, global extension uniqueness relative to that family, absolute continuity of both time marginals, absence of time atoms, C0 spacetime and projected momentum-force convergence on every ordered real window, the original physical time budget and the Schwartz increment balance at all real endpoints. Fixed positive floor and width, strictly positive matter coefficients, admissible nonzero hbar tending to zero and any positive diverging resolvent scale remain required. No extra physical evolution, force-closure, limit-existence or probability-curve-differentiability hypothesis was introduced. Approximation and summability hypotheses specify analytic test classes, and their density in the full smooth test class has NOT been assumed. A closed classical force functional, independence across semiclassical subsequences, full phase-space dynamics, remaining canonical controls, neutral-position and negative-clock-momentum bounds, late-time zero clock defect, fixed-hbar recovery, floor removal, GR/QFT/Standard Model identification and empirical validity remain open. Possible escaped momentum mass is retained at compactification boundaries; global positive-force tightness and its absence remain unproved. Global total force mass is not assumed finite. The positive-floor clock obstruction persists. No model or preceding operator changed and no necessity of a model change is established. All 1006 predecessor source/script hashes are preserved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_neutral_uniform_tests_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
