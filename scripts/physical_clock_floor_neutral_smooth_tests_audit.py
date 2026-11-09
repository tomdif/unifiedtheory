#!/usr/bin/env python3
"""Audit full smooth compact spacetime-test density and neutral weak dynamics.

Run with the repository toolchain and verified dependency overlay:
  lake env python3 scripts/physical_clock_floor_neutral_smooth_tests_audit.py --overlay PATH

Sequential direct Lean checks rebuild eight new modules, audit their axioms,
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


MODULES = [('KFCausalSpacetimeSliceRegularity', 5), ('KFCausalSmoothSpacetimeTests', 10), ('KFCausalSmoothTestApproximation', 6), ('KFCausalSmoothUnitWindow', 3), ('KFCausalTensorAffineTime', 6), ('KFCausalSmoothTestDensity', 5), ('KFCausalSmoothWeakEquation', 5), ('KFCausalNeutralSmoothTestDynamics', 1)]


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
    logs = overlay/'physical-clock-floor-neutral-smooth-tests-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_neutral_bernstein_tests_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_neutral_smooth_tests_audit.py']
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
        scope='Every smooth compactly supported complex-valued function on real time times real neutral momentum now has a sequence of finite tensor tests whose values and both partial derivatives converge in the global spacetime supremum norm. The derivative hypotheses needed by the preceding Bernstein construction are DERIVED from smoothness and compact support. A uniformly continuous spacetime function gives a norm-continuous curve of bounded momentum slices. For a uniformly continuous time derivative, scalar and Banach-valued fundamental theorems of calculus identify the slice curve with its Banach integral and prove norm differentiability. Smooth compact tests and all their directional derivatives are bundled as bounded continuous functions; mixed time/momentum derivatives commute, and fixed-time momentum slices are Schwartz functions. This proves that the value/momentum-derivative pair has the required continuous norm derivative. Localized Bernstein tensor approximants therefore exist for these tests. A concrete smooth bump equals one on [1/4,3/4] and is supported in [0,1], with its actual derivative bundled as a bounded continuous function. Affine changes of time preserve finite tensor tests and simultaneous uniform convergence; the time derivative acquires the proved chain-rule factor. Compact support supplies a finite positive time bound. An invertible affine time change moves that support to [1/4,3/4], the bump construction supplies approximants, and the inverse time change returns them to the original test. Uniqueness of derivatives identifies the two limiting derivative fields with the original partial derivatives. Thus no approximation-existence or extra test-norm-regularity assumption remains for the full smooth compact spacetime test class. The existing UniformWeakEquation implies SmoothWeakEquation on every ordered real interval, with time integrability and both probability boundary terms. Tests vanishing on the temporal boundary satisfy the zero-boundary distributional identity; every compact test has a finite time window beyond which the identity holds for all larger windows. The actual-model existence theorem retains the SAME common semiclassical subsequence, continuous neutral momentum probability curve, initial Dirac law, characteristic-function and fixed-time probability limits, compactified force-window limits, global positive/negative force measures with exact window restrictions, relative uniqueness, time absolute continuity, no time atoms, all ordered real C0 spacetime and momentum force-action limits, the original physical time marginal budget, interval Schwartz balance, TensorWeakEquation and UniformWeakEquation, and adds SmoothWeakEquation. It uses only the preceding assumptions: positive floor and width, positive matter coefficients, admissible nonzero hbar sequence tending to zero, and a positive resolvent scale tending to infinity. No model, operator or physical assumption is changed. The global positive/negative force measures are finite on bounded time windows; globally finite total mass is not claimed. The force action retains the preceding half-difference normalization. This is the full smooth compact test formulation of the neutral momentum marginal continuity equation with a separately extracted flux. It is NOT a closed evolution law: classical force identification, force closure, uniqueness across semiclassical subsequences, full phase-space dynamics, remaining canonical controls, neutral-position and negative-clock-momentum bounds, late-time zero clock defect, fixed-hbar recovery, floor removal, GR/QFT/Standard Model identification and empirical validation remain open. Possible escaped momentum mass is retained; global positive-force tightness and absence of escaped mass remain unproved. The positive-floor clock obstruction persists. No necessity of a model change is established. All 1018 predecessor source/script hashes are preserved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_neutral_smooth_tests_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
