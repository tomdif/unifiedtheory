#!/usr/bin/env python3
"""Audit the all-time subsequential neutral probability dynamics.

Run with the repository toolchain and verified dependency overlay:
  lake env python3 scripts/physical_clock_floor_neutral_temporal_probability_audit.py --overlay PATH

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


MODULES = [('KFCausalJointCharacteristicEquicontinuity', 1), ('KFCausalNeutralCharacteristicControl', 6), ('KFCausalNeutralTemporalCompactness', 5), ('KFCausalNeutralMomentumProbability', 4), ('KFCausalTemporalProbabilityRepresentation', 3), ('KFCausalNeutralTemporalProbability', 1), ('KFCausalNeutralInitialProbability', 7), ('KFCausalNeutralTemporalResponseLimit', 3)]


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
    logs = overlay/'physical-clock-floor-neutral-temporal-probability-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_neutral_resolvent_linear_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_neutral_temporal_probability_audit.py']
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
        scope='The actual canonical neutral-momentum characteristic has an exact additive frequency family and no Weyl ordering phase error. Previously derived complementary momentum tails supply a frequency modulus uniform over finite symmetric time windows; the actual neutral Ehrenfest estimate supplies a local time Lipschitz bound. Their combination gives joint eventual local equicontinuity in time and frequency. For every admissible nonzero hbar sequence tending to zero, fixed positive floor and width, strictly positive mass-squared, quartic and vacuum coefficients, and a fixed canonical initial momentum boost, there is ONE subsequence whose original neutral characteristics converge for EVERY real time and EVERY real neutral frequency. Convergence is uniform on every compact subset of the time-frequency plane, and the continuous limit retains the derived finite-window time Lipschitz bound. Exact finite-hbar neutral Born probabilities are constructed by pushing forward the physical complementary Fourier density under the neutral momentum symbol; their characteristic functions equal the original canonical neutral tests, without an auxiliary smoothing approximation. These exact probabilities converge along the common subsequence to a derived weakly continuous probability curve on all real times. The same subsequence gives weak convergence at every moving sampling time sequence converging to a fixed time. The initial curve value is proved to be the Dirac probability at the neutral component p.2 4 of the specified initial canonical momentum. This is obtained from the actual full boosted initial-characteristic limit and the initial identity of the propagator. Along the SAME subsequence, for EVERY positive resolvent scale sequence tending to infinity with no relative scale condition, the integral of the actual explicit neutral linear quantum response converges to the difference of characteristic functions of this probability curve. The response limit is also proved for bounded converging neutral frequencies and bounded converging endpoints in each finite window. The complete existence theorem derives the curve, its initial condition, joint compact-uniform characteristic convergence, weak moving-time convergence, time Lipschitz estimates, and response-integral balance from the actual model and states; none of these conclusions is introduced as a dynamical assumption. This is subsequential probability evolution of ONE neutral-momentum marginal. The quantum energy-output correlations in the leading response are still not identified with a classical force functional of the limiting state. No closed classical transport equation, independence from the chosen subsequence, full twelve-dimensional tightness or probability evolution, neutral-position or negative-clock-momentum control, normalized commutator control in the remaining canonical directions, late-time zero clock defect, fixed-hbar recovery, floor removal, GR/QFT/Standard Model identification or empirical validity is proved. The positive-floor clock commutator defect is distinct from the vanishing resolvent and polynomial response errors. No model or preceding operator changed, and no necessity of changing the model is established. All 940 predecessor source/script hashes are preserved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_neutral_temporal_probability_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
