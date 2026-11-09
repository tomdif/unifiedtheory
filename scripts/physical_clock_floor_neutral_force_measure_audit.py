#!/usr/bin/env python3
"""Audit the constructed positive force measures and neutral structured response.

Run with the repository toolchain and verified dependency overlay:
  lake env python3 scripts/physical_clock_floor_neutral_force_measure_audit.py --overlay PATH

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


MODULES = [('KFCausalL2BornMeasurability', 4), ('KFCausalNeutralOutputPolarization', 5), ('KFCausalNeutralOutputBornMeasure', 10), ('KFCausalNeutralForceMeasure', 9), ('KFCausalNeutralStructuredResponse', 7), ('KFCausalNeutralForceBalanceLimit', 3)]


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
    logs = overlay/'physical-clock-floor-neutral-force-measure-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_neutral_temporal_probability_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_neutral_force_measure_audit.py']
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
        scope='The unnormalised L2 Born measure is measurable in its actual L2 state, including zero, because every measurable-set evaluation is a continuous squared norm of a bounded cut operator. The neutral spectral Born law extends to arbitrary unnormalised physical states with mass equal to squared norm. Summing all eight physical energy-output channel laws gives a measurable finite positive output law. Integrating this kernel over any L2 output family constructs a finite positive measure with exactly the squared L2 norm as mass. Its Fourier transform equals the actual output translation expectation, with no assumed joint pointwise representative. Exact polarization of the neutral linear response gives half the difference of translation expectations of y+L y and y-L y, where L is the actual weighted linear coefficient lifted to the output L2 space. This identity does not assume that L commutes with translations. Thus a concrete pair of finite positive measures represents the signed force response: its Fourier transform is half the difference of their characteristic functions, and the actual linear rate equals i*v times that transform. The pair has total mass 2*norm(y)^2+2*norm(L y)^2, bounded by 2*(1+norm(weightedLinear)^2)*norm(y)^2. Its action on each bounded continuous complex test is bounded by half that mass times the test norm. The actual evolved neutral probability and the actual resolvent energy-output pair are assembled into one explicitly constructed State. Its probability characteristic is exactly the original canonical neutral test, its force Fourier response is continuous in time for each fixed positive resolvent scale and frequency, and its total force-pair mass is bounded by 2*(1+norm(weightedLinear(energyWeight(m,g,k,0)))^2)*the actual time energy. For nonnegative couplings, admissible nonzero hbar tending to zero, and fixed positive floor and width, the mass bound is eventually uniform in every positive resolvent scale and all times in each finite symmetric window, using the previously derived windowBudget. With strictly positive couplings, the full neutral resolvent rate differs from i*v times the force Fourier transform by at most 2*abs(hbar)*abs(v)^2*norm(weightedQuadratic)*energy. Along the previously derived common subsequence, the integral of this concrete force Fourier response converges to the characteristic increments of one weakly continuous all-time neutral probability curve with its proved initial Dirac law. This holds for every positive resolvent scale sequence tending to infinity, with no relative scale condition, and also for bounded converging frequencies and endpoints. The assembled existence theorem includes joint compact-uniform characteristic convergence, time Lipschitz bounds, weak moving-time convergence of the probability component, force-integral balance and uniform force-pair mass bounds. These are derived properties of actual states, not assumed physical closure data. Convergence or tightness of the force measures themselves is NOT proved: uniform total mass alone does not supply tightness or uniform integrability. No force functional of the limiting probability, closed classical transport equation, subsequence independence, full twelve-dimensional probability evolution, remaining canonical commutator controls, neutral-position or negative-clock-momentum bounds, late-time zero clock defect, fixed-hbar recovery, floor removal, GR/QFT/Standard Model identification or empirical validity is proved. The fixed positive-floor clock obstruction remains distinct from the vanishing response errors. No model or preceding operator changed, and no necessity of a model change is established. All 949 predecessor source/script hashes are preserved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_neutral_force_measure_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
