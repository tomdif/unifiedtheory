#!/usr/bin/env python3
"""Audit the actual time-integrated neutral force measures and their local limits.

Run with the repository toolchain and verified dependency overlay:
  lake env python3 scripts/physical_clock_floor_neutral_local_force_audit.py --overlay PATH

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


MODULES = [('KFCausalNeutralOutputSpectralCut', 5), ('KFCausalFiniteKernelInterval', 8), ('KFCausalNeutralOutputTimeKernel', 9), ('KFCausalNeutralIntegratedForce', 5), ('KFCausalCompactFiniteMeasureSubsequence', 2), ('KFCausalCompactifiedForceMeasure', 4), ('KFCausalLocalForceMeasure', 6), ('KFCausalNeutralLocalForceLimit', 3)]


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
    logs = overlay/'physical-clock-floor-neutral-local-force-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_neutral_force_measure_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_neutral_local_force_audit.py']
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
        scope='Every measurable-set evaluation of the averaged neutral output Born law is now proved equal to the squared norm of a bounded spectral cut of the actual L2 output. Consequently the law is measurable in the L2 state. Along every continuous output curve the two positive force-output measures form measurable time kernels with continuous masses. Integrating these kernels over a compact time interval gives actual finite positive measures. Their combined mass is the integral of the actual force-pair mass, and their bounded-continuous test evaluations and Fourier transforms equal the corresponding time integrals. For the actual boosted unitary trajectories and positive resolvent scale, these constructions require no added force or transport assumptions. For nonnegative matter coefficients and every admissible nonzero hbar sequence tending to zero, the integrated force-pair mass on b<=c in a finite symmetric time window is eventually at most (c-b)*2*(1+norm(weightedLinear(energyWeight(m,g,k,0)))^2)*windowBudget. One threshold controls all positive scales and endpoints in the window. For strictly positive coefficients the integrated measures retain the previously derived original neutral characteristic balance for every positive diverging scale sequence. A general compact-metric finite-measure subsequence theorem is proved for countably many families with separate eventual mass bounds, including zero masses. It uses normalization and compactness of probability measures together with compact scalar mass intervals; no common eventual threshold across the countable family is assumed. Real momentum is explicitly embedded by arctan into the compact interval [-pi/2,pi/2]. The positive and negative integrated measures have a common weakly converging subsequence on that interval. Possible mass at its endpoints is retained. Restricting each limit to the open interval and pushing forward by tan constructs finite positive measures on real momentum. For every bounded continuous compactified test vanishing outside the open interval, their integrals agree exactly with those of the compactified limits. Hence the signed force-pair actions on the pullbacks of these tests converge to the actual finite real-line limit pair. The actual model supplies all required mass bounds for ANY chosen countable family of ordered real time intervals, and every positive scale sequence, without a divergence requirement for force compactness alone. With strictly positive coefficients and diverging scales, the assembled theorem derives ONE further subsequence carrying the same weakly continuous all-time neutral probability curve and initial Dirac law, pointwise original characteristic convergence at every real time and frequency, weak probability convergence at every fixed real time, the common compactified positive/negative force limits for the chosen interval family, and convergence against the stated boundary-vanishing test class to their finite real-line restrictions. On that SAME subsequence, the original integrated Fourier response balance holds for every ordered real interval and every real frequency. This last Fourier statement is kept separate: Fourier exponentials do not extend continuously to the compactification endpoints, so their balance has NOT been identified with the Fourier transform of the local force-limit pair. No vanishing endpoint mass or global force-measure tightness is assumed or proved. Extension of the local test result to a general compactly supported or C0 test API, the Fourier-inversion limit interchange needed for a distributional continuity equation, consistency/additivity of all interval limit pairs as a spacetime force measure, a closed classical force functional, uniqueness across subsequences and full phase-space dynamics remain open. The remaining canonical controls, neutral-position and negative-clock-momentum bounds, late-time zero clock defect, fixed-hbar recovery, floor removal, GR/QFT/Standard Model identification and empirical validity are not proved. The positive-floor clock obstruction remains. No model or preceding operator changed, and no necessity of a model change is established. All 956 predecessor source/script hashes are preserved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_neutral_local_force_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
