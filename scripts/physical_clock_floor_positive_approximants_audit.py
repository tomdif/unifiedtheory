#!/usr/bin/env python3
"""Recompile and audit positive phase-space probability approximants of actual evolved states, with vanishing characteristic error on the shared global-clock subsequence.

Run through the repository toolchain, using its previously verified dependencies:
  lake env python3 scripts/physical_clock_floor_positive_approximants_audit.py --overlay PATH

This does not invoke lake build. It rebuilds all ten new modules in dependency
order, checks their printed axioms, checks the root import, and preserves the
preceding source hash chain. It is a scoped formal audit, not a TOE certificate.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess


MODULES = [('KFCausalWindowedPhaseSpaceState', 5), ('KFCausalL2BornLaw', 4), ('KFCausalWindowedCanonicalTests', 8), ('KFCausalWindowedPhaseSpaceLaw', 7), ('KFCausalPhysicalCanonicalCoordinates', 3), ('KFCausalPhysicalWindowedLaw', 3), ('KFCausalLocalizedWindow', 5), ('KFCausalSemiclassicalWindow', 5), ('KFCausalWindowedApproximation', 2), ('KFCausalClockFloorPositiveApproximants', 1)]


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
    logs = overlay/'physical-clock-floor-positive-approximants-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_joint_characteristic_limit_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_positive_approximants_audit.py']
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
        scope='A tensor state, a volume-preserving shear and a partial Fourier unitary construct a positive phase-space measure for every actual L2 state and auxiliary window. Its total mass is the product of the squared norms, so unit states and unit windows give genuine probability measures. An exact intertwining calculation identifies each classical characteristic as the product of the original canonical quantum characteristic and a reflected window characteristic. The existing physical-to-Euclidean pullback preserves this identity for all physical canonical tests. Normalized indicators of shrinking Euclidean balls have controlled position-phase error. Strong translation continuity selects a strictly increasing subsequence of any hbar sequence tending to zero on which the window translation error vanishes on growing momentum-frequency balls. Consequently the window characteristic tends to one for every fixed frequency. This supplies a state-independent approximation error tending to zero, uniformly over all normalized physical input states at each fixed canonical frequency. Refining the previously constructed joint clock-and-characteristic subsequence therefore gives actual positive phase-space probability approximants whose ten controlled characteristics converge to the existing positive continuous kernels at any prescribed countable family of future times. The same subsequence retains the global continuous clock path, values in [0,1], uniform convergence on every compact time set, the existing window Lipschitz estimates, and convergence of integrated actual quantum comparison rates to clock increments at every pair of real endpoints. The concrete theorem constructs its windows and probability approximants and assumes no classical measure limit, characteristic limit or translation-error limit. The fixed positive floor and width, nonnegative couplings, fixed initial time and momentum, and nonzero hbar approaching zero in the existing strip are unchanged. The constructed approximants live on twelve-dimensional phase space, but convergence is proved only for the controlled ten-frequency family; the construction is a windowed positive law, not a sharp joint Born law for noncommuting quantum observables. Uniform tightness of the ten-dimensional projected measures, existence of a representing limit probability measure, compatibility of that measure with the global clock limit, characteristic time regularity, Hamiltonian phase-test domain and commutator estimates, uniqueness and positive-time classical transport remain open. Quantum dynamic control of neutral position and negative clock momentum, full twelve-dimensional measure limits, fixed-hbar zero clock defect, floor removal, GR/QFT/Standard Model identification and empirical validity remain open. No model or preceding operator changed; all 867 predecessor source/script hashes are preserved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_positive_approximants_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
