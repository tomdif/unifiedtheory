#!/usr/bin/env python3
"""Audit cutoff-free neutral-position time control and moving-time probability limits.

Run with the repository toolchain and verified dependency overlay:
  lake env python3 scripts/physical_clock_floor_neutral_position_time_audit.py --overlay PATH

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


MODULES = [('KFCausalRadialResponseFrequencyBound', 5), ('KFCausalNeutralPositionRadialCharacteristic', 5), ('KFCausalNeutralPositionTimeContinuity', 3), ('KFCausalNeutralPositionProbability', 3), ('KFCausalNeutralPositionInitialLimit', 5), ('KFCausalNeutralPositionMovingProbability', 4)]


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
    logs = overlay/'physical-clock-floor-neutral-position-time-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_radial_full_response_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_neutral_position_time_audit.py']
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
        expected = {'UnifiedTheory.Audit.'+name+'.'+n for n in
                    re.findall(r'^#print axioms (\S+)', (root/source).read_text(), re.M)}
        assert {n for n, _ in audits} == expected, (name, expected)
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
        scope='The radial cutoff is now removed from value-level time control of the actual bare canonical neutral-position characteristic, while the positive clock floor is retained. The previous full radial response constant is bounded uniformly on bounded neutral-frequency intervals. The radial expectation on the actual evolved boosted state is identified with the already differentiated completed-form expectation. Its difference from the bare canonical position characteristic is uniformly small over all frequencies and finite time windows by the already proved charged-tail approximation. Combining this uniform approximation with the derived regulated expectation Lipschitz bound proves eventual time equicontinuity of the bare characteristic, uniformly for abs(frequency)<=V and times in any fixed finite window, along each nonzero admissible hbar sequence tending to zero. No convergence of differentiated responses, operator-domain preservation for the bare phase, or energy graph-norm cutoff removal is asserted. Bare expectations at two moving times whose difference tends to zero become uniformly equal on bounded frequency intervals; the result also allows moving bounded frequencies. The actual Born neutral-position marginal is constructed directly from the physical L2 state density, proved to be a probability for normalized states, and its characteristic is identified exactly with the bare quantum expectation. The existing boosted initial phase-space characteristic theorem supplies full-sequence convergence of the initial position marginal to the origin, independently of the canonical momentum boost. The new time continuity transfers any established fixed-time weak position probability limit to moving observation times converging to that time. In particular, for observation times tending to the actual initial time as hbar tends to zero, the actual position probabilities converge to the origin with no relation between the two rates, and the whole resulting sequence is tight. The initial-time application supplies the fixed-time probability limit from a prior theorem; it is not a new physical hypothesis. Conditions for the time-control and moving-time theorems are positive fixed epsilon and initial clock width, nonnegative matter couplings, and the existing admissible nonzero hbar sequence tending to zero. This is not uniform position tightness on a fixed nonzero time interval, a position probability curve at all times, a cutoff-free response derivative or a closed classical force law. Frequency equicontinuity at zero over full time windows, energy-output tail control, full twelve-dimensional dynamics, negative-clock-momentum control, force closure and uniqueness, clock-defect recovery, fixed-hbar and floor removal, GR/QFT/Standard Model identification and empirical validation remain open. The Hamiltonian and model are unchanged; no necessity of a model change is established. All 1127 predecessor source/script hashes are preserved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_neutral_position_time_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
