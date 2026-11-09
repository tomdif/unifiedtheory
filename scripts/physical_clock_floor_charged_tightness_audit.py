#!/usr/bin/env python3
"""Recompile and audit the derived weighted charged moment bounds and eventual uniform tightness of actual evolved four-dimensional mixed Born laws on finite time windows.

Run through the repository toolchain, using its previously verified dependencies:
  lake env python3 scripts/physical_clock_floor_charged_tightness_audit.py --overlay PATH

This does not invoke lake build. It rebuilds all eleven new modules in dependency
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


MODULES = [('KFCausalPartialFourierTranslation', 6), ('KFCausalPairedTranslationCoordinates', 8), ('KFCausalAntisymmetricMomentumCoordinates', 5), ('KFCausalClockFloorAntisymmetricGraph', 8), ('KFCausalClockFloorRotatedAntiSymbol', 7), ('KFCausalClockFloorChargedMomentTonelli', 6), ('KFCausalClockFloorAveragedChargedMoment', 6), ('KFCausalClockFloorChargedTail', 6), ('KFCausalClockFloorDisplacedChargedTail', 5), ('KFCausalClockFloorChargedLaw', 7), ('KFCausalClockFloorDisplacedChargedTightness', 2)]


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
    logs = overlay/'physical-clock-floor-charged-tightness-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_clock_position_tightness_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_charged_tightness_audit.py']
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
        scope='The partial Fourier transform intertwines translations in its transformed block with the exact phase multiplier on all L2 states, proved by tensor density. The existing physical coordinate unitaries transport this identity to the two actual antisymmetric maximal momentum operators. Their natural graphs have exact physical-momentum multiplier representatives in charge coordinates, derived from their strong translation generators. The bounded inverse half-clock has its exact multiplier representative in these coordinates; its composition with each antisymmetric momentum is closed. The actual closed eight-factor energy graph retains both weighted kinetic outputs. An exact scalar charge average gives the sum of the corresponding physical momentum square and symmetric position square divided by the positive clock C=exp(clockPosition)+epsilon. Nonnegative Tonelli averaging identifies this weighted moment with the angle-averaged kinetic integral before any state moment is assumed finite. Finite actual averaged energy then proves integrability and the bound integral((P_i^2+Q_i^2)/C times squared state density) <= 2*exp(-2*t)*energy for each of the two pairs. This holds throughout the averaged form and transfers to the completed reference form used by the actual propagator. The half-clock output also has its exact multiplier representative in charge coordinates. Combining the clock and charged moments gives R times the probability of P_i^2+Q_i^2 >= R^2 <= (1+exp(-2*t))*energy. The existing uniform evolved-energy estimate makes both plane tails arbitrarily small uniformly on each finite symmetric time window, eventually along every admissible nonzero hbar sequence tending to zero. The joint Born law of the two antisymmetric physical momenta and two symmetric positions is constructed directly from the actual charge-coordinate L2 density; its mass is the squared state norm. The evolved laws are probability measures, and the final theorem gives a compact four-dimensional box with arbitrarily small probability outside it, uniformly throughout each finite time window and eventually in the sequence. The four observables commute in this mixed representation. Parameters are fixed positive floor and clock width, fixed canonical momentum and initial time, nonnegative mass-squared, quartic and vacuum couplings, and nonzero hbar within the existing strip tending to zero from either or mixed signs. No state-moment integrability, quantum tightness or classical evolved law is assumed. This is a four-dimensional mixed quantum marginal; it is not a full canonical phase-space probability law or full phase-space tightness. The other charged canonical directions, neutral position and momentum, negative clock momentum, time-dependent phase-space measure limits, uniqueness and classical transport identification remain open, as do general Hamiltonian phase-test domain and commutator bounds, fixed-hbar long-time zero clock defect, floor removal, GR/QFT/Standard Model identification and empirical validity. No model or preceding operator changed; all 806 predecessor source/script hashes are preserved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_charged_tightness_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
