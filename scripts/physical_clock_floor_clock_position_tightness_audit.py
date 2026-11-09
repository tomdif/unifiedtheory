#!/usr/bin/env python3
"""Recompile and audit the full averaged clock-energy bound and eventual uniform tightness of actual evolved log-clock Born laws on finite forward windows.

Run through the repository toolchain, using its previously verified dependencies:
  lake env python3 scripts/physical_clock_floor_clock_position_tightness_audit.py --overlay PATH

This does not invoke lake build. It rebuilds all seven new modules in dependency
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


MODULES = [('KFCausalClockChargeMultiplier', 11), ('KFCausalClockFloorChargeClockHalf', 5), ('KFCausalClockFloorAveragedClockBound', 4), ('KFCausalClockFloorClockPositionMass', 7), ('KFCausalClockPositionLaw', 6), ('KFCausalClockFloorDisplacedClockRightTail', 5), ('KFCausalClockFloorDisplacedClockTightness', 3)]


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
    logs = overlay/'physical-clock-floor-clock-position-tightness-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_clock_moment_tightness_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_clock_position_tightness_audit.py']
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
        scope='Every measurable contractive multiplier depending only on the physical log-clock coordinate is proved to commute with the actual charge-circle action through the existing coordinate unitaries and partial Fourier transform. The normalized bounded inverse half-clock is identified with such a multiplier. Its commutation implies invariance of the actual unbounded half-clock graph. Every averaged form state has a half-clock graph output, and its norm squared is bounded by twice the actual averaged energy, using orbit compatibility, graph uniqueness and the normalized charge integral. This holds without a charge-zero assumption and transfers to the completed reference form used by the actual propagator. The half-clock output norm is exactly the weighted Born position integral. A Markov bound controls the upper log-clock tail by this energy. The previously proved evolved-energy bound yields an arbitrarily small upper-tail probability uniformly over a finite time window for all sufficiently late terms of each admissible small-hbar sequence. Combining it with the preceding forward-window lower-tail theorem yields a compact clock interval with arbitrarily small probability outside it, uniformly over the finite forward window and eventually in the sequence. The actual Born configuration measure and log-clock marginal are constructed from the L2 state density; their total mass is the squared L2 norm, and the actual evolved boosted marginals are probability measures. The final compact-tail theorem is stated directly for these actual evolved quantum marginal measures. Parameters are fixed positive floor and clock width, fixed canonical momentum and initial time, nonnegative mass-squared, quartic and vacuum couplings, and a nonzero hbar sequence tending to zero within the existing analytic strip from either or mixed signs. No clock-energy-domain, quantum tightness, classical evolved law or transport conclusion is assumed. This is eventual uniform tightness of one log-clock position marginal on finite forward windows. It does not prove full phase-space tightness, negative clock-momentum control, a common time-dependent measure subsequence, uniqueness or classical-flow identification. General Hamiltonian phase-test domain and commutator control, positive-time quantum-classical correspondence, fixed-hbar long-time zero clock defect, floor removal, GR/QFT/Standard Model identification and empirical validity remain open. No model or preceding operator changed; all 798 predecessor source/script hashes are preserved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_clock_position_tightness_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
