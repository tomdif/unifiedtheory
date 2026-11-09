#!/usr/bin/env python3
"""Recompile and audit simultaneous control of ten independent canonical frequency directions on actual evolved states, including clock position and every transverse momentum.

Run through the repository toolchain, using its previously verified dependencies:
  lake env python3 scripts/physical_clock_floor_ten_test_control_audit.py --overlay PATH

This does not invoke lake build. It rebuilds all nine new modules in dependency
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


MODULES = [('KFCausalChargeSpectatorMultiplier', 4), ('KFCausalChargedPositionTests', 6), ('KFCausalChargedMomentumTests', 4), ('KFCausalClockFloorDisplacedChargedTestControl', 7), ('KFCausalClockFloorDisplacedClockTestControl', 6), ('KFCausalCanonicalWeylSumBounds', 4), ('KFCausalCanonicalTenDirections', 4), ('KFCausalClockFloorDisplacedTenTestControl', 4), ('KFCausalCanonicalTenCoordinates', 3)]


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
    logs = overlay/'physical-clock-floor-ten-test-control-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_canonical_test_control_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_ten_test_control_audit.py']
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
        scope='Arbitrary contractive spectator-position multipliers commute with the actual antisymmetric partial Fourier transform on all L2 states. The symmetric position coordinates and normalized antisymmetric momentum coordinates of the preceding charged Born law are identified with actual canonical position phases and transverse translations, including their all-L2 representatives. Existing evolved charged tails then give eventual uniform norm and characteristic control of all four canonical tests on finite symmetric time windows. The actual canonical log-clock position phase is multiplication by exp(i*u*clockPosition). Its radial Born tail is bounded by the already derived two-sided compact-interval tail; this gives eventual uniform norm and characteristic control on finite forward windows without a clock-position second moment. Exact ordered Weyl products control a simultaneous position/momentum test by the sum of the individual test norm displacements, with no semiclassical product-error assumption. A concrete family has five position frequencies (clock and four charged positions) and five momentum frequencies (all transverse momenta). It is encoded as a continuous real linear map from ten real coefficients, with an explicit proved left inverse and hence injectivity. The omitted neutral-position and clock-momentum components are proved zero. Combining the preceding five complementary controls with the four charged controls and clock control gives one radius and one eventual index for all ten axes on every finite forward window. A further theorem handles arbitrary simultaneous coefficient vectors within that radius, proving that the actual canonical test changes the evolved normalized state by less than any prescribed tolerance and that its canonical characteristic differs from one by less than that tolerance. The clock floor and initial width are fixed and positive; initial time and canonical momentum are fixed; couplings are nonnegative; nonzero hbar approaches zero within the existing strip from either or mixed signs. No evolved classical law, unweighted second moment, tail hypothesis or simultaneous-test bound is assumed. The result controls a ten-dimensional frequency subspace, not all twelve directions and not a joint Born law of noncommuting observables. Quantum dynamic control of neutral position and negative clock momentum, full phase-space measure limits, common time-dependent subsequences, Hamiltonian phase-test domain and commutator estimates, uniqueness and positive-time classical transport remain open. Fixed-hbar long-time clock recovery, floor removal, physical GR/QFT/Standard Model identification and empirical validity remain open. No model or preceding operator changed; all 845 predecessor source/script hashes are preserved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_ten_test_control_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
