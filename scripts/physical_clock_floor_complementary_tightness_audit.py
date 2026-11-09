#!/usr/bin/env python3
"""Recompile and audit the complementary weighted moments, physical momentum identities, and eventual uniform tightness of actual evolved five-dimensional complementary Born laws on finite time windows.

Run through the repository toolchain, using its previously verified dependencies:
  lake env python3 scripts/physical_clock_floor_complementary_tightness_audit.py --overlay PATH

This does not invoke lake build. It rebuilds all fifteen new modules in dependency
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


MODULES = [('KFCausalPartialFourierRightTranslation', 4), ('KFCausalMixedRotationMomentumGraph', 7), ('KFCausalSymmetricMomentumCoordinates', 9), ('KFCausalChargeTransverseSplit', 7), ('KFCausalChargeDualMomentum', 8), ('KFCausalClockFloorDualClock', 11), ('KFCausalComplementaryChargeSymbol', 8), ('KFCausalComplementaryPhysicalMomenta', 5), ('KFCausalClockFloorSymmetricOrbitGraph', 6), ('KFCausalClockFloorComplementaryTonelli', 6), ('KFCausalClockFloorAveragedComplementaryMoment', 6), ('KFCausalClockFloorComplementaryTail', 3), ('KFCausalClockFloorDisplacedComplementaryTail', 5), ('KFCausalClockFloorComplementaryLaw', 7), ('KFCausalClockFloorDisplacedComplementaryTightness', 2)]


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
    logs = overlay/'physical-clock-floor-complementary-tightness-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_charged_tightness_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_complementary_tightness_audit.py']
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
        scope='Translation in the untransformed block commutes with the actual partial Fourier transform on all L2 states. The actual normalized charge pullback conjugates translations by its explicit linear flow; differentiation yields covariance of full natural maximal momentum graphs without smooth-core assumptions. The two remaining physical kinetic directions retain their derivative graphs in the existing charge representation. An explicit volume-preserving isometry reorders the mixed coordinates into five transverse coordinates and the unchanged clock. Partial Fourier transformation of those five coordinates yields a complementary unitary and diagonalizes every clock-preserving translation generator. Clock multipliers, the bounded inverse half-clock and the natural half-clock graph retain exact multiplier representatives. Full operator equality identifies three complementary coordinate multipliers with the original maximal physical momenta in the two normalized symmetric directions and the neutral direction. Exact rotation averages retain the neutral term: the two averaged squares are X_0^2+P_0^2 and X_1^2+P_1^2+N^2, where X_i is the negative dual antisymmetric Fourier coordinate, P_i is the scaled symmetric Fourier coordinate and N is the scaled neutral Fourier coordinate. The actual closed eight-factor energy graph retains the two weighted outputs. Nonnegative Tonelli averaging is justified before state moment finiteness is known. Finite averaged energy then proves integrability and bounds each complementary inverse-clock weighted second moment by twice the actual energy, for every averaged form vector, without a charge-zero assumption. The result transfers to the completed reference form used by the actual propagator. Combining these moments with the half-clock energy gives R times each radial tail probability <= twice the actual time-dependent energy. Existing evolved-energy bounds imply eventual uniform small tails throughout every finite symmetric time window for every admissible nonzero hbar sequence tending to zero. The complementary five-dimensional Born law is constructed directly from the actual transformed L2 state density, has total mass equal to the squared norm, and is a probability measure for the actual evolved boosted states. The final theorem supplies a compact five-dimensional box with arbitrarily small probability outside it, uniformly across each finite time window and eventually along the sequence. Parameters are fixed positive floor and clock width, fixed initial canonical momentum and time, nonnegative mass-squared, quartic and vacuum couplings, and nonzero hbar within the existing strip approaching zero from either or mixed signs. No state-moment integrability, tightness or classical evolved law is assumed. The two X_i coordinates are explicitly defined by the complementary unitary; their graph identification with the original antisymmetric position operators remains to be written. The result is a complementary quantum marginal and does not construct a joint canonical phase-space law. Connecting these marginals to full canonical phase tests, dynamic bounds for neutral position and negative clock momentum, phase-space measure limits, uniqueness and positive-time classical transport remain open. General Hamiltonian phase-test domain and commutator estimates, fixed-hbar long-time zero clock defect, floor removal, GR/QFT/Standard Model identification and empirical validity remain open. No model or preceding operator changed; all 818 predecessor source/script hashes are preserved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_complementary_tightness_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
