#!/usr/bin/env python3
"""Recompile and audit full physical position operator identification and eventual uniform control of five actual canonical phase tests on evolved states.

Run through the repository toolchain, using its previously verified dependencies:
  lake env python3 scripts/physical_clock_floor_canonical_test_control_audit.py --overlay PATH

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


MODULES = [('KFCausalL2FourierModulation', 4), ('KFCausalChargePositionPhase', 6), ('KFCausalSelfAdjointMultiplierIdentification', 1), ('KFCausalChargePositionGraph', 1), ('KFCausalComplementaryPhysicalPositions', 10), ('KFCausalL2PhaseTailBound', 3), ('KFCausalComplementaryPositionTests', 6), ('KFCausalClockFloorDisplacedPositionTestControl', 4), ('KFCausalComplementaryMomentumTests', 4), ('KFCausalClockFloorDisplacedMomentumTestControl', 5)]


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
    logs = overlay/'physical-clock-floor-canonical-test-control-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_complementary_tightness_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_canonical_test_control_audit.py']
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
        scope='L2 Fourier modulation becomes negative translation, first on Schwartz inputs and then by density on all L2 states; the partial Fourier identity follows by tensor density. Antisymmetric charge-coordinate translations are exact phases of the original physical positions. Differentiation on natural translation-generator graphs and almost-everywhere derivative identification gives the original position multiplier representative without a smooth-core or position-moment assumption. Self-adjoint maximality identifies both complementary position multipliers with maximal multiplication by the normalized original positions (x1-x2)/sqrt(2) and (x3-x4)/sqrt(2), including equality of their full domains. These complete the physical identification of all five complementary coordinates; the preceding three momentum equalities are preserved. Bounded position exponentials are identified with the actual canonical Weyl position tests on every L2 state. Actual canonical translations in the two normalized symmetric directions and neutral direction are exactly the corresponding momentum phases under the complementary unitary. A general L2 inequality bounds squared phase-test displacement by frequency squared times radius squared times state norm squared plus four times the radial Born tail; no unweighted second moment is assumed. The already derived evolved complementary tails then prove eventual uniform continuity at zero, in norm and in canonical characteristics, for each of these five tests throughout every finite symmetric time window. Parameters are fixed positive clock floor and initial clock width, fixed initial time and canonical momentum, nonnegative mass-squared, quartic and vacuum couplings, and any admissible nonzero hbar sequence approaching zero from either or mixed signs. No state-integrability, tail, classical evolved-law or desired operator-identity assumption is added. These are five canonical directions, not control of all twelve canonical frequency directions or a full phase-space measure limit. The analogous canonical test connection for the previous four-dimensional charged marginal and clock marginal, quantum dynamic bounds for neutral position and negative clock momentum, full phase-space measure limits, common time-dependent subsequences, Hamiltonian domain and commutator estimates, uniqueness and positive-time classical transport remain open. Fixed-hbar long-time zero clock defect, floor removal, GR/QFT/Standard Model identification and empirical validity remain open. No model or preceding operator changed; all 834 predecessor source/script hashes are preserved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_canonical_test_control_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
