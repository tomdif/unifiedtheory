#!/usr/bin/env python3
"""Recompile and audit the closed energy and Hamiltonian for the revised clock-floor model.

Run through the repository toolchain, using its previously verified dependencies:
  lake env python3 scripts/physical_clock_floor_hamiltonian_audit.py --overlay PATH

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


MODULES = [
    ('KFCausalClockFloorFieldCoefficient', 11),
    ('KFCausalClockFloorShiftedCoefficient', 6),
    ('KFCausalClockFloorWeightedProducts', 7),
    ('KFCausalClockFloorFieldPolynomials', 7),
    ('KFCausalClockFloorFieldGraphs', 6),
    ('KFCausalClockFloorMatterClosure', 8),
    ('KFCausalClockFloorJointEnergy', 11),
    ('KFCausalClockFloorFormHamiltonian', 12),
    ('KFCausalClockFloorAveragedEnergy', 13),
]


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
    logs = overlay/'physical-clock-floor-hamiltonian-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous = json.loads((root/'data/physical_clock_floor_density_audit.json').read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_hamiltonian_audit.py']
    hashes = {p: sha256(root/p) for p in sources}
    assert all(hashes[p] == h for p, h in previous['source_sha256'].items())
    root_hash = sha256(root/'UnifiedTheory.lean')
    root_text = (root/'UnifiedTheory.lean').read_text()
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
    assert all(sha256(root/p) == h for p, h in hashes.items()), 'Sources changed during verification.'
    report = dict(
        modules=checks, root_check=dict(command=['lean', '-j1', 'UnifiedTheory.lean'], exit_code=0,
            empty_log=True, source_sha256=root_hash, log_sha256=sha256(log)),
        audited_declaration_count=sum(n for _, n in MODULES), source_sha256=hashes,
        lean_toolchain=(root/'lean-toolchain').read_text().strip(),
        scope='For the optional equal-mobility clock-floor revision, proved closability of both actual ordered matter factors and of all eight energy factors for epsilon>0 and abs(hbar)<=pi*epsilon. A new analytic field coefficient exp(j*s(q)/2), including its closed-strip growth bound and Fourier-shift identity, yields explicit field-polynomial product states in the reversed composition domains. The revised coordinate unitary transfers product totality to the physical Hilbert space, proving these reversed domains dense without commuting factors or assuming density of an unbounded multiplier image. Together with the preceding full common-domain density, the weighted eight-factor joint graph has a densely defined closed operator completion. The associated unaveraged fixed-time Hamiltonian is positive, self-adjoint, densely defined and closed; its domain is characterized by the closed form representation. For nonnegative mass-squared, quartic and vacuum coefficients the closed form energy on the natural common domain agrees with the specified ordered seed energy; Hamiltonian expectation has that value for states additionally in the operator domain. Common-domain states are embedded in the closed form domain; they are not asserted to lie in the Hamiltonian operator domain. The actual physical-circle averaged energy operator is constructed and closed, with exact orbit-domain and energy-integral formulas and an energy-contractive zero-charge projection. A unit-norm charge-zero state belongs to this averaged energy domain when hbar is nonzero and abs(hbar)<=2*pi*epsilon/3. This proves nontriviality, not density, of the invariant and averaged energy domains. No averaged self-adjoint Hamiltonian or constraint-preserving dynamics is claimed. A time-dependent propagator for the revised Hamiltonian, graph-core identification, finite-to-infinite Jordan/Sylvester matching, controlled regulator or continuum limits, GR/QFT recovery and empirical identification remain unproved. The original model and finite executable are unchanged; necessity of a model change is not established. The parameter bounds do not justify a zero-floor limit at fixed nonzero hbar. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_hamiltonian_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
