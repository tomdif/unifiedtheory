#!/usr/bin/env python3
"""Recompile and audit the eight-factor unbounded weak-form evolution.

Run through the repository toolchain, using its previously verified dependencies:
  lake env python3 scripts/physical_unbounded_evolution_audit.py --overlay PATH

This does not invoke lake build. It rebuilds all seventeen new modules in dependency
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
    ('KFCausalPhysicalFormGeometry', 6),
    ('KFCausalPhysicalSmoothedTrajectory', 7),
    ('KFCausalPhysicalFormWindowBound', 5),
    ('KFCausalPhysicalWeakPairing', 3),
    ('KFCausalPhysicalCountableLimit', 3),
    ('KFCausalPhysicalWeakTrajectory', 5),
    ('KFCausalPhysicalWeakIntegralEquation', 8),
    ('KFCausalPhysicalWeakFormContinuity', 7),
    ('KFCausalPhysicalMassEnergy', 9),
    ('KFCausalPhysicalWeakNormConservation', 5),
    ('KFCausalPhysicalWeakUniqueness', 4),
    ('KFCausalPhysicalFormFlow', 8),
    ('KFCausalPhysicalWeakSolution', 3),
    ('KFCausalPhysicalFormLinearity', 4),
    ('KFCausalPhysicalEvolution', 13),
    ('KFCausalStrongIsometryContinuity', 2),
    ('KFCausalPhysicalEvolutionContinuity', 2),
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
    logs = overlay/'physical-unbounded-evolution-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous = json.loads((root/'data/physical_yosida_dynamics_audit.json').read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_unbounded_evolution_audit.py']
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
        scope=('For epsilon>0 and |hbar|<=pi*epsilon, proved separability '
            'and dense embedding of the actual eight-factor completed '
            'form spaces. Constructed resolvent-smoothed approximate '
            'trajectories, with squared physical mismatch O(1/a), '
            'uniform form-norm bounds on compact time intervals and '
            'uniform Lipschitz bounds on scalar form-test pairings. '
            'Constructed simultaneous all-time weak subsequential '
            'limits and passed to the actual integrated form equation. '
            'Proved physical norm conservation via auxiliary mass '
            'regularization, strong continuity, and strong convergence '
            'along the constructed subsequences for form-domain initial '
            'data. Proved uniqueness in the locally bounded weak-form '
            'solution class, complex linearity, reversibility and '
            'composition. Constructed an all-time unitary evolution on '
            'all physical L2 states by dense extension, with joint '
            'strong continuity in both time endpoints. For nonzero '
            'hbar, its form-domain trajectories satisfy the integrated '
            'Schrodinger equation of the actual unbounded Hamiltonian '
            'form. This does not assert classical differentiability or '
            'operator-domain invariance for every L2 state, convergence '
            'of the full approximation family, charge averaging, '
            'finite-to-infinite identification, clock-regulator removal, '
            'continuum limits, GR/QFT recovery or physical identification. '
            'The TOE remains unproved.'))


    target = root/'data/physical_unbounded_evolution_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
