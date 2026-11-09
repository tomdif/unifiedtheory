#!/usr/bin/env python3
"""Recompile and audit physical resolvents and bounded-approximation dynamics.

Run through the repository toolchain, using its previously verified dependencies:
  lake env python3 scripts/physical_yosida_dynamics_audit.py --overlay PATH

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


MODULES = [
    ('KFCausalSplitTargetShiftedForm', 6),
    ('KFCausalPhysicalShiftedResolvent', 10),
    ('KFCausalPhysicalYosida', 13),
    ('KFCausalPhysicalYosidaDynamics', 16),
    ('KFCausalSplitTargetEnergyIdentities', 5),
    ('KFCausalPhysicalYosidaDerivative', 6),
    ('KFCausalPhysicalYosidaEnergy', 9),
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
    logs = overlay/'physical-yosida-dynamics-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous = json.loads((root/'data/physical_form_time_audit.json').read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_yosida_dynamics_audit.py']
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
        scope=('Constructed coercive shifted forms with separate physical '
            'and energy-output Hilbert targets. For epsilon>0 and '
            '|hbar|<=pi*epsilon, constructed positive shifted resolvents '
            'of the actual eight-factor unaveraged Hamiltonian, proved '
            'both inverse identities, inverse-curve differentiability '
            'and continuity, positivity, self-adjointness and norm bounds. '
            'Constructed bounded positive self-adjoint Yosida '
            'approximations. Their scaled resolvents converge strongly '
            'on physical L2 at each fixed time, and their Hamiltonians '
            'converge on the actual unbounded operator domain. For '
            'every positive approximation parameter, constructed '
            'all-time unitary evolution with composition, reversal, '
            'joint continuity, norm conservation and unique state '
            'solutions. The Schrodinger identity additionally requires '
            'nonzero hbar. The comparison of evolutions retains an '
            'explicit Hamiltonian-residual hypothesis. Proved '
            'operator-norm time derivatives of the physical resolvent '
            'and bounded Hamiltonian, a positive quadratic derivative '
            'identity, a completed-square energy estimate, and '
            'energy bounds along actual approximate evolutions '
            'uniform in the approximation parameter for every '
            'completed-form initial vector. No decay of '
            'that residual or convergence of evolving states is proved. '
            'These are bounded-approximation dynamics, not yet the '
            'unbounded physical propagator. Charge averaging, '
            'finite-to-infinite identification, controlled regulator '
            'and continuum limits, physical identification and the '
            'TOE remain open.'))


    target = root/'data/physical_yosida_dynamics_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
