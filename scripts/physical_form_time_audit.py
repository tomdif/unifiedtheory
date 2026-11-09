#!/usr/bin/env python3
"""Recompile and audit common physical form domains and their time regularity.

Run through the repository toolchain, using its previously verified dependencies:
  lake env python3 scripts/physical_form_time_audit.py --overlay PATH

This does not invoke lake build. It rebuilds all eight new modules in dependency
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
    ('KFCausalFiniteOutputRescaling', 8),
    ('KFCausalJointGraphRescaling', 6),
    ('KFCausalClosedGraphTransport', 6),
    ('KFCausalPhysicalEnergyTransport', 8),
    ('KFCausalPhysicalFormTransport', 10),
    ('KFCausalPhysicalFormTimeControl', 9),
    ('KFCausalPhysicalFormRegularity', 7),
    ('KFCausalPhysicalHamiltonianFormBridge', 3),
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
    logs = overlay/'physical-form-time-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous = json.loads((root/'data/physical_form_hamiltonian_audit.json').read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_form_time_audit.py']
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
        scope=('Constructed bounded diagonal rescaling of finite Hilbert '
            'outputs and proved orthogonal static/growing norm and inner '
            'product identities. Transported the full natural weighted '
            'joint graph and its closure directly, without a trial '
            'graph-core assumption. The eight-factor unaveraged '
            'regulated model has time-independent natural and closed '
            'form domains, including vanishing coefficients, for '
            'epsilon>0 and |hbar|<=pi*epsilon. Constructed continuous '
            'linear equivalences between completed form spaces at '
            'all times, preserving the physical embedding and giving '
            'the exact scaled energy output. On the fixed reference '
            'form space, the actual energy is A+exp(2t) B with '
            'nonnegative A and B. Proved its derivative, the relative '
            'derivative bound, energy and graph-norm comparisons, '
            'and positive coercivity. Constructed a differentiable '
            'bounded form-operator curve with continuous derivative '
            'and explicit operator-norm bounds, and identified its '
            'pairing with every transported closed form. Proved the '
            'actual unbounded Hamiltonian domain and action are '
            'characterized by this curve on the fixed reference form '
            'space. This does not identify the bounded form operator '
            'with the unbounded Hamiltonian. It does not construct '
            'physical time evolution or charge averaging. Those, '
            'finite-to-infinite identification, controlled regulator '
            'and continuum limits, physical identification and the '
            'TOE remain open.'))

    target = root/'data/physical_form_time_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
