#!/usr/bin/env python3
"""Recompile and audit the actual averaged energy graph and its zero-sector projection.

Run through the repository toolchain, using its previously verified dependencies:
  lake env python3 scripts/physical_averaged_energy_audit.py --overlay PATH

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
    ('KFCausalProbabilityL2Mean', 7),
    ('KFCausalUnitIntervalOrbit', 8),
    ('KFCausalAveragedFormSpace', 10),
    ('KFCausalAveragedFormProjection', 9),
    ('KFCausalAveragedEnergyGraph', 10),
    ('KFCausalPhysicalAveragedEnergy', 11),
    ('KFCausalAveragedFormTransport', 7),
    ('KFCausalPhysicalAveragedTransport', 7),
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
    logs = overlay/'physical-averaged-energy-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous = json.loads((root/'data/physical_circle_action_audit.json').read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_averaged_energy_audit.py']
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
        scope='Constructed the actual orbit-averaged energy domain as a closed complete Hilbert subspace of physical states and square-integrable lifts into the original completed energy form space. Identified the probability-space Bochner mean with the adjoint of constant embedding and proved contraction. Constructed a closed single-valued averaged energy-output operator without assuming domain density or nontriviality. Identified its energy with the integral of the original energy along the normalized circle orbit. The one-period zero-charge projection preserves this averaged domain, is idempotent, and does not increase the averaged energy. Its projected state has an actual lift into the original unaveraged form domain. For fixed/zero-charge states, membership in the averaged domain is equivalent to membership in the original completed form domain. Specialized every construction to the regulated eight-factor physical energy for epsilon>0, nonzero hbar and abs(hbar)<=pi*epsilon, retaining all coupling-dependent factors and the actual circle action. Proved that this averaged domain is independent of Hamiltonian time through bounded invertible form transports that commute with zero projection. These results do not prove a nonzero admissible zero-charge state, density of the averaged domain, an averaged self-adjoint Hamiltonian, or charge-preserving Hamiltonian evolution. No dense-domain or energy-invariance certificate is assumed. Finite-to-infinite identification with exact clock/source ordering, controlled regulator/continuum limits, GR/QFT recovery and empirical identification remain open. The TOE remains unproved.')


    target = root/'data/physical_averaged_energy_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
