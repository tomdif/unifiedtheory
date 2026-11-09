#!/usr/bin/env python3
"""Recompile and audit the normalized standing-wave circle action and its zero-sector projection.

Run through the repository toolchain, using its previously verified dependencies:
  lake env python3 scripts/physical_circle_action_audit.py --overlay PATH

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


MODULES = [
    ('KFCausalPairedRotation', 11),
    ('KFCausalHaarConjugation', 2),
    ('KFCausalNormalizedChargeFlow', 14),
    ('KFCausalMixedCircleAction', 9),
    ('KFCausalPhysicalCircleAction', 12),
    ('KFCausalPeriodicUnitaryMean', 12),
    ('KFCausalStandingChargeOperator', 17),
    ('KFCausalStandingCoordinateDerivatives', 4),
    ('KFCausalFiniteStandingCharge', 13),
    ('KFCausalFiniteStandingFieldBridge', 6),
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
    logs = overlay/'physical-circle-action-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous = json.loads((root/'data/physical_mixed_coordinates_audit.json').read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_circle_action_audit.py']
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
        scope='Constructed simultaneous standing-wave rotations, proved volume preservation under their conjugation by a nonzero linear frequency-to-momentum scale, and specialized that scale to 2*pi*hbar for nonzero hbar. Constructed a 2*pi-periodic strongly continuous unitary group on the actual mixed and physical Hilbert spaces, with joint continuity in angle and state. Constructed its dimensionless charge operator as -i times the maximal strong orbit derivative and proved dense domain, closedness and self-adjointness. Proved that its zero-charge graph is exactly the closed fixed subspace. Constructed the one-period integral average as a bounded self-adjoint contractive idempotent, with range precisely that fixed subspace and invariance on either side under the circle action. Proved the explicit cosine/sine coordinate rotation and derivative laws, exact finite standing-wave charge commutators for arbitrary radial ladder weights and capacity, and their identities with the finite Hamiltonian gradient and matter-position fields, retaining the neutral matter term. This verifies normalization and covariance consistency, not an intertwiner or limit identifying the finite occupation operator with the constructed continuum generator. Nontriviality of its zero sector, a dense domain for the averaged energy form, invariance under Hamiltonian evolution, finite-to-infinite identification with exact clock/source ordering, regulator/continuum limits, GR/QFT recovery and empirical physical identification remain unproved. No energy-domain invariance is assumed. The TOE remains unproved.')


    target = root/'data/physical_circle_action_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
