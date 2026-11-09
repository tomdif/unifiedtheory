#!/usr/bin/env python3
"""Recompile and audit the clock dressing and the ordered joint energy domain.

Run through the repository toolchain, using its previously verified dependencies:
  lake env python3 scripts/clock_dressed_domain_audit.py --overlay PATH

This does not invoke lake build. It rebuilds all six new modules in dependency
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
    ('KFCausalClockTrialWeights', 10),
    ('KFCausalPhysicalClockPowers', 9),
    ('KFCausalClockDressedProducts', 5),
    ('KFCausalWeightedProductTotality', 6),
    ('KFCausalClockDressedActions', 8),
    ('KFCausalClockDressedDomain', 7),
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
    logs = overlay/'clock-dressed-domain-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous = json.loads((root/'data/coupled_joint_domain_audit.json').read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/clock_dressed_domain_audit.py']
    hashes = {p: sha256(root/p) for p in sources}
    assert all(hashes[p] == h for p, h in previous['source_sha256'].items())
    root_hash = sha256(root/'UnifiedTheory.lean')
    root_text = (root/'UnifiedTheory.lean').read_text()
    for name, _ in MODULES:
        assert 'import UnifiedTheory.Audit.'+name in root_text

    checks = []
    for name, count in MODULES:
        source = 'UnifiedTheory/Audit/'+name+'.lean'
        command = ['lean', '-o', str(overlay/'UnifiedTheory/Audit'/f'{name}.olean'), source]
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

    result = subprocess.run(['lean', 'UnifiedTheory.lean'], cwd=root, env=env, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    log = logs/'root-import.log'
    log.write_text(result.stdout)
    assert result.returncode == 0 and not result.stdout.strip(), str(log)
    assert root_hash == sha256(root/'UnifiedTheory.lean'), 'Root changed during verification.'
    assert all(sha256(root/p) == h for p, h in hashes.items()), 'Sources changed during verification.'
    report = dict(
        modules=checks, root_check=dict(command=['lean', 'UnifiedTheory.lean'], exit_code=0,
            empty_log=True, source_sha256=root_hash, log_sha256=sha256(log)),
        audited_declaration_count=sum(n for _, n in MODULES), source_sha256=hashes,
        lean_toolchain=(root/'lean-toolchain').read_text().strip(),
        scope=('Proved the inverse-chart bound C(q)<=1+|q| and Gaussian '
            'clock moment estimates. The half-clock dressed repaired trials '
            'and their once-more half-clock-weighted states are in actual '
            'physical L2. Positive self-adjoint clock powers C^b are constructed '
            'with exact graphs, domains, energy formulas, inverses and '
            'composition on their stated domains. For u=C^(1/2)*trial, the '
            'actual C^(-1/2) action is proved to recover trial and the actual '
            'C^(1/2) action gives the C-weighted trial. A generic Fourier '
            'uniqueness argument proves product totality for every nowhere-zero '
            'L2 clock weight, so dressed-family density is proved independently '
            'of the unbounded dressing map. An actual linear ordered domain '
            'requires u in D(C^(1/2)) and D(C^(-1/2)), with C^(-1/2)u in '
            'the previously proved longitudinal-half-exponential and smooth '
            'first-transverse-energy intersection. This domain is proved '
            'dense for epsilon>0 and the sufficient bound |hbar|<pi*epsilon. '
            'No model-specific clock-domain, cancellation or density '
            'certificate is assumed. These are fixed-regulator ordered '
            'factor results, not the full closed Hamiltonian form or a '
            'graph-core theorem. Remaining transverse components, matter '
            'weights after the longitudinal exponential, charge averaging, '
            'full physical evolution, finite-to-infinite identification, '
            'controlled limits, physical identification and the TOE remain open.'))
    target = root/'data/clock_dressed_domain_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
