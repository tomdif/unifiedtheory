#!/usr/bin/env python3
"""Recompile and audit the noncompact coordinate and Fourier domain identification.

Run through the repository toolchain, using its previously verified dependencies:
  lake env python3 scripts/noncompact_coordinate_domain_audit.py --overlay PATH

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
    ('KFCausalCoupledCoordinateNullSets', 6),
    ('KFCausalWeightedLpRepresentative', 3),
    ('KFCausalCoupledLpCoordinates', 12),
    ('KFCausalCoupledFunctionEnergy', 7),
    ('KFCausalCoupledLpTransport', 6),
    ('KFCausalNoncompactFourierCoordinates', 10),
    ('KFCausalL2FourierIntegral', 4),
    ('KFCausalNoncompactIntegralDomains', 4),
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
    logs = overlay/'noncompact-coordinate-domain-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous = json.loads((root/'data/longitudinal_exponential_audit.json').read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/noncompact_coordinate_domain_audit.py']
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
        scope=('Proved preservation of null sets for the actual coupled coordinate '
            'map and its inverse, using their differentiability. A dense-set '
            'extension argument with two almost-everywhere subsequences identifies '
            'the coordinate unitary and inverse on every L2 state. Explicit '
            'noncompact function pullbacks have an exact two-way L2 membership '
            'criterion, integral norm identity, and Jacobian-weighted integrability '
            'equivalence. The full longitudinal transport has its half-density '
            'representative on every L2 state. The coupled Fourier map is identified '
            'on explicit noncompact functions. Schwartz duality proves that the '
            'actual L2 Fourier transform agrees with the ordinary Fourier integral '
            'for L1 intersect L2 inputs. Consequently the actual half-exponential '
            'domain and energy of pulled-back L1/L2 functions have a proved '
            'Fourier-integral criterion. No representative or Fourier-identification '
            'certificate about the model is assumed. These are fixed-positive-regulator '
            'longitudinal results. Joint energy estimates and density for the full '
            'matter-weighted and charge-averaged Hamiltonian, a spatial differential '
            'core, full physical evolution, finite-to-infinite identification, '
            'controlled limits, physical identification and the TOE remain open.'))
    target = root/'data/noncompact_coordinate_domain_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
