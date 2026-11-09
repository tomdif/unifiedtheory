#!/usr/bin/env python3
"""Recompile and audit the complex clock inverse and field-coefficient Fourier shifts.

Run through the repository toolchain, using its previously verified dependencies:
  lake env python3 scripts/complex_clock_inverse_audit.py --overlay PATH

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
    ('KFCausalComplexClockChart', 11),
    ('KFCausalComplexClockCoercivity', 4),
    ('KFCausalComplexClockImage', 5),
    ('KFCausalComplexClockInverse', 9),
    ('KFCausalComplexClockWeights', 7),
    ('KFCausalLocalStripContour', 3),
    ('KFCausalFieldCoefficientTrials', 9),
    ('KFCausalShiftedFieldCoefficient', 8),
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
    logs = overlay/'complex-clock-inverse-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous = json.loads((root/'data/clock_momentum_closure_audit.json').read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/complex_clock_inverse_audit.py']
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
        scope=('Derived strong monotonicity and quantitative injectivity of '
            'Z(z)=exp(z)+epsilon*z on |Im(z)|<=pi/2 for epsilon>0. '
            'Proved its closed strip image closed by a Cauchy sequence '
            'argument, its open strip image open, and existence of an '
            'interior preimage for every |Im(q)|<=pi*epsilon/2 by '
            'connectedness and boundary exclusion. Constructed one inverse '
            'branch, proved it analytic near each point of the closed '
            'target strip, equal to the real chart inverse on the real '
            'axis, and Lipschitz there with constant 1/epsilon. Derived '
            'real-part, inverse-clock, and nonnegative field-coefficient '
            'growth bounds. A local-strip contour theorem yields exact '
            'Fourier translations for coefficient-weighted repaired '
            'scalar trials, including the strip boundary. These trials '
            'and their shifted modulations are L1 and L2; the shifted '
            'outputs also have finite inverse-clock energy, with explicit '
            'L2 inverse-half-clock images. The physical reversed matter '
            'operator triples, their dense domains and adjoint pairings, '
            'the full Hamiltonian form, charge averaging, physical '
            'evolution, finite-to-infinite identification, controlled '
            'limits, physical identification and the TOE remain open.'))

    target = root/'data/complex_clock_inverse_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
