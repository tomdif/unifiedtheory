#!/usr/bin/env python3
"""Recompile and audit Gaussian strip failure and the optional clock-floor flow.

Run through the repository toolchain, using its previously verified dependencies:
  lake env python3 scripts/physical_gaussian_clock_audit.py --overlay PATH

This does not invoke lake build. It rebuilds all five new modules in dependency
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
    ('KFCausalComplexPhaseWinding', 16),
    ('KFCausalGaussianSliceDomain', 11),
    ('KFCausalGaussianStripFailure', 8),
    ('KFCausalClockFloorFlow', 14),
    ('KFCausalClockFloorGaussian', 8),
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
    logs = overlay/'physical-gaussian-clock-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous = json.loads((root/'data/physical_averaged_energy_audit.json').read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_gaussian_clock_audit.py']
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
        scope='For the current regulated chart q=exp(s)+epsilon*s and source phase F=s-epsilon*exp(-s), constructed explicit points in the established analytic strip, arbitrarily close above and below the real clock axis, where the real part of fieldCoefficient(epsilon,2,q)=exp(F(s(q))) is negative. Proved the exact L2 criterion for scalar complex Gaussians and identified this coefficient with the gravity-coordinate Gaussian under the actual inverse straightening map. Real slices are L2. Every positive-width Gaussian of this form has non-L2 complex slices arbitrarily near the real axis, even after multiplication by a nonzero scalar. Fubini and continuity prove failure of joint clock-gravity L2 integrability on corresponding horizontal lines; adjoining spectators with a nowhere-zero prefactor does not repair it. This rules out the explicit Gaussian strip-continuation strategy, not all possible trial states or the full spectral or completed energy domain. A separate optional equal-mobility revision uses 1/(exp(s)+epsilon) for both clock and transverse source velocities. Constructed its complete real configuration flow, straightening homeomorphism and local mobility-error estimate. Proved its gravity Gaussian has strictly positive real width and L2 transverse slices throughout the closed target strip. The original model and finite executable are unchanged. No joint clock norm bound, sheared-matter domain theorem, weighted Hilbert realization, charge-zero finite-energy state, density or averaged Hamiltonian is established for the revision. Analytic-continuation necessity for the existing spectral domain, finite-to-infinite identification with exact Jordan ordering, controlled limits, GR/QFT recovery and empirical identification remain open. The TOE remains unproved; another model change is a tested candidate, not proved necessary.')


    target = root/'data/physical_gaussian_clock_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
