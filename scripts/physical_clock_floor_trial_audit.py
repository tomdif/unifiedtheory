#!/usr/bin/env python3
"""Recompile and audit the full sheared clock-floor Gaussian and its longitudinal Fourier energy.

Run through the repository toolchain, using its previously verified dependencies:
  lake env python3 scripts/physical_clock_floor_trial_audit.py --overlay PATH

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
    ('KFCausalClockInverseStripBounds', 5),
    ('KFCausalClockFloorShearBounds', 14),
    ('KFCausalClockFloorShearIntegrals', 11),
    ('KFCausalClockFloorFullGaussian', 12),
    ('KFCausalClockFloorGaussianFourier', 6),
    ('KFCausalClockFloorGaussianEnergy', 8),
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
    logs = overlay/'physical-clock-floor-trial-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous = json.loads((root/'data/physical_gaussian_clock_audit.json').read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_trial_audit.py']
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
        scope='For the separate equal-mobility clock-floor candidate, proved quantitative inverse-clock imaginary-part and negative-power bounds, then a positive lower bound for the full complex transverse Gaussian quadratic form including the actual neutral shear. The four charged widths are equal to alpha>0 and the neutral width beta>0 satisfies 32*beta<=alpha. Identified the real packet with the existing transverse flow acting on the diagonal physical Gaussian. Proved five-dimensional transverse L2 integrability and a norm-square integral bound by an explicit constant times exp(-2*Re(s)), integrating the real shear rather than discarding it. Constructed nonzero six-dimensional L2 Gaussian states, with an actual joint L2 continuation on every horizontal line satisfying abs(y)<=pi*epsilon/3. The clock Gaussian controls the inverse-clock tail. Derived the clock Fourier contour-shift identity and joint partial-Fourier Plancherel estimates from the actual L1/L2 Fourier bridge. Proved integrability of exp(2*pi*hbar*k) times the squared modulus of the actual clock Fourier transform, and identified the exponential Fourier norm with the shifted six-dimensional norm, whenever epsilon>0 and abs(hbar)<=2*pi*epsilon/3. This is a longitudinal-factor estimate for an optional revised candidate, not a finite-energy vector for the existing eight-factor Hamiltonian. The original model and executable remain unchanged. Weighted unitary realization for the revised flow, the other ordered energy factors, charge invariance of the trial, common-domain density, averaged Hamiltonian and constraint-preserving dynamics still need proof. Necessity of changing the original model, finite-to-infinite identification with Jordan ordering, controlled limits, GR/QFT recovery and empirical identification remain open. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_trial_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
