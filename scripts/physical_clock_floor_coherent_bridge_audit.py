#!/usr/bin/env python3
"""Recompile and audit the physical-coordinate, spectral and matter-domain bridge for the enlarged clock-floor family.

Run through the repository toolchain, using its previously verified dependencies:
  lake env python3 scripts/physical_clock_floor_coherent_bridge_audit.py --overlay PATH

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
    ('KFCausalClockFloorCoherentCoordinates', 8),
    ('KFCausalClockFloorCoherentSources', 5),
    ('KFCausalClockFloorCoherentUnitary', 7),
    ('KFCausalClockFloorCoherentFullFourier', 11),
    ('KFCausalClockFloorCoherentSpectral', 11),
    ('KFCausalClockFloorCoherentMatter', 7),
    ('KFCausalClockFloorCoherentParameters', 10),
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
    logs = overlay/'physical-clock-floor-coherent-bridge-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous = json.loads((root/'data/physical_clock_floor_coherent_audit.json').read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_coherent_bridge_audit.py']
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
        scope='The actual total charge-modulation family is identified with translated antisymmetric Gaussians and modulated spectator Gaussians using the exact partial Fourier formula. The positive translation sign and mathlib 2*pi normalization are derived. Explicit physical complex source coefficients, clock frequency and nonzero scalar amplitude are computed, and the amplitude norm is at most one. Applying the actual inverse clock half and inverse coordinate unitary gives exactly the sourced analytic Gaussian line, retaining the full neutral shear. The earlier contour estimate now transfers to full six-dimensional Fourier exponential energy for arbitrary sources; the actual maximal longitudinal exponential graph has the explicitly shifted line as output. Consequently every physical modulation state is in the exact ordered E D, Phi E D and Phi^2 E D domains for epsilon,a>0, hbar nonzero and abs(hbar)<=2*pi*epsilon/3, with any continuous linear transverse field. These are three of the eight energy factors. Exact source-size normalization gives 4*pi^2*(norm(k)^2-k_clock^2), invariant under the charge-circle parameter rotation; the clock frequency is also invariant. An explicit Gaussian majorant controls the entire parameter orbit on the admissible complex-clock strip. The enlarged family still needs its clock-half and four ordered momentum-domain memberships, measurable graph/form orbit lifts and finite integrated full orbit energy. Averaged-domain and zero-charge energy-domain density, an averaged Hamiltonian and constraint-preserving dynamics remain open. The prior fixed-time unaveraged revised Hamiltonian and normalized averaged-energy witness remain valid. The work does not prove the original model impossible or a model change necessary. Finite-to-infinite matching, controlled regulator/continuum limits, GR/QFT/SM recovery and empirical identification remain unproved; the parameter bounds do not justify removing the clock floor at fixed nonzero hbar. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_coherent_bridge_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
