#!/usr/bin/env python3
"""Recompile and audit the clock-floor spectral domain and explicit shifted output of the charge-zero trial.

Run through the repository toolchain, using its previously verified dependencies:
  lake env python3 scripts/physical_clock_floor_spectral_audit.py --overlay PATH

This does not invoke lake build. It rebuilds all nine new modules in dependency
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
    ('KFCausalClockFloorFourierCoordinates', 5),
    ('KFCausalClockFloorFourierMultiplier', 5),
    ('KFCausalClockFloorExponential', 13),
    ('KFCausalClockFourierFubini', 6),
    ('KFCausalClockFourierEnergyTransfer', 5),
    ('KFCausalClockFloorGaussianL1', 12),
    ('KFCausalClockFloorFullFourierEnergy', 8),
    ('KFCausalClockFloorTrialSpectralDomain', 13),
    ('KFCausalClockFloorShiftedOutput', 10),
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
    logs = overlay/'physical-clock-floor-spectral-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous = json.loads((root/'data/physical_clock_floor_unitary_audit.json').read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_spectral_audit.py']
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
        scope='For the optional equal-mobility clock-floor revision, proved diagonalization of the actual longitudinal transport in the full six-dimensional Fourier unitary and identified the maximal self-adjoint longitudinal momentum graph and domain with the real symbol 2*pi*hbar*k_clock. Constructed its positive self-adjoint spectral exponentials with exact maximal graph, energy, inverse, composition and square-root laws. Proved a general joint Fourier Fubini formula and energy-transfer theorem for continuous jointly L1 functions with joint L2 clock Fourier transform and finite exponentially weighted clock-Fourier norm; no product factorization of the input is assumed. Proved the full sheared Gaussian is jointly L1 by the existing L2 estimate with halved widths. A volume-preserving regrouping transfers the previous clock-fiber estimates to full Euclidean Fourier estimates, including an exact energy identity and a full Fourier contour-shift formula. Identified the actual physical charge-zero trial after the inverse shifted clock-half in these Fourier coordinates. For epsilon,a>0, hbar nonzero and abs(hbar)<=2*pi*epsilon/3, proved this state lies in the actual half-exponential domain, and the original nonzero charge-zero trial lies in the natural ordered E D domain, where E=exp(L/2) and D=(exp(s)+epsilon)^(-1/2). Defined the ordered factor on its exact composition domain and proved closability using the dense reversed composition; no density of the forward ordered domain is asserted. Its output graph and norm are identified explicitly with the coordinate unitary applied to the sheared Gaussian on the line Im(q)=-hbar/2. This is a finite-energy theorem for the longitudinal ordered factor, not the full eight-factor Hamiltonian. The remaining clock, gradient and matter factors, full common-domain admissibility and density, averaged Hamiltonian and constraint-preserving dynamics remain open for the revision. The original model and finite executable are unchanged. Necessity of changing the model, finite-to-infinite Jordan/Sylvester identification, controlled limits, GR/QFT recovery and empirical identification remain unproved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_spectral_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
