#!/usr/bin/env python3
"""Recompile and audit the clock-floor unitary, longitudinal transport, and actual ordered trial.

Run through the repository toolchain, using its previously verified dependencies:
  lake env python3 scripts/physical_clock_floor_unitary_audit.py --overlay PATH

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
    ('KFCausalClockFloorTestPullback', 8),
    ('KFCausalClockFloorUnitaryCoordinates', 7),
    ('KFCausalClockFloorLpCoordinates', 16),
    ('KFCausalClockFloorUnitaryTransport', 11),
    ('KFCausalClockFloorLpTransport', 6),
    ('KFCausalClockFloorLongitudinalMomentum', 11),
    ('KFCausalClockFloorClockHalf', 13),
    ('KFCausalClockFloorGroupedCoordinates', 7),
    ('KFCausalClockFloorTrialUnitary', 10),
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
    logs = overlay/'physical-clock-floor-unitary-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous = json.loads((root/'data/physical_charge_gaussian_audit.json').read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_unitary_audit.py']
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
        scope='For the optional equal-mobility clock-floor revision, constructed the actual physical L2 coordinate unitary with half-density sqrt(exp(s)+epsilon)*exp(-s). Proved the model-specific norm identity on compact continuous tests from the clock Jacobian and transverse dilation/shear Jacobian, then used the existing dense unitary extension. Proved both coordinate maps preserve null sets and established forward and inverse representative formulas on all L2 states. Conjugating clock translation gives an actual strongly continuous unitary transport group, with the explicit revised-flow half-density formula on every L2 vector. Its maximal longitudinal momentum is densely defined, closed and self-adjoint for nonzero hbar; strong orbit derivatives, invariant domain and an averaged graph core are proved. This transport parameter is not Hamiltonian time. Constructed actual positive self-adjoint shifted clock-half and inverse-half multipliers. The inverse half has full L2 domain for epsilon>0, and the exact inverse graph and preservation of nonzeroness are proved. Constructed a volume-preserving regrouping into the coordinates of the Gaussian estimates. Proved that the previously constructed nonzero physical charge-zero trial, after the actual inverse shifted clock-half and actual inverse coordinate unitary in that order, equals the L2 state of the full sheared longitudinal Gaussian. The resulting state is nonzero, its norm is identified, and the finite exponential clock-Fourier estimate transfers to its actual representative for abs(hbar)<=2*pi*epsilon/3. Identification of the fiber Fourier formula with the spectral exponential of the revised longitudinal generator, all remaining ordered energy factors, full finite-energy admissibility, common-domain density, averaged Hamiltonian and constraint-preserving dynamics remain open. The original model and finite executable are unchanged. Necessity of changing the model, finite-to-infinite Jordan/Sylvester identification, controlled limits, GR/QFT recovery and empirical identification remain unproved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_unitary_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
