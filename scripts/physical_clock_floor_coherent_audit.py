#!/usr/bin/env python3
"""Recompile and audit the enlarged Gaussian family and its analytic estimates for the revised clock-floor model.

Run through the repository toolchain, using its previously verified dependencies:
  lake env python3 scripts/physical_clock_floor_coherent_audit.py --overlay PATH

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
    ('KFCausalModulatedLpTotality', 5),
    ('KFCausalChargeModulationFlow', 8),
    ('KFCausalClockFloorCoherentStates', 10),
    ('KFCausalClockFloorCoherentProjection', 5),
    ('KFCausalClockFloorCoherentBounds', 10),
    ('KFCausalClockFloorCoherentStrip', 8),
    ('KFCausalClockFloorCoherentFourier', 6),
    ('KFCausalClockFloorCoherentEnergy', 8),
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
    logs = overlay/'physical-clock-floor-coherent-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous = json.loads((root/'data/physical_clock_floor_hamiltonian_audit.json').read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_coherent_audit.py']
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
        scope='Constructed an explicit Gaussian modulation family using the actual charge-coordinate unitary and the previously proved clock-floor invariant trial. Its zero parameter is exactly that trial. Fourier uniqueness proves Hilbert-norm totality for a nowhere-zero L2 weight; applying this result to scaled charge-coordinate modulations proves totality of the physical family for epsilon,a>0 and hbar nonzero. The actual physical circle action rotates the parameters by the ordinary paired orthogonal rotation, with constant parameter norm and a continuous periodic orbit. Projecting the family by the actual zero-charge projection has closed linear span equal to the full zero-charge sector; every projected vector has zero standing-charge output. These are Hilbert-space density theorems, not energy-domain density theorems. Separately, arbitrary complex linear sources evaluated on the full complex sheared transverse position are controlled by the positive Gaussian quadratic on abs(Im(s))<=pi/3. Their exponential is absorbed into halved Gaussian widths with an explicit source-dependent constant. Real clock modulation is also bounded there. This yields joint L1 and L2 strip bounds, uniform bounds on bounded source sets, and finite quadratic physical-field moments for the sourced Gaussian on abs(Im(q))<=pi*epsilon/3, with positive widths and 32*beta<=alpha. The exact contour Fourier-shift identity, joint clock Plancherel identity, and finite exponentially weighted clock-Fourier energy are proved for abs(hbar)<=2*pi*epsilon/3. The partial-Fourier/physical-coordinate identification between the total charge-modulation family and this sourced analytic family is not yet proved, nor are all eight energy-domain memberships and integrable orbit energy for the enlarged family. Consequently density of the actual invariant or averaged energy domain, an averaged Hamiltonian and constraint-preserving dynamics remain open. The earlier fixed-time unaveraged revised Hamiltonian and normalized averaged-energy witness remain valid. Neither original-model failure nor necessity of a model change is established. Finite-to-infinite matching, controlled limits, GR/QFT recovery and empirical identification remain unproved; the parameter bounds do not justify removing the clock floor at fixed nonzero hbar. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_coherent_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
