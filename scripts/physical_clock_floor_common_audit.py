#!/usr/bin/env python3
"""Recompile and audit the eight natural clock-floor energy domains of a constructed charge-zero trial.

Run through the repository toolchain, using its previously verified dependencies:
  lake env python3 scripts/physical_clock_floor_common_audit.py --overlay PATH

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
    ('KFCausalPhysicalGaussianMoments', 6),
    ('KFCausalClockFloorTrialClockEnergy', 7),
    ('KFCausalPhysicalGaussianDerivative', 7),
    ('KFCausalClockFloorTrialMomentum', 8),
    ('KFCausalClockFloorFieldBounds', 8),
    ('KFCausalClockFloorFieldMoments', 7),
    ('KFCausalClockFloorTrialMatter', 8),
    ('KFCausalClockFloorCommonDomain', 5),
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
    logs = overlay/'physical-clock-floor-common-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous = json.loads((root/'data/physical_clock_floor_spectral_audit.json').read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_common_audit.py']
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
        scope='For the optional equal-mobility clock-floor revision, proved that the explicit physical charge-zero Gaussian belongs to the natural domains of all eight energy factors: C_epsilon^(1/2), the four P_v D factors, Phi E D, Phi^2 E D, and E D, where C_epsilon=exp(s)+epsilon, D=C_epsilon^(-1/2), and E=exp(L/2) for the actual revised longitudinal generator. Conditions are epsilon,a>0, hbar nonzero and abs(hbar)<=2*pi*epsilon/3. The theorem holds for any four transverse momentum directions and any real continuous linear transverse field. Clock exponential moments are derived for every real exponent. The actual maximal transverse momentum graph is identified using explicit L2 derivatives of the inverse-clock-damped physical Gaussian. A uniform inverse-clock comparison controls the physical real-flow norm by the positive real complex Gaussian quadratic. Quadratic field moments are absorbed by halving the transverse widths, preserving the clock profile and strip bound. These joint L2 estimates transfer through the actual coordinate unitary to both maximal field domains of the explicit E D output. The natural ordered composition domains are retained. A normalized unit-norm state is constructed in their common domain and in the actual standing-charge operator graph with output zero. The invariant common domain is therefore nontrivial. No density of the common or invariant domain, full factor-closure theorem, closed Hamiltonian form completion, averaged Hamiltonian or constraint-preserving dynamics is asserted for the revision. The original model and finite executable are unchanged. Necessity of changing the model, finite-to-infinite Jordan/Sylvester identification, controlled limits, GR/QFT recovery and empirical identification remain unproved. The present bound does not allow epsilon to tend to zero at fixed nonzero hbar. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_common_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
