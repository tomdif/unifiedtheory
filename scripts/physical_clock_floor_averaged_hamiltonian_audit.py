#!/usr/bin/env python3
"""Recompile and audit the clock-floor averaged Hamiltonian and its zero-charge compatibility.

Run through the repository toolchain, using its previously verified dependencies:
  lake env python3 scripts/physical_clock_floor_averaged_hamiltonian_audit.py --overlay PATH

This does not invoke lake build. It rebuilds all ten new modules in dependency
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
    ('KFCausalClockFloorCoherentGradientContinuity', 5),
    ('KFCausalClockFloorCoherentMomentumOrbit', 4),
    ('KFCausalClockFloorCoherentMultiplierOrbit', 6),
    ('KFCausalClockFloorCoherentShiftedOrbit', 7),
    ('KFCausalClockFloorCoherentMatterOrbit', 9),
    ('KFCausalClockFloorCoherentFormOrbit', 8),
    ('KFCausalClockFloorAveragedDensity', 9),
    ('KFCausalClockFloorAveragedHamiltonian', 10),
    ('KFCausalAveragedProjectionPairing', 3),
    ('KFCausalClockFloorHamiltonianProjection', 6),
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
    logs = overlay/'physical-clock-floor-averaged-hamiltonian-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_coherent_common_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_averaged_hamiltonian_audit.py']
    hashes = {p: sha256(root/p) for p in sources}
    assert all(hashes[p] == h for p, h in previous['source_sha256'].items())
    root_hash = sha256(root/'UnifiedTheory.lean')
    root_text = (root/'UnifiedTheory.lean').read_text()
    appended_imports = ''.join('import UnifiedTheory.Audit.'+name+'\n' for name, _ in MODULES)
    assert root_text.endswith(appended_imports), 'Expected only the new appended root imports.'
    assert hashlib.sha256(root_text[:-len(appended_imports)].encode()).hexdigest() == previous['root_check']['source_sha256']
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
    assert previous_hash == sha256(previous_path), 'Previous report changed during verification.'
    assert all(sha256(root/p) == h for p, h in hashes.items()), 'Sources changed during verification.'
    report = dict(
        modules=checks, root_check=dict(command=['lean', '-j1', 'UnifiedTheory.lean'], exit_code=0,
            empty_log=True, source_sha256=root_hash, log_sha256=sha256(log)),
        audited_declaration_count=sum(n for _, n in MODULES), source_sha256=hashes,
        previous_report=dict(path=str(previous_path.relative_to(root)), sha256=previous_hash),
        lean_toolchain=(root/'lean-toolchain').read_text().strip(),
        scope='For the optional equal-mobility clock-floor model, all eight actual energy outputs of every coherent state have continuous L2 charge orbits. Uniform half-width Gaussian majorants control transverse derivatives and the exact shifted exponential and pulled-back linear/quadratic matter outputs. Their checked operator graphs identify the full weighted joint output, yielding a continuous orbit in the completed unaveraged graph form and an explicit L2 orbit lift. Every coherent state belongs to the actual averaged energy domain. Its dense finite span proves averaged-domain density, and its zero projections prove energy-domain density within the actual zero-charge sector. The averaged energy equals the circle integral of the ordered seed energy on these states for nonnegative mass-squared, quartic and vacuum coefficients. The closed densely defined averaged output operator yields a positive self-adjoint fixed-time Hamiltonian, with the integrated energy identity and variational domain criterion proved. The zero-charge projection preserves this Hamiltonian domain and commutes with its value; the Hamiltonian maps admissible zero-sector vectors into the zero sector. This is generator-level constraint compatibility, not an evolution theorem. All physical conclusions require epsilon>0, hbar nonzero and abs(hbar)<=2*pi*epsilon/3; coherent states also use a>0. No form-core claim, time-dependent averaged propagator, removal of the clock floor at fixed nonzero hbar, finite-to-infinite Jordan/Sylvester identification, GR/QFT/SM recovery or empirical identification is established. No original-model impossibility or necessity of a model change is proved. The original model is unchanged and the TOE remains unproved.')


    target = root/'data/physical_clock_floor_averaged_hamiltonian_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
