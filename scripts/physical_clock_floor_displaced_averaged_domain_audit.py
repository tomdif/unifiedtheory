#!/usr/bin/env python3
"""Recompile and audit the actual energy-factor domains, continuous graph-form charge orbits and averaged energy-form admissibility for the enlarged state family.

Run through the repository toolchain, using its previously verified dependencies:
  lake env python3 scripts/physical_clock_floor_displaced_averaged_domain_audit.py --overlay PATH

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


MODULES = [('KFCausalClockFloorSourcedClockMomentum', 10), ('KFCausalClockFloorSourcedSpectral', 6), ('KFCausalClockFloorSourcedCommonDomain', 6), ('KFCausalClockFloorDisplacedCommonDomain', 9), ('KFCausalClockFloorDisplacedParameterBounds', 8), ('KFCausalClockFloorSourcedMultiplierContinuity', 5), ('KFCausalClockFloorSourcedFieldContinuity', 5), ('KFCausalClockFloorDisplacedFormOrbit', 6), ('KFCausalClockFloorDisplacedAveragedDomain', 6)]


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
    logs = overlay/'physical-clock-floor-displaced-averaged-domain-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_displaced_boost_orbit_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_displaced_averaged_domain_audit.py']
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
        scope='The actual complex-sourced Gaussian states, with arbitrary complex amplitude and source and positive widths satisfying the existing neutral-shear bound, have proved clock-half, ordered inverse-clock momentum and ordered longitudinal-exponential graphs. The shifted output belongs to the physical linear and quadratic field domains; the explicit eight outputs belong to the existing eight energy-factor graphs. The enlarged displaced family with zero clock displacement is identified with these states and belongs to the natural common energy domain, as does every point of every canonical momentum-boost charge orbit. The normalized states embed with unit norm and exact seed energy in the existing completed unaveraged graph form. Displacement amplitudes and sources depend continuously on their parameters; source size is bounded around each periodic charge orbit at fixed nonzero hbar. An integrable half-width Gaussian controls the shifted sourced profiles with fixed field multipliers. Their continuous L2 outputs are proved equal to the actual spectral, physical linear-field and quadratic-field outputs. Consequently all eight actual factor outputs, the joint output and the actual completed-form vector vary continuously around each admissible charge orbit. An explicit L2 form lift satisfies the actual unitary-orbit compatibility equation. This constructs a normalized averaged-form vector and proves that every canonical momentum boost lies in the domain of the existing averaged energy operator (the form operator, not the Hamiltonian operator). Its squared energy-output norm equals the circle integral of the actual rotated seed energies for nonnegative couplings. No orbit-domain, graph-continuity or compatibility assumption is introduced. These are fixed-positive-floor and fixed-nonzero-hbar domain and integrability results within the existing strip bound. The source bounds are not uniform as hbar tends to zero. Uniform averaged energy bounds and limits, a controlled quantum derivation of the existing charge-averaged classical candidate and its flow, Hamiltonian operator-domain membership, positive-time quantum transport, fixed-hbar quantum zero-defect convergence, small-floor control and physical GR/QFT/Standard Model and empirical identification remain unproved. No model, quantum operator or predecessor source changed. All 721 predecessor source/script hashes are preserved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_displaced_averaged_domain_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
