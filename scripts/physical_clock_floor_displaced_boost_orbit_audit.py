#!/usr/bin/env python3
"""Recompile and audit the enlarged structured state family, exact charge covariance and physical momentum-boost orbit identification.

Run through the repository toolchain, using its previously verified dependencies:
  lake env python3 scripts/physical_clock_floor_displaced_boost_orbit_audit.py --overlay PATH

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


MODULES = [('KFCausalChargeDisplacementCovariance', 7), ('KFCausalClockFloorDisplacedStates', 9), ('KFCausalFourierPhasePackets', 7), ('KFCausalDisplacedPairedCoordinates', 7), ('KFCausalDisplacedBoostParameters', 4), ('KFCausalClockFloorDisplacedBoostOrbit', 9), ('KFCausalClockFloorDisplacedSources', 6)]


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
    logs = overlay/'physical-clock-floor-displaced-boost-orbit-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_boosted_energy_limit_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_displaced_boost_orbit_audit.py']
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
        scope='The larger structured state family is constructed by genuine L2 unitary translations and phases in normalized charge coordinates, with two independent six-real-component parameter vectors. The exact charge covariance is proved on all mixed-coordinate L2 states, without Gaussian or energy-domain assumptions: both displacement and phase parameters rotate by the inverse orthogonal rotation. Conjugating by the existing physical charge-coordinate unitary and applying the result to the actual trial gives raw and normalized states, unit norm, exact charge-orbit closure and strong orbit continuity. The preceding coherent family is the zero-displacement slice. Fourier modulation and translated-modulation identities are proved with their actual sign and 2*pi convention, and identify the physical paired-coordinate representative of every member. Every six-component canonical physical momentum boost of the normalized trial is proved to be a member, and its full actual charge orbit is identified with the rotated two-parameter state. Clock and neutral displacement coordinates remain zero along these boosted orbits. The two symmetric-position displacement parameters are sin(theta)/sqrt(2) times the corresponding paired momentum differences, independently of nonzero hbar; therefore ignoring the displaced orbit is not justified by small hbar. For arbitrary parameters with zero clock displacement, the actual physical representative is an explicit complex-sourced Gaussian with the unchanged clock function. Its amplitude has norm at most one. The normalized physical source formula is proved for the entire actual boosted charge orbit. These are exact Hilbert-space, Fourier and representative results. They do not yet prove common energy-domain membership of the full enlarged orbit, its integrable form lift, circle-averaged energy bounds or limits, a general Hamiltonian symbol theorem, positive-time quantum transport, fixed-hbar quantum zero-defect convergence, small-floor control, or physical GR/QFT/Standard Model and empirical identification. No predecessor model or quantum operator changed; this enlarges the state family to remove a missing coordinate bridge. All 713 predecessor source/script hashes are preserved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_displaced_boost_orbit_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
