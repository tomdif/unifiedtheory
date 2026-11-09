#!/usr/bin/env python3
"""Recompile and audit the the full recentered longitudinal-output density limit and a uniform small-hbar Gaussian bound over every boosted charge orbit.

Run through the repository toolchain, using its previously verified dependencies:
  lake env python3 scripts/physical_clock_floor_displaced_density_audit.py --overlay PATH

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


MODULES = [('KFCausalClockFloorRescaledDisplacement', 6), ('KFCausalClockFloorCenteredDensityLimit', 8), ('KFCausalClockFloorDisplacedLineDensity', 7), ('KFCausalClockFloorDisplacedUniformShift', 5), ('KFCausalClockFloorCenteredEstimates', 10), ('KFCausalClockFloorDisplacedGaussianBound', 4), ('KFCausalClockFloorDisplacedDensityBound', 6), ('KFCausalClockFloorBoostedOrbitDensityBound', 3)]


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
    logs = overlay/'physical-clock-floor-displaced-density-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_displaced_centering_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_displaced_density_audit.py']
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
        scope='The actual complex displacement error divided by sqrt(abs(hbar)) is proved to vanish for arbitrary nonzero hbar sequences tending to zero, of either sign. Exact rescaling of both charged and neutral Gaussian widths identifies the full centred Gaussian factor with a fixed-width quadratic evaluated at these convergent fluctuations. Combining its limit with the checked clock-plus-shear phase limit proves the full pointwise recentered transverse density limit. The actual sourced analytic longitudinal-output line, including its displacement amplitude, clock Gaussian and neutral shear, is identified with this centred expression. Its full pointwise squared-modulus limit is proved on every canonical boosted charge orbit. This is the raw analytic output evaluated in rescaled coordinates; the integral Jacobian and trial normalization are separate. The actual relative complex scale has a bound of order abs(hbar), uniform in the real clock coordinate, within the strip and a stated small-hbar bound. Fixed-width coercivity and explicit shear-momentum estimates absorb the complex shift and its phase into a weaker Gaussian. For fixed positive floor, nonnegative clock width and fixed physical centre/momentum, the full recentered line density has an explicit bound independent of hbar and clock coordinate when abs(hbar)<=min(1,epsilon/2) and the existing strip bound holds. Compactness of the actual periodic phase orbit supplies one such bound for every charge angle of each canonical momentum boost. The remaining envelope is a constant times the original real clock Gaussian squared times exp(-fixed_width_quadratic(fluctuation)/4). Neither the vanishing displacement error nor the uniform orbit bound is assumed. The integral change of variables, including the exp(-2*s)*sqrt(abs(hbar))^5 Jacobian, the normalized output energy limit, ordered field-factor limits on displaced orbits, complete averaged quantum energy convergence, unbounded-Hamiltonian symbol and commutator control, positive-time quantum transport, fixed-hbar quantum zero-defect recovery, joint small-floor control and physical GR/QFT/Standard Model and empirical identification remain unproved. No model, quantum operator or predecessor source changed. All 738 predecessor source/script hashes are preserved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_displaced_density_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
