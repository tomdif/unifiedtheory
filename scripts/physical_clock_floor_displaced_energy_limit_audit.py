#!/usr/bin/env python3
"""Recompile and audit the actual normalized longitudinal-energy limit on boosted charge orbits and its circle average, identified with the classical longitudinal squared symbol.

Run through the repository toolchain, using its previously verified dependencies:
  lake env python3 scripts/physical_clock_floor_displaced_energy_limit_audit.py --overlay PATH

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


MODULES = [('KFCausalClockFloorRecenteredJacobian', 4), ('KFCausalClockFloorDisplacedEnergyIntegral', 4), ('KFCausalClockFloorRecenteredMajorant', 8), ('KFCausalClockFloorRecenteredOutputLimit', 10), ('KFCausalClockFloorDisplacedEnergyLimit', 7), ('KFCausalClockFloorDisplacedAveragedExponentialLimit', 3), ('KFCausalClockFloorDisplacedExponentialSymbol', 5)]


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
    logs = overlay/'physical-clock-floor-displaced-energy-limit-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_displaced_density_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_displaced_energy_limit_audit.py']
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
        scope='The exact transverse integral change of variables combines the volume-preserving regrouping, the real dilation/shear Jacobian exp(-2*s), translation and five-dimensional concentration scaling sqrt(abs(hbar))^5. The concentration factor cancels the actual trial Gaussian normalization exactly. The normalized ordered longitudinal exponential output is identified with the recentered integral and is proved to belong to the actual operator graph on each charge rotation of every canonical momentum boost. The remaining clock weight, including the real-flow Jacobian, is integrable because its clock-chart transform is the square of the existing damped clock state. The fixed-width fluctuation Gaussian is integrable. These provide a proved dominating function uniform in clock coordinate, charge angle and sufficiently small nonzero hbar. Dominated convergence establishes the actual normalized longitudinal output energy limit for every nonzero hbar sequence tending to zero, of either sign, within the existing analytic strip, at fixed positive clock floor and clock width and fixed canonical momentum. The smallness conditions needed for domination are derived eventually from convergence, rather than imposed on every term. The limit at each angle is the physical clock-law average of exp((p_clock+shear(z_theta))/C)/C. A uniform output-energy bound and continuity of the actual operator outputs justify charge averaging. Fubini and the proved periodic orientation identity identify the averaged limit with the physical clock-law integral of the classical charge mean of squaredSymbols at index 7. This closes the averaged initial longitudinal factor only. Displaced-orbit ordered linear and quadratic field-factor limits, transverse kinetic limits on those orbits and complete averaged matter-energy convergence remain open. No quantum propagation, unbounded-Hamiltonian symbol or commutator control, fixed-hbar quantum zero-defect recovery, joint small-floor control, physical GR/QFT/Standard Model identification or empirical validation is established. No model, preceding quantum operator or predecessor source changed. All 747 predecessor source/script hashes are preserved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_displaced_energy_limit_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
