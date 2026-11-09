#!/usr/bin/env python3
"""Recompile and audit both actual normalized ordered field-energy limits on boosted charge orbits and their circle averages, identified with classical squared symbols 5 and 6.

Run through the repository toolchain, using its previously verified dependencies:
  lake env python3 scripts/physical_clock_floor_displaced_field_limit_audit.py --overlay PATH

This does not invoke lake build. It rebuilds all five new modules in dependency
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


MODULES = [('KFCausalClockFloorRecenteredFields', 7), ('KFCausalClockFloorDisplacedFieldIntegral', 8), ('KFCausalClockFloorDisplacedFieldDensity', 7), ('KFCausalClockFloorDisplacedFieldEnergyLimit', 7), ('KFCausalClockFloorDisplacedFieldSymbols', 6)]


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
    logs = overlay/'physical-clock-floor-displaced-field-limit-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_displaced_energy_limit_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_displaced_field_limit_audit.py']
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
        scope='The actual ordered physical field evaluated at the recentered transverse coordinate is exactly the field of Q_theta+sqrt(abs(hbar))*xi; the real dilation/shear cancels without replacing the field by its value at a complex shifted position. Both field powers are treated together: the linear field energy retains the square of the displaced centre field, and the quadratic field energy retains its fourth power. A proved bound controls every continuous linear transverse field by the fixed Gaussian energy, and polynomial absorption leaves an integrable Gaussian of weaker fixed width. Compactness of the actual phase orbit provides a bound uniform in charge angle and both field powers, independent of sufficiently small nonzero hbar and the clock coordinate. The sourced multiplier outputs are identified with the actual ordered field outputs at indices 5 and 6. Their squared norms equal weighted analytic-line integrals, and the exact real-flow and concentration Jacobians are retained. The concentration factor cancels the actual trial normalization as in the preceding longitudinal theorem. Dominated convergence proves the normalized field-energy limits on each actual boosted charge orbit for every nonzero hbar sequence tending to zero within the analytic strip, of either sign, at fixed positive clock floor, positive clock width and fixed canonical momentum. No extra smallness is required of every sequence term: the bounds hold eventually by convergence. The actual operator graph and output continuity are supplied. One uniform output-energy bound justifies the charge-average limit for both field powers and arbitrary fixed continuous linear transverse field. For the model pointField, an integrable classical bound justifies exchanging clock and charge integrals, and the proved periodic orientation identity identifies the limits with the clock-law integrals of the classical charge means of squaredSymbols at indices 5 and 6. Their generally nonzero displaced-centre contributions are retained. Together with the preceding result, the three ordered exponential and matter factors now have averaged initial-energy limits. The transverse kinetic factors and clock factor still need their displaced-orbit limits and assembly into the complete averaged initial matter energy. No unbounded-Hamiltonian commutator control, quantum propagation, fixed-hbar quantum zero-defect recovery, joint small-floor limit, physical GR/QFT/Standard Model identification or empirical validation is established. No model, preceding operator or predecessor source changed. All 755 predecessor source/script hashes are preserved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_displaced_field_limit_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
