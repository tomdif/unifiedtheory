#!/usr/bin/env python3
"""Recompile and audit the complete averaged initial matter-energy limit of actual normalized canonical momentum boosts, including all eight energy factors.

Run through the repository toolchain, using its previously verified dependencies:
  lake env python3 scripts/physical_clock_floor_displaced_initial_energy_audit.py --overlay PATH

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


MODULES = [('KFCausalClockFloorDisplacedPhysicalPackets', 7), ('KFCausalClockFloorDisplacedMomentumDensity', 11), ('KFCausalClockFloorDisplacedProfileMass', 7), ('KFCausalClockFloorDisplacedKineticEnergy', 8), ('KFCausalClockFloorDisplacedClockLaw', 6), ('KFCausalClockFloorDisplacedKineticSymbols', 11), ('KFCausalClockFloorDisplacedFactorLimits', 6), ('KFCausalClockFloorDisplacedEnergyAssembly', 8), ('KFCausalClockFloorDisplacedInitialEnergy', 2)]


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
    logs = overlay/'physical-clock-floor-displaced-initial-energy-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_displaced_field_limit_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_displaced_initial_energy_audit.py']
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
        scope='The actual displaced physical packet is identified with its centred Gaussian and rescaled exactly. The sourced momentum derivative separates into a real phase momentum and an imaginary Gaussian derivative. Their squared-norm cross term is zero, giving an exact nonnegative correction proportional to abs(hbar). The correction moment is integrable by the existing physical Gaussian derivative. Exact transverse integrals and the actual trial normalization yield the clock energy halfMass/clockMass and each kinetic energy (dampedMass/clockMass)*((v dot P_theta)^2+abs(hbar)*kineticCorrection(v)). On each canonical momentum boost the phase momentum is independent of nonzero hbar. The clock-law expectations of C and inverse C are proved integrable and identified with the profile mass ratios. Charge averaging retains the exact abs(hbar) kinetic correction, and its limit matches the classical squared symbols at indices 1 through 4; the clock factor at index 0 matches exactly. Combined with the preceding field and longitudinal results, every one of the eight actual averaged factors converges to its classical clock-law and charge-mean integral. All eight classical means are proved clock-law integrable. Linear integration of the existing energy polynomial identifies the full classical matter Hamiltonian expectation. The actual averaged energy-form norm of the normalized boosted initial state is proved equal to the polynomial of the eight averaged factor energies. For fixed positive clock floor and clock width, arbitrary fixed canonical momentum, fixed form parameter t, and nonnegative mass-squared, quartic and vacuum couplings, that full initial form energy converges to the classical matter Hamiltonian expectation along every nonzero hbar sequence tending to zero within the existing analytic strip, from either or mixed sign. No desired energy limit, integrable bound, graph identity or domain property is added as an assumption. This is an initial-state result for a fixed form parameter t, not a positive-time propagated-state limit and not Hamiltonian operator-domain membership. It does not establish unbounded-Hamiltonian commutator control, quantum propagation, fixed-hbar quantum zero-defect recovery, a joint small-floor limit, physical GR/QFT/Standard Model identification or empirical validation. No model or preceding operator changed. All 761 predecessor source/script hashes are preserved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_displaced_initial_energy_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
