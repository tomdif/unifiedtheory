#!/usr/bin/env python3
"""Recompile and audit the actual boosted matter decay and uniform complete unaveraged energy bounds.

Run through the repository toolchain, using its previously verified dependencies:
  lake env python3 scripts/physical_clock_floor_boosted_matter_energy_audit.py --overlay PATH

This does not invoke lake build. It rebuilds all four new modules in dependency
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


MODULES = [('KFCausalClockFloorBoostedMatterBounds', 6), ('KFCausalClockFloorBoostedMatterLimit', 10), ('KFCausalClockFloorBoostedUniformEnergy', 9), ('KFCausalClockFloorBoostedEnergyRemainder', 3)]


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
    logs = overlay/'physical-clock-floor-boosted-matter-energy-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_boosted_exponential_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_boosted_matter_energy_audit.py']
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
        scope='At fixed epsilon>0, clock width a>0 and any fixed six-component canonical momentum p, the actual normalized boosted trial has uniform bounds for all eight unaveraged natural energy-factor outputs whenever h is nonzero, abs(h)<=1 and abs(h)<=2*pi*epsilon/3. The longitudinal exponential retains its actual order and neutral shear. The sourced Gaussian field-square norm is identified with its exact weighted integral. The actual normalized ordered linear matter output has squared norm at most abs(h)*(E+Q)/clockMass, and the quadratic matter output at most h^2*Q/clockMass, with explicit finite constants E=8*uniformEnvelope^2*stripMass and Q=32*uniformEnvelope^2*quadraticMass independent of h. Both ordered matter outputs therefore converge strongly to zero along every admissible sequence h->0. The boosted clock-half output has squared norm exactly halfMass/clockMass. Each ordered transverse kinetic output is bounded by 2*(kineticMass+frequency(direction)^2*dampedMass)/clockMass. Combining these with the previously proved exponential bound gives an explicit h-independent bound for the complete eight-factor seed energy and for the actual energy-output norm squared of the completed unaveraged form vector, for nonnegative mass2, quartic and vacuum couplings. All seven non-exponential factor energies have proved limits. The full seed energy minus its exact exp(2*t)*vacuum*norm(boostedExponentialOutput)^2 contribution converges to the explicit clock-plus-transverse-kinetic expression; the unresolved exponential contribution is retained, not assigned an assumed limit. These are initial-family results at fixed positive floor and fixed momentum. They do not prove convergence of that last integrated exponential energy, uniformity in the clock floor or momentum, circle-averaged form membership, zero charge of general boosts, full Hamiltonian operator-domain membership, quantum propagation to the classical law, or fixed-hbar quantum zero-defect recovery. Averaged-symbol identification, full Hamiltonian commutators, phase-space tightness, joint small-floor control, GR/QFT/Standard Model recovery and empirical identification remain open. No predecessor model or operator changed. All 702 predecessor source/script hashes are preserved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_boosted_matter_energy_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
