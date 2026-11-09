#!/usr/bin/env python3
"""Recompile and audit the unbounded clock-floor averaged evolution and its zero-charge preservation.

Run through the repository toolchain, using its previously verified dependencies:
  lake env python3 scripts/physical_clock_floor_averaged_evolution_audit.py --overlay PATH

This does not invoke lake build. It rebuilds all sixteen new modules in dependency
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
    ('KFCausalClockFloorAveragedFormGeometry', 7),
    ('KFCausalClockFloorAveragedFormWindowBound', 5),
    ('KFCausalClockFloorAveragedWeakPairing', 3),
    ('KFCausalClockFloorAveragedCountableLimit', 3),
    ('KFCausalClockFloorAveragedWeakTrajectory', 5),
    ('KFCausalClockFloorAveragedWeakIntegralEquation', 8),
    ('KFCausalClockFloorAveragedWeakFormContinuity', 7),
    ('KFCausalClockFloorAveragedMassEnergy', 9),
    ('KFCausalClockFloorAveragedWeakNormConservation', 5),
    ('KFCausalClockFloorAveragedWeakUniqueness', 4),
    ('KFCausalClockFloorAveragedFormFlow', 8),
    ('KFCausalClockFloorAveragedWeakSolution', 3),
    ('KFCausalClockFloorAveragedFormLinearity', 4),
    ('KFCausalClockFloorAveragedEvolution', 13),
    ('KFCausalClockFloorAveragedEvolutionContinuity', 2),
    ('KFCausalClockFloorAveragedEvolutionProjection', 8),
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
    logs = overlay/'physical-clock-floor-averaged-evolution-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_averaged_dynamics_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_averaged_evolution_audit.py']
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
        scope='For the optional equal-mobility clock-floor model with epsilon>0, hbar nonzero and abs(hbar)<=2*pi*epsilon/3, constructed the all-time unitary evolution of the actual charge-averaged Hamiltonian in the weak-form sense. Proved separability and dense physical embedding of its completed graph form, compact-time form bounds and scalar time regularity of the actual approximations. Constructed simultaneous all-time weak subsequential limits and passed to the integrated Schrodinger form equation by dominated convergence, without assuming a limit trajectory. Auxiliary mass regularization proves physical norm conservation, strong continuity and strong convergence along the constructed cutoff subsequences for form-domain initial data. Uniqueness in the locally bounded weak-form solution class proves complex linearity, reversibility and composition; dense extension yields an evolution on every physical L2 state with joint strong continuity in both time endpoints. The actual zero-charge sector is preserved, first through the constructed strong limits and then through its proved energy-domain density. Reversibility and self-adjointness of the projection prove that this unbounded evolution commutes with zero-charge projection. Its restriction is a linear isometric equivalence of the zero-charge sector, and evolved zero-sector states have zero output from the actual standing-charge operator. Identification with the ordered seed energy uses the preceding nonnegative-coupling hypotheses. This does not assert classical differentiability or Hamiltonian operator-domain invariance for every L2 state, convergence of the full approximation family, removal of the clock floor at fixed nonzero hbar, finite-to-infinite Jordan/Sylvester identification, GR/QFT/SM recovery or empirical identification. No further model change was required and no original-model impossibility or necessity of a model change is proved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_averaged_evolution_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
