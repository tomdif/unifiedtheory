#!/usr/bin/env python3
"""Recompile and audit global existence, uniqueness and clock recovery for the full classical vacuum candidate.

Run through the repository toolchain, using its previously verified dependencies:
  lake env python3 scripts/physical_clock_floor_classical_global_audit.py --overlay PATH

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


MODULES = [('KFCausalClassicalVacuumTranslation', 6), ('KFCausalClassicalVacuumMomentumBounds', 4), ('KFCausalClassicalVacuumCoercivity', 4), ('KFCausalClassicalVacuumDamping', 10), ('KFCausalClassicalVacuumWindow', 6), ('KFCausalClassicalVacuumUniformBound', 1), ('KFCausalClassicalVacuumGlobal', 3), ('KFCausalClassicalVacuumCompleteRecovery', 3)]


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
    logs = overlay/'physical-clock-floor-classical-global-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_classical_canonical_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_classical_global_audit.py']
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
        scope='For the previously defined full charge-averaged classical vacuum Hamiltonian, constructs a unique canonical trajectory on all real times through every initial time and phase point, when epsilon>0 and kappa>0. Proves invariance of the full differential and canonical vector field under neutral-position translations. Erasing that cyclic coordinate gives a compact-set bound on neutral speed, independent of neutral position. An exact square-sum identity controls the erased phase norm using the two clock coordinates and the charged-plus-neutral-momentum square sum. Bounds the tilted shear by (2*phaseSize/C)*F and proves an energy-only upper bound on clock-momentum velocity, complementing the previous lower bound and controlling backward momentum drift. An auxiliary scalar phase damping leaves time velocity one and preserves the exact energy law Hprime=2*growingEnergy by symplectic cancellation. It consequently preserves the finite-window energy bound. Scalar derivative estimates, compactness of the time-energy rectangle, the erased-phase estimate and neutral-speed bound give a single bound for the norm of every trajectory on [-T,T], depending only on epsilon,kappa,T and the initial state, uniformly over arbitrary damping factors in [0,1]. A smooth compact cutoff of the phase field is globally Lipschitz and therefore has a constructed global auxiliary solution. The uniform bound keeps the cutoff identically one on the requested interval, so the solution there obeys the original canonical ODE. Uniqueness glues these exact finite-window curves into an all-real-time solution; global uniqueness follows from the derived C1 vector field. A time translation removes the earlier initial-autonomous-time-zero restriction. Thus every initial time and full phase point has a unique global canonical trajectory whose clock defect tends to zero in the future. The existence and recovery statements have no assumed global trajectory, no transverse-sector restriction, and no separate clock-force premise. The damping is only a proof construction and does not change the model. This closes the full classical vacuum global-existence gap. Nonzero mass/quartic potentials are absent from the result. Controlled identification with the ordered quantum Hamiltonian, positive-time quantum transport, actual fixed-state quantum zero-defect convergence, joint small-floor limits, GR/QFT/Standard Model recovery and empirical identification remain open. No earlier model or quantum operator changed. All 636 predecessor source/script hashes are preserved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_classical_global_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
