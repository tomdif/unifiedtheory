#!/usr/bin/env python3
"""Recompile and audit global existence, uniqueness and strict clock-defect decay for the full classical matter dynamics.

Run through the repository toolchain, using its previously verified dependencies:
  lake env python3 scripts/physical_clock_floor_classical_matter_global_audit.py --overlay PATH

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


MODULES = [('KFCausalClassicalMatterNeutralShift', 8), ('KFCausalClassicalMatterOrbitBounds', 9), ('KFCausalClassicalMatterNeutralBounds', 1), ('KFCausalClassicalMatterMomentumBounds', 6), ('KFCausalClassicalMatterDamping', 10), ('KFCausalClassicalMatterWindow', 4), ('KFCausalClassicalMatterUniformBound', 1), ('KFCausalClassicalMatterGlobal', 4), ('KFCausalClassicalMatterGlobalDecay', 3)]


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
    logs = overlay/'physical-clock-floor-classical-matter-global-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_classical_matter_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_classical_matter_global_audit.py']
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
        scope='For the full classical matter candidate at epsilon>0, mass2>=0, quartic>=0 and kappa>0, constructs a unique all-real-time canonical trajectory through every initial time and full phase point. No global solution is supplied as a premise and no transverse sector is fixed. Differentiating the Hamiltonian under a neutral-momentum shift identifies the actual neutral-position velocity as neutralMomentum/C plus amplitude*mean(V*exp(S/C)*slope)/C^2. The slope is controlled by the energy-controlled phaseSize. This gives a neutral-speed bound independent of neutral position, without assuming cyclicity or conserved neutral momentum. Weighted shear and polynomial potential bounds give both clock-momentum velocity tails, explicitly allowing negative matter tilt. The exact energy work law survives arbitrary scalar damping of all phase components while retaining time velocity one. For damping in [0,1], all coordinates have a uniform finite-window bound determined only by the initial state, interval and couplings. A compact cutoff gives a globally Lipschitz auxiliary field; the bound makes that cutoff identically one on each requested window, and uniqueness glues exact original-field solutions globally. Their clock defect is strictly decreasing on all real times and has a nonnegative future limit strictly below every finite-time value. That limit is not proved zero for general nonzero matter. The frozen negative-tilt witness remains valid, and a replacement for the vacuum tilt argument is still needed. The already proved global vacuum zero-defect recovery theorem remains unchanged. This proves global existence for the explicit classical candidate, not controlled identification with the ordered quantum Hamiltonian. Positive-time quantum transport, actual fixed-state quantum zero-defect convergence, joint small-floor limits, GR/QFT/Standard Model recovery and empirical identification remain open. No predecessor model definition or quantum operator changed. All 656 predecessor source/script hashes are preserved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_classical_matter_global_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
