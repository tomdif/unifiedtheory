#!/usr/bin/env python3
"""Recompile and audit the smooth full classical vacuum Hamiltonian, its canonical ODE, local well-posedness and continuation estimates.

Run through the repository toolchain, using its previously verified dependencies:
  lake env python3 scripts/physical_clock_floor_classical_canonical_audit.py --overlay PATH

This does not invoke lake build. It rebuilds all ten new modules in dependency
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


MODULES = [('KFCausalBoundedAngleExponential', 6), ('KFCausalClassicalVacuumSmooth', 10), ('KFCausalCanonicalPhaseODE', 7), ('KFCausalClassicalVacuumLocal', 2), ('KFCausalClassicalVacuumEnergy', 12), ('KFCausalClassicalVacuumClockComponents', 8), ('KFCausalClassicalVacuumEnergyBounds', 12), ('KFCausalClassicalVacuumShearBounds', 6), ('KFCausalClassicalVacuumNeutral', 7), ('KFCausalCanonicalVacuumRecovery', 4)]


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
    logs = overlay/'physical-clock-floor-classical-canonical-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_averaged_classical_vacuum_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_classical_canonical_audit.py']
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
        scope='For the previously defined charge-averaged classical vacuum candidate, proves smoothness of the entire time-dependent Hamiltonian, including the orbit exponential, rather than assuming it. The angle profiles form a commutative Banach algebra; its analytic exponential followed by a bounded integral functional is identified with the same normalized scalar orbit average. Explicit polynomial shear coefficients transfer this smoothness to the physical paired phase variables. Builds the full canonical vector field from the actual Frechet differential and proves symplectic cancellation. With epsilon>=0 and arbitrary real kappa, every initial time and phase point has a local integral curve, and local curves through the same point are unique near that point. The autonomous time coordinate is proved to advance at unit speed. The clock and clock-momentum components are exactly the previously derived clockRate and momentumRate, using explicit clock shifts that leave the transverse Hamiltonian symbols unchanged. The energy is split into a positive static part and a nonnegative growing part when kappa>=0. Along the full canonical ODE its derivative is exactly twice the growing part, hence nonnegative and at most twice the energy. This gives a forward exponential bound and a uniform energy bound on every finite symmetric existence interval. Pointwise energy estimates control the positive clock, the sum of squares of all eight charged phase coordinates and neutral momentum, and the upper clock-momentum tail at kappa>0. The clock velocity is bounded above by H/epsilon at epsilon>0. The transverse shear is bounded by twice the charged-plus-neutral-momentum square sum, which is invariant under the charge action. Its exponential mean has an explicit upper bound in terms of time, energy and epsilon. A scalar exponential inequality gives an energy-only lower bound on clock-momentum drift. The neutral position is cyclic and its momentum is conserved under the derived ODE. Finally the canonical ODE itself supplies the clock equations of the previous recovery theorem, so every global canonical trajectory starting with autonomous time zero has defect tending to zero when epsilon>0 and kappa>0. General global existence is not yet proved: neutral-position growth and the continuation construction remain to be completed, and backward lower-tail control would also be needed for all-real-time completeness. The estimates are steps toward that proof, not a replacement for it. This is a classical vacuum candidate, with mass and quartic matter potentials absent. Its controlled quantum symbol identification, positive-time quantum transport, actual fixed-state quantum zero-defect limit, nonzero matter extension, joint small-floor limit, GR/QFT/Standard Model recovery and empirical identification remain open. No earlier model or quantum operator is changed. All 625 predecessor source/script hashes are preserved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_classical_canonical_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
