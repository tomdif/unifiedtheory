#!/usr/bin/env python3
"""Recompile and audit the weighted classical matter Hamiltonian, local dynamics, energy bounds and an exact tilt-sign obstruction.

Run through the repository toolchain, using its previously verified dependencies:
  lake env python3 scripts/physical_clock_floor_classical_matter_audit.py --overlay PATH

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


MODULES = [('KFCausalClassicalWeightedLaplace', 1), ('KFCausalClassicalMatterSymbols', 8), ('KFCausalClassicalMatterHamiltonian', 8), ('KFCausalClassicalMatterSmooth', 7), ('KFCausalClassicalMatterODE', 5), ('KFCausalClassicalMatterEnergy', 10), ('KFCausalClassicalMatterEnergyBounds', 8), ('KFCausalClassicalMatterClock', 7), ('KFCausalClassicalMatterDefect', 5), ('KFCausalClassicalMatterTiltSign', 6)]


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
    logs = overlay/'physical-clock-floor-classical-matter-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_classical_global_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_classical_matter_audit.py']
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
        scope='Extends the explicit classical candidate to mass and quartic matter factors using the existing physical point field, full canonical charge rotation and normalized charge mean. The raw Hamiltonian is exactly the existing eight-factor energy polynomial evaluated on explicitly defined classical squared factor symbols: the field square and fourth power multiply the same exponential as the vacuum factor. This is an algebraic candidate identification, not a controlled principal-symbol theorem for the unbounded ordered quantum operators. Derives differentiation of continuous weighted exponential means and the exact clock and clock-momentum partial derivatives. The matter potential is kappa+(mass2/2)*phi^2+(quartic/4)*phi^4. For nonnegative mass2 and quartic, and nonnegative kappa, its weighted exponential mean is at least kappa. Polynomial bounded angle profiles and the analytic Banach-algebra exponential prove smoothness in every phase coordinate and time. Constructs the canonical field from the actual differential, proves symplectic cancellation, local existence for every initial time and phase point, and local uniqueness, with epsilon>=0 and arbitrary real matter and vacuum parameters. The zero-matter Hamiltonian and field agree with the frozen vacuum definitions. For nonnegative couplings, the exact work law Hprime=2*growingEnergy, with positive H and 0<=growingEnergy<=H, gives energy monotonicity and a uniform exponential energy bound on each finite existence interval. Pointwise bounds control the clock, the nine-square phaseSize, the interaction energy, clock speed at epsilon>0 and the upper clock-momentum tail at kappa>0. Clock shifts identify both clock components of the derived canonical field with the computed partial derivatives. For epsilon>0, mass2>=0, quartic>=0 and kappa>0, the clock defect is strictly decreasing along every existence interval. Global existence and the future zero-defect limit for nonzero matter remain open. An explicit phase point with mass2=2, quartic=0 and kappa=1 has shear=-cos(theta), field=1+cos(theta), and mean(potential*shear)=-1. Continuity of a differentiated weighted exponential mean proves that its weighted tilt is negative for some positive clock C and for a realizable positive-floor clock. Thus the vacuum nonnegative-tilt lemma cannot simply be reused with matter. This is an obstruction to that proof step, not a failure theorem for matter recovery or for the quantum model. The already proved global vacuum recovery theorem remains unchanged. Controlled quantum symbol identification, positive-time quantum transport, actual fixed-state quantum zero-defect convergence, joint small-floor limits, GR/QFT/Standard Model recovery and empirical identification remain open. No earlier model definition or quantum operator changed. All 645 predecessor source/script hashes are preserved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_classical_matter_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
