#!/usr/bin/env python3
"""Recompile and audit the charge-averaged classical vacuum candidate, its clock recovery theorem, and its embedded global reduced sector.

Run through the repository toolchain, using its previously verified dependencies:
  lake env python3 scripts/physical_clock_floor_averaged_classical_vacuum_audit.py --overlay PATH

This does not invoke lake build. It rebuilds all six new modules in dependency
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


MODULES = [('KFCausalClassicalChargePhase', 11), ('KFCausalClassicalChargeMean', 13), ('KFCausalClassicalChargeLaplace', 2), ('KFCausalClassicalAveragedVacuum', 10), ('KFCausalClassicalAveragedVacuumDecay', 9), ('KFCausalClassicalAveragedVacuumSector', 5)]


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
    logs = overlay/'physical-clock-floor-averaged-classical-vacuum-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_strict_decay_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_averaged_classical_vacuum_audit.py']
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
        scope='Proves the canonical phase-space lift of the actual normalized mixed-coordinate charge rotation, including exact agreement after the frequency-to-momentum scaling and preservation of the symplectic form. Identifies the actual transverse dilation/shear polynomial and four-direction kinetic polynomial in the paired coordinates. The same normalized angle measure as the quantum form yields exactly zero mean shear. The exponential mean is at least one, and the exponentially tilted shear mean is nonnegative. The averaged kinetic form is computed explicitly: it controls all eight charged phase coordinates and neutral momentum, with no neutral position term in the vacuum case. Differentiation under the compact orbit integral is proved, including the clock dependence of the exponential mean. Defines the full transverse classical vacuum candidate H=C/2+mean(K_t+kappa*exp(2*t+(p+shear)/C))/C with C=exp(s)+epsilon, and proves exact agreement with the decomposed formula. Derives its clock and canonical momentum partial derivatives and the bracket for B=p/C. For epsilon>0 and kappa>=0, B derivative is at least -1/2. With kappa>0, every globally defined trajectory satisfying those two Hamilton equations has s tending to infinity and epsilon/C tending to zero, allowing arbitrary moving transverse coordinates. An explicit primitive G with derivative C squared obeys G(s(t))>=G(s(0))+kappa*exp(B(0))*t for t>=0. The global trajectory premise is explicit: global existence for arbitrary full phase data is not proved. The zero transverse sector is validated independently: the candidate equals the earlier reduced Hamiltonian there, every transverse directional derivative vanishes, and the previously constructed reduced solutions give global solutions of this sector with defect tending to zero for every initial clock pair. No assumption of transverse-sector invariance is substituted for this verification. These are classical candidate-model results. Their identification as a controlled semiclassical limit of the ordered quantum Hamiltonian, positive-time quantum transport, the fixed-state quantum zero-defect limit, inclusion of the nonzero mass/quartic matter potentials in this classical decay argument, general global existence, joint small-floor control, GR/QFT/Standard Model recovery, and empirical identification remain open. The unaveraged exploratory stalling calculation is not a counterexample to this averaged candidate or the quantum model. No prior model, factor order, or operator is changed. All 618 predecessor source/script hashes are preserved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_averaged_classical_vacuum_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
