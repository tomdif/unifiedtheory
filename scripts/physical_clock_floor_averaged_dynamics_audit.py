#!/usr/bin/env python3
"""Recompile and audit time-dependent bounded approximations of the clock-floor averaged Hamiltonian.

Run through the repository toolchain, using its previously verified dependencies:
  lake env python3 scripts/physical_clock_floor_averaged_dynamics_audit.py --overlay PATH

This does not invoke lake build. It rebuilds all eighteen new modules in dependency
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
    ('KFCausalClockFloorEnergyTransport', 4),
    ('KFCausalClockFloorFormTransport', 10),
    ('KFCausalClockFloorFormTimeControl', 9),
    ('KFCausalClockFloorAveragedTransport', 7),
    ('KFCausalAveragedOutputTransport', 2),
    ('KFCausalClockFloorAveragedOutputTransport', 3),
    ('KFCausalAveragedOutputRescaling', 6),
    ('KFCausalClockFloorAveragedFormTransport', 10),
    ('KFCausalClockFloorAveragedTimeControl', 9),
    ('KFCausalClockFloorAveragedRegularity', 7),
    ('KFCausalClockFloorAveragedHamiltonianBridge', 3),
    ('KFCausalClockFloorAveragedShiftedResolvent', 10),
    ('KFCausalClockFloorAveragedYosida', 13),
    ('KFCausalClockFloorAveragedYosidaDynamics', 16),
    ('KFCausalClockFloorAveragedDynamicsProjection', 6),
    ('KFCausalClockFloorAveragedYosidaDerivative', 6),
    ('KFCausalClockFloorAveragedYosidaEnergy', 9),
    ('KFCausalClockFloorAveragedSmoothedTrajectory', 7),
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
    logs = overlay/'physical-clock-floor-averaged-dynamics-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_averaged_hamiltonian_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_averaged_dynamics_audit.py']
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
        scope='For the optional equal-mobility clock-floor model, proved time transport and common energy domains for the actual unaveraged and charge-averaged closed operators. The completed graph form of the averaged energy has norm squared equal to physical norm squared plus averaged energy; this is distinct from the orbit-lift space norm. On a fixed reference form space the actual averaged form is A* A + exp(2t) B* B, with differentiability, comparison and coercivity estimates. Constructed positive shifted resolvents of the actual averaged Hamiltonian and proved both unbounded resolvent identities. The bounded positive self-adjoint Yosida approximations converge strongly to the actual Hamiltonian on its operator domain at each fixed time. Their time-dependent evolutions are unitary, unique, reversible, compositional and jointly continuous, and obey the bounded Schrodinger equation. The actual zero-charge projection commutes with these resolvents, approximations and evolutions, so each approximate trajectory starting in the zero sector remains there. Proved resolvent and Yosida operator derivatives, an exact positive energy splitting, and uniform-in-approximation energy bounds for reference-form initial data. Constructed resolvent-smoothed form-domain trajectories with exact weak Schrodinger pairing, uniform form-energy control and squared physical mismatch bounded by exp(2*abs(t-s))*q_s(initial)/a. All physical conclusions require epsilon>0, hbar nonzero and abs(hbar)<=2*pi*epsilon/3. No unbounded averaged evolution limit, full approximation-family trajectory convergence, removal of the clock floor at fixed nonzero hbar, finite-to-infinite Jordan/Sylvester identification, GR/QFT/SM recovery or empirical identification is established. No original-model impossibility or necessity of a model change is proved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_averaged_dynamics_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
