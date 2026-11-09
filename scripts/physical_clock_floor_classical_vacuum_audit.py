#!/usr/bin/env python3
"""Recompile and audit global classical vacuum-clock trajectories in the revised clock-floor model.

Run through the repository toolchain, using its previously verified dependencies:
  lake env python3 scripts/physical_clock_floor_classical_vacuum_audit.py --overlay PATH

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


MODULES = [('KFCausalGlobalLipschitzODE', 2), ('KFCausalClockFloorReducedODE', 9), ('KFCausalClockFloorVacuumReduction', 9), ('KFCausalScalarIntegratingFactor', 2), ('KFCausalClockFloorVacuumReconstruction', 10), ('KFCausalClockFloorVacuumUniqueness', 2), ('KFCausalClockFloorVacuumDynamics', 9), ('KFCausalClockFloorVacuumDefectDecay', 9)]


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
    logs = overlay/'physical-clock-floor-classical-vacuum-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_initial_phase_space_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_classical_vacuum_audit.py']
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
        scope='For the optional equal-mobility clock-floor model, proves global existence and uniqueness of the reduced classical vacuum Hamilton equations with C=exp(s)+epsilon, L=p/C, and H(t,s,p)=C/2+kappa*exp(2*t+p/C)/C. Every epsilon>0, every real coupling kappa and every initial canonical pair (s0,p0) has a solution for all real Hamiltonian times, with C>epsilon. The proof does not assume global trajectories: a general C1 globally Lipschitz ODE theorem uses Picard-Lindelof on a uniform local interval and verified continuation. The exact conserved quantity J=H-2*(exp(s)+epsilon*s) reduces s to the autonomous globally Lipschitz vector field 3/2+(J-2*epsilon+2*epsilon*s)/C. An explicit integrating-factor reconstruction recovers L and p. Both directions of the canonical-equation correspondence and uniqueness are proved. For kappa>=0 the energy is positive and nondecreasing, with H(t)<=exp(2*(t-u))*H(u) for u<=t. The defect D=epsilon/C obeys Dprime=drift(epsilon,D)*(kappa*exp(2*t+L)/C), with the same classical drift coefficient used in the existing quantum comparison theorem. For kappa>0 the classical defect is strictly decreasing and tends to zero as t tends to positive infinity; the transport coordinate grows at least linearly. Actual global solutions with this decay are constructed. At kappa=0 the clock and defect are constant and the defect cannot tend to zero. These are results for the reduced classical vacuum Hamiltonian already defined in the repository, not a proof that the full charge-averaged quantum Hamiltonian has this evolving semiclassical limit. Full symbol identification, invariance of the proposed classical reduction, transport of the previously proved initial phase-space law under the quantum evolution, and convergence of its unbounded energy outputs remain open. No quantum strict decay or quantum zero-defect limit, joint small-floor limit, finite-capacity/Jordan limit, GR/QFT/Standard Model recovery, or empirical identification is asserted. No prior model, factor ordering, or operator is changed. All 579 predecessor source/script hashes are preserved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_classical_vacuum_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
