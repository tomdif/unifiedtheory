#!/usr/bin/env python3
"""Recompile and audit the initial unbounded quantum-to-classical energy limit in the revised clock-floor model.

Run through the repository toolchain, using its previously verified dependencies:
  lake env python3 scripts/physical_clock_floor_initial_energy_audit.py --overlay PATH

This does not invoke lake build. It rebuilds all seven new modules in dependency
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


MODULES = [('KFCausalExponentialEnergyContinuity', 2), ('KFCausalClockFloorGaussianRescaling', 5), ('KFCausalClockFloorOrderedEnergyLimit', 9), ('KFCausalClockFloorTrialEnergyDecay', 5), ('KFCausalClockFloorInitialEnergyLimit', 8), ('KFCausalClockFloorInitialAveragedEnergy', 3), ('KFCausalClockFloorInitialEnergyIdentification', 10)]


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
    logs = overlay/'physical-clock-floor-initial-energy-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_classical_vacuum_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_initial_energy_audit.py']
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
        scope='For the optional equal-mobility clock-floor model, proves the actual normalized charge-zero trial family has an initial unbounded-energy limit as nonzero hbar tends to zero, at fixed epsilon>0 and clock width a>0. Exact transverse rescaling removes the hbar-dependent Gaussian width while retaining the longitudinal shear and actual ordered factor. Two-sided exponential Fourier integrability proves continuity of the fixed-profile exponential energy at zero. The actual ordered exponential output has squared norm divided by trial squared norm tending to dampedMass/clockMass, the inverse-clock energy. Actual kinetic and linear-matter squared output norms, after normalization, are O(abs(hbar)); the quadratic-matter output is O(hbar^2). All eight actual factor energy ratios converge: the clock-half factor tends to halfMass/clockMass, the four kinetic and two matter factors tend to zero, and the ordered exponential tends to dampedMass/clockMass. Their weighted sum converges to (halfMass/2+exp(2*t)*vacuum*dampedMass)/clockMass. For nonnegative mass2/quartic/vacuum, the existing normalized state in the completed charge-averaged reference form has exactly that normalized seed energy, proved using invariant-state averaging and injectivity of its physical embedding. Thus the theorem applies to the same actual states as the prior uniform-energy and initial phase-space characteristic results, with 0<abs(hbar)<=min(1,2*pi*epsilon/3). Lean identifies the limiting energy with the integrable reduced vacuum Hamiltonian H(t,s,p)=C/2+vacuum*exp(2*t+p/C)/C averaged against the already constructed classical initial probability law, supported on zero transverse coordinates and zero canonical momenta, with clock density norm(clockFunction)^2/clockMass. This is energy-form convergence at the initial state, not operator-domain membership, a full classical-symbol identification, invariance of the reduced vacuum sector in that full symbol, propagation of the initial law under quantum dynamics, or convergence of evolving unbounded energy outputs. Quantum strict decay and quantum fixed-state zero-defect limits, joint small-floor control, finite-capacity/Jordan limits, GR/QFT/Standard Model recovery, and empirical identification remain open. No prior model, factor order, or operator is changed. All 588 predecessor source/script hashes are preserved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_initial_energy_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
