#!/usr/bin/env python3
"""Audit constructed eleven-coordinate probabilities with marginal, clock and force dynamics.

Run with the repository toolchain and verified dependency overlay:
  lake env python3 scripts/physical_clock_floor_eleven_structured_dynamics_audit.py --overlay PATH

Sequential direct Lean checks rebuild eight new modules, audit their axioms,
check the root import, and preserve the preceding source hash chain.
This does not invoke lake build and is not a TOE certificate.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess


MODULES = [('KFCausalElevenPhaseProjection', 5), ('KFCausalElevenProbabilityRepresentation', 2), ('KFCausalElevenMarginals', 9), ('KFCausalElevenClockCompatibility', 2), ('KFCausalElevenPositionProbability', 2), ('KFCausalElevenProbabilityClockPath', 1), ('KFCausalElevenMomentumMarginal', 5), ('KFCausalElevenStructuredDynamics', 1)]


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
    logs = overlay/'physical-clock-floor-eleven-structured-dynamics-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_eleven_position_limit_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_eleven_structured_dynamics_audit.py']
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
        expected = {'UnifiedTheory.Audit.'+name+'.'+n for n in
                    re.findall(r'^#print axioms (\S+)', (root/source).read_text(), re.M)}
        assert {n for n, _ in audits} == expected, (name, expected)
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
        scope='The actual eleven-coordinate characteristic limits are now represented by probability measures constructed from positive phase-space approximants of the evolved quantum states. An eleven-dimensional Euclidean coefficient space and its dual physical projection are defined explicitly; the projected characteristic equals the actual physical phase test. The projection retains the old ten physical coordinates and adds the actual neutral position. A further strictly increasing extraction uses the existing state-uniform shrinking-window approximation, so probability existence, tightness and weak convergence are derived rather than supplied. Every prescribed countable collection of independently bounded forward sampling sequences has one common subsequence, with compact-uniform canonical characteristic convergence and weak convergence of the positive eleven-coordinate approximants. Each representing probability is unique for its derived characteristic kernel; uniqueness across different extracted kernels is not claimed. Constructed LimitState and ClockLimitState records retain the all-real-time neutral-position probability curve, its initial origin, compact-uniform characteristics and moving-time weak convergence. At every convergent sampling family, the neutral-position marginal of the eleven-coordinate probability equals that curve. The actual clock Born marginal and clock-defect mean are identified with projections of the same probability. The all-real-time clock path, its bounds in [0,1], derived local Lipschitz estimate, and the limiting integrals of the actual comparison rate are preserved on this common subsequence. Its value at a convergent sampling time equals the corresponding eleven-coordinate clock-defect mean. These results require fixed positive clock floor and initial width, nonnegative couplings, and the existing admissible nonzero hbar sequence tending to zero. With strictly positive couplings, the inhabited StructuredState also retains the actual neutral-momentum probability curve, its initial law, compact-uniform characteristics, moving-time weak convergence, and a global net force. Its neutral-momentum marginal is proved equal to that curve at every convergent sampling family. The force Description is derived from the actual characteristic convergence and includes physical time bounds, no time atoms, interval balance, tensor/uniform/smooth weak equations, Fourier reconstruction, net uniqueness relative to the momentum curve, and convergence for all diverging positive resolvent scales as well as joint index/resolvent convergence. The probability, position, momentum, clock and force data all share one strictly increasing subsequence. No limiting law, compatibility field, or force description is assumed in the existence theorem. A continuous joint eleven-coordinate probability evolution, identification of the force as a classical function of that joint state, closed transport and subsequence-independent dynamics remain open. Clock momentum remains absent. Full twelve-dimensional dynamics, quantum clock-defect recovery to zero, fixed-hbar and clock-floor removal, GR/QFT/Standard Model identification and empirical validation remain open. The Hamiltonian and model are unchanged. All 1161 predecessor source/script hashes are preserved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_eleven_structured_dynamics_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
