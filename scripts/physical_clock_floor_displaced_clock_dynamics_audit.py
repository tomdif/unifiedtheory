#!/usr/bin/env python3
"""Recompile and audit actual evolved boosted states, uniform finite-window energy and clock-rate errors, and extracted clock-expectation limits.

Run through the repository toolchain, using its previously verified dependencies:
  lake env python3 scripts/physical_clock_floor_displaced_clock_dynamics_audit.py --overlay PATH

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


MODULES = [('KFCausalClockFloorDisplacedReferenceState', 7), ('KFCausalClockFloorDisplacedEvolutionBounds', 5), ('KFCausalClockFloorDisplacedClockRates', 8), ('KFCausalClockFloorDisplacedOutputContinuity', 4), ('KFCausalClockFloorDisplacedClockWindow', 6), ('KFCausalClockFloorDisplacedClockIntegral', 3), ('KFCausalClockFloorDisplacedClockCompactness', 3), ('KFCausalClockFloorDisplacedClockLimit', 2)]


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
    logs = overlay/'physical-clock-floor-displaced-clock-dynamics-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_displaced_initial_energy_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_displaced_clock_dynamics_audit.py']
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
        scope='The actual normalized canonical momentum boosts are embedded into the reference completed energy form used by the existing all-time unitary propagator. The embedding is the same physical state and its initial timeEnergy equals the preceding full averaged initial energy exactly. Its form trajectory is identified with the actual unitary evolution and retains norm one. The preceding initial-energy limit supplies an eventual bound by one plus the absolute classical initial Hamiltonian expectation; this bound is derived, not assumed. The existing form-flow energy estimate gives bounds uniform along every admissible nonzero small-hbar sequence and on each fixed finite time window for both the evolved energy and the transported form norm. The actual evolved clock-defect expectation is differentiable, lies in [0,1], and has the exact Ehrenfest rate. The comparison rate is the existing classical clock coefficient paired with actual quantum energy outputs, not an expectation under an assumed classical evolved measure. The rate difference is bounded by an explicit window constant times abs(hbar), tending uniformly to zero. Continuity of the evolving output and comparison rate is proved from the actual static/growing output splitting. The integrated expectation increment differs from the comparison-rate integral by at most that same constant times abs(hbar) times the interval length, uniformly for endpoints in the window. The clock-expectation curves have a common eventual Lipschitz constant independent of hbar. Arzela-Ascoli yields a strictly increasing subsequence converging uniformly on every chosen compact time window to a bounded continuous [0,1]-valued Lipschitz clock path. Along that same subsequence, all comparison-rate integrals within that window converge to the increments of the limiting clock path. No rate, energy, compactness or limit conclusion is introduced as a hypothesis. Parameters are fixed positive clock floor and width, fixed canonical momentum and initial time, and nonnegative mass-squared, quartic and vacuum couplings; hbar approaches zero from either or mixed sign within the existing strip. The compactness theorem is for one clock observable on one chosen finite window. It does not prove uniqueness of the limit, a common subsequence on all time windows, phase-space tightness or a probability-measure limit, identification with the full classical matter flow, or a Hamiltonian commutator theorem for general phase tests. It does not identify the fixed-hbar long-time clock defect as zero or remove the clock floor. Physical GR/QFT/Standard Model identification and empirical validation remain open. No model or preceding operator changed; all 771 predecessor source/script hashes are preserved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_displaced_clock_dynamics_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
