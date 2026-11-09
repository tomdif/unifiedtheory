#!/usr/bin/env python3
"""Recompile and audit the full initial clock-derivative correspondence for actual canonical momentum boosts, including ordered mass and quartic field outputs.

Run through the repository toolchain, using its previously verified dependencies:
  lake env python3 scripts/physical_clock_floor_displaced_initial_rate_audit.py --overlay PATH

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


MODULES = [('KFCausalClockFloorDriftCoordinates', 7), ('KFCausalClockFloorDisplacedDriftIntegral', 7), ('KFCausalClockFloorDisplacedDriftDensity', 6), ('KFCausalClockFloorDisplacedDriftLimit', 5), ('KFCausalClockFloorDisplacedDriftAverage', 5), ('KFCausalClockFloorDisplacedInitialRate', 6), ('KFCausalClockFloorDisplacedDriftSymbols', 5), ('KFCausalClockFloorDisplacedRateIdentification', 6)]


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
    logs = overlay/'physical-clock-floor-displaced-initial-rate-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_displaced_clock_dynamics_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_displaced_initial_rate_audit.py']
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
        scope='The actual bounded physical drift operator is transported through the existing straightening unitary and its real quadratic pairing is identified with a clock-weighted integral. Exact formulas are proved for the actual normalized ordered exponential output and both ordered field outputs on every canonical momentum-boost charge orbit, retaining the transverse Jacobian and normalization. Integrability and dominated convergence follow from the previously proved recentered output densities, Gaussian bounds and the bounded clock drift. The limits are explicit clock-law integrals with the full shear exponential and both displaced field powers. Actual output continuity and the existing uniform orbit energy bounds justify charge-averaging these signed pairings. At the initial time, the actual reference-form trajectory output is identified almost everywhere with its constructed charge-orbit lift. This is proved for the boosted states, without assuming they are invariant charge-zero states. The classical-coefficient comparison rate equals the weighted sum of the three actual averaged drift pairings. Its limit is derived and the preceding uniform clock-rate error proves the same limit for the exact Ehrenfest derivative of the actual evolved clock expectation. Clock/angle Fubini, orbit orientation and integrability identify the limit with the physical clock-law expectation of the canonical clock-defect bracket for the full classical matter Hamiltonian, including mass and quartic couplings. Parameters are fixed positive floor and clock width, fixed canonical momentum and initial time, nonnegative mass-squared, quartic and vacuum couplings, and any nonzero hbar sequence tending to zero within the existing strip from either or mixed signs. No drift-limit, rate-limit or Hamiltonian correspondence conclusion is introduced as a hypothesis. This is an initial derivative theorem for the constructed normalized boosted family. It does not establish convergence of derivatives at positive elapsed times, identification of the preceding clock-path subsequences with the classical flow, a full phase-space measure limit, uniqueness of such a limit, or general phase-test Hamiltonian commutator control. It does not identify the fixed-hbar long-time clock defect as zero, remove the positive clock floor, or prove physical GR/QFT/Standard Model identification or empirical validity. No model or preceding operator changed; all 780 predecessor source/script hashes are preserved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_displaced_initial_rate_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
