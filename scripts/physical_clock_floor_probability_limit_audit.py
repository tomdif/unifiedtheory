#!/usr/bin/env python3
"""Recompile and audit tight ten-coordinate probability measures, their unique characteristic representation and weak convergence along the shared global-clock subsequence.

Run through the repository toolchain, using its previously verified dependencies:
  lake env python3 scripts/physical_clock_floor_probability_limit_audit.py --overlay PATH

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


MODULES = [('KFCausalCharacteristicTailControl', 2), ('KFCausalCharacteristicTightness', 3), ('KFCausalCharacteristicRepresentation', 3), ('KFCausalTenPhaseProjection', 4), ('KFCausalTenProbabilityLimit', 2), ('KFCausalClockFloorProbabilityLimit', 2)]


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
    logs = overlay/'physical-clock-floor-probability-limit-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_positive_approximants_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_probability_limit_audit.py']
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
        scope='For a sequence of positive probability measures on a finite-dimensional real inner product space, pointwise characteristic convergence to a continuous normalized function implies tightness. Dominated convergence first controls integrated characteristic defects on each fixed interval. Continuity at zero and the integrated characteristic tail inequality give eventual small tails along every fixed projection. Individual tightness controls the finite initial prefix; the finite-dimensional projection criterion gives tightness of the entire sequence. Prokhorov supplies a weak subsequence, bounded continuous phase tests identify its characteristic, and characteristic separation proves uniqueness of the probability representing the given limiting function. A subsequence criterion then proves weak convergence of the whole sequence to that representing probability. In the physical model, a derived continuous linear projection is dual to the existing ten-dimensional canonical frequency encoding; pushforward characteristic functions are exactly the corresponding physical phase tests. The positive windowed approximants from the preceding milestone therefore have tight ten-dimensional projections and converge weakly to unique probabilities representing the previously constructed kernels. The concrete theorem constructs one strictly increasing semiclassical subsequence, a global continuous clock path, the countable-time kernels and their representing probability measures. The same subsequence gives weak convergence of the projected actual-state approximants at every member of any prescribed countable family of future times, actual quantum characteristic convergence, clock convergence on all real times uniform on every compact time set, the existing window Lipschitz bounds, and comparison-rate balance at every pair of real endpoints. No probability limit, tightness or classical evolution is assumed in that concrete theorem. Uniqueness is for the measure representing a fixed characteristic kernel, not uniqueness across different semiclassical subsequences or a classical transport theorem. The floor and initial width remain fixed and positive, the couplings nonnegative, the initial time and canonical momentum fixed, and nonzero hbar tends to zero within the existing strip from either or mixed signs. The probability measures are defined on the ten controlled phase coordinates; no full twelve-dimensional tightness or limit is claimed. Agreement of the represented probability with the global clock observable, characteristic time regularity, the missing neutral-position and negative-clock-momentum controls, Hamiltonian phase-test domain and commutator estimates, uniqueness of classical transport and quantum-to-classical dynamical identification remain open. The comparison-rate balance retains quantum energy outputs. Fixed-hbar zero clock defect, floor removal, GR/QFT/Standard Model identification and empirical validity remain open. No model or preceding operator changed; all 878 predecessor source/script hashes are preserved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_probability_limit_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
