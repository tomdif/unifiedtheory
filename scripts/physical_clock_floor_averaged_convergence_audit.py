#!/usr/bin/env python3
"""Recompile and audit the complete real-cutoff convergence, uniform on compact final-time sets.

Run through the repository toolchain, using its previously verified dependencies:
  lake env python3 scripts/physical_clock_floor_averaged_convergence_audit.py --overlay PATH

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


MODULES = [
    ('KFCausalDenseIsometryLimit', 1),
    ('KFCausalClockFloorAveragedSubsequenceCompactness', 1),
    ('KFCausalClockFloorAveragedSubsequenceTrajectory', 1),
    ('KFCausalClockFloorAveragedSequenceConvergence', 3),
    ('KFCausalYosidaParameterDifference', 3),
    ('KFCausalClockFloorAveragedCutoffComparison', 2),
    ('KFCausalClockFloorAveragedRealConvergence', 9),
    ('KFCausalNormPairingStrongLimit', 1),
    ('KFCausalClockFloorAveragedJointTimeLimit', 4),
    ('KFCausalClockFloorAveragedUniformConvergence', 3),
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
    logs = overlay/'physical-clock-floor-averaged-convergence-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_averaged_evolution_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_averaged_convergence_audit.py']
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
        scope='For the optional equal-mobility clock-floor model with epsilon>0, hbar nonzero and abs(hbar)<=2*pi*epsilon/3, proved strong convergence of the complete positive-real Yosida cutoff family to the previously constructed actual averaged Hamiltonian evolution, for every physical L2 state. Every integer-cutoff subsequence has a further all-time weak trajectory of the existing verified type. Its strong limit is identified by proved uniqueness, yielding convergence of the whole integer-cutoff sequence. Two-sided resolvent equations yield an explicit Yosida parameter-difference factorization through the smoothing defect. The actual energy estimates discharge the residual hypothesis in the dynamics comparison theorem, proving a vanishing comparison bound for cutoffs at distance at most one. Rounding a positive real cutoff up to the next integer then gives convergence for all positive cutoffs, including arbitrary nonmonotone positive paths tending to infinity. Norm-preserving density extends convergence from the form domain to all L2 states. Scalar time-regularity and the pairing against the limiting form state prove strong convergence as cutoff tends to infinity while final time tends to a fixed time. This yields locally uniform strong convergence in final time and uniform convergence on every compact final-time set, for each fixed initial time and L2 state. An explicit quantified theorem gives one positive cutoff threshold for the whole compact set. No trajectory limit or convergence is assumed. The real-indexed approximation is defined as identity for nonpositive cutoffs only to make a total function; it equals the actual dynamics at every positive cutoff. This removes the auxiliary Yosida cutoff for dynamics with fixed positive clock floor; it does not remove that clock floor, assert operator-norm convergence, give a convergence rate to the unbounded evolution, prove uniformity over varying initial times, classical operator-domain regularity, finite-to-infinite Jordan/Sylvester identification, controlled physical continuum limits, GR/QFT/SM recovery or empirical identification. No further model change was required, and no original-model impossibility or necessity of a model change is proved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_averaged_convergence_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
