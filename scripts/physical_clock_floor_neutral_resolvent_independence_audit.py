#!/usr/bin/env python3
"""Audit full probability-subsequence and joint resolvent net-force limits.

Run with the repository toolchain and verified dependency overlay:
  lake env python3 scripts/physical_clock_floor_neutral_resolvent_independence_audit.py --overlay PATH

Sequential direct Lean checks rebuild five new modules, audit their axioms,
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


MODULES = [('KFCausalNeutralForceClusterIdentification', 2), ('KFCausalNeutralFullSequenceForceConvergence', 4), ('KFCausalNeutralJointForceLimit', 2), ('KFCausalNeutralProbabilityDeterminesForce', 1), ('KFCausalNeutralResolventIndependentDynamics', 1)]


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
    logs = overlay/'physical-clock-floor-neutral-resolvent-independence-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_neutral_net_force_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_neutral_resolvent_independence_audit.py']
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
        scope='The actual neutral net-force limit no longer requires a further force subsequence once the probability curve has converged. Equality of probability curves is derived from equality of the limits of their characteristic functions, using uniqueness of complex limits and characteristic-function injectivity. The existing actual global spacetime compactness theorem constructs a force cluster for any admissible hbar sequence and positive diverging resolvent sequence. If the original characteristic functions already converge to a given probability curve, the cluster probability curve is identified with that given curve. This supplies compatible global force clusters on every reindexing tending to infinity. Global net-force uniqueness for a fixed probability curve then identifies every cluster action with the chosen compatible force. The every-subsequence-has-a-subsubsequence criterion proves convergence along the ENTIRE probability-convergent sequence for every ordered real time interval and every continuous spacetime or momentum test vanishing at infinity. The positive and negative force components are not individually asserted to converge on this larger sequence. Any two positive resolvent sequences tending to infinity have net-test action difference tending to zero. A sequential characterization of limits further proves a genuine joint limit over the product filter atTop(Nat) times atTop(positive real resolvent scale). Reindexing the hbar sequence by the first coordinate and using the second coordinate as the scale reduces every sequence in the product filter to the proved full-sequence result. Thus the index and resolvent scale may tend to infinity independently; no prescribed rate relation is imposed. The convergence is for each fixed C0 test and fixed ordered real interval; no uniform convergence over the entire unit ball of tests or all endpoints is claimed. Given any actual probability-convergent admissible hbar sequence, a canonical positive reference scale n+1 constructs one global force, and all conclusions are derived: probability-curve continuity and the initial Dirac law, positive and negative force time marginals absolutely continuous with respect to volume, absence of time atoms, original physical time marginal budget, interval Schwartz balance, tensor, uniform-closure and full smooth compact-test weak equations, Fourier balance and nonzero-frequency reconstruction, global net-force uniqueness for the fixed probability curve, convergence for every positive diverging resolvent sequence, and both joint limits. The Description record bundles these CONCLUSIONS; all fields are constructed by the theorem, not assumed as extra physical hypotheses. The final existence theorem selects its strict subsequence using probability compactness ALONE and retains compact-uniform characteristic convergence, the original characteristic time Lipschitz estimate and moving-time probability convergence. It constructs the force with the complete Description on that SAME subsequence, without a subsequent force refinement and without supplying a resolvent sequence as input. Earlier theorems with compactified positive/negative component convergence on further extracted subsequences remain unchanged; component convergence is not silently transferred to the broader probability subsequence. The preceding fixed positive floor and width, positive matter coefficients, admissible nonzero hbar sequence tending to zero and original initial state remain required. No model, operator, physical evolution assumption or classical force-identification assumption is changed. The resolvent is an auxiliary scale; its independence does not remove the positive physical clock floor. Uniqueness of the probability curve across semiclassical subsequences, identification of a local classical force law, closed full phase-space dynamics, remaining canonical controls, neutral-position and negative-clock-momentum bounds, late-time zero clock defect, fixed-hbar recovery, floor removal, GR/QFT/Standard Model identification and empirical validation remain open. The net force is finite on bounded time windows through its positive pair; globally finite total mass is not assumed, and the half-difference normalization is retained. Possible escaped momentum mass in the positive/negative components remains; global positive-force tightness and absence of escaped mass are not proved. Convergence for arbitrary bounded nonvanishing tests, including the total-force constant test, is not claimed. The positive-floor clock obstruction persists. No necessity of a model change is established. All 1034 predecessor source/script hashes are preserved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_neutral_resolvent_independence_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
