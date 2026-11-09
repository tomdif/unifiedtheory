#!/usr/bin/env python3
"""Recompile and audit exact neutral-momentum Ehrenfest dynamics and uniform temporal Lipschitz control for actual evolved boosted states.

Run through the repository toolchain, using its previously verified dependencies:
  lake env python3 scripts/physical_clock_floor_neutral_ehrenfest_audit.py --overlay PATH

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


MODULES = [('KFCausalComplexFormObservableDerivative', 3), ('KFCausalNeutralReferenceForm', 5), ('KFCausalNeutralReferencePairing', 6), ('KFCausalNeutralWeightTime', 8), ('KFCausalNeutralEhrenfest', 6), ('KFCausalDisplacedNeutralDynamics', 7), ('KFCausalDisplacedNeutralTimeControl', 3)]


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
    logs = overlay/'physical-clock-floor-neutral-ehrenfest-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_neutral_canonical_form_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_neutral_ehrenfest_audit.py']
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
        scope='A generic complex form-observable chain rule is proved for a bounded observable and its adjoint with bounded form lifts. It uses strong form continuity, the weak mass-dual derivative and its local Lipschitz bound; it assumes neither physical strong differentiability nor Hamiltonian operator-domain invariance. The previously derived neutral translation action is transferred from the raw averaged form to the exact graph presentation used by the actual propagator, preserving physical embeddings and energy outputs and commuting with form transfer. The physical adjoint identity, reference form pairing and energy-weighted rate estimate are derived. Explicit formulas show that only ratios among the three matter-channel weights enter the neutral commutator coefficients; their common exponential time factor cancels exactly. The bound coefficient is therefore independent of time and hbar. The chain rule is applied to the actual constructed weak evolution, supplying all its hypotheses from established evolution theorems. This gives the exact complex neutral-test expectation derivative, continuity of the rate, and an all-endpoint integral identity for every initial completed form state. At canonical displacement hbar*v, the rate is bounded by a time-independent coefficient times the actual evolved energy, uniformly for bounded nonzero hbar. These theorems are specialized to the actual normalized evolved canonical boosts, and their characteristic is explicitly the existing physical Weyl characteristic at the neutral-momentum frequency. Derived uniform energy bounds and hbar convergence give eventual uniform rate and temporal Lipschitz bounds on every finite time window. The eventual index threshold works simultaneously for every neutral-momentum test frequency; the explicit bound depends on the frequency. The fixed positive clock floor and initial width, strictly positive mass-squared, quartic and vacuum coefficients, fixed initial time and boost momentum, and admissible nonzero hbar sequence tending to zero are explicit. No temporal equicontinuity, trajectory derivative, classical evolved law or new dynamical assumption is inserted. The time-ratio algebra itself includes zero couplings, but the completed-domain and dynamics application retains the strict-positive-coupling scope of its predecessor. This establishes temporal control for one actual canonical momentum test direction. It does not establish temporal control of all ten-dimensional characteristics or probability measures, quantum-to-classical transport, weak limits of unbounded energy-output pairings, subsequence independence or uniqueness of the classical transport limit. Neutral-position and negative-clock-momentum control, full twelve-dimensional limits, late-time zero clock defect, fixed-hbar recovery, floor removal, GR/QFT/Standard Model identification and empirical validity remain open. No model or preceding operator changed; all 902 predecessor source/script hashes are preserved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_neutral_ehrenfest_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
