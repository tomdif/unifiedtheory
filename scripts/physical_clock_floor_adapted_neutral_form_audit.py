#!/usr/bin/env python3
"""Audit adapted neutral-position phase covariance on the unaveraged energy form and the exact linear-coordinate compatibility obstruction.

Run through the repository toolchain, using its previously verified dependencies:
  lake env python3 scripts/physical_clock_floor_adapted_neutral_form_audit.py --overlay PATH

This does not invoke lake build. It rebuilds all five new modules in dependency
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


MODULES = [('KFCausalAdaptedNeutralModulationCoordinates', 13), ('KFCausalAdaptedNeutralModulationFactors', 10), ('KFCausalAdaptedNeutralModulationGraph', 7), ('KFCausalAdaptedNeutralModulationForm', 6), ('KFCausalNeutralLinearPhaseCompatibility', 8)]


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
    logs = overlay/'physical-clock-floor-adapted-neutral-form-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/physical_clock_floor_neutral_ehrenfest_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/physical_clock_floor_adapted_neutral_form_audit.py']
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
        scope='The actual transverse longitudinal flow shears the bare neutral position. All transverse real linear coordinates invariant under that flow are classified: they are multiples of x4-2*(x2+x3). An explicit example shows that bare x4 is not invariant. The adapted coordinate defines an actual unitary phase multiplier. Its commutation with physical floor-clock straightening and its exact coupled Fourier translation are proved on every L2 state; this translation fixes the longitudinal exponential symbol. The full natural longitudinal exponential, clock, inverse-clock, ordered exponential and matter graphs are preserved. The existing exact kinetic covariance is specialized to this phase. For the actual model directions only the second kinetic output changes. A bounded triangular map preserves the weighted joint graph and its closure without dividing by weights. Thus zero matter couplings are included. A bounded invertible lift to the completed unaveraged energy form has exact physical embedding and energy-output identities. Its output correction has norm bounded by abs(hbar)*3*abs(v)*sqrt(1/2)/sqrt(epsilon) times the physical state norm, independent of time and matter couplings. The mixed-coordinate representative of the adapted linear coordinate is identified explicitly. Its change under charge half-turn is exact; invariance under all charge rotations holds if and only if its coefficient is zero. These are real-coordinate invariance statements, not a no-go theorem for other bounded form actions. No preservation of the charge-averaged energy form by this adapted phase, no neutral-position Ehrenfest derivative or tail estimate, and no larger evolved probability limit are asserted. The preceding actual neutral-momentum Ehrenfest and temporal Lipschitz theorems remain intact. Direct averaged-domain estimates, controlled analytic or localized observables, or a larger state space with proved propagation are possible next directions; none are assumed here. Quantum-to-classical transport, limits of unbounded energy-output pairings, subsequence independence, negative clock momentum, full twelve-dimensional limits, late-time zero defect, fixed-hbar recovery, floor removal, physical GR/QFT/Standard Model identification and empirical validity remain open. No model or preceding operator changed and no result here establishes that a model change is necessary. All 910 predecessor source/script hashes are preserved. The TOE remains unproved.')


    target = root/'data/physical_clock_floor_adapted_neutral_form_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
