#!/usr/bin/env python3
"""Audit the derived charge-averaged vacuum sign on the coherent span.

Run with the repository toolchain and verified dependency overlay:
  lake env python3 scripts/coherent_vacuum_sign_audit.py --overlay PATH

Sequential direct Lean checks rebuild nine new modules, audit their axioms,
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


MODULES = [('KFCausalBoundedClockCharge', 5), ('KFCausalImaginaryShearInitialMultiplier', 8), ('KFCausalImaginaryShearInitialEndpoint', 9), ('KFCausalImaginaryShearInitialRegularity', 7), ('KFCausalWeightedQuarterShearCancellation', 4), ('KFCausalImaginaryShearQuarterComparison', 7), ('KFCausalPeriodicFourTermAverage', 3), ('KFCausalCoherentVacuumShearSign', 9), ('KFCausalCoherentSpanVacuumSign', 5)]


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
    logs = overlay/'coherent-vacuum-sign-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/imaginary_shear_monotonicity_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/coherent_vacuum_sign_audit.py']
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
        assert not re.search(r'\b(sorry|admit|axiom|unsafe)\b', (root/source).read_text()), source
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
        scope='The charge-averaged weighted shear is nonnegative on the actual coherent span, and the averaged pure-clock vacuum response is at least its nonnegative longitudinal contribution. This is proved for the actual ordered-exponential and shear-generator outputs. A derived bounded smooth clock multiplier identifies each modified initial interpolation endpoint with the existing coherent state, retaining each seed frequency. Arbitrary bounded clock multipliers commute with actual physical charge and have derived mixed-coordinate representatives. Initial charge covariance and smooth mixed-coordinate representatives are proved for finite complex superpositions. The existing four actual shear graphs then give cancellation of the four weighted initial pairings. Combining four previously proved interpolation inequalities gives a pointwise nonnegative sum of final pairings. Periodicity, continuity and established final-output integrability yield the nonnegative charge mean; no separate assumption about the integral of the initial endpoint is used. Finite complex superpositions retain every interference term. A finite-support representation theorem transfers the result to every vector in the existing coherent span, and graph uniqueness identifies any actual output representatives. Continuous actual output orbits are constructed, so the result is not vacuous. Assumptions are epsilon>0, a>0, hbar!=0 and abs(hbar)<=2*pi*epsilon/3, with the existing ground and neutral Gaussian widths. For kappa>=0 the scaled vacuum shear contribution is nonnegative at every external time. These are unnormalized quadratic forms on a specified domain, not an asserted Hamiltonian evolution law or a pointwise-in-charge-angle sign. Coherent-span Hilbert density is not Hamiltonian form-core density or evolution invariance. Extension of the signed response to the required full evolution domain, the full Hamiltonian Ehrenfest identity, ordered matter control, quantitative long-time quantum clock-error recovery, regulator removal, physical Einstein/Standard Model identification and octonion necessity remain unproved. No Hamiltonian change is established and the physical TOE remains unproved. All 1374 predecessor source/script hashes are preserved.')


    target = root/'data/coherent_vacuum_sign_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
