#!/usr/bin/env python3
"""Audit charge averaging of the actual matter-shear interpolation.

Run with the repository toolchain and verified dependency overlay:
  lake env python3 scripts/matter_interpolation_average_audit.py --overlay PATH

Sequential direct Lean checks rebuild four new modules, audit their axioms,
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


MODULES = [('KFCausalShearSourceOrbitContinuity', 6), ('KFCausalCoherentMatterInterpolationOrbit', 9), ('KFCausalAveragedMatterInterpolation', 5), ('KFCausalInterpolatedMatterResponse', 1)]


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
    logs = overlay/'matter-interpolation-average-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/matter_interpolation_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/matter_interpolation_average_audit.py']
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
        declared = {'UnifiedTheory.Audit.'+name+'.'+n for n in re.findall(r'^theorem (\S+)', (root/source).read_text(), re.M)}
        assert {n for n, _ in audits} == expected == declared, (name, expected, declared)
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
        scope='For continuous Gaussian source orbits of fixed squared source norm, one common Gaussian envelope and a uniform first-shear polynomial bound prove joint strong L2 continuity in charge angle and the clipped auxiliary interpolation parameter. Actual coherent charge rotation preserves the source norm and clock frequency; the preceding generic continuity theorem is therefore instantiated without new analytic assumptions. The field, actual field shear and field derivative paths are jointly norm-continuous for finite complex coherent superpositions, retaining their cross terms. The weighted shear expectation is jointly continuous. The integral over the interpolation interval of the squared weighted field derivative is a continuous function of charge angle. Both the signed initial expectation and the path cost are separately charge-integrable. The pointwise interpolation comparison consequently yields the actual charge-averaged comparison. Endpoint graph uniqueness identifies the constructed paths with given actual ordered-exponential, field-power and shear outputs, and proves continuity of those field/shear output curves without assuming it. One fixed finite coherent representation is used at every angle; the result extends to every state in the existing coherent span. For the existing physical weight W, the actual averaged weighted shear is at least (4/epsilon^2)*mean(initial expectation)-(hbar^2/epsilon^3)*mean(path cost). Combining this with the preceding actual longitudinal absorption theorem gives, for each of the two matter factors of the same coherent state and the same actual energy-factor outputs, matter rate >= (4/epsilon^2)*mean(initial expectation)-(hbar^2/epsilon^3)*mean(path cost)-betaAbs*mean(terminal derivative moment), where betaAbs=800*exp(4*pi/3)*hbar^4/epsilon^5. All three scalar terms are integrable. Existing positive-floor, nonzero-hbar, positive clock-width, closed-strip and coherent-width conditions are unchanged. The auxiliary parameter is not Hamiltonian time. No sign or sufficient Hamiltonian-energy control of the initial expectation is proved, and no sufficient energy bound for the path or terminal derivative costs is proved. No interchange of unbounded operators along actual evolution, common Hamiltonian form core, evolution identity, long-time quantum clock recovery, controlled limit, physical Standard Model/Einstein identification or octonion necessity is established. No model change is established; the physical TOE remains unproved. All 1454 predecessor source/script hashes are preserved.')


    target = root/'data/matter_interpolation_average_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
