#!/usr/bin/env python3
"""Audit the actual weak vacuum commutator and averaged sign on the coherent span.

Run with the repository toolchain and verified dependency overlay:
  lake env python3 scripts/coherent_vacuum_weak_force_audit.py --overlay PATH

Sequential direct Lean checks rebuild seven new modules, audit their axioms,
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


MODULES = [('KFCausalRelativeGaussianClockDerivative', 4), ('KFCausalShiftedGaussianLongitudinalDifferential', 8), ('KFCausalGaussianClockMoment', 8), ('KFCausalShiftedGaussianLongitudinalDomain', 4), ('KFCausalCoherentLongitudinalDomain', 8), ('KFCausalCoherentVacuumCommutator', 5), ('KFCausalCoherentVacuumWeakForce', 7)]


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
    logs = overlay/'coherent-vacuum-weak-force-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/coherent_vacuum_sign_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/coherent_vacuum_weak_force_audit.py']
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
        scope='The actual weak pure-clock vacuum momentum response has a nonnegative charge average on every vector in the existing coherent span. The averaged response is at least its nonnegative longitudinal contribution. The missing longitudinal momentum domains of both the original coherent inputs and actual ordered-exponential outputs are derived, including the boundary of the existing closed imaginary strip. A general relative-Gaussian clock differential, an exact shifted-density cancellation, a bounded inverse complex clock, and a Gaussian clock-moment estimate give actual L2 longitudinal differentials. The original input clock prefactor is treated separately and retained. The coherent input/output pairs therefore belong to the existing joint regular graph, with both longitudinal and shear domains. Both actual compositions B T and T B exist, where B is pure-clock momentum and T the ordered exponential; their actual commutator and weak response identity follow without assuming domain membership or the identity for this family. Charge covariance identifies the input momentum orbit with U(theta) B f for a single actual B f. Actual continuous T and J T output orbits are constructed, and the scalar weak pairing with T U(theta) B f is integrable and has the stated nonnegative lower bound. No continuity or square-integrability of the latter T U(theta) B f output is asserted. Finite complex superpositions retain all interference terms and distinct seed frequencies. The assumptions remain epsilon>0, a>0, hbar!=0 and abs(hbar)<=2*pi*epsilon/3 with the existing coherent Gaussian widths. The intermediate shifted Gaussian domain theorem covers every point of the closed strip abs(y)<=pi*epsilon/3; no stricter strip or extra regularity premise is imposed. These are unnormalized quadratic expressions on a specified family. This is an actual vacuum commutator theorem, not an Ehrenfest identity along the full Hamiltonian evolution. Coherent-span Hilbert density does not establish the required Hamiltonian form core, common evolution domain, or invariance. Clock and kinetic contributions must be assembled on the same suitable domain; ordered matter control, quantitative long-time quantum clock recovery, regulator removal, physical Einstein/Standard Model identification and octonion necessity remain unproved. No Hamiltonian change is established and the physical TOE remains unproved. All 1384 predecessor source/script hashes are preserved.')


    target = root/'data/coherent_vacuum_weak_force_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
