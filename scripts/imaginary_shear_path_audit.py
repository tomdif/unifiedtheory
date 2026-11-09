#!/usr/bin/env python3
"""Audit the concrete imaginary-shear interpolation and its actual domains.

Run with the repository toolchain and verified dependency overlay:
  lake env python3 scripts/imaginary_shear_path_audit.py --overlay PATH

Sequential direct Lean checks rebuild six new modules, audit their axioms,
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


MODULES = [('KFCausalImaginaryShearCoefficient', 10), ('KFCausalImaginaryShearInterpolation', 11), ('KFCausalShiftedClockAmplitude', 5), ('KFCausalUniformShearGaussian', 6), ('KFCausalImaginaryShearPathBounds', 9), ('KFCausalImaginaryShearPathDomain', 10)]


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
    logs = overlay/'imaginary-shear-path-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/coherent_shear_orbit_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/imaginary_shear_path_audit.py']
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
        scope='The actual inverse-clock displacement Delta(s)=complexInverse(epsilon,chart(epsilon,s)-i*hbar/2)-s gives c(s)=i*Delta(s)/hbar with strictly positive real part and norm at most 1/(2*epsilon), for either sign of nonzero hbar within the proved strip restriction. These are derived scalar facts. The concrete interpolation F_tau has transverse scale exp(tau*Delta/2) and clock amplitude exp((tau-1)*Delta)*A. Its endpoint at tau=1 is identified almost everywhere and in physical Hilbert space with the existing shifted Gaussian. Its pointwise time derivative equals c times the shear differential momentum expression, including the density term. The shifted clock amplitude is proved L2 by a bound using the existing clock trial and inverse square-root clock factor. A uniform isotropic Gaussian lower bound for the real quadratic form retains the neutral shear and supplies an L2 envelope and quadratic moments uniformly over the closed unit interval. The resulting physical Hilbert-space path is continuous and belongs to the actual shear-generator domain at every interpolation time, with an explicit generator graph. Derived Gaussian conditions are epsilon>0, a>0, alpha>0, beta>0, 32*beta<=alpha, and abs(hbar)<=2*pi*epsilon/3; shear domain membership and strict coefficient positivity additionally use hbar!=0. The path is not claimed normalized. Strong Hilbert-space derivatives of F_tau and J F_tau, actual J-squared graphs, monotonicity of the weighted expectation, and charge-averaged initial endpoint cancellation remain unproved. A pointwise derivative and a positive scalar coefficient do not establish these missing facts. No vacuum mean-shear sign, matter-weighted sign, full Hamiltonian Ehrenfest identity, physical energy bound, evolution-invariant domain, quantum clock-error recovery, regulator removal, octonion necessity or physical TOE is derived. No Hamiltonian change is established. All 1354 predecessor source/script hashes are preserved; the TOE remains unproved.')


    target = root/'data/imaginary_shear_path_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
