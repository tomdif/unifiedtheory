#!/usr/bin/env python3
"""Audit strong imaginary-shear derivatives and weighted monotonicity.

Run with the repository toolchain and verified dependency overlay:
  lake env python3 scripts/imaginary_shear_monotonicity_audit.py --overlay PATH

Sequential direct Lean checks rebuild twelve new modules, audit their axioms,
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


MODULES = [('KFCausalShearRadius', 9), ('KFCausalGaussianFourthMoments', 6), ('KFCausalGaussianShearSlopeBounds', 6), ('KFCausalGaussianSecondShearDifferential', 10), ('KFCausalIntervalL2Derivative', 5), ('KFCausalGaussianSecondShearBounds', 11), ('KFCausalStrongImaginaryShearCurve', 11), ('KFCausalActualImaginaryShearCurve', 13), ('KFCausalClockShearPositiveVariation', 8), ('KFCausalImaginaryShearMonotonicity', 6), ('KFCausalImaginaryShearSuperposition', 13), ('KFCausalImaginaryShearCoherentBridge', 6)]


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
    logs = overlay/'imaginary-shear-monotonicity-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/imaginary_shear_path_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/imaginary_shear_monotonicity_audit.py']
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
        scope='The actual inverse-clock interpolation now has strong physical-Hilbert-space derivatives F_prime=C JF and (JF)_prime=C J_squared_F on the open unit interval, continuous F and JF on the closed interval, and actual first and second shear-generator graphs at every interpolation parameter. These statements are derived for the existing Gaussian family from polynomial Gaussian moment estimates and dominated L2 differentiation, without supplying the desired derivatives or generator graphs as assumptions. Fourth coordinate factors are proved L2 using eighth Gaussian moments. A clipped real-parameter extension avoids requiring L2 membership outside the established interval. The bounded multiplier C has the previously derived coefficient c(s)=i*Delta(s)/hbar with positive real part. Clock multiplier commutation and actual selfadjoint shear graphs prove the weighted expectation derivative q_prime=2*integral Re(c(s))*abs(W JF)^2, hence monotonicity on the closed interval, for bounded clock multipliers W including the actual root of the imaginary shifted defect. Finite complex superpositions satisfy the same derivatives, second-shear graphs, monotonicity and endpoint comparison, allowing different clock frequencies, amplitudes and widths and retaining interference terms. The coherent-family bridge identifies the endpoint with the existing actual T and JT outputs of finite coherent superpositions and proves the comparison at each charge angle. Assumptions are epsilon>0, hbar!=0, abs(hbar)<=2*pi*epsilon/3 and, for each Gaussian, a>0, alpha>0, beta>0 and 32*beta<=alpha. The interpolation is not asserted normalized or equal to Hamiltonian evolution. Charge-averaged cancellation at the modified initial endpoint is still unproved; the endpoint inequality alone does not establish a vacuum mean-shear sign. Ordered matter control, a full Hamiltonian Ehrenfest identity, physical energy control, evolution-invariant domain, quantum clock-error recovery, regulator removal, octonion necessity and physical TOE remain unproved. No Hamiltonian change is established. All 1361 predecessor source/script hashes are preserved.')


    target = root/'data/imaginary_shear_monotonicity_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
