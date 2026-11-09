#!/usr/bin/env python3
"""Audit transported field interpolation and the intrinsic matter lower bound.

Run with the repository toolchain and verified dependency overlay:
  lake env python3 scripts/transported_matter_interpolation_audit.py --overlay PATH

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


MODULES = [('KFCausalClockProfileCalculus', 10), ('KFCausalTransportedShearCurve', 9), ('KFCausalEigenfieldShearGraphs', 7), ('KFCausalFieldEigenpolynomials', 6), ('KFCausalActualTransportedField', 13), ('KFCausalTransportedMatterInterpolation', 11), ('KFCausalIntrinsicTransportedMatter', 4)]


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
    logs = overlay/'transported-matter-interpolation-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/coherent_interpolation_operator_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/transported_matter_interpolation_audit.py']
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
        scope='Bounded continuous complex clock profiles act continuously on the actual Hilbert space. Their Banach-algebra exponential has a proved strong operator derivative and preserves the full shear graph. For a field component P with v dot grad P = r P, the bounded multiplier exp((tau-1)*r*Delta) transforms the actual polynomial Gaussian interpolation into the unforced equation Uprime=C J U. Its output has the derived strong derivative C J squared U, with both actual shear graphs. The original linear field splits into constant and scaling components; its square splits into the constant square, twice the mixed product and the scaling square, of shear degrees zero, one half and one. Recombining these components before taking the expectation preserves all complex cross terms. All finite complex Gaussian superpositions satisfy the exact positive-production derivative qprime=2 Re inner(W J U,C W J U) and monotonicity. At tau=1 the recombined input and shear are exactly the original field-power and field-shear outputs, identified by representatives and graph uniqueness. Consequently the actual final shear expectation is bounded below by the new transported initial expectation with no integrated derivative path cost. The initial observable is changed by transport: this is not the old untransported initial expectation, and no comparison between the two initial expectations is asserted. The previous coherent-basis theorem defines intrinsic algebraic initial-input and initial-shear operators on the coherent span; arbitrary finite representations agree and their shear graph is derived. The final actual weak matter-response bound is rate >= (4/epsilon squared)*transportedInitialPairing - betaAbs*H(d_terminal), with the exact existing derivative representative, betaAbs=800*exp(4*pi/3)*hbar^4/epsilon^5 and H(d)=integral D^5*(1-D)*norm(d)^2. No sufficient energy bound or additional moment assumption is introduced. Parameters remain epsilon>0, a>0, nonzero hbar, abs(hbar)<=2*pi*epsilon/3 and the existing coherent widths. The interpolation parameter is not Hamiltonian time. This audit does not establish charge integrability or an averaged comparison for the NEW transported initial pairing; the prior three-term averaged theorem remains valid. The new initial pairing is signed, and sufficient one-sided control of it together with the terminal correction by the actual time-dependent Hamiltonian energy remains unproved. There is no claimed Hilbert-norm boundedness or closability of the unbounded field recipes, common Hamiltonian form core, momentum evolution identity, quantum clock recovery, controlled regulator limits, physical SM/GR identification or octonion necessity. No model change is established; the physical TOE is unproved. All 1465 predecessor source/script hashes are preserved.')


    target = root/'data/transported_matter_interpolation_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
