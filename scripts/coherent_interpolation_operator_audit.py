#!/usr/bin/env python3
"""Audit representation-independent coherent interpolation operators.

Run with the repository toolchain and verified dependency overlay:
  lake env python3 scripts/coherent_interpolation_operator_audit.py --overlay PATH

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


MODULES = [('KFCausalModulatedLpIndependence', 5), ('KFCausalCoherentStateBasis', 7), ('KFCausalCoherentMatterPathOperator', 9), ('KFCausalIntrinsicMatterInterpolation', 12), ('KFCausalIntrinsicMatterResponse', 4)]


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
    logs = overlay/'coherent-interpolation-operator-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/matter_interpolation_average_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/coherent_interpolation_operator_audit.py']
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
        scope='Distinct Euclidean Fourier characters are linearly independent by Dedekind character independence; their parameter map is injective by differentiating characters along real lines. For any nowhere-zero L2 weight on finite-dimensional real Euclidean space, its modulated L2 states are linearly independent: a finite L2 relation yields an almost-everywhere character relation after division by the weight, and continuity plus full support of volume makes the relation pointwise. This is instantiated for the actual coherent states using the existing nonzero Gaussian weight, invertible momentum dilation and unitary charge coordinates. The coherent family is a basis of its algebraic coherent span, not an orthogonal basis or a basis of the full Hilbert space. Every seed recipe has a unique algebraic linear extension to that span. The actual interpolation input, field, field shear and field derivative are therefore well-defined algebraic linear operators on coherent states, with evaluation formulas for every finite representation, including repeated parameters and complex interference. Actual field/shear graphs along the interpolation and the ordered-exponential endpoint graph are derived. The initial base operator commutes with the actual charge action, without identifying distinct frequency-dependent seed multipliers. The field and derivative charge paths, their initial expectation and their integrated cost are intrinsic functions of the state. Their previously proved joint parameter continuity and angle integrability transfer to these definitions. The path cost is nonnegative, scales by the squared norm of a complex scalar, and obeys the parallelogram identity; so does its charge mean. The actual averaged matter-response lower bound is now expressed directly through these intrinsic initial and cost functionals and the existing actual terminal derivative moment, without existential coherent expansion parameters in the bound. The same physical endpoint graph premises and previously constructed actual energy-factor curves are retained. No additional initial-state moment or energy-control assumption is introduced. Existing positive-floor, nonzero-hbar, positive clock-width, closed-strip and coherent-width conditions remain unchanged for the interpolation. Independence itself requires no strip bound. No Hilbert-norm boundedness, closability, extension beyond the algebraic coherent span, common Hamiltonian form core, evolution invariance, or energy comparison is established by the basis construction. Gaussian coefficient estimates still do not imply state-independent Hamiltonian-energy bounds. The sufficient one-sided energy estimate, actual evolution identity, quantum clock recovery, controlled limits, physical SM/GR identification and octonion necessity remain open. No model change is established; the physical TOE remains unproved. All 1459 predecessor source/script hashes are preserved.')


    target = root/'data/coherent_interpolation_operator_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
