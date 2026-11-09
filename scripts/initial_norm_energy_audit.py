#!/usr/bin/env python3
"""Audit the uniform initial interpolation norm comparison with actual energy.

Run with the repository toolchain and verified dependency overlay:
  lake env python3 scripts/initial_norm_energy_audit.py --overlay PATH

Sequential direct Lean checks rebuild three new modules, audit their axioms,
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


MODULES = [('KFCausalImaginaryShearNormConvexity', 6), ('KFCausalInitialNormVacuumComparison', 7), ('KFCausalInitialNormEnergyBound', 5)]


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
    logs = overlay/'initial-norm-energy-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/norm_matter_response_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/initial_norm_energy_audit.py']
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
        scope='The unweighted squared norm along the actual complex-clock shear interpolation is convex. For Uprime=CJ and Jprime=CK with the actual first/second self-adjoint shear graphs, the derivative of Re inner(U,CJ) is Re(inner(J,C^2 J)+inner(CJ,CJ)), nonnegative by the scalar identity |c|^2+Re(c^2)=2 Re(c)^2. The actual finite coherent paths supply these hypotheses. The clock coefficient operator commutes with physical charge; initial charge covariance and the actual four rotated shear outputs cancel the initial tangents. Therefore the sum of four final squared norms is at least four times the initial squared norm. Periodicity and continuity yield norm(I0 f)^2 <= mean norm(T action(theta) f)^2 for every actual coherent-span f, where I0 is CoherentMatterPathOperator.input at zero and T is the original ordered exponential. All cross terms remain and there is no coherent-coefficient or clock-frequency cutoff. The theorem identifies arbitrary actual graph outputs, derives continuity and integrability, and transfers to any actual averaged vacuum-form lift of f. A proved full-form factor estimate gives exp(2t)*vacuum*norm(I0 f)^2 <= norm(energyOutput u)^2 for nonnegative mass2, quartic and vacuum, any real time t and any actual full-form lift u of f. The weighted statement includes vacuum=0 and is then trivial; division is confined to an explicit vacuum>0 corollary, norm(I0 f)^2 <= exp(-2t)/vacuum*norm(energyOutput u)^2. Assumptions remain epsilon>0, a>0, nonzero hbar, abs(hbar)<=2*pi*epsilon/3, including both signs and the closed-strip boundary. This is a genuine uniform state-to-energy estimate for the UNWEIGHTED base initial map, not a bound for IntrinsicTransportedMatter.initialInput of either field power. The field-weighted initial norm costs and terminal derivative correction in the preceding matter-response bound still lack sufficient combined one-sided energy control. No common Hamiltonian form core, extension of the initial field maps, evolution invariance, momentum evolution identity, long-time quantum clock recovery, controlled regulator limits, Standard Model/GR identification or octonion necessity is established. The auxiliary interpolation is not physical time, and Hamiltonian energy is time dependent. No model change is established and the physical TOE remains unproved. All 1485 predecessor source/script hashes are preserved.')


    target = root/'data/initial_norm_energy_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
