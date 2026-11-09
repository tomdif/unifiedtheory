#!/usr/bin/env python3
"""Audit the actual field/shear correction and its charge-averaged matter response.

Run with the repository toolchain and verified dependency overlay:
  lake env python3 scripts/coherent_matter_shear_correction_audit.py --overlay PATH

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


MODULES = [('KFCausalFieldShearDifferential', 5), ('KFCausalCoherentShiftedRegularity', 3), ('KFCausalCoherentFieldShearGraph', 4), ('KFCausalFieldShearResponseCorrection', 3), ('KFCausalCoherentMatterShearCorrection', 1), ('KFCausalCoherentFieldDerivativeOrbit', 2), ('KFCausalAveragedMatterShearCorrection', 1)]


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
    logs = overlay/'coherent-matter-shear-correction-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/coherent_matter_response_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/coherent_matter_shear_correction_audit.py']
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
        scope='The physical field directional derivative along the actual shear velocity is derived, including its product rule with the half-density term. Every actual ordered exponential output of a coherent-span state has a C1 representative and every real transverse field-square domain. Polarization derives the L2 correction d=(v dot grad F)G for F=Phi or Phi^2, with no extra initial moment hypothesis. The actual closed shear graph satisfies J(FG)=FJG-i*hbar*d; all compositions are justified and the unbounded fields are not assumed to commute with shear. The actual matter weak response is responseL(u)+(4/epsilon^2)*Re inner(Wu,WJ(u))-2*Re inner(u,C_J d), where u=FG, C_J=(D-Z)/epsilon and W is the previously derived real clock root weight. Its correction has absolute bound (4*abs(hbar)/epsilon^2)*norm(u)*norm(D(D d)), involving a field derivative of degree at most two rather than the previous field-weighted shear output moment. This does not remove or bound the weighted shear expectation. Both physical field powers have norm-continuous charge orbits for every real transverse linear field, and polarization gives a norm-continuous d orbit. On the actual eight-factor orbit family, the weighted shear scalar and correction scalar are continuous and integrable; their separate integrals are derived without assuming norm continuity of J(FG). Each averaged matter rate is exactly its existing nonnegative longitudinal mean plus the new weighted shear mean minus the derivative correction mean. The absolute correction mean is bounded by the integral of its continuous pointwise norm bound. No sign for the weighted matter shear, sufficient one-sided energy estimate, or full evolution identity is established. Conditions remain epsilon>0, a>0, hbar!=0, abs(hbar)<=2*pi*epsilon/3 and the existing coherent widths, including the closed-strip boundary. No Hamiltonian change or extra initial-state moment premise is introduced. Combined with the existing full-form reduction, the frontier remains adequate upper control of S_matter,t, now split into derivative correction minus weighted shear. This is fixed-time form analysis, not a differentiated expectation along the actual time-dependent Hamiltonian evolution. Common Hamiltonian form-core regularity, operator-domain membership, evolution invariance, long-time quantum clock recovery, regulator removal and physical Standard Model/Einstein identification remain open. No model change is established and the physical TOE remains unproved. All 1424 predecessor source/script hashes are preserved.')


    target = root/'data/coherent_matter_shear_correction_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
