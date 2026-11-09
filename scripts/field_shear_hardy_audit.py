#!/usr/bin/env python3
"""Audit the actual field-derivative Hardy estimate and matter correction bound.

Run with the repository toolchain and verified dependency overlay:
  lake env python3 scripts/field_shear_hardy_audit.py --overlay PATH

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


MODULES = [('KFCausalTransportedInitialPolynomial', 8), ('KFCausalFieldSlopeShearGraph', 6), ('KFCausalFieldShearHardy', 11), ('KFCausalFieldShearHardyCorrection', 6)]


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
    logs = overlay/'field-shear-hardy-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/initial_norm_energy_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/field_shear_hardy_audit.py']
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
        scope='The actual transported initial field is identified pointwise as [constantField(l)+exp(-Delta/2)*scaleField(l)]^p times the unweighted I0 input, p=1,2. For pointField this is [q4+(3 exp(-Delta/2)-2)(q2+q3)]^p. This checks the polynomial in the preceding numerical probe, but does not certify its quadrature or prove a counterexample. The first derivative d=Fprime*g of F=l^p has a constructed actual shear graph Jd=Fprime*Jg-i*h*Fsecond*g. All L2 requirements follow from the actual coherent output and shear fourth-moment domains. The second field derivative and the exact polynomial identity F*Fsecond=(1-1/p)*Fprime^2+(1/2)*F*Fprime are derived. Actual self-adjoint shear graph pairings give norm(d)^2=-(2p/h)*Im inner(d,Ju)+(p/2)*Re inner(u,d), u=F*g and Ju=F*Jg-i*h*d. Cauchy-Schwarz yields norm(W*d)<=(2p/abs(h))*norm(W*Ju)+(p/2)*norm(W*u) for every bounded complex clock multiplier W with its actual representative. Clock graph commutation and field representatives are supplied, without a formal unbounded interchange. The theorem applies to every coherent-span input and both field powers, any real continuous linear transverse field, epsilon>0, a>0, h nonzero and abs(h)<=2*pi*epsilon/3, including both signs and the closed boundary. No frequency, coefficient, or finite-basis cutoff is imposed. With D the original clock defect multiplier, the actual real derivative correction satisfies abs(correction)<=A*norm(u)*norm(D^3 Ju)+B*norm(u)*norm(D^3 u), A=40p*abs(h)/epsilon^3 and B=10p*h^2/epsilon^3. Contractivity of D^3 and Young inequality prove, for every eta>0, abs(correction)<=eta*norm(D^3 Ju)^2+(A^2/(4eta)+B)*norm(u)^2. This is an arbitrarily small relative bound with respect to the weighted SHEAR GRAPH quadratic form, not with respect to the original Hamiltonian energy. It does not bound the remaining combined signed matter response by energy, prove positivity of that response, or certify the numerical unit-comparison obstruction. No common Hamiltonian form core, evolution invariance, momentum evolution identity, quantum clock escape, controlled regulator limits, SM/GR identification or octonion necessity is established. No model change is established and the physical TOE remains unproved. All 1489 predecessor source/script hashes are preserved.')


    target = root/'data/field_shear_hardy_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
