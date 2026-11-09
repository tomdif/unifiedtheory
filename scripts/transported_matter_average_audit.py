#!/usr/bin/env python3
"""Audit charge averaging and the full transported matter response bound.

Run with the repository toolchain and verified dependency overlay:
  lake env python3 scripts/transported_matter_average_audit.py --overlay PATH

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


MODULES = [('KFCausalTransportedInitialAssembly', 5), ('KFCausalTransportedChargeInitial', 6), ('KFCausalTransportedMatterResponse', 1), ('KFCausalTransportedFullResponse', 1)]


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
    logs = overlay/'transported-matter-average-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/transported_matter_interpolation_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/transported_matter_average_audit.py']
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
        scope='The transported initial field is exactly a finite combination of the existing polynomial field paths at auxiliary time zero, acted on by fixed bounded clock transports of degrees zero, one half and one. The mixed quadratic component is retained by polarization. The same assembly identity holds for the actual shear outputs by graph linearity and uniqueness. The identities extend intrinsically to the algebraic coherent span using the established coherent basis, with no coefficient-norm estimate. Existing joint continuity of the original field and shear paths therefore gives continuity along charge rotations for the new initial input and shear. Their signed quadratic pairing is continuous and charge-integrable for any bounded clock multiplier. Integrating the actual transported endpoint inequality gives mean(finalPairing) >= mean(transportedInitialPairing), with no auxiliary path cost. All complex interference terms remain. Combining this result with the existing actual longitudinal absorption gives each actual matter rate >= (4/epsilon squared)*mean(transportedInitialPairing) - betaAbs*mean(H(d_terminal)), where betaAbs=800*exp(4*pi/3)*hbar^4/epsilon^5 and H(d)=integral D^5*(1-D)*norm(d)^2. Terminal derivative curves and their moment integrability are derived with their exact representatives. The final theorem constructs the actual pure-clock momentum, form lifts of the state and its momentum, all eight factor outputs, and terminal derivative curves. With nonnegative mass squared, quartic and vacuum coefficients, the full averaged energy-form response is bounded below by exp(2t) times the mass/quartic weighted sum of the two matter lower bounds, minus norm(f)^2/2. The full response is also identified with the actual eight-factor rate. No additional sign, force, moment or energy premise is introduced. Conditions remain epsilon>0, a>0, nonzero hbar, abs(hbar)<=2*pi*epsilon/3 and the existing coherent widths, including either sign of hbar and the strip boundary. The new initial pairing differs from the earlier untransported pairing and remains signed. This closes its charge-integrability and averaging gap, and connects the bound to the actual full form response. It does not establish sufficient one-sided Hamiltonian-energy control of the combined initial pairing and terminal correction, boundedness or closability of the algebraic field recipes, a common Hamiltonian form core, evolution invariance, a momentum evolution identity, long-time quantum clock recovery, controlled regulator limits, physical Standard Model/GR identification or octonion necessity. The energy remains explicitly time dependent and is not assumed conserved. No model change is established; the physical TOE remains unproved. All 1473 predecessor source/script hashes are preserved.')


    target = root/'data/transported_matter_average_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
