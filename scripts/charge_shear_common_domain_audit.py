#!/usr/bin/env python3
"""Audit the constructed common shear domain and noncompact differential criterion.

Run with the repository toolchain and verified dependency overlay:
  lake env python3 scripts/charge_shear_common_domain_audit.py --overlay PATH

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


MODULES = [('KFCausalDominatedL2Derivative', 2), ('KFCausalCompactFlowSlopeBound', 6), ('KFCausalChargeShearSmoothFlow', 5), ('KFCausalChargeShearCompactDomain', 7), ('KFCausalChargeShearCompactDensity', 5), ('KFCausalTransverseShearDifferentialDomain', 5)]


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
    logs = overlay/'charge-shear-common-domain-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/charge_shear_quarter_cancellation_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/charge_shear_common_domain_audit.py']
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
        scope='A dominated L2 differentiation theorem and compact flow-tube estimates derive strong Hilbert derivatives from pointwise derivatives and an integrable bound. Applied to the actual physical shear in charge coordinates, they construct its actual momentum graph on every compactly supported C1 test function. Every physical charge rotation remains in this test family, so all rotated shear graph memberships and the four-quarter-turn cancellation are derived without assumed graph memberships. This test family is dense in the physical Hilbert space. The intersection of the shear domains over every charge angle is dense and contains a norm-one state, for nonzero hbar. This is Hilbert density, not graph-core density or membership in the Hamiltonian energy domain. A separate noncompact criterion proves the actual physical shear graph for a C1 physical function when the function, its canonical clock derivative and its shear differential belong to L2. Its output is minus i times hbar times the shear differential; the inverse shear-coordinate clock derivative identity derives the necessary domain membership. Gaussian differential integrability applications remain open in this milestone. The existing coherent Gaussian family already has actual energy-factor graph memberships, but these new compact tests are not claimed to have exponential-factor domains. No full-period Bochner shear average, weighted-force lower bound, charge-integrated Hamiltonian force law, quantum zero-clock-defect limit, regulator removal, octonion necessity or physical TOE identification is derived. The classical affine upper-bound obstruction remains valid. No Hamiltonian change is established. All 1324 predecessor source/script hashes are preserved; the TOE remains unproved.')


    target = root/'data/charge_shear_common_domain_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
