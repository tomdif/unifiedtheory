#!/usr/bin/env python3
"""Audit actual shear/vacuum compositions and the natural weighted domain.

Run with the repository toolchain and verified dependency overlay:
  lake env python3 scripts/coherent_shear_compositions_audit.py --overlay PATH

Sequential direct Lean checks rebuild nine new modules, audit their axioms,
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


MODULES = [('KFCausalShearCutoffDifferential', 13), ('KFCausalShearMaximalDifferential', 9), ('KFCausalClockFloorRelativeShift', 6), ('KFCausalShearPolynomialMoments', 3), ('KFCausalRelativeGaussianDifferential', 4), ('KFCausalRelativeGaussianShearDomain', 5), ('KFCausalShiftedGaussianPhysicalProfile', 7), ('KFCausalShiftedGaussianShearDomain', 5), ('KFCausalCoherentShearCompositions', 9)]


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
    logs = overlay/'coherent-shear-compositions-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/coherent_shear_energy_domain_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/coherent_shear_compositions_audit.py']
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
        scope='Scaled compact cutoffs derive the actual shear graph for every C1 physical function with itself and its shear differential in L2, without a clock-derivative L2 assumption. The complex inverse-clock difference is bounded by abs(y)/epsilon, so the relative complex transverse scale is C1 and uniformly bounded. Physical linear and mixed coordinate moments follow from pure quadratic moments. The exact shear differential of a clock-dependent relative Gaussian profile is quadratic in physical coordinates, including the half-density term; bounded scale and quadratic moments give its L2 estimate and actual shear graph. The profile is identified with the existing complex-shifted Gaussian state; all required moments are derived from the preceding Gaussian estimates. Every existing coherent energy state has both JT and TJ graphs with the same explicit shifted shear output, and the result holds for every physical charge rotation. The actual exponential outputs belong to the natural weighted domain requiring Wg in Dom(J). The finite coherent span is contained in all these composition domains and the common eight-factor energy domain; the all-angle common set is Hilbert-dense. Conditions are positive clock floor and clock width, nonzero hbar, and abs(hbar)<=2*pi*epsilon/3. Generic Gaussian graphs use positive alpha and beta, 32*beta<=alpha, and abs(y)<=pi*epsilon/3. This supplies actual composition membership, not a common Hamiltonian graph core or evolution-domain invariance. Shear-output angle continuity and integrability, the charge-integrated signed force estimate, and its control along actual time-dependent Hamiltonian evolution remain open. No weighted-force bound, quantum clock-error recovery, regulator removal, octonion necessity or physical TOE identification is derived. The classical affine upper-bound obstruction remains valid and does not rule out a one-sided lower bound. No Hamiltonian change is established. All 1336 predecessor source/script hashes are preserved; the TOE remains unproved.')


    target = root/'data/coherent_shear_compositions_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
