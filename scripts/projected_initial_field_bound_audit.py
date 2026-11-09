#!/usr/bin/env python3
"""Audit actual initial parity and uniform transported-to-initial field bounds.

Run with lake env python3 and the verified overlay. Sequential direct Lean
checks preserve every predecessor hash. Numerical matrices remain floating
exploratory evidence, not a proof of their sign or of a uniform estimate.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess


MODULES = [
    ('KFCausalInitialParityReflection', 4),
    ('KFCausalStructuredInitialParity', 5),
    ('KFCausalParityPolynomialBound', 6),
    ('KFCausalProjectedInitialFieldBound', 7),
]


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
    logs = overlay/'projected-initial-field-bound-audit'
    logs.mkdir(exist_ok=True)
    (overlay/'UnifiedTheory/Audit').mkdir(parents=True, exist_ok=True)
    previous_path = root/'data/projected_matter_cost_density_audit.json'
    previous_hash = sha256(previous_path)
    previous = json.loads(previous_path.read_text())
    sources = list(previous['source_sha256'])
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name, _ in MODULES]
    sources += ['scripts/projected_initial_field_bound_audit.py']
    hashes = {p: sha256(root/p) for p in sources}
    assert all(hashes[p] == h for p, h in previous['source_sha256'].items())
    numeric_path = root/'data/projected_integrated_response_probe.json'
    validation_path = root/'data/projected_integrated_response_validation.json'
    numeric = json.loads(numeric_path.read_text())
    validation = json.loads(validation_path.read_text())
    assert all(sha256(root/p) == h for p,h in numeric['source_sha256'].items())
    assert validation['probe_report_sha256'] == sha256(numeric_path)
    assert validation['verifier_sha256'] == sha256(root/'scripts/verify_projected_integrated_response.py')
    assert len(numeric['cases']) == 5 and len(validation['checks']) == 10
    numerical_evidence = dict(report=dict(path=str(numeric_path.relative_to(root)), sha256=sha256(numeric_path)),
        validation=dict(path=str(validation_path.relative_to(root)), sha256=sha256(validation_path)),
        interpretation='Floating finite-subspace tests only; no certified sign, tail, uniform lower bound or evolution claim.')
    cost_path = root/'data/projected_matter_cost_probe.json'
    cost_validation_path = root/'data/projected_matter_cost_validation.json'
    cost = json.loads(cost_path.read_text())
    cost_validation = json.loads(cost_validation_path.read_text())
    assert all(sha256(root/p) == h for p,h in cost['source_sha256'].items())
    assert cost_validation['probe_report_sha256'] == sha256(cost_path)
    assert cost_validation['verifier_sha256'] == sha256(root/'scripts/verify_projected_matter_cost.py')
    assert len(cost['cases']) == 5 and len(cost_validation['checks']) == 10
    numerical_evidence['cost_report'] = dict(path=str(cost_path.relative_to(root)), sha256=sha256(cost_path))
    numerical_evidence['cost_validation'] = dict(path=str(cost_validation_path.relative_to(root)), sha256=sha256(cost_validation_path))
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
    assert sha256(numeric_path) == numerical_evidence['report']['sha256']
    assert sha256(validation_path) == numerical_evidence['validation']['sha256']
    assert sha256(cost_path) == numerical_evidence['cost_report']['sha256']
    assert sha256(cost_validation_path) == numerical_evidence['cost_validation']['sha256']
    report = dict(
        numerical_evidence=numerical_evidence, modules=checks, root_check=dict(command=['lean', '-j1', 'UnifiedTheory.lean'], exit_code=0,
            empty_log=True, source_sha256=root_hash, log_sha256=sha256(log)),
        audited_declaration_count=sum(n for _, n in MODULES), source_sha256=hashes,
        previous_report=dict(path=str(previous_path.relative_to(root)), sha256=previous_hash),
        lean_toolchain=(root/'lean-toolchain').read_text().strip(),
        scope='Twenty-two public theorem dependency lists prove a measure-preserving reflection of the four charged physical coordinates; source/amplitude half-turn identities for the actual displaced packets; reflection invariance of the full structured initial mean, derived by commuting the bounded unitary with its periodic Bochner average; paired second/fourth polynomial inequalities; and uniform transported-to-ordinary initial field norm bounds. For p=1,2, K=3*exp(pi/6)+2, G0 the actual initial mean, H_p=P_Delta^p*G0 and V_p=Phi^p*G0, the proved bounds are norm(H_p)^2 <= K^(2*p)*norm(V_p)^2 and norm(M H_p)^2 <= K^(2*p)*norm(M V_p)^2. The ordinary initial field representatives and their unweighted and clock-secant-weighted integrable densities are derived through the actual closed multiplier graphs. The generic nonnegative clock-weight bound states its integrability hypotheses explicitly; both norm specializations discharge them. All finite complex superpositions, independent positive clock widths, zero clock centres, arbitrary remaining allowed displacements/frequencies and epsilon>0, h!=0, abs(h)<=2*pi*epsilon/3 are retained. K is uniform inside that strip, not a justification for removing epsilon at fixed nonzero h. The new bound compares two initial quantities; it does not control initial moments or final slope moments by the final Hamiltonian energy. The sharp signed full-response bound remains available and may be stronger. Uniform energy control, form/core extension, physical evolution, clock escape, controlled limits, SM/GR identification, octonion necessity, necessary model revision and a physical TOE remain unproved. All1568 predecessor source/script hashes and both prior numerical report/validation pairs are preserved.')


    target = root/'data/projected_initial_field_bound_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed;', report['audited_declaration_count'],
          'audited declarations;', len(hashes), 'verified source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
