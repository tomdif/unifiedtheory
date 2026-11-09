#!/usr/bin/env python3
"""Audit the independent-neutral family and recheck existing evolution scope.

Uses sequential Lean checks in the existing dependency overlay. Preserves
the prior source chain and binds floating evidence without certifying it.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess


NEW_MODULE = 'KFCausalIndependentNeutralTestFamily'
REVIEW_MODULES = [('KFCausalClockFloorAveragedEvolution', 13),
                  ('KFCausalClockFloorAveragedEvolutionProjection', 8)]
STANDARD_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--overlay', type=Path, required=True)
    args = parser.parse_args()
    root, overlay = Path(__file__).resolve().parents[1], args.overlay.resolve()
    assert 'LEAN_PATH' in os.environ and overlay.is_dir()
    env = os.environ.copy()
    env['LEAN_PATH'] = str(overlay)+os.pathsep+env['LEAN_PATH']
    logs = overlay/'independent-neutral-test-audit'
    logs.mkdir(exist_ok=True)
    previous_path = root/'data/projected_initial_vacuum_bound_audit.json'
    previous_hash, previous = sha(previous_path), json.loads(previous_path.read_text())
    additions = ['UnifiedTheory/Audit/'+NEW_MODULE+'.lean',
                 'scripts/independent_neutral_moment_probe.py',
                 'scripts/verify_independent_neutral_moments.py',
                 'scripts/independent_neutral_test_audit.py']
    hashes = {p: sha(root/p) for p in [*previous['source_sha256'], *additions]}
    assert all(hashes[p] == h for p, h in previous['source_sha256'].items())
    evidence = dict(previous['numerical_evidence'])
    for item in evidence.values():
        if isinstance(item, dict) and 'path' in item:
            assert sha(root/item['path']) == item['sha256']
    probe_path = root/'data/independent_neutral_moment_probe.json'
    validation_path = root/'data/independent_neutral_moment_validation.json'
    probe, validation = [json.loads(p.read_text()) for p in [probe_path, validation_path]]
    assert all(sha(root/p) == h for p, h in probe['source_sha256'].items())
    assert validation['probe_report_sha256'] == sha(probe_path)
    assert validation['verifier_sha256'] == sha(root/'scripts/verify_independent_neutral_moments.py')
    assert len(probe['cases']) == 3 and len(validation['checks']) == 6
    for key, path in [('independent_neutral_report', probe_path),
                      ('independent_neutral_validation', validation_path)]:
        evidence[key] = dict(path=str(path.relative_to(root)), sha256=sha(path))
    root_text = (root/'UnifiedTheory.lean').read_text()
    suffix = 'import UnifiedTheory.Audit.'+NEW_MODULE+'\n'
    assert root_text.endswith(suffix)
    assert hashlib.sha256(root_text[:-len(suffix)].encode()).hexdigest() == previous['root_check']['source_sha256']
    root_hash = sha(root/'UnifiedTheory.lean')
    checks = []
    for name, count in [(NEW_MODULE, 15), *REVIEW_MODULES]:
        source = 'UnifiedTheory/Audit/'+name+'.lean'
        source_text = (root/source).read_text()
        assert not re.search(r'\b(sorry|admit|axiom|unsafe)\b', source_text)
        command = ['lean', '-j1', '-o', str(overlay/'UnifiedTheory/Audit'/f'{name}.olean'), source]
        result = subprocess.run(command, cwd=root, env=env, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        log = logs/(name+'.log')
        log.write_text(result.stdout)
        assert result.returncode == 0 and not re.search(r': error|: warning|sorryAx', result.stdout), str(log)
        audits = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", result.stdout)
        expected = {'UnifiedTheory.Audit.'+name+'.'+n for n in
                    re.findall(r'^#print axioms (\S+)', source_text, re.M)}
        assert len(audits) == count and {n for n, _ in audits} == expected
        if name == NEW_MODULE:
            declared = {'UnifiedTheory.Audit.'+name+'.'+n for n in
                        re.findall(r'^theorem (\S+)', source_text, re.M)}
            assert declared == expected
        dependencies = {}
        for declaration, axioms in audits:
            used = {s.strip() for s in axioms.split(',') if s.strip()}
            assert used <= STANDARD_AXIOMS
            dependencies[declaration] = sorted(used)
        checks.append(dict(source=source, command=command, exit_code=0, log_sha256=sha(log),
                           audited_declarations=dependencies))
        print(name, ': clean;', count, 'standard-axiom dependency lists', flush=True)
    result = subprocess.run(['lean', '-j1', 'UnifiedTheory.lean'], cwd=root, env=env,
                            text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    log = logs/'root-import.log'
    log.write_text(result.stdout)
    assert result.returncode == 0 and not result.stdout.strip(), str(log)
    assert sha(root/'UnifiedTheory.lean') == root_hash
    assert sha(previous_path) == previous_hash
    assert all(sha(root/p) == h for p, h in hashes.items())
    for item in evidence.values():
        if isinstance(item, dict) and 'path' in item:
            assert sha(root/item['path']) == item['sha256']
    assert not (root/'.lake/build/lib/lean/UnifiedTheory/Audit'/f'{NEW_MODULE}.olean').exists()
    report = dict(modules=checks[:1], reviewed_evolution_modules=checks[1:],
                  audited_declaration_count=15, reviewed_evolution_declaration_count=21,
                  source_sha256=hashes, numerical_evidence=evidence,
                  previous_report=dict(path=str(previous_path.relative_to(root)), sha256=previous_hash),
                  root_check=dict(command=['lean', '-j1', 'UnifiedTheory.lean'], exit_code=0,
                                  empty_log=True, source_sha256=root_hash, log_sha256=sha(log)),
                  lean_toolchain=(root/'lean-toolchain').read_text().strip(),
                  scope='Fifteen new Lean theorems admit independently variable charged radius A, neutral position B, neutral momentum P, positive clock width a and real clock frequency p. The physical charge-orbit centres, momenta, source, exact positive-real amplitude, field B+A*cos(theta), shear A*P*cos(theta), Packet construction and averaged energy-domain admission are derived. No nonzero-A hypothesis is needed. All 1577 predecessor source/script hashes are preserved. Two existing evolution modules are rechecked: the regulated averaged Hamiltonian already has an all-time strongly continuous unitary propagator, integrated Schrodinger equation on form trajectories and preservation of zero charge. The remaining dynamics obligation is an adequate response bound, form/core extension and response/Ehrenfest identity along that propagator, then clock escape and controlled physical limits. New full-clock numerical moment tests retain all modes and independent charge angles; floating ratios are neither formal counterexamples nor uniform field-energy bounds. No necessary model revision, Standard Model/GR identification, octonion necessity or physical TOE is established.')
    target = root/'data/independent_neutral_test_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print('Root import passed; 15 new and 21 existing dependency audits;', len(hashes), 'source hashes.', flush=True)
    print(target, flush=True)


if __name__ == '__main__':
    main()
