#!/usr/bin/env python3
"""Independently verify physical Q L Q insertions, original finite states and exact audit preservation."""
import argparse
import hashlib
import json
from pathlib import Path
import re

EXPECTED = {'KFCausalSymmetricInsertionCoordinate': 3, 'KFCausalSourcedWidthSymmetricInsertion': 4, 'KFCausalSourcedWidthSymmetricMultiplier': 5, 'KFCausalSourcedWidthSymmetricRegularity': 4, 'KFCausalSourcedWidthSymmetricSquare': 6, 'KFCausalSourcedWidthSymmetricContinuity': 7, 'KFCausalSourcedWidthSymmetricProjected': 4, 'KFCausalFiniteSourcedSymmetricSquare': 8, 'KFCausalPointFieldInsertionCoordinate': 3, 'KFCausalSourcedWidthPointFieldInsertion': 5, 'KFCausalSourcedWidthPointFieldMultiplier': 5, 'KFCausalSourcedWidthPointFieldRegularity': 4, 'KFCausalSourcedWidthPointFieldSquare': 6, 'KFCausalSourcedWidthPointFieldContinuity': 7, 'KFCausalSourcedWidthPointFieldProjected': 4, 'KFCausalFiniteSourcedPointFieldSquare': 8, 'KFCausalChargeConjugatedInsertion': 4, 'KFCausalFiniteSourcedTwoAngleInsertion': 4, 'KFCausalScalarPowerSourceAbsorption': 2}
NAMESPACES = {'KFCausalSourcedWidthSymmetricRegularity': 'KFCausalSourcedWidthSymmetricMultiplier', 'KFCausalSourcedWidthPointFieldRegularity': 'KFCausalSourcedWidthPointFieldMultiplier'}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--overlay', required=True, type=Path)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    overlay = args.overlay.resolve()
    report = json.loads((root/'data/quantum_physical_field_insertion_audit.json').read_text())
    expected_parent = dict(path='data/quantum_two_width_physical_response_audit.json',
                           sha256='6e7948d956e9f2e14361320f4b9671f326a7a8679b432b3bb70ac87549782d9b')
    assert report['previous_report'] == expected_parent
    assert sha(root/expected_parent['path']) == expected_parent['sha256']
    parent = json.loads((root/expected_parent['path']).read_text())
    assert len(parent['source_sha256']) == 2941 and len(report['source_sha256']) == 2962
    assert all(report['source_sha256'][p] == h for p, h in parent['source_sha256'].items())
    assert all(sha(root/p) == h for p, h in report['source_sha256'].items())
    additions = {f'UnifiedTheory/Audit/{n}.lean' for n in EXPECTED} | {
        'scripts/quantum_physical_field_insertion_audit.py',
        'scripts/verify_quantum_physical_field_insertion.py'}
    assert set(report['source_sha256'])-set(parent['source_sha256']) == additions
    assert len(report['modules']) == len(EXPECTED)
    assert [Path(item['source']).stem for item in report['modules']] == list(EXPECTED)
    logs = overlay/'quantum-physical-field-insertion-audit'
    count = 0
    for item in report['modules']:
        name = Path(item['source']).stem
        source = (root/item['source']).read_text()
        # English in the opening module comment is not executable Lean.
        source_body = re.sub(r'\A/-.*?-/', '', source, count=1, flags=re.S)
        assert not re.search(r'\b(sorry|admit|axiom|unsafe)\b', source_body)
        assert item['command'] == ['lean', '-j1', '-o', str(overlay/'UnifiedTheory/Audit'/(name+'.olean')), item['source']]
        log_path = logs/(name+'.log')
        assert item['exit_code'] == 0 and item['log_sha256'] == sha(log_path)
        log = log_path.read_text()
        assert not re.search(r': error|: warning|sorryAx', log)
        parsed = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", log)
        audits = {n: sorted(x.strip() for x in xs.split(',') if x.strip()) for n, xs in parsed}
        declarations = {'UnifiedTheory.Audit.'+NAMESPACES.get(name,name)+'.'+n for n in re.findall(r'^theorem (\S+)', source, re.M)}
        commands = {'UnifiedTheory.Audit.'+NAMESPACES.get(name,name)+'.'+n for n in re.findall(r'^#print axioms (\S+)', source, re.M)}
        assert len(parsed) == len(audits) == EXPECTED[name]
        assert set(audits) == declarations == commands
        assert audits == item['audited_declarations']
        assert all(set(xs) <= {'propext', 'Classical.choice', 'Quot.sound'} for xs in audits.values())
        assert not (root/'.lake/build/lib/lean/UnifiedTheory/Audit'/(name+'.olean')).exists()
        count += len(audits)
    assert count == report['new_lean_theorem_count'] == 93
    root_source = (root/'UnifiedTheory.lean').read_text()
    suffix = ''.join('import UnifiedTheory.Audit.'+name+'\n' for name in EXPECTED)
    assert root_source.endswith(suffix) and len(root_source.splitlines()) == 8624
    assert hashlib.sha256(root_source[:-len(suffix)].encode()).hexdigest() == parent['root_check']['source_sha256']
    assert sha(root/'UnifiedTheory.lean') == report['root_check']['source_sha256']
    assert report['root_check']['appended_imports'] == list(EXPECTED)
    assert report['root_check']['command'] == ['lean', '-j1', 'UnifiedTheory.lean']
    assert report['root_check']['exit_code'] == 0 and report['root_check']['empty_log']
    assert sha(logs/'root-import.log') == report['root_check']['log_sha256']
    assert not (logs/'root-import.log').read_text().strip()
    assert report['analytic_evidence'] == parent['analytic_evidence']
    assert report['analytic_evidence'] == dict(
        path='data/quantum_fixed_v_charged_cooling_analytic.txt',
        sha256='38bb567709bcba710996d3b1d8302facb8df7cb7063723189bb642040c99225d',
        status='Analytic derivation; not a Lean-verified theorem; moving field estimate remains open')
    assert sha(root/report['analytic_evidence']['path']) == report['analytic_evidence']['sha256']
    assert report['analytic_obstruction'] == parent['analytic_obstruction']
    assert report['analytic_obstruction'] == dict(
        path='data/quantum_quartic_imaginary_contraction_obstruction.txt',
        sha256='c2b84b9d756700d949ebc9687144f4812bf8cf151d0fa7715c9f1491ea4556df',
        status='Exact analytic counterexample to pure quartic imaginary contraction; not Lean verified; not a counterexample to the uniform response bound')
    assert sha(root/report['analytic_obstruction']['path']) == report['analytic_obstruction']['sha256']
    assert report['numerical_evidence'] == parent['numerical_evidence']
    evidence = [v for v in report['numerical_evidence'].values() if isinstance(v, dict) and 'path' in v]
    assert len(evidence) == 23
    assert all(sha(root/v['path']) == v['sha256'] for v in evidence)
    assert report['lean_toolchain'] == (root/'lean-toolchain').read_text().strip()
    print('Verified: 93 Lean theorems, 2962 source hashes, exact 19-import root extension,')
    print('all 23 numerical files preserved, standard axioms only, no new .lake artifacts.')


if __name__ == '__main__':
    main()
