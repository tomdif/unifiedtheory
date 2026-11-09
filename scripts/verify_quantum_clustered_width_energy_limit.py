#!/usr/bin/env python3
"""Independently verify the clustered-width energy-limit checkpoint."""
import argparse
import hashlib
import json
from pathlib import Path
import re

EXPECTED = {'KFCausalJointPolynomialIntegrability': 6,
            'KFCausalClusteredWidthDensityIntegrability': 9,
            'KFCausalClusteredWidthEnergyLimit': 7,
            'KFCausalClusteredWidthChargedJet': 7}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--overlay', required=True, type=Path)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    report = json.loads((root/'data/quantum_clustered_width_energy_limit_audit.json').read_text())
    expected_parent = dict(path='data/quantum_clustered_width_profiles_audit.json',
                           sha256='18f12694f072edfdc4e1a132dacc950ee1fca26a60fddc2e9d469123b6918b79')
    assert report['previous_report'] == expected_parent
    assert sha(root/expected_parent['path']) == expected_parent['sha256']
    parent = json.loads((root/expected_parent['path']).read_text())
    assert len(parent['source_sha256']) == 2535 and len(report['source_sha256']) == 2541
    assert all(report['source_sha256'][p] == h for p, h in parent['source_sha256'].items())
    assert all(sha(root/p) == h for p, h in report['source_sha256'].items())
    assert len(report['modules']) == len(EXPECTED)
    assert [Path(item['source']).stem for item in report['modules']] == list(EXPECTED)
    logs = args.overlay/'quantum-clustered-width-energy-limit-audit'
    count = 0
    for item in report['modules']:
        name = Path(item['source']).stem
        source = (root/item['source']).read_text()
        assert not re.search(r'\b(sorry|admit|axiom|unsafe)\b', source)
        log_path = logs/(name+'.log')
        assert item['exit_code'] == 0 and item['log_sha256'] == sha(log_path)
        log = log_path.read_text()
        assert not re.search(r': error|: warning|sorryAx', log)
        parsed = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", log)
        audits = {n:sorted(x.strip() for x in xs.split(',') if x.strip()) for n, xs in parsed}
        declarations = {'UnifiedTheory.Audit.'+name+'.'+n for n in re.findall(r'^theorem (\S+)', source, re.M)}
        commands = {'UnifiedTheory.Audit.'+name+'.'+n for n in re.findall(r'^#print axioms (\S+)', source, re.M)}
        assert len(parsed) == len(audits) == EXPECTED[name]
        assert set(audits) == declarations == commands
        assert audits == item['audited_declarations']
        assert all(set(xs) <= {'propext', 'Classical.choice', 'Quot.sound'} for xs in audits.values())
        assert not (root/'.lake/build/lib/lean/UnifiedTheory/Audit'/(name+'.olean')).exists()
        count += len(audits)
    assert count == report['new_lean_theorem_count'] == 29
    root_source = (root/'UnifiedTheory.lean').read_text()
    suffix = ''.join('import UnifiedTheory.Audit.'+name+'\n' for name in EXPECTED)
    assert root_source.endswith(suffix) and len(root_source.splitlines()) == 8281
    assert hashlib.sha256(root_source[:-len(suffix)].encode()).hexdigest() == parent['root_check']['source_sha256']
    assert sha(root/'UnifiedTheory.lean') == report['root_check']['source_sha256']
    assert report['root_check']['appended_imports'] == list(EXPECTED)
    assert report['root_check']['exit_code'] == 0 and report['root_check']['empty_log']
    assert sha(logs/'root-import.log') == report['root_check']['log_sha256']
    assert not (logs/'root-import.log').read_text().strip()
    evidence = report['numerical_evidence']
    assert evidence == parent['numerical_evidence']
    for v in evidence.values():
        if isinstance(v, dict) and 'path' in v:
            assert sha(root/v['path']) == v['sha256']
    scan = json.loads((root/evidence['joint_neutral_clustered_scan']['path']).read_text())
    checked = json.loads((root/evidence['joint_neutral_clustered_verification']['path']).read_text())
    assert checked['passed'] and checked['test_count'] == scan['test_count'] == 44
    assert checked['independently_integrated_witness_count'] == 2
    assert checked['report_sha256'] == evidence['joint_neutral_clustered_scan']['sha256']
    assert checked['source_sha256'] == scan['source_sha256']
    assert all(sha(root/p) == h for p, h in scan['source_sha256'].items())
    assert checked['verifier_sha256'] == sha(root/'scripts/verify_joint_neutral_clustered_response.py')
    assert report['lean_toolchain'] == (root/'lean-toolchain').read_text().strip()
    print('Verified: 29 Lean theorems, 2541 source hashes, exact four-import root extension,')
    print('all parent numerical evidence preserved, standard axioms only, no new .lake artifacts.')


if __name__ == '__main__':
    main()
