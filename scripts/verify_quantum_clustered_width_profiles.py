#!/usr/bin/env python3
"""Independently check the clustered-width Lean and numerical checkpoint."""
import argparse
import hashlib
import json
from pathlib import Path
import re


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--overlay', required=True, type=Path)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    report = json.loads((root/'data/quantum_clustered_width_profiles_audit.json').read_text())
    expected_parent = dict(path='data/quantum_joint_angular_clock_obstruction_audit.json',
                           sha256='b980893bfaf538b30cc5c8896e71099f5ccd5d63fa6a27504749c5a863aff0c3')
    assert report['previous_report'] == expected_parent
    assert sha(root/expected_parent['path']) == expected_parent['sha256']
    parent = json.loads((root/expected_parent['path']).read_text())
    assert len(parent['source_sha256']) == 2530 and len(report['source_sha256']) == 2535
    assert all(report['source_sha256'][p] == h for p, h in parent['source_sha256'].items())
    assert all(sha(root/p) == h for p, h in report['source_sha256'].items())
    name = 'KFCausalClusteredWidthProfiles'
    source_path = 'UnifiedTheory/Audit/'+name+'.lean'
    source = (root/source_path).read_text()
    assert not re.search(r'\b(sorry|admit|axiom|unsafe)\b', source)
    assert len(report['modules']) == 1 and report['modules'][0]['source'] == source_path
    item = report['modules'][0]
    logs = args.overlay/'quantum-clustered-width-profiles-audit'
    log_path = logs/(name+'.log')
    assert item['exit_code'] == 0 and item['log_sha256'] == sha(log_path)
    log = log_path.read_text()
    assert not re.search(r': error|: warning|sorryAx', log)
    parsed = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", log)
    audits = {n:sorted(x.strip() for x in xs.split(',') if x.strip()) for n, xs in parsed}
    declarations = {'UnifiedTheory.Audit.'+name+'.'+n for n in re.findall(r'^theorem (\S+)', source, re.M)}
    commands = {'UnifiedTheory.Audit.'+name+'.'+n for n in re.findall(r'^#print axioms (\S+)', source, re.M)}
    assert len(parsed) == len(audits) == report['new_lean_theorem_count'] == 12
    assert set(audits) == declarations == commands
    assert audits == item['audited_declarations']
    assert all(set(xs) <= {'propext', 'Classical.choice', 'Quot.sound'} for xs in audits.values())
    assert not (root/'.lake/build/lib/lean/UnifiedTheory/Audit'/(name+'.olean')).exists()
    root_source = (root/'UnifiedTheory.lean').read_text()
    suffix = 'import UnifiedTheory.Audit.'+name+'\n'
    assert root_source.endswith(suffix) and len(root_source.splitlines()) == 8277
    assert hashlib.sha256(root_source[:-len(suffix)].encode()).hexdigest() == parent['root_check']['source_sha256']
    assert sha(root/'UnifiedTheory.lean') == report['root_check']['source_sha256']
    assert report['root_check']['appended_imports'] == [name]
    assert report['root_check']['exit_code'] == 0 and report['root_check']['empty_log']
    assert sha(logs/'root-import.log') == report['root_check']['log_sha256']
    assert not (logs/'root-import.log').read_text().strip()
    expected_keys = set(parent['numerical_evidence']) | {'joint_neutral_clustered_scan', 'joint_neutral_clustered_verification'}
    evidence = report['numerical_evidence']
    assert set(evidence) == expected_keys
    assert all(evidence[k] == v for k, v in parent['numerical_evidence'].items())
    for v in evidence.values():
        if isinstance(v, dict) and 'path' in v:
            assert sha(root/v['path']) == v['sha256']
    scan = json.loads((root/evidence['joint_neutral_clustered_scan']['path']).read_text())
    checked = json.loads((root/evidence['joint_neutral_clustered_verification']['path']).read_text())
    assert scan['parent_report'] == checked['parent_report'] == expected_parent
    assert scan['root_sha256'] == checked['root_sha256'] == parent['root_check']['source_sha256']
    assert scan['test_count'] == checked['test_count'] == 44
    assert len(scan['records']) == 44 and len(scan['witnesses']) == 2
    assert checked['passed'] and checked['independently_integrated_witness_count'] == 2
    assert scan['precision'] == 120 and checked['mpmath_precision'] == 160
    assert scan['rank_truncation'] is False and checked['rank_truncation'] is False
    assert scan['rejected_cases'] == checked['rejected_cases'] == 0
    assert checked['report_sha256'] == evidence['joint_neutral_clustered_scan']['sha256']
    assert checked['verifier_sha256'] == sha(root/'scripts/verify_joint_neutral_clustered_response.py')
    assert checked['source_sha256'] == scan['source_sha256']
    assert all(sha(root/p) == h for p, h in scan['source_sha256'].items())
    assert report['lean_toolchain'] == (root/'lean-toolchain').read_text().strip()
    print('Verified: 12 Lean theorems, 2535 source hashes, exact one-import root extension,')
    print('44 finite matrix records and two independent 160-digit integral witnesses; all parent evidence preserved.')


if __name__ == '__main__':
    main()
