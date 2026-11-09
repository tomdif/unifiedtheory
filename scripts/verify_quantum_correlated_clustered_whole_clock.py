#!/usr/bin/env python3
"""Independently verify the correlated clustered full-clock checkpoint."""
import argparse
import hashlib
import json
from pathlib import Path
import re

EXPECTED = {'KFCausalCorrelatedClusteredGlobalEnvelope': 4, 'KFCausalCorrelatedClusteredClockBounds': 3, 'KFCausalCorrelatedClusteredClockContinuity': 8, 'KFCausalCorrelatedClusteredWholeClock': 10, 'KFCausalCorrelatedClusteredReducedClock': 7, 'KFCausalCorrelatedClusteredPhysicalClockLimit': 11}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--overlay', required=True, type=Path)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    report = json.loads((root/'data/quantum_correlated_clustered_whole_clock_audit.json').read_text())
    expected_parent = dict(path='data/quantum_correlated_clustered_response_limit_audit.json',
                           sha256='f83d4c044b1381e4a0c0231f1e252f5d7a735a16363fa8226991e075b1a176d7')
    assert report['previous_report'] == expected_parent
    assert sha(root/expected_parent['path']) == expected_parent['sha256']
    parent = json.loads((root/expected_parent['path']).read_text())
    assert len(parent['source_sha256']) == 2562 and len(report['source_sha256']) == 2574
    assert all(report['source_sha256'][p] == h for p, h in parent['source_sha256'].items())
    assert all(sha(root/p) == h for p, h in report['source_sha256'].items())
    assert len(report['modules']) == len(EXPECTED)
    assert [Path(item['source']).stem for item in report['modules']] == list(EXPECTED)
    logs = args.overlay/'quantum-correlated-clustered-whole-clock-audit'
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
    assert count == report['new_lean_theorem_count'] == 43
    root_source = (root/'UnifiedTheory.lean').read_text()
    suffix = ''.join('import UnifiedTheory.Audit.'+name+'\n' for name in EXPECTED)
    assert root_source.endswith(suffix) and len(root_source.splitlines()) == 8302
    assert hashlib.sha256(root_source[:-len(suffix)].encode()).hexdigest() == parent['root_check']['source_sha256']
    assert sha(root/'UnifiedTheory.lean') == report['root_check']['source_sha256']
    assert report['root_check']['appended_imports'] == list(EXPECTED)
    assert report['root_check']['exit_code'] == 0 and report['root_check']['empty_log']
    assert sha(logs/'root-import.log') == report['root_check']['log_sha256']
    assert not (logs/'root-import.log').read_text().strip()
    evidence = report['numerical_evidence']
    expected_evidence = dict(parent['numerical_evidence'])
    expected_evidence.update({'correlated_polynomial_scan': {'path': 'data/correlated_polynomial_response_probe.json', 'sha256': '9de058e5d6ccf4f28e4f61df41f83958a4654c52a5371c4498fd2d4624e8956b'}, 'correlated_polynomial_verification': {'path': 'data/correlated_polynomial_response_verification.json', 'sha256': '5ba7bdc44d4b78ab341f9487f603c55df7769c0039189563fa9a7ac3dd436619'}, 'correlated_polynomial_growth_scan': {'path': 'data/correlated_polynomial_growth_probe.json', 'sha256': '804e88c584989dd552cbbdc79f1526aed6445ef452399ddd5a8b79f9ad551709'}, 'correlated_polynomial_growth_verification': {'path': 'data/correlated_polynomial_growth_verification.json', 'sha256': 'e4533090914679905b5b09f23df9480151e9de7c2469313b641d713988b3563a'}})
    assert evidence == expected_evidence
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
    for scan_key, check_key, tests, witnesses in [
        ('correlated_polynomial_scan', 'correlated_polynomial_verification', 24, 2),
        ('correlated_polynomial_growth_scan', 'correlated_polynomial_growth_verification', 8, 1)]:
        new_scan = json.loads((root/evidence[scan_key]['path']).read_text())
        new_check = json.loads((root/evidence[check_key]['path']).read_text())
        assert new_check['passed'] and new_scan['test_count'] == new_check['test_count'] == tests
        assert new_check['independently_integrated_witness_count'] == witnesses
        assert new_check['report_sha256'] == evidence[scan_key]['sha256']
        assert new_check['source_sha256'] == new_scan['source_sha256']
        assert all(report['source_sha256'][p] == h for p, h in new_scan['source_sha256'].items())
        assert new_scan['root_sha256'] == parent['root_check']['source_sha256']
    assert len(new_scan['source_sha256']) == 2566
    additions = {f'UnifiedTheory/Audit/{n}.lean' for n in EXPECTED} | {
        'scripts/quantum_correlated_clustered_whole_clock_audit.py',
        'scripts/verify_quantum_correlated_clustered_whole_clock.py'}
    assert set(report['source_sha256'])-set(new_scan['source_sha256']) == additions
    assert report['lean_toolchain'] == (root/'lean-toolchain').read_text().strip()
    print('Verified: 43 Lean theorems, 2574 source hashes, exact six-import root extension,')
    print('all 23 numerical files preserved, standard axioms only, no new .lake artifacts.')


if __name__ == '__main__':
    main()
