#!/usr/bin/env python3
"""Independently verify momentum potential domains, physical response pairings and clock compositions."""
import argparse
import hashlib
import json
from pathlib import Path
import re

EXPECTED = {'KFCausalReciprocalNeutralFieldSliceNorm': 4, 'KFCausalCorrelatedClusteredFieldTransfer': 4, 'KFCausalShiftedMomentumClockAmplitude': 6, 'KFCausalCorrelatedClusteredMomentumPotentialProfiles': 3, 'KFCausalCorrelatedClusteredMomentumPotentialLimit': 13, 'KFCausalCorrelatedClusteredPhysicalResponsePairing': 6, 'KFCausalHalfMomentumClockAmplitude': 6, 'KFCausalCorrelatedClusteredHalfMomentumLimit': 11, 'KFCausalCorrelatedClusteredClockCompositionLimit': 10}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--overlay', required=True, type=Path)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    overlay = args.overlay.resolve()
    report = json.loads((root/'data/quantum_correlated_clustered_momentum_response_audit.json').read_text())
    expected_parent = dict(path='data/quantum_correlated_clustered_clock_domains_audit.json',
                           sha256='693868216831f131ec4d8726a48ed378b17e22dfa9217bb92b6a0034fa879ab0')
    assert report['previous_report'] == expected_parent
    assert sha(root/expected_parent['path']) == expected_parent['sha256']
    parent = json.loads((root/expected_parent['path']).read_text())
    assert len(parent['source_sha256']) == 2599 and len(report['source_sha256']) == 2610
    assert all(report['source_sha256'][p] == h for p, h in parent['source_sha256'].items())
    assert all(sha(root/p) == h for p, h in report['source_sha256'].items())
    additions = {f'UnifiedTheory/Audit/{n}.lean' for n in EXPECTED} | {
        'scripts/quantum_correlated_clustered_momentum_response_audit.py',
        'scripts/verify_quantum_correlated_clustered_momentum_response.py'}
    assert set(report['source_sha256'])-set(parent['source_sha256']) == additions
    assert len(report['modules']) == len(EXPECTED)
    assert [Path(item['source']).stem for item in report['modules']] == list(EXPECTED)
    logs = overlay/'quantum-correlated-clustered-momentum-response-audit'
    count = 0
    for item in report['modules']:
        name = Path(item['source']).stem
        source = (root/item['source']).read_text()
        assert not re.search(r'\b(sorry|admit|axiom|unsafe)\b', source)
        assert item['command'] == ['lean', '-j1', '-o', str(overlay/'UnifiedTheory/Audit'/(name+'.olean')), item['source']]
        log_path = logs/(name+'.log')
        assert item['exit_code'] == 0 and item['log_sha256'] == sha(log_path)
        log = log_path.read_text()
        assert not re.search(r': error|: warning|sorryAx', log)
        parsed = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", log)
        audits = {n: sorted(x.strip() for x in xs.split(',') if x.strip()) for n, xs in parsed}
        declarations = {'UnifiedTheory.Audit.'+name+'.'+n for n in re.findall(r'^theorem (\S+)', source, re.M)}
        commands = {'UnifiedTheory.Audit.'+name+'.'+n for n in re.findall(r'^#print axioms (\S+)', source, re.M)}
        assert len(parsed) == len(audits) == EXPECTED[name]
        assert set(audits) == declarations == commands
        assert audits == item['audited_declarations']
        assert all(set(xs) <= {'propext', 'Classical.choice', 'Quot.sound'} for xs in audits.values())
        assert not (root/'.lake/build/lib/lean/UnifiedTheory/Audit'/(name+'.olean')).exists()
        count += len(audits)
    assert count == report['new_lean_theorem_count'] == 63
    root_source = (root/'UnifiedTheory.lean').read_text()
    suffix = ''.join('import UnifiedTheory.Audit.'+name+'\n' for name in EXPECTED)
    assert root_source.endswith(suffix) and len(root_source.splitlines()) == 8330
    assert hashlib.sha256(root_source[:-len(suffix)].encode()).hexdigest() == parent['root_check']['source_sha256']
    assert sha(root/'UnifiedTheory.lean') == report['root_check']['source_sha256']
    assert report['root_check']['appended_imports'] == list(EXPECTED)
    assert report['root_check']['command'] == ['lean', '-j1', 'UnifiedTheory.lean']
    assert report['root_check']['exit_code'] == 0 and report['root_check']['empty_log']
    assert sha(logs/'root-import.log') == report['root_check']['log_sha256']
    assert not (logs/'root-import.log').read_text().strip()
    assert report['numerical_evidence'] == parent['numerical_evidence']
    evidence = [v for v in report['numerical_evidence'].values() if isinstance(v, dict) and 'path' in v]
    assert len(evidence) == 23
    assert all(sha(root/v['path']) == v['sha256'] for v in evidence)
    assert report['lean_toolchain'] == (root/'lean-toolchain').read_text().strip()
    print('Verified: 63 Lean theorems, 2610 source hashes, exact nine-import root extension,')
    print('all 23 numerical files preserved, standard axioms only, no new .lake artifacts.')


if __name__ == '__main__':
    main()
