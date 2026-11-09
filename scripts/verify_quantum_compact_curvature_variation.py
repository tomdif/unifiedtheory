#!/usr/bin/env python3
"""Independently verify actual compact curvature variations and frozen evidence."""
import argparse
import hashlib
import json
from pathlib import Path
import re

EXPECTED = {'KFCausalClockFloorGrowingProjection': 7, 'KFCausalGrowingCoreProjectedCoherent': 4, 'KFCausalBDG4DCompactTensorFactors': 12, 'KFCausalBDG4DCompactSymmetricTensor': 9, 'KFCausalBDG4DQuadraticEulerProfiles': 18, 'KFCausalMinkowski4DEulerQuadrant': 6, 'KFCausalMinkowski4DVariationCone': 2, 'KFCausalConformal4DRegularVolume': 5, 'KFCausalBDG4DQuadraticVariationLimit': 4, 'KFCausalBDG4DTemporalCurvatureLimit': 7, 'KFCausalConformal4DRegularVolumeSmoothness': 8, 'KFCausalConformal4DCompactKernelDerivative': 6, 'KFCausalBDG4DActualTemporalVariation': 6}
NAMESPACES = {}
FACTOR_THEOREMS = {'first_smooth', 'second_smooth', 'value_derivative', 'first_derivative',
                   'compact', 'outside_support', 'exists_bound', 'uniform_bound'}


def declaration_name(module, theorem):
    inner = 'Factor.' if module == 'KFCausalBDG4DCompactTensorFactors' and theorem in FACTOR_THEOREMS else ''
    return 'UnifiedTheory.Audit.' + NAMESPACES.get(module, module) + '.' + inner + theorem



def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--overlay', required=True, type=Path)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    overlay = args.overlay.resolve()
    report = json.loads((root/'data/quantum_compact_curvature_variation_audit.json').read_text())
    expected_parent = dict(path='data/quantum_common_domains_lorentzian_variation_audit.json',
                           sha256='b1bf0a99c7f02b808f5b83415a934f3df0b3a7f6fe6d454c4b601e26edb349fe')
    assert report['previous_report'] == expected_parent
    assert sha(root/expected_parent['path']) == expected_parent['sha256']
    parent = json.loads((root/expected_parent['path']).read_text())
    assert len(parent['source_sha256']) == 3139 and len(report['source_sha256']) == 3154
    assert all(report['source_sha256'][p] == h for p, h in parent['source_sha256'].items())
    assert all(sha(root/p) == h for p, h in report['source_sha256'].items())
    additions = {f'UnifiedTheory/Audit/{n}.lean' for n in EXPECTED} | {
        'scripts/quantum_compact_curvature_variation_audit.py',
        'scripts/verify_quantum_compact_curvature_variation.py'}
    assert set(report['source_sha256'])-set(parent['source_sha256']) == additions
    assert len(report['modules']) == len(EXPECTED)
    assert [Path(item['source']).stem for item in report['modules']] == list(EXPECTED)
    logs = overlay/'quantum-compact-curvature-variation-audit'
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
        assert not re.search(r': error|: warning|sorryAx|PANIC', log)
        parsed = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", log)
        audits = {n: sorted(x.strip() for x in xs.split(',') if x.strip()) for n, xs in parsed}
        declarations = {declaration_name(name,n) for n in re.findall(r'^theorem (\S+)', source, re.M)}
        commands = {'UnifiedTheory.Audit.'+NAMESPACES.get(name,name)+'.'+n for n in re.findall(r'^#print axioms (\S+)', source, re.M)}
        assert len(parsed) == len(audits) == EXPECTED[name]
        assert set(audits) == declarations == commands
        assert audits == item['audited_declarations']
        assert all(set(xs) <= {'propext', 'Classical.choice', 'Quot.sound'} for xs in audits.values())
        assert not (root/'.lake/build/lib/lean/UnifiedTheory/Audit'/(name+'.olean')).exists()
        assert (overlay/'UnifiedTheory/Audit'/(name+'.olean')).is_file()
        assert not (overlay/'UnifiedTheory/Audit'/(name+'.olean')).is_symlink()
        count += len(audits)
    assert count == report['new_lean_theorem_count'] == 94
    root_source = (root/'UnifiedTheory.lean').read_text()
    suffix = ''.join('import UnifiedTheory.Audit.'+name+'\n' for name in EXPECTED)
    assert root_source.endswith(suffix) and len(root_source.splitlines()) == 8794
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
    assert report['analytic_frontier'] == {'path': 'data/quantum_whole_response_mellin_frontier_20261021.txt', 'sha256': 'f9e28fb65eb823d0ec5f9d8b44b4984e50580e05bd679e4d7a7b688742ca7390', 'status': 'Analytic research only; not Lean verified. Exact linked full-response formulation and scoped strategy obstructions; unrestricted response bound and admissible counterexample remain open.'}
    assert sha(root/report['analytic_frontier']['path']) == report['analytic_frontier']['sha256']
    assert report['analytic_frontier'] == parent['analytic_frontier']
    assert report['analytic_charged_pairing'] == {'path': 'data/quantum_charged_mellin_pairing_20261021.txt', 'sha256': 'b6b472c6af208ccdd67214c196016de5439e98457a014e5380b5182063755d8a', 'status': 'Analytic proof only; not Lean verified. Charged-density coercivity and a full linked polarized-pair bound retain n=0 without a separate negative-index norm. Conversion to the full quartic charged form and the unrestricted physical response bound remain open.'}
    assert sha(root/report['analytic_charged_pairing']['path']) == report['analytic_charged_pairing']['sha256']
    assert report['analytic_charged_pairing'] == parent['analytic_charged_pairing']
    assert report['analytic_matrix_curvature'] == {'path': 'data/quantum_whole_response_matrix_curvature_20261021.txt', 'sha256': 'f6f4119d5f5736dd4a679addad5c548e1c8c6d372e277d56d6f4baa2ad4fbafd', 'status': 'Independently reviewed analytic identities, not Lean verified. Exact positive full-quartic Gram and connection decomposition retains all linked neutral derivatives. The required combined clock matrix inequality remains open.'}
    assert sha(root/report['analytic_matrix_curvature']['path']) == report['analytic_matrix_curvature']['sha256']
    assert report['analytic_width_floor_obstruction'] == {'path': 'data/quantum_width_floor_cooling_obstruction_20261021.txt', 'sha256': 'cdf4e33e91731885c718d4dee77b8fef418334dc29627e6fc7875c4ce11be459', 'status': 'Independently reviewed analytic obstruction, not Lean verified. Actual finite real-width families disprove the stronger uniform v-squared cooling comparison. The actual zero-shift clock response cancels exactly; this is not a counterexample to the full response bound.'}
    assert sha(root/report['analytic_width_floor_obstruction']['path']) == report['analytic_width_floor_obstruction']['sha256']
    assert report['numerical_evidence'] == parent['numerical_evidence']
    evidence = [v for v in report['numerical_evidence'].values() if isinstance(v, dict) and 'path' in v]
    assert len(evidence) == 23
    assert all(sha(root/v['path']) == v['sha256'] for v in evidence)
    assert report['lean_toolchain'] == (root/'lean-toolchain').read_text().strip()
    print('Verified: 94 Lean theorems, 3154 source hashes, exact 13-import root extension,')
    print('all 23 numerical files preserved, standard axioms only, no new .lake artifacts.')


if __name__ == '__main__':
    main()
