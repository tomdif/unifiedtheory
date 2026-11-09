#!/usr/bin/env python3
"""Independent direct integration of a saved polynomial growth candidate.

The integral evaluator is the frozen independent quadrature implementation;
neither growth producer, moment recurrence, nor clock jet is imported.
Two sufficient orders at 180 digits check one fixed complex state. Search
residuals are diagnostic, not certificates of a global maximum. This is
decimal verification, not interval certification or a Lean theorem.
"""
import argparse
import json
from pathlib import Path
import time
import mpmath as mp
from verify_correlated_polynomial_response import digest, unpack, energy_function

PARENT = 'data/correlated_polynomial_response_probe.json'
PARENT_SHA = '9de058e5d6ccf4f28e4f61df41f83958a4654c52a5371c4498fd2d4624e8956b'
VERIFICATION = 'data/correlated_polynomial_response_verification.json'
VERIFICATION_SHA = '5ba7bdc44d4b78ab341f9487f603c55df7769c0039189563fa9a7ac3dd436619'


def verify_state(witness):
    p, v = witness['parameters'], witness['result']
    K, D, c = [unpack(witness[k]) for k in ['gram', 'derivative', 'coefficients']]
    size = p['dimension']
    assert K.rows == K.cols == D.rows == D.cols == c.rows == size and c.cols == 1
    assert max(mp.norm(K-K.H)/mp.norm(K), mp.norm(D-D.H)/mp.norm(D)) < mp.mpf('1e-110')
    E, R = (c.H*K*c)[0], (c.H*D*c)[0]
    assert mp.re(E) > 0 and max(abs(mp.im(E)), abs(mp.im(R))) < mp.mpf('1e-100')
    E, R = mp.re(E), mp.re(R)/mp.re(E)
    assert abs(E-1) < mp.mpf('1e-130')
    assert abs(R-mp.mpf(v['rayleigh_slope'])) < mp.mpf('1e-130')
    residual = mp.norm(D*c-R*K*c)/((mp.norm(D)+abs(R)*mp.norm(K))*mp.norm(c))
    assert residual < mp.mpf('1e-12')
    assert abs(residual-mp.mpf(v['eigen_residual'])) < mp.mpf('1e-130')
    s = mp.mpf(p['s'])
    checks, results = [], []
    for extra in [0, 1]:
        started = time.monotonic()
        energy, orders = energy_function(witness, extra)
        print('Integrating saved state', orders, flush=True)
        observed_E = energy(s)
        observed_R = mp.diff(energy, s)/observed_E
        energy_error, slope_error = abs(observed_E-E)/observed_E, abs(observed_R-R)
        assert observed_E > 0 and max(energy_error, slope_error) < mp.mpf('1e-95')
        checks.append(dict(orders=orders, energy=mp.nstr(observed_E, 140), slope=mp.nstr(observed_R, 140),
                           energy_relative_error=mp.nstr(energy_error, 16),
                           slope_absolute_error=mp.nstr(slope_error, 16)))
        results.append((observed_E, observed_R))
        print(orders, 'slope', mp.nstr(observed_R, 35),
              'seconds', round(time.monotonic()-started, 2), flush=True)
    order_error = max(abs(results[0][0]-results[1][0])/results[0][0], abs(results[0][1]-results[1][1]))
    assert order_error < mp.mpf('1e-140')
    norm_slope = mp.mpf(p['epsilon'])/(mp.exp(s)+mp.mpf(p['epsilon']))*results[0][1]
    return dict(parameters=p, quadrature=checks, normalized_slope=mp.nstr(norm_slope, 140),
                quadrature_order_difference=mp.nstr(order_error, 16),
                saved_matrix_eigen_residual=mp.nstr(residual, 16))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--report', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    assert not args.output.exists(), 'Use a new output path; frozen reports must not be replaced.'
    report_hash = digest(args.report)
    report = json.loads(args.report.read_text())
    assert report['parent_report'] == dict(path=PARENT, sha256=PARENT_SHA)
    assert report['parent_verification'] == dict(path=VERIFICATION, sha256=VERIFICATION_SHA)
    assert digest(root/PARENT) == PARENT_SHA and digest(root/VERIFICATION) == VERIFICATION_SHA
    parent = json.loads((root/PARENT).read_text())
    assert report['formal_parent'] == parent['parent_report']
    formal = report['formal_parent']
    assert digest(root/formal['path']) == formal['sha256']
    expected_evidence = {v['path']: v['sha256'] for v in
                         json.loads((root/formal['path']).read_text())['numerical_evidence'].values()
                         if isinstance(v, dict) and 'path' in v and 'sha256' in v}
    expected_evidence.update({PARENT: PARENT_SHA, VERIFICATION: VERIFICATION_SHA})
    assert report['preserved_numerical_evidence'] == expected_evidence
    assert all(digest(root/p) == h for p, h in expected_evidence.items())
    sources = report['source_sha256']
    assert len(sources) == 2566 and all(sources[p] == h for p, h in parent['source_sha256'].items())
    assert set(sources)-set(parent['source_sha256']) == {
        'scripts/correlated_polynomial_growth_probe.py', 'scripts/verify_correlated_polynomial_growth.py'}
    assert all(digest(root/p) == h for p, h in sources.items())
    assert digest(root/'UnifiedTheory.lean') == report['root_sha256'] == parent['root_sha256']
    assert report['moment_precision_digits'] == report['rayleigh_precision_digits'] == 160
    assert report['rank_truncation'] is False and report['certified_maxima'] is False
    assert report['neutral_sources_zero'] is True and report['basis'] == parent['basis']
    assert report['test_count'] == len(report['records']) == 8 and report['rejected_cases'] == 0
    assert [(r['parameters']['charged_degree'], r['parameters']['neutral_degree']) for r in report['records']] == [
        (16, 8), (20, 8), (24, 8), (32, 8), (8, 12), (16, 12), (8, 16), (16, 16)]
    mp.mp.dps = 180
    for record in report['records']:
        p, v = record['parameters'], record['result']
        assert mp.mpf(p['epsilon']) == mp.mpf(p['h']) == 100
        assert mp.mpf(p['alpha']) == mp.mpf('0.005') and mp.mpf(p['beta']) == mp.mpf('0.00015625')
        assert p['clock_offset'] == '1' and abs(mp.mpf(p['s'])-mp.log(100)-1) < mp.mpf('1e-150')
        assert p['dimension'] == (p['charged_degree']+1)*(p['neutral_degree']+1)
        assert 0 < v['search_gram_min'] <= v['search_gram_max'] and 1 <= v['search_condition'] < 1e8
        assert abs(v['search_condition']-v['search_gram_max']/v['search_gram_min']) < 1e-8
        assert abs(mp.mpf(v['energy'])-1) < mp.mpf('1e-130')
        assert 0 <= mp.mpf(v['hermitian_error']) < mp.mpf('1e-110')
        for key in ['search_hermitian_error', 'search_eigen_residual', 'eigen_residual']:
            assert 0 <= mp.mpf(v[key]) < mp.mpf('1e-12')
        error = abs(mp.mpf(v['rayleigh_slope'])-mp.mpf(v['search_max_slope']))
        assert error < mp.mpf('1e-9') and abs(error-mp.mpf(v['search_rayleigh_difference'])) < mp.mpf('1e-140')
        assert abs(mp.mpf(v['normalized_rayleigh_slope'])-mp.mpf(v['rayleigh_slope'])/(mp.e+1)) < mp.mpf('1e-150')
    baseline = report['baseline_comparison']
    old_max = parent['witnesses']['largest_observed']['result']['max_slope']
    assert baseline['charged_degree'] == 16 and baseline['neutral_degree'] == 8
    assert baseline['previous_high_precision_max'] == old_max
    delta = abs(mp.mpf(report['records'][0]['result']['rayleigh_slope'])-mp.mpf(old_max))
    assert delta < mp.mpf('1e-10') and abs(delta-mp.mpf(baseline['candidate_absolute_difference'])) < mp.mpf('1e-140')
    assert set(report['witnesses']) == {'largest_observed'}
    witness = report['witnesses']['largest_observed']
    assert dict(parameters=witness['parameters'], result=witness['result']) in report['records']
    assert mp.mpf(witness['result']['rayleigh_slope']) == max(mp.mpf(r['result']['rayleigh_slope']) for r in report['records'])
    result = verify_state(witness)
    assert all(digest(root/p) == h for p, h in sources.items())
    assert all(digest(root/p) == h for p, h in expected_evidence.items())
    assert digest(args.report) == report_hash and digest(root/'UnifiedTheory.lean') == report['root_sha256']
    output = dict(scope=__doc__, report_sha256=report_hash, parent_report=report['parent_report'],
                  parent_verification=report['parent_verification'], formal_parent=formal,
                  preserved_numerical_evidence=expected_evidence,
                  root_sha256=report['root_sha256'], source_sha256=sources,
                  verifier_sha256=digest(Path(__file__)), precision=180, test_count=8,
                  independently_integrated_witness_count=1, candidate=result,
                  rank_truncation=False, certified_maxima=False, passed=True)
    args.output.write_text(json.dumps(output, indent=2, allow_nan=False)+'\n')
    print('Independent polynomial growth candidate verification passed.', flush=True)


if __name__ == '__main__':
    main()
