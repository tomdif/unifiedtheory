#!/usr/bin/env python3
"""Independent checks of signed response matrices and prior moment witnesses.

Uses direct generalized eigenvalues and Cholesky scaling without importing
the probe. Does not certify integration error, tails or infinite-space signs.
"""
import hashlib
import json
from pathlib import Path
import numpy as np
from scipy.linalg import cholesky, eigh, solve_triangular


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def matrix(raw):
    return np.array(raw['real'])+1j*np.array(raw['imag'])


def quotient(A, E, w):
    return float(np.vdot(w, A@w).real/np.vdot(w, E@w).real)


def main():
    root = Path(__file__).resolve().parents[1]
    path = root/'data/independent_neutral_response_probe.json'
    report = json.loads(path.read_text())
    assert all(sha(root/p) == h for p, h in report['source_sha256'].items())
    prior_path = root/report['prior_moment_report']['path']
    assert sha(prior_path) == report['prior_moment_report']['sha256']
    prior = json.loads(prior_path.read_text())
    assert all(sha(root/p) == h for p, h in prior['source_sha256'].items())
    assert [c['name'] for c in report['cases']] == [
        'neutral_grid_9', 'neutral_grid_16', 'independent_neutral_adverse_9']
    records = []
    for case in report['cases']:
        n, eps = len(case['packets']), case['eps']
        assert eps > 0 and 0 < abs(case['h']) <= 2*np.pi*eps/3
        assert np.isfinite(case['packets']).all()
        assert all(p[0] >= 0 and p[3] > 0 for p in case['packets'])
        assert len(case['runs']) == 2
        first, first_witness, prior_witnesses, field_ratios = None, None, {}, {}
        if 'prior_moment_case' in case:
            pc = next(c for c in prior['cases'] if c['name'] == case['prior_moment_case'])
            assert pc['packets'] == case['packets'] and pc['h'] == case['h'] and pc['eps'] == eps
            pr = pc['runs'][-1]
            prior_witnesses = {p: np.array(v['witness_real'])+1j*np.array(v['witness_imag'])
                               for p, v in pr['spectra'].items()}
            field_ratios = {p: quotient(matrix(pr['matrices']['initial'+p]),
                                         matrix(pr['matrices']['final'+p]), w)
                            for p, w in prior_witnesses.items()}
            assert field_ratios['1'] > 1 and field_ratios['2'] > 1
        for run in case['runs']:
            forms = {name: matrix(raw) for name, raw in run['matrices'].items()}
            assert set(forms) == {'energy', 'ordered', 'remainder', 'norm',
                                  'ordered_direct', 'remainder_direct', 'response'}
            assert all(M.shape == (n, n) and np.isfinite(M).all() for M in forms.values())
            assert all(np.linalg.norm(M-M.conj().T) <= 2e-10*max(1., np.linalg.norm(M))
                       for M in forms.values())
            E = forms['energy']
            W = solve_triangular(cholesky(E, lower=True).conj().T, np.eye(n), lower=False)
            assert np.linalg.norm(W.conj().T@E@W-np.eye(n), 2) < 2e-8
            assert np.allclose(forms['response'], forms['ordered']+forms['remainder'], rtol=2e-12, atol=2e-12)
            condition = run['spectrum']['conditioning']
            assert condition['rank_truncated'] is False and condition['dimension'] == n
            assert condition['whitening_residual'] < 2e-8
            maximum_spectral_error = 0.
            for name in ['ordered', 'response', 'remainder', 'norm']:
                values = eigh(forms[name], E, eigvals_only=True)
                saved = run['spectrum'][name]
                error = max(abs(values[0]-saved['minimum']), abs(values[-1]-saved['maximum']))
                assert error < 2e-8
                maximum_spectral_error = max(maximum_spectral_error, float(error))
                w = np.array(saved['witness_real'])+1j*np.array(saved['witness_imag'])
                assert abs(np.vdot(w, E@w)-1) < 2e-8
                assert abs(quotient(forms[name], E, w)-values[0]) < 2e-8
                residual = np.linalg.norm(forms[name]@w-values[0]*(E@w))/max(
                    1., np.linalg.norm(forms[name]@w), abs(values[0])*np.linalg.norm(E@w))
                assert residual < 2e-8
                diagonal = float(np.min(np.diag(forms[name]).real/np.diag(E).real))
                assert abs(diagonal-saved['diagonal_minimum']) < 2e-8
                if name == 'remainder':
                    assert max(abs(values)) <= 1/(4*eps)+2e-8
                if name == 'norm':
                    assert values[0] >= -2e-10
            if first is None:
                first = forms
                s = run['spectrum']['response']
                first_witness = np.array(s['witness_real'])+1j*np.array(s['witness_imag'])
                assert run['energy_scaled_matrix_changes'] == {}
            else:
                changes = {name: float(np.linalg.norm(W.conj().T@(M-first[name])@W, 2)/
                                       max(1., np.linalg.norm(W.conj().T@M@W, 2)))
                           for name, M in forms.items()}
                assert max(changes.values()) < 2e-8
                assert max(abs(v-run['energy_scaled_matrix_changes'][k]) for k, v in changes.items()) < 2e-9
            assert abs(quotient(forms['response'], E, first_witness)-run['original_witness_quotient']) < 2e-8
            prior_records = {}
            for p, w in prior_witnesses.items():
                saved = run['prior_moment_witness_responses'][p]
                actual = quotient(forms['response'], E, w)
                assert abs(actual-saved['response_over_energy']) < 2e-8
                assert abs(quotient(forms['ordered'], E, w)-saved['ordered_over_energy']) < 2e-8
                prior_records[p] = dict(initial_final_field_ratio=field_ratios[p], response_over_energy=actual)
            assert max(run['checks']['integration_by_parts_errors'].values()) < 2e-8
            assert run['checks']['projected_gram_oracle_error'] < 5e-10
            records.append(dict(case=case['name'], dimension=n, quadrature=run['quadrature'],
                                maximum_spectral_error=maximum_spectral_error,
                                prior_moment_witnesses=prior_records))
    checks = report['checks']
    assert len(checks['independent_direct_references']) == 2
    assert {v['h'] for v in checks['independent_direct_references']} == {.3, -.3}
    assert max(e for c in checks['independent_direct_references'] for e in c['errors'].values()) < 2e-8
    finite = checks['finite_interval_boundary']
    assert finite['error_if_omitted'] > .01
    assert max(finite['checks']['integration_by_parts_errors'].values()) < 2e-8
    target = root/'data/independent_neutral_response_validation.json'
    result = dict(probe_report_sha256=sha(path), verifier_sha256=sha(Path(__file__)), checks=records,
                  scope='Independent floating spectra, complex witnesses, prior field-moment witnesses, static bound, refinements and provenance. No certified sign, integration error or uniform energy estimate.')
    target.write_text(json.dumps(result, indent=2, allow_nan=False)+'\n')
    print('Independent response verification passed for six complete-space runs and all prior moment witnesses.')
    print(target)


if __name__ == '__main__':
    main()
