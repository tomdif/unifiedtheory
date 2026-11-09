#!/usr/bin/env python3
"""Recheck stored full projected matrices without importing the probe.

Uses direct generalized eigensolvers and Cholesky-scaled refinement checks.
This verifies numerical consistency, not clock tails or mathematical signs.
"""
import hashlib
import json
from pathlib import Path

import numpy as np
from scipy.linalg import cholesky, eigh, solve_triangular


def main():
    root = Path(__file__).resolve().parents[1]
    path = root/'data/projected_integrated_response_probe.json'
    report = json.loads(path.read_text())
    sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
    assert all(sha(root/p) == digest for p, digest in report['source_sha256'].items())
    expected = ['transverse_superposition', 'clock_frequency_superposition',
                'mixed_width_frequency_superposition', 'negative_clock_span_33',
                'negative_transverse_clock_span_9']
    assert [case['name'] for case in report['cases']] == expected
    records = []
    for case in report['cases']:
        n = len(case['packets'])
        eps = case.get('eps', report['default_parameters']['eps'])
        first, W = None, None
        assert len(case['runs']) == 2
        for run in case['runs']:
            forms = {name: np.array(raw['real'])+1j*np.array(raw['imag']) for name, raw in run['matrices'].items()}
            assert all(M.shape == (n, n) and np.isfinite(M).all() for M in forms.values())
            assert all(np.linalg.norm(M-M.conj().T) <= 2e-10*max(1., np.linalg.norm(M)) for M in forms.values())
            E = forms['energy']
            assert np.allclose(forms['response'], forms['ordered']+forms['remainder'], rtol=2e-12, atol=2e-12)
            values, vectors = eigh(forms['response'], E)
            recorded = run['spectrum']['response']
            assert abs(values[0]-recorded['minimum']) < 2e-8
            assert abs(values[-1]-recorded['maximum']) < 2e-8
            witness = np.array(recorded['witness_real'])+1j*np.array(recorded['witness_imag'])
            energy = np.vdot(witness, E@witness)
            quotient = np.vdot(witness, forms['response']@witness)/energy
            assert abs(energy-1) < 2e-8 and abs(quotient-values[0]) < 2e-8
            for name in ['ordered', 'norm', 'remainder']:
                spectrum = eigh(forms[name], E, eigvals_only=True)
                assert abs(spectrum[0]-run['spectrum'][name]['minimum']) < 2e-8
                assert abs(spectrum[-1]-run['spectrum'][name]['maximum']) < 2e-8
            remainder = eigh(forms['remainder'], E, eigvals_only=True)
            assert np.max(abs(remainder)) <= 1/(4*eps)+2e-8
            assert eigh(forms['norm'], E, eigvals_only=True)[0] >= -2e-10
            if first is None:
                first = forms
                L = cholesky(E, lower=True)
                W = solve_triangular(L.conj().T, np.eye(n), lower=False)
            assert np.linalg.norm(W.conj().T@first['energy']@W-np.eye(n), 2) < 2e-8
            changes = {name: float(np.linalg.norm(W.conj().T@(M-first[name])@W, 2)/
                                   max(1., np.linalg.norm(W.conj().T@M@W, 2))) for name, M in forms.items()}
            assert max(changes.values()) < 2e-8, (case['name'], changes)
            real_minimum = float(eigh(forms['response'].real, E.real, eigvals_only=True)[0])
            assert real_minimum >= values[0]-2e-8
            records.append(dict(case=case['name'], dimension=n, quadrature=run['quadrature'],
                                minimum=float(values[0]), real_coefficient_minimum=real_minimum,
                                energy_scaled_matrix_changes=changes))
    checks = report['checks']
    assert max(checks['mixed_absolute_angle_matrix_errors'].values()) < 2e-8
    assert checks['finite_interval_check']['error_if_boundary_omitted'] > .01
    assert max(checks['finite_interval_check']['checks']['integration_by_parts_errors'].values()) < 2e-8
    result = dict(scope='Independent consistency checks of stored floating-point matrices; no certified sign or uniform bound.',
                  probe_report_sha256=sha(path), verifier_sha256=sha(Path(__file__).resolve()),
                  checks=records)
    target = root/'data/projected_integrated_response_validation.json'
    target.write_text(json.dumps(result, indent=2, allow_nan=False)+'\n')
    print('Verified source hashes, five complete subspaces, ten generalized spectra, complex witnesses,')
    print('static bounds, positive norms, and Cholesky-scaled matrix refinement without mode truncation.')
    print(target)


if __name__ == '__main__':
    main()
