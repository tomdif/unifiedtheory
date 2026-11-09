#!/usr/bin/env python3
"""Independently check saved initial/final moment matrices and witnesses.

This verifies floating spectra and provenance, not quadrature error bounds.
"""
import hashlib
import json
from pathlib import Path
import numpy as np
from scipy.linalg import cholesky, eigh, solve_triangular


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def unpack(record):
    return np.array(record['real'])+1j*np.array(record['imag'])


def whitener(M):
    return solve_triangular(cholesky(M, lower=True).conj().T, np.eye(len(M)), lower=False)


def main():
    root = Path(__file__).resolve().parents[1]
    path = root/'data/projected_initial_moment_probe.json'
    report = json.loads(path.read_text())
    assert all(sha(root/p) == h for p, h in report['source_sha256'].items())
    assert len(report['checks']) == 9 and len(report['cases']) == 3
    assert max(e for c in report['checks'] for e in c['errors'].values()) < 2e-9
    checks = []
    for case in report['cases']:
        assert case['eps'] > 0 and 0 < abs(case['h']) <= 2*np.pi*case['eps']/3
        first = None
        first_witnesses = None
        for run in case['runs']:
            matrices = {key: unpack(value) for key, value in run['matrices'].items()}
            for M in matrices.values():
                assert M.shape == (len(case['packets']), len(case['packets']))
                assert np.isfinite(M).all()
                assert np.linalg.norm(M-M.conj().T) < 1e-11*max(1., np.linalg.norm(M))
                assert eigh(M, eigvals_only=True)[0] > 0
            EW = whitener(matrices['energy'])
            maximum_error = 0.
            for p in range(3):
                I, F = matrices[f'initial{p}'], matrices[f'final{p}']
                W = whitener(F)
                H = W.conj().T@I@W
                ev = eigh((H+H.conj().T)/2, eigvals_only=True)
                direct = eigh(I, F, eigvals_only=True)
                saved = run['spectra'][str(p)]
                assert saved['conditioning']['rank_truncated'] is False
                assert saved['conditioning']['dimension'] == len(F)
                error = max(abs(ev[0]-saved['minimum']), abs(ev[-1]-saved['maximum']), np.max(abs(ev-direct)))
                assert error < 2e-9
                maximum_error = max(maximum_error, float(error))
                w = np.array(saved['witness_real'])+1j*np.array(saved['witness_imag'])
                denominator = np.vdot(w, F@w).real
                assert abs(denominator-1) < 2e-8
                ratio = np.vdot(w, I@w).real/denominator
                assert abs(ratio-ev[-1]) < 2e-9
                residual = np.linalg.norm(I@w-ev[-1]*F@w)/max(1., np.linalg.norm(I@w), abs(ev[-1])*np.linalg.norm(F@w))
                assert residual < 2e-8
                if p == 0:
                    assert ev[-1] <= 1+2e-8
            if first is None:
                first = matrices
                first_witnesses = {p: np.array(v['witness_real'])+1j*np.array(v['witness_imag'])
                                   for p, v in run['spectra'].items()}
                assert run['refinement_energy_scaled_changes'] == {}
            else:
                for name, M in matrices.items():
                    change = np.linalg.norm(EW.conj().T@(M-first[name])@EW, 2)/max(1., np.linalg.norm(EW.conj().T@M@EW, 2))
                    assert change < 2e-7
                    assert abs(change-run['refinement_energy_scaled_changes'][name]) < 2e-9
            for p, w in first_witnesses.items():
                ratio = np.vdot(w, matrices['initial'+p]@w).real/np.vdot(w, matrices['final'+p]@w).real
                assert abs(ratio-run['first_witness_ratios'][p]) < 2e-9
            checks.append(dict(case=case['name'], quadrature=run['quadrature'], maximum_spectral_error=maximum_error))
    result = dict(probe_report_sha256=sha(path), verifier_sha256=sha(Path(__file__)), checks=checks,
                  limitations='Checks floating matrices, full-space spectra, witnesses, refinements and source hashes. No certified quadrature error, tails, field-energy inequality, model refutation or physical TOE.')
    target = root/'data/projected_initial_moment_validation.json'
    target.write_text(json.dumps(result, indent=2)+'\n')
    print('Independent Cholesky/generalized-eigenvalue verification passed for six complete finite-space runs.')
    print(target)


if __name__ == '__main__':
    main()
