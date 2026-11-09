#!/usr/bin/env python3
"""Check the neutral Hermite probe and provide a separate Gaussian quadrature.

The reference evaluates Hermite polynomials at a two-dimensional Gaussian
quadrature. It does not use the probe's joint-moment or derivative recurrence.
It shares the inverse-clock helper and the coherent packet convention.
"""
import argparse
import hashlib
import json
from pathlib import Path
import numpy as np
from numpy.polynomial.hermite import hermgauss
from scipy.linalg import eigh
from matter_energy_gram_probe import inverse_shift


def reference(A, B, P, h, s, N, nt=48, order=None):
    """Absolute-angle grids and direct polynomial Gaussian integration."""
    if order is None:
        order = N + 4
    theta = 2*np.pi*np.arange(nt)/nt
    th = np.repeat(theta, nt)
    ph = np.tile(theta, nt)
    w = np.array([1., 1., 1., 1., 1/32])/(2*abs(h))
    def source(a):
        b = np.zeros((len(a), 5), complex)
        b[:, 2] = w[2]*A*np.cos(a)+1j*A*np.sin(a)/(2*h)
        b[:, 3] = w[3]*A*np.cos(a)-1j*A*np.sin(a)/(2*h)
        b[:, 4] = 2*w[4]*B+1j*P/h
        logamp = -w[2]*A*A*np.cos(a)**2/2-w[4]*B*B
        return b, logamp
    b, lb = source(th)
    c, lc = source(ph)
    z = inverse_shift(s, 1., h)
    r = np.exp((z-s)/2)
    L = np.eye(5, dtype=complex)*r
    L[4, 4] = 1
    L[4, 2:4] = 2*(r-1)
    H = 2*(L.T@np.diag(w)@L).real
    V = .5*np.linalg.inv(H)
    lin = (b@L).conj()+c@L
    mu = lin@V
    base = 2.5*np.log(np.pi)-.5*np.linalg.slogdet(np.diag(2*w))[1]
    weight = np.exp(2.5*np.log(np.pi)-.5*np.linalg.slogdet(H)[1]
                    +.5*np.sum(lin*mu, axis=-1)+lb+lc-base)/(nt*nt)
    # Only x2+x3 and x4 enter either Hermite polynomial or the field.
    D = np.array([[0., 0., 1., 1., 0.], [0., 0., 0., 0., 1.]])
    means = mu@D.T
    covariance = D@V@D.T
    nodes, weights = hermgauss(order)
    mesh = np.stack(np.meshgrid(nodes, nodes, indexing='ij'), axis=-1).reshape(-1, 2)
    offsets = np.sqrt(2)*mesh@np.linalg.cholesky(covariance).T
    gw = np.outer(weights, weights).ravel()/np.pi
    T = np.zeros((N+1, N+1), complex)
    for lo in range(0, len(mu), 128):
        sl = slice(lo, lo+128)
        x = means[sl, None, :]+offsets[None, :, :]
        X = np.sqrt(2*w[4])*(x[:, :, 1]+2*(r.conjugate()-1)*x[:, :, 0]-B)
        Y = np.sqrt(2*w[4])*(x[:, :, 1]+2*(r-1)*x[:, :, 0]-B)
        field = x[:, :, 0]+x[:, :, 1]
        def hermite(arg):
            values = np.empty((N+1,)+arg.shape, complex)
            values[0] = 1
            if N:
                values[1] = np.sqrt(2)*arg
            for n in range(1, N):
                values[n+1] = np.sqrt(2/(n+1))*arg*values[n]-np.sqrt(n/(n+1))*values[n-1]
            return values
        left, right = hermite(X), hermite(Y)
        factor = weight[sl, None]*gw[None, :]*(1+field**2/2+field**4/4)
        T += np.einsum('nak,mak,ak->nm', left, right, factor)
    return T


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def matrix(record):
    return np.array(record['real'])+1j*np.array(record['imag'])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--report', type=Path, default=Path('data/neutral_hermite_response_probe.json'))
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    report = json.loads(args.report.read_text())
    parent = report['formal_checkpoint']
    assert parent['path'] == 'data/quantum_charge_conservation_audit.json'
    assert parent['sha256'] == '92d8a58152c531a2ef9c797d482650717bb8a448e3b1f76d4c1b8050e72174b0'
    assert sha(root/parent['path']) == parent['sha256']
    previous = json.loads((root/parent['path']).read_text())
    assert len(previous['source_sha256']) == 2039
    assert all(sha(root/p) == h for p, h in previous['source_sha256'].items())
    assert sha(root/'UnifiedTheory.lean') == previous['root_check']['source_sha256']
    assert all(sha(root/p) == h for p, h in report['source_sha256'].items())
    assert report['epsilon'] == 1.
    assert report['couplings'] == dict(mass2=1., quartic=1., vacuum=1.)
    assert [(c['A'], c['B'], c['P'], c['h'], c['clock_coordinate']) for c in report['cases']] == [
        (10., 8., -.4, .05, 0.), (10., 8., -.4, .05, 1.), (20., 16., -.4, .05, 1.)]
    for c in report['cases']:
        assert [(r['nt'], r['nd']) for r in c['runs']] == [(64,512), (96,768)]
        first = None
        for run in c['runs']:
            T, R = [matrix(run['matrices'][name]) for name in ['drift_density', 'response_density']]
            assert T.shape == R.shape == (65, 65)
            for M in [T, R]:
                assert np.isfinite(M).all()
                assert np.linalg.norm(M-M.conj().T)/max(1., np.linalg.norm(M)) < 2e-10
            last = np.inf
            assert [r['degree'] for r in run['spectra']] == [0,8,16,24,32,48,64]
            for row in run['spectra']:
                n = row['degree']+1
                a, b = T[:n, :n], R[:n, :n]
                # Direct generalized eigensolver, without the producer's whitening.
                ev = eigh(b, a, eigvals_only=True)
                v = np.array(row['witness_real'])+1j*np.array(row['witness_imag'])
                den = np.vdot(v, a@v).real
                num = np.vdot(v, b@v).real
                assert den > 0 and abs(den-1) < 2e-8
                assert abs(num/den-row['minimum']) < 2e-8
                assert abs(ev[0]-row['minimum']) < 2e-8
                assert abs(ev[-1]-row['maximum']) < 2e-8
                assert row['condition']['rank_truncated'] is False
                assert row['condition']['whitening_residual'] < 2e-8
                residual = np.linalg.norm(b@v-row['minimum']*(a@v))/max(1.,np.linalg.norm(b@v))
                assert residual < 2e-8
                assert row['minimum'] <= last+2e-8
                last = row['minimum']
            if first is not None:
                d = np.sqrt(np.diag(T).real)
                scaled = lambda M: M/d[:, None]/d[None, :]
                error = max(np.linalg.norm(scaled(M-P), 2) for M, P in zip([T,R], first))
                assert abs(error-run['scaled_matrix_change']) < 2e-10 and error < 2e-8
            first = [T,R]
    # Re-evaluate a reference matrix independently, not just saved checks.
    ref = report['reference']
    T = reference(**ref['parameters'])
    saved = matrix(ref['matrix'])
    assert np.linalg.norm(T-saved)/max(1.,np.linalg.norm(saved)) < 2e-10
    assert ref['matrix_error'] < 2e-9 and ref['derivative_error'] < 2e-7
    assert max(report['derivative_checks']) < 2e-7
    print('Independent verification passed: all complex Hermite modes retained through degree 64; '
          'generalized spectra and witnesses checked; refined angle grids agree; '
          'separate Gaussian quadrature recomputed; prior 2039 hashes and root unchanged. '
          'This is local floating evidence, not a domain theorem or a uniform bound.')


if __name__ == '__main__':
    main()
