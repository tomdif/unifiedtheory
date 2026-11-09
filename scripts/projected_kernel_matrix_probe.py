#!/usr/bin/env python3
"""Actual projected Gaussian cross-kernel matrices and local clock response.

This tests the growing density c*T-T'/C relative to T at a fixed clock
coordinate, NOT the full clock-integrated response/energy quotient. All
complex cross terms are retained; unresolved modes cause rejection.
Floating quadrature and analytic moment formulas are not certified bounds.
Run: python3 scripts/projected_kernel_matrix_probe.py --output PATH
"""
import argparse
import hashlib
import json
from pathlib import Path
import time
import numpy as np
from numpy.polynomial.legendre import leggauss
from scipy.special import i0e
from scipy.linalg import eigh
import displaced_signed_response_probe as single
import matter_energy_gram_probe as old

class Kernels:

    def __init__(self, seeds, h=0.01, eps=1.0, nt=64, nd=768):
        self.seeds = np.asarray(seeds, float)
        if self.seeds.ndim != 2 or self.seeds.shape[1] != 2 or len(self.seeds) == 0 or (not np.isfinite(self.seeds).all()):
            raise ValueError('Expected a nonempty finite [A,lambda] list.')
        if np.any(self.seeds[:, 0] <= 0) or not np.isfinite([h, eps]).all() or (not (eps > 0 and 0 < abs(h) <= 2 * np.pi * eps / 3)):
            raise ValueError('Require positive A,epsilon and admissible nonzero hbar.')
        if any((not isinstance(n, int) or isinstance(n, bool) for n in [nt, nd])) or nt < 8 or nd < 16:
            raise ValueError('Invalid angle quadrature counts.')
        self.h = h
        self.eps = eps
        self.n = len(seeds)
        theta = 2 * np.pi * np.arange(nt) / nt
        (delta, dw) = leggauss(nd)
        delta *= np.pi
        dw /= 2 * nt
        th = np.repeat(theta, nd)
        ph = (theta[:, None] + delta[None, :]).ravel()
        self.aw = np.tile(dw, nt)
        left = [single.sources(A, l, h, th) for (A, l) in seeds]
        right = [single.sources(A, l, h, ph) for (A, l) in seeds]
        self.b = np.array([x[1] for x in left])
        self.c = np.array([x[1] for x in right])
        self.la = np.array([x[2] for x in left])
        self.lc = np.array([x[2] for x in right])
        self.widths = left[0][0]
        self.W = np.diag(self.widths)
        self.logbase = 2.5 * np.log(np.pi) - 0.5 * np.linalg.slogdet(2 * self.W)[1]
        (self.N, self.Kin) = self.static()
        (A, l) = self.seeds.T
        P = -l / A
        oracle = i0e(A[:, None] * A[None, :] / (4 * abs(h))) * np.exp(-(A[:, None] - A[None, :]) ** 2 / (8 * abs(h)) - (A[:, None] - A[None, :]) ** 2 / (128 * abs(h)) - 8 * (P[:, None] - P[None, :]) ** 2 / abs(h) + 1j * (A[:, None] + A[None, :]) * (P[None, :] - P[:, None]) / (2 * h))
        self.oracle_error = np.linalg.norm(self.N - oracle) / np.linalg.norm(oracle)
        if self.oracle_error >= 5e-10:
            raise ArithmeticError(f'Underresolved projected Gram: relative error {self.oracle_error:.6g}')
        self.diagonal_oracle_error = float(np.max(abs(np.diag(self.N - oracle)) / np.diag(oracle).real))
        assert self.diagonal_oracle_error < 5e-10
        for matrix in [self.N, self.Kin]:
            assert np.isfinite(matrix).all() and np.linalg.norm(matrix - matrix.conj().T) / max(1, np.linalg.norm(matrix)) < 1e-10

    def static(self):
        V0 = np.diag(1 / (4 * self.widths))
        N = np.zeros((self.n, self.n), complex)
        Kin = np.zeros_like(N)
        for i in range(self.n):
            for j in range(self.n):
                (b, c) = (self.b[i], self.c[j])
                lin = b.conj() + c
                mu = lin @ V0
                K = np.exp(0.5 * np.sum(lin * mu, axis=-1) + self.la[i] + self.lc[j])
                kin = np.zeros_like(K)
                for d in np.array([[1, 1, 0, 0, 0], [0, 0, 1, 1, 1], [1, -1, 0, 0, 0], [0, 0, 1, -1, 0]]):
                    row = -2 * self.widths * d
                    mr = mu @ row
                    kin += self.h ** 2 * ((b.conj() @ d + mr) * (c @ d + mr) + row @ V0 @ row)
                N[i, j] = self.aw @ K
                Kin[i, j] = self.aw @ (K * kin)
        return (N, Kin)

    def at(self, s):
        if not np.isfinite(s):
            raise ValueError('Clock coordinate must be finite.')
        (h, eps) = (self.h, self.eps)
        C = np.exp(s) + eps
        z = old.inverse_shift(s, eps, h)
        Cz = np.exp(z) + eps
        r = np.exp((z - s) / 2)
        rp = (C / Cz - 1) * r / 2
        L = np.eye(5, dtype=complex) * r
        L[4, 4] = 1
        L[4, 2:4] = 2 * (r - 1)
        Lp = np.eye(5, dtype=complex) * rp
        Lp[4, 4] = 0
        Lp[4, 2:4] = 2 * rp
        H = 2 * (L.T @ self.W @ L).real
        Hp = 2 * (Lp.T @ self.W @ L + L.T @ self.W @ Lp).real
        assert np.linalg.eigvalsh(H)[0] > 0
        V = 0.5 * np.linalg.inv(H)
        Vp = -2 * V @ Hp @ V
        T = np.zeros((self.n, self.n), complex)
        Tp = np.zeros_like(T)
        B = self.b @ L
        Bp = self.b @ Lp
        D = self.c @ L
        Dp = self.c @ Lp
        for i in range(self.n):
            for j in range(self.n):
                lin = B[i].conj() + D[j]
                linp = Bp[i].conj() + Dp[j]
                mu = lin @ V
                mup = linp @ V + lin @ Vp
                K = np.exp(2.5 * np.log(np.pi) - 0.5 * np.linalg.slogdet(H)[1] + 0.5 * np.sum(lin * mu, axis=-1) + self.la[i] + self.lc[j] - self.logbase)
                dlog = -np.trace(V @ Hp) + np.sum(linp * mu, axis=-1) + 0.5 * np.sum(lin * (lin @ Vp), axis=-1)
                F = np.array([0.0, 0.0, 1.0, 1.0, 1.0])
                m = mu @ F
                mp = mup @ F
                v = F @ V @ F
                vp = F @ Vp @ F
                poly = 1 + (m * m + v) / 2 + (m ** 4 + 6 * m * m * v + 3 * v * v) / 4
                polyp = (2 * m * mp + vp) / 2 + (4 * m ** 3 * mp + 12 * m * mp * v + 6 * m * m * vp + 6 * v * vp) / 4
                T[i, j] = self.aw @ (K * poly)
                Tp[i, j] = self.aw @ (K * (dlog * poly + polyp))
        coeff = 2 / C - (1 / Cz + eps / Cz ** 2).real
        for M in [T, Tp]:
            assert np.isfinite(M).all() and np.linalg.norm(M - M.conj().T) / max(1, np.linalg.norm(M)) < 1e-10
        return ((T + T.conj().T) / 2, (Tp + Tp.conj().T) / 2, coeff, C)

def recursive_reference(seeds, s, h=0.3, nt=64):
    """Absolute-angle torus and recursive moments, sharing source/inverse helpers."""
    theta = 2 * np.pi * np.arange(nt) / nt
    data = [single.sources(A, lam, h, theta) for (A, lam) in seeds]
    widths = data[0][0]
    b = np.concatenate([v[1] for v in data])
    amp = np.exp(np.concatenate([v[2] for v in data]))
    z = old.inverse_shift(s, 1.0, h)
    r = np.exp((z - s) / 2)
    L = np.eye(5, dtype=complex) * r
    (L[4, 4], L[4, 2:4]) = (1, 2 * (r - 1))
    (Z, _, _, moment) = old.gaussian_gram(b, amp, widths, L)
    F = np.array([0.0, 0.0, 1.0, 1.0, 1.0])
    value = Z * (1 + moment(F, F) / 2 + moment(F, F, F, F) / 4)
    base = np.exp(2.5 * np.log(np.pi) - 0.5 * np.linalg.slogdet(np.diag(2 * widths))[1])
    return value.reshape(len(seeds), nt, len(seeds), nt).mean(axis=(1, 3)) / base

def independent_check():
    seeds = [[1.0, 0.4], [1.2, 0.7], [1.5, 0.9]]
    (s, dx) = (-0.5, 0.001)
    k = Kernels(seeds, h=0.3, nt=32, nd=128)
    (T, Tp, _, _) = k.at(s)
    R = recursive_reference(seeds, s)
    Rp = (-recursive_reference(seeds, s + 2 * dx) + 8 * recursive_reference(seeds, s + dx) - 8 * recursive_reference(seeds, s - dx) + recursive_reference(seeds, s - 2 * dx)) / (12 * dx)
    error = float(np.linalg.norm(T - R) / max(1.0, np.linalg.norm(R)))
    derivative_error = float(np.linalg.norm(Tp - Rp) / max(1.0, np.linalg.norm(Rp)))
    assert error < 2e-10 and derivative_error < 2e-07
    return dict(seeds=seeds, h=0.3, s=s, main_angles=[32, 128], reference_absolute_angles=64, difference_step=dx, matrix_error=error, derivative_error=derivative_error)

def matrix_record(M):
    return dict(real=M.real.tolist(), imag=M.imag.tolist())

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    np.seterr(over='raise', invalid='raise', divide='raise')
    checks = independent_check()
    try:
        Kernels([[10.0, 4.0], [10.0, 4.2]], nt=64, nd=256)
    except ArithmeticError as exc:
        rejection = str(exc)
        assert rejection.startswith('Underresolved projected Gram:')
    else:
        raise AssertionError('Expected underresolved projected Gram rejection.')
    print('Independent recursive matrix/derivative checks and coarse-grid rejection passed.', flush=True)
    cases = [dict(name='lambda_line_33', seeds=[[10.0, float(l)] for l in np.linspace(1, 7, 33)], s=0.0, settings=[dict(nt=64, nd=768), dict(nt=96, nd=1024)]), dict(name='displacement_line_17', seeds=[[float(A), 4.0] for A in np.linspace(8, 12, 17)], s=-0.5, settings=[dict(nt=64, nd=896), dict(nt=96, nd=1152)])]
    reports = []
    for case in cases:
        (runs, first, first_witness) = ([], None, None)
        for setting in case['settings']:
            start = time.monotonic()
            k = Kernels(case['seeds'], **setting)
            (T, Tp, c, C) = k.at(case['s'])
            response = c * T - Tp / C
            (W, conditioning) = old.whitening(T)
            assert conditioning['whitening_residual'] < 2e-08
            H = W.conj().T @ response @ W
            assert np.linalg.norm(H - H.conj().T) / max(1.0, np.linalg.norm(H)) < 2e-10
            (values, U) = eigh((H + H.conj().T) / 2)
            witness = W @ U[:, 0]
            quotient = lambda v: float((v.conj() @ response @ v).real / (v.conj() @ T @ v).real)
            residual = float(np.linalg.norm(response @ witness - values[0] * (T @ witness)) / max(1.0, np.linalg.norm(response @ witness), abs(values[0]) * np.linalg.norm(T @ witness)))
            assert residual < 2e-10 and abs(quotient(witness) - values[0]) < 2e-10
            if first is None:
                (first, first_witness) = ((T, Tp), witness)
            changes = dict(kernel=float(np.linalg.norm(T - first[0]) / max(1.0, np.linalg.norm(T))), derivative=float(np.linalg.norm(Tp - first[1]) / max(1.0, np.linalg.norm(Tp))))
            fixed = quotient(first_witness)
            assert max(changes.values()) < 2e-08
            if runs:
                assert abs(fixed - runs[0]['minimum']) < 2e-08
                assert abs(values[0] - runs[0]['minimum']) < 2e-08
            runs.append(dict(quadrature=setting, minimum=float(values[0]), maximum=float(values[-1]), diagonal_minimum=float(np.min(np.diag(response).real / np.diag(T).real)), conditioning=conditioning, eigenpair_residual=residual, original_witness_quotient=fixed, matrix_changes=changes, clock=C, coefficient=c, kernel=matrix_record(T), derivative=matrix_record(Tp), witness_real=witness.real.tolist(), witness_imag=witness.imag.tolist(), projected_overlap_error=float(k.oracle_error), diagonal_overlap_error=k.diagonal_oracle_error, seconds=time.monotonic() - start))
            print(json.dumps(dict(case=case['name'], quadrature=setting, minimum=float(values[0]), fixed_witness=fixed, condition=conditioning['normalized_energy_condition'])), flush=True)
        reports.append(dict(name=case['name'], seeds=case['seeds'], clock_coordinate=case['s'], runs=runs))
    root = Path(__file__).resolve().parents[1]
    sources = ['scripts/projected_kernel_matrix_probe.py', 'scripts/displaced_signed_response_probe.py', 'scripts/matter_energy_gram_probe.py', 'data/clock_response_transport_audit.json', 'UnifiedTheory/Audit/KFCausalGaussianKernelResponse.lean']
    report = dict(kind='Exploratory local projected cross-kernel test, not a full energy quotient', parameters=dict(h=0.01, eps=1.0, vacuum=1.0, mass2=1.0, quartic=1.0), interpretation='Generalized spectrum of c*T-T_prime/C relative to T at a fixed clock coordinate. T is the growing transverse density with the zero-charge projection applied to vectors before pairing. The static energy and clock integrals are not included.', checks=checks, underresolved_grid_rejection=rejection, cases=reports, overlap_oracle='For positive A_i, let P_i=-lambda_i/A_i and t=A_i*A_j/(4*abs(h)). The unshifted normalized projected Gram is i0e(t)*exp(-(A_i-A_j)^2/(8*abs(h))-(A_i-A_j)^2/(128*abs(h))-8*(P_i-P_j)^2/abs(h)+i*(A_i+A_j)*(P_j-P_i)/(2*h)). Checked numerically; the Bessel integral is not formalized here.', source_sha256={p: hashlib.sha256((root / p).read_bytes()).hexdigest() for p in sources}, limitations=['Finite floating quadrature and finite-dimensional spectra; no certified sign or error enclosure.', 'No rank truncation; unresolved small modes are rejected.', 'The independent calculation shares source and inverse-chart helpers.', 'The coefficients are local growing-density quotients, not full fixed-time or evolution response/energy quotients.', 'These finite negative values do not refute a finite uniform lower bound.', 'Neither a model revision nor a physical TOE is established.'])
    text = json.dumps(report, indent=2, allow_nan=False) + '\n'
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text)
        print(args.output, flush=True)
    else:
        print(text)
if __name__ == '__main__':
    main()
