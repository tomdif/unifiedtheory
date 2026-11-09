#!/usr/bin/env python3
"""Projected field moments with independent neutral position and momentum.

The Lean companion derives the admitted packet source and its exact phase.
This script retains all complex coefficients and both charge-angle integrals.
Numerical quadrature does not certify tails or a state-uniform field bound.
"""
import argparse
import hashlib
import json
from pathlib import Path
import time

import numpy as np
from numpy.polynomial.legendre import leggauss
from scipy.special import i0e
import projected_initial_moment_probe as previous
import projected_integrated_response_probe as baseline
import projected_kernel_matrix_probe as transverse
import matter_energy_gram_probe as old


def sources(A, B, P, h, theta):
    widths = np.array([1., 1., 1., 1., 1/32])/(2*abs(h))
    Q = np.zeros((len(theta), 5))
    K = np.zeros_like(Q)
    Q[:, 2:4] = (A*np.cos(theta)/2)[:, None]
    Q[:, 4] = B
    K[:, 2], K[:, 3], K[:, 4] = A*np.sin(theta)/2, -A*np.sin(theta)/2, P
    return widths, 2*widths*Q+1j*K/h, -np.sum(widths*Q*Q, axis=1)


class Kernels(transverse.Kernels):
    def __init__(self, seeds, h=.3, eps=1., nt=32, nd=128):
        self.seeds = np.asarray(seeds, float)
        if (self.seeds.ndim != 2 or self.seeds.shape[1] != 3 or not len(self.seeds)
                or not np.isfinite(self.seeds).all() or np.any(self.seeds[:, 0] < 0)):
            raise ValueError('Expected finite [A,B,P] seeds with A >= 0.')
        if not np.isfinite([h, eps]).all() or not (eps > 0 and 0 < abs(h) <= 2*np.pi*eps/3):
            raise ValueError('Require positive epsilon and admissible nonzero hbar.')
        if any(not isinstance(n, int) or isinstance(n, bool) for n in [nt, nd]) or nt < 8 or nd < 16:
            raise ValueError('Invalid angle quadrature counts.')
        self.h, self.eps, self.n = h, eps, len(seeds)
        theta = 2*np.pi*np.arange(nt)/nt
        delta, dw = leggauss(nd)
        th = np.repeat(theta, nd)
        ph = (theta[:, None]+np.pi*delta[None, :]).ravel()
        self.aw = np.tile(dw/(2*nt), nt)
        left = [sources(A, B, P, h, th) for A, B, P in seeds]
        right = [sources(A, B, P, h, ph) for A, B, P in seeds]
        self.b, self.c = [np.array([s[1] for s in side]) for side in [left, right]]
        self.la, self.lc = [np.array([s[2] for s in side]) for side in [left, right]]
        self.widths = left[0][0]
        self.W = np.diag(self.widths)
        self.logbase = 2.5*np.log(np.pi)-.5*np.linalg.slogdet(2*self.W)[1]
        self.N, self.Kin = self.static()
        A, B, P = self.seeds.T
        oracle = i0e(A[:, None]*A[None, :]/(4*abs(h)))*np.exp(
            -(A[:, None]-A[None, :])**2/(8*abs(h))
            -(B[:, None]-B[None, :])**2/(128*abs(h))
            -8*(P[:, None]-P[None, :])**2/abs(h)
            +1j*(B[:, None]+B[None, :])*(P[None, :]-P[:, None])/(2*h))
        self.oracle_error = float(np.linalg.norm(self.N-oracle)/np.linalg.norm(oracle))
        if self.oracle_error >= 5e-10:
            raise ArithmeticError(f'Underresolved projected Gram: {self.oracle_error}')
        self.N, self.Kin = [baseline.hermitian(M) for M in [self.N, self.Kin]]


class Moments(previous.Moments):
    def __init__(self, packets, h=.3, eps=1., nt=32, nd=128):
        self.packets = np.asarray(packets, float)
        if (self.packets.ndim != 2 or self.packets.shape[1] != 5 or not len(self.packets)
                or not np.isfinite(self.packets).all() or np.any(self.packets[:, 3] <= 0)):
            raise ValueError('Expected finite [A,B,P,a,p] packets with a > 0.')
        seeds, self.indices = np.unique(self.packets[:, :3], axis=0, return_inverse=True)
        self.kernels = Kernels(seeds, h=h, eps=eps, nt=nt, nd=nd)
        self.h, self.eps = h, eps
        self.a, self.p = self.packets[:, 3:].T
        self.N, self.Kin = self.expand(self.kernels.N), self.expand(self.kernels.Kin)
        self.initial = self.transverse_moments(np.eye(5))


def reference_density(packets, s, h, nt=64):
    """Independent absolute-angle grid, component sources and Wick recursion.

    Shares the inverse-clock and Gaussian integration library with the main
    calculation; this is an implementation cross-check, not an error enclosure.
    """
    theta = 2*np.pi*np.arange(nt)/nt
    widths = np.array([1., 1., 1., 1., 1/32])/(2*abs(h))
    rows, amps = [], []
    for A, B, P, _, _ in packets:
        b = np.zeros((nt, 5), complex)
        b[:, 2] = widths[2]*A*np.cos(theta)+1j*A*np.sin(theta)/(2*h)
        b[:, 3] = widths[3]*A*np.cos(theta)-1j*A*np.sin(theta)/(2*h)
        b[:, 4] = 2*widths[4]*B+1j*P/h
        rows.append(b)
        amps.append(np.exp(-widths[2]*A*A*np.cos(theta)**2/2-widths[4]*B*B))
    b, amp = np.concatenate(rows), np.concatenate(amps)
    a, p = [np.repeat([v[col] for v in packets], nt) for col in [3, 4]]
    z = old.inverse_shift(s, 1., h)
    delta, C, chart = z-s, np.exp(s)+1, np.exp(s)+s
    r = np.exp(delta/2)
    L = np.eye(5, dtype=complex)*r
    L[4, 4], L[4, 2:4] = 1, 2*(r-1)
    amplitude1 = np.sqrt(C)*np.exp(-s-a*(chart-.5j*h)**2+1j*p*z)
    base = np.exp(2.5*np.log(np.pi)-.5*np.linalg.slogdet(np.diag(2*widths))[1])
    F = np.array([0., 0., 1., 1., 1.])
    out = {}
    for name, T, amplitude in [('initial', np.eye(5), np.exp(-delta)*amplitude1),
                                ('final', L, amplitude1)]:
        Z, _, _, moment = old.gaussian_gram(b, amp, widths, T)
        pair = amplitude.conj()[:, None]*amplitude[None, :]
        for power in range(3):
            poly = 1 if power == 0 else moment(*([F]*(2*power)))
            M = pair*Z*poly
            out[name+str(power)] = M.reshape(len(packets), nt, len(packets), nt).mean(axis=(1, 3))/base
    return out


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    np.seterr(over='raise', invalid='raise', divide='raise')
    root = Path(__file__).resolve().parents[1]
    # Check exact reduction to the previously used B=A, P=-lambda/A family.
    theta = np.linspace(-1., 8., 37)
    source_errors = []
    for A, lam, h in [(0.7, .2, .3), (2., -.4, -.3)]:
        new, prior = sources(A, A, -lam/A, h, theta), transverse.single.sources(A, lam, h, theta)
        error = max(float(np.max(abs(x-y))) for x, y in zip(new, prior))
        assert error < 1e-13
        source_errors.append(error)
    checks = []
    mixed = [[0., -2., .1, .5, -1.], [1., 0., -.2, .8, -.5],
             [2., 1., .3, 1.3, .7], [3., 3., 0., 2., 2.]]
    for h in [.3, -.3]:
        k = Moments(mixed, h=h, nt=40, nd=160)
        for s in [-2., -.5, .5]:
            actual, ref = k.densities(s), reference_density(mixed, s, h)
            errors = {name: float(np.linalg.norm(actual[name]-M)/max(1., np.linalg.norm(M)))
                      for name, M in ref.items()}
            assert max(errors.values()) < 2e-9, errors
            checks.append(dict(h=h, s=s, packets=mixed, errors=errors))
    print('Source specialization and six independent density checks passed.', flush=True)
    settings = [dict(nt=32, nd=128, left=-10., right=4., panels=28, order=10),
                dict(nt=48, nd=192, left=-12., right=4.5, panels=44, order=12)]
    grids = [('neutral_grid_9', [[A, B, 0., 1., 0.] for A in [0., 2., 4.] for B in [-4., 0., 4.]]),
             ('neutral_grid_16', [[A, B, 0., 1., 0.] for A in [0., 1., 2., 3.] for B in [-4., -2., 0., 2.]]),
             ('independent_momentum_clock', mixed)]
    cases = []
    for name, packets in grids:
        runs, first, first_witnesses = [], None, None
        for setting in settings:
            start = time.monotonic()
            k = Moments(packets, nt=setting['nt'], nd=setting['nd'])
            forms = k.integrate_moments(setting)
            spec = previous.spectra(forms)
            W, condition = old.whitening(forms['energy'])
            changes = {} if first is None else {
                key: float(np.linalg.norm(W.conj().T@(M-first[key])@W, 2)/
                           max(1., np.linalg.norm(W.conj().T@M@W, 2))) for key, M in forms.items()}
            assert not changes or max(changes.values()) < 2e-7, changes
            energy_ratios = {str(p): float(np.linalg.eigvalsh(
                baseline.hermitian(W.conj().T@forms['initial'+str(p)]@W))[-1]) for p in range(3)}
            if first is None:
                first = forms
                first_witnesses = {p: np.array(v['witness_real'])+1j*np.array(v['witness_imag'])
                                   for p, v in spec.items()}
            ratios = {p: old.value(forms['initial'+p], w)/old.value(forms['final'+p], w)
                      for p, w in first_witnesses.items()}
            runs.append(dict(quadrature=setting, spectra=spec, energy_condition=condition,
                             maximum_initial_energy_ratios=energy_ratios,
                             refinement_energy_scaled_changes=changes, first_witness_ratios=ratios,
                             gram_oracle_error=k.kernels.oracle_error,
                             matrices={key: transverse.matrix_record(M) for key, M in forms.items()},
                             seconds=time.monotonic()-start))
            print(json.dumps(dict(case=name, maxima={p: v['maximum'] for p, v in spec.items()},
                                  energy_ratios=energy_ratios)), flush=True)
        cases.append(dict(name=name, h=.3, eps=1., packets=packets, runs=runs))
    source_paths = ['scripts/independent_neutral_moment_probe.py',
                    'scripts/projected_initial_moment_probe.py',
                    'scripts/projected_integrated_response_probe.py',
                    'scripts/projected_kernel_matrix_probe.py', 'scripts/projected_matter_cost_probe.py',
                    'scripts/matter_energy_gram_probe.py', 'scripts/displaced_signed_response_probe.py',
                    'UnifiedTheory/Audit/KFCausalIndependentNeutralTestFamily.lean',
                    'UnifiedTheory/Audit/KFCausalProjectedInitialVacuumBound.lean']
    report = dict(kind='Independent-neutral projected initial field moments', cases=cases, checks=checks,
                  source_specialization_errors=source_errors, physical_time=0.,
                  energy_couplings=dict(mass2=1., quartic=1., vacuum=1.),
                  source_sha256={p: sha(root/p) for p in source_paths},
                  packet_columns=['charged_radius_A', 'neutral_position_B', 'neutral_momentum_P',
                                  'positive_clock_width_a', 'clock_frequency_p'],
                  formulas='initial_p=integral |Phi^p G0|^2, final_p=integral |Phi^p G1|^2. G0 includes exp(-Delta). Independent neutral coordinates are admitted by the Lean companion.',
                  limitations=['Floating quadrature, no certified tails, error enclosure or formal counterexample.',
                               'Source formulas are proved in Lean; this numerical implementation is not.',
                               'The independent density reference shares inverse-clock and Gaussian integral helpers.',
                               'Every complex mode retained; unresolved Gram modes rejected, no rank truncation.',
                               'Finite maxima neither prove nor disprove a state-uniform larger bound.',
                               'No response identity along the existing regulated propagator, clock escape, physical limit or TOE is established.'])
    args.output.write_text(json.dumps(report, indent=2, allow_nan=False)+'\n')
    print(args.output, flush=True)


if __name__ == '__main__':
    main()
