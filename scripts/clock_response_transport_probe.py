#!/usr/bin/env python3
"""Check clock-response transport with actual projected Gaussian kernels.

Five transverse integrals use floating Gaussian moments. Clock and two
charge angles use finite quadrature. All complex cross terms are retained.
Both finite-clock boundary terms are included. No quadrature, infinite-tail,
sign, uniform lower bound or physical evolution claim is certified here.

Run with NumPy/SciPy:
  python3 scripts/clock_response_transport_probe.py --output PATH
"""
import argparse
import hashlib
import json
from pathlib import Path
import time

import numpy as np
from numpy.polynomial.legendre import leggauss
from scipy.special import i0e, logsumexp
import displaced_signed_response_probe as single
import matter_energy_gram_probe as old


class Transverse:
    """Projected transverse energy kernel T and its analytic clock derivative.

    All kernels share the original unprojected transverse norm divisor.
    Differentiation includes covariance, mean, determinant and field moments.
    """
    def __init__(self, A=10., lam=4., h=.01, eps=1., nt=96, nd=768):
        if not np.isfinite([A, lam, h, eps]).all():
            raise ValueError('All parameters must be finite.')
        if not (A != 0 and eps > 0 and 0 < abs(h) <= 2*np.pi*eps/3):
            raise ValueError('Require A nonzero, epsilon positive and the admissible nonzero hbar strip.')
        if any(not isinstance(n, int) or isinstance(n, bool) for n in [nt, nd]):
            raise ValueError('Quadrature counts must be integers.')
        if nt < 8 or nd < 16:
            raise ValueError('Insufficient quadrature nodes.')
        self.h, self.eps = h, eps
        theta = 2*np.pi*np.arange(nt)/nt
        delta, dw = leggauss(nd)
        delta *= np.pi
        dw /= 2*nt
        th = np.repeat(theta, nd)
        ph = (theta[:, None]+delta[None, :]).ravel()
        self.aw = np.tile(dw, nt)
        widths, self.b, self.la, _, _ = single.sources(A, lam, h, th)
        _, self.c, self.lc, _, _ = single.sources(A, lam, h, ph)
        self.W = np.diag(widths)
        V0 = np.diag(1/(4*widths))
        cl0 = 2.5*np.log(np.pi)-.5*np.linalg.slogdet(2*self.W)[1]
        _, bz, laz, _, _ = single.sources(A, lam, h, [0.])
        self.logbase = cl0+np.sum(bz.real*(bz.real/(2*widths)), axis=-1)[0]+2*laz[0]
        lin = self.b.conj()+self.c
        mu = lin@V0
        K = np.exp(cl0+.5*np.sum(lin*mu, axis=-1)+self.la+self.lc-self.logbase)
        exact = np.exp(-A*A/(4*abs(h))*(1-np.cos(ph-th)))
        self.kernel_error = float(np.max(abs(K-exact)))
        kinetic = np.zeros_like(K)
        for d in np.array([[1, 1, 0, 0, 0], [0, 0, 1, 1, 1],
                           [1, -1, 0, 0, 0], [0, 0, 1, -1, 0]]):
            row = -2*widths*d
            mr = mu@row
            kinetic += h*h*((self.b.conj()@d+mr)*(self.c@d+mr)+row@V0@row)
        normal, kin = np.dot(self.aw, K), np.dot(self.aw, K*kinetic)
        reference = float(i0e(A*A/(4*abs(h))))
        self.overlap_error = float(abs(normal-reference)/reference)
        if self.overlap_error > 5e-10:
            raise ArithmeticError(f'Underresolved charge projection: relative norm error {self.overlap_error:.6g}')
        assert self.kernel_error < 2e-9
        assert max(abs(normal.imag), abs(kin.imag))/max(1., abs(normal), abs(kin)) < 2e-10
        assert normal.real > 0 and kin.real >= 0
        self.normal, self.kinetic = float(normal.real), float(kin.real)

    def at(self, s):
        if not np.isfinite(s):
            raise ValueError('Clock coordinate must be finite.')
        h, eps = self.h, self.eps
        C = np.exp(s)+eps
        z = old.inverse_shift(s, eps, h)
        Cz = np.exp(z)+eps
        r = np.exp((z-s)/2)
        rp = (C/Cz-1)*r/2
        L = np.eye(5, dtype=complex)*r
        L[4, 4], L[4, 2:4] = 1, 2*(r-1)
        Lp = np.eye(5, dtype=complex)*rp
        Lp[4, 4], Lp[4, 2:4] = 0, 2*rp
        H = 2*(L.T@self.W@L).real
        Hp = 2*(Lp.T@self.W@L+L.T@self.W@Lp).real
        if np.linalg.eigvalsh(H)[0] <= 0:
            raise ArithmeticError('Shifted Gaussian quadratic form is not positive.')
        V = .5*np.linalg.inv(H)
        Vp = -2*V@Hp@V
        lin = (self.b@L).conj()+self.c@L
        linp = (self.b@Lp).conj()+self.c@Lp
        mu, mup = lin@V, linp@V+lin@Vp
        K = np.exp(2.5*np.log(np.pi)-.5*np.linalg.slogdet(H)[1]+
                   .5*np.sum(lin*mu, axis=-1)+self.la+self.lc-self.logbase)
        dlog = -np.trace(V@Hp)+np.sum(linp*mu, axis=-1)+.5*np.sum(lin*(lin@Vp), axis=-1)
        F = np.array([0., 0., 1., 1., 1.])
        m, mp, v, vp = mu@F, mup@F, F@V@F, F@Vp@F
        poly = 1+(m*m+v)/2+(m**4+6*m*m*v+3*v*v)/4
        polyp = (2*m*mp+vp)/2+(4*m**3*mp+12*m*mp*v+6*m*m*vp+6*v*vp)/4
        T, Tp = np.dot(self.aw, K*poly), np.dot(self.aw, K*(dlog*poly+polyp))
        assert max(abs(T.imag), abs(Tp.imag))/max(1., abs(T), abs(Tp)) < 1e-9
        assert np.isfinite([T, Tp, z]).all() and T.real > 0
        coefficient = 2/C+(np.exp(z)/(Cz*Cz)-2/Cz).real
        return float(T.real), float(Tp.real), float(coefficient-Tp.real/C/T.real), z


def phase_log(p, h, eps, z):
    """Log squared phase minus max(p*h/eps,0), without large cancellation.

    Im(exp(z))+eps*Im(z)=-h/2 gives the alternate positive-offset formula.
    The same offset must be subtracted from the static energy density.
    """
    return 2*p*np.exp(z).imag/eps if p*h >= 0 else -2*p*np.imag(z)


def frequency_scan(transverse, ns, left, right, frequencies, a=1.):
    if not isinstance(ns, int) or isinstance(ns, bool) or ns < 16:
        raise ValueError('Clock quadrature count must be an integer of at least 16.')
    if not np.isfinite([left, right, a, *frequencies]).all() or left >= right or a <= 0:
        raise ValueError('Invalid clock interval, width or frequencies.')
    t = transverse
    h, eps = t.h, t.eps
    nodes, w = leggauss(ns)
    nodes = left+(nodes+1)*(right-left)/2
    w *= (right-left)/2
    vals = np.array([t.at(s) for s in nodes], complex)
    T, _, local, z = vals.T
    T, local = T.real, local.real
    C, u, Cz = np.exp(nodes)+eps, np.exp(nodes)+eps*nodes, np.exp(z)+eps
    static = .5*(C*t.normal+t.kinetic/C)
    sr = .5*(-np.exp(nodes)/C*t.normal+t.kinetic*np.exp(nodes)/C**3)
    direct_static = np.exp(nodes)/C**2-2/C-4*a*u
    endpoints = [(s, *t.at(s)) for s in [left, right]]
    result = []
    for p in frequencies:
        offset = max(p*h/eps, 0.)
        lg = np.log(w)+np.log(C)-2*nodes-2*a*(u*u-h*h/4)+phase_log(p, h, eps, z)+np.log(T)
        li = np.log(w)+2*np.log(C)-2*nodes-2*a*u*u+np.log(static)-offset
        logE = logsumexp(np.r_[lg, li])
        wg, wi = np.exp(lg-logE), np.exp(li-logE)
        rate = 2*(np.exp(z)/(2*Cz*Cz)-1/Cz-2*a*(u-.5j*h)+1j*p/Cz).real
        direct = np.dot(wg, rate)+np.dot(wi, direct_static)
        reduced = np.dot(wg, local)+np.dot(wi, sr/static)
        boundary = 0.
        for sign, (s, tv, _, _, zz) in zip([-1, 1], endpoints):
            cc, uu = np.exp(s)+eps, np.exp(s)+eps*s
            st = .5*(cc*t.normal+t.kinetic/cc)
            bg = -2*s-2*a*(uu*uu-h*h/4)+phase_log(p, h, eps, zz)+np.log(tv)
            bs = np.log(cc)-2*s-2*a*uu*uu+np.log(st)-offset
            boundary += sign*(np.exp(bg-logE)+np.exp(bs-logE))
        error = abs(direct-reduced-boundary)
        assert abs(np.sum(wg)+np.sum(wi)-1) < 2e-12 and error < 2e-9
        result.append(dict(p=p, direct_ratio=float(direct), reduced_ratio=float(reduced),
                           boundary_over_energy=float(boundary), identity_error=float(error),
                           log_energy=float(logE+offset), mean_clock=float(np.dot(wg+wi, nodes))))
    return dict(values=result, sampled_local_min=float(local.min()), sampled_local_max=float(local.max()),
                sampled_min_clock=float(nodes[local.argmin()]),
                projection_norm_relative_error=t.overlap_error, overlap_kernel_error=t.kernel_error)


def matrix_boundary_check():
    """All complex entries, three independent widths/frequencies; shared transverse recipe."""
    t = Transverse(A=1., lam=.4, h=.3, nt=64, nd=160)
    left, right, ns = -2., 1., 160
    a, p = np.array([.7, 1., 1.3]), np.array([-3., 0., 4.])
    nodes, w = leggauss(ns)
    nodes, w = left+(nodes+1)*(right-left)/2, w*(right-left)/2
    direct = np.zeros((3, 3), complex)
    reduced, energy = np.zeros_like(direct), np.zeros_like(direct)

    def values(s):
        T, _, local, z = t.at(s)
        C, u, Cz = np.exp(s)+1, np.exp(s)+s, np.exp(z)+1
        amp = np.sqrt(C)*np.exp(-s-a*(u-.15j)**2+1j*p*z)
        pairing = amp.conj()[:, None]*amp[None, :]
        slope = np.exp(z)/(2*Cz*Cz)-1/Cz-2*a*(u-.15j)+1j*p/Cz
        return T*pairing, slope.conj()[:, None]+slope[None, :], local, C

    for s, ds in zip(nodes, w):
        matrix, slope, local, _ = values(s)
        direct += ds*matrix*slope
        reduced += ds*matrix*local
        energy += ds*matrix
    boundary = values(right)[0]/values(right)[3]-values(left)[0]/values(left)[3]
    denominator = max(1., np.linalg.norm(direct))
    error = float(np.linalg.norm(direct-reduced-boundary)/denominator)
    omitted = float(np.linalg.norm(direct-reduced)/denominator)
    mineig = float(np.linalg.eigvalsh(energy)[0])
    assert error < 2e-11 and omitted > .05 and mineig > 0
    return dict(parameters=dict(A=1., lam=.4, h=.3, eps=1.), widths=a.tolist(), frequencies=p.tolist(),
                quadrature=dict(ns=ns, nt=64, nd=160, left=left, right=right),
                relative_matrix_error=error, error_without_boundary=omitted,
                boundary_norm=float(np.linalg.norm(boundary)), minimum_energy_eigenvalue=mineig,
                direct_real=direct.real.tolist(), direct_imag=direct.imag.tolist(),
                reduced_real=reduced.real.tolist(), reduced_imag=reduced.imag.tolist(),
                boundary_real=boundary.real.tolist(), boundary_imag=boundary.imag.tolist())


def derivative_check(t):
    result = []
    dx = 1e-3
    for s in [-30., -15., -5., -1., 0., 1., 3., 5.]:
        _, derivative, _, _ = t.at(s)
        finite = (-t.at(s+2*dx)[0]+8*t.at(s+dx)[0]-8*t.at(s-dx)[0]+t.at(s-2*dx)[0])/(12*dx)
        error = abs(finite-derivative)/max(1., abs(derivative))
        assert error < 2e-7
        result.append(dict(s=s, analytic_derivative=derivative, finite_difference=float(finite), error=float(error)))
    return dict(step=dx, stencil='five-point centered', results=result)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    np.seterr(over='raise', invalid='raise', divide='raise')
    matrix = matrix_boundary_check()
    try:
        Transverse(nt=96, nd=256)
    except ArithmeticError as exc:
        rejection = str(exc)
        assert rejection.startswith('Underresolved charge projection:')
    else:
        raise AssertionError('Expected underresolved charge projection rejection.')
    print('Complex matrix boundary check and underresolved-grid rejection passed.', flush=True)
    settings = [dict(ns=360, nt=96, nd=768, left=-20., right=4.),
                dict(ns=480, nt=128, nd=1024, left=-22., right=5.),
                dict(ns=600, nt=160, nd=1280, left=-24., right=5.5)]
    frequencies = [-1000., -100., -30., 0., 30., 100., 1000., 1e4, 1e6]
    runs = []
    derivative = None
    for setting in settings:
        start = time.monotonic()
        t = Transverse(nt=setting['nt'], nd=setting['nd'])
        scan = frequency_scan(t, setting['ns'], setting['left'], setting['right'], frequencies)
        if derivative is None:
            derivative = derivative_check(t)
        runs.append(dict(quadrature=setting, **scan, seconds=time.monotonic()-start))
        print(json.dumps(dict(quadrature=setting, ratios=[v['direct_ratio'] for v in scan['values']],
                             max_identity_error=max(v['identity_error'] for v in scan['values']))), flush=True)
    refinements = []
    for before, after in zip(runs, runs[1:]):
        changes = [abs(v['direct_ratio']-w['direct_ratio']) for v, w in zip(before['values'], after['values'])]
        assert max(changes) < 2e-8
        refinements.append(changes)
    root = Path(__file__).resolve().parents[1]
    files = ['scripts/clock_response_transport_probe.py', 'scripts/displaced_signed_response_probe.py',
             'scripts/matter_energy_gram_probe.py', 'data/zero_charge_structured_response_audit.json',
             'UnifiedTheory/Audit/KFCausalClockResponseTransport.lean',
             'UnifiedTheory/Audit/KFCausalSourcedMomentumDensity.lean',
             'UnifiedTheory/Audit/KFCausalGaussianKernelResponse.lean']
    report = dict(kind='Exploratory floating-point clock transport check; no certified bounds',
                  parameters=dict(A=10., lam=4., h=.01, eps=1., a=1.), physical_time=0.,
                  couplings=dict(mass2=1., quartic=1., vacuum=1.),
                  runs=runs, refinement_ratio_changes=refinements, matrix_boundary_check=matrix,
                  derivative_check=derivative, underresolved_grid_rejection=rejection,
                  stable_normalization='Common log offset max(p*h/eps,0), chart imaginary identity for growing phase, logsumexp energy; log_energy restores the offset.',
                  source_sha256={p: hashlib.sha256((root/p).read_bytes()).hexdigest() for p in files},
                  limitations=['Finite floating quadrature, not interval bounds or certified clock-tail control.',
                               'The complex matrix check shares transverse moments, source and inverse-chart helpers.',
                               'Lean derives actual pointwise Gaussian identities and finite clock transport, not this entire integration recipe.',
                               'Large-frequency sampling and local sampled extrema do not prove a state-uniform bound.',
                               'Transverse/charge integrals, infinite-clock limits, operator/core extension and physical evolution need separate justification.',
                               'Neither a physical TOE nor a need to revise the model is established.'])
    text = json.dumps(report, indent=2, allow_nan=False)+'\n'
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text)
        print(args.output, flush=True)
    else:
        print(text)


if __name__ == '__main__':
    main()
