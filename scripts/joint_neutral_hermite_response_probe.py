#!/usr/bin/env python3
"""Finite mixed-width neutral-Hermite kernel diagnostic, with all interference.

The basis uses zero neutral exponential sources and
P_n(z)=He_n(2*sqrt(beta)*z)/sqrt(n!), where He is the probabilists' Hermite
polynomial. Gaussian generating-function moments evaluate the existing
two-dimensional cross kernel. A differentiated recurrence computes its
actual clock derivative with the basis and coefficients frozen.

This is floating research evidence, not a Lean theorem, interval bound,
uniform constant, full-Hamiltonian test, or evolution statement. A poorly
conditioned Gram matrix rejects the whole case; no eigenmodes are removed.
"""
import argparse
import hashlib
import json
import math
from pathlib import Path

import numpy as np
import scipy
from numpy.polynomial.hermite import hermgauss

from joint_neutral_coherent_response_probe import components, geometry, pack, spectral


def matrices(alpha, beta, widths, degree, eps, h, s):
    """Return complete Gram/derivative matrices, width-major then degree."""
    w = np.asarray(widths, dtype=float)
    assert alpha > 0 and beta > 0 and 32*beta <= alpha*(1+1e-14)
    assert degree >= 0 and (w >= 1).all()
    r, rp = geometry(eps, h, s)
    wi, wj = w[:, None], w[None, :]
    A = alpha/2*(r.conjugate()**2/wi+r*r/wj)
    B = alpha/2*(r.conjugate()**2*wi+r*r*wj)
    C = B-8*beta*r.imag**2
    Ap = alpha*((r*rp).conjugate()/wi+r*rp/wj)
    Bp = alpha*((r*rp).conjugate()*wi+r*rp*wj)
    Cp = Bp-16*beta*r.imag*rp.imag
    assert min(A.real.min(), B.real.min(), C.real.min()) > 0
    eta, etap = 2*r.imag, 2*rp.imag
    L, Lp = 3-2*r.real, -2*rp.real
    vx, vy = 1/(4*beta), 1/(2*C)
    vyp = -Cp/(2*C*C)
    # Covariances in exp(t U-t^2/2+u V-u^2/2+z field).
    diagonal = -4*beta*eta*eta*vy
    diagonalp = -4*beta*(2*eta*etap*vy+eta*eta*vyp)
    mixed, mixedp = 1-diagonal, -diagonalp
    uf = 2*np.sqrt(beta)*(vx-1j*eta*L*vy)
    ufp = -2j*np.sqrt(beta)*(etap*L*vy+eta*Lp*vy+eta*L*vyp)
    vf = 2*np.sqrt(beta)*(vx+1j*eta*L*vy)
    vfp = -ufp
    ff = vx+L*L*vy
    ffp = 2*L*Lp*vy+L*L*vyp
    size = degree+1
    moments = np.zeros((size, size, 5, len(w), len(w)), dtype=complex)
    slopes = np.zeros_like(moments)
    moments[0, 0, 0] = 1
    for k in range(2, 5):
        moments[0, 0, k] = (k-1)*ff*moments[0, 0, k-2]
        slopes[0, 0, k] = (k-1)*(ffp*moments[0, 0, k-2]+ff*slopes[0, 0, k-2])
    for n in range(1, size):
        for k in range(5):
            if n >= 2:
                a = np.sqrt((n-1)/n)
                moments[0, n, k] += a*diagonal*moments[0, n-2, k]
                slopes[0, n, k] += a*(diagonalp*moments[0, n-2, k]+diagonal*slopes[0, n-2, k])
            if k:
                a = k/np.sqrt(n)
                moments[0, n, k] += a*vf*moments[0, n-1, k-1]
                slopes[0, n, k] += a*(vfp*moments[0, n-1, k-1]+vf*slopes[0, n-1, k-1])
    for m in range(1, size):
        for n in range(size):
            for k in range(5):
                terms = []
                if m >= 2:
                    terms.append((np.sqrt((m-1)/m), diagonal, diagonalp, m-2, n, k))
                if n:
                    terms.append((np.sqrt(n/m), mixed, mixedp, m-1, n-1, k))
                if k:
                    terms.append((k/np.sqrt(m), uf, ufp, m-1, n, k-1))
                for a, cov, covp, mi, ni, ki in terms:
                    moments[m, n, k] += a*cov*moments[mi, ni, ki]
                    slopes[m, n, k] += a*(covp*moments[mi, ni, ki]+cov*slopes[mi, ni, ki])
    polynomial = moments[:, :, 0]+moments[:, :, 2]/2+moments[:, :, 4]/4
    polynomialp = slopes[:, :, 0]+slopes[:, :, 2]/2+slopes[:, :, 4]/4
    prefactor = np.pi/(4*A)*np.sqrt(np.pi/B)*np.sqrt(np.pi/C)*np.sqrt(np.pi/(2*beta))
    score = -Ap/A-Bp/(2*B)-Cp/(2*C)
    K = (prefactor*polynomial).transpose(2, 0, 3, 1).reshape(len(w)*size, len(w)*size)
    D = (prefactor*(score*polynomial+polynomialp)).transpose(2, 0, 3, 1).reshape(K.shape)
    assert np.isfinite(K).all() and np.isfinite(D).all()
    return K, D


def hermite_value(n, z):
    """Normalized probabilists' Hermite polynomial, independent evaluation."""
    previous = np.ones_like(z, dtype=complex)
    if not n:
        return previous
    current = z.astype(complex)
    for k in range(1, n):
        previous, current = current, z*current/np.sqrt(k+1)-np.sqrt(k/(k+1))*previous
    return current


def quadrature(alpha, beta, wi, wj, m, n, r, order):
    """Real two-dimensional quadrature; complex Gaussian phase retained."""
    A = alpha/2*(r.conjugate()**2/wi+r*r/wj)
    B = alpha/2*(r.conjugate()**2*wi+r*r*wj)
    C = B-8*beta*r.imag**2
    nodes, weights = hermgauss(order)
    X, Y = np.meshgrid(nodes/np.sqrt(2*beta), nodes/np.sqrt(C.real), indexing='ij')
    zeta = X+2j*r.imag*Y
    field = X+(3-2*r.real)*Y
    integrand = (1+field**2/2+field**4/4)*hermite_value(m, 2*np.sqrt(beta)*zeta).conj()*hermite_value(n, 2*np.sqrt(beta)*zeta)
    integrand *= np.exp(-1j*C.imag*Y*Y)
    plane = np.einsum('i,j,ij->', weights, weights, integrand)/np.sqrt(2*beta*C.real)
    return np.pi/(4*A)*np.sqrt(np.pi/B)*plane


def validation():
    eps, h, s = 1., 1., 0.
    alpha, beta, widths, degree = .5, 1/64, [1., 2., 10.], 12
    K, D = matrices(alpha, beta, widths, degree, eps, h, s)
    scale = np.sqrt(K.diagonal().real)
    normalized = lambda A: A/scale[:, None]/scale[None, :]
    differences = []
    for step in [1e-3, 1e-4]:
        F = lambda t: matrices(alpha, beta, widths, degree, eps, h, t)[0]
        fd = (-F(s+2*step)+8*F(s+step)-8*F(s-step)+F(s-2*step))/(12*step)
        error = float(np.linalg.norm(normalized(fd-D))/np.linalg.norm(normalized(D)))
        assert error < 2e-8, error
        differences.append(dict(step=step, normalized_relative_error=error))
    base, basep = components(alpha, beta, widths, [0]*len(widths), *geometry(eps, h, s))
    indexes = np.arange(len(widths))*(degree+1)
    base_errors = [float(np.linalg.norm(K[np.ix_(indexes, indexes)]-base)/np.linalg.norm(base)),
                   float(np.linalg.norm(D[np.ix_(indexes, indexes)]-basep)/np.linalg.norm(basep))]
    assert max(base_errors) < 2e-12, base_errors
    checks = []
    r, _ = geometry(eps, h, s)
    for i, j, m, n in [(0, 0, 0, 0), (0, 1, 1, 3), (1, 2, 4, 4), (0, 2, 8, 10), (2, 1, 12, 12)]:
        row, col = i*(degree+1)+m, j*(degree+1)+n
        for order in [48, 96]:
            q = quadrature(alpha, beta, widths[i], widths[j], m, n, r, order)
            # Absolute error in normalized Gram coordinates also covers tiny entries.
            error = float(abs(q-K[row, col])/(scale[row]*scale[col]))
            assert error < 2e-11, (i, j, m, n, order, error)
            checks.append(dict(width_i=i, width_j=j, degree_i=m, degree_j=n,
                               order=order, normalized_absolute_error=error))
    return dict(finite_differences=differences, degree_zero_coherent_errors=base_errors,
                independent_real_quadrature=checks)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path)
    parser.add_argument('--smoke', action='store_true')
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    parent = root/'data/quantum_joint_whole_clock_transport_audit.json'
    assert digest(parent) == '66969ec1f3595c57cca7a83ea8381bb100f0995f54798b54391b7aba0f6307f5'
    checks = validation()
    grid = dict(h=[1., 100.] if args.smoke else [1/64, .1, 1., 10., 100.],
                clock_offset=[0., 2.] if args.smoke else [-3., 0., 1., 2., 3.],
                width_count=[1, 3] if args.smoke else [1, 3, 5],
                max_degree=[0, 2, 8] if args.smoke else [0, 1, 2, 4, 8, 12, 16])
    records, best, normalized_best = [], None, None
    for h in grid['h']:
        eps, alpha, beta = h, 1/(2*h), 1/(64*h)
        for offset in grid['clock_offset']:
            s = math.log(eps)+offset
            for count in grid['width_count']:
                widths = np.geomspace(1, 30, count)
                for degree in grid['max_degree']:
                    K, D = matrices(alpha, beta, widths, degree, eps, h, s)
                    result = spectral(K, D)
                    meta = dict(h=h, epsilon=eps, alpha=alpha, beta=beta, s=s,
                                clock_offset=offset, width_count=count, max_degree=degree,
                                dimension=count*(degree+1))
                    if isinstance(result, dict):
                        records.append(dict(**meta, **result))
                        continue
                    values, coefficients = result
                    values['normalized_max_slope'] = eps/(math.exp(s)+eps)*values['max_slope']
                    record = dict(**meta, **values)
                    records.append(record)
                    witness = dict(parameters=meta, result=values, widths=widths.tolist(),
                                   coefficients=pack(coefficients), gram=pack(K), derivative=pack(D))
                    if best is None or values['max_slope'] > best['result']['max_slope']:
                        best = witness
                    if normalized_best is None or values['normalized_max_slope'] > normalized_best['result']['normalized_max_slope']:
                        normalized_best = witness
        print('Completed h=', h, 'cases=', len(records), flush=True)
    sources = ['scripts/joint_neutral_hermite_response_probe.py',
               'scripts/joint_neutral_coherent_response_probe.py', 'scripts/matter_energy_gram_probe.py',
               'UnifiedTheory/Audit/KFCausalReciprocalNeutralKernel.lean',
               'UnifiedTheory/Audit/KFCausalReciprocalCrossGeometry.lean',
               'UnifiedTheory/Audit/KFCausalReciprocalNeutralWholeClock.lean']
    report = dict(scope=__doc__, parent_report=dict(path=str(parent.relative_to(root)), sha256=digest(parent)),
                  source_sha256={p:digest(root/p) for p in sources}, numpy=np.__version__, scipy=scipy.__version__,
                  smoke=args.smoke, grid=grid, neutral_sources_zero=True,
                  basis='He_n(2*sqrt(beta)*z)/sqrt(n!), width-major then degree',
                  conditioning_floor=1e-9, rank_truncation=False, validation=checks,
                  test_count=len(records), rejected_cases=sum(bool(r.get('rejected_condition')) for r in records),
                  records=records, largest_observed=best, largest_normalized_observed=normalized_best,
                  conclusion='Finite polynomial-span diagnostic only. A finite maximum neither proves a uniform relative bound nor disproves one. Nonzero neutral sources, unrestricted degrees and widths, the full clock integral, full Hamiltonian response and evolution are not covered.')
    args.output.write_text(json.dumps(report, indent=2, allow_nan=False)+'\n')
    print('Cases', report['test_count'], 'rejected whole matrices', report['rejected_cases'], flush=True)
    print('Largest raw slope', best['result']['max_slope'], best['parameters'], flush=True)
    print('Largest epsilon/clock normalized slope', normalized_best['result']['normalized_max_slope'], normalized_best['parameters'], flush=True)
    print(args.output)


if __name__ == '__main__':
    main()
