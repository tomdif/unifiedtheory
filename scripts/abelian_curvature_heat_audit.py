#!/usr/bin/env python3
"""Audit the specified U(1) curvature heat model, not a presumed continuum law.

Exact rational checks cover finite identities. FFT, real-space Poisson series,
and an independent continuum Fourier series are compared numerically.
Floating-point checks are not substitutes for the accompanying proof.
Requires NumPy, already available in the project environment.
"""
from __future__ import annotations

import json
import math
import random
from fractions import Fraction as Q
from pathlib import Path

import numpy as np

AX, BX, AY, BY = 0.17, 0.61, 0.23, 0.79
T0, TMAX = 0.02, 0.08
TIMES = (T0, 0.04, TMAX)
FOURIER_CUTOFF = 32


def averaging(a):
    return (np.roll(a, 1, 0)+np.roll(a, -1, 0)+np.roll(a, 1, 1)+np.roll(a, -1, 1))/4


def symbol(n):
    k = np.fft.fftfreq(n)*n
    lam = 4*n*n*(np.sin(np.pi*k[:, None]/n)**2+np.sin(np.pi*k[None, :]/n)**2)
    return k, lam


def evolve(a, t):
    n = len(a)
    _, lam = symbol(n)
    answer = np.fft.ifft2(np.fft.fft2(a)*np.exp(-t*lam))
    assert np.max(np.abs(answer.imag)) < 2e-13
    return answer.real


def exact_cell_averages(n):
    def overlaps(a, b):
        return [max(Q(0), min(Q(i+1, n), b)-max(Q(i, n), a))*n for i in range(n)]
    x = overlaps(Q(17, 100), Q(61, 100))
    y = overlaps(Q(23, 100), Q(79, 100))
    return [[xx*yy for yy in y] for xx in x]


def exact_checks():
    rng = random.Random(41082)
    checks = 0
    for n in (3, 4, 5, 8):
        f = [[Q(rng.randint(-8, 8), 9) for _ in range(n)] for _ in range(n)]
        mean0 = sum(map(sum, f))
        bound = max(abs(v) for row in f for v in row)
        generator = [[n*n*(f[(i+1)%n][j]+f[(i-1)%n][j]+f[i][(j+1)%n]+f[i][(j-1)%n]-4*f[i][j])
                      for j in range(n)] for i in range(n)]
        lhs = sum(f[i][j]*generator[i][j] for i in range(n) for j in range(n))/(n*n)
        rhs = -sum((f[(i+1)%n][j]-f[i][j])**2+(f[i][(j+1)%n]-f[i][j])**2
                   for i in range(n) for j in range(n))
        assert lhs == rhs
        checks += 1
        for _ in range(10):
            f = [[(f[(i+1)%n][j]+f[(i-1)%n][j]+f[i][(j+1)%n]+f[i][(j-1)%n])/4
                  for j in range(n)] for i in range(n)]
            assert sum(map(sum, f)) == mean0
            assert max(abs(v) for row in f for v in row) <= bound
            checks += 2
        cells = exact_cell_averages(n)
        assert sum(map(sum, cells))/(n*n) == Q(44, 100)*Q(56, 100)
        assert all(0 <= v <= 1 for row in cells for v in row)
        checks += 2
    return checks


def poisson_checks():
    rng = np.random.default_rng(753)
    results = []
    for n in (4, 8):
        a = rng.uniform(-1, 1, (n, n))
        for t in (0.005, 0.03, 0.1):
            s = 4*n*n*t
            weight = math.exp(-s)
            current = a.copy()
            answer = weight*current
            for k in range(1000):
                next_weight = weight*s/(k+1)
                rho = s/(k+2)
                if rho < 1:
                    tail = next_weight/(1-rho)
                    if tail < 1e-14:
                        break
                current = averaging(current)
                weight = next_weight
                answer += weight*current
            else:
                raise AssertionError('Poisson tail did not close')
            err = float(np.max(np.abs(answer-evolve(a, t))))
            assert err <= tail+2e-13
            results.append({'n': n, 't': t, 'terms': k+1, 'error': err, 'tail_bound': tail})
    return results


def fourier_coeff(a, b, k):
    k = np.asarray(k)
    result = np.empty(k.shape, dtype=complex)
    zero = k == 0
    result[zero] = b-a
    nz = k[~zero]
    result[~zero] = (np.exp(-2j*np.pi*nz*a)-np.exp(-2j*np.pi*nz*b))/(2j*np.pi*nz)
    return result


def continuum_1d(a, b, t, points, integral=False):
    k = np.arange(-FOURIER_CUTOFF, FOURIER_CUTOFF+1)
    coeff = fourier_coeff(a, b, k)*np.exp(-4*np.pi*np.pi*k*k*t)
    e = np.exp(2j*np.pi*np.asarray(points)[:, None]*k[None, :])
    if integral:
        nz = k != 0
        e[:, nz] = (e[:, nz]-1)/(2j*np.pi*k[nz])
        e[:, ~nz] = np.asarray(points)[:, None]
    result = e@coeff
    assert np.max(np.abs(result.imag)) < 2e-13
    return result.real


def continuum_reference(n, t):
    nodes = np.arange(n+1)/n
    fx = continuum_1d(AX, BX, t, nodes[:-1])
    fy = continuum_1d(AY, BY, t, nodes[:-1])
    ix = continuum_1d(AX, BX, t, nodes, integral=True)
    iy = continuum_1d(AY, BY, t, nodes, integral=True)
    ref = fx[:, None]*fy[None, :]
    refv = np.exp(1j*ix[:, None]*np.diff(iy)[None, :])
    # In 1D |c_k|<=1. The Gaussian tail is bounded by a geometric tail.
    a = 4*math.pi*math.pi*t
    first = FOURIER_CUTOFF+1
    tail1d = 2*math.exp(-a*first*first)/(1-math.exp(-a*(2*first+1)))
    tail2d = 2*tail1d+tail1d*tail1d
    return ref, refv, tail2d


def gaussian_moment(q, t0):
    # Sum a square and bound all remaining square shells. The expression is
    # a rigorous analytic bound, evaluated here with uncertified floats.
    cut = 20
    k = np.arange(-cut, cut+1)
    r1 = np.abs(k[:, None])+np.abs(k[None, :])
    r2sq = k[:, None]**2+k[None, :]**2
    partial = float(np.sum(r1**q*np.exp(-16*t0*r2sq)))
    first = cut+1
    a = 16*t0
    initial = 8*(2**q)*(first**(q+1))*math.exp(-a*first*first)
    ratio = ((first+1)/first)**(q+1)*math.exp(-a*(2*first+1))
    assert ratio < 1
    return partial+initial/(1-ratio)


def spectral_checks():
    checks = 0
    for n in (3, 4, 5, 8, 12, 32, 64):
        k, lam = symbol(n)
        rsq = k[:, None]**2+k[None, :]**2
        mu = 4*np.pi*np.pi*rsq
        gap = (4*np.pi**4/3)/(n*n)*(k[:, None]**4+k[None, :]**4)
        assert np.all(lam >= 16*rsq-1e-9)
        assert np.all(lam <= mu+1e-9)
        assert np.all(mu-lam <= gap+1e-9)
        checks += n*n
    return checks


def reconstruct(f):
    n = len(f)
    h = 1/n
    H = np.ones((n, n+1), dtype=complex)
    phases = np.vstack((np.zeros((1, n)), h*h*np.cumsum(f, axis=0)))
    V = np.exp(1j*phases)
    P = V[1:, :]*np.conj(V[:-1, :])
    assert np.max(np.abs(P-np.exp(1j*h*h*f))) < 2e-14
    return H, V


def gauge_check(H, V, rng):
    n = H.shape[0]
    g = np.exp(1j*rng.uniform(-math.pi, math.pi, (n+1, n+1)))
    g[0, 0] = 1
    rawH = g[:-1, :]*H*np.conj(g[1:, :])
    rawV = g[:, :-1]*V*np.conj(g[:, 1:])
    fix = np.ones((n+1, n+1), dtype=complex)
    fix[0, 1:] = np.cumprod(rawV[0, :])
    for i in range(n):
        fix[i+1, :] = fix[i, :]*rawH[i, :]
    fixedH = fix[:-1, :]*rawH*np.conj(fix[1:, :])
    fixedV = fix[:, :-1]*rawV*np.conj(fix[:, 1:])
    err = max(float(np.max(np.abs(fixedH-H))), float(np.max(np.abs(fixedV-V))))
    assert err < 2e-10
    return err


def edge(H, V, a, b):
    i, j = a
    if b == (i+1, j):
        return H[i, j]
    if b == (i-1, j):
        return np.conj(H[i-1, j])
    if b == (i, j+1):
        return V[i, j]
    if b == (i, j-1):
        return np.conj(V[i, j-1])
    raise ValueError('non-neighbor path')


def transport(H, V, path):
    z = 1+0j
    for a, b in zip(path, path[1:]):
        z *= edge(H, V, a, b)
    return z


def rectangle(w, z):
    return ([(i, 0) for i in range(w+1)]+[(w, j) for j in range(1, z+1)]+
            [(i, z) for i in range(w-1, -1, -1)]+[(0, j) for j in range(z-1, -1, -1)])


def random_path(n, rng, steps):
    path = [(n//2, n//2)]
    for _ in range(steps):
        i, j = path[-1]
        choices = [(a, b) for a, b in ((i+1,j), (i-1,j), (i,j+1), (i,j-1))
                   if 0 <= a <= n and 0 <= b <= n]
        path.append(choices[rng.randrange(len(choices))])
    return path


def main():
    exact = exact_checks()
    poisson = poisson_checks()
    modes = spectral_checks()
    C = {q: gaussian_moment(q, T0) for q in (1, 2, 4)}
    L = 2*math.pi*C[1]
    rows = []
    expected_mean = (BX-AX)*(BY-AY)
    for n in (8, 12, 16, 24, 32, 48, 64, 96, 128):
        h = 1/n
        a = np.array(exact_cell_averages(n), dtype=float)
        initial_gradient = max(np.max(np.abs(np.roll(a,-1,0)-a)),
                               np.max(np.abs(np.roll(a,-1,1)-a)))/h
        previous_energy = float(np.mean(a*a)/2)
        E = 2*math.pi*C[1]*h+((4*math.pi**4/3)*TMAX*C[4]+4*C[2])*h*h
        for t in TIMES:
            f = evolve(a, t)
            assert f.min() >= -2e-13 and f.max() <= 1+2e-13
            assert abs(float(f.mean())-expected_mean) < 2e-13
            energy = float(np.mean(f*f)/2)
            assert energy <= previous_energy+2e-13
            previous_energy = energy
            grad = max(np.max(np.abs(np.roll(f,-1,0)-f)),
                       np.max(np.abs(np.roll(f,-1,1)-f)))/h
            assert grad <= L+2e-12
            ref, refV, ref_tail = continuum_reference(n, t)
            error = float(np.max(np.abs(f-ref)))
            assert error <= E+ref_tail+2e-12
            H, V = reconstruct(f)
            gauge_error = gauge_check(H, V, np.random.default_rng(2000+n))
            full_loop = transport(H,V,rectangle(n,n))
            assert abs(full_loop-np.exp(1j*expected_mean)) < 2e-11
            paths = [rectangle(n//2,n//2), rectangle(n,n)]
            rng = random.Random(n+round(t*1000))
            paths += [random_path(n,rng,4*n) for _ in range(12)]
            errors = []
            for path in paths:
                discrepancy = abs(transport(H,V,path)-transport(H,refV,path))
                ny = sum(p[1] != q[1] for p,q in zip(path,path[1:]))
                bound = ny*h*(E+L*h)
                assert discrepancy <= bound+ny*ref_tail+2e-11
                errors.append(discrepancy)
            eta = h/10
            rng2 = np.random.default_rng(n+91)
            perturbed = a+eta*rng2.uniform(-1,1,a.shape)
            contraction_error = float(np.max(np.abs(evolve(perturbed,t)-f)))
            assert contraction_error <= eta+2e-13
            rows.append({'n': n, 'time': t, 'curvature_error': error,
                         'universal_curvature_bound': E, 'initial_max_gradient': float(initial_gradient),
                         'evolved_max_gradient': float(grad), 'universal_gradient_bound': L,
                         'energy': energy, 'mean': float(f.mean()),
                         'interior_wilson_loop_error': errors[0], 'path_checks': len(paths),
                         'max_path_error': max(errors), 'gauge_fixing_error': gauge_error,
                         'continuum_series_tail_bound': ref_tail,
                         'initial_perturbation': eta, 'evolved_perturbation': contraction_error})
    for t in TIMES:
        subset = [r for r in rows if r['time'] == t]
        assert subset[-1]['curvature_error'] < subset[0]['curvature_error']/8
        assert subset[-1]['interior_wilson_loop_error'] < subset[0]['interior_wilson_loop_error']/8
    report = {'status': 'PASS', 'model': 'semidiscrete periodic lifted U(1) curvature heat; open-square links',
              'initial_data': 'indicator of [0.17,0.61) x [0.23,0.79), initialized by exact cell averages',
              'exact_rational_checks': exact, 'spectral_modes_checked': modes, 'poisson_fft_checks': poisson,
              't0': T0, 'T': TMAX, 'M': 1, 'gaussian_constants': C,
              'fourier_cutoff': FOURIER_CUTOFF, 'convergence': rows,
              'scope': 'Analytic theorem with partial Lean formalization. Floating-point rounding not certified.'}
    dest = Path(__file__).resolve().parents[1]/'data'/'abelian_curvature_heat_audit.json'
    dest.write_text(json.dumps(report,indent=2)+'\n')
    print(f'PASS: {exact} exact rational checks; {modes} spectral modes; {len(poisson)} Poisson/FFT comparisons')
    print('n    t       curvature error     interior Wilson error    evolved gradient')
    for row in rows:
        if row['time'] == T0:
            print(f"{row['n']:3d}  {row['time']:.3f}    {row['curvature_error']:.8f}          "
                  f"{row['interior_wilson_loop_error']:.8f}             {row['evolved_max_gradient']:.6f}")
    print(f"PASS: {sum(r['path_checks'] for r in rows)} path comparisons; {len(rows)} smoothing/conservation/perturbation cases")
    print(dest)


if __name__ == '__main__':
    main()
