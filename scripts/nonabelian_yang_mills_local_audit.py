#!/usr/bin/env python3
"""Audit the actual SU(2) DeTurck--Yang--Mills Fourier--Galerkin ODE.

Exact rational algebra, independent convolution, and numerical evolution.
Floating-point results validate the implementation, not the continuum proof.
SU(2) Lie algebra elements are imaginary quaternions: [a,b] = 2 a cross b.
Requires numpy and scipy. Run from any directory; output is repository-local.
"""
from __future__ import annotations

import json
import math
import random
from fractions import Fraction as Q
from pathlib import Path

import numpy as np
from scipy.integrate import solve_ivp


def qmul(a, b):
    w, x, y, z = a
    v, i, j, k = b
    return (w*v-x*i-y*j-z*k, w*i+x*v+y*k-z*j,
            w*j-x*k+y*v+z*i, w*k+x*j-y*i+z*v)


def qadd(a, b):
    return tuple(x+y for x, y in zip(a, b))


def qsub(a, b):
    return tuple(x-y for x, y in zip(a, b))


def bracket(a, b):
    return qsub(qmul(a, b), qmul(b, a))


def exact_checks():
    rng = random.Random(20261109)
    count = 0
    for _ in range(24):
        a, b, ax, ay, bx, by = [tuple(Q(rng.randint(-7, 7), 5) for _ in range(4))
                                for _ in range(6)]
        # D_j F_ji + D_i div A: derivative brackets, omitting cancelling jets.
        lhs = qadd(qadd(bracket(by, a), bracket(b, ay)),
                   qadd(bracket(b, qadd(qsub(ay, bx), bracket(b, a))),
                        bracket(a, qadd(ax, by))))
        rhs = qadd(qadd(bracket(a, ax), tuple(2*x for x in bracket(b, ay))),
                   qsub(bracket(b, bracket(b, a)), bracket(b, bx)))
        assert lhs == rhs
        assert qsub(bracket(a, b), bracket(ax, ay)) == qadd(
            bracket(qsub(a, ax), b), bracket(ax, qsub(b, ay)))
        count += 2
    for a in (Q(-3, 2), Q(0), Q(1, 7), Q(7, 10)):
        x, y = (0, a, 0, 0), (0, 0, a, 0)
        f = bracket(x, y)
        assert f == (0, 0, 0, 2*a*a)
        assert bracket(y, bracket(y, x)) == (0, -4*a**3, 0, 0)
        assert bracket(x, bracket(x, y)) == (0, 0, -4*a**3, 0)
        assert sum(v*v for v in f) == 4*a**4
        count += 4
    return count


def modes(n):
    return np.arange(-n, n+1)


def derivative(a, j):
    n = (len(a)-1)//2
    k = modes(n)
    factor = k[:, None] if j == 0 else k[None, :]
    return a*(2j*np.pi*factor[:, :, None, None])


def pad_coeff(a, m):
    n = (len(a)-1)//2
    k = modes(n) % m
    z = np.zeros((m, m, 2, 3), complex)
    z[k[:, None], k[None, :]] = a
    return z


def nonlinear(a):
    n = (len(a)-1)//2
    # Every cubic frequency lies in [-3N,3N]^2: M=6N+1 resolves all of it.
    m = 6*n+1
    physical = np.fft.ifft2(pad_coeff(a, m), axes=(0, 1))*m*m
    d = [np.fft.ifft2(pad_coeff(derivative(a, j), m), axes=(0, 1))*m*m
         for j in range(2)]
    out = np.zeros_like(physical)
    for i in range(2):
        for j in range(2):
            aj = physical[:, :, j, :]
            ai = physical[:, :, i, :]
            out[:, :, i, :] += (4*np.cross(aj, d[j][:, :, i, :])
                                - 2*np.cross(aj, d[i][:, :, j, :])
                                + 4*np.cross(aj, np.cross(aj, ai)))
    coeff = np.fft.fft2(out, axes=(0, 1))/(m*m)
    k = modes(n) % m
    return coeff[k[:, None], k[None, :]]


def diffusion(a):
    n = (len(a)-1)//2
    k = modes(n)
    return -4*np.pi**2*(k[:, None]**2+k[None, :]**2)[:, :, None, None]*a


def evolve(a, times, tight=False):
    shape = a.shape
    def rhs(_, y):
        field = y.reshape(shape)
        return (diffusion(field)+nonlinear(field)).ravel()
    sol = solve_ivp(rhs, (0, float(times[-1])), a.ravel(), method='DOP853',
                    t_eval=times, rtol=2e-12 if tight else 2e-10,
                    atol=2e-15 if tight else 2e-13,
                    max_step=float(times[-1])/(16 if tight else 8))
    assert sol.success, sol.message
    return [row.reshape(shape) for row in sol.y.T], sol.nfev


def norm_upper(a, r):
    # Triangle inequality in the fixed quaternion basis is a safe upper bound
    # for COMPLEX Fourier coefficients' matrix operator norms.
    n = (len(a)-1)//2
    k = modes(n)
    w = 1+abs(k[:, None])+abs(k[None, :])
    return float(np.sum(w[:, :, None, None]**r*np.abs(a)))


def embed(a, n):
    j = (len(a)-1)//2
    assert j <= n
    out = np.zeros((2*n+1, 2*n+1, 2, 3), complex)
    out[n-j:n+j+1, n-j:n+j+1] = a
    return out


def project(a, n):
    j = (len(a)-1)//2
    assert n <= j
    return a[j-n:j+n+1, j-n:j+n+1].copy()


def initial_data(n=8):
    a = np.zeros((2*n+1, 2*n+1, 2, 3), complex)
    a[n, n, 0, 0] = .035
    a[n, n, 1, 1] = .028
    def add_mode(i, axis, kx, ky, amplitude, sine=False):
        z = amplitude/(2j) if sine else amplitude/2
        a[n+kx, n+ky, i, axis] += z
        a[n-kx, n-ky, i, axis] += z.conjugate() if isinstance(z, complex) else z
    for k in range(1, 7):
        add_mode(0, 2, k, 0, .0015/k**6)
        add_mode(1, 0, 0, k, .0012/k**6, sine=True)
    add_mode(0, 1, 1, 1, .0004, sine=True)
    add_mode(1, 2, 1, -1, .0003)
    return a


def direct_convolution_checks():
    # Independent dictionary convolutions: NEVER project the inner bracket.
    rng = np.random.default_rng(531)
    a = rng.normal(size=(3, 3, 2, 3))+1j*rng.normal(size=(3, 3, 2, 3))
    a = (a+np.conj(a[::-1, ::-1]))/20
    fs = [{(x, y): a[x+1, y+1, i] for x in (-1, 0, 1) for y in (-1, 0, 1)}
          for i in range(2)]
    def cross_conv(f, g):
        out = {}
        for k, v in f.items():
            for ell, w in g.items():
                key = (k[0]+ell[0], k[1]+ell[1])
                out[key] = out.get(key, np.zeros(3, complex))+np.cross(v, w)
        return out
    def deriv(f, j):
        return {k: 2j*np.pi*k[j]*v for k, v in f.items()}
    out = np.zeros_like(a)
    for i in range(2):
        for j in range(2):
            terms = [(4, cross_conv(fs[j], deriv(fs[i], j))),
                     (-2, cross_conv(fs[j], deriv(fs[j], i))),
                     (4, cross_conv(fs[j], cross_conv(fs[j], fs[i])))]
            for scale, f in terms:
                for (x, y), v in f.items():
                    if max(abs(x), abs(y)) <= 1:
                        out[x+1, y+1, i] += scale*v
    error = float(np.max(abs(nonlinear(a)-out)))
    assert error < 3e-14
    # Proper rotations are precisely the adjoint SU(2) action on this algebra.
    theta = .61
    rotation = np.array([[math.cos(theta), -math.sin(theta), 0],
                         [math.sin(theta), math.cos(theta), 0], [0, 0, 1]])
    gauge_error = float(np.max(abs(nonlinear(a@rotation.T)-nonlinear(a)@rotation.T)))
    assert gauge_error < 3e-14
    reality_error = float(np.max(abs(nonlinear(a)-np.conj(nonlinear(a)[::-1, ::-1]))))
    assert reality_error < 3e-14
    return {'independent_convolution_max_error': error,
            'constant_SU2_conjugation_max_error': gauge_error,
            'Lie_algebra_reality_max_error': reality_error,
            'coefficients_compared': int(a.size), 'padding_rule': 'M=6N+1'}


def homogeneous_checks():
    a0 = .7
    init = np.zeros((1, 1, 2, 3), complex)
    init[0, 0, 0, 0] = a0
    init[0, 0, 1, 1] = a0
    times = np.linspace(0, 1, 21)
    values, calls = evolve(init, times, tight=True)
    error = 0.
    energies = []
    for t, value in zip(times, values):
        exact = init/math.sqrt(1+8*a0*a0*t)
        error = max(error, float(np.max(abs(value-exact))))
        f = 2*np.cross(value[0, 0, 0].real, value[0, 0, 1].real)
        energies.append(float(.5*np.dot(f, f)))
    assert error < 1e-10
    assert all(b < a for a, b in zip(energies, energies[1:]))
    assert energies[-1] > 0
    separation = float(np.max(abs(values[-1]-init)))
    assert separation > .3
    return {'initial_amplitude': a0, 'end_time': 1., 'time_samples': len(times),
            'exact_solution_max_error': error, 'half_energy_initial': energies[0],
            'half_energy_final': energies[-1], 'energy_strictly_decreases': True,
            'separation_from_commutator_free_solution': separation,
            'rhs_evaluations': calls,
            'scope': 'Global test of this exact homogeneous family only.'}


def evaluate(a, points):
    n = (len(a)-1)//2
    k = modes(n)
    kx, ky = np.meshgrid(k, k, indexing='ij')
    phase = np.exp(2j*np.pi*(points[:, 0, None]*kx.ravel()
                            +points[:, 1, None]*ky.ravel()))
    values = (phase@a.reshape(-1, 6)).reshape(len(points), 2, 3)
    assert np.max(abs(values.imag)) < 3e-12
    return values.real


def transport(a, vertices, steps):
    u = (1., 0., 0., 0.)
    for x, y in zip(vertices, vertices[1:]):
        x, y = np.asarray(x), np.asarray(y)
        delta = y-x
        points = x+(np.arange(steps)[:, None]+.5)*delta/steps
        field = evaluate(a, points)
        vectors = (delta[0]*field[:, 0]+delta[1]*field[:, 1])/steps
        for v in vectors:
            size = float(np.linalg.norm(v))
            scale = math.sin(size)/size if size else 1.
            u = qmul(u, (math.cos(size), *(scale*v)))
    assert abs(sum(x*x for x in u)-1) < 3e-12
    return np.asarray(u)


def run():
    result = {'status': 'PASS',
              'model': 'Exact Fourier--Galerkin SU(2) DeTurck--Yang--Mills heat on T^2',
              'scope': 'Local regular-data theorem; no local Wilson-link evolution asserted.',
              'exact_rational_checks': exact_checks(),
              'projection_audit': direct_convolution_checks(),
              'homogeneous_nonlinear_witness': homogeneous_checks()}
    s, p, q = 2, 2, 4
    reference_n = 8
    init = initial_data(reference_n)
    a0_upper = norm_upper(init, q)
    radius = 2*a0_upper
    lipschitz = 32*np.pi*radius+12*radius**2
    b = 16*np.pi*radius**2+4*radius**3
    z = 1/(2*lipschitz)
    tmax = (z/(math.sqrt(1+z)+1))**2  # cancellation-safe form of (8)
    kernel = tmax+2*math.sqrt(tmax)
    assert abs(kernel*lipschitz-.5) < 1e-14
    assert a0_upper+kernel*b <= .75*radius
    times = np.linspace(0, tmax, 5)
    references, _ = evolve(init, times, tight=True)
    def error_bound(n):
        return 2*(a0_upper+kernel*b)/(n+1)**p
    assert max(norm_upper(a, q) for a in references) <= radius
    rows = []
    finals = {reference_n: references[-1]}
    max_temporal = 0.
    for n in (1, 2, 3, 4, 6):
        values, calls = evolve(project(init, n), times)
        tighter, _ = evolve(project(init, n), times, tight=True)
        time_difference = max(norm_upper(a-c, s) for a, c in zip(values, tighter))
        max_temporal = max(max_temporal, time_difference)
        error = max(norm_upper(embed(a, reference_n)-ref, s)
                    for a, ref in zip(values, references))
        upper = max(norm_upper(a, q) for a in values)
        assert upper <= radius
        assert error <= error_bound(n)+error_bound(reference_n)
        assert time_difference < 2e-9
        finals[n] = tighter[-1]
        rows.append({'cutoff': n, 'sampled_max_Ws_difference_to_N8': error,
                     'sampled_max_Wq_upper': upper,
                     'analytic_allowance_EN_plus_E8': error_bound(n)+error_bound(reference_n),
                     'tighter_time_integration_difference_Ws': time_difference,
                     'rhs_evaluations': calls})
    assert all(y['sampled_max_Ws_difference_to_N8'] < x['sampled_max_Ws_difference_to_N8']
               for x, y in zip(rows, rows[1:]))
    linear_final = init*np.exp(-4*np.pi**2*tmax*(modes(reference_n)[:, None]**2
                                 +modes(reference_n)[None, :]**2))[:, :, None, None]
    nonlinear_separation = norm_upper(references[-1]-linear_final, s)
    assert nonlinear_separation > 1e-9
    result['local_experiment'] = {
        's': s, 'p': p, 'q': q, 'initial_Wq_certifying_upper_formula_float': a0_upper,
        'common_radius': radius, 'guaranteed_time_formula_float': tmax,
        'contraction_constant_formula_float': kernel*lipschitz,
        'time_samples': len(times), 'reference_cutoff': reference_n,
        'inhomogeneous_nonlinear_separation_from_heat_Ws': nonlinear_separation,
        'maximum_time_tolerance_comparison_Ws': max_temporal, 'cutoff_comparisons': rows,
        'qualification': 'Bounds evaluated in ordinary floating point, not interval-certified. '
                         'Differences use an N=8 numerical reference, not the exact continuum. '
                         'Tolerance comparisons are diagnostics, not rigorous ODE error bounds.'}
    paths = [np.array([(0.13, .17), (.83, .17)]),
             np.array([(.11, .19), (.71, .19), (.71, .79), (.11, .79), (.11, .19)]),
             np.array([(.05, .31), (1.05, .31)]),
             np.array([(.14, .21), (.67, .21), (.67, .72)])]
    path_rows = []
    steps = 96
    for j, path in enumerate(paths):
        lengths = np.sum(abs(np.diff(path, axis=0)), axis=1)
        length = float(sum(lengths))
        ref = transport(finals[reference_n], path, steps)
        # Axis-aligned paths only. A Lipschitz constant 2pi R for the pulled
        # coefficient yields this midpoint piecewise-constant transport budget.
        one_quadrature_budget = 2*np.pi*radius*float(sum(lengths**2))/(4*steps)
        for n in (1, 2, 3, 4, 6):
            u = transport(finals[n], path, steps)
            finer = transport(finals[n], path, 2*steps)
            error = float(np.linalg.norm(u-ref))
            quadrature_change = float(np.linalg.norm(u-finer))
            allowance = length*(error_bound(n)+error_bound(reference_n))+2*one_quadrature_budget
            assert error <= allowance
            assert quadrature_change <= 1.5*one_quadrature_budget
            path_rows.append({'path': j, 'cutoff': n, 'coordinate_length': length,
                              'SU2_operator_error_to_N8': error,
                              'normalized_trace_error_to_N8': float(abs(u[0]-ref[0])),
                              'analytic_allowance_including_quadrature': allowance,
                              'quadrature_doubling_change': quadrature_change})
    result['transport'] = {
        'path_comparisons': len(path_rows), 'steps_per_segment': steps,
        'max_operator_difference': max(r['SU2_operator_error_to_N8'] for r in path_rows),
        'max_quadrature_doubling_change': max(r['quadrature_doubling_change'] for r in path_rows),
        'comparisons': path_rows,
        'qualification': 'Computed from numerical ODE endpoints; no rigorous time-error '
                         'certificate is claimed. For unit quaternions, Euclidean quaternion '
                         'difference equals the SU(2) matrix operator difference.'}
    root = Path(__file__).resolve().parents[1]
    path = root/'data/nonabelian_yang_mills_local_audit.json'
    path.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({'status': result['status'], 'output': str(path),
                      'rational_checks': result['exact_rational_checks'],
                      'homogeneous_error': result['homogeneous_nonlinear_witness']['exact_solution_max_error'],
                      'common_time': tmax, 'cutoff_errors': [r['sampled_max_Ws_difference_to_N8'] for r in rows],
                      'path_checks': len(path_rows)}, indent=2))


if __name__ == '__main__':
    run()
