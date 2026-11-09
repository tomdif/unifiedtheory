#!/usr/bin/env python3
"""Global finite-horizon convergence audit against an exact smooth SU(2) flow.

The reference is a fixed nonconstant gauge transform of the homogeneous
nonlinear solution. Errors are against that solution, not a higher-cutoff ODE.
No interval-certified time integration or practical cutoff-threshold claim.
"""
from __future__ import annotations

import json
import math
import random
from fractions import Fraction as Q
from pathlib import Path

import numpy as np
from scipy.integrate import solve_ivp
from scipy.special import jv

import nonabelian_yang_mills_energy_audit as energy
import nonabelian_yang_mills_local_audit as local

A0 = .7
EPS1, EPS2 = .28, .19
REFERENCE_CUTOFF = 18
TMAX = .25


def amplitude(t):
    return A0/math.sqrt(1+8*A0*A0*t)


def exact_coeff(n, t):
    k = local.modes(n)
    weights = jv(k, 2*EPS1)[:, None]*jv(k, 2*EPS2)[None, :]
    even = (k[:, None]+k[None, :]) % 2 == 0
    cosine = weights*even
    sine = -1j*weights*(~even)
    a = np.zeros((2*n+1, 2*n+1, 2, 3), complex)
    a[:, :, 0, 0] = amplitude(t)*cosine
    a[:, :, 0, 1] = amplitude(t)*sine
    a[:, :, 1, 0] = -amplitude(t)*sine
    a[:, :, 1, 1] = amplitude(t)*cosine
    if n >= 1:
        a[n-1, n, 0, 2] = a[n+1, n, 0, 2] = -np.pi*EPS1
        a[n, n-1, 1, 2] = a[n, n+1, 1, 2] = -np.pi*EPS2
    return a


def exact_field(points, t):
    x, y = points[:, 0], points[:, 1]
    theta = EPS1*np.sin(2*np.pi*x)+EPS2*np.sin(2*np.pi*y)
    c, s, a = np.cos(2*theta), np.sin(2*theta), amplitude(t)
    out = np.zeros((len(points), 2, 3))
    out[:, 0] = np.stack((a*c, a*s, -2*np.pi*EPS1*np.cos(2*np.pi*x)), axis=-1)
    out[:, 1] = np.stack((-a*s, a*c, -2*np.pi*EPS2*np.cos(2*np.pi*y)), axis=-1)
    return out


def reference_tail(n):
    def full(u):
        return math.exp(u*u)*(2*math.exp(u)-1)
    def tail(u):
        return 2*math.exp(u*u)*u**(n+1)/math.factorial(n+1)/(1-u/(n+2))
    return 2*A0*(tail(EPS1)*full(EPS2)+full(EPS1)*tail(EPS2))


def exact_checks():
    rng = random.Random(902612)
    count = 0
    def dot(u, v):
        return sum(x*y for x, y in zip(u, v))
    def add(*vs):
        return tuple(sum(x) for x in zip(*vs))
    def mul(t, v):
        return tuple(t*x for x in v)
    for _ in range(32):
        f, l, c = [tuple(Q(rng.randint(-7, 7), 9) for _ in range(3)) for _ in range(3)]
        lhs = -dot(add(f, l, c), add(l, mul(2, c)))+dot(f, l)
        middle = -dot(l, l)-3*dot(l, c)-2*dot(c, c)-2*dot(f, c)
        completed = -dot(add(l, mul(Q(3, 2), c)), add(l, mul(Q(3, 2), c)))+dot(c, c)/4-2*dot(f, c)
        assert lhs == middle == completed
        assert lhs <= dot(c, c)/4-2*dot(f, c)
        count += 2
    return count


def relative_gradient_checks():
    rng = np.random.default_rng(282419)
    rows = []
    for n in (1, 2, 3):
        v = energy.random_field(n, rng, .08)
        e = energy.random_field(n, rng, .035)
        vgeo, ugeo = energy.geometry(v), energy.geometry(v+e)
        ep = energy.physical(e, len(vgeo['F']))
        l = energy.curvature_variation(vgeo['field'], ep)
        c = 2*np.cross(ep[:, :, 0], ep[:, :, 1])
        lhs = energy.pair(ep, ugeo['G']-vgeo['G'])
        rhs = (-energy.pair(l+1.5*c, l+1.5*c)+.25*energy.pair(c, c)
               -2*energy.pair(vgeo['F'], c))
        error = abs(lhs-rhs)
        assert error < 2e-10
        y = float(np.sum(abs(e)**2))
        r = local.norm_upper(v, 2)
        m = 2*np.pi*r+2*r*r
        bound = 2*m*y+.25*(2*n+1)**2*y*y  # kappa=2 in SU(2).
        assert lhs <= bound+2e-10
        inverse_ratio = float(np.max(np.sqrt(np.sum(ep*ep, axis=(2, 3))))/
                              ((2*n+1)*math.sqrt(y)))
        assert inverse_ratio <= 1+1e-13
        rows.append({'cutoff': n, 'relative_gradient_identity_error': error,
                     'one_sided_pairing': lhs, 'one_sided_upper_bound': bound,
                     'inverse_estimate_ratio': inverse_ratio})
    return rows


def reference_checks():
    rng = np.random.default_rng(135)
    points = rng.uniform(0, 1, (29, 2))
    worst = 0.
    for t in (0., .125, .25, 2.):
        approximation = local.evaluate(exact_coeff(REFERENCE_CUTOFF, t), points)
        worst = max(worst, float(np.max(abs(approximation-exact_field(points, t)))))
    assert worst < 4e-14
    # Resolve the explicit reference far beyond the tested finite cutoffs.
    a = exact_coeff(12, .17)
    geo = energy.geometry(a)
    fexact = np.zeros_like(geo['F'])
    fexact[:, :, 2] = 2*amplitude(.17)**2
    curvature_error = float(np.max(abs(geo['F']-fexact)))
    dt = a.copy()
    dt[:, :, :, 2] = 0
    dt *= -4*amplitude(.17)**2
    equation_error = float(np.max(abs(geo['G']-energy.physical(dt, len(geo['F'])))))
    assert curvature_error < 2e-11
    assert equation_error < 3e-10
    return {'physical_vs_Bessel_max_error': worst,
            'exact_curvature_max_residual': curvature_error,
            'exact_YM_equation_max_residual': equation_error,
            'reference_cutoff': REFERENCE_CUTOFF,
            'reference_tail_upper_formula_float': reference_tail(REFERENCE_CUTOFF)}


def evolve(n, tight=False):
    init = exact_coeff(n, 0.)
    shape = init.shape
    def rhs(_, state):
        field = state[:-1].reshape(shape)
        gradient = energy.project_grid(energy.geometry(field)['G'], n)
        speed = float(np.sum(abs(gradient)**2))
        return np.concatenate((gradient.ravel(), np.array([speed])))
    times = np.linspace(0, TMAX, 9)
    sol = solve_ivp(rhs, (0, TMAX), np.concatenate((init.ravel(), np.zeros(1))),
                    t_eval=times, method='DOP853', rtol=2e-12 if tight else 2e-10,
                    atol=2e-14 if tight else 2e-12,
                    max_step=TMAX/(64 if tight else 32))
    assert sol.success, sol.message
    values = [state[:-1].reshape(shape) for state in sol.y.T]
    rows = []
    initial_energy = energy.geometry(init)['energy']
    for i, (t, value) in enumerate(zip(times, values)):
        ref = exact_coeff(REFERENCE_CUTOFF, t)
        error = local.embed(value, REFERENCE_CUTOFF)-ref
        l2 = float(np.sqrt(np.sum(abs(error)**2)))
        e = value-exact_coeff(n, t)
        geo = energy.geometry(value)
        fref = np.zeros_like(geo['F'])
        fref[:, :, 2] = 2*amplitude(t)**2
        curvature_l2 = math.sqrt(energy.pair(geo['F']-fref, geo['F']-fref))
        exact_energy = 2*amplitude(t)**4
        rows.append({'time': float(t), 'L2_error_to_exact_reference': l2,
                     'L2_error_to_projected_reference': float(np.sqrt(np.sum(abs(e)**2))),
                     'uniform_error_fourier_upper': local.norm_upper(error, 0)+reference_tail(REFERENCE_CUTOFF),
                     'curvature_L2_error': curvature_l2,
                     'energy_error': abs(geo['energy']-exact_energy),
                     'cumulative_dissipation_error': abs(float(sol.y[-1, i].real)-(2*A0**4-exact_energy)),
                     'numerical_energy_balance_error': abs(geo['energy']+float(sol.y[-1, i].real)-initial_energy)})
    assert max(r['numerical_energy_balance_error'] for r in rows) < 2e-8
    return values, {'cutoff': n, 'max_L2_error': max(r['L2_error_to_exact_reference'] for r in rows),
                    'final_L2_error': rows[-1]['L2_error_to_exact_reference'],
                    'max_projected_reference_error': max(r['L2_error_to_projected_reference'] for r in rows),
                    'max_curvature_L2_error': max(r['curvature_L2_error'] for r in rows),
                    'max_energy_error': max(r['energy_error'] for r in rows),
                    'max_cumulative_dissipation_error': max(r['cumulative_dissipation_error'] for r in rows),
                    'rhs_evaluations': sol.nfev, 'samples': rows}


def quaternion_exp(v):
    size = float(np.linalg.norm(v))
    scale = math.sin(size)/size if size else 1.
    return np.array([math.cos(size), *(scale*np.asarray(v))])


def exact_transport(vertices, t):
    u = np.array([1., 0., 0., 0.])
    for x, y in zip(vertices, vertices[1:]):
        delta = y-x
        assert abs(delta[0]*delta[1]) < 1e-15
        u = np.asarray(local.qmul(u, quaternion_exp(amplitude(t)*np.array([delta[0], delta[1], 0.]))))
    def gauge(x):
        theta = EPS1*np.sin(2*np.pi*x[0])+EPS2*np.sin(2*np.pi*x[1])
        return quaternion_exp(np.array([0., 0., theta]))
    start, end = gauge(vertices[0]), gauge(vertices[-1])
    return np.asarray(local.qmul(local.qmul(start, u), end*np.array([1., -1., -1., -1.])))


def numerical_transport(field, vertices, tight=False):
    u = np.array([1., 0., 0., 0.])
    for x, y in zip(vertices, vertices[1:]):
        delta = y-x
        def rhs(s, q):
            value = local.evaluate(field, (x+s*delta)[None, :])[0]
            generator = delta[0]*value[0]+delta[1]*value[1]
            return np.asarray(local.qmul(q, (0., *generator)))
        sol = solve_ivp(rhs, (0, 1), u, method='DOP853',
                        rtol=2e-13 if tight else 2e-11,
                        atol=2e-15 if tight else 2e-13)
        assert sol.success
        u = sol.y[:, -1]
    assert abs(np.dot(u, u)-1) < 2e-10
    return u


def main():
    rational = exact_checks()
    identities = relative_gradient_checks()
    reference = reference_checks()
    comparisons, finals = [], {}
    for n in (1, 2, 3, 4, 6):
        values, result = evolve(n)
        comparisons.append(result)
        finals[n] = values[-1]
    assert all(b['max_L2_error'] < a['max_L2_error'] for a, b in zip(comparisons, comparisons[1:]))
    assert all(b['final_L2_error'] < a['final_L2_error'] for a, b in zip(comparisons, comparisons[1:]))
    tight, _ = evolve(6, tight=True)
    tolerance_error = float(np.sqrt(np.sum(abs(tight[-1]-finals[6])**2)))
    assert tolerance_error < 2e-9
    paths = [np.array([(.13, .17), (.73, .17)]),
             np.array([(.13, .17), (.73, .17), (.73, .77), (.13, .77), (.13, .17)]),
             np.array([(.13, .17), (1.13, .17)])]
    transport_rows = []
    for j, path in enumerate(paths):
        exact = exact_transport(path, TMAX)
        length = float(np.sum(abs(np.diff(path, axis=0))))
        for n in (1, 2, 3, 4, 6):
            value = numerical_transport(finals[n], path)
            error = float(np.linalg.norm(value-exact))
            upper = comparisons[(1, 2, 3, 4, 6).index(n)]['samples'][-1]['uniform_error_fourier_upper']
            assert error <= length*upper+3e-10
            transport_rows.append({'path': j, 'cutoff': n, 'SU2_operator_error': error,
                                   'normalized_trace_error': float(abs(value[0]-exact[0])),
                                   'length_times_computed_field_upper': length*upper})
    transport_tolerance_error = float(np.linalg.norm(
        numerical_transport(finals[6], paths[1])-numerical_transport(finals[6], paths[1], tight=True)))
    report = {'status': 'PASS', 'exact_rational_checks': rational,
              'relative_gradient_checks': identities, 'exact_reference_checks': reference,
              'parameters': {'initial_amplitude': A0, 'gauge_amplitudes': [EPS1, EPS2], 'end_time': TMAX},
              'cutoff_comparisons': comparisons,
              'tightened_N6_endpoint_L2_difference': tolerance_error,
              'transport_comparisons': transport_rows,
              'tightened_path_integration_difference': transport_tolerance_error,
              'qualifications': ['Reference is exact analytic gauge-rotated flow; Bessel tail separately bounded.',
                                 'Maximum sampled errors include t=0; final-time errors are also reported.',
                                 'ODE and transport tolerances are diagnostics, not rigorous enclosures.',
                                 'No assertion that tested cutoffs meet the conservative theorem threshold.',
                                 'No novelty or infinite-time-uniform convergence claim.']}
    out = Path(__file__).resolve().parents[1]/'data/nonabelian_yang_mills_global_audit.json'
    out.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({'status': 'PASS', 'rational_checks': rational,
                      'max_L2_errors': [r['max_L2_error'] for r in comparisons],
                      'final_L2_errors': [r['final_L2_error'] for r in comparisons],
                      'transport_checks': len(transport_rows), 'output': str(out)}, indent=2))


if __name__ == '__main__':
    main()
