#!/usr/bin/env python3
"""A sharp spectral-edge obstruction and a polynomial interaction taper.

Checks exact finite-sphere density response, flat bubble cusps, and the
revised Gaussian curvature coefficient. This is not full microscopic
locality or a finite-eight-species Einstein derivation.
"""
from functools import lru_cache
import hashlib
import json
from pathlib import Path

import numpy as np
from numpy.polynomial.legendre import legvander
from scipy.integrate import quad
from scipy.optimize import brentq
from scipy.special import roots_legendre
import sympy as sy

from proper_resolution_induction_audit import coefficient, complete_action, spectrum


@lru_cache(maxsize=64)
def unit_quadrature(order):
    x, w = roots_legendre(order)
    return (x+1)/2, w/2


def bubble_step(left, right, c, tapered, shift=0.):
    x, wx = spectrum(left, False, dtype=float)
    y, wy = spectrum(right, False, dtype=float)
    den = x[:, None]+y[None, :]+c
    amplitude = 1/den
    if tapered:
        r = (1-x[:, None])**2*(1-y[None, :])**2
        amplitude = r/(den+shift*r)
    normalization = 16*np.pi**2*left**2*right**2
    edge = left*np.sum(wy*amplitude[-1]**2)/normalization
    bulk = np.sum(np.arange(1, left)[:, None]*wy[None, :]*
                  np.diff(amplitude, axis=0)**2)/normalization
    zero = np.sum(wx[:, None]*wy[None, :]*amplitude**2)/normalization
    return zero, edge, bulk


def symbolic_checks():
    u, v, c, s, t = sy.symbols('u v c s t', positive=True)
    phi = sy.log(1+s*(1-u)**2*(1-v)**2/(u+v+c))
    assert phi.subs(u, 1) == 0
    assert sy.diff(phi, u).subs(u, 1) == 0
    # Single-sphere quadrature boundary functional.
    heat = sy.exp(-t*u)
    boundary = (heat.subs(u, 0)-heat.subs(u, 1))/3-sy.diff(heat, u).subs(u, 1)/6
    assert sy.simplify(boundary-(sy.Rational(1, 3)+(t/6-sy.Rational(1, 3))*sy.exp(-t))) == 0
    weighted = (1-u)**2*heat
    assert (weighted.subs(u, 0)-weighted.subs(u, 1))/3-sy.diff(weighted, u).subs(u, 1)/6 == sy.Rational(1, 3)
    for size in [2, 3, 5]:
        a = sy.symbols('a:'+str(size), real=True)
        left = sum((2*l+1)*a[l]**2 for l in range(size))-2*sum((l+1)*a[l]*a[l+1] for l in range(size-1))
        right = size*a[-1]**2+sum((l+1)*(a[l+1]-a[l])**2 for l in range(size-1))
        assert sy.expand(left-right) == 0
    return dict(exact_edge_bulk_identity=True, quadrature_boundary_functional=True,
                tapered_heat_boundary_coefficient='1/3', tapered_log_upper_endpoint_and_derivative_zero=True)


def finite_kernel_checks():
    rows = []
    for left, right in [(2, 3), (4, 5), (8, 6)]:
        x, wx = spectrum(left, False, dtype=float)
        y, wy = spectrum(right, False, dtype=float)
        z1, w1 = roots_legendre(2*left)
        z2, w2 = roots_legendre(2*right)
        p1, p2 = legvander(z1, left-1), legvander(z2, right-1)
        for tapered in [False, True]:
            a = 1/(x[:, None]+y[None, :]+.1)
            if tapered:
                a *= (1-x[:, None])**2*(1-y[None, :])**2
            kernel = p1 @ (wx[:, None]*wy[None, :]*a) @ p2.T/(16*np.pi**2*left**2*right**2)
            density = 4*np.pi**2*left**2*right**2*w1[:, None]*w2[None, :]*kernel**2
            direct_zero = np.sum(density)
            direct_step = np.sum((1-z1[:, None])*density)
            zero, edge, bulk = bubble_step(left, right, .1, tapered)
            assert abs(direct_zero-zero) < 2e-14
            assert abs(direct_step-edge-bulk) < 2e-14
            rows.append(dict(matrix_sizes=[left, right], tapered=tapered,
                             independently_integrated_zero=float(direct_zero),
                             independently_integrated_harmonic_step=float(direct_step),
                             exact_edge=float(edge), exact_bulk=float(bulk),
                             absolute_step_error=float(abs(direct_step-edge-bulk))))
    return dict(cases=rows, scope='Exact-degree Legendre cubature independently checks the finite density covariance eigenvalues and the positive edge/bulk decomposition.')


@lru_cache(maxsize=32)
def tapered_flat_coefficients(c, order=160):
    u, w = unit_quadrature(order)
    x, y = u[:, None], u[None, :]
    weights = w[:, None]*w[None, :]
    den = x+y+c
    h = (1-x)**2*(1-y)**2/den
    hu = -(1-x)*(1-y)**2*(2/den+(1-x)/den**2)
    zero = np.sum(weights*h*h)/(16*np.pi**2)
    gradient = np.sum(weights*x*hu*hu)/(16*np.pi**2)
    return float(zero), float(gradient)


def finite_gradient_checks():
    rows = []
    for c in [.01, .1, 1.]:
        _, target = tapered_flat_coefficients(c)
        edge_target = 1/(16*np.pi**2*(1+c)*(2+c))
        for left in [8, 32, 128, 512]:
            right = 3*left//2
            p_squared = 2/left**2
            for tapered in [False, True]:
                zero, edge, bulk = bubble_step(left, right, c, tapered)
                gradient = (edge+bulk)/p_squared
                if tapered:
                    dc = 2/c+1/c**2
                    uniform_bound = (dc*dc+1/c**2)/(32*np.pi**2)
                    assert gradient <= uniform_bound
                    assert edge <= 1/(16*np.pi**2*c*c*left**5)
                    if left == 512:
                        assert abs(gradient/target-1) < .0003
                else:
                    lower = left/(32*np.pi**2*(2+c)**2)
                    assert gradient >= lower
                    if left == 512:
                        assert abs(left*edge/edge_target-1) < .004
                    uniform_bound = None
                rows.append(dict(mass_ratio=c, matrix_sizes=[left, right], tapered=tapered,
                                 zero_mode=float(zero), edge=float(edge), bulk=float(bulk),
                                 effective_gradient=float(gradient),
                                 tapered_limiting_gradient=target if tapered else None,
                                 tapered_uniform_upper_bound=uniform_bound,
                                 untapered_diverging_lower_bound=lower if not tapered else None))
    return dict(cases=rows, scope='The unfiltered first-harmonic gradient coefficient has an all-size linearly diverging lower bound. The taper gives an all-size uniform upper bound and a finite limiting coefficient.')


def lens_states(shift, order):
    u, w = unit_quadrature(order)
    theta, wt = u*np.pi/2, w*np.pi/2
    radius_max = np.sqrt(1-shift**2*np.sin(theta)**2/4)-shift*np.cos(theta)/2
    radius = radius_max[:, None]*u[None, :]
    weight = 4*wt[:, None]*w[None, :]*radius*radius_max[:, None]
    dot = shift*radius*np.cos(theta)[:, None]
    square = radius*radius
    taper_pair = ((1-square-shift**2/4)**2-dot*dot)**2
    return square.ravel(), dot.ravel(), weight.ravel(), taper_pair.ravel()


def flat_bubble(p, c, tapered, direction, order=40):
    shifts = [p, 0.] if direction == 'axis' else [p/np.sqrt(2), p/np.sqrt(2)]
    a, da, wa, fa = lens_states(shifts[0], order)
    b, db, wb, fb = lens_states(shifts[1], order)
    value = 0.
    for start in range(0, len(a), 128):
        sl = slice(start, start+128)
        center = a[sl, None]+b[None, :]+c+p*p/4
        plus = da[sl, None]+db[None, :]
        minus = da[sl, None]-db[None, :]
        integrand = .5/(center*center-plus*plus)+.5/(center*center-minus*minus)
        if tapered:
            integrand *= fa[sl, None]*fb[None, :]
        value += np.sum(wa[sl, None]*wb[None, :]*integrand)
    return float(value/(2*np.pi)**4)


def independent_sharp_axis(p, c):
    # Integrate the second disk analytically, independently of four-dimensional cubature.
    u, w = unit_quadrature(160)
    theta, wt = u*np.pi/2, w*np.pi/2
    radius_max = np.sqrt(1-p*p*np.sin(theta)**2/4)-p*np.cos(theta)/2
    radius = radius_max[:, None]*u[None, :]
    center = radius*radius+c+p*p/4
    dot = p*radius*np.cos(theta)[:, None]
    radial_integral = (np.arctanh(dot/center)-np.arctanh(dot/(center+1)))/dot
    return float(np.sum(4*wt[:, None]*w[None, :]*radius*radius_max[:, None]*radial_integral)*np.pi/(2*np.pi)**4)


def flat_response_checks():
    c, rows = .1, []
    sharp_zero = np.log((c+1)**2/(c*(c+2)))/(16*np.pi**2)
    cusp = 1/(8*np.pi**3*(c+1)*(c+2))
    taper_zero, beta = tapered_flat_coefficients(c)
    for tapered in [False, True]:
        for direction in ['axis', 'diagonal']:
            values = []
            for p in [.04, .02, .01, .005]:
                actual = flat_bubble(p, c, tapered, direction)
                zero = taper_zero if tapered else sharp_zero
                quotient = (zero-actual)/(p*p if tapered else p)
                values.append(quotient)
                if direction == 'axis' and not tapered:
                    independent = independent_sharp_axis(p, c)
                    assert abs(actual-independent) < 3e-12
                if p == .005 and tapered:
                    assert abs(quotient-beta) < 1e-6
                rows.append(dict(tapered=tapered, direction=direction, momentum=p,
                                 bubble=float(actual), response_quotient=float(quotient),
                                 predicted_limit=float(beta if tapered else cusp*(1 if direction == 'axis' else np.sqrt(2)))))
            if not tapered:
                extrapolated = 2*values[-1]-values[-2]
                target = cusp*(1 if direction == 'axis' else np.sqrt(2))
                assert abs(extrapolated-target) < 1e-7
    return dict(cases=rows, sharp_axis_cusp=cusp, sharp_diagonal_cusp=np.sqrt(2)*cusp,
                tapered_isotropic_gradient=beta,
                scope='Centered disk-intersection integrals test the nonanalytic sharp response and its anisotropy. With the taper the leading quadratic coefficient agrees across directions; no tensor/graviton inference follows.')


@lru_cache(maxsize=64)
def filtered_limit(c, coupling, order=160):
    u, w = unit_quadrature(order)
    x, y = u[:, None], u[None, :]
    weights = w[:, None]*w[None, :]
    r = (1-x)**2*(1-y)**2
    den = x+y+c
    gamma = coupling/(16*np.pi**2)
    a0 = lambda s: np.sum(weights*r/(den+s*r))
    s = brentq(lambda s: s-gamma*a0(s), 0, np.sqrt(gamma), xtol=1e-14)
    volume = .5*np.sum(weights*np.log1p(s*r/den))-s*s/(4*gamma)
    boundary, _ = quad(lambda v: np.log1p(s*(1-v)**2/(v+c)), 0, 1, epsabs=1e-12)
    curvature = -coefficient(c)/2+boundary/6
    return float(s), float(volume), float(curvature)


@lru_cache(maxsize=128)
def filtered_finite(left, right, c, coupling):
    x, wx = spectrum(left, False)
    y, wy = spectrum(right, False)
    den = x[:, None]+y[None, :]+c
    r = (1-x[:, None])**2*(1-y[None, :])**2
    weights = wx[:, None]*wy[None, :]
    product = left**2*right**2
    gamma = coupling/(16*np.pi**2)
    s = brentq(lambda s: s-gamma*float(np.sum(weights*r/(den+s*r)))/product,
               0, np.sqrt(gamma), xtol=1e-14)
    increase = np.sum(weights*np.log1p(s*r/den))/2-product*s*s/(4*gamma)
    value = complete_action(left, right, c)/8+increase
    return float(s), float(value)


def filtered_geometry_checks():
    rows, c = [], .1
    for coupling in [1., 100., 1000.]:
        star, volume, curvature = filtered_limit(c, coupling)
        assert curvature < 0
        for left in [16, 32, 64, 128]:
            right = 3*left//2
            s, actual = filtered_finite(left, right, c, coupling)
            product, total = left**2*right**2, left**2+right**2
            remainder = actual-product*volume-total*curvature
            error_bound_q8 = product*s*s/(2*(coupling/(16*np.pi**2))*8)
            assert error_bound_q8 <= product/16*(1+1e-12)
            if left == 128:
                assert abs(remainder) < .5
            rows.append(dict(coupling=coupling, matrix_sizes=[left, right], reference_shift=s,
                             limiting_reference_shift=star, gaussian_action_per_species=actual,
                             volume_term=float(product*volume), curvature_term=float(total*curvature),
                             gaussian_remainder=float(remainder), full_q8_action_upper_error=float(error_bound_q8)))
    return dict(cases=rows,
                scope='The revised interaction preserves the exact finite-species enclosure with a momentum-dependent Gaussian self-energy. Its homogeneous Gaussian curvature expansion is recomputed, not inherited from the constant-mass model.')


def filtered_reference_gradient_checks():
    rows, c = [], .1
    dc = 2/c+1/c**2
    upper = (dc*dc+1/c**2)/(32*np.pi**2)
    for coupling in [1., 100., 1000.]:
        for left in [8, 32, 128]:
            right = 3*left//2
            shift, _ = filtered_finite(left, right, c, coupling)
            _, edge, bulk = bubble_step(left, right, c, True, shift)
            gradient = (edge+bulk)*left**2/2
            assert gradient <= upper
            assert edge <= 1/(16*np.pi**2*c*c*left**5)
            rows.append(dict(coupling=coupling, matrix_sizes=[left, right], reference_shift=shift,
                             effective_gradient=float(gradient), uniform_all_shift_upper_bound=float(upper),
                             edge=float(edge), bulk=float(bulk)))
    return dict(cases=rows, scope='The same first-harmonic bound holds for the tapered self-consistent Gaussian covariance at every nonnegative reference shift. It is not a bound on all exact interacting correlation functions.')


def strong_coupling_check():
    c, rows = .1, []
    critical, shifts = [], []
    for order in [80, 160]:
        u, w = unit_quadrature(order)
        r = (1-u[:, None])**2*(1-u[None, :])**2
        den = u[:, None]+u[None, :]+c
        def curvature_at_shift(s):
            return -coefficient(c)/2+quad(lambda v: np.log1p(s*(1-v)**2/(v+c)), 0, 1, epsabs=2e-12)[0]/6
        shift = brentq(curvature_at_shift, 0, 100, xtol=1e-11)
        a0 = np.sum(w[:, None]*w[None, :]*r/(den+shift*r))
        coupling = 16*np.pi**2*shift/a0
        critical.append(coupling)
        shifts.append(shift)
    assert abs(critical[0]/critical[1]-1) < 1e-10
    for coupling in [critical[1]/2, 2*critical[1]]:
        shift, volume, curvature = filtered_limit(c, coupling)
        rows.append(dict(coupling=float(coupling), reference_shift=shift, curvature_coefficient=curvature))
    assert rows[0]['curvature_coefficient'] < 0 < rows[1]['curvature_coefficient']
    return dict(cases=rows, bare_mass_ratio=c, critical_reference_shift=float(shifts[-1]),
                critical_gaussian_curvature_coupling=float(critical[1]),
                independent_quadrature_relative_error=float(abs(critical[0]/critical[1]-1)),
                scope='The tapered Gaussian curvature coefficient changes sign at sufficiently strong coupling. This is not a proved phase transition or a fixed-eight-species gravitational threshold.')


def main():
    root = Path(__file__).resolve().parents[1]
    report = dict(symbolic=symbolic_checks(), finite_kernel=finite_kernel_checks(),
                  finite_gradient=finite_gradient_checks(), flat_response=flat_response_checks(),
                  filtered_geometry=filtered_geometry_checks(),
                  filtered_reference_gradients=filtered_reference_gradient_checks(),
                  strong_coupling=strong_coupling_check())
    sources = ['SPECTRAL_EDGE_LOCALITY.md', 'scripts/spectral_edge_locality_audit.py',
               'NONPERTURBATIVE_MATTER_BOUND.md', 'scripts/nonperturbative_matter_bound_audit.py',
               'LOCAL_SYMBOL_INTERACTION.md', 'scripts/local_symbol_interaction_audit.py',
               'PROPER_RESOLUTION_INDUCTION.md', 'scripts/proper_resolution_induction_audit.py',
               'GEOMETRIC_SPECTRAL_INDUCTION.md', 'GRAVITY_FROM_CLOCK_CONSTRAINTS.md']
    report['source_sha256'] = {p: hashlib.sha256((root/p).read_bytes()).hexdigest() for p in sources}
    report['scope'] = ('The exact unfiltered collective density response has a spectral-edge term that forces its '
                       'first-harmonic gradient coefficient to grow with radius. Its flat counterpart has an anisotropic '
                       '|p| cusp. A new polynomial taper in the interaction removes that obstruction in this channel, '
                       'preserves the free determinant, and retains a finite-species nonlinear enclosure. The recomputed '
                       'homogeneous Gaussian curvature coefficient has the Einstein sign in a finite coupling range but '
                       'changes sign at sufficiently strong coupling. Full observable locality, fixed-eight-species '
                       'Einstein dynamics, microscopic refinement, Lorentzian gravity, Standard Model and TOE remain unproved. '
                       'No new Lean theorem.')
    target = root/'data/spectral_edge_locality_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    counts = {k: len(v['cases']) for k, v in report.items() if isinstance(v, dict) and 'cases' in v}
    print(json.dumps(dict(report=str(target), checks=counts, source_references=len(sources), scope=report['scope']), indent=2))


if __name__ == '__main__':
    main()
