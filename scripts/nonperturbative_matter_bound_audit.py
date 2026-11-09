#!/usr/bin/env python3
"""Exact finite-species enclosure and homogeneous curvature at finite coupling.

The full field integral is enclosed analytically. Large-grid numbers below
evaluate the optimized Gaussian expression, not the full interacting
partition function. Exact radial integrals test finite-species cases.
"""
from functools import lru_cache
import hashlib
import json
from pathlib import Path

import numpy as np
from scipy.integrate import quad
from scipy.optimize import brentq
from scipy.special import gammaln
import sympy as sy

from local_symbol_interaction_audit import resolvent_coefficients, scalar_resolvent_trace
from proper_resolution_induction_audit import coefficient, complete_action, spectrum


def log_ratio(c):
    return np.log1p(1/(c+1))


def a0_derivative(c):
    return np.log(c*(c+2)/(c+1)**2)


def integrated_a0(c):
    return .5*(c*c*np.log(c)-2*(c+1)**2*np.log1p(c)+(c+2)**2*np.log(c+2))


def integrated_a1(c):
    return -resolvent_coefficients(c)[0]/3-log_ratio(c)/6


@lru_cache(maxsize=128)
def limiting_coefficients(c0, coupling):
    gamma = coupling/(16*np.pi**2)
    if coupling == 0:
        mass, volume = c0, 0.
    else:
        mass = brentq(lambda c: c-c0-gamma*resolvent_coefficients(c)[0],
                      c0, c0+gamma/c0, xtol=1e-14)
        volume = .5*(integrated_a0(mass)-integrated_a0(c0))-(mass-c0)**2/(4*gamma)
    a0, _ = resolvent_coefficients(c0)
    astar, _ = resolvent_coefficients(mass)
    curvature = -a0/12-log_ratio(c0)/6-astar/6-log_ratio(mass)/12
    return mass, volume, curvature


@lru_cache(maxsize=256)
def finite_mass(left, right, c0, coupling):
    if coupling == 0:
        return c0
    gamma, product = coupling/(16*np.pi**2), left**2*right**2
    return brentq(lambda c: c-c0-gamma*float(scalar_resolvent_trace(left, right, c))/product,
                  c0, c0+gamma/c0, xtol=1e-14)


@lru_cache(maxsize=256)
def gaussian_action(left, right, c0, coupling):
    """Action per species, optimized in a constant Gaussian mass."""
    mass = finite_mass(left, right, c0, coupling)
    if coupling == 0:
        return complete_action(left, right, c0)/8
    gamma, product = coupling/(16*np.pi**2), left**2*right**2
    a, wa = spectrum(left, False)
    b, wb = spectrum(right, False)
    scalar_increase = np.sum(wa[:, None]*wb[None, :]*
                             np.log1p((mass-c0)/(a[:, None]+b[None, :]+c0)),
                             dtype=np.longdouble)/2
    return float(complete_action(left, right, c0)/8+scalar_increase-
                 product*(mass-c0)**2/(4*gamma))


def species_error(left, right, c0, coupling, species):
    if coupling == 0:
        return 0.
    mass = finite_mass(left, right, c0, coupling)
    gamma, product = coupling/(16*np.pi**2), left**2*right**2
    error = product*(mass-c0)**2/(2*gamma*species)
    assert error <= product/(2*species)*(1+1e-12)
    return error


def symbolic_checks():
    s, sigma, g, q = sy.symbols('s sigma g q', positive=True)
    original = q*sigma*s/2-q*g*s*s/4
    rewritten = q*sigma*sigma/(4*g)-q*g*(s-sigma/g)**2/4
    assert sy.expand(original-rewritten) == 0
    c, d = sy.symbols('c d', positive=True)
    a0 = c*sy.log(c)-2*(c+1)*sy.log(c+1)+(c+2)*sy.log(c+2)
    a1 = sy.log((c+1)**2/(c*(c+2)))/3+(1/(c+1)-1/(c+2))/6
    l = sy.log((c+2)/(c+1))
    primitive0 = (c*c*sy.log(c)-2*(c+1)**2*sy.log(c+1)+(c+2)**2*sy.log(c+2))/2
    primitive1 = -a0/3-l/6
    assert sy.simplify(sy.diff(primitive0, c)-a0) == 0
    assert sy.simplify(sy.expand_log(sy.diff(primitive1, c)-a1, force=True)) == 0
    j = (a0+l)/2
    first_form = -j/2+(primitive1.subs(c, d)-primitive1)/2
    negative_form = -a0/12-l/6-a0.subs(c, d)/6-l.subs(c, d)/12
    assert sy.simplify(first_form-negative_form) == 0
    return dict(exact_square_completion=True, resolvent_antiderivatives=True,
                manifestly_negative_curvature_identity=True,
                scope='The reweighting identity, Gaussian fourth moments and Jensen yield an exact finite-species inequality. Symbolic identities do not replace the analytical uniform-limit argument.')


def coefficient_checks():
    rows = []
    for c0 in [.01, .1, 1.]:
        for coupling in [0., .1, 1., 10., 100., 1000.]:
            mass, volume, curvature = limiting_coefficients(c0, coupling)
            gamma = coupling/(16*np.pi**2)
            assert curvature < 0 and mass >= c0
            assert abs(mass-c0-gamma*resolvent_coefficients(mass)[0]) < 2e-13
            if coupling:
                int0, err0 = quad(lambda c: resolvent_coefficients(c)[0], c0, mass,
                                  epsabs=2e-12, epsrel=2e-12)
                int1, err1 = quad(lambda c: resolvent_coefficients(c)[1], c0, mass,
                                  epsabs=2e-12, epsrel=2e-12)
                independent_volume = .5*int0-(mass-c0)**2/(4*gamma)
                independent_curvature = -coefficient(c0)/2+.5*int1
                assert abs(volume-independent_volume) < 2e-12
                assert abs(curvature-independent_curvature) < 2e-12
                assert volume > 0
            else:
                independent_volume, independent_curvature = 0., -coefficient(c0)/2
                err0, err1 = 0., 0.
            saturation = -resolvent_coefficients(c0)[0]/12-log_ratio(c0)/6
            assert -coefficient(c0)/2-2e-14 <= curvature < saturation
            rows.append(dict(bare_mass_ratio=c0, coupling=coupling,
                             limiting_gaussian_mass_ratio=float(mass), volume_coefficient=float(volume),
                             curvature_coefficient=float(curvature), strong_coupling_curvature_limit=float(saturation),
                             independent_volume=float(independent_volume), independent_curvature=float(independent_curvature),
                             quadrature_errors=[float(err0), float(err1)],
                             inverse_newton_per_species_over_cutoff_squared=float(-curvature/(2*np.pi))))
    return dict(cases=rows, scope='The optimized Gaussian curvature coefficient has the Einstein sign for all positive coupling by the negative-sum identity; numerical samples check the formula, not the all-coupling theorem.')


def gap_and_geometry_checks():
    rows = []
    c0 = .1
    for coupling in [1., 10., 100., 1000.]:
        gamma = coupling/(16*np.pi**2)
        star, h, curvature = limiting_coefficients(c0, coupling)
        predicted_mass_shift = gamma*resolvent_coefficients(star)[1]/(1-gamma*a0_derivative(star))
        for scale in [16, 32, 64, 128]:
            left, right = scale, 3*scale//2
            product, total = left**2*right**2, left**2+right**2
            mass = finite_mass(left, right, c0, coupling)
            trace = float(scalar_resolvent_trace(left, right, mass))
            gap_error = abs(mass-c0-gamma*trace/product)
            assert gap_error < 2e-12
            assert (mass-c0)**2 <= gamma*(1+1e-12)
            actual = gaussian_action(left, right, c0, coupling)
            residual = actual-product*h-total*curvature
            scaled_mass_shift = (mass-star)*product/total
            scaled_mass_error = abs(scaled_mass_shift-predicted_mass_shift)*scale**2
            assert scaled_mass_error < .032
            if scale == 128:
                assert abs(scaled_mass_shift-predicted_mass_shift) < 2e-6
                assert abs(residual) < .4
            rows.append(dict(coupling=coupling, matrix_sizes=[left, right],
                             gaussian_mass_ratio=float(mass), gap_residual=float(gap_error),
                             mass_shift_times_product_over_sum=float(scaled_mass_shift),
                             predicted_scaled_mass_shift=float(predicted_mass_shift),
                             mass_shift_error_times_size_squared=float(scaled_mass_error),
                             complete_gaussian_action_per_species=float(actual),
                             leading_volume_term=float(product*h), leading_curvature_term=float(total*curvature),
                             gaussian_action_remainder=float(residual)))
    return dict(cases=rows,
                scope='These are complete finite spectral sums for the variational Gaussian action. The full nonlinear partition function is enclosed separately; it has not been integrated at these large dimensions.')


def exact_radial_interaction(c0, coupling, species):
    # Exact N1=N2=1 reduction to a Gamma(q/2,1) radial variable.
    volume = 16*np.pi**2
    shape = species/2
    a = coupling/(species*volume*c0*c0)
    h = shape-1
    mode = 2*h/(1+np.sqrt(1+8*a*h))
    log_at_mode = h*np.log(mode)-mode-a*mode**2-gammaln(shape)
    def scaled_density(t):
        if t == 0:
            return 0.
        return np.exp(h*np.log(t)-mode*(t-1)-a*mode**2*(t*t-1))
    left, e1 = quad(scaled_density, 0, 1, epsabs=2e-13, epsrel=2e-13)
    right, e2 = quad(scaled_density, 1, np.inf, epsabs=2e-13, epsrel=2e-13)
    log_partition = log_at_mode+np.log(mode)+np.log(left+right)
    return -log_partition/species, (e1+e2)/(species*(left+right))


def radial_enclosure_checks():
    rows, c0 = [], .1
    for coupling in [1., 10., 100.]:
        gamma = coupling/(16*np.pi**2)
        mass = finite_mass(1, 1, c0, coupling)
        gaussian_interaction = .5*np.log(mass/c0)-(mass-c0)**2/(4*gamma)
        for species in [8, 32, 128, 512]:
            exact, integration_error = exact_radial_interaction(c0, coupling, species)
            error = exact-gaussian_interaction
            bound = species_error(1, 1, c0, coupling, species)
            assert 0 <= error <= bound
            assert bound <= 1/(2*species)
            rows.append(dict(coupling=coupling, species=species,
                             exact_interaction_action_per_species=float(exact),
                             optimized_gaussian_interaction=float(gaussian_interaction),
                             exact_gap=float(error), analytical_gap_bound=float(bound),
                             uniform_all_coupling_gap_bound=1/(2*species),
                             quadrature_error=float(integration_error)))
    return dict(cases=rows,
                scope='Independent nonperturbative integrals for the exact constant-mode member verify the enclosure at finite species. The general proof is square completion and Jensen, not extrapolation from these cases.')


def finite_eight_species_shapes():
    rows, c0, species = [], .1, 8
    for coupling in [.1, 1., 10., 100.]:
        for scale in [12, 24, 48, 96]:
            base, deformed = (scale, scale), (4*scale//3, 3*scale//4)
            assert base[0]*base[1] == deformed[0]*deformed[1]
            center = gaussian_action(*base, c0, coupling)
            shifted = gaussian_action(*deformed, c0, coupling)
            center_error = species_error(*base, c0, coupling, species)
            shifted_error = species_error(*deformed, c0, coupling, species)
            difference = shifted-center
            lower, upper = difference-center_error, difference+shifted_error
            rows.append(dict(coupling=coupling, species=species, base_sizes=list(base),
                             deformed_sizes=list(deformed), gaussian_shape_difference=float(difference),
                             full_interacting_difference_lower=float(lower),
                             full_interacting_difference_upper=float(upper),
                             enclosure_has_negative_sign=bool(upper < 0)))
    assert any(r['enclosure_has_negative_sign'] for r in rows)
    assert any(not r['enclosure_has_negative_sign'] for r in rows)
    return dict(cases=rows,
                scope='Analytical finite-species enclosures, printed with floating-point endpoints. Some finite-size shape signs follow; many bounds include both signs. These are not direct evaluations of the eight-species partition function or a finite-species Einstein limit.')


def joint_limit_shapes():
    rows, c0 = [], .1
    for coupling in [1., 10., 100.]:
        star, volume, curvature = limiting_coefficients(c0, coupling)
        for k in [2, 3, 4, 5]:
            scale, h = (k*(k+1))**2, np.log1p(1/k)
            species = 8*k**16
            pairs = [(scale, scale), (k*(k+1)**3, k**3*(k+1)), ((k+1)**4, k**4)]
            assert all(a*b == scale**2 for a, b in pairs)
            values = [(gaussian_action(a, b, c0, coupling)-scale**4*volume)/scale**2 for a, b in pairs]
            target = 2*curvature*np.cosh(2*h*np.arange(3))
            def stencil(v):
                return np.array([2*(v[1]-v[0])/h**2, (2*v[2]-8*v[1]+6*v[0])/h**4])
            actual, expected = stencil(values), stencil(target)
            # Each full-action correction after normalization is in [0,L].
            # Positive and negative stencil weights each sum to 2 or 8.
            second_bound = scale**2/(species*h*h)
            fourth_bound = 4*scale**2/(species*h**4)
            if k == 5:
                assert abs(actual[0]-expected[0]) < 5e-6
                assert abs(actual[1]-expected[1]) < .0002
                assert fourth_bound < .003
            rows.append(dict(coupling=coupling, k=k, scale=scale, shape_step=float(h), species=species,
                             gaussian_second_difference=float(actual[0]), gaussian_fourth_difference=float(actual[1]),
                             finite_einstein_second=float(expected[0]), finite_einstein_fourth=float(expected[1]),
                             gaussian_second_error=float(actual[0]-expected[0]),
                             gaussian_fourth_error=float(actual[1]-expected[1]),
                             full_action_second_deviation_bound=float(second_bound),
                             full_action_fourth_deviation_bound=float(fourth_bound)))
    return dict(cases=rows,
                scope='The full finite-coupling partition function lies within the analytical stencil errors shown around the Gaussian values. The joint limit requires growing species, and is not a proof for fixed eight-species matter.')


def main():
    root = Path(__file__).resolve().parents[1]
    report = dict(symbolic=symbolic_checks(), coefficients=coefficient_checks(),
                  finite_gap_and_geometry=gap_and_geometry_checks(),
                  exact_radial_enclosures=radial_enclosure_checks(),
                  eight_species_shapes=finite_eight_species_shapes(),
                  joint_geometry_species_limit=joint_limit_shapes())
    sources = ['NONPERTURBATIVE_MATTER_BOUND.md', 'scripts/nonperturbative_matter_bound_audit.py',
               'LOCAL_SYMBOL_INTERACTION.md', 'scripts/local_symbol_interaction_audit.py',
               'PROPER_RESOLUTION_INDUCTION.md', 'scripts/proper_resolution_induction_audit.py',
               'GEOMETRIC_SPECTRAL_INDUCTION.md', 'BALANCED_MATTER_INDUCTION.md',
               'CONTINUUM_EINSTEIN_BRIDGE.md', 'GRAVITY_FROM_CLOCK_CONSTRAINTS.md']
    report['source_sha256'] = {p: hashlib.sha256((root/p).read_bytes()).hexdigest() for p in sources}
    report['scope'] = ('An exact square-completion identity encloses the full positive-quartic action per species '
                       'between an optimized Gaussian action and that value plus P/(2q), for every finite species '
                       'count and nonnegative coupling. The Gaussian homogeneous curvature coefficient is negative '
                       'at every coupling. A joint large-geometry/large-species limit controls full second and fourth '
                       'shape differences at finite coupling. Fixed eight-species curvature recovery is not proved. '
                       'Nor are fixed physical Newton coupling in the large-species limit, independent local sites, '
                       'microscopic refinement, arbitrary-metric dynamics, Lorentzian gravity, Standard Model or TOE. '
                       'No new Lean theorem is asserted.')
    target = root/'data/nonperturbative_matter_bound_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    counts = {k: len(v['cases']) for k, v in report.items() if isinstance(v, dict) and 'cases' in v}
    print(json.dumps(dict(report=str(target), checks=counts, source_references=len(sources), scope=report['scope']), indent=2))


if __name__ == '__main__':
    main()
