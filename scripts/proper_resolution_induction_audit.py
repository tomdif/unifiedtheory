#!/usr/bin/env python3
"""Complete massive determinants under a supplied proper-resolution rule.

The analytical all-size estimate is in PROPER_RESOLUTION_INDUCTION.md.
These independent numerical and symbolic checks are not a Lean proof or
a construction of microscopic refinement dynamics.
"""
from functools import lru_cache
import hashlib
import json
from pathlib import Path

import numpy as np
from scipy.integrate import quad
from scipy.special import exp1
import sympy as sy

from geometric_spectral_induction_audit import spin_matrices


def spectrum(size, fermion, dtype=np.longdouble):
    if fermion:
        n = np.arange(1, size+1, dtype=dtype)
        weights = 4*n
        weights[-1] = 2*size
        return n*n/size**2, weights
    ell = np.arange(size, dtype=dtype)
    return ell*(ell+1)/size**2, 2*ell+1


@lru_cache(maxsize=512)
def complete_action(left, right, mass_ratio):
    """8 real scalar half-logdets minus 2 sphere-spinor half-logdets.

    Sums include every eigenvalue, including the massive scalar zero modes.
    Weights compress the exact spectra; no huge dense matrix is constructed.
    """
    values = []
    for fermion in [False, True]:
        a, wa = spectrum(left, fermion)
        b, wb = spectrum(right, fermion)
        total = a[:, None]+b[None, :]+np.longdouble(mass_ratio)
        values.append(np.sum(wa[:, None]*wb[None, :]*np.log(total),
                             dtype=np.longdouble)/2)
    return float(8*values[0]-2*values[1])


def coefficient(c):
    return .5*(c*np.log(c)-(2*c+3)*np.log1p(c)+(c+3)*np.log(c+2))


def heat_limit(t):
    if t == 0:
        return 1., 0., 0., 0.
    decay = np.exp(-t)
    integral = -np.expm1(-t)/t
    boundary = 2*(np.expm1(-t)-2*t*decay)
    boson = t*integral/4-boundary/24
    fermion = boundary/12
    difference = (-np.expm1(-t)+t*decay)/2
    return integral, boson, fermion, difference


def symbolic_checks():
    x, t, c = sy.symbols('x t c', positive=True)
    f = 2*x*sy.exp(-t*x*x)
    fourth = (120*t**2*x-160*t**3*x**3+32*t**4*x**5)*sy.exp(-t*x*x)
    assert sy.simplify(sy.diff(f, x, 4)-fourth) == 0
    integral = (1-sy.exp(-t))/t
    boundary = sy.diff(f, x).subs(x, 1)-sy.diff(f, x).subs(x, 0)
    difference = (1+(t-1)*sy.exp(-t))/2
    assert sy.simplify(t*integral/4-boundary/8-difference) == 0
    split_integrand = ((1-sy.exp(-t))**2/t**2+
                       (sy.exp(-t)-sy.exp(-2*t))/t)/2
    assert sy.simplify(integral*difference/t-split_integrand) == 0
    j = (c*sy.log(c)-(2*c+3)*sy.log(c+1)+(c+3)*sy.log(c+2))/2
    assert sy.limit(j, c, 0, dir='+') == 3*sy.log(2)/2
    # Constants in the explicit analytical bound, including the exponential.
    assert np.exp(.25)*(172+1/32+1/16) < 224
    assert .5+448+100352 < 102000
    assert 896 < 900
    return dict(fourth_derivative_identity=True, quadrature_boundary_identity=True,
                frullani_integrand_split=True, positive_mass_coefficient=str(j),
                coefficient_massless_limit='3*log(2)/2',
                single_sphere_remainder_constant=224,
                product_remainder_constant='102000+900*rho**2',
                precision_bits=int(np.finfo(np.longdouble).nmant),
                scope='Symbolic identities and arithmetic checks support the written all-size proof. The massless coefficient limit does not extend the positive-mass remainder theorem to zero mass.')


def coefficient_checks():
    rows = []
    for c in [.01, .1, 1., 4.]:
        def integrand(t):
            i, _, _, d = heat_limit(t)
            return np.exp(-c*t)*i*d/t if t else 1.
        actual, error = quad(integrand, 0, np.inf, epsabs=2e-12, epsrel=2e-12)
        target = coefficient(c)
        assert actual > 0
        assert abs(actual-target) < 3e-12
        rows.append(dict(mass_squared_over_cutoff_squared=c, closed_coefficient=target,
                         independent_integral=float(actual), quadrature_error=float(error),
                         absolute_error=float(abs(actual-target)),
                         inverse_newton_over_cutoff_squared=float(2*target/np.pi)))
    return dict(cases=rows)


def heat_values(size, t):
    boson, wb = spectrum(size, False)
    fermion, wf = spectrum(size, True)
    return float(np.sum(wb*np.exp(-t*boson))), float(np.sum(wf*np.exp(-t*fermion))/2)


def quadrature_checks():
    rows = []
    for size in [8, 16, 32, 64]:
        for t in [.02, .2, 1., 4., 16., size**2/2, float(size**2)]:
            boson, fermion = heat_values(size, t)
            midpoint = (np.arange(size)+.5)/size
            endpoints = np.arange(size+1)/size
            mid = np.mean(2*midpoint*np.exp(-t*midpoint**2))
            edge = 2*endpoints*np.exp(-t*endpoints**2)
            trap = (edge[0]/2+edge[-1]/2+np.sum(edge[1:-1]))/size
            identity_error = max(abs(boson-size**2*np.exp(t/(4*size**2))*mid),
                                 abs(fermion-size**2*trap))
            assert identity_error < 3e-12
            integral, b, f, _ = heat_limit(t)
            rb, rf = boson-size**2*integral-b, fermion-size**2*integral-f
            bound = 224*min(t*t, t)/size**2
            assert max(abs(rb), abs(rf)) <= bound+3e-12
            rows.append(dict(size=size, scaled_time=t, identity_error=float(identity_error),
                             boson_remainder=float(rb), fermion_remainder=float(rf),
                             analytical_bound=float(bound)))
    return dict(cases=rows,
                scope='Sampled checks of exact quadrature identities and the bound. The written Euler-Maclaurin estimate, not these samples, proves uniformity in size and time.')


def proper_time_action(left, right, c):
    spectra = [[spectrum(n, False, dtype=float), spectrum(n, True, dtype=float)]
               for n in [left, right]]
    def factor(index, t):
        (b, wb), (f, wf) = spectra[index]
        boson = np.sum(wb*np.exp(-t*b))
        fermion = np.sum(wf*np.exp(-t*f))/2
        if t < 1:
            # Exact count cancellation avoids subtracting two near-N^2 sums.
            difference = np.sum(wb*np.expm1(-t*b))-np.sum(wf*np.expm1(-t*f))/2
        else:
            difference = boson-fermion
        return boson, fermion, difference
    def integrand(t):
        if t == 0:
            return -4*(left**2+right**2)
        b1, f1, d1 = factor(0, t)
        b2, _, d2 = factor(1, t)
        return -4*np.exp(-c*t)*(d1*b2+f1*d2)/t
    # Split to resolve both the ultraviolet endpoint and the massive tail.
    first, e1 = quad(integrand, 0, 1, epsabs=1e-8, epsrel=1e-11)
    second, e2 = quad(integrand, 1, np.inf, epsabs=1e-8, epsrel=1e-11, limit=200)
    return first+second, e1+e2


def complete_integral_checks():
    rows = []
    for left, right, c in [(2, 3, .01), (8, 5, .1), (16, 24, .1), (32, 20, 1.)]:
        actual = complete_action(left, right, c)
        independent, error = proper_time_action(left, right, c)
        assert abs(actual-independent) < 2e-7
        assert 8*left**2*right**2 == 2*(2*left**2)*(2*right**2)
        rows.append(dict(matrix_sizes=[left, right], mass_ratio=c, complete_logdet=actual,
                         complete_proper_time_integral=float(independent),
                         absolute_error=float(abs(actual-independent)), quadrature_error=float(error),
                         balanced_field_count=8*left**2*right**2))
    return dict(cases=rows, scope='Every massive mode is included in both independent calculations; no spectral window or zero-mode subtraction is used.')


def remainder_bound(c, rho):
    constant = 102000+900*rho**2
    return 4*constant*(.5+exp1(c))+8*rho**2/(np.e*c*c)+4*(1+rho*rho)


def scaling_checks():
    rows = []
    for c in [.01, .1, 1.]:
        for aspect in [(1., 1.), (.8, 1.3), (.5, 1.5)]:
            for scale in [16, 32, 64, 128, 256]:
                left, right = [int(round(scale*x)) for x in aspect]
                value = complete_action(left, right, c)
                leading = -4*coefficient(c)*(left**2+right**2)
                remainder = value-leading
                bound = remainder_bound(c, max(left, right)/min(left, right))
                assert abs(remainder) < bound
                if scale == 256:
                    assert abs(remainder/leading) < 2e-4
                rows.append(dict(mass_ratio=c, nominal_scale=scale, matrix_sizes=[left, right],
                                 complete_action=value, einstein_term=float(leading),
                                 absolute_remainder=float(remainder),
                                 remainder_relative_to_leading=float(abs(remainder/leading)),
                                 analytical_remainder_bound=float(bound)))
    return dict(cases=rows)


def radius_variations():
    rows = []
    for c in [.01, .1, 1.]:
        j = coefficient(c)
        for scale in [32, 64, 128, 256]:
            point = np.array([round(.8*scale), round(1.3*scale)], dtype=int)
            step = round(np.sqrt(scale))
            center = complete_action(int(point[0]), int(point[1]), c)
            for direction in [(1, 0), (0, 1), (1, 1)]:
                vector = np.array(direction)
                plus, minus = point+step*vector, point-step*vector
                fp = complete_action(int(plus[0]), int(plus[1]), c)
                fm = complete_action(int(minus[0]), int(minus[1]), c)
                first, second = (fp-fm)/(2*step), (fp-2*center+fm)/step**2
                target_first = float(-8*j*np.dot(point, vector))
                target_second = float(-8*j*np.dot(vector, vector))
                if scale == 256:
                    assert abs(first/target_first-1) < 1e-4
                    assert abs(second/target_second-1) < 1e-4
                rows.append(dict(mass_ratio=c, matrix_sizes=point.tolist(), step=step,
                                 direction=list(direction), first_difference=first,
                                 einstein_first_difference=target_first,
                                 second_difference=second, einstein_second_difference=target_second))
    return dict(cases=rows,
                scope='Collective integer refinement steps grow while their relative size shrinks. These are not derivatives of an action with its two representation sizes held fixed.')


def constant_volume_profiles():
    rows = []
    c = .1
    for scale in [24, 96, 384]:
        for numerator, denominator in [(1, 1), (4, 3), (3, 2), (2, 1)]:
            assert scale*numerator % denominator == 0
            assert scale*denominator % numerator == 0
            left, right = scale*numerator//denominator, scale*denominator//numerator
            assert left*right == scale**2
            u = np.log(numerator/denominator)
            value = complete_action(left, right, c)/scale**2
            target = -8*coefficient(c)*np.cosh(2*u)
            if scale == 384:
                assert abs(value-target) < 1e-4
            rows.append(dict(scale=scale, shape=float(u), matrix_sizes=[left, right],
                             scalar_dimension=scale**4, fermion_dimension=8*scale**4,
                             normalized_action=float(value), einstein_shape_function=float(target),
                             absolute_error=float(abs(value-target))))
    return dict(cases=rows, scope='Each scale has exactly fixed total volume and field dimension across shapes; the factor representation sizes are redistributed.')


def constant_volume_fourth_variations():
    c, rows = .1, []
    for k in [2, 3, 4, 5]:
        scale = (k*(k+1))**2
        step = np.log1p(1/k)
        pairs = [(scale, scale), (k*(k+1)**3, k**3*(k+1)), ((k+1)**4, k**4)]
        assert all(left*right == scale**2 for left, right in pairs)
        values = np.array([complete_action(left, right, c)/scale**2 for left, right in pairs])
        targets = -8*coefficient(c)*np.cosh(2*step*np.arange(3))
        def stencil(v):
            return np.array([2*(v[1]-v[0])/step**2,
                             (2*v[2]-8*v[1]+6*v[0])/step**4])
        actual, expected = stencil(values), stencil(targets)
        if k == 5:
            assert abs(actual[0]-expected[0]) < 5e-5
            assert abs(actual[1]-expected[1]) < .002
        rows.append(dict(k=k, scale=scale, shape_step=float(step), matrix_sizes=[list(p) for p in pairs],
                         scalar_dimension=scale**4, fermion_dimension=8*scale**4,
                         second_difference=float(actual[0]), fourth_difference=float(actual[1]),
                         finite_einstein_second_difference=float(expected[0]),
                         finite_einstein_fourth_difference=float(expected[1]),
                         second_difference_error=float(actual[0]-expected[0]),
                         fourth_difference_error=float(actual[1]-expected[1]),
                         fourth_over_second=float(actual[1]/actual[0])))
    return dict(cases=rows, limiting_second=-32*coefficient(c), limiting_fourth=-128*coefficient(c),
                scope='Uniform action errors divided by K^2 h^4 vanish on this exact integer stencil. This justifies finite shape variations through fourth order, but supplies no local microscopic transition law.')


def fixed_size_jets(size, c):
    jets = []
    for fermion in [False, True]:
        a, w = spectrum(size, fermion)
        left, right = a[:, None], a[None, :]
        lam = left+right+c
        weights = w[:, None]*w[None, :]
        p, q = 2*(right-left), 4*(left+right)
        jets.append(np.array([
            np.sum(weights*np.log(lam))/2,
            np.sum(weights*(q/lam-p*p/lam**2))/2,
            np.sum(weights*(4*q/lam-16*p*p/lam**2-3*q*q/lam**2+
                            12*q*p*p/lam**3-6*p**4/lam**4))/2], dtype=np.longdouble))
    return np.array((8*jets[0]-2*jets[1])/size**2, dtype=float)


def fixed_size_control():
    u = sy.Symbol('u', real=True)
    c = sy.Rational(1, 10)
    a, b = sy.exp(-2*u), sy.exp(2*u)
    f = c*sy.log(c)-(c+a)*sy.log(c+a)-(c+b)*sy.log(c+b)+(c+a+b)*sy.log(c+a+b)
    w = -2*((1/a+1/b)*f+(a/b)*sy.log((c+a+b)/(c+a))+(b/a)*sy.log((c+a+b)/(c+b)))
    targets = np.array([float(sy.diff(w, u, order).subs(u, 0).evalf(25)) for order in [0, 2, 4]])
    assert abs(targets[0]+8*coefficient(float(c))) < 2e-13
    mismatch = targets[2]-4*targets[1]
    assert mismatch > 25
    rows = []
    for size in [32, 128, 512]:
        actual = fixed_size_jets(size, float(c))
        scaled_error = abs(actual-targets)*size**2
        # The independently differentiated limiting function has O(N^-2)
        # finite-size errors here, with a much larger fourth-jet constant.
        assert np.all(scaled_error < np.array([2.1, 16., 130.]))
        if size == 512:
            assert max(abs(actual-targets)) < .0005
        rows.append(dict(size=size, normalized_action=float(actual[0]),
                         normalized_second_derivative=float(actual[1]),
                         normalized_fourth_derivative=float(actual[2]),
                         errors_times_size_squared=scaled_error.tolist(),
                         einstein_identity_mismatch=float(actual[2]-4*actual[1])))
    return dict(cases=rows, mass_ratio=float(c), limiting_jets=targets.tolist(),
                limiting_einstein_identity_mismatch=float(mismatch),
                scope='The same common positive mass does not fix the leading shape mismatch if both matrix sizes are held fixed. This isolates the effect of the supplied proper-resolution rule.')


def coordinate_localization_checks():
    rows = []
    cutoff = 2.
    for size in [2, 4, 8, 16]:
        j, radius = (size-1)/2, size/cutoff
        coordinates = [radius*a/np.sqrt(j*(j+1)) for a in spin_matrices(size-1)]
        x, y, z = coordinates
        commutator = (x @ y-y @ x)[-1, -1]
        expected_commutator = 1j*2*radius**2/(size+1)
        variances = [float(((a @ a)[-1, -1]-a[-1, -1]**2).real) for a in [x, y]]
        expected_variance = radius**2/(size+1)
        assert abs(commutator-expected_commutator) < 1e-12
        assert max(abs(v-expected_variance) for v in variances) < 1e-12
        assert np.max(abs(x @ x+y @ y+z @ z-radius**2*np.eye(size))) < 1e-12
        rows.append(dict(size=size, radius=radius, proper_spectral_cutoff=cutoff,
                         commutator_imaginary_part=float(commutator.imag),
                         transverse_position_variance=variances[0],
                         expected_position_variance=expected_variance,
                         localization_length=float(np.sqrt(expected_variance)),
                         variance_over_radius_squared=expected_variance/radius**2))
    return dict(cases=rows,
                scope='With fixed spectral cutoff, coherent-state position variance grows as radius/cutoff. This obstructs treating spectral density alone as a proof of uniform matrix-product locality; it is not a no-go for every observable algebra or a failure of the free determinant theorem.')


def main():
    root = Path(__file__).resolve().parents[1]
    report = dict(symbolic=symbolic_checks(), coefficient=coefficient_checks(),
                  quadrature=quadrature_checks(), complete_integral=complete_integral_checks(),
                  scaling=scaling_checks(), radius_variations=radius_variations(),
                  constant_volume_profiles=constant_volume_profiles(),
                  constant_volume_fourth_variations=constant_volume_fourth_variations(),
                  fixed_size_control=fixed_size_control(),
                  coordinate_localization=coordinate_localization_checks())
    sources = ['PROPER_RESOLUTION_INDUCTION.md', 'scripts/proper_resolution_induction_audit.py',
               'BALANCED_MATTER_INDUCTION.md', 'scripts/balanced_matter_induction_audit.py',
               'GEOMETRIC_SPECTRAL_INDUCTION.md', 'scripts/geometric_spectral_induction_audit.py',
               'CONTINUUM_EINSTEIN_BRIDGE.md',
               'EINSTEIN_MODEL_DECISION.md', 'GRAVITY_FROM_CLOCK_CONSTRAINTS.md']
    report['source_sha256'] = {p: hashlib.sha256((root/p).read_bytes()).hexdigest() for p in sources}
    report['scope'] = ('At fixed positive common mass and proper cutoff, the complete balanced determinant '
                       'has the Einstein leading curvature functional with a uniformly bounded remainder '
                       'on bounded-aspect product spheres. Exact-volume refinement stencils recover its '
                       'second and fourth shape variations. The resolution rule, matrix geometry, matter '
                       'balance, common mass and measure are supplied. No arbitrary-metric action, local '
                       'refinement Hamiltonian, Lorentzian gravitational phase, Einstein constraint algebra, '
                       'Standard Model recovery or TOE is proved; there is no new Lean theorem.')
    target = root/'data/proper_resolution_induction_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    counts = {key: len(value['cases']) for key, value in report.items()
              if isinstance(value, dict) and 'cases' in value}
    print(json.dumps(dict(report=str(target), checks=counts, source_references=len(sources),
                          scope=report['scope']), indent=2))


if __name__ == '__main__':
    main()
