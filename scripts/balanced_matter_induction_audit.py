#!/usr/bin/env python3
"""Boson/fermion cancellation in the complete curved matrix determinant.

The conventional first-order Grassmann determinant is used. The chosen
Euclidean matrix family is not an established Lorentzian microscopic phase.
"""
import hashlib
import json
from pathlib import Path

import numpy as np
from scipy.integrate import quad, quad_vec
from scipy.linalg import lu_factor
import sympy as sy

from geometric_spectral_induction_audit import spin_matrices


PAULI = [np.array([[0, 1], [1, 0]], dtype=complex),
         np.array([[0, -1j], [1j, 0]], dtype=complex),
         np.diag([1., -1.]).astype(complex)]


def sphere_dirac(size):
    identity = np.eye(size)
    angular = [np.kron(identity, j)-np.kron(j.T, identity)
               for j in spin_matrices(size-1)]
    return np.eye(2*size*size)+sum(np.kron(sigma, ell) for sigma, ell in zip(PAULI, angular))


def sphere_dirac_eigenvalues(size):
    values = []
    for ell in range(size):
        values.extend([ell+1]*(2*ell+2))
        values.extend([-ell]*(2*ell))
    return np.array(values, dtype=float)


def matrix_fermion_checks():
    rows = []
    for left, right in [(2, 2), (2, 3), (3, 3)]:
        a, b = sphere_dirac(left), sphere_dirac(right)
        ea, eb = sphere_dirac_eigenvalues(left), sphere_dirac_eigenvalues(right)
        assert np.max(abs(np.linalg.eigvalsh(a)-np.sort(ea))) < 2e-13
        assert np.max(abs(np.linalg.eigvalsh(b)-np.sort(eb))) < 2e-13
        r1, r2 = .9, 1.2
        first = np.kron(a/r1, np.eye(len(b)))
        second = np.kron(np.eye(len(a)), b/r2)
        q = np.kron(PAULI[0], first)+np.kron(PAULI[1], second)
        chirality = np.kron(PAULI[2], np.eye(len(first)))
        target_square = np.kron(np.eye(2), first @ first+second @ second)
        square_error = np.max(abs(q @ q-target_square))
        assert square_error < 2e-12
        assert np.max(abs(q @ chirality+chirality @ q)) < 2e-13
        expected_positive = np.sqrt((ea[:, None]/r1)**2+(eb[None, :]/r2)**2).ravel()
        expected = np.sort(np.concatenate([-expected_positive, expected_positive]))
        spectrum = np.linalg.eigvalsh(q)
        spectral_error = np.max(abs(spectrum-expected))
        assert spectral_error < 2e-12
        mass = .4
        # Recover the determinant from pivoted complex LU independently of
        # the Hermitian eigensolver used for the spectral reference.
        factor, pivots = lu_factor(mass*np.eye(len(q))+1j*q)
        diagonal = np.diag(factor)
        assert np.min(abs(diagonal)) > 0
        phase = (-1)**np.sum(pivots != np.arange(len(pivots)))*np.prod(diagonal/abs(diagonal))
        logdet = np.sum(np.log(abs(diagonal)))
        expected_logdet = .5*np.sum(np.log(mass*mass+spectrum*spectrum))
        assert abs(phase-1) < 2e-12
        assert abs(logdet-expected_logdet) < 2e-10
        rows.append(dict(matrix_sizes=[left, right], fermion_dimension=len(q),
                         matching_eight_scalar_dimension=8*left**2*right**2,
                         square_error=float(square_error), spectral_error=float(spectral_error),
                         determinant_phase_error=float(abs(phase-1)),
                         determinant_log_error=float(abs(logdet-expected_logdet))))
    return dict(cases=rows,
                scope='An explicit Hermitian first-order matrix operator with paired spectrum gives a positive det(m+iQ). This checks the finite fermionic determinant and its statistics sign, not reflection positivity or a Lorentzian physical fermion phase.')


def single_spectrum(size, fermion, nonminimal=0.):
    if fermion:
        n = np.arange(1, size+1, dtype=float)
        weight = 4*n
        weight[-1] = 2*size
        return n*n, weight
    ell = np.arange(size, dtype=float)
    return ell*(ell+1)+2*nonminimal, 2*ell+1


def determinant_jets(size, shape, fermion, nonminimal=0.):
    eigen, weight = single_spectrum(size, fermion, nonminimal)
    a = eigen[:, None]*np.exp(-2*shape)
    b = eigen[None, :]*np.exp(2*shape)
    total = a+b
    weights = weight[:, None]*weight[None, :]
    keep = total > 0
    lam, w = total[keep], weights[keep]
    product_ratio = (a*b)[keep]/lam**2
    # Derivatives 0, 1, 2 and 4 of one-half log determinant.
    return np.array([.5*np.sum(w*np.log(lam)),
                     np.sum(w*((b-a)[keep]/lam)),
                     np.sum(w*8*product_ratio),
                     np.sum(w*(128*product_ratio-768*product_ratio**2))])


def balanced_jets(size, shape, nonminimal=0.):
    return 8*determinant_jets(size, shape, False, nonminimal)-2*determinant_jets(size, shape, True)


def symbolic_limit():
    u, xi, z = sy.symbols('u xi z', real=True)
    s = 2*sy.cosh(2*u)
    f = s*sy.log(s)-4*u*sy.sinh(2*u)
    w = 4*sy.log(s)+(8*xi-4)*s*f
    # Exact quadrature boundary term controlling the first surviving scale.
    x = sy.Symbol('x', real=True)
    integrand = 2*x*sy.exp(-z*x*x)
    boundary = sy.diff(integrand, x).subs(x, 1)-sy.diff(integrand, x).subs(x, 0)
    i = (1-sy.exp(-z))/z
    d = (1+(z-1)*sy.exp(-z))/2
    assert sy.simplify(z*i/4-boundary/8-d) == 0
    target_second = 80-128*sy.log(2)
    target_fourth = 1408-2048*sy.log(2)
    assert sy.expand_log(sy.diff(w, u, 2).subs({u: 0, xi: 0}), force=True).expand() == target_second
    assert sy.expand_log(sy.diff(w, u, 4).subs({u: 0, xi: 0}), force=True).expand() == target_fourth
    mismatch = 1088-1536*sy.log(2)
    assert sy.expand(target_fourth-4*target_second-mismatch) == 0
    functions = [sy.lambdify((u, xi), sy.diff(w, u, n), 'numpy') for n in [0, 1, 2, 4]]
    return functions, dict(second_at_round=float(target_second), fourth_at_round=float(target_fourth),
                           einstein_fourth_order_mismatch=float(mismatch),
                           exact_boundary_correction=True,
                           scope='The leading normalized full action is W_xi(u), up to a shape-independent constant. W_0 fails the Einstein fourth-versus-second derivative identity.')


def heat_values(size, scaled_time):
    boson, wb = single_spectrum(size, False)
    fermion, wf = single_spectrum(size, True)
    return np.sum(wb*np.exp(-scaled_time*boson/size**2)), np.sum(wf*np.exp(-scaled_time*fermion/size**2))


def quadrature_and_supertrace_checks():
    rows = []
    for size in [8, 16, 32, 64]:
        for z in [.2, 1., 4., 16.]:
            mid = (np.arange(size)+.5)/size
            edge = np.arange(size+1)/size
            fmid = 2*mid*np.exp(-z*mid*mid)
            fedge = 2*edge*np.exp(-z*edge*edge)
            midpoint = np.mean(fmid)
            trapezoid = (fedge[0]/2+fedge[-1]/2+np.sum(fedge[1:-1]))/size
            boson, fermion = heat_values(size, z)
            assert abs(boson-size**2*np.exp(z/(4*size**2))*midpoint) < 2e-12
            assert abs(fermion/2-size**2*trapezoid) < 2e-12
            d = (1+(z-1)*np.exp(-z))/2
            difference = boson-fermion/2
            if size == 64:
                assert abs(difference-d) < .003
            rows.append(dict(size=size, scaled_time=z, finite_difference=float(difference),
                             boundary_limit=float(d), error=float(abs(difference-d))))
    for size in [2, 3, 8, 32, 128]:
        _, wb = single_spectrum(size, False)
        _, wf = single_spectrum(size, True)
        assert 8*np.sum(wb)**2 == 2*np.sum(wf)**2 == 8*size**4
    return dict(cases=rows, exact_dimension_balance=True,
                scope='Exact midpoint/trapezoid representations expose cancellation of the fourth-power cutoff term. Equality of counts is a chosen field-content condition, not a proved supersymmetry.')


def limit_integral_checks(functions):
    rows = []
    for shape in [0., .2, .4, .7]:
        a, b = np.exp(-2*shape), np.exp(2*shape)
        def i(z):
            return -np.expm1(-z)/z if z else 1.
        def d(z):
            return (-np.expm1(-z)+z*np.exp(-z))/2
        value, error = quad(lambda t: -4*(d(a*t)*i(b*t)+i(a*t)*d(b*t))/t,
                            0, np.inf, epsabs=1e-10, epsrel=1e-11, limit=200)
        target = float(functions[0](shape, 0.))
        assert abs(value-target) < 2e-9
        rows.append(dict(shape=shape, integral=float(value), closed_expression=target,
                         absolute_error=float(abs(value-target)), quadrature_error=float(error)))
    return dict(cases=rows)


def full_determinant_limit_checks(functions):
    rows = []
    for xi in [0., .1, .25]:
        sizes = [16, 32, 64, 128, 256, 512] if xi == 0 else [32, 128, 512]
        for size in sizes:
            base = balanced_jets(size, 0., xi)/size**2
            for shape in ([0., .2, .4] if xi == 0 else [0., .2]):
                actual = balanced_jets(size, shape, xi)/size**2
                target = np.array([f(shape, xi) for f in functions], dtype=float)
                action_difference = actual[0]-base[0]
                target_difference = target[0]-float(functions[0](0., xi))
                if size == 512:
                    assert abs(action_difference-target_difference) < 7e-5
                    assert abs(actual[2]-target[2]) < .005
                    assert abs(actual[3]-target[3]) < .06
                if xi == 0:
                    assert actual[2] < 0
                rows.append(dict(size=size, nonminimal_scalar_coupling=xi, shape=shape,
                                 normalized_shape_action_difference=float(action_difference),
                                 limiting_shape_action_difference=float(target_difference),
                                 normalized_second_derivative=float(actual[2]),
                                 limiting_second_derivative=float(target[2]),
                                 normalized_fourth_derivative=float(actual[3]),
                                 limiting_fourth_derivative=float(target[3])))
    return dict(cases=rows,
                scope='Complete boson-plus-fermion determinants; no intermediate spectral window is discarded. The leading term is quadratic in matrix size and negative near the round background, but its shape function is not the Einstein functional.')


def independent_variations():
    rows = []
    for size in [12, 24]:
        for shape in [0., .2]:
            base = balanced_jets(size, shape)
            errors = []
            for epsilon in [.004, .002]:
                plus, minus = balanced_jets(size, shape+epsilon), balanced_jets(size, shape-epsilon)
                second = (plus[0]-2*base[0]+minus[0])/epsilon**2
                fourth = (plus[2]-2*base[2]+minus[2])/epsilon**2
                errors.append([float(abs(second-base[2])/abs(base[2])),
                               float(abs(fourth-base[3])/max(1., abs(base[3])))])
            assert max(errors[-1]) < .001
            rows.append(dict(size=size, shape=shape, relative_second_and_fourth_errors=errors))
    return dict(cases=rows)


def continuum_window_checks():
    # Untruncated sphere coefficients through first curvature order:
    # H_B(t)=1/t+1/3+..., H_F(t)=2/t-1/3+... .
    s, a, b = sy.symbols('s a b', positive=True)
    supertrace = sy.expand(8*(a/s+sy.Rational(1, 3))*(b/s+sy.Rational(1, 3))-
                          2*(2*a/s-sy.Rational(1, 3))*(2*b/s-sy.Rational(1, 3)))
    assert supertrace.coeff(s, -2) == 0
    assert supertrace.coeff(s, -1) == 4*(a+b)
    rows = []
    for cutoff in [4., 8., 16., 32.]:
        size = int(12*cutoff)
        def jets(t, fermion):
            eigen, weight = single_spectrum(size, fermion)
            x = t*eigen
            e = weight*np.exp(-x)
            return np.array([np.sum(e), np.sum(2*x*e), np.sum((4*x*x-4*x)*e)])
        def shape_hessian(log_s):
            proper = np.exp(log_s)
            bos, fer = jets(proper, False), jets(proper, True)
            kb = 2*bos[0]*bos[2]-2*bos[1]**2
            kf = 2*fer[0]*fer[2]-2*fer[1]**2
            return -.5*(8*kb-2*kf)
        actual, error = quad(shape_hessian, np.log(cutoff**-2), np.log((cutoff/2)**-2),
                             epsabs=1e-8, epsrel=2e-10)
        target = -12*cutoff**2
        if cutoff == 32:
            assert abs(actual/target-1) < .002
        rows.append(dict(upper_cutoff=cutoff, lower_cutoff=cutoff/2,
                         full_matter_window_hessian=float(actual), einstein_hessian=target,
                         quadrature_error=float(error)))
    return dict(cases=rows, leading_volume_coefficient=0, curvature_coefficient_in_supertrace='2R',
                scope='The balanced geometric window retains an Einstein term with positive Newton coefficient. Its proper-time regularization is distinct from the complete fixed-size determinant.')


def main():
    root = Path(__file__).resolve().parents[1]
    functions, symbolic = symbolic_limit()
    report = dict(symbolic=symbolic, fermion_matrices=matrix_fermion_checks(),
                  quadrature=quadrature_and_supertrace_checks(), limit_integral=limit_integral_checks(functions),
                  complete_determinants=full_determinant_limit_checks(functions),
                  independent_variations=independent_variations(), continuum_window=continuum_window_checks())
    sources = ['BALANCED_MATTER_INDUCTION.md', 'scripts/balanced_matter_induction_audit.py',
               'GEOMETRIC_SPECTRAL_INDUCTION.md', 'scripts/geometric_spectral_induction_audit.py',
               'MICROSCOPIC_METRIC_WARD.md', 'ISOTROPIC_TENSOR_REGULATOR.md',
               'EINSTEIN_MODEL_DECISION.md', 'GRAVITY_FROM_CLOCK_CONSTRAINTS.md']
    report['source_sha256'] = {p: hashlib.sha256((root/p).read_bytes()).hexdigest() for p in sources}
    report['scope'] = ('A specified first-order fermion determinant and eight real scalars cancel the leading '
                       'fourth-power cutoff shape term in the complete curved matrix model. The derived quadratic-order '
                       'shape response has the Einstein sign near the round background but fails its higher-variation '
                       'identity. A constant scalar curvature coupling cannot repair the whole shape function. '
                       'No supersymmetry, Lorentzian microscopic phase, gravitational constraint algebra, or TOE is proved.')
    target = root/'data/balanced_matter_induction_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(dict(report=str(target), fermion_matrix_cases=3, quadrature_cases=16,
                          full_determinant_cases=len(report['complete_determinants']['cases']),
                          limit_integral_cases=4, independent_variation_cases=4,
                          continuum_window_cases=4, source_references=8, scope=report['scope']), indent=2))


if __name__ == '__main__':
    main()
