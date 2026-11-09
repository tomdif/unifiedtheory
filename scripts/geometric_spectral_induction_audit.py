#!/usr/bin/env python3
"""Curved spin-matrix spectral window versus the complete Gaussian determinant.

Known fuzzy-sphere spectra supply a controlled geometric benchmark, not a
derived spacetime phase of the repository's fixed four-spin Hamiltonian.
"""
import hashlib
import itertools
import json
from pathlib import Path

import numpy as np
from scipy.integrate import quad_vec
import sympy as sy


def comm(a, b):
    return a @ b-b @ a


def spin_matrices(twice_spin):
    j = twice_spin/2
    m = np.arange(-j, j+1)
    raising = np.zeros((len(m), len(m)), dtype=complex)
    for index in range(len(m)-1):
        raising[index+1, index] = np.sqrt((j-m[index])*(j+m[index]+1))
    return [(raising+raising.T)/2, (raising-raising.T)/(2j), np.diag(m)]


def adjoint_laplacian(twice_spin):
    generators = spin_matrices(twice_spin)
    identity = np.eye(twice_spin+1)
    adjoints = [np.kron(identity, j)-np.kron(j.T, identity) for j in generators]
    return sum(a @ a for a in adjoints), generators


def matrix_spectrum_checks():
    rng = np.random.default_rng(95508)
    rows = []
    for left, right in [(1, 1), (1, 2), (2, 2), (2, 3), (3, 3)]:
        a, generators = adjoint_laplacian(left)
        b, _ = adjoint_laplacian(right)
        r1, r2 = .9, 1.3
        matrix = np.kron(a, np.eye(len(b)))/r1**2+np.kron(np.eye(len(a)), b)/r2**2
        actual = np.linalg.eigvalsh(matrix)
        expected = []
        for ell, k in itertools.product(range(left+1), range(right+1)):
            expected.extend([ell*(ell+1)/r1**2+k*(k+1)/r2**2]*((2*ell+1)*(2*k+1)))
        error = np.max(abs(actual-np.sort(expected)))
        assert error < 2e-12 and actual.min() > -2e-13
        assert np.sum(abs(actual) < 1e-11) == 1
        x, y, z = generators
        assert np.max(abs(comm(x, y)-1j*z)) < 2e-14
        shape = x.shape
        phi = rng.normal(size=shape)+1j*rng.normal(size=shape)
        chi = rng.normal(size=shape)+1j*rng.normal(size=shape)
        leibniz = comm(x, phi @ chi)-comm(x, phi) @ chi-phi @ comm(x, chi)
        assert np.max(abs(leibniz)) < 1e-13
        vector = phi.ravel(order='F')
        energy = np.vdot(vector, a @ vector).real
        direct = sum(np.linalg.norm(comm(j, phi))**2 for j in generators)
        assert abs(energy-direct) < 2e-11
        rows.append(dict(twice_spins=[left, right], scalar_matrix_dimension=len(matrix),
                         spectral_error=float(error), zero_modes=1,
                         leibniz_error=float(np.max(abs(leibniz))),
                         quadratic_form_error=float(abs(energy-direct))))
    return dict(cases=rows,
                scope='Dense adjoint-Casimir matrices independently reproduce the product-sphere spectrum. This does not establish a local finite-spin ground phase or a Lorentzian spacetime.')


def symbolic_checks():
    t, x = sy.symbols('t x', positive=True)
    f = (2*x+1)*sy.exp(-t*x*(x+1))
    boundary = sy.Rational(1, 2)
    for k in range(1, 5):
        boundary -= sy.bernoulli(2*k)*sy.diff(f, x, 2*k-1).subs(x, 0)/sy.factorial(2*k)
    expected = sy.Rational(1, 3)+t/15+4*t*t/315
    assert sy.series(boundary-expected, t, 0, 3).removeO() == 0
    aa, bb, m2 = sy.symbols('A B m2', nonnegative=True)
    lam = aa+bb+m2
    hessian = sy.Rational(1, 2)*(4*(aa+bb)/lam-4*(bb-aa)**2/lam**2)
    positive_form = (8*aa*bb+2*m2*(aa+bb))/lam**2
    assert sy.factor(hessian-positive_form) == 0
    r1, r2 = sy.symbols('r1 r2', positive=True)
    curvature = 2/r1**2+2/r2**2
    ricci2 = 2/r1**4+2/r2**4
    riemann2 = 4/r1**4+4/r2**4
    a4 = (5*curvature**2-2*ricci2+2*riemann2)/360
    assert sy.simplify(r1**2*r2**2*a4-(sy.Rational(1, 9)+(r1**2/r2**2+r2**2/r1**2)/15)) == 0
    return dict(euler_maclaurin_boundary_coefficients=str(expected),
                complete_determinant_positive_shape_hessian=str(positive_form),
                product_sphere_curvature_square_identity=True)


def heat_jets(t, maximum, minimum=0):
    ell = np.arange(minimum, maximum+1, dtype=float)
    scaled = t*ell*(ell+1)
    weights = (2*ell+1)*np.exp(-scaled)
    # Derivatives with respect to log radius at fixed proper time.
    return np.array([weights.sum(), (2*scaled*weights).sum(),
                     ((4*scaled**2-4*scaled)*weights).sum()])


def heat_bound(t):
    return 1+1/t+3*np.sqrt(np.pi)/(2*np.sqrt(t))


TAIL_CONSTANTS = np.array([1., 8/np.e, 256/np.e**2+16/np.e])


def tail_checks():
    rows = []
    for t, maximum in itertools.product([.003, .03, .3], [4, 12, 32]):
        reference = max(maximum+2, int(np.ceil(25/np.sqrt(t))))
        tail = heat_jets(t, reference, maximum+1)
        bound = TAIL_CONSTANTS*np.exp(-t*(maximum+1)*(maximum+2)/4)*heat_bound(t/2)
        assert np.all(abs(tail) <= bound+1e-13)
        full = heat_jets(t, reference)
        assert full[0] <= heat_bound(t)+1e-12
        rows.append(dict(dimensionless_time=t, maximum_angular_momentum=maximum,
                         tail_jets=tail.tolist(), analytical_tail_bounds=bound.tolist()))
    return dict(cases=rows,
                scope='Explicit infinite-tail bounds for the trace and first two log-radius derivatives. Numerical tails stop after exponential suppression; the bound is established analytically, not by the finite reference sum.')


def product_shape_jets(s, maximum, radius, shape):
    r1, r2 = radius*np.exp(shape), radius*np.exp(-shape)
    a = heat_jets(s/r1**2, maximum)
    b = heat_jets(s/r2**2, maximum)
    return np.array([a[0]*b[0], a[1]*b[0]-a[0]*b[1],
                     a[2]*b[0]+a[0]*b[2]-2*a[1]*b[1]])


def window_jets(cutoff, infrared, maximum, radius, shape):
    value, error = quad_vec(lambda log_s: -.5*product_shape_jets(np.exp(log_s), maximum, radius, shape),
                            np.log(cutoff**-2), np.log(infrared**-2),
                            epsabs=1e-9, epsrel=2e-12)
    return value, float(error)


def continuum_window_jets(cutoff, infrared, radius, shape):
    fourth = cutoff**4-infrared**4
    second = cutoff**2-infrared**2
    logarithm = np.log(cutoff**2/infrared**2)
    volume = np.array([-radius**4*fourth/4, 0., 0.])
    einstein = -radius**2*second/3*np.array([np.cosh(2*shape), 2*np.sinh(2*shape), 4*np.cosh(2*shape)])
    curvature2 = -.5*logarithm*np.array([1/9+2*np.cosh(4*shape)/15,
                                        8*np.sinh(4*shape)/15, 32*np.cosh(4*shape)/15])
    return volume, einstein, curvature2


def eigenvalue_shape_data(maximum, radius, shape, mass=0.):
    ell = np.arange(maximum+1, dtype=float)
    base = ell*(ell+1)
    aa = base[:, None]/(radius*np.exp(shape))**2
    bb = base[None, :]/(radius*np.exp(-shape))**2
    lam = aa+bb+mass**2
    weights = (2*ell[:, None]+1)*(2*ell[None, :]+1)
    first, second = 2*(bb-aa), 4*(aa+bb)
    keep = lam > 0
    # The massless constant matrix is omitted from the complete determinant.
    return lam[keep], weights[keep], first[keep], second[keep], aa, bb, keep


def determinant_jets(maximum, radius, shape, mass=0., lower_time=0.):
    lam, weights, first, second, _, _, _ = eigenvalue_shape_data(maximum, radius, shape, mass)
    if lower_time == 0:
        value = .5*np.sum(weights*np.log(lam))
    else:
        value = None
    first_value = .5*np.sum(weights*np.exp(-lower_time*lam)*first/lam)
    hessian = .5*np.sum(weights*np.exp(-lower_time*lam)*(
        second/lam-first**2*(1/lam**2+lower_time/lam)))
    return value, float(first_value), float(hessian)


def heat_geometry_checks():
    rows = []
    for r1, r2 in [(1., 1.), (.8, 1.3), (1.2, .9)]:
        a2 = (1/r1**2+1/r2**2)/3
        a4 = (1/r1**4+1/r2**4)/15+1/(9*r1**2*r2**2)
        previous = None
        for s in [.04, .02, .01, .005]:
            maximum = int(np.ceil(20*max(r1, r2)/np.sqrt(s)))
            trace = heat_jets(s/r1**2, maximum)[0]*heat_jets(s/r2**2, maximum)[0]
            normalized = s*s*trace/(r1*r1*r2*r2)
            remainder = abs(normalized-(1+a2*s+a4*s*s))
            assert remainder < 2*s**3
            if previous is not None:
                assert 7.5 < previous/remainder < 8.5
            previous = remainder
            rows.append(dict(radii=[r1, r2], proper_time=s,
                             estimated_curvature_over_six=float((normalized-1)/s),
                             target_curvature_over_six=a2,
                             remainder_after_curvature_squared=float(remainder)))
    return dict(cases=rows)


def window_and_complete_determinant_checks():
    rows = []
    for shape in [0., .2]:
        previous = None
        for cutoff in [4., 8., 16., 32.]:
            infrared = cutoff/2
            radius = 1.
            # Fix one matrix size for the entire |u| <= .2 family at each cutoff.
            eta = cutoff*radius*np.exp(.2)
            maximum = int(np.ceil(eta*max(10., np.sqrt(24*np.log(max(eta, np.e))))))
            actual, quadrature_error = window_jets(cutoff, infrared, maximum, radius, shape)
            volume, einstein, curvature2 = continuum_window_jets(cutoff, infrared, radius, shape)
            remainder = actual-volume-einstein-curvature2
            assert actual[2] < 0
            if cutoff == 32:
                assert abs(actual[2]/einstein[2]-1) < .004
            if previous is not None:
                assert 3.6 < previous/abs(remainder[2]) < 4.7
            previous = abs(remainder[2])
            bare = determinant_jets(maximum, radius, shape)
            below_upper = determinant_jets(maximum, radius, shape, lower_time=cutoff**-2)
            infrared_part = determinant_jets(maximum, radius, shape, lower_time=infrared**-2)
            independent_window = below_upper[2]-infrared_part[2]
            assert abs(independent_window-actual[2]) < 2e-7
            assert bare[2] > 0
            # Exact all-size shape bound on the massless complete determinant.
            ratio_bound = 8*np.exp(4*.2)
            shape_lower_bound = 2*ratio_bound/(1+ratio_bound)**2*maximum**4
            shape_upper_bound = 2*(maximum+1)**4
            assert shape_lower_bound <= bare[2] <= shape_upper_bound
            ultraviolet_part = bare[2]-below_upper[2]
            closure_error = abs(bare[2]-(ultraviolet_part+actual[2]+infrared_part[2]))
            assert closure_error < 1e-5
            r1, r2 = radius*np.exp(shape), radius*np.exp(-shape)
            t1, t2 = cutoff**-2/r1**2, cutoff**-2/r2**2
            common_bound = heat_bound(t1/2)*heat_bound(t2/2)*(
                np.exp(-t1*(maximum+1)*(maximum+2)/4)+
                np.exp(-t2*(maximum+1)*(maximum+2)/4))
            shape_constants = np.array([1., 2*TAIL_CONSTANTS[1],
                                        2*TAIL_CONSTANTS[2]+2*TAIL_CONSTANTS[1]**2])
            finite_size_bounds = .5*np.log(cutoff**2/infrared**2)*shape_constants*common_bound
            rows.append(dict(shape=shape, upper_cutoff=cutoff, lower_cutoff=infrared,
                             maximum_angular_momentum=maximum,
                             scalar_real_dimensions_including_constant=(maximum+1)**4,
                             window_jets=actual.tolist(), quadrature_error=quadrature_error,
                             volume_jets=volume.tolist(), einstein_jets=einstein.tolist(),
                             curvature_squared_jets=curvature2.tolist(),
                             remainder_jets=remainder.tolist(),
                             analytical_finite_size_jet_bounds=finite_size_bounds.tolist(),
                             independent_window_hessian_error=float(abs(independent_window-actual[2])),
                             complete_determinant_shape_hessian=bare[2],
                             complete_hessian_analytical_lower_bound=float(shape_lower_bound),
                             complete_hessian_analytical_upper_bound=float(shape_upper_bound),
                             ultraviolet_shape_hessian=ultraviolet_part,
                             infrared_shape_hessian=infrared_part[2],
                             sector_sum_error=float(closure_error)))
    return dict(cases=rows,
                scope='The proper-time window has a controlled Einstein curvature response. The full fixed-size positive scalar determinant instead has positive shape Hessian. The window is a regulated spectral contribution, not a separately derived microscopic theory or proof that the omitted contribution can be discarded.')


def independent_shape_variations():
    rows = []
    for maximum, shape, mass in itertools.product([8, 16], [0., .2], [0., .3]):
        base = determinant_jets(maximum, 1., shape, mass)
        lam, weights, _, _, aa, bb, keep = eigenvalue_shape_data(maximum, 1., shape, mass)
        positive = float(np.sum(weights*(8*(aa*bb)[keep]+2*mass**2*(aa+bb)[keep])/lam**2))
        assert abs(positive-base[2]) < 2e-9
        errors = []
        for epsilon in [.004, .002]:
            plus = determinant_jets(maximum, 1., shape+epsilon, mass)[0]
            minus = determinant_jets(maximum, 1., shape-epsilon, mass)[0]
            difference = (plus-2*base[0]+minus)/epsilon**2
            error = abs(difference-base[2])/base[2]
            assert error < 2e-5
            errors.append(error)
        assert 3.8 < errors[0]/errors[1] < 4.2
        rows.append(dict(maximum_angular_momentum=maximum, shape=shape, mass=mass,
                         positive_hessian=positive, finite_difference_relative_errors=errors))
    # Independently vary the regulated action value at fixed matrix size.
    for shape in [0., .2]:
        base, _ = window_jets(8., 4., 120, 1., shape)
        epsilon = .002
        plus, _ = window_jets(8., 4., 120, 1., shape+epsilon)
        minus, _ = window_jets(8., 4., 120, 1., shape-epsilon)
        difference = (plus[0]-2*base[0]+minus[0])/epsilon**2
        error = abs(difference-base[2])/abs(base[2])
        assert error < 1e-5
        rows.append(dict(window_shape=shape, finite_difference_relative_error=float(error)))
    return dict(cases=rows)


def main():
    root = Path(__file__).resolve().parents[1]
    report = dict(symbolic=symbolic_checks(), spin_spectra=matrix_spectrum_checks(),
                  heat_tails=tail_checks(), heat_geometry=heat_geometry_checks(),
                  induced_window=window_and_complete_determinant_checks(),
                  independent_variations=independent_shape_variations())
    sources = ['GEOMETRIC_SPECTRAL_INDUCTION.md', 'scripts/geometric_spectral_induction_audit.py',
               'MICROSCOPIC_METRIC_WARD.md', 'ISOTROPIC_TENSOR_REGULATOR.md',
               'INDUCED_TENSOR_DYNAMICS.md', 'CONTINUUM_EINSTEIN_BRIDGE.md',
               'EINSTEIN_MODEL_DECISION.md', 'GRAVITY_FROM_CLOCK_CONSTRAINTS.md']
    report['source_sha256'] = {p: hashlib.sha256((root/p).read_bytes()).hexdigest() for p in sources}
    report['scope'] = ('Known spin-matrix product-sphere spectra yield a controlled geometric heat-kernel window '
                       'and its first two radius variations, including the Einstein curvature coefficient. '
                       'The complete fixed-size scalar determinant has the opposite sign of fixed-volume shape '
                       'curvature, with a proved fourth-power angular-cutoff lower bound; the omitted ultraviolet contribution cannot be dropped. '
                       'The matrix geometry and regulator window are supplied. Microscopic locality, Lorentzian '
                       'gravity, state selection, gravitational constraints, and a TOE remain unproved.')
    target = root/'data/geometric_spectral_induction_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(dict(report=str(target), matrix_spectra=5, tail_cases=9,
                          heat_geometry_cases=12, spectral_window_cases=8,
                          independent_variation_cases=10, source_references=8,
                          scope=report['scope']), indent=2))


if __name__ == '__main__':
    main()
