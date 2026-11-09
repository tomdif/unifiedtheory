#!/usr/bin/env python3
"""Check a full-interacting quadratic-response bound and its source normalization.

The proof is in CONVEX_MATTER_POLE_BOUND.md. Finite quadrature checks include
an actual nonconstant-mode member of the tapered theory and radial test
measures. They do not construct a metric propagator or prove Einstein gravity.
"""
import hashlib
import json
from pathlib import Path

import numpy as np
from scipy.integrate import quad
from scipy.linalg import block_diag
from scipy.special import gamma, roots_genlaguerre
import sympy as sy

from geometric_spectral_induction_audit import spin_matrices
from local_symbol_interaction_audit import sphere_cubature


def symbolic_checks():
    x = sy.Matrix(sy.symbols('x:3', real=True))
    g, q = sy.symbols('g q', positive=True)
    squared = (x.T*x)[0]
    hessian = sy.hessian(g*squared**2/(4*q), list(x))
    assert sy.simplify(hessian-g/q*(squared*sy.eye(3)+2*x*x.T)) == sy.zeros(3)
    a, b, t = sy.symbols('a b t', real=True)
    filtered = a+sy.sqrt(3)*b*t/2
    spherical = sy.integrate(filtered**4, (t, -1, 1))/2
    assert sy.expand(spherical-a**4-sy.Rational(3, 2)*a*a*b*b-
                     sy.Rational(9, 80)*b**4) == 0
    return dict(quartic_hessian_identity=True, actual_low_mode_quartic_identity=True)


def real_rotations(size):
    blocks = [[], [], []]
    eigenvalues = []
    for ell in range(size):
        transform = np.zeros((2*ell+1, 2*ell+1), complex)
        transform[ell, 0] = 1
        for m in range(1, ell+1):
            transform[ell+m, 2*m-1] = (-1)**m/np.sqrt(2)
            transform[ell-m, 2*m-1] = 1/np.sqrt(2)
            transform[ell+m, 2*m] = -1j*(-1)**m/np.sqrt(2)
            transform[ell-m, 2*m] = 1j/np.sqrt(2)
        assert np.max(abs(transform.conj().T @ transform-np.eye(2*ell+1))) < 1e-14
        for axis, angular in enumerate(spin_matrices(2*ell)):
            derivative = transform.conj().T @ (-1j*angular) @ transform
            assert np.max(abs(derivative.imag)) < 1e-14
            assert np.max(abs(derivative.real+derivative.real.T)) < 1e-14
            blocks[axis].append(derivative.real)
        eigenvalues.extend([ell*(ell+1)]*(2*ell+1))
    return [block_diag(*entries) for entries in blocks], np.array(eigenvalues)


def tensor_basis():
    matrices = []
    for left, right in [(0, 1), (3, 4)]:
        matrix = np.zeros((6, 6))
        matrix[left, left], matrix[right, right] = 1/np.sqrt(2), -1/np.sqrt(2)
        matrices.append(matrix)
    cross = np.zeros((6, 6))
    cross[0, 3] = cross[3, 0] = 1/np.sqrt(2)
    matrices.extend([cross, np.eye(6)/np.sqrt(6)])
    return matrices


def derivative_source_checks():
    rows = []
    for left, right in [(2, 2), (2, 3), (3, 3)]:
        dl, ell = real_rotations(left)
        dr, angular = real_rotations(right)
        for kappa in [.7, 1.4]:
            r1, r2, mass = left/kappa, right/kappa, .4*kappa
            volume = 16*np.pi**2*r1*r1*r2*r2
            count = left**2*right**2
            laplacian = (ell[:, None]/r1**2+angular[None, :]/r2**2).ravel()
            taper = ((1-ell[:, None]/left**2)*(1-angular[None, :]/right**2)).ravel()
            covariance = 1/(laplacian+mass*mass)
            rotations = [np.kron(d, np.eye(right**2))/r1 for d in dl]
            rotations += [np.kron(np.eye(left**2), d)/r2 for d in dr]
            filtered = [d*taper[None, :] for d in rotations]
            casimir_error = np.max(abs(sum(t.T @ t for t in filtered)-
                                        np.diag(taper*taper*laplacian)))
            assert casimir_error < 1e-13
            operator_bound = float(np.max(covariance*taper*taper*laplacian))
            assert operator_bound <= 1
            el, wl = sphere_cubature(left, r1, 4)
            er, wr = sphere_cubature(right, r2, 4)
            evaluation, weights = np.kron(el, er), np.kron(wl, wr)
            values = np.array([evaluation @ t for t in filtered])
            diagonal_trace = np.einsum('axp,p,axp->x', values, covariance, values)
            exact_diagonal = np.sum(covariance*taper*taper*laplacian)/volume
            diagonal_error = np.max(abs(diagonal_trace-exact_diagonal))
            assert diagonal_error < 2e-14
            assert exact_diagonal <= count/volume
            matrices = tensor_basis()
            profiles = [np.ones(len(weights))/np.sqrt(volume)]*len(matrices)
            # A genuinely varying, L2-normalized source orthogonal to constants.
            matrices.append(matrices[0])
            profiles.append(evaluation[:, right**2])
            gram = np.array([[np.trace(b @ d)*np.dot(weights, f*h)
                              for d, h in zip(matrices, profiles)]
                             for b, f in zip(matrices, profiles)])
            assert np.max(abs(gram-np.eye(len(matrices)))) < 2e-13
            source_matrices = []
            for tensor, profile in zip(matrices, profiles):
                matrix = np.zeros((count, count))
                for i, j in zip(*np.nonzero(tensor)):
                    matrix += tensor[i, j]*values[i].T @ (
                        (weights*profile)[:, None]*values[j])
                assert np.max(abs(matrix-matrix.T)) < 1e-13
                source_matrices.append(matrix)
            root_c = np.sqrt(covariance)
            whitened = [root_c[:, None]*b*root_c[None, :] for b in source_matrices]
            traces = np.array([[np.sum(b*d) for d in whitened] for b in whitened])
            for species in [1, 8]:
                free_chi = 2*traces/species
                bound = kappa**4/(4*np.pi**2*species)
                slack = np.linalg.eigvalsh(bound*np.eye(len(matrices))-2*free_chi)
                assert min(slack) > -1e-13
                rows.append(dict(matrix_sizes=[left, right], kappa=kappa, species=species,
                                 real_frame_casimir_error=float(casimir_error),
                                 kernel_diagonal_error=float(diagonal_error),
                                 derivative_covariance_operator_norm=operator_bound,
                                 source_gram_error=float(np.max(abs(gram-np.eye(len(matrices))))),
                                 free_susceptibility_largest_eigenvalue=float(np.linalg.eigvalsh(free_chi)[-1]),
                                 full_interacting_uniform_upper_bound=float(bound),
                                 minimum_upper_bound_slack=float(min(slack))))
    return dict(cases=rows, scope='Exact-degree cubature and real angular matrices check the derivative-frame and local-source constants on actual product spheres. These cases evaluate free covariances; the analytical inequality bounds the nonlinear ones.')


def radial_moments(dimension, mass_squared, coupling, species):
    shape = dimension/2
    alpha = coupling/(species*mass_squared**2)
    # Integrate z = mass_squared*|x|^2/2, rescaled around its positive mode.
    mode = shape-1 if alpha == 0 else 2*(shape-1)/(1+np.sqrt(1+8*alpha*(shape-1)))
    def moment(power):
        def density(t):
            if t == 0:
                return 0.
            return np.exp((shape-1+power)*np.log(t)-mode*(t-1)-
                          alpha*mode*mode*(t*t-1))
        return (quad(density, 0, 1, epsabs=2e-12, epsrel=2e-12)[0]+
                quad(density, 1, np.inf, epsabs=2e-12, epsrel=2e-12)[0])
    normalizer = moment(0)
    return [moment(p)/normalizer*(2*mode/mass_squared)**p for p in [1, 2]]


def radial_covariance_checks():
    rows = []
    for modes in [2, 3]:
        matrices = [np.eye(modes)/np.sqrt(modes)]
        traceless = np.zeros((modes, modes))
        traceless[0, 0], traceless[1, 1] = 1/np.sqrt(2), -1/np.sqrt(2)
        cross = np.zeros_like(traceless)
        cross[0, 1] = cross[1, 0] = 1/np.sqrt(2)
        matrices += [traceless, cross]
        traces = np.array([np.trace(b) for b in matrices])
        gram = np.array([[np.trace(b @ c) for c in matrices] for b in matrices])
        for species in [8, 32]:
            dimension, a = modes*species, .7
            free = 2*gram/(species*a*a)
            for coupling in [0., .1, 1., 10.]:
                r2, r4 = radial_moments(dimension, a, coupling, species)
                v = r4/(dimension*(dimension+2))
                chi = 2*v*gram/species+(v-(r2/dimension)**2)*np.outer(traces, traces)
                eig = np.linalg.eigvalsh(chi)
                assert min(eig) > 0
                assert min(np.linalg.eigvalsh(2*free-chi)) > -1e-11
                assert r2/dimension <= 1/a+1e-11
                if coupling == 0:
                    assert np.max(abs(chi-free)) < 1e-11
                upper = float(np.linalg.eigvalsh(2*free)[-1])
                legendre_floor = float(np.linalg.eigvalsh(np.linalg.inv(chi))[0])
                assert legendre_floor >= 1/upper-1e-10
                rows.append(dict(modes=modes, species=species, coupling=coupling,
                                 exact_radial_susceptibility_eigenvalues=eig.tolist(),
                                 twice_free_upper_eigenvalue=upper,
                                 composite_legendre_minimum_eigenvalue=legendre_floor,
                                 analytical_legendre_floor=1/upper))
    return dict(cases=rows, scope='Nonperturbative radial integrals test the general even-convex theorem at finite species, including indefinite quadratic matrices. For more than one mode this radial quartic is a test measure, not the pointwise product-sphere interaction.')


def low_mode_moments(coupling, order, mass_squared=.4):
    # Actual q=1, (N1,N2)=(2,1), kappa=1 tapered pointwise model.
    # Constant coefficient a and three real ell=1 coefficients b have
    # integral psi^4 = (a^4 + 3 a^2 |b|^2/2 + 9 |b|^4/80)/V.
    volume = 64*np.pi**2
    z, wz = roots_genlaguerre(order, -.5)
    w, ww = roots_genlaguerre(order, .5)
    a2, b2 = 2*z[:, None]/mass_squared, 2*w[None, :]/(mass_squared+.5)
    quartic = (a2*a2+1.5*a2*b2+9*b2*b2/80)/volume
    weights = wz[:, None]*ww[None, :]/(gamma(.5)*gamma(1.5))
    tilted = weights*np.exp(-coupling*quartic/4)
    normalizer = tilted.sum()
    return np.array([np.sum(tilted*p)/normalizer for p in [a2, b2, a2*a2, b2*b2, a2*b2]])


def low_mode_interaction_checks():
    rows, mass_squared = [], .4
    free = np.diag([2/mass_squared**2, 2/(mass_squared+.5)**2,
                    2/(mass_squared+.5)**2])
    for coupling in [0., 1., 10., 50.]:
        first = low_mode_moments(coupling, 100, mass_squared)
        second = low_mode_moments(coupling, 180, mass_squared)
        error = np.max(abs(first-second))
        assert error < 3e-7
        a2, b2, a4, b4, a2b2 = second
        # Q = a^2, |b|^2/sqrt(3), (b_x^2-b_y^2)/sqrt(2).
        chi = np.array([[a4-a2*a2, (a2b2-a2*b2)/np.sqrt(3), 0.],
                        [(a2b2-a2*b2)/np.sqrt(3), (b4-b2*b2)/3, 0.],
                        [0., 0., 2*b4/15]])
        assert min(np.linalg.eigvalsh(chi)) > 0
        slack = min(np.linalg.eigvalsh(2*free-chi))
        assert slack > 0
        if coupling == 0:
            assert np.max(abs(chi-free)) < 2e-10
        rows.append(dict(matrix_sizes=[2, 1], species=1, coupling=coupling,
                         independent_quadrature_moment_error=float(error),
                         full_nonlinear_susceptibility=chi.tolist(),
                         minimum_twice_free_bound_slack=float(slack)))
    return dict(cases=rows, scope='Actual nonconstant-mode tapered pointwise theory at q=1. Rotational integration reduces the four-dimensional field integral to two Gamma-weighted integrals. Increasing quadrature order checks numerical convergence; no interval-certified integration or large-volume extrapolation is claimed.')


def main():
    root = Path(__file__).resolve().parents[1]
    report = dict(symbolic=symbolic_checks(), derivative_sources=derivative_source_checks(),
                  radial_covariances=radial_covariance_checks(),
                  actual_low_mode_interaction=low_mode_interaction_checks())
    sources = ['CONVEX_MATTER_POLE_BOUND.md', 'scripts/convex_matter_pole_bound_audit.py',
               'SPECTRAL_EDGE_LOCALITY.md', 'scripts/spectral_edge_locality_audit.py',
               'LOCAL_SYMBOL_INTERACTION.md', 'scripts/local_symbol_interaction_audit.py',
               'scripts/geometric_spectral_induction_audit.py',
               'INDUCED_TENSOR_DYNAMICS.md', 'EINSTEIN_MODEL_DECISION.md',
               'MICROSCOPIC_METRIC_WARD.md']
    report['source_sha256'] = {p: hashlib.sha256((root/p).read_bytes()).hexdigest() for p in sources}
    report['scope'] = ('The even convex matter measure obeys a full-interacting quadratic-source covariance '
                       'bound at every nonnegative coupling and finite species. Derivative tensor sources '
                       'have a uniform fixed-proper-cutoff bound. A positive massless pole with nonzero '
                       'fixed residue cannot be identified with these bounded-normalization composites. '
                       'This is not a no-go theorem for every emergent graviton, a proof of momentum '
                       'differentiability, or a construction of a physical metric propagator. Einstein '
                       'gravity, fixed-species curvature control, and TOE remain unproved. No Lean theorem.')
    target = root/'data/convex_matter_pole_bound_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    counts = {k: len(v['cases']) for k, v in report.items() if isinstance(v, dict) and 'cases' in v}
    print(json.dumps(dict(report=str(target), checks=counts, source_references=len(sources),
                          scope=report['scope']), indent=2))


if __name__ == '__main__':
    main()
