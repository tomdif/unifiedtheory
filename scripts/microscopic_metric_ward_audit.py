#!/usr/bin/env python3
"""Exact scalar relabeling identities and their limits as gravitational symmetry.

Checks finite Gaussian identities, local coefficient bounds, the enlarged
matrix Lie algebra, and smooth versus ultraviolet lattice bracket errors.
No interacting spin phase or Einstein constraint algebra is established.
"""
import hashlib
import itertools
import json
import math
from pathlib import Path

import numpy as np
from scipy.linalg import expm
import sympy as sy


def comm(a, b):
    return a @ b-b @ a


def lattice(side, dimension, mass=.3):
    coords = np.array(list(itertools.product(range(side), repeat=dimension)))
    size = len(coords)
    shifts = []
    for axis in range(dimension):
        moved = coords.copy()
        moved[:, axis] = (moved[:, axis]+1) % side
        columns = np.ravel_multi_index(moved.T, (side,)*dimension)
        shift = np.zeros((size, size))
        shift[np.arange(size), columns] = 1
        shifts.append(shift)
    derivatives = [(t-t.T)/2 for t in shifts]
    matrix = mass*mass*np.eye(size)+sum(2*np.eye(size)-t-t.T for t in shifts)
    separation = abs(coords[:, None, :]-coords[None, :, :])
    distance = np.minimum(separation, side-separation).sum(axis=2)
    return coords, derivatives, matrix, distance


def generator(fields, derivatives):
    return sum((f[:, None]*d+d*f[None, :])/2 for f, d in zip(fields, derivatives))


def exact_symbolic_checks():
    # Nontrivial rational example of the general cyclic-trace identity.
    matrix = sy.Matrix([[3, -1, 0], [-1, 4, -1], [0, -1, 3]])
    r = sy.Matrix([[0, 2, -1], [-2, 0, 3], [1, -3, 0]])
    s = sy.Matrix([[0, -1, 4], [1, 0, 2], [-4, -2, 0]])
    v = matrix*r-r*matrix
    w = v*r-r*v
    inverse = matrix.inv()
    bubble = -sy.trace(inverse*v*inverse*v)/2
    contact = sy.trace(inverse*w)/2
    assert bubble+contact == 0 and bubble < 0
    vs = matrix*s-s*matrix
    mixed = ((v*s-s*v)+(vs*r-r*vs))/2
    assert sy.trace(inverse*mixed-inverse*v*inverse*vs) == 0
    # Idempotents force every derivation of the pointwise finite algebra to zero.
    derivation_rows = []
    for size in range(2, 8):
        unknown = sy.symbols('a:'+str(size*size))
        a = sy.Matrix(size, size, unknown)
        equations = []
        for j in range(size):
            for i in range(size):
                equations.append(a[i, j]-2*int(i == j)*a[i, j])
        coefficients, _ = sy.linear_eq_to_matrix(equations, unknown)
        assert coefficients.rank() == size*size
        derivation_rows.append(dict(sites=size, derivation_dimension=0))
    return dict(exact_bubble=str(bubble), exact_contact=str(contact),
                mixed_ward_identity=True, finite_point_algebra=derivation_rows)


def ward_and_spectator_checks():
    rng = np.random.default_rng(95406)
    rows = []
    for dimension, side in [(1, 9), (2, 5), (3, 4), (3, 5)]:
        coords, derivatives, matrix, distance = lattice(side, dimension)
        fields = rng.uniform(-.4, .4, (dimension, len(coords)))
        r = generator(fields, derivatives)
        s = generator(rng.uniform(-.3, .3, fields.shape), derivatives)
        assert np.max(abs(r+r.T)) < 1e-15
        v, vs = comm(matrix, r), comm(matrix, s)
        w = comm(v, r)
        mixed = (comm(v, s)+comm(vs, r))/2
        inverse_v = np.linalg.solve(matrix, v)
        bubble = -.5*np.trace(inverse_v @ inverse_v)
        contact = .5*np.trace(np.linalg.solve(matrix, w))
        mixed_error = .5*abs(np.trace(np.linalg.solve(matrix, mixed)-
                                    inverse_v @ np.linalg.solve(matrix, vs)))
        assert bubble < 0
        assert abs(bubble+contact) < 2e-11 and mixed_error < 2e-11
        assert abs(np.trace(inverse_v)) < 2e-12
        assert np.max(abs(v[distance > 2]), initial=0.) < 1e-14
        assert np.max(abs(w[distance > 3]), initial=0.) < 1e-14
        # An arbitrary independent strain interaction survives the relabeling.
        f = rng.uniform(-.2, .2, len(coords))
        strain = derivatives[0].T @ (f[:, None]*derivatives[0])
        strain_curvature = -.5*np.trace(np.linalg.solve(matrix, strain) @
                                      np.linalg.solve(matrix, strain))
        mixed_strain = .5*np.trace(np.linalg.solve(matrix, comm(strain, r))-
                                  np.linalg.solve(matrix, strain) @ inverse_v)
        assert abs(mixed_strain) < 2e-12
        base_logdet = np.linalg.slogdet(matrix)[1]
        for amplitude in [.15, .6]:
            u = expm(amplitude*r)
            transformed = u.T @ matrix @ u
            transformed_strain = u.T @ strain @ u
            det_error = abs(np.linalg.slogdet(transformed)[1]-base_logdet)
            spectrum_error = np.max(abs(np.linalg.eigvalsh(matrix)-
                                       np.linalg.eigvalsh(transformed)))
            transported_curvature = -.5*np.trace(np.linalg.solve(transformed, transformed_strain) @
                                                np.linalg.solve(transformed, transformed_strain))
            assert det_error < 2e-11 and spectrum_error < 2e-12
            assert abs(transported_curvature-strain_curvature) < 2e-12
            # Compare full finite-source determinants, not only a Hessian formula.
            finite_source = matrix+.1*strain
            finite_error = abs(np.linalg.slogdet(u.T @ finite_source @ u)[1]-
                               np.linalg.slogdet(finite_source)[1])
            assert finite_error < 2e-11
            rows.append(dict(dimension=dimension, side=side, sites=len(coords), amplitude=amplitude,
                             bubble=float(bubble), contact=float(contact),
                             cancellation_error=float(abs(bubble+contact)),
                             mixed_ward_error=float(mixed_error), logdet_error=float(det_error),
                             spectrum_error=float(spectrum_error),
                             unchanged_strain_curvature_error=float(abs(transported_curvature-strain_curvature)),
                             finite_strain_logdet_error=float(finite_error)))
    return dict(cases=rows,
                scope='Exact relabeling of positive finite Gaussian matrices. Transporting an independent strain interaction preserves its complete effective action, including any failed Einstein response.')


def weighted_norm(matrix, distance, rate):
    return float(np.max(np.sum(abs(matrix)*np.exp(rate*distance), axis=1)))


def locality_and_positive_approximation():
    rows = []
    for dimension, side in [(1, 41), (2, 9), (3, 5)]:
        coords, derivatives, matrix, distance = lattice(side, dimension)
        fields = np.array([.3*np.sin(2*np.pi*(coords[:, i]+.17)/side)
                           for i in range(dimension)])
        r = generator(fields, derivatives)
        rho = dimension*float(np.max(abs(fields)))
        mnorm = .3**2+4*dimension
        amplitude, rate = .7, .4
        u = expm(amplitude*r)
        target = u.T @ matrix @ u
        analytic_weighted_bound = (.3**2+2*dimension*(1+np.exp(rate)))*np.exp(
            2*amplitude*rho*np.exp(rate))
        measured = weighted_norm(target, distance, rate)
        assert measured <= analytic_weighted_bound+1e-12
        polynomial, term = np.eye(len(coords)), np.eye(len(coords))
        for degree in range(1, 9):
            term = term @ (amplitude*r)/degree
            polynomial = polynomial+term
            if degree not in [2, 4, 8]:
                continue
            remainder_bound = np.exp(amplitude*rho)*(amplitude*rho)**(degree+1)/math.factorial(degree+1)
            approximate = polynomial.T @ matrix @ polynomial
            error = np.linalg.norm(approximate-target, 2)
            bound = mnorm*(2*remainder_bound+remainder_bound**2)
            assert remainder_bound < 1
            assert error < bound+2e-12
            assert np.max(abs(polynomial[distance > degree]), initial=0.) < 1e-15
            assert np.max(abs(approximate[distance > 2*degree+1]), initial=0.) < 1e-14
            lowest = np.linalg.eigvalsh(approximate).min()
            positive_bound = .3**2*(1-remainder_bound)**2
            assert lowest >= positive_bound-2e-12
            rows.append(dict(dimension=dimension, side=side, degree=degree,
                             coefficient_error=float(error), analytical_error_bound=float(bound),
                             smallest_eigenvalue=float(lowest), positive_lower_bound=float(positive_bound),
                             finite_range=2*degree+1, measured_weighted_row_norm=measured,
                             analytical_weighted_row_bound=float(analytic_weighted_bound)))
    return dict(cases=rows,
                scope='Volume-independent matrix-coefficient bounds at fixed lattice spacing, bounded displacement and finite transformation parameter. They are not uniform refinement bounds or bounded-operator-norm estimates for interacting scalar/spin Hamiltonians.')


def modular_lie_dimension(side, dimension=1, prime=101):
    # Four times R(e_i) has integer entries at unit spacing.
    coords, derivatives, _, _ = lattice(side, dimension)
    size = len(coords)
    initial = []
    for derivative in derivatives:
        difference = (2*derivative).astype(np.int64)
        for i in range(size):
            projector = np.zeros((size, size), dtype=np.int64)
            projector[i, i] = 1
            initial.append((projector @ difference+difference @ projector) % prime)
    upper = np.triu_indices(size, 1)
    pivots, basis = {}, []
    def insert(matrix):
        vector = matrix[upper].copy() % prime
        for index in sorted(pivots):
            vector = (vector-vector[index]*pivots[index]) % prime
        nonzero = np.flatnonzero(vector)
        if not len(nonzero):
            return False
        index = int(nonzero[0])
        pivots[index] = vector*pow(int(vector[index]), -1, prime) % prime
        basis.append(matrix % prime)
        return True
    for matrix in initial:
        insert(matrix)
    initial_rank = len(basis)
    cursor = 0
    target = size*(size-1)//2
    while cursor < len(basis) and len(basis) < target:
        matrix = basis[cursor]
        for other in initial:
            insert(comm(matrix, other) % prime)
        cursor += 1
    assert initial_rank == dimension*size and len(basis) == target
    return dict(sites=size, side=side, dimension=dimension,
                initial_rank=initial_rank, lie_rank_mod_prime=len(basis),
                full_skew_dimension=target, prime=prime)


def local_algebra_checks():
    rows = [modular_lie_dimension(size) for size in [5, 7, 9, 11]]
    rows.append(modular_lie_dimension(3, dimension=2))
    # Exact inversion of xi_i+xi_(i+1) on odd cycles isolates every edge.
    for size in [5, 7, 9]:
        shift = sy.zeros(size)
        for i in range(size):
            shift[i, (i+1) % size] = 1
        assert (sy.eye(size)+shift).det() == 2
    # Neighbor rotations generate longer-range rotations by commutators.
    e01, e12, e02 = [sy.zeros(3) for _ in range(3)]
    for matrix, i, j in [(e01, 0, 1), (e12, 1, 2), (e02, 0, 2)]:
        matrix[i, j], matrix[j, i] = 1, -1
    assert e01*e12-e12*e01 == e02
    return dict(odd_cycle_cases=rows, exact_edge_reconstruction=True,
                exact_edge_commutator=True,
                scope='For this generator family on a periodic cubic graph with odd side, unrestricted finite-lattice closure is so(V), not generally the dV-parameter family of sampled vector fields. Edge reconstruction on each odd coordinate cycle and graph connectivity prove the general statement. This is not a no-go theorem for emergent gravitational symmetry.')


def mode_vertex(spacing, k, q):
    return .5j*(np.sin(spacing*q)+np.sin(spacing*(q+k)))/spacing


def bracket_defect(spacing, k, ell, q):
    r = lambda first, second: mode_vertex(spacing, first, second)
    return r(ell, q)*r(k, q+ell)-r(k, q)*r(ell, q+k)-1j*(ell-k)*r(k+ell, q)


def smooth_and_uv_checks():
    # Continuum half-density generators represent the vector-field bracket.
    k, ell, q = sy.symbols('k ell q', real=True)
    r = lambda first, second: sy.I*(second+first/2)
    assert sy.expand(r(ell, q)*r(k, q+ell)-r(k, q)*r(ell, q+k)-sy.I*(ell-k)*r(k+ell, q)) == 0
    rng = np.random.default_rng(95407)
    bound_cases = []
    for _ in range(80):
        band = float(rng.uniform(.2, 8))
        spacing = float(rng.uniform(.01, .3)/band)
        k_, ell_, q_ = rng.uniform(-band, band, 3)
        error = abs(bracket_defect(spacing, k_, ell_, q_))
        bound = (103/6)*spacing**2*band**4
        assert error <= bound+1e-12
        bound_cases.append(float(error/bound))
    rows = []
    previous = None
    for sites in [64, 128, 256, 512]:
        spacing = 2*np.pi/sites
        smooth = float(abs(bracket_defect(spacing, 1, 2, 3)))
        ultraviolet = float(abs(bracket_defect(spacing, 0, 1, sites/4)))
        if sites >= 256:
            assert 3.8 < previous/smooth < 4.1
        assert 1 < spacing*ultraviolet < 1.1
        previous = smooth
        # Direct full-output sampled action, including the generated mode.
        x = spacing*np.arange(sites)
        xi, eta, field = np.exp(1j*x), np.exp(2j*x), np.exp(3j*x)
        def derivative(f):
            return (np.roll(f, -1)-np.roll(f, 1))/(2*spacing)
        def action(vector, f):
            return (vector*derivative(f)+derivative(vector*f))/2
        bracket = 1j*np.exp(3j*x)
        actual = action(xi, action(eta, field))-action(eta, action(xi, field))-action(bracket, field)
        target = bracket_defect(spacing, 1, 2, 3)*np.exp(6j*x)
        assert np.max(abs(actual-target)) < 2e-11
        rows.append(dict(sites=sites, spacing=spacing, smooth_full_output_error=smooth,
                         ultraviolet_error=ultraviolet, spacing_times_uv_error=spacing*ultraviolet))
    return dict(refinement=rows, mode_bound_cases=80, largest_fraction_of_proved_bound=max(bound_cases),
                scope='The spatial half-density bracket converges on fixed band-limited data with a proved a^2 K^4 bound. A high-frequency input exhibits an error proportional to 1/a; there is no full-space operator-norm convergence. No state-selection or loop-level Ward restoration follows.')


def main():
    root = Path(__file__).resolve().parents[1]
    report = dict(symbolic=exact_symbolic_checks(), ward=ward_and_spectator_checks(),
                  locality=locality_and_positive_approximation(), algebra=local_algebra_checks(),
                  continuum=smooth_and_uv_checks())
    sources = ['MICROSCOPIC_METRIC_WARD.md', 'scripts/microscopic_metric_ward_audit.py',
               'ISOTROPIC_TENSOR_REGULATOR.md', 'scripts/isotropic_tensor_regulator_audit.py',
               'INDUCED_TENSOR_DYNAMICS.md', 'EINSTEIN_MODEL_DECISION.md',
               'GRAVITY_FROM_CLOCK_CONSTRAINTS.md', 'SPIN_CLOCK_BRACKET.md']
    report['source_sha256'] = {p: hashlib.sha256((root/p).read_bytes()).hexdigest() for p in sources}
    report['scope'] = ('An exact positive, exponentially local Gaussian relabeling completion supplies '
                       'the nonlinear contact cancellation required along its redundant directions. '
                       'It preserves any independent strain response and does not repair the failed Einstein cone. '
                       'The finite-lattice generator closure and fixed-band versus ultraviolet estimates distinguish '
                       'matrix basis symmetry from gravitational diffeomorphisms. No microscopic Einstein gravity or TOE is proved.')
    target = root/'data/microscopic_metric_ward_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(dict(report=str(target), ward_cases=len(report['ward']['cases']),
                          locality_cases=len(report['locality']['cases']),
                          lie_closure_cases=5, smooth_bound_cases=80, refinement_cases=4,
                          source_references=len(sources), scope=report['scope']), indent=2))


if __name__ == '__main__':
    main()
