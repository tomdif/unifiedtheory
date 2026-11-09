#!/usr/bin/env python3
"""Gaussian field-mediated geometry response, with explicit scope boundaries."""
import hashlib
import copy
import itertools
import json
from pathlib import Path

import numpy as np
import scipy.linalg as la
import scipy.sparse as sp
import sympy as sy
from scipy.integrate import quad
from scipy.sparse.linalg import LinearOperator, cg

from collective_wave_audit import MeanCell, reduced_inverse
from energetic_probe_audit import adjacency_matrix
from patch_geometry_audit import rectangular_torus


def local_bound(p):
    Q = sy.Matrix([[1, 1, 0], [1, 3, 1], [0, 1, 1]])
    assert set(Q.eigenvals()) == {1, 2-sy.sqrt(3), 2+sy.sqrt(3)}
    lambdas = np.array([0., 1-np.sqrt(3), 1+np.sqrt(3)])
    ratios = [(z-p)*x/(1+p*x) for z in [0., 1.] for x in lambdas]
    radius = float(max(abs(x) for x in ratios))
    assert (3-np.sqrt(3))/4 < p < (1+np.sqrt(3))/4
    assert radius < 1
    base = np.eye(3)+p*(np.array(Q, dtype=float)-np.eye(3))
    rng = np.random.default_rng(3001)
    for _ in range(200):
        x = rng.normal(size=3)
        z = rng.uniform()
        change = (z-p)*(np.array(Q, dtype=float)-np.eye(3))
        assert abs(x@change@x) <= radius*(x@base@x)+1e-12
    u, v, y = sy.symbols('u v y', real=True)
    middle = (u*u+v*v)/2+2*y*y+u*y
    difference = y*y+u*y
    squares = (u*u+2*u*y-2*y*y)**2+2*v*v*(u+y)**2+6*v*v*y*y+v**4
    assert sy.expand(4*(middle**2-3*difference**2)-squares) == 0
    midpoint = max(abs((z-.5)*x/(1+.5*x)) for z in [0., 1.] for x in lambdas)
    assert abs(midpoint-1/np.sqrt(3)) < 1e-14
    return dict(local_eigenvalues=['1', '2-sqrt(3)', '2+sqrt(3)'],
                physical_mean_relative_radius=radius, midpoint_relative_radius=float(midpoint),
                midpoint_sum_of_squares=True, admissible_reference_interval=[float((3-np.sqrt(3))/4),
                                                                       float((1+np.sqrt(3))/4)],
                endpoint_ratios=[float(x) for x in ratios], random_form_checks=200)


def change_reference(mean, reference):
    result = copy.copy(mean)
    result.p = reference
    result.H0 = result.hamiltonian([0., 0., 0.]).real.tocsr()
    first, second = result.quantum.derivatives()
    result.first, result.second = result.average_blocks(first), result.average_blocks(second)
    result.source = result.first@result.g
    solved, _ = reduced_inverse(result.H0, result.g, result.source)
    diamagnetic = np.vdot(result.g, result.second@result.g).real/2
    result.D = np.array([diamagnetic-np.vdot(result.source, solved).real, result.kappa, result.kappa])
    return result


def time_history_determinant():
    Q = np.array([[1., 1., 0.], [1., 3., 1.], [0., 1., 1.]])
    middle = (Q+np.eye(3))/2
    steps, duration, chi = 8, 3., .7
    step = duration/steps
    shift = np.roll(np.eye(steps), 1, axis=0)
    kinetic = chi*(2*np.eye(steps)-shift-shift.T)/step**2
    A0 = np.kron(kinetic, np.eye(3))+np.kron(np.eye(steps), middle)
    path = np.array([0., 0., 1., 1., 0., 1., 0., 1.])
    change = np.kron(np.diag(path-.5), Q-np.eye(3))
    values, basis = la.eigh(A0)
    invroot = (basis*(1/np.sqrt(values)))@basis.T
    spectrum = la.eigvalsh(invroot@change@invroot)
    radius = 1/np.sqrt(3)
    assert max(abs(spectrum)) <= radius+1e-12
    exact = np.sum(np.log1p(spectrum))/2
    trace_square = np.sum(spectrum*spectrum)
    rows = []
    for order in [2, 4, 8, 12]:
        series = sum((-1)**(n+1)*np.sum(spectrum**n)/(2*n) for n in range(1, order+1))
        bound = radius**(order-1)*trace_square/(2*(order+1)*(1-radius))
        assert abs(exact-series) <= bound+1e-13
        rows.append(dict(order=order, actual_error=float(abs(exact-series)), bound=float(bound)))
    return dict(euclidean_time_points=steps, relative_field_coordinates=3, matrix_dimension=24,
                actual_relative_radius=float(max(abs(spectrum))), universal_radius=float(radius),
                history=path.tolist(), truncation_rows=rows,
                scope='Finite time-grid determinant check; the trace-class argument removes this time grid at finite volume and duration.')


def matched_vertex(mean):
    solved, residual = reduced_inverse(mean.H0, mean.g, mean.source)
    correction = np.sqrt(mean.n)*solved.imag
    ids = [mean.quantum.lookup[(x, 4, 4)] for x in range(4, 8)]
    harmonic = np.arange(4., 8.)+correction[ids]
    gamma = float(mean.kappa*(harmonic[0]-harmonic[3])*(harmonic[1]-harmonic[2]))
    first, second = mean.quantum.derivatives()
    n = mean.n
    first_change = first[n:, n:]-first[:n, :n]
    second_change = second[n:, n:]-second[:n, :n]
    u, v = np.zeros(n), np.zeros(n)
    u[ids[0]], u[ids[3]] = 1., -1.
    v[ids[1]], v[ids[2]] = 1., -1.
    us, vs = sp.csr_matrix(u[:, None]), sp.csr_matrix(v[:, None])
    change = mean.kappa*(us@vs.T+vs@us.T)
    values = []
    eps = 1e-4
    for shift in [-eps, eps]:
        H = mean.H0+shift*change
        f = (mean.first+shift*first_change)@mean.g
        invf, _ = reduced_inverse(H, mean.g, f)
        diam = np.vdot(mean.g, (mean.second+shift*second_change)@mean.g).real/2
        values.append(float(diam-np.vdot(f, invf).real))
    derivative = (values[1]-values[0])/(2*eps)
    assert abs(derivative-2*gamma/n) < 1e-10
    return dict(harmonic_coordinates=harmonic.tolist(), matched_gamma=gamma,
                uncorrected_affine_gamma=3*mean.kappa,
                derivative_Dx_wrt_p=derivative, vertex_derivative_prediction=2*gamma/n,
                corrector_residual=residual)


class GaussianCarrier:
    """The actual two-cell (24,12,12) reference carrier, on relative fields."""
    def __init__(self, mean):
        self.kappa, self.p = mean.kappa, mean.p
        self.chi = 1/(6*self.kappa)
        coords, adj = rectangular_torus((24, 12, 12))
        self.n = len(coords)
        lookup = {x: i for i, x in enumerate(coords)}
        self.U = np.zeros((self.n, 4))
        for s in range(2):
            ids = [lookup[(12*s+x, 4, 4)] for x in range(4, 8)]
            self.U[ids[0], 2*s], self.U[ids[3], 2*s] = 1., -1.
            self.U[ids[1], 2*s+1], self.U[ids[2], 2*s+1] = 1., -1.
        self.Js = []
        for s in range(2):
            j = np.zeros((4, 4))
            j[2*s, 2*s+1] = j[2*s+1, 2*s] = self.kappa
            self.Js.append(j)
        us = sp.csr_matrix(self.U)
        self.A = self.kappa*(6*sp.eye(self.n)-adjacency_matrix(adj))
        self.A = (self.A+self.p*(us@sp.csr_matrix(sum(self.Js))@us.T)).tocsr()
        self.g = np.ones(self.n)/np.sqrt(self.n)
        assert la.norm(self.A@self.g) < 1e-12
        self.max_residual = 0.

    def gram(self, frequency):
        shift = self.chi*frequency**2
        operator = LinearOperator(self.A.shape,
            matvec=lambda x: self.A@x+shift*x+self.g*np.dot(self.g, x), dtype=float)
        invdiag = 1/(self.A.diagonal()+shift+1/self.n)
        preconditioner = LinearOperator(self.A.shape, matvec=lambda x: invdiag*x, dtype=float)
        solutions = []
        for j in range(4):
            solved, info = cg(operator, self.U[:, j], M=preconditioner, rtol=2e-12,
                              atol=2e-14, maxiter=5000)
            residual = la.norm(operator@solved-self.U[:, j])
            self.max_residual = max(self.max_residual, residual)
            assert info == 0 and residual < 1e-10
            solutions.append(solved)
        gram = self.U.T@np.column_stack(solutions)
        assert la.norm(gram-gram.T) < 1e-10
        return (gram+gram.T)/2

    def quadrature(self, nodes):
        points, weights = np.polynomial.legendre.leggauss(nodes)
        points, weights = (points+1)/2, weights/2
        mu, W = np.zeros(2), np.zeros((2, 2))
        eta_values = [.025, .05, .1, .2]
        energy = np.zeros(len(eta_values))
        for t, weight in zip(points, weights):
            frequency = t/(1-t)
            factor = weight/(1-t)**2/(2*np.pi)
            M = self.gram(frequency)
            e, ev = la.eigh(M)
            assert e[0] > 0
            sqrtM = (ev*np.sqrt(e))@ev.T
            changes = [sqrtM@j@sqrtM for j in self.Js]
            for i, x in enumerate(changes):
                mu[i] += factor*np.trace(x)
                for j, y in enumerate(changes):
                    W[i, j] += factor*np.trace(x@y)
            spectrum = la.eigvalsh(sum(changes))
            for i, eta in enumerate(eta_values):
                assert np.min(eta*spectrum) > -1
                energy[i] += factor*np.sum(np.log1p(eta*spectrum))
        return mu, W, energy, eta_values

    def audit(self):
        M0 = self.gram(0.)
        val, vec = la.eigh(M0)
        sqrtM0 = (vec*np.sqrt(val))@vec.T
        direction_radius = float(max(abs(la.eigvalsh(sqrtM0@sum(self.Js)@sqrtM0))))
        config_radii = []
        for bits in itertools.product([0., 1.], repeat=2):
            change = sum((bit-self.p)*j for bit, j in zip(bits, self.Js))
            radius = float(max(abs(la.eigvalsh(sqrtM0@change@sqrtM0))))
            assert radius <= 1/np.sqrt(3)+1e-12
            config_radii.append(dict(bits=list(bits), relative_radius=radius))
        first = self.quadrature(48)
        mu, W, energies, etas = self.quadrature(80)
        quadrature_change = max(float(np.max(abs(a-b))) for a, b in zip(first[:3], [mu, W, energies]))
        assert quadrature_change < 2e-8
        assert la.eigvalsh(W)[0] >= -1e-13 and W[0, 1] > 0
        total_W = float(np.sum(W))
        rows = []
        for eta, exact in zip(etas, energies):
            radius = eta*direction_radius
            assert radius < 1
            approx = eta*np.sum(mu)-eta*eta*total_W/2
            error = abs(exact-approx)
            bound = eta*eta*radius*total_W/(3*(1-radius))
            assert error <= bound+2e-10
            rows.append(dict(source_amplitude=eta, exact_gaussian_energy_shift=float(exact),
                             second_order_energy_shift=float(approx), remainder=float(error),
                             remainder_bound=float(bound), relative_radius=radius))
        return dict(vertices=self.n, relative_oscillators=self.n-1, geometry_sources=2,
                    periods=[24, 12, 12], vacuum_force=mu.tolist(), static_susceptibility=W.tolist(),
                    two_source_relative_radius=direction_radius,
                    full_configuration_relative_radii=config_radii,
                    quadrature_orders=[48, 80], quadrature_change=quadrature_change,
                    maximum_linear_solve_residual=float(self.max_residual), energy_rows=rows,
                    scope='Finite spatial carrier, full Gaussian oscillator Hilbert space; no occupation cutoff or infinite-volume fit.')


def oscillator_crosscheck():
    # Independent trace-square-root, imaginary-time, and Fock-state suppliers.
    chi = .7
    A = np.array([[2., -.2, .1], [-.2, 1.5, .15], [.1, .15, 1.1]])
    V = np.array([[0., .3, 0.], [.3, .1, -.2], [0., -.2, -.1]])
    values, basis = la.eigh(A)
    omega = np.sqrt(values/chi)
    rotated = basis.T@V@basis
    mu = np.sum(np.diag(rotated)/omega)/(4*chi)
    W = np.sum(rotated**2/(omega[:, None]*omega[None, :]*(omega[:, None]+omega[None, :])))/(4*chi*chi)
    def corr(time):
        C = (basis*(np.exp(-omega*time)/(2*chi*omega)))@basis.T
        return np.trace(V@C@V@C)/2
    W_time = 2*quad(corr, 0., np.inf, epsabs=1e-12)[0]
    assert abs(W-W_time) < 1e-12
    annih = np.diag(np.sqrt(np.arange(1, 3)), 1)
    qs = []
    for axis in range(3):
        pieces = [np.eye(3) for _ in range(3)]
        pieces[axis] = (annih+annih.T)/np.sqrt(2*chi*omega[axis])
        qs.append(np.kron(np.kron(pieces[0], pieces[1]), pieces[2]))
    F = sum(rotated[i, j]*(qs[i]@qs[j])/2 for i in range(3) for j in range(3))
    amplitude = F[:, 0].copy()
    assert abs(amplitude[0]-mu) < 1e-13
    amplitude[0] = 0.
    states = list(itertools.product(range(3), repeat=3))
    for state, coefficient in zip(states, amplitude):
        if sum(state) != 2:
            assert abs(coefficient) < 1e-13
    excitation = np.array([np.dot(omega, state) for state in states])
    W_fock = 2*np.sum(amplitude[1:]**2/excitation[1:])
    assert abs(W-W_fock) < 1e-13
    inverse_sqrt = (basis*(1/np.sqrt(values)))@basis.T
    radius_direction = max(abs(la.eigvalsh(inverse_sqrt@V@inverse_sqrt)))
    rows = []
    for eta in [.1, .2, .4]:
        exact = np.sum(np.sqrt(la.eigvalsh(A+eta*V)/chi)-omega)/2
        approximation = eta*mu-eta*eta*W/2
        radius = eta*radius_direction
        bound = eta*eta*radius*W/(3*(1-radius))
        assert abs(exact-approximation) <= bound+1e-13
        rows.append(dict(amplitude=eta, exact_energy_shift=float(exact),
                         second_order_error=float(abs(exact-approximation)), bound=float(bound)))
    return dict(oscillators=3, fock_dimension=27, susceptibility=float(W),
                imaginary_time_error=float(abs(W-W_time)), fock_error=float(abs(W-W_fock)),
                vacuum_creates_only_two_phonons=True, trace_square_root_rows=rows)


def continuum(mean, gamma):
    t, m = sy.symbols('t m', real=True)
    integrals = [sy.simplify(sy.sqrt(sy.pi)*sy.gamma(sy.Rational(2*n-1, 2))/sy.gamma(n))
                 for n in [4, 5, 6]]
    angular = 5-35*m+63*m*m
    assert sy.expand(integrals[0]-8*m*integrals[1]+16*m*m*integrals[2]-sy.pi*angular/16) == 0
    assert sy.expand(angular-(63*(m-sy.Rational(5, 18))**2+sy.Rational(5, 36))) == 0
    rows = []
    for mu2 in [0., 5/18, .5, 1.]:
        numeric = quad(lambda t: ((1+t*t)-4*mu2)**2/(1+t*t)**6,
                       -np.inf, np.inf, epsabs=1e-12)[0]
        expected = np.pi*(5-35*mu2+63*mu2*mu2)/16
        assert abs(numeric-expected) < 1e-12
        rows.append(dict(cosine_squared=mu2, angular_polynomial=5-35*mu2+63*mu2*mu2,
                         time_integral_error=float(abs(numeric-expected))))
    chi = 1/(6*mean.kappa)
    speeds = np.sqrt(6*mean.kappa*mean.D)
    prefactor = gamma*gamma/(32*np.pi**3*chi*chi*np.prod(speeds)**2*speeds[0]**4)
    spectral_prefactor = gamma*gamma/(320*np.pi*chi*chi*np.prod(speeds)*speeds[0]**4)
    frequency = .6
    # In acoustic coordinates, integrate the two-particle angular phase space.
    angular_average = quad(lambda z: z**4, -1., 1., epsabs=1e-13)[0]/2
    phase_space = gamma*gamma*frequency**4*angular_average/(64*np.pi*chi*chi*np.prod(speeds)*speeds[0]**4)
    assert abs(phase_space-spectral_prefactor*frequency**4) < 1e-14
    # Independent normalization: spatial integral of the Euclidean correlator
    # equals the Laplace transform of the zero-momentum spectral density.
    radial = quad(lambda r: r*r*((1+r*r)**(-4)-(8/3)*r*r*(1+r*r)**(-5)
                                +(16/5)*r**4*(1+r*r)**(-6)),
                  0., np.inf, epsabs=1e-13)[0]
    amplitude = 1/(4*np.pi*np.pi*chi*np.prod(speeds))
    euclidean_integral = 8*gamma*gamma*amplitude**2*np.prod(speeds)*4*np.pi*radial/speeds[0]**4
    spectral_integral = spectral_prefactor*24/(2*np.pi)
    assert abs(euclidean_integral-spectral_integral) < 1e-12
    return dict(time_integrals=[str(x) for x in integrals], angular_rows=rows,
                acoustic_speeds=speeds.tolist(), matched_gamma=gamma,
                static_kernel_prefactor=float(prefactor), kernel_formula='prefactor*(5-35*mu^2+63*mu^4)/R^7',
                zero_momentum_spectral_prefactor=float(spectral_prefactor),
                spectral_normalization_crosscheck_error=float(abs(euclidean_integral-spectral_integral)),
                spectral_formula='prefactor*omega^4*theta(omega); continuous two-phonon weight',
                scope='Exact Gaussian acoustic calculation with the cell-matched vertex; no proof of the full interacting quantum continuum.')


def main():
    root = Path(__file__).resolve().parents[1]
    mean = MeanCell()
    middle = change_reference(mean, .5)
    vertex = matched_vertex(middle)
    report = dict(uniform_relative_bound=local_bound(mean.p), physical_mean_vertex=matched_vertex(mean),
                  midpoint_vertex=vertex, finite_carrier=GaussianCarrier(middle).audit(),
                  time_history_determinant=time_history_determinant(), oscillator_crosscheck=oscillator_crosscheck(),
                  acoustic_prediction=continuum(middle, vertex['matched_gamma']))
    sources = ['INDUCED_GEOMETRY_INTERACTION.md', 'scripts/induced_geometry_audit.py',
               'UnifiedTheory/Audit/KFCausalInducedGeometry.lean', 'FINITE_GAP_GEOMETRY_FEEDBACK.md',
               'scripts/finite_gap_feedback_audit.py', 'COLLECTIVE_WAVE_SPACETIME.md',
               'scripts/collective_wave_audit.py', 'PROJECTED_GEOMETRY_AND_LOCAL_DYNAMICS.md']
    report['source_sha256'] = {name: hashlib.sha256((root/name).read_bytes()).hexdigest() for name in sources}
    report['scope'] = ('Exact Gaussian influence at finite spatial volume, a uniform relative form bound, '
                       'and leading two-phonon induced response. The acoustic pair potential is anisotropic '
                       'R^-7, with continuous spectral weight, not a demonstrated graviton. No resummed '
                       'interacting phase, physical spin-half phase, universal coupling, or Einstein equation.')
    (root/'data/induced_geometry_audit.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
