#!/usr/bin/env python3
"""Boundary-energy encoding tests and nonlinear dressing of a localized TT seed.

Supplied Einstein initial-data constraints; no microscopic gravity or TOE proof.
"""
import hashlib
import itertools
import json
from pathlib import Path

import numpy as np
import scipy.linalg as la
import sympy as sy
from numpy.polynomial.legendre import leggauss, legvander

from prepotential_lattice_bridge_audit import continuum_operators
from bond_tensor_audit import basis_matrices


def norm(a):
    return float(la.norm(a, 2))


def comm(a, b):
    return a @ b-b @ a


def boundary_operator_checks():
    rng, rows = np.random.default_rng(9112636), []
    for case in range(16):
        raw = rng.normal(size=(8, 8))+1j*rng.normal(size=(8, 8))
        unitary = la.qr(raw)[0]
        rank = 3+case % 2
        embedding = unitary[:, :rank]
        p = embedding @ embedding.conj().T
        q = np.eye(8)-p
        raw_b = rng.normal(size=(2, 2))+1j*rng.normal(size=(2, 2))
        raw_o = rng.normal(size=(2, 2))+1j*rng.normal(size=(2, 2))
        b = np.kron(np.eye(4), (raw_b+raw_b.conj().T)/2)
        o = np.kron((raw_o+raw_o.conj().T)/2, np.eye(4))
        assert norm(comm(b, o)) < 1e-13
        perturb = .02*(case % 3)*(p @ (raw+raw.conj().T) @ p)
        h = p @ b @ p+perturb+8*q
        hp, op, bp = p @ h @ p, p @ o @ p, p @ b @ p
        assert norm(comm(h, p)) < 1e-12
        epsilon = norm((h-b) @ p)
        delta = norm(hp-bp)
        b_leak, o_leak = norm(q @ b @ p), norm(q @ o @ p)
        measured = norm(comm(hp, op))
        assert norm(comm(bp, op)-(p @ o @ q @ b @ p-p @ b @ q @ o @ p)) < 1e-12
        strong_bound = 2*epsilon*norm(o)
        weak_bound = 2*delta*norm(op)+2*b_leak*o_leak
        assert measured <= strong_bound+1e-12
        assert measured <= weak_bound+1e-12
        # Test an independently chosen physical operator and its dressing bound.
        raw_a = rng.normal(size=(rank, rank))+1j*rng.normal(size=(rank, rank))
        a = embedding @ ((raw_a+raw_a.conj().T)/2) @ embedding.conj().T
        eta = norm((a-o) @ p)
        dressing_bound = 2*epsilon*norm(a)+2*norm(b @ p)*eta
        assert norm(comm(hp, a)) <= dressing_bound+1e-12
        t = .31
        evolution = la.expm(1j*t*hp)
        assert norm(evolution @ op @ evolution.conj().T-op) <= t*strong_bound+1e-12
        rows.append(dict(case=case, code_rank=rank,
                         physical_commutator_norm=measured,
                         boundary_intertwining_error=epsilon,
                         compression_error=delta,
                         boundary_leakage=b_leak, bulk_leakage=o_leak,
                         strong_commutator_bound=strong_bound,
                         compression_with_leakage_bound=weak_bound,
                         physical_dressing_error=eta,
                         physical_dressing_commutator_bound=dressing_bound))
    return dict(cases=rows, scope="Finite eight-state operator tests, with generic nonlocal projectors. The random Hamiltonians are not microscopic gravity models.")


def two_qubit_checks():
    rows = []
    b = np.kron(np.eye(2), np.diag([1., -1.]))
    o = np.kron(np.array([[0., 1.], [1., 0.]]), np.eye(2))
    for theta in [0., .2, .4, .7, 1., np.pi/2]:
        c, s = np.cos(theta), np.sin(theta)
        v = np.array([[1., 0.], [0., s], [0., c], [0., 0.]])
        p, bp, op = v @ v.T, v.T @ b @ v, v.T @ o @ v
        q = np.eye(4)-p
        assert norm(bp-np.diag([1., np.cos(2*theta)])) < 1e-13
        assert norm(op-c*np.array([[0., 1.], [1., 0.]])) < 1e-13
        assert abs(norm(comm(bp, op))-2*s*s*c) < 1e-13
        assert abs(norm(q @ b @ p)-2*s*c) < 1e-13
        assert abs(norm(q @ o @ p)-s) < 1e-13
        rows.append(dict(theta=theta, physical_commutator_norm=norm(comm(bp, op)),
                         predicted_commutator_norm=float(2*s*s*c),
                         boundary_leakage=norm(q @ b @ p),
                         bulk_leakage=norm(q @ o @ p)))
    return dict(cases=rows, scope="An exact compression-equality counterexample: disjoint operators can have noncommuting compressions when both leak out of the code.")


def prefix_code_checks():
    rows = []
    for size in [1, 2, 3, 4]:
        # Enumerate the full classical product basis, not just presumed code states.
        kernel, outside_min = [], float('inf')
        delta, omega = size+1., 1.
        for occupations in itertools.product([0, 1], repeat=size):
            for links in itertools.product(range(size+1), repeat=size):
                previous = (0,)+links[:-1]
                violation = sum((e-ep-n)**2 for e, ep, n in zip(links, previous, occupations))
                energy = delta*violation+omega*links[-1]
                if violation == 0:
                    kernel.append((occupations, links))
                    assert links == tuple(np.cumsum(occupations))
                    assert energy == sum(occupations)
                else:
                    outside_min = min(outside_min, energy)
        assert len(kernel) == 2**size
        assert outside_min >= delta > size*omega
        kernel_set = set(kernel)
        transitions = 0
        for occupations, links in kernel:
            for site in range(size):
                if occupations[site] != 0:
                    continue
                new_n = list(occupations)
                new_n[site] = 1
                new_links = tuple(e+int(j >= site) for j, e in enumerate(links))
                assert max(new_links) <= size
                assert (tuple(new_n), new_links) in kernel_set
                assert new_links[-1]-links[-1] == 1
                # The bare local flip is outside the exact physical space.
                assert (tuple(new_n), links) not in kernel_set
                transitions += 1
        rows.append(dict(size=size, full_product_dimension=2**size*(size+1)**size,
                         exact_code_dimension=len(kernel),
                         verified_dressed_creations=transitions,
                         maximum_code_energy=float(size*omega),
                         minimum_excluded_energy=float(outside_min),
                         link_dimension=size+1, penalty=delta))
    return dict(cases=rows, scope="Complete finite kernels and logical transitions for local prefix constraints. Link dimensions and the full-band protection penalty grow with size. There are no propagating tensor modes.")


def exact_tensor():
    xyz = sy.symbols('x y z', real=True)
    k = sy.symbols('kx ky kz', real=True)
    x, y, z = xyz
    cross = sy.Matrix([[0, -k[2], k[1]], [k[2], 0, -k[0]], [-k[1], k[0], 0]])
    seed = sy.diag(-1, -1, 2)
    curl = sy.I*(cross*seed-seed*cross)/2
    symbol = -cross*curl*cross.T
    phi = sy.exp(-sum(v*v for v in xyz)/2)
    tau = sy.zeros(3)
    for i, j in itertools.product(range(3), repeat=2):
        for powers, coefficient in sy.Poly(sy.expand(symbol[i, j]), *k).terms():
            derivative = phi
            for coordinate, power in zip(xyz, powers):
                derivative = sy.diff(derivative, coordinate, power)
            tau[i, j] += coefficient*(-sy.I)**sum(powers)*derivative
        tau[i, j] = sy.simplify(tau[i, j])
    assert tau == tau.T
    assert sy.simplify(sy.trace(tau)) == 0
    for i in range(3):
        assert sy.simplify(sum(sy.diff(tau[i, j], xyz[j]) for j in range(3))) == 0
    polynomial = sy.simplify(sy.trace(tau*tau)/phi**2)
    rho2 = x*x+y*y
    expected = sy.Rational(9, 2)*rho2*((rho2-4)**2+rho2*z*z)
    assert sy.expand(polynomial-expected) == 0
    moment = lambda n: sy.Integer(0) if n % 2 else sy.gamma(sy.Rational(n+1, 2))
    integral = sy.simplify(sum(c*sy.prod(moment(n) for n in powers)
                              for powers, c in sy.Poly(polynomial, *xyz).terms()))
    assert integral == 63*sy.pi**sy.Rational(3, 2)/2
    r, mu = sy.symbols('r mu', real=True)
    envelope = sy.Rational(9, 2)*r*r*(r**4+16)*sy.exp(-r*r)
    potential_bound = sy.integrate(r*envelope/8, (r, 0, sy.oo))
    assert potential_bound == sy.Rational(99, 16)
    angular_source = sy.Rational(9, 2)*r*r*((1-mu*mu)**2*(r**4-8*r*r)+16*(1-mu*mu))
    monopole = sy.integrate(angular_source, (mu, -1, 1))/2
    center = sy.integrate(r*monopole*sy.exp(-r*r)/8, (r, 0, sy.oo))
    assert center == sy.Rational(3, 2)
    # Check that the exact polynomial operator is the existing physical Cotton map.
    evaluate = sy.lambdify(k, symbol, 'numpy')
    basis = basis_matrices()
    seed_coordinates = np.array([np.sum(np.array(seed, float)*b) for b in basis])
    for momentum in [np.array([.2, -.4, .7]), np.array([0., 0., .3]), np.array([1., 2., 3.])]:
        cotton = continuum_operators(momentum)[3]
        predicted = sum(a*b for a, b in zip(cotton @ seed_coordinates, basis))
        assert la.norm(predicted-evaluate(*momentum)) < 2e-12
    return dict(trace_identically_zero=True, divergence_identically_zero=True,
                source_polynomial=str(sy.factor(polynomial)),
                exact_source_integral=str(integral),
                newton_potential_uniform_bound=str(potential_bound),
                leading_newton_potential_at_origin=str(center),
                scope="Exact symbolic localized TT data from the prepotential Cotton operator, its source norm and a continuum contraction bound.")


class AxisymmetricNewton:
    def __init__(self, nr, na, radius=8.):
        self.nr, self.na, self.radius = nr, na, radius
        self.dr = radius/nr
        self.r = (np.arange(nr)+.5)*self.dr
        self.mu, self.weights = leggauss(na)
        self.ell = np.arange(0, na, 2)
        self.legendre = legvander(self.mu, self.ell[-1])[:, self.ell]
        self.projection = ((self.legendre.T*self.weights)*
                           (2*self.ell+1)[:, None]/2)
        r2 = self.r[:, None]**2
        rho2, z2 = r2*(1-self.mu[None, :]**2), r2*self.mu[None, :]**2
        self.source = 4.5*rho2*((rho2-4)**2+rho2*z2)*np.exp(-r2)
        self.volume_weights = 2*np.pi*(self.dr*self.r**2)[:, None]*self.weights[None, :]
        lower = np.minimum(self.r[:, None], self.r[None, :])
        upper = np.maximum(self.r[:, None], self.r[None, :])
        self.kernels = np.array([
            (lower/upper)**ell/upper*(self.dr*self.r**2)[None, :]/(8*(2*ell+1))
            for ell in self.ell])

    def green(self, source):
        coefficients = source @ self.projection.T
        potentials = np.column_stack([kernel @ coefficients[:, j]
                                      for j, kernel in enumerate(self.kernels)])
        return potentials @ self.legendre.T

    def solve(self, amplitude):
        gamma = amplitude**2*99/16
        assert 7*gamma < 1
        linear = amplitude**2*self.green(self.source)
        u = np.zeros_like(self.source)
        for iteration in range(100):
            updated = amplitude**2*self.green(self.source*(1+u)**-7)
            step_error = np.max(abs(updated-u))
            u = updated
            if step_error < 1e-13:
                break
        else:
            raise AssertionError("Nonlinear iteration did not converge")
        effective = self.source*(1+u)**-7
        residual = float(np.max(abs(u-amplitude**2*self.green(effective))))
        assert residual < 1e-13
        assert min(u.ravel()) >= 0
        assert max(u.ravel()) <= gamma
        perturbation_error = float(np.max(abs(u-linear)))
        assert perturbation_error <= 7*gamma**2
        source_integral = np.sum(self.source*self.volume_weights)
        exact_integral = 63*np.pi**1.5/2
        assert abs(source_integral/exact_integral-1) < 1e-11
        bare_energy = amplitude**2*exact_integral/(16*np.pi)
        energy = amplitude**2*np.sum(effective*self.volume_weights)/(16*np.pi)
        assert bare_energy/(1+gamma)**7 <= energy <= bare_energy
        coefficients = effective @ self.projection.T
        moments = np.array([np.sum(self.dr*self.r**(ell+2)*coefficients[:, j])
                            for j, ell in enumerate(self.ell)])
        row = dict(radial_points=self.nr, angular_points=self.na, radius=self.radius,
                   amplitude=amplitude, contraction_upper_bound=7*gamma,
                   iterations=iteration+1, discrete_fixed_point_residual=residual,
                   maximum_conformal_change=float(max(u.ravel())),
                   nonlinear_minus_leading_uniform_error=perturbation_error,
                   continuum_perturbation_error_bound=7*gamma**2,
                   bare_TT_energy=float(bare_energy), ADM_energy=float(energy),
                   continuum_ADM_lower_bound=float(bare_energy/(1+gamma)**7))
        return row, moments

    def outer_flux(self, amplitude, moments, radius, energy):
        assert radius > self.radius
        coefficients = amplitude**2*moments/(8*(2*self.ell+1))
        u = (coefficients/radius**(self.ell+1)) @ self.legendre.T
        derivative = (-(self.ell+1)*coefficients/radius**(self.ell+2)) @ self.legendre.T
        # G=1. The conformal flux equals the truncated-source volume mass exactly.
        conformal_flux = -radius**2*np.sum(self.weights*derivative)
        metric_flux = -radius**2*np.sum(self.weights*(1+u)**3*derivative)
        assert abs(conformal_flux-energy) < 2e-13
        assert metric_flux > energy
        asymptotic_prediction = 3*energy/(2*radius)
        actual_error = metric_flux/energy-1
        assert abs(actual_error/asymptotic_prediction-1) < .015
        return dict(amplitude=amplitude, observation_radius=radius,
                    conformal_flux=float(conformal_flux),
                    finite_radius_ADM_metric_surface_expression=float(metric_flux),
                    limiting_ADM_energy=float(energy),
                    finite_radius_metric_relative_error=float(actual_error),
                    leading_relative_error_prediction=float(asymptotic_prediction),
                    metric_tail_monopole_coefficient=float(2*energy))


def conformal_checks():
    rows, outer, by_amplitude = [], [], {a: [] for a in [.05, .1, .14]}
    for nr, na in [(48, 8), (96, 12), (192, 16)]:
        solver = AxisymmetricNewton(nr, na)
        for amplitude in by_amplitude:
            row, moments = solver.solve(amplitude)
            rows.append(row)
            by_amplitude[amplitude].append(row['ADM_energy'])
            if nr == 192:
                for radius in [16., 32., 64.]:
                    outer.append(solver.outer_flux(amplitude, moments, radius, row['ADM_energy']))
    convergence = []
    for amplitude, values in by_amplitude.items():
        coarse_change, fine_change = abs(values[1]-values[0]), abs(values[2]-values[1])
        assert fine_change < .3*coarse_change
        convergence.append(dict(amplitude=amplitude, coarse_to_middle_change=coarse_change,
                                middle_to_fine_change=fine_change,
                                refinement_change_ratio=fine_change/coarse_change))
    return (dict(cases=rows, refinement=convergence,
                 scope="Nonlinear conformal Einstein initial data with an actual smooth TT seed, G=1. Discrete Newton-potential residuals and resolution comparisons are numerical evidence, not certified continuum discretization bounds."),
            dict(cases=outer, scope="Boundary flux for the numerically truncated source. The conformal flux is distinct from the finite-radius ADM metric surface expression, which approaches the same limiting mass."))


def main():
    root = Path(__file__).resolve().parents[1]
    conformal, flux = conformal_checks()
    report = dict(exact_TT_seed=exact_tensor(), boundary_operator_bounds=boundary_operator_checks(),
                  compression_counterexample=two_qubit_checks(), finite_prefix_code=prefix_code_checks(),
                  nonlinear_conformal_dressing=conformal, asymptotic_flux=flux)
    sources = ['GRAVITATIONAL_BOUNDARY_DRESSING.md',
               'scripts/gravitational_boundary_dressing_audit.py',
               'CAUSAL_VACUUM_SELECTION.md', 'PREPOTENTIAL_LATTICE_BRIDGE.md',
               'scripts/prepotential_lattice_bridge_audit.py', 'scripts/bond_tensor_audit.py',
               'NONLINEAR_TENSOR_BACKREACTION.md', 'COMPACT_CONSTRAINT_NORMALIZER.md',
               'SPIN_STATE_GAUGE_GEOMETRY.md', 'LOCAL_CAUSAL_CLOCK.md',
               'PROJECTED_GEOMETRY_AND_LOCAL_DYNAMICS.md']
    report['source_sha256'] = {p: hashlib.sha256((root/p).read_bytes()).hexdigest() for p in sources}
    report['scope'] = (
        'A quantitative boundary-energy bound requires nonlocal dressing or a change of '
        'the stated encoding assumptions for energy-changing bulk observables. A finite '
        'local prefix code demonstrates dressed logical transitions but is not gravity. '
        'A localized TT seed has a controlled small-amplitude asymptotically flat conformal '
        'completion with positive ADM energy and a compulsory metric tail. Einstein '
        'constraints and G are inputs. No microscopic gravitational phase, derived '
        'nonlinear evolution, universal coupling, Standard Model dynamics, or TOE is proved.')
    target = root/'data/gravitational_boundary_dressing_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    counts = {k: len(v['cases']) for k, v in report.items() if isinstance(v, dict) and 'cases' in v}
    print(json.dumps(dict(report=str(target), checks=counts, total_cases=sum(counts.values()),
                         exact_TT_identities=True, source_references=len(sources),
                         scope=report['scope']), indent=2))


if __name__ == '__main__':
    main()
