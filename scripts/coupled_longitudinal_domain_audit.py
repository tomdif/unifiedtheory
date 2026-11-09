#!/usr/bin/env python3
"""Finite and real-coordinate checks for the coupled longitudinal domain.

The source identity is tested in the actual finite simplex model, where
clock/source commutation is not imposed. Coordinate-flow and Gaussian
checks concern the stated commuting differential expression. They do not
identify an infinite operator limit or prove a common quantum domain.
"""
import hashlib
import json
from pathlib import Path

import numpy as np
import scipy
from scipy import integrate, linalg, optimize

from regularized_constraint_spin_model import RegularizedConstraintSpinModel, Parameters

NEW_MODULES = [
    'KFCausalQuadraticSourcePrimitive', 'KFCausalSourcePrimitiveQuadratures',
    'KFCausalTransverseDilationFlow', 'KFCausalCoupledLongitudinalFlow',
    'KFCausalCommutingClockReconstruction', 'KFCausalCoupledGaussianObstruction',
    'KFCausalTransverseDilationPullback', 'KFCausalTransverseDerivativeScaling',
    'KFCausalCoupledDampedGaussian',
]


def current(a, b):
    return (a@b+b@a)/2


def relative_error(a, b):
    return float(linalg.norm(a-b)/max(1., linalg.norm(a), linalg.norm(b)))


def finite_cases():
    cases = []
    for capacity in [2, 3, 4]:
        for correction in ['bare', 'second_order', 'exact']:
            for hbar in [.2, .7]:
                epsilon = .4
                model = RegularizedConstraintSpinModel(Parameters(
                    R=capacity, flavors=6, correction=correction, hbar=hbar,
                    mass2=0., quartic=0., vacuum=.03), epsilon)
                a, b, c, d, z = [op.toarray() for op in model.ann[1:]]
                transverse = [a, b, c, d]
                shear = c+c.conj().T+d+d.conj().T
                zskew = z-z.conj().T
                explicit = (-1j*hbar/4)*(sum(op@op-op.conj().T@op.conj().T
                    for op in transverse)+zskew@shear+shear@zskew)
                primitive = np.zeros_like(model.source)
                np.divide(model.source, 1j*model.charge_difference,
                    out=primitive, where=~model.same_charge)
                scale = np.sqrt(hbar/2)
                positions = [scale*(op+op.conj().T) for op in transverse]
                momenta = [-1j*scale*(op-op.conj().T) for op in transverse]
                pz = -1j*scale*zskew
                quadratures = sum(current(x, p) for x, p in zip(positions, momenta))/2
                quadratures += current(pz, positions[2]+positions[3])
                longitudinal = model.L-model.Lbar
                naive = linalg.solve(model.C, primitive, assume_a='pos')
                row = dict(capacity=capacity, correction=correction, hbar=hbar,
                    epsilon=epsilon, dimension=model.dim,
                    primitive_error=relative_error(primitive, explicit),
                    quadrature_error=relative_error(primitive, quadratures),
                    jordan_error=relative_error(current(model.C, longitudinal), primitive),
                    hermiticity_error=relative_error(primitive, primitive.conj().T),
                    clock_commutator_norm=float(linalg.norm(model.C@primitive-primitive@model.C)),
                    inverse_clock_jordan_residual=float(linalg.norm(current(model.C, naive)-primitive)))
                for key, value in row.items():
                    if key.endswith('_error'):
                        assert value < 2e-12, (key, row)
                # This actual finite cutoff is not a tensor-product truncation.
                assert row['clock_commutator_norm'] > 1e-5, row
                assert row['inverse_clock_jordan_residual'] > 1e-5, row
                cases.append(row)
    return cases


def transverse_matrix(t):
    scale = np.exp(t/2)
    matrix = np.diag([scale]*4+[1.])
    matrix[4, 2:4] = 2*(scale-1)
    return matrix


def transverse_velocity(x):
    return np.array([x[0]/2, x[1]/2, x[2]/2, x[3]/2, x[2]+x[3]])


def chart(epsilon, s):
    return np.exp(s)+epsilon*s


def phase(epsilon, s):
    return s-epsilon*np.exp(-s)


def chart_inverse(epsilon, q):
    left, right = -1., 1.
    while chart(epsilon, left) > q:
        left *= 2
    while chart(epsilon, right) < q:
        right *= 2
    return optimize.brentq(lambda s: chart(epsilon, s)-q, left, right,
        xtol=5e-15, rtol=1e-14)


def coupled(epsilon, t, state):
    s, x = state[0], state[1:]
    st = chart_inverse(epsilon, chart(epsilon, s)+t)
    theta = phase(epsilon, st)-phase(epsilon, s)
    return np.r_[st, transverse_matrix(theta)@x]


def straightening(epsilon, state):
    s, x = state[0], state[1:]
    return np.r_[chart(epsilon, s), transverse_matrix(-phase(epsilon, s))@x]


def flow_cases():
    rows = []
    x = np.array([.3, -.2, .4, .1, -.7])
    step = 2e-5
    for epsilon in [.1, 1., 2.]:
        for s in [-.3, .1, .7]:
            for t in [-.12, .08, .17]:
                u = -.07
                state = np.r_[s, x]
                evolved = coupled(epsilon, t, state)
                actual = (coupled(epsilon, t+step, state)-coupled(epsilon, t-step, state))/(2*step)
                expected = np.r_[1/(np.exp(evolved[0])+epsilon),
                    np.exp(-evolved[0])*transverse_velocity(evolved[1:])]
                target = straightening(epsilon, state)
                target[0] += t
                matrix = transverse_matrix(t)
                tx = matrix@x
                row = dict(epsilon=epsilon, s=s, t=t,
                    composition_error=relative_error(coupled(epsilon, u, evolved),
                                                       coupled(epsilon, t+u, state)),
                    inverse_error=relative_error(coupled(epsilon, -t, evolved), state),
                    straightening_error=relative_error(straightening(epsilon, evolved), target),
                    derivative_error=relative_error(actual, expected),
                    transverse_composition_error=relative_error(transverse_matrix(u)@matrix,
                                                                  transverse_matrix(t+u)),
                    determinant_error=float(abs(linalg.det(matrix)-np.exp(2*t))),
                    shear_invariant_error=float(abs(tx[4]-2*tx[2]-2*tx[3]-(x[4]-2*x[2]-2*x[3]))))
                for key, value in row.items():
                    if key.endswith('_error'):
                        assert value < 3e-8, (key, row)
                rows.append(row)
    return rows


def pullback_cases():
    rows = []
    x = np.array([.3, -.2, .4, .1, -.7])
    direction = np.array([1., 0., 0., 0., 0.])
    step = 2e-5
    for t in [-2., -.5, 0., .5, 2.]:
        inverse = transverse_matrix(-t)
        quadratic = inverse.T@inverse
        prefactor = np.exp(-t)*np.pi**(-5/4)

        def packet(y):
            return prefactor*np.exp(-(inverse@y)@(inverse@y)/2)

        # Independent Gaussian integration from the transformed quadratic matrix.
        mass = prefactor**2*np.pi**(5/2)/np.sqrt(linalg.det(quadratic))
        derivative_energy = mass*quadratic[0, 0]/2
        derivative = (packet(x+step*direction)-packet(x-step*direction))/(2*step)
        expected_derivative = -(quadratic@x)[0]*packet(x)
        row = dict(t=t, mass_error=float(abs(mass-1)),
            derivative_energy_error=float(abs(derivative_energy-np.exp(-t)/2)),
            derivative_error=float(abs(derivative-expected_derivative)))
        for key, value in row.items():
            if key.endswith('_error'):
                assert value < 3e-8, (key, row)
        rows.append(row)
    return rows


def damped_cases():
    rows = []
    for epsilon in [.1, .4, 1., 2.]:
        for a in [.5, 2*np.pi, 20.]:
            def log_weight(q):
                s = chart_inverse(epsilon, q)
                return -phase(epsilon, s)-a*q*q-2*epsilon*np.exp(-q/epsilon)

            # The Jacobian cancels when the weighted integral is written in q.
            # This finite-window quadrature is diagnostic; Lean proves integrability.
            integral, error = integrate.quad(lambda q: np.exp(log_weight(q)), -12., 12.,
                epsabs=2e-11, epsrel=2e-11, points=[0.])
            bound = np.exp(2)/epsilon*np.sqrt(np.pi/a)
            excess = max(log_weight(q)-(2-np.log(epsilon)-a*q*q)
                for q in np.linspace(-12., 12., 241))
            assert excess <= 1e-10, (epsilon, a, excess)
            assert 0 < integral < bound, (epsilon, a, integral, bound)
            rows.append(dict(epsilon=epsilon, gaussian_square_coefficient=a,
                clock_window=[-12., 12.], weighted_integral_in_window=float(integral),
                quadrature_error_estimate=float(error), gaussian_dominating_integral=float(bound),
                sampled_log_bound_excess=float(excess)))
    return rows


def main():
    finite, flows, pullbacks = finite_cases(), flow_cases(), pullback_cases()
    damped = damped_cases()
    tails = []
    for epsilon in [.01, .1, 1.]:
        for a in [0., 2*np.pi, 20.]:
            for x in [5., 10., 15., 20.]:
                s = -x
                value = np.log(np.exp(s)+epsilon)-phase(epsilon, s)-a*chart(epsilon, s)**2
                tails.append(dict(epsilon=epsilon, gaussian_square_coefficient=a,
                    negative_s=x, log_weighted_gaussian_density=float(value)))
    root = Path(__file__).resolve().parents[1]
    previous = json.loads((root/'data/regularized_homogeneous_evolution_audit.json').read_text())
    sources = list(previous['source_sha256'])+['scripts/coupled_longitudinal_domain_audit.py']
    sources += ['UnifiedTheory/Audit/'+name+'.lean' for name in NEW_MODULES]
    hashes = {p: hashlib.sha256((root/p).read_bytes()).hexdigest() for p in sources}
    assert all(hashes[p] == h for p, h in previous['source_sha256'].items())
    report = dict(finite_cases=finite, flow_cases=flows, pullback_cases=pullbacks,
        damped_gaussian_cases=damped,
        gaussian_tail_diagnostics=tails, source_sha256=hashes,
        numpy_version=np.__version__, scipy_version=scipy.__version__,
        lean_toolchain=(root/'lean-toolchain').read_text().strip(),
        scope=('Exact source and quadrature identities are checked in the actual finite '
            'six-mode simplex model, retaining its noncommuting clock and source. '
            'Complete coupled coordinate transport and norm-preserving transverse '
            'pullback concern the stated commuting differential expression. Lean '
            'proves the Gaussian weighted-energy divergence, independently of tail '
            'samples, and exact directional derivative-energy scaling. The resulting '
            'obstruction excludes this Gaussian product ansatz with nonzero transverse '
            'derivative energy; it is not a no-go theorem for all domains. An explicit '
            'additional negative-tail damping factor restores this weighted derivative '
            'energy, as proved in Lean by Gaussian domination and change of variables. '
            'Its exponential-longitudinal domain membership is not yet proved. Infinite '
            'operator identification, a full common finite-energy domain, capacity '
            'and regulator limits, physical identification and the TOE remain open.'))
    target = root/'data/coupled_longitudinal_domain_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print(target, ':', len(finite), 'finite cases,', len(flows), 'flow cases,',
        len(pullbacks), 'pullback cases,', len(damped), 'damped cases,',
        len(hashes), 'source hashes.')
    for label, rows in [('finite', finite), ('flow', flows), ('pullback', pullbacks)]:
        for key in rows[0]:
            if key.endswith('_error'):
                print(label, 'maximum', key, ':', max(row[key] for row in rows))
    print('Actual finite clock commutator norms:',
        min(row['clock_commutator_norm'] for row in finite), 'to',
        max(row['clock_commutator_norm'] for row in finite))


if __name__ == '__main__':
    main()
