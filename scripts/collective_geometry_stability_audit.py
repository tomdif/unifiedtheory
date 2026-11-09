#!/usr/bin/env python3
"""Uniform field-response bounds, factorized stability, and finite history sums."""
import hashlib
import itertools
import json
from pathlib import Path

import numpy as np
import scipy.linalg as la
import sympy as sy
from scipy.special import logsumexp

from induced_geometry_audit import GaussianCarrier, MeanCell, change_reference

B, D, KAPPA = .4, .31, .25
OMEGA = np.sqrt(D*D+4*B*B)
CHI = 1/(6*KAPPA)
RESPONSE_BOUND = np.sqrt(3)*KAPPA/2


def local_certificate():
    coords = list(itertools.product(range(4), range(3), range(3)))
    index = {x: i for i, x in enumerate(coords)}
    edges = []
    for i, x in enumerate(coords):
        for axis in range(3):
            y = list(x)
            y[axis] += 1
            if tuple(y) in index:
                edges.append((i, index[tuple(y)]))
    ids = [index[(x, 1, 1)] for x in range(4)]
    U = sy.zeros(36, 2)
    U[ids[0], 0], U[ids[3], 0] = 1, -1
    U[ids[1], 1], U[ids[2], 1] = 1, -1
    rows = []
    for occupied in [0, 1]:
        local_edges = list(edges)
        if occupied:
            local_edges.remove((ids[0], ids[1]))
            local_edges.remove((ids[2], ids[3]))
            local_edges.extend([(ids[0], ids[2]), (ids[1], ids[3])])
        L = sy.zeros(36)
        for i, j in local_edges:
            L[i, i] += 1
            L[j, j] += 1
            L[i, j] -= 1
            L[j, i] -= 1
        potential = sy.zeros(1, 2).col_join(L[1:, 1:].inv()*U[1:, :])
        assert L*potential == U
        resistance = U.T*potential
        assert potential.T*L*potential == resistance
        remainder = sy.eye(2)-resistance
        assert remainder[0, 0] > 0 and remainder.det() > 0
        rows.append(dict(occupied=occupied, vertices=36, edges=len(local_edges),
                         resistance=[[str(resistance[i, j]) for j in range(2)] for i in range(2)],
                         potential=[[str(potential[i, j]) for j in range(2)] for i in range(36)],
                         largest_resistance_eigenvalue=float(la.eigvalsh(np.array(resistance, dtype=float))[-1]),
                         exact_divergence_and_energy_identities=True))
    return dict(box=[4, 3, 3], source_columns='e_a-e_d, e_b-e_c',
                uniform_operator_inequality='U U^T <= L(m), all m in [0,1]^M', certificates=rows)


class ResponseCache:
    def __init__(self):
        self.carrier = GaussianCarrier(change_reference(MeanCell(), .5))
        self.cache = {}
        points, weights = np.polynomial.legendre.leggauss(80)
        self.nodes, self.weights = (points+1)/2, weights/2
        self.roots = []
        for t in self.nodes:
            gram = self.gram(t/(1-t))
            e, v = la.eigh(gram)
            self.roots.append((v*np.sqrt(e))@v.T)

    def gram(self, frequency):
        key = float(frequency)
        if key not in self.cache:
            value = self.carrier.gram(frequency)
            envelope = 2/(CHI*frequency**2+2*KAPPA)
            assert la.eigvalsh(value)[-1] <= envelope+1e-10
            self.cache[key] = value
        return self.cache[key]

    def evaluate(self, occupations):
        change = sum((m-.5)*j for m, j in zip(occupations, self.carrier.Js))
        mu, W, energy = np.zeros(2), np.zeros((2, 2)), 0.
        for t, weight, root in zip(self.nodes, self.weights, self.roots):
            relative = root@change@root
            value, basis = la.eigh(relative)
            assert value[0] > -1
            updated = root@((basis*(1/(1+value)))@basis.T)@root
            factor = weight/(1-t)**2/(2*np.pi)
            energy += factor*np.sum(np.log1p(value))
            for i, a in enumerate(self.carrier.Js):
                mu[i] += factor*np.trace(a@updated)
                for j, b in enumerate(self.carrier.Js):
                    W[i, j] += factor*np.trace(a@updated@b@updated)
        assert la.eigvalsh(W)[0] >= -1e-12
        assert la.eigvalsh(W)[-1] <= RESPONSE_BOUND+1e-10
        return energy, mu, W


def nonlinear_variational(cache):
    random = np.random.default_rng(4137)
    rows = []
    for m in [[0., 0.], [1., 1.], [0., 1.], [.5, .5]]+random.uniform(size=(8, 2)).tolist():
        _, mu, W = cache.evaluate(m)
        rows.append(dict(occupations=m, vacuum_force=mu.tolist(),
                         largest_field_susceptibility=float(la.eigvalsh(W)[-1])))
    p0 = (1-D/OMEGA)/2
    solutions = []
    for scale in [1., .5, .2]:
        ratio = RESPONSE_BOUND/(4*scale*B)
        assert ratio < 1
        m = np.array([.2, .8])
        for iteration in range(100):
            _, mu, W = cache.evaluate(m)
            effective_bias = scale*D+mu
            gap = np.hypot(effective_bias, 2*scale*B)
            target = (1-effective_bias/gap)/2
            residual = float(la.norm(target-m))
            if residual < 2e-12:
                break
            m = target
        else:
            raise AssertionError('fixed point failed')
        assert abs(m[0]-m[1]) < 1e-10
        curvature = scale*B/(2*(m*(1-m))**1.5)
        hessian = np.diag(curvature)-W
        margin = 4*scale*B-RESPONSE_BOUND
        assert la.eigvalsh(hessian)[0] >= margin
        response = la.inv(hessian)
        assert la.eigvalsh(response)[-1] <= 1/margin
        solutions.append(dict(geometry_scale=scale, uncorrected_occupancy=float(p0),
                              optimized_occupancy=m.tolist(), vacuum_force=mu.tolist(),
                              local_effective_spin_gap=gap.tolist(), iterations=iteration+1,
                              fixed_point_residual=residual,
                              a_posteriori_distance_bound=residual/(1-ratio),
                              contraction_bound=ratio, uniform_curvature_margin=margin,
                              variational_hessian_eigenvalues=la.eigvalsh(hessian).tolist(),
                              quadratic_static_response=response.tolist()))
    return dict(uniform_response_bound=float(RESPONSE_BOUND),
                sufficient_geometry_scale=float(RESPONSE_BOUND/(4*B)),
                nonlinear_source_checks=rows, solutions=solutions,
                scope='Exact optimum among geometry-field factorized states; not the full entangled ground state or an exact spectral gap.')


def finite_histories(cache, steps, beta=2.):
    dt = beta/steps
    frequencies = np.sqrt(2*(1-np.cos(2*np.pi*np.arange(steps)/steps)))/dt
    grams = [cache.gram(float(w)) for w in frequencies]
    time_gram = np.block([[sum(np.cos(2*np.pi*n*(i-j)/steps)*grams[n] for n in range(steps))/steps
                           for j in range(steps)] for i in range(steps)])
    e, v = la.eigh(time_gram)
    assert e[0] > 0
    root = (v*np.sqrt(e))@v.T
    coefficients = []
    for j in range(2*steps):
        i = 2*j
        coefficients.append(KAPPA*(np.outer(root[:, i], root[:, i+1])+np.outer(root[:, i+1], root[:, i])))
    coefficients = np.array(coefficients)
    geometry = np.array([[(OMEGA-D)/2, -B], [-B, (OMEGA+D)/2]])
    transfer = la.expm(-dt*geometry)
    assert np.min(transfer) > 0
    histories = 2**(2*steps)
    orders = [2, 4, 8, 12]
    radius = 1/np.sqrt(3)
    cgrid = KAPPA*KAPPA*np.sum(4/(CHI*frequencies**2+2*KAPPA)**2)/beta
    epsilons = [cgrid*radius**(order-1)/(4*(order+1)*(1-radius)) for order in orders]
    log_weights, exact_gamma, approximate_gamma, averages = [], [], [], []
    largest_error = np.zeros(4)
    largest_trace = 0.
    for start in range(0, histories, 256):
        labels = np.arange(start, min(histories, start+256), dtype=np.uint64)
        bits = ((labels[:, None] >> np.arange(2*steps, dtype=np.uint64)) & 1).astype(int)
        relative = ((bits-.5)@coefficients.reshape(2*steps, -1)).reshape(-1, 4*steps, 4*steps)
        spectrum = np.linalg.eigvalsh(relative)
        assert np.max(abs(spectrum)) <= radius+1e-11
        gamma = np.sum(np.log1p(spectrum), axis=1)/2
        trace_square = np.sum(spectrum*spectrum, axis=1)
        largest_trace = max(largest_trace, float(max(trace_square)))
        assert max(trace_square) <= cgrid*beta+1e-10  # M=2, so C beta M/2=C beta.
        power, series, approx = np.ones_like(spectrum), np.zeros(len(labels)), []
        for order in range(1, 13):
            power *= spectrum
            series += (-1)**(order+1)*np.sum(power, axis=1)/(2*order)
            if order in orders:
                approx.append(series.copy())
                index = orders.index(order)
                errors = abs(series-gamma)
                largest_error[index] = max(largest_error[index], float(max(errors)))
                bounds = radius**(order-1)*trace_square/(2*(order+1)*(1-radius))
                assert np.all(errors <= bounds+1e-11)
        path = bits.reshape(-1, steps, 2)
        successor = np.roll(path, -1, axis=1)
        logs = np.sum(np.log(transfer[path, successor]), axis=(1, 2))
        log_weights.extend(logs.tolist())
        exact_gamma.extend(gamma.tolist())
        approximate_gamma.extend(np.column_stack(approx).tolist())
        averages.extend(np.mean(path, axis=1).tolist())
    log_weights = np.asarray(log_weights)
    exact_gamma, approximate_gamma, averages = map(np.asarray, [exact_gamma, approximate_gamma, averages])
    log_z0 = logsumexp(log_weights)
    assert abs(log_z0-2*np.log1p(np.exp(-beta*OMEGA))) < 1e-12
    log_z = logsumexp(log_weights-exact_gamma)
    normalized = np.exp(log_weights-exact_gamma-log_z)
    mean = normalized@averages
    centered = averages-mean
    response = beta*(centered.T@(normalized[:, None]*centered))
    free_energy = -(log_z-log_z0)/(2*beta)
    approximations = []
    for j, order in enumerate(orders):
        log_approx = logsumexp(log_weights-approximate_gamma[:, j])
        free_approx = -(log_approx-log_z0)/(2*beta)
        error = abs(free_approx-free_energy)
        assert error <= epsilons[j]+1e-12
        approximations.append(dict(order=order, free_energy_density_error=float(error),
                                   uniform_error_bound=float(epsilons[j]),
                                   largest_history_action_error=float(largest_error[j])))
    return dict(time_steps=steps, inverse_temperature=beta, histories_enumerated=histories,
                source_matrix_dimension=4*steps, gaussian_field_vertices=cache.carrier.n,
                finite_grid_response_constant=float(cgrid), maximum_trace_square=largest_trace,
                exact_grid_free_energy_shift_per_switch=float(free_energy),
                exact_grid_occupancy=mean.tolist(), exact_grid_static_response=response.tolist(),
                bare_finite_temperature_occupancy=float((1-D/OMEGA*np.tanh(beta*OMEGA/2))/2),
                truncation_rows=approximations,
                scope='Full interacting history sum on this finite Euclidean time grid; no claimed time-grid error rate, zero-temperature spectrum, or thermodynamic phase.')


def temperature_bounds():
    mass_frequency = np.sqrt(12)*KAPPA
    rows = []
    for beta in [1., 2., 4., 8., 16., 32.]:
        x = beta*mass_frequency/2
        value = RESPONSE_BOUND*(1/np.tanh(x)+x/np.sinh(x)**2)
        modes = 2*np.pi*np.arange(-20000, 20001)/beta
        numeric = KAPPA*KAPPA*np.sum(4/(CHI*modes*modes+2*KAPPA)**2)/beta
        assert abs(value-numeric) < 2e-10
        rows.append(dict(beta=beta, uniform_history_curvature_bound=float(value),
                         direct_sum_error=float(abs(value-numeric))))
    errors = {str(order): float(RESPONSE_BOUND*(1/np.sqrt(3))**(order-1)/
                               (4*(order+1)*(1-1/np.sqrt(3)))) for order in [2, 4, 8, 12, 16]}
    return dict(thermal_rows=rows, zero_temperature_bound=float(RESPONSE_BOUND),
                zero_temperature_free_energy_density_errors=errors)


def main():
    root = Path(__file__).resolve().parents[1]
    cache = ResponseCache()
    report = dict(local_flow_certificate=local_certificate(), temperature_bounds=temperature_bounds(),
                  factorized_stability=nonlinear_variational(cache),
                  finite_history_sums=[finite_histories(cache, steps) for steps in [4, 6, 8]])
    sources = ['COLLECTIVE_GEOMETRY_STABILITY.md', 'scripts/collective_geometry_stability_audit.py',
               'UnifiedTheory/Audit/KFCausalGeometryStability.lean', 'INDUCED_GEOMETRY_INTERACTION.md',
               'scripts/induced_geometry_audit.py', 'FINITE_GAP_GEOMETRY_FEEDBACK.md',
               'COLLECTIVE_WAVE_SPACETIME.md', 'PROJECTED_GEOMETRY_AND_LOCAL_DYNAMICS.md']
    report['source_sha256'] = {name: hashlib.sha256((root/name).read_bytes()).hexdigest() for name in sources}
    report['scope'] = ('Uniform nonlinear Gaussian influence curvature and intensive determinant-error bounds; '
                       'unique stable factorized variational branch; exact finite-time-grid interacting history sums. '
                       'No proof of the entangled thermodynamic phase, a graviton pole, physical spin-half order, or Einstein gravity.')
    (root/'data/collective_geometry_stability_audit.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
