#!/usr/bin/env python3
"""A local staggered prepotential action with its actual reduced brackets.

Constructs a classical linear-gravity lattice benchmark. It is not a
finite-spin Hamiltonian realization or a nonlinear Einstein derivation.
"""
from functools import lru_cache
import hashlib
import itertools
import json
from pathlib import Path

import numpy as np
import scipy.linalg as la
import sympy as sy

from bond_tensor_audit import basis_matrices, matrix_blocks


def component_basis():
    out = [sy.diag(*[int(i == j) for j in range(3)]) for i in range(3)]
    for i, j in [(0, 1), (1, 2), (2, 0)]:
        e = sy.zeros(3)
        e[i, j] = e[j, i] = 1
        out.append(e)
    return out


@lru_cache(maxsize=1)
def exact_stencils():
    k = sy.symbols('kx ky kz', real=True)
    half = sy.symbols('tx ty tz', nonzero=True)
    w = sy.symbols('wx wy wz', nonzero=True)
    cross = sy.Matrix([[0, -k[2], k[1]], [k[2], 0, -k[0]], [-k[1], k[0], 0]])
    basis = component_basis()
    curvature = [-cross*e*cross.T for e in basis]
    symmetric_curl = [sy.I*(cross*e-e*cross)/2 for e in basis]
    energy = sy.Matrix(6, 6, lambda i, j: sy.expand(
        sy.trace(curvature[i]*curvature[j])-
        sy.trace(curvature[i])*sy.trace(curvature[j])/2))
    cotton = sy.Matrix(6, 6, lambda i, j: sy.expand(sy.trace(curvature[i]*symmetric_curl[j])))
    vector, k2 = sy.Matrix(k), sum(v*v for v in k)
    inverse_pairing = sy.diag(1, 1, 1, sy.Rational(1, 2), sy.Rational(1, 2), sy.Rational(1, 2))
    for r, s in zip(curvature, symmetric_curl):
        assert (r*vector).applyfunc(sy.expand) == sy.zeros(3, 1)
        assert sy.expand((vector.T*s*vector)[0]-k2*sy.trace(s)) == 0
    assert (cotton.conjugate().T-cotton).applyfunc(sy.expand) == sy.zeros(6)
    assert (cotton*inverse_pairing*cotton-k2*energy).applyfunc(sy.expand) == sy.zeros(6)
    assert (energy*inverse_pairing*energy-k2*k2*energy).applyfunc(sy.expand) == sy.zeros(6)
    phases = [half[0]**2, half[1]**2, half[2]**2,
              half[0]*half[1], half[1]*half[2], half[2]*half[0]]
    substitution = {k[i]: (half[i]-1/half[i])/sy.I for i in range(3)}

    def stagger(matrix, shift):
        result, stencil = sy.zeros(6), []
        for i, j in itertools.product(range(6), repeat=2):
            expr = sy.expand(shift*phases[j]/phases[i]*matrix[i, j].subs(substitution))
            for term in sy.Add.make_args(expr):
                if term == 0:
                    continue
                powers = term.as_powers_dict()
                exponents = [powers.get(v, 0) for v in half]
                assert all(p % 2 == 0 for p in exponents)
                coefficient = sy.cancel(term/sy.prod(v**p for v, p in zip(half, exponents)))
                assert coefficient.is_Rational
                offset = tuple(int(p//2) for p in exponents)
                result[i, j] += coefficient*sy.prod(v**p for v, p in zip(w, offset))
                stencil.append((i, j, offset, coefficient))
        return result, stencil

    q, qs = stagger(energy, 1)
    o, os = stagger(cotton, sy.prod(half))
    gauge = sy.zeros(6, 4)
    backward = [1-1/v for v in w]
    for i in range(3):
        gauge[i, i] = 2*backward[i]
        gauge[i, 3] = 1/w[i]
    for row, (i, j) in enumerate([(0, 1), (1, 2), (2, 0)], 3):
        gauge[row, i], gauge[row, j] = backward[j], backward[i]
    star = lambda m: m.T.subs({v: 1/v for v in w}, simultaneous=True)
    assert (q*gauge).applyfunc(sy.expand) == sy.zeros(6, 4)
    assert (o*gauge).applyfunc(sy.expand) == sy.zeros(6, 4)
    assert (star(o)*gauge).applyfunc(sy.expand) == sy.zeros(6, 4)
    assert (star(q)-q).applyfunc(sy.expand) == sy.zeros(6)
    assert (star(o)-o/sy.prod(w)).applyfunc(sy.expand) == sy.zeros(6)

    def entries(stencil):
        return [dict(row=i, column=j, shift=list(offset), coefficient=str(c))
                for i, j, offset, c in stencil]
    report = dict(exact_energy_gauge_null=True, exact_kinetic_gauge_null_on_both_sides=True,
                  exact_prepotential_metric_constraints=True,
                  exact_cotton_square_equals_momentum_squared_energy=True,
                  exact_energy_projector_polynomial_identity=True,
                  exact_real_energy_self_adjoint=True,
                  kinetic_adjoint_translation='O* = (wx wy wz)^(-1) O',
                  energy_term_count=len(qs), kinetic_term_count=len(os),
                  maximum_l1_offset=max(sum(abs(v) for v in offset) for _, _, offset, _ in qs+os),
                  energy_coefficient_denominators=sorted(set(int(c.q) for _, _, _, c in qs)),
                  kinetic_coefficient_denominators=sorted(set(int(c.q) for _, _, _, c in os)),
                  energy_stencil=entries(qs), kinetic_stencil=entries(os),
                  gauge_symbol=[[str(v) for v in gauge.row(i)] for i in range(6)])
    return w, q, o, gauge, qs, os, report


def continuum_operators(k):
    basis = basis_matrices()
    cross = np.array([[0., -k[2], k[1]], [k[2], 0., -k[0]], [-k[1], k[0], 0.]])
    r = np.column_stack([[np.sum(f*(-cross @ e @ cross.T)) for f in basis] for e in basis])
    s = np.column_stack([[np.sum(f*(.5j*(cross @ e-e @ cross))) for f in basis] for e in basis])
    kinetic, potential, _, _, _, _, _, tt = matrix_blocks(k)
    q = r.T @ kinetic @ r
    o = r.T @ s
    return r, s, q, o, potential, tt


def symbol_checks(symbols):
    w, q, o, gauge, _, _, _ = symbols
    qfun, ofun, gfun = [sy.lambdify(w, v, 'numpy') for v in [q, o, gauge]]
    rng, rows = np.random.default_rng(9112610), []
    scale = np.diag([1., 1., 1., np.sqrt(2), np.sqrt(2), np.sqrt(2)])
    offsets = np.array([[1, 0, 0], [0, 1, 0], [0, 0, 1],
                        [.5, .5, 0], [0, .5, .5], [.5, 0, .5]])
    special = [np.array(k)*np.pi for k in [(1, 0, 0), (1, 1, 0), (1, 1, 1)]]
    momenta = special+[rng.uniform(-np.pi, np.pi, 3) for _ in range(45)]
    for index, k in enumerate(momenta):
        v = 2*np.sin(k/2)
        v2 = float(v @ v)
        r, s, qc, oc, potential, tt = continuum_operators(v)
        assert la.norm(qc-v2*v2*tt) < 1e-10
        assert la.norm(oc @ oc-v2**3*tt) < 1e-10
        assert la.norm(oc-oc.conj().T) < 1e-11
        assert la.norm(s.conj().T @ potential @ s-qc) < 1e-10
        phase = np.diag(np.exp(1j*(offsets @ k)))
        expected_q = phase.conj().T @ scale @ qc @ scale @ phase
        expected_o = np.exp(.5j*np.sum(k))*phase.conj().T @ scale @ oc @ scale @ phase
        actual_q = np.asarray(qfun(*np.exp(1j*k)), dtype=complex)
        actual_o = np.asarray(ofun(*np.exp(1j*k)), dtype=complex)
        actual_g = np.asarray(gfun(*np.exp(1j*k)), dtype=complex)
        error = max(la.norm(actual_q-expected_q), la.norm(actual_o-expected_o))
        assert error < 3e-10
        assert np.linalg.matrix_rank(actual_g, tol=1e-10) == 4
        assert np.linalg.matrix_rank(actual_o, tol=1e-9) == 2
        assert np.linalg.matrix_rank(actual_q, tol=1e-9) == 2
        assert min(la.eigvalsh(actual_q)) > -1e-10
        # Work in the orthonormal TT frame, then pull back to the lattice components.
        physical = la.eigh(tt)[1][:, -2:]
        embedding = la.solve(scale @ phase, physical)
        qt = embedding.conj().T @ actual_q @ embedding
        ot = embedding.conj().T @ actual_o @ embedding
        form = np.block([[np.zeros((2, 2)), ot], [-ot.conj().T, np.zeros((2, 2))]])
        J, g = .7, 1.3
        energy = la.block_diag(J*qt, g*qt)
        flow = la.solve(form, energy)
        frequencies = np.sort(np.abs(la.eigvals(flow).imag))
        assert np.max(abs(frequencies-np.sqrt(J*g*v2))) < 1e-10
        # Pullback of the original tensor one-form, not an independent canonical assignment.
        assert la.norm(physical.conj().T @ oc @ physical-
                       (r @ physical).conj().T @ (s @ physical)) < 1e-11
        rows.append(dict(case=index, momentum=k.tolist(), staggered_squared_momentum=v2,
                         polynomial_symbol_error=float(error), gauge_rank=4,
                         physical_presymplectic_rank=4,
                         frequencies=frequencies.tolist(), expected_frequency=float(np.sqrt(J*g*v2)),
                         corner_case=bool(index < 3)))
    return dict(cases=rows, scope='Exact local Laurent stencils agree with the staggered continuum tensor symbols throughout the Brillouin zone. Reduction uses the noncanonical kinetic form. Checks include the zone corners, where centered derivatives would have unwanted zeros.')


def lattice_matrix(stencil, length):
    volume = length**3
    sites = list(itertools.product(range(length), repeat=3))
    lookup = {x: i for i, x in enumerate(sites)}
    result = np.zeros((6*volume, 6*volume))
    for x in sites:
        for row, col, offset, coefficient in stencil:
            y = tuple((x[i]+offset[i]) % length for i in range(3))
            result[row*volume+lookup[x], col*volume+lookup[y]] += float(coefficient)
    return result


def full_lattice_checks(symbols):
    _, _, _, _, qs, os, _ = symbols
    rows = []
    for length in [2, 3, 4, 5]:
        volume = length**3
        q, o = lattice_matrix(qs, length), lattice_matrix(os, length)
        assert la.norm(q-q.T) < 1e-12
        eigenvalues, eigenvectors = la.eigh(q)
        rank = int(np.sum(eigenvalues > 1e-8))
        assert rank == 2*(volume-1)
        assert min(eigenvalues) > -1e-10
        image = eigenvectors[:, -rank:]
        kernel = eigenvectors[:, :-rank]
        assert max(la.norm(o @ kernel), la.norm(o.T @ kernel)) < 2e-10
        qt, ot = image.T @ q @ image, image.T @ o @ image
        form = np.block([[np.zeros_like(ot), ot], [-ot.T, np.zeros_like(ot)]])
        energy = la.block_diag(qt, qt)
        inverse = la.inv(form)
        assert la.norm(inverse+inverse.T) < 2e-11
        lower = la.cholesky(energy, lower=True)
        all_frequencies = la.eigvalsh(1j*lower.T @ inverse @ lower)
        positive = all_frequencies[rank:]
        expected = []
        for n in itertools.product(range(length), repeat=3):
            if n != (0, 0, 0):
                momentum = 2*np.pi*np.array(n)/length
                expected += [float(la.norm(2*np.sin(momentum/2)))]*2
        expected = np.sort(expected)
        error = np.max(abs(positive-expected))
        assert error < 2e-10
        # Gauge-invariant kinetic currents have the original finite-range O bracket.
        current_map = np.block([[np.zeros_like(q), o], [o.T, np.zeros_like(q)]])
        embedding = la.block_diag(image, image)
        current_bracket = current_map @ embedding @ inverse @ embedding.T @ current_map.T
        target = np.block([[np.zeros_like(q), o], [-o.T, np.zeros_like(q)]])
        current_error = la.norm(current_bracket-target)
        assert current_error < 1e-8
        rows.append(dict(length=length, volume=volume, energy_rank=rank,
                         physical_phase_dimension=2*rank, canonical_pair_count=rank,
                         omitted_homogeneous_prepotential_coordinates=12,
                         smallest_frequency=float(positive[0]),
                         largest_full_spectrum_error=float(error),
                         local_current_bracket_error=float(current_error)))
    return dict(cases=rows, scope='Independent dense real-space reductions of complete periodic lattices. Positivity, all physical frequencies, null directions and local current brackets are checked without using individual Fourier blocks to construct the reduced matrices.')


def continuum_and_bracket_checks():
    rows = []
    directions = [np.array(v, float) for v in [(1, 0, 0), (1, 1, 1), (1, 2, -3)]]
    for direction in directions:
        direction /= la.norm(direction)
        physical_k = .8*direction
        for spacing in [1., .5, .25, .125]:
            v = 2*np.sin(spacing*physical_k/2)/spacing
            r, s, q, o, _, tt = continuum_operators(v)
            image = la.eigh(tt)[1][:, -2:]
            restricted = image.conj().T @ o @ image
            inverse_norm = la.norm(la.inv(restricted), 2)
            assert abs(inverse_norm*la.norm(v)**3-1) < 1e-12
            actual, continuum = la.norm(v), la.norm(physical_k)
            error = abs(actual-continuum)
            bound = spacing**2*continuum**3/24
            assert error <= bound+1e-14
            rows.append(dict(direction=direction.tolist(), spacing=spacing,
                             frequency_error=float(error), analytical_error_bound=float(bound),
                             inverse_kinetic_norm=float(inverse_norm),
                             inverse_norm_times_momentum_cubed=float(inverse_norm*la.norm(v)**3)))
    return dict(cases=rows, scope='The lattice wave has an explicit second-order dispersion error bound. The inverse kinetic form scales as momentum^(-3), so prepotentials cannot be assigned independent local canonical brackets.')


def metric_response_checks():
    rows, J, g = [], .7, 1.3
    for direction in [np.array(v, float) for v in [(1, 0, 0), (1, 1, 1), (1, 2, -3)]]:
        direction /= la.norm(direction)
        for radius in [.02, .1, .4, 1.]:
            k = radius*direction
            r, s, q, o, _, tt = continuum_operators(k)
            image = la.eigh(tt)[1][:, -2:]
            rt, st, qt, ot = [image.conj().T @ a @ image for a in [r, s, q, o]]
            form = np.block([[np.zeros((2, 2)), ot], [-ot.conj().T, np.zeros((2, 2))]])
            energy = la.block_diag(J*qt, g*qt)
            metric_map = np.concatenate([np.zeros((2, 2)), st], axis=1)
            canonical_map = la.block_diag(rt, st)
            expected_bracket = np.block([[np.zeros((2, 2)), -np.eye(2)],
                                         [np.eye(2), np.zeros((2, 2))]])
            bracket_error = la.norm(canonical_map @ la.inv(form) @
                                   canonical_map.conj().T-expected_bracket)
            assert bracket_error < 2e-11
            for euclidean_frequency in [0., .3, 1.]:
                response = metric_map @ la.solve(
                    energy+euclidean_frequency*form, metric_map.conj().T)
                expected = J/(euclidean_frequency**2+J*g*radius**2)
                relative_error = la.norm(response-expected*np.eye(2))/expected
                assert relative_error < 2e-11
                rows.append(dict(wave_number=radius, euclidean_frequency=euclidean_frequency,
                                 direction=direction.tolist(),
                                 reconstructed_metric_canonical_bracket_error=float(bracket_error),
                                 metric_response_eigenvalues=la.eigvalsh((response+response.conj().T)/2).tolist(),
                                 expected_positive_response=float(expected),
                                 relative_response_error=float(relative_error)))
    return dict(cases=rows, scope='Independent inversion of the complete first-order reduced kernel reconstructs the canonical metric response J/(omega_E^2+J g k^2) for both polarizations. This is the Gaussian quantization of the supplied action, not a pole derived from the microscopic spin measure.')


def main():
    root = Path(__file__).resolve().parents[1]
    symbols = exact_stencils()
    report = dict(symbolic_stencils=symbols[-1], symbols=symbol_checks(symbols),
                  full_lattices=full_lattice_checks(symbols),
                  continuum_and_brackets=continuum_and_bracket_checks(),
                  metric_response=metric_response_checks())
    sources = ['PREPOTENTIAL_LATTICE_BRIDGE.md', 'scripts/prepotential_lattice_bridge_audit.py',
               'CONSTRAINED_MEDIATOR_TEST.md', 'COMPACT_TENSOR_DYNAMICS.md',
               'COMPACT_TENSOR_CONSTRAINTS.md', 'BOND_TENSOR_CONSTRAINTS.md',
               'scripts/bond_tensor_audit.py', 'NONLINEAR_TENSOR_BACKREACTION.md',
               'CONVEX_MATTER_POLE_BOUND.md', 'EINSTEIN_MODEL_DECISION.md']
    report['source_sha256'] = {p: hashlib.sha256((root/p).read_bytes()).hexdigest() for p in sources}
    report['scope'] = ('A supplied local staggered prepotential action has exact gauge null directions, '
                       'positive physical energy and precisely two canonical tensor modes per nonzero '
                       'lattice momentum, with the linear-gravity dispersion and the correctly reduced '
                       'kinetic brackets. The inverse prepotential bracket is nonlocal, while specified '
                       'gauge-invariant current brackets are local. This is a classical linearized-gravity '
                       'benchmark adapted from the established prepotential formulation, not a microscopic '
                       'finite-spin realization, nonlinear Einstein gravity, or TOE. Homogeneous Einstein '
                       'data, physical state selection, matter coupling and microscopic quantization remain open. No Lean theorem.')
    target = root/'data/prepotential_lattice_bridge_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    counts = {k: len(v['cases']) for k, v in report.items() if isinstance(v, dict) and 'cases' in v}
    print(json.dumps(dict(report=str(target), checks=counts, source_references=len(sources),
                          scope=report['scope']), indent=2))


if __name__ == '__main__':
    main()
