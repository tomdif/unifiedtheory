#!/usr/bin/env python3
"""Finite-spin state geometry versus the prepotential gauge quotient.

An exact local Berry pullback need not identify gauge-equivalent rays.
A global finite-spin normal-mode encoding does, but supplies no spatial
locality or microscopic derivation of its prescribed dispersion.
"""
from functools import lru_cache
import hashlib
import itertools
import json
from pathlib import Path

import numpy as np
import scipy.linalg as la
from scipy.special import comb
import sympy as sy

from geometric_spectral_induction_audit import spin_matrices
from prepotential_lattice_bridge_audit import component_basis, exact_stencils, lattice_matrix


def analytic_gauge_checks():
    k = sy.symbols('kx ky kz', real=True)
    rows = []
    for degree in range(4):
        monomials = [sy.prod(k[i]**a[i] for i in range(3))
                     for a in itertools.product(range(degree+1), repeat=3) if sum(a) == degree]
        coefficients = sy.symbols('c:'+str(6*len(monomials)))
        entries = [sum(coefficients[j*len(monomials)+i]*m for i, m in enumerate(monomials))
                   for j in range(6)]
        a, b, c, d, e, f = entries
        tensor = sy.Matrix([[a, d, f], [d, b, e], [f, e, c]])
        equations = []
        for polynomial in list(tensor*sy.Matrix(k))+[sy.trace(tensor)]:
            equations += sy.Poly(sy.expand(polynomial), *k).coeffs()
        matrix, _ = sy.linear_eq_to_matrix(equations, coefficients)
        rank = int(matrix.rank())
        nullity = len(coefficients)-rank
        assert nullity == (5 if degree == 3 else 0)
        rows.append(dict(homogeneous_degree=degree, unknown_coefficients=len(coefficients),
                         exact_constraint_rank=rank, exact_kernel_dimension=nullity))
    return dict(cases=rows, scope='Exact coefficient elimination over the rationals: an analytic symmetric transverse tracefree covector starts at third order in momentum. This supports the bounded-depth tangent-factor argument, not a general theorem excluding all entangled phases.')


def coherent_state(j, p, q):
    n = np.arange(int(2*j)+1)
    m = j-n
    plus, minus = (1+p/j)/2, (1-p/j)/2
    state = np.sqrt(comb(int(2*j), n)*plus**(2*j-n)*minus**n)*np.exp(-1j*m*q)
    dp = state*((2*j-n)/(2*(j+p))-n/(2*(j-p)))
    dq = -1j*m*state
    return state, np.column_stack([dp, dq])


def single_spin_checks():
    rows = []
    for j in [.5, 2., 5.]:
        for fraction in [-.6, 0., .7]:
            for angle in [.2, 1.1]:
                p = j*fraction
                state, tangent = coherent_state(j, p, angle)
                assert abs(np.vdot(state, state)-1) < 1e-13
                horizontal = tangent-state[:, None]*(state.conj() @ tangent)[None, :]
                tensor = horizontal.conj().T @ horizontal
                expected = np.array([[j/(2*(j*j-p*p)), -.5j],
                                     [.5j, (j*j-p*p)/(2*j)]])
                connection = 1j*(state.conj() @ tangent)
                assert la.norm(tensor-expected) < 2e-12
                assert la.norm(connection-np.array([0., p])) < 2e-12
                other, _ = coherent_state(j, p+.04*j, angle+.09)
                n1 = np.array([np.sqrt(1-(p/j)**2)*np.cos(angle),
                               np.sqrt(1-(p/j)**2)*np.sin(angle), p/j])
                pp, qq = p+.04*j, angle+.09
                n2 = np.array([np.sqrt(1-(pp/j)**2)*np.cos(qq),
                               np.sqrt(1-(pp/j)**2)*np.sin(qq), pp/j])
                fidelity = abs(np.vdot(state, other))**2
                assert abs(fidelity-((1+n1 @ n2)/2)**(2*j)) < 2e-12
                rows.append(dict(spin=j, momentum=p, angle=angle,
                                 quantum_geometric_tensor_error=float(la.norm(tensor-expected)),
                                 berry_connection_momentum=float(connection[1].real),
                                 exact_metric_determinant=float(np.linalg.det(tensor.real)),
                                 nearby_fidelity=float(fidelity)))
    return dict(cases=rows, scope='Exact finite spin vectors, derivatives and overlaps independently verify the coherent-state Berry form and Fubini-Study metric. No large-spin approximation is used.')


@lru_cache(maxsize=1)
def reconstruction_stencils():
    k = sy.symbols('kx ky kz', real=True)
    t = sy.symbols('tx ty tz', nonzero=True)
    x = sy.Matrix([[0, -k[2], k[1]], [k[2], 0, -k[0]], [-k[1], k[0], 0]])
    raw = component_basis()
    orthonormal = [e/(sy.sqrt(2) if index >= 3 else 1) for index, e in enumerate(raw)]
    r = sy.Matrix(6, 6, lambda i, j: sy.expand(sy.trace(orthonormal[i]*(-x*raw[j]*x.T))))
    s = sy.Matrix(6, 6, lambda i, j: sy.expand(sy.trace(orthonormal[i]*sy.I*(x*raw[j]-raw[j]*x)/2)))
    phases = [t[0]**2, t[1]**2, t[2]**2, t[0]*t[1], t[1]*t[2], t[2]*t[0]]
    substitution = {k[i]: (t[i]-1/t[i])/sy.I for i in range(3)}
    stencils = []
    for matrix, shift in [(r, 1), (s, sy.prod(t))]:
        stencil = []
        for i, j in itertools.product(range(6), repeat=2):
            expr = sy.expand(shift*phases[j]/phases[i]*matrix[i, j].subs(substitution))
            for term in sy.Add.make_args(expr):
                if term == 0:
                    continue
                powers = term.as_powers_dict()
                exponents = [powers.get(v, 0) for v in t]
                assert all(p % 2 == 0 for p in exponents)
                coefficient = sy.simplify(term/sy.prod(v**p for v, p in zip(t, exponents)))
                assert coefficient.is_real
                stencil.append((i, j, tuple(int(p//2) for p in exponents), coefficient))
        stencils.append(stencil)
    return stencils


def gauge_matrix(length):
    _, _, _, gauge, _, _, _ = exact_stencils()
    w = exact_stencils()[0]
    sites = list(itertools.product(range(length), repeat=3))
    lookup, volume = {x: i for i, x in enumerate(sites)}, length**3
    matrix = np.zeros((6*volume, 4*volume))
    for row in range(6):
        for col in range(4):
            for term in sy.Add.make_args(sy.expand(gauge[row, col])):
                if term == 0:
                    continue
                powers = term.as_powers_dict()
                offset = tuple(int(powers.get(v, 0)) for v in w)
                coefficient = float(sy.cancel(term/sy.prod(v**p for v, p in zip(w, offset))))
                for x in sites:
                    y = tuple((x[i]+offset[i]) % length for i in range(3))
                    matrix[row*volume+lookup[x], col*volume+lookup[y]] += coefficient
    return matrix


def product_fidelity(j, p, q):
    direct, formula = 1., 1.
    reference, _ = coherent_state(j, 0., 0.)
    for pp, qq in zip(p, q):
        state, _ = coherent_state(j, pp, qq)
        direct *= abs(np.vdot(reference, state))**2
        formula *= ((1+np.sqrt(1-(pp/j)**2)*np.cos(qq))/2)**(2*j)
    assert abs(direct-formula) < 2e-11
    return direct


def local_state_checks():
    rows = []
    symbols = exact_stencils()
    rs, ss = reconstruction_stencils()
    for length in [2, 3]:
        volume, n = length**3, 6*length**3
        r, s = lattice_matrix(rs, length), lattice_matrix(ss, length)
        o = lattice_matrix(symbols[5], length)
        d = gauge_matrix(length)
        form = np.block([[np.zeros((n, n)), r.T @ s], [-s.T @ r, np.zeros((n, n))]])
        target = np.block([[np.zeros((n, n)), o], [-o.T, np.zeros((n, n))]])
        gauges = la.block_diag(d, d)
        assert la.norm(form-target) < 1e-11
        assert la.norm(form @ gauges) < 1e-11
        for j in [.5, 2.]:
            metric = la.block_diag(r.T @ r/(2*j), j*s.T @ s/2)
            rank = int(np.sum(la.eigvalsh(metric) > 1e-8))
            gauge_rank = int(np.sum(la.eigvalsh(gauges.T @ metric @ gauges) > 1e-8))
            assert rank == 7*(volume-1)
            assert gauge_rank == 3*(volume-1)
            fidelities = []
            for mapping, momentum_case in [(r, True), (s, False)]:
                changes = mapping @ d
                index = np.argmax(la.norm(changes, axis=0))
                delta = changes[:, index]
                delta *= .15*(j if momentum_case else 1)/max(abs(delta))
                p, q = (delta, np.zeros(n)) if momentum_case else (np.zeros(n), delta)
                fidelity = product_fidelity(j, p, q)
                assert 0 < fidelity < .999
                fidelities.append(float(fidelity))
            rows.append(dict(length=length, spin=j, exact_berry_form_error=float(la.norm(form-target)),
                             berry_rank=4*(volume-1), quantum_metric_rank=rank,
                             distinguishable_gauge_rank=gauge_rank,
                             scalar_P_gauge_fidelity=fidelities[0],
                             spatial_Phi_gauge_fidelity=fidelities[1]))
    return dict(cases=rows, scope='A finite-range product-spin state map reproduces the exact lattice Berry form. Full state overlaps and quantum-metric ranks show that three nominal gauge directions per nonzero momentum still change the physical ray.')


def positive_root(matrix):
    values, vectors = la.eigh(matrix)
    assert min(values) > 0
    root = (vectors*np.sqrt(values)) @ vectors.T
    inverse = (vectors/np.sqrt(values)) @ vectors.T
    return root, inverse


def global_mode_encoding_checks():
    rows, symbols, J, g = [], exact_stencils(), .7, 1.3
    for length in [2, 3]:
        volume, n = length**3, 6*length**3
        q, o = [lattice_matrix(symbols[index], length) for index in [4, 5]]
        u, singular, vt = la.svd(o)
        rank = 2*(volume-1)
        assert singular[rank-1] > 1e-9 and max(singular[rank:]) < 1e-9
        u, v, singular = u[:, :rank], vt.T[:, :rank], singular[:rank]
        root_sigma = np.diag(np.sqrt(singular))
        inverse_sigma = np.diag(1/np.sqrt(singular))
        initial_map = la.block_diag(root_sigma @ u.T, root_sigma @ v.T)
        p_inverse, q_inverse = u @ inverse_sigma, v @ inverse_sigma
        kp, kq = J*p_inverse.T @ q @ p_inverse, g*q_inverse.T @ q @ q_inverse
        root_p, inverse_p = positive_root(kp)
        squared, rotation = la.eigh(root_p @ kq @ root_p)
        omega = np.sqrt(squared)
        p_map = inverse_p @ rotation @ np.diag(np.sqrt(omega))
        q_map = root_p @ rotation @ np.diag(1/np.sqrt(omega))
        mode_map = la.solve(la.block_diag(p_map, q_map), initial_map)
        canonical_form = np.block([[np.zeros((rank, rank)), np.eye(rank)],
                                   [-np.eye(rank), np.zeros((rank, rank))]])
        target_form = np.block([[np.zeros((n, n)), o], [-o.T, np.zeros((n, n))]])
        target_energy = la.block_diag(J*q, g*q)
        berry_error = la.norm(mode_map.T @ canonical_form @ mode_map-target_form)
        energy_error = la.norm(mode_map.T @ np.diag(np.r_[omega, omega]) @ mode_map-target_energy)
        d = la.block_diag(gauge_matrix(length), gauge_matrix(length))
        gauge_error = la.norm(mode_map @ d)
        assert max(berry_error, energy_error, gauge_error) < 2e-9
        metric_reconstruction = lattice_matrix(reconstruction_stencils()[1], length)
        canonical_metric_map = metric_reconstruction @ q_inverse
        spin_metric_map = canonical_metric_map @ q_map
        source_map = np.concatenate([np.zeros((n, rank)), canonical_metric_map], axis=1)
        response_errors = []
        for frequency in [0., .3, 1.]:
            first_order_response = source_map @ la.solve(
                la.block_diag(kp, kq)+frequency*canonical_form, source_map.T)
            spin_response = (spin_metric_map*(omega/(frequency**2+omega**2))) @ spin_metric_map.T
            error = la.norm(first_order_response-spin_response)/la.norm(first_order_response)
            assert error < 2e-11
            response_errors.append(float(error))
        expected = []
        for momentum in itertools.product(range(length), repeat=3):
            if momentum != (0, 0, 0):
                expected += [np.sqrt(J*g)*la.norm(2*np.sin(np.pi*np.array(momentum)/length))]*2
        assert np.max(abs(np.sort(expected)-omega)) < 1e-11
        for j in [.5, 2.]:
            amplitude = .03
            p = amplitude*np.cos(np.arange(rank))
            angle = amplitude*np.sin(np.arange(rank))
            spin_energy = np.sum(omega*(j-np.sqrt(j*j-j*p*p)*np.cos(angle/np.sqrt(j))))
            quadratic = .5*np.sum(omega*(p*p+angle*angle))
            assert abs(spin_energy/quadratic-1) < .002
            rows.append(dict(length=length, spin=j, encoded_spins=rank,
                             exact_berry_form_error=float(berry_error),
                             exact_quadratic_energy_error=float(energy_error),
                             gauge_parameter_to_spin_state_error=float(gauge_error),
                             reconstructed_metric_response_relative_error=max(response_errors),
                             finite_amplitude_energy_relative_error=float(abs(spin_energy/quadratic-1)),
                             encoding='Global singular-vector and normal-mode map; spatial locality is not established.'))
    return dict(cases=rows, scope='A global encoding into finitely many genuine spins reproduces the same Berry form, gauge-ray identification and quadratic energy. Its Hamiltonian frequencies and nonlocal parameter map are explicitly supplied, so this is an existence benchmark, not emergent gravity from local spin dynamics.')


def finite_spin_pole_checks():
    rows, J, g = [], .7, 1.3
    for j in [.5, 2., 5.]:
        sx, sy_, _ = spin_matrices(int(2*j))
        identity = np.eye(int(2*j)+1)
        for wave_number in [.03, .3, 1.]:
            omega = np.sqrt(J*g)*wave_number
            energy = omega*(j*identity-sx)
            energies, states = la.eigh(energy)
            gaps = energies[1:]-energies[0]
            metric = np.sqrt(J/omega)*sy_/np.sqrt(j)
            weights = abs(states[:, 1:].conj().T @ metric @ states[:, 0])**2
            assert abs(gaps[0]-omega) < 1e-12
            assert np.sum(weights[1:]) < 1e-25
            for frequency in [0., .2, .7]:
                response = np.sum(2*gaps*weights/(frequency**2+gaps*gaps))
                expected = J/(frequency**2+omega*omega)
                error = abs(response/expected-1)
                assert error < 1e-11
                rows.append(dict(spin=j, wave_number=wave_number, euclidean_frequency=frequency,
                                 prescribed_spin_gap=float(omega),
                                 exact_spectral_response=float(response),
                                 expected_metric_response=float(expected), relative_error=float(error)))
    return dict(cases=rows, scope='Exact finite-spin spectral sums reproduce a massless-shaped response when each spin is assigned the desired momentum-dependent gap and a singularly normalized mode observable. The dispersion is input; there is no spatially local microscopic derivation.')


def main():
    root = Path(__file__).resolve().parents[1]
    report = dict(analytic_gauge_covectors=analytic_gauge_checks(),
                  single_spin_geometry=single_spin_checks(),
                  local_state_pullback=local_state_checks(),
                  global_mode_encoding=global_mode_encoding_checks(),
                  finite_spin_mode_response=finite_spin_pole_checks())
    sources = ['SPIN_STATE_GAUGE_GEOMETRY.md', 'scripts/spin_state_gauge_geometry_audit.py',
               'PREPOTENTIAL_LATTICE_BRIDGE.md', 'scripts/prepotential_lattice_bridge_audit.py',
               'scripts/geometric_spectral_induction_audit.py',
               'COMPACT_TENSOR_CONSTRAINTS.md', 'COMPACT_TENSOR_DYNAMICS.md',
               'CONVEX_MATTER_POLE_BOUND.md', 'GRAVITY_FROM_CLOCK_CONSTRAINTS.md',
               'EINSTEIN_MODEL_DECISION.md']
    report['source_sha256'] = {p: hashlib.sha256((root/p).read_bytes()).hexdigest() for p in sources}
    report['scope'] = ('Finite-spin product coherent states can pull back the exact prepotential Berry form '
                       'while failing its gauge-ray identification. Exact polynomial elimination supports '
                       'a conditional obstruction to a fixed-depth local state preparation with exact '
                       'linearized gauge rays. A global finite-spin encoding reproduces the Berry form, '
                       'gauge identification, quadratic energy and prescribed positive mode response. Its '
                       'spatially nonlocal encoding and inserted spectrum do not derive a local spin phase, '
                       'nonlinear Einstein gravity or TOE. No Lean theorem.')
    target = root/'data/spin_state_gauge_geometry_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    counts = {k: len(v['cases']) for k, v in report.items() if isinstance(v, dict) and 'cases' in v}
    print(json.dumps(dict(report=str(target), checks=counts, source_references=len(sources),
                          scope=report['scope']), indent=2))


if __name__ == '__main__':
    main()
