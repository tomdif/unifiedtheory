#!/usr/bin/env python3
"""Stable auxiliary spectra, constrained Coulomb energy, and Dirac brackets.

These are exact Gaussian/linear-constraint benchmarks. They do not prove
a phase or gravitational continuum for the finite-spin Hamiltonian.
"""
import hashlib
import json
from pathlib import Path

import numpy as np
import scipy.linalg as la
import sympy as sy

from bond_tensor_audit import basis_matrices


def canonical(pairs):
    return np.kron(np.eye(pairs), np.array([[0., 1.], [-1., 0.]]))


def frequencies(energy):
    # Hermitian matrix similar to i Omega K, avoiding nonnormal eigensolvers.
    lower = la.cholesky(energy, lower=True)
    values = la.eigvalsh(1j*lower.T @ canonical(len(energy)//2) @ lower)
    count = len(energy)//2
    assert np.max(abs(values[:count]+values[count:][::-1])) < 1e-10
    return values[count:]


def auxiliary_interlacing_checks():
    rng, rows = np.random.default_rng(9112602), []
    for pairs in [1, 2, 4]:
        for case in range(8):
            coupling_shape = rng.normal(size=(4, 2*pairs))
            coupling_shape *= .72/la.svdvals(coupling_shape)[0]
            raw = rng.normal(size=(2*pairs, 2*pairs))
            base = raw @ raw.T+np.eye(2*pairs)
            for wave_number in [.3, .1, .03, .01]:
                k = wave_number
                original = np.diag([1.3*k**4, .8*k**2, .7*k**4, 1.1*k**2])
                # Alternating massive and gapless auxiliaries, with mixed Q/P.
                scale = np.diag([k if (i % 2 == 0 and case % 2) else 1.
                                 for i in range(2*pairs)])
                auxiliary = scale @ base @ scale
                lo = la.cholesky(original, lower=True)
                ld = la.cholesky(auxiliary, lower=True)
                mixed = lo @ coupling_shape @ ld.T
                energy = np.block([[original, mixed], [mixed.T, auxiliary]])
                omega = frequencies(energy)
                bare = frequencies(original)
                assert np.all(omega[:2] <= bare+2e-11)
                reduced = original-mixed @ la.solve(auxiliary, mixed.T, assume_a='pos')
                assert min(la.eigvalsh(reduced)) > 0
                assert min(la.eigvalsh(original-reduced)) > -1e-13
                threshold = 1.2*bare[-1]
                negative = int(np.sum(la.eigvalsh(energy-1j*threshold*canonical(pairs+2)) < -1e-13))
                assert negative >= 2
                rows.append(dict(auxiliary_pairs=pairs, case=case, wave_number=k,
                                 gapless_auxiliary=bool(case % 2),
                                 lowest_full_frequencies=omega[:2].tolist(),
                                 original_frequencies=bare.tolist(),
                                 full_frequency_over_k_cubed=(omega[:2]/k**3).tolist(),
                                 full_inertia_negative_count=negative,
                                 minimum_static_schur_eigenvalue=float(min(la.eigvalsh(reduced)))))
    return dict(cases=rows, scope='Full stable canonical spectra, including mixed coordinate-momentum couplings and auxiliaries whose frequencies vanish with momentum. The original two canonical pairs remain a principal subspace. Tests verify symplectic interlacing and the sign of the static Schur correction.')


def symbolic_constraint_checks():
    k, j, g = sy.symbols('k J g', positive=True)
    omega = sy.diag(*[sy.Matrix([[0, 1], [-1, 0]])]*3)
    # Variables q,p,a,e,b,f. Constraints k(e-p)=0 and k f-k^2 q=0.
    constraint = sy.Matrix([[0, -k, 0, k, 0, 0],
                            [-k*k, 0, 0, 0, 0, k]])
    bracket = sy.simplify(constraint*omega*constraint.T)
    assert bracket == sy.Matrix([[0, -k**3], [k**3, 0]])
    reduced = sy.simplify(omega-omega*constraint.T*bracket.inv()*constraint*omega)
    assert constraint*reduced == sy.zeros(2, 6)
    assert reduced[:2, :2] == sy.zeros(2)
    assert reduced.rank() == 4
    energy = sy.diag(0, 0, 0, j, 0, g)
    flow = sy.simplify(reduced*energy)
    assert flow != sy.zeros(6)
    assert sy.simplify(flow*flow) == sy.zeros(6)
    assert flow[:2, :] == sy.zeros(2, 6)
    # Original variables become commuting momenta of two different pairs.
    # With e=p, f=k q, the pulled-back canonical one-form is
    # p d(q+a) + k q db. Hence P1=p, Q1=q+a, P2=k q, Q2=b.
    q, p, a, e, b, f = sy.symbols('q p a e b f', real=True)
    variables = sy.Matrix([q, p, a, e, b, f])
    physical = sy.Matrix([q+a, p, b, k*q])
    jacobian = physical.jacobian(variables)
    physical_bracket = sy.simplify(jacobian*reduced*jacobian.T)
    assert physical_bracket == sy.diag(*[sy.Matrix([[0, 1], [-1, 0]])]*2)
    lam, v = sy.symbols('lambda v', positive=True)
    potential = sy.Matrix([[g*k**4, lam*k*k], [lam*k*k, v*v*k*k]])
    assert sy.factor(potential.det()) == k**4*(g*k*k*v*v-lam**2)
    return dict(exact_second_class_bracket=str(bracket),
                original_q_p_dirac_bracket_zero=True,
                reduced_phase_space_dimension=4,
                reduced_canonical_coordinates=['q+a', 'p', 'b', 'k*q'],
                exact_flow_nonzero_but_square_zero=True,
                attempted_unconstrained_mediator_determinant=str(sy.factor(potential.det())))


def dirac_dynamics_checks():
    rows, omega = [], canonical(3)
    for k in [.4, .2, .1, .05]:
        constraint = np.array([[0., -k, 0., k, 0., 0.],
                               [-k*k, 0., 0., 0., 0., k]])
        bracket = constraint @ omega @ constraint.T
        reduced = omega-omega @ constraint.T @ la.solve(bracket, constraint @ omega)
        for j, g in [(.7, 1.3), (2., .5)]:
            energy = np.diag([0., 0., 0., j, 0., g])
            flow = reduced @ energy
            # The chosen initial data satisfy the constraints exactly.
            state = np.array([.8, -.3, .4, -.3, -.7, .8*k])
            evolved = la.expm(2.3*flow) @ state
            assert la.norm(constraint @ evolved) < 1e-13
            assert la.norm(evolved[:2]-state[:2]) < 1e-13
            assert la.norm(evolved[2:]-state[2:]) > .1
            assert la.norm(flow @ flow) < 1e-13
            naive_frequency = k*np.sqrt(j*g)
            rows.append(dict(wave_number=k, J=j, g=g,
                             naive_substitution_frequency=float(naive_frequency),
                             exact_dirac_flow_eigenvalues_zero=True,
                             original_q_p_change=float(la.norm(evolved[:2]-state[:2])),
                             auxiliary_coordinate_change=float(la.norm(evolved[2:]-state[2:])),
                             preserved_constraint_residual=float(la.norm(constraint @ evolved))))
    return dict(cases=rows, scope='An exact three-pair Gaussian model. Substituting the two constraints into its positive energy gives an apparent oscillator only if the original bracket is incorrectly retained. Correct Dirac reduction gives two free canonical pairs and constant original q,p.')


def periodic_divergence(length):
    volume = length**3
    identity = np.eye(volume)
    grid = np.arange(volume).reshape((length,)*3)
    differences = [identity-np.eye(volume)[np.roll(grid, 1, axis=axis).ravel()]
                   for axis in range(3)]
    return np.concatenate(differences, axis=1)


def coulomb_minimization_checks():
    rng, rows = np.random.default_rng(9112603), []
    for length in [3, 4, 5]:
        divergence = periodic_divergence(length)
        laplacian = divergence @ divergence.T
        values, vectors = la.eigh(laplacian)
        assert abs(values[0]) < 1e-13 and values[1] > 0
        inverse = (vectors[:, 1:]/values[None, 1:]) @ vectors[:, 1:].T
        for case in range(4):
            source = rng.normal(size=length**3)
            source -= source.mean()
            field = divergence.T @ inverse @ source
            independent, _, rank, _ = la.lstsq(divergence, source, cond=1e-12)
            assert rank == length**3-1
            assert la.norm(field-independent) < 2e-12
            assert la.norm(divergence @ field-source) < 2e-12
            energy = .5*(field @ field)
            effective = .5*(source @ inverse @ source)
            trial = rng.normal(size=3*length**3)
            transverse = trial-divergence.T @ inverse @ (divergence @ trial)
            excess = .5*la.norm(field+transverse)**2-energy
            assert abs(excess-.5*la.norm(transverse)**2) < 2e-11
            assert abs(energy-effective) < 2e-12
            rows.append(dict(length=length, case=case,
                             exact_constrained_energy=float(energy),
                             inverse_laplacian_energy=float(effective),
                             independent_least_squares_error=float(la.norm(field-independent)),
                             divergence_residual=float(la.norm(divergence @ field-source)),
                             transverse_energy_excess=float(excess)))
    return dict(cases=rows, scope='Positive local electric energy with an imposed divergence constraint yields a positive inverse Laplacian on zero-mean sources. This static minimization does not remove canonical transverse modes or establish compatible tensor Gauss laws.')


def tensor_constraint_checks():
    rng, rows = np.random.default_rng(9112604), []
    basis = basis_matrices()
    for case in range(16):
        k = rng.normal(size=3)
        k *= .3/la.norm(k)
        cross = np.array([[0., -k[2], k[1]], [k[2], 0., -k[0]], [-k[1], k[0], 0.]])
        c = np.column_stack([(cross @ (e-np.trace(e)*np.eye(3)/2)).ravel() for e in basis])
        r = np.column_stack([(cross @ e @ cross.T).ravel() for e in basis])
        mixed = -c @ r.T
        rank = int(np.linalg.matrix_rank(mixed, tol=1e-12))
        assert rank == 2
        algebra = np.block([[np.zeros((9, 9)), mixed], [-mixed.T, np.zeros((9, 9))]])
        assert np.linalg.matrix_rank(algebra, tol=1e-12) == 4
        rows.append(dict(case=case, wave_vector=k.tolist(),
                         mixed_tensor_constraint_rank=rank,
                         total_added_constraint_bracket_rank=4,
                         largest_mixed_singular_value=float(la.svdvals(mixed)[0])))
    root = Path(__file__).resolve().parents[1]
    old = json.loads((root/'data/compact_tensor_dynamics_audit.json').read_text())
    pair = old['local_operators']['logical_pair']
    u = {entry['index']: entry['coefficient'] for entry in pair['x_pattern']}
    v = {entry['index']: entry['coefficient'] for entry in pair['z_pattern']}
    pairing = sum(value*v.get(index, 0) for index, value in u.items())
    assert pairing % pair['prime'] == pair['symplectic_phase'] != 0
    return dict(cases=rows, exact_lattice_current_pairing=int(pairing),
                exact_lattice_pairing_mod_5=int(pairing % 5),
                scope='The continuum current pairings have rank two at nonzero momentum (real coefficient convention, with Fourier reality partners understood). An independently contracted exact finite-lattice pair from the frozen compact audit also has nonzero Weyl charge pairing. Independent electric Gauss constraints therefore do not commute.')


def main():
    root = Path(__file__).resolve().parents[1]
    report = dict(symbolic=symbolic_constraint_checks(),
                  auxiliary_interlacing=auxiliary_interlacing_checks(),
                  coulomb_minimization=coulomb_minimization_checks(),
                  dirac_dynamics=dirac_dynamics_checks(),
                  tensor_constraint_algebra=tensor_constraint_checks())
    sources = ['CONSTRAINED_MEDIATOR_TEST.md', 'scripts/constrained_mediator_audit.py',
               'COMPACT_TENSOR_DYNAMICS.md', 'data/compact_tensor_dynamics_audit.json',
               'COMPACT_CONSTRAINT_NORMALIZER.md', 'COMPACT_TENSOR_CONSTRAINTS.md',
               'BOND_TENSOR_CONSTRAINTS.md', 'scripts/bond_tensor_audit.py',
               'CONVEX_MATTER_POLE_BOUND.md', 'EINSTEIN_MODEL_DECISION.md']
    report['source_sha256'] = {p: hashlib.sha256((root/p).read_bytes()).hexdigest() for p in sources}
    report['scope'] = ('Stable canonical auxiliary oscillators leave at least two O(k^3) frequencies '
                       'when the compact tensor quadratic block survives as a canonical principal subspace. '
                       'Constrained electric minimization supplies a positive inverse Laplacian, but the '
                       'two proposed tensor-current Gauss laws fail to commute. Exact Dirac reduction of '
                       'a minimal example eliminates the apparent oscillator obtained by naive substitution. '
                       'These are conditional Gaussian and constraint benchmarks, not a finite-spin phase '
                       'theorem, nonlinear Einstein gravity, or TOE. No new Lean theorem.')
    target = root/'data/constrained_mediator_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    counts = {k: len(v['cases']) for k, v in report.items() if isinstance(v, dict) and 'cases' in v}
    print(json.dumps(dict(report=str(target), checks=counts, source_references=len(sources),
                          scope=report['scope']), indent=2))


if __name__ == '__main__':
    main()
