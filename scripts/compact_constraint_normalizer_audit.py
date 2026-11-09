#!/usr/bin/env python3
"""Local stabilizer averaging, leakage bounds, and virtual logical dynamics."""
import hashlib
import itertools
import json
from pathlib import Path

import numpy as np
import scipy.linalg as la
import sympy as sy

from compact_tensor_dynamics_audit import derivative_obstruction, weyl


def re(matrix):
    return (matrix + matrix.conj().T) / 2


def kron3(a, b, c):
    return np.kron(np.kron(a, b), c)


def setup(prime):
    x, z = weyl(prime)
    identity = np.eye(prime)
    sx = kron3(x, x, identity)
    sz = kron3(z, z.conj().T, identity)
    code = np.zeros((prime**3, prime), dtype=complex)
    for n, t in itertools.product(range(prime), repeat=2):
        code[(n * prime + n) * prime + t, t] = 1 / np.sqrt(prime)
    projector = code @ code.conj().T
    px = sum(np.linalg.matrix_power(sx, r) for r in range(prime)) / prime
    pz = sum(np.linalg.matrix_power(sz, r) for r in range(prime)) / prime
    assert la.norm(px @ pz - projector) < 1e-12
    return dict(p=prime, x=x, z=z, identity=identity, sx=sx, sz=sz,
                code=code, projector=projector, px=px, pz=pz)


def twirl(matrix, checks, prime):
    result = matrix.astype(complex)
    for check in checks:
        result = sum(np.linalg.matrix_power(check, r) @ result
                     @ np.linalg.matrix_power(check, r).conj().T
                     for r in range(prime)) / prime
    return result


def character_checks():
    variable = sy.Symbol('z')
    rows = []
    for prime in [3, 5, 7]:
        cyclotomic = sy.Poly(sy.cyclotomic_poly(prime, variable), variable)
        for charge in range(prime):
            total = sy.Poly(sum(variable**((r * charge) % prime)
                                for r in range(prime)), variable)
            remainder = total.rem(cyclotomic).as_expr()
            assert remainder == (prime if charge == 0 else 0)
        rows.append(dict(prime=prime,exact_character_identities=prime))
    return rows


def locality_and_compression_checks():
    rng = np.random.default_rng(95111)
    rows = []
    for prime in [3, 5]:
        s = setup(prime)
        for case in range(6):
            # Independent dense operator on sites 0 and 2, with site 1 idle.
            local = rng.normal(size=(prime**2, prime**2)) + 1j * rng.normal(size=(prime**2, prime**2))
            local = re(local)
            local /= la.norm(local, 2)
            matrix = np.einsum('acdf,be->abcdef',
                               local.reshape((prime,) * 4), s['identity']).reshape((prime**3,) * 2)
            averaged = twirl(matrix, [s['sx'], s['sz']], prime)
            reduced = np.trace(averaged.reshape((prime,) * 6), axis1=1, axis2=4) / prime
            reconstructed = np.einsum('acdf,be->abcdef', reduced, s['identity']).reshape((prime**3,) * 2)
            support_error = la.norm(averaged - reconstructed, 2)
            compression_error = la.norm(s['code'].conj().T @ (matrix - averaged) @ s['code'], 2)
            commutation_error = max(la.norm(averaged @ s[name] - s[name] @ averaged, 2)
                                    for name in ['sx', 'sz'])
            assert max(support_error, compression_error, commutation_error) < 1e-11
            averaged_norm = la.norm(averaged, 2)
            assert averaged_norm <= 1 + 1e-12
            rows.append(dict(prime=prime, case=case, support_error=float(support_error),
                             compression_error=float(compression_error),
                             commutation_error=float(commutation_error),
                             original_norm=float(la.norm(matrix, 2)), averaged_norm=float(averaged_norm)))
    return dict(cases=len(rows), rows=rows,
                scope='Dense local operators, not preselected neutral Pauli sums; independent partial traces check that averaging leaves the idle site idle.')


def weak_and_approximate_checks():
    s = setup(5)
    x, z, i = s['x'], s['z'], s['identity']
    x1, z1 = kron3(x, i, i), kron3(z, i, i)
    logical = -.7 * re(kron3(i, i, x)) - 1.1 * re(kron3(i, i, z))
    nontrivial_x = np.eye(125) - s['px']
    weak = logical + .6 * nontrivial_x @ re(x1) @ nontrivial_x
    averaged = twirl(weak, [s['sx'], s['sz']], 5)
    leakage = float(la.norm((np.eye(125) - s['projector']) @ weak @ s['code'], 2))
    outside_commutator = float(la.norm(weak @ s['sz'] - s['sz'] @ weak, 2))
    code_action_error = float(la.norm((weak - averaged) @ s['code'], 2))
    assert leakage < 1e-12 and code_action_error < 1e-12 and outside_commutator > .1
    time = .8
    exact_error = float(la.norm((la.expm(-1j * time * weak)
                                 - la.expm(-1j * time * averaged)) @ s['code'], 2))
    assert exact_error < 1e-11
    # A separate stable weak representative has an analytical defect margin:
    # H_parent >= 3 Q, logical >= E0, and the extra term >= -0.6 Q.
    stable = weak + 3 * (2 * np.eye(125) - s['px'] - s['pz'])
    stable_averaged = twirl(stable, [s['sx'], s['sz']], 5)
    e0 = float(la.eigvalsh(s['code'].conj().T @ logical @ s['code'])[0])
    excluded = np.eye(125) - s['projector']
    original_bound_error = float(la.eigvalsh(stable-e0*np.eye(125)-2.4*excluded)[0])
    averaged_bound_error = float(la.eigvalsh(stable_averaged-e0*np.eye(125)-2.4*excluded)[0])
    assert min(original_bound_error, averaged_bound_error) > -1e-11
    rows = []
    # An additional term deliberately violates the physical code.
    perturbation = re(x1) + .43 * re(z1)
    for strength, time in itertools.product([.001, .01, .1], [.2, 1., 4.]):
        ham = weak + strength * perturbation
        projected = twirl(ham, [s['sx'], s['sz']], 5)
        epsilon = float(la.norm((np.eye(125) - s['projector']) @ ham @ s['code'], 2))
        difference = float(la.norm((la.expm(-1j * time * ham)
                                    - la.expm(-1j * time * projected)) @ s['code'], 2))
        assert difference <= abs(time) * epsilon + 1e-11
        rows.append(dict(strength=strength, time=time, leakage_norm=epsilon,
                         evolution_error=difference, upper_bound=abs(time)*epsilon))
    return dict(exact_code_leakage=leakage,nonzero_check_commutator=outside_commutator,
                exact_code_action_error=code_action_error, exact_evolution_error=exact_error,
                preserved_protection=dict(ground_energy=e0,excluded_sector_bound=2.4,
                                          original_minimum_residual=original_bound_error,
                                          averaged_minimum_residual=averaged_bound_error),
                approximate_cases=rows,
                scope='A Hamiltonian that preserves the code but fails to commute with a check has identical code evolution after averaging; nine leaking examples check the all-output Duhamel bound.')


def virtual_process_checks():
    s = setup(5)
    x, z, i = s['x'], s['z'], s['identity']
    x1, z1 = kron3(x, i, i), kron3(z, i, i)
    x3, z3 = kron3(i, i, x), kron3(i, i, z)
    a, b, c, d = .7, .4, .9, .3
    delta = 1.6
    ham0 = delta * (2 * np.eye(125) - s['px'] - s['pz'])
    perturbation = -a * re(x1) - b * re(x1.conj().T @ x3)
    perturbation += -c * re(z1) - d * re(z1.conj().T @ z3)
    values, vectors = la.eigh(ham0)
    positive = values > delta / 2
    inverse = (vectors[:, positive] / values[positive]) @ vectors[:, positive].conj().T
    code = s['code']
    first = code.conj().T @ perturbation @ code
    second = -code.conj().T @ perturbation @ inverse @ perturbation @ code
    constant = (a*a + b*b + c*c + d*d) / 2
    expected = -(constant * i + a*b*re(x) + c*d*re(z)) / delta
    exact_error = float(la.norm(second - expected, 2))
    assert la.norm(first, 2) < 1e-12 and exact_error < 1e-12
    nu = float(la.norm(perturbation, 2))
    rows = []
    for strength in [.005, .01, .02, .04]:
        assert 2 * strength * nu < delta
        ham = ham0 + strength * perturbation
        energies, states = la.eigh(ham, subset_by_index=[0,4])
        approximate = strength**2 * la.eigvalsh(expected)
        error = float(np.max(abs(energies - approximate)))
        bound = 2 * strength**3 * nu**3 / (delta * (delta - 2 * strength * nu))
        # Independent Feshbach residual, retaining the actual eigenvectors.
        residuals = []
        for energy, vector in zip(energies, states.T):
            physical = code.conj().T @ vector
            residual = la.norm((strength**2 * second - energy * i) @ physical) / la.norm(physical)
            residuals.append(float(residual))
            assert residual <= bound + 1e-12
        assert error <= bound + 1e-12
        rows.append(dict(strength=strength, maximum_energy_error=error,
                         conservative_feshbach_bound=bound,
                         maximum_feshbach_residual=max(residuals),
                         exact_low_energies=energies.tolist()))
    return dict(prime=5, matrix_dimension=125, delta=delta, perturbation_norm=nu,
                first_order_norm=float(la.norm(first,2)), second_order_error=exact_error,
                second_order_logical_spectrum=la.eigvalsh(expected).tolist(), rows=rows,
                scope='A finite three-qudit calculation generates neutral logical X and Z at second order. The norm bound is finite-volume and does not establish a thermodynamic perturbation expansion or tensor dispersion.')


def full_spin_average_checks():
    # Work in a local basis with the quintet first. A local change to the
    # Dicke embedding preserves every support, norm, and spectrum here.
    p, d = 5, 16
    x, z = weyl(p)
    xb, zb = la.block_diag(x, np.eye(11)), la.block_diag(z, np.eye(11))
    flag = la.block_diag(np.eye(5), np.exp(2j*np.pi/p)*np.eye(11))
    identity = np.eye(d)
    sx, sz = np.kron(xb,xb), np.kron(zb,zb.conj().T)
    flags = [np.kron(flag,identity),np.kron(identity,flag)]
    # Pinch active/inactive sectors first. Within each block the X/Z
    # adjoint actions commute, including the single-active Weyl blocks.
    average = lambda matrix:twirl(matrix, flags+[sx,sz], p)
    rng = np.random.default_rng(95119)
    local = re(rng.normal(size=(d,d))+1j*rng.normal(size=(d,d)))
    local /= la.norm(local,2)
    original = np.kron(local,identity)
    averaged = average(original)
    expected_local = la.block_diag(np.trace(local[:p,:p])*np.eye(p)/p, local[p:,p:])
    locality_error = float(la.norm(averaged-np.kron(expected_local,identity),2))
    assert locality_error < 1e-11
    assert la.norm(averaged,2) <= la.norm(original,2)+1e-12
    unguarded_commutator = float(la.norm(sx@sz-sz@sx,2))
    assert unguarded_commutator > 1
    code = np.zeros(d*d,dtype=complex)
    for n in range(p):code[n*d+n] = 1/np.sqrt(p)
    projector = np.outer(code,code.conj())
    excluded = np.eye(d*d)-projector
    dense = re(rng.normal(size=(d*d,d*d))+1j*rng.normal(size=(d*d,d*d)))
    dense /= la.norm(dense,2)
    stable = -.3*projector + excluded@(2*np.eye(d*d)+.4*dense)@excluded
    stable_averaged = average(stable)
    code_error = float(la.norm((stable-stable_averaged)@code))
    commutation_error = float(max(la.norm(check@stable_averaged-stable_averaged@check,2)
                                  for check in flags+[sx,sz]))
    protection_residual = float(la.eigvalsh(stable_averaged+.3*np.eye(d*d)-1.9*excluded)[0])
    assert max(code_error,commutation_error) < 1e-11
    assert protection_residual > -1e-11
    return dict(matrix_dimension=d*d,unused_states_per_cell=11,
                nonzero_unguarded_check_commutator=unguarded_commutator,
                support_error=locality_error,code_action_error=code_error,
                averaged_check_commutator=commutation_error,
                protected_sector_margin=1.9,minimum_protection_residual=protection_residual,
                scope='The full finite group is non-Abelian on inactive sectors. Flag dephasing followed by Weyl averaging implements its projection in this two-cell example.')


def tensor_charge_paths():
    # Use the audited tensor stencil, then split a local neutral pattern
    # into charged single-cell shifts. Every proper prefix is tested.
    from compact_tensor_dynamics_audit import local_dynamics
    from compact_tensor_constraint_audit import lattice_matrix, stencil_symbols
    _, report = local_dynamics()
    original, _ = stencil_symbols()
    bm = lattice_matrix(original[4], 1, 6, 3)
    gm = lattice_matrix(original[3], 6, 3, 3)
    patterns = report['logical_pair']
    rows = []
    for kind, key, charge_matrix in [('X','x_pattern',bm), ('Z','z_pattern',gm.T)]:
        entries = patterns[key]
        total = np.zeros(162, dtype=np.int64)
        charges = []
        for item in entries:
            total[item['index']] += item['coefficient']
            charge = charge_matrix @ total % 5
            charges.append(int(np.count_nonzero(charge)))
        assert charges[-1] == 0
        assert all(count > 0 for count in charges[:-1])
        assert all(np.count_nonzero(charge_matrix[:, item['index']] * item['coefficient'] % 5)
                   for item in entries)
        rows.append(dict(kind=kind,steps=len(entries),violated_checks_after_each_step=charges,
                         support=len(entries)))
    return dict(paths=rows,
                scope='Explicit charged single-cell paths ending in the previous neutral tensor logical patterns; no claim that these are minimal-order processes or that their coefficient survives every perturbative cancellation.')


def main():
    root = Path(__file__).resolve().parents[1]
    report = dict(character_identities=character_checks(),
                  local_compression=locality_and_compression_checks(),
                  weak_preservation=weak_and_approximate_checks(),
                  full_spin_average=full_spin_average_checks(),
                  virtual_dynamics=virtual_process_checks(),
                  tensor_paths=tensor_charge_paths(),
                  inherited_derivative_obstruction=derivative_obstruction())
    sources = ['COMPACT_CONSTRAINT_NORMALIZER.md',
               'scripts/compact_constraint_normalizer_audit.py',
               'COMPACT_TENSOR_DYNAMICS.md', 'scripts/compact_tensor_dynamics_audit.py',
               'COMPACT_TENSOR_CONSTRAINTS.md', 'scripts/compact_tensor_constraint_audit.py',
               'BOND_TENSOR_CONSTRAINTS.md', 'GRAVITY_FROM_CLOCK_CONSTRAINTS.md']
    report['source_sha256'] = {p:hashlib.sha256((root/p).read_bytes()).hexdigest() for p in sources}
    report['scope'] = ('Local averaging closes the weak-preservation loophole for the fixed compact code. '
                       'The regular continuum obstruction retains its stated assumptions; a gravitational '
                       'phase, nonlinear clock algebra, and TOE are not proved.')
    (root/'data/compact_constraint_normalizer_audit.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))


if __name__ == '__main__':
    main()
