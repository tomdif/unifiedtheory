#!/usr/bin/env python3
"""Finite checks for the causal-past clock bridge, not a spacetime selection law."""
import hashlib
import itertools
import json
from pathlib import Path

import numpy as np
import scipy.linalg as la


def order(n, relations):
    reach = np.zeros((n, n), dtype=bool)
    for i, j in relations:
        reach[i, j] = True
    for k in range(n):
        reach |= reach[:, k, None] & reach[None, k, :]
    assert not np.any(np.diag(reach))
    pred = [sum(1 << i for i in range(n) if reach[i, j]) for j in range(n)]
    return pred


def ideals(pred):
    return [mask for mask in range(1 << len(pred))
            if all(not mask & (1 << x) or pred[x] & mask == pred[x]
                   for x in range(len(pred)))]


def addable(pred, mask):
    return [x for x in range(len(pred))
            if not mask & (1 << x) and pred[x] & mask == pred[x]]


def extensions(pred, target=None):
    target = (1 << len(pred))-1 if target is None else target
    def visit(mask, path):
        if mask == target:
            yield tuple(path)
        else:
            for x in addable(pred, mask):
                if target & (1 << x):
                    yield from visit(mask | (1 << x), path+[x])
    return list(visit(0, []))


def transport(path, gate, dim):
    value, mask = np.eye(dim, dtype=complex), 0
    for x in path:
        value = gate(mask, x) @ value
        mask |= 1 << x
    return value


def clock_matrices(pred, gate, dim):
    states = ideals(pred)
    index = {mask: i for i, mask in enumerate(states)}
    blocks = len(states)
    C = np.zeros((blocks*dim, blocks*dim), complex)
    L = np.zeros((blocks, blocks))
    edges, diamond_errors = [], []
    for mask in states:
        possible = addable(pred, mask)
        for x, y in itertools.combinations(possible, 2):
            left = gate(mask | (1 << x), y) @ gate(mask, x)
            right = gate(mask | (1 << y), x) @ gate(mask, y)
            diamond_errors.append(float(la.norm(left-right, 2)))
        for x in possible:
            new = mask | (1 << x)
            i, j = index[mask], index[new]
            u = gate(mask, x)
            assert la.norm(u.conj().T@u-np.eye(dim), 2) < 1e-12
            si, sj = slice(i*dim, (i+1)*dim), slice(j*dim, (j+1)*dim)
            C[si, si] += np.eye(dim)
            C[sj, sj] += np.eye(dim)
            C[sj, si] -= u
            C[si, sj] -= u.conj().T
            L[i, i] += 1
            L[j, j] += 1
            L[i, j] -= 1
            L[j, i] -= 1
            edges.append((mask, new))
    return states, C, L, edges, diamond_errors


def verify_flat_history(pred, gate, dim):
    states, C, L, edges, errors = clock_matrices(pred, gate, dim)
    Vs, path_count, maximum_path_error = [], 0, 0.
    for mask in states:
        paths = extensions(pred, mask)
        values = [transport(path, gate, dim) for path in paths]
        Vs.append(values[0])
        path_count += len(paths)
        maximum_path_error = max(maximum_path_error,
                                 max(float(la.norm(v-values[0], 2)) for v in values))
    W = la.block_diag(*Vs)
    equivalence = float(la.norm(W.conj().T@C@W-np.kron(L, np.eye(dim)), 2))
    embedding = np.concatenate(Vs, axis=0)/np.sqrt(len(states))
    constraint_error = float(la.norm(C@embedding, 2))
    isometry_error = float(la.norm(embedding.conj().T@embedding-np.eye(dim), 2))
    eig = la.eigvalsh(C)
    spectrum_error = float(np.max(np.abs(eig-np.repeat(la.eigvalsh(L), dim))))
    nullity = int(np.sum(np.abs(eig) < 1e-10))
    assert max(errors, default=0.) < 1e-12
    assert max(maximum_path_error, equivalence, constraint_error, isometry_error,
               spectrum_error) < 1e-11
    assert nullity == dim
    return dict(events=len(pred), ideals=len(states), edges=len(edges), diamonds=len(errors),
                full_extensions=len(extensions(pred)), paths_to_all_ideals=path_count,
                joint_dimension=len(C), maximum_diamond_error=max(errors, default=0.),
                maximum_path_error=maximum_path_error, gauge_equivalence_error=equivalence,
                constraint_error=constraint_error, history_isometry_error=isometry_error,
                spectrum_error=spectrum_error, kernel_dimension=nullity)


def finite_clocks():
    pred = order(5, [(0, 1)])
    paths = extensions(pred)
    gaps = sorted(set(path.index(1)-path.index(0) for path in paths))
    assert gaps == [1, 2, 3, 4]
    assert len(paths) == 60
    # A short branch through y=1, and a longer alternative branch to z=5.
    branching = order(6, [(0, 1), (1, 5), (0, 2), (2, 3), (3, 4), (4, 5)])
    def height(x, y):
        dist = {x: 0}
        for v in range(x+1, y+1):
            options = [dist[u]+1 for u in dist if branching[v] & (1 << u)]
            if options:
                dist[v] = max(options)
        return dist[y]
    through_y, maximal = height(0, 1)+height(1, 5), height(0, 5)
    assert (through_y, maximal) == (2, 4)
    return dict(spectator_example_extensions=len(paths), enumeration_tick_gaps=gaps,
                unchanged_interval_strict_step_height=1,
                branch_height_through_y=through_y, maximal_endpoint_height=maximal,
                scope='Exact finite enumeration and chain counts; no continuum-duration claim.')


def finite_histories():
    X = np.array([[0, 1], [1, 0]], complex)
    Z = np.diag([1., -1.])
    I = np.eye(2)
    pred = order(5, [(0, 2), (1, 2), (2, 3), (2, 4)])
    generators = [np.kron(X, I), np.kron(I, Z), np.kron(Z, X),
                  np.kron(Z, I), np.kron(I, X)]
    gates = [la.expm(-1j*a*h) for a, h in zip([.2, .3, .4, .5, .6], generators)]
    flat = verify_flat_history(pred, lambda mask, x: gates[x], 4)
    rng = np.random.default_rng(20260910)
    V = {}
    for mask in ideals(pred):
        a = rng.normal(size=(4, 4))+1j*rng.normal(size=(4, 4))
        V[mask] = la.expm(-.13j*(a+a.conj().T)) if mask else np.eye(4)
    context = verify_flat_history(pred, lambda mask, x: V[mask | (1 << x)]@V[mask].conj().T, 4)
    # Two unrelated gates acting on the same qubit do not define a flat history.
    bad_pred = order(2, [])
    bad_gates = [la.expm(-.37j*X), la.expm(-.61j*Z)]
    _, Cbad, _, _, bad_errors = clock_matrices(bad_pred, lambda mask, x: bad_gates[x], 2)
    min_eigenvalue = float(la.eigvalsh(Cbad)[0])
    assert bad_errors[0] > .1 and min_eigenvalue > .001
    # The same one-event order admits different conditional dynamics.
    psi = np.array([1., 0.], complex)
    rotated = la.expm(-.37j*X)@psi
    different_probability = float(abs(rotated[1])**2)
    assert different_probability > .1
    return dict(context_independent=flat, context_dependent=context,
                inconsistent_diamond=dict(operator_mismatch=bad_errors[0],
                                          constraint_smallest_eigenvalue=min_eigenvalue,
                                          kernel_dimension=0),
                same_order_different_laws=dict(identity_excitation_probability=0.,
                                               rotation_excitation_probability=different_probability))


def local_geometry_matter():
    identity = np.eye(2)
    X = np.array([[0, 1], [1, 0]], complex)
    number = np.diag([0., 1.])
    lower = np.array([[0, 1], [0, 0]], complex)
    def site(matrix, position):
        answer = np.array([[1.]])
        for i in range(5):
            answer = np.kron(answer, matrix if i == position else identity)
        return answer
    n0, x0 = site(number, 0), site(X, 0)
    lowers = [site(lower, i) for i in range(5)]
    def hop(i, j):
        return lowers[i].conj().T@lowers[j]+lowers[j].conj().T@lowers[i]
    b, d, kappa = .4, .31, .25
    terms = [-b*x0+d*n0, -kappa*hop(1, 2), -kappa*hop(2, 3), -kappa*hop(3, 4),
             kappa*n0@hop(1, 2), kappa*n0@hop(3, 4),
             -kappa*n0@hop(1, 3), -kappa*n0@hop(2, 4)]
    supports = [{0}, {1, 2}, {2, 3}, {3, 4}, {0, 1, 2}, {0, 3, 4}, {0, 1, 3}, {0, 2, 4}]
    pred = order(len(terms), [(i, j) for i in range(len(terms)) for j in range(i+1, len(terms))
                              if supports[i] & supports[j]])
    gates = [la.expm(-.23j*h) for h in terms]
    paths = extensions(pred)
    values = [transport(path, lambda mask, x: gates[x], 32) for path in paths]
    path_error = max(float(la.norm(v-values[0], 2)) for v in values)
    assert path_error < 1e-12 and len(paths) > 1
    H = sum(terms)
    total_number = sum(site(number, i) for i in range(1, 5))
    assert la.norm(H@total_number-total_number@H, 2) < 1e-12
    assert la.norm(H@n0-n0@H, 2) > .1  # Quantum geometry changes.
    commutator_sum = sum(float(la.norm(a@b-b@a, 2))
                         for i, a in enumerate(terms) for b in terms[i+1:])
    T, rows = .7, []
    target = la.expm(-1j*T*H)
    for m in [4, 8, 16, 32, 64]:
        one_round = np.eye(32, dtype=complex)
        for term in terms:
            one_round = la.expm(-1j*T/m*term)@one_round
        error = float(la.norm(np.linalg.matrix_power(one_round, m)-target, 2))
        bound = T*T/(2*m)*commutator_sum
        assert error < bound+1e-13
        rows.append(dict(rounds=m, ticks=8*m, error=error, analytic_bound=bound))
    assert all(rows[i+1]['error'] < .6*rows[i]['error'] for i in range(len(rows)-1))
    return dict(qubits=5, system_dimension=32, gate_occurrences_per_round=8,
                ideal_clock_states_one_round=len(ideals(pred)),
                allowed_enumerations_one_round=len(paths), enumeration_error=path_error,
                commutator_norm_sum=commutator_sum, product_limit=rows,
                scope='Exact local neutral-field/switch motif. The other degree-six carrier edges are omitted; this is a local benchmark, not a complete torus simulation.')


def clock_dispersion():
    rows = []
    for k in [.1, .05, .025, .0125]:
        # Supplied reference quadratic band; its ratio is invariant under clock units.
        energy = lambda q: 2*(1-np.cos(q))
        ratio = float(energy(2*k)/energy(k))
        for clock_scale in [.01, 1., 100.]:
            assert abs((energy(2*k)/clock_scale)/(energy(k)/clock_scale)-ratio) < 1e-12
        rows.append(dict(momentum=k, quadratic_frequency_ratio=ratio,
                         linear_frequency_ratio=2.))
    assert abs(rows[-1]['quadratic_frequency_ratio']-4) < .001
    return rows


def main():
    root = Path(__file__).resolve().parents[1]
    report = dict(finite_clocks=finite_clocks(), quantum_histories=finite_histories(),
                  local_geometry_matter=local_geometry_matter(), frequency_ratios=clock_dispersion())
    names = ['CAUSAL_ORDER_CLOCK_BRIDGE.md', 'scripts/causal_order_clock_audit.py',
             'UnifiedTheory/Audit/KFCausalOrderClock.lean',
             'UnifiedTheory/Audit/KFCausalBornRateAndDilation.lean',
             'UnifiedTheory/Audit/KFCausalCSpecVolumeGauge.lean',
             'UnifiedTheory/Audit/KFCausalCSpecTwoEmbeddingProperTime.lean',
             'COLLECTIVE_SPACETIME_TEST.md', 'PROJECTED_GEOMETRY_AND_LOCAL_DYNAMICS.md',
             'HARMONIC_BORN_EVENTUAL_CHAIN_COLLAPSE.md']
    report['source_sha256'] = {name: hashlib.sha256((root/name).read_bytes()).hexdigest() for name in names}
    report['scope'] = ('A supplied finite event order and unitary ticks admit an internal causal-past '
                       'clock exactly when all diamonds are flat for every initial state. This does '
                       'not select the event order, tick dynamics, physical clock calibration, a '
                       'Lorentzian continuum, or Einstein gravity.')
    (root/'data/causal_order_clock_audit.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
