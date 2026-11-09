#!/usr/bin/env python3
"""Local event clocks and reduced-state readouts; finite supplied circuits only."""
import hashlib
import itertools
import json
from pathlib import Path

import numpy as np
import scipy.linalg as la
from scipy import sparse as sp
from scipy.sparse.linalg import eigsh

from causal_order_clock_audit import order, ideals, addable, transport


def wiring(supports):
    last, counts, edges, positions = {}, {}, set(), []
    for v, support in enumerate(supports):
        local_positions = []
        for q in sorted(support):
            if q in last:
                edges.add((last[q], v))
            last[q] = v
            counts[q] = counts.get(q, 0)+1
            local_positions.append(counts[q])
        positions.append(max(local_positions))
    previous = [set() for _ in supports]
    following = [set() for _ in supports]
    for u, v in edges:
        previous[v].add(u)
        following[u].add(v)
    weights = [1./(k*(k+1)) for k in positions]
    return sorted(edges), previous, following, weights


def clock_operator(gates, edges, previous, following, weights, penalty=1.3,
                   successor_guard=True):
    events, dim = len(gates), len(gates[0])
    rows, cols, values = [], [], []
    for v, gate in enumerate(gates):
        assert la.norm(gate.conj().T@gate-np.eye(dim), 2) < 1e-12
        u = sp.coo_matrix(gate)
        for low in range(1 << events):
            if low & (1 << v):
                continue
            if not all(low & (1 << x) for x in previous[v]):
                continue
            if successor_guard and any(low & (1 << x) for x in following[v]):
                continue
            high = low | (1 << v)
            for mask in [low, high]:
                diagonal = np.arange(dim)+mask*dim
                rows.extend(diagonal)
                cols.extend(diagonal)
                values.extend(np.full(dim, weights[v]))
            rows.extend(high*dim+u.row)
            cols.extend(low*dim+u.col)
            values.extend(-weights[v]*u.data)
            rows.extend(low*dim+u.col)
            cols.extend(high*dim+u.row)
            values.extend(-weights[v]*u.data.conj())
    violations = np.array([sum(not mask & (1 << u) and bool(mask & (1 << v))
                               for u, v in edges) for mask in range(1 << events)])
    result = sp.csr_matrix((values, (rows, cols)), shape=((1 << events)*dim,)*2)
    result += sp.diags(penalty*np.repeat(violations, dim))
    return result, violations


def ideal_laplacian(pred, states, weights):
    lookup = {mask: i for i, mask in enumerate(states)}
    rows, cols, values = [], [], []
    for mask in states:
        i = lookup[mask]
        for v in addable(pred, mask):
            j = lookup[mask | (1 << v)]
            rows.extend([i, j, i, j])
            cols.extend([i, j, j, i])
            values.extend([weights[v], weights[v], -weights[v], -weights[v]])
    return sp.csr_matrix((values, (rows, cols)), shape=(len(states),)*2)


def reduced(psi, observed, qubits):
    other = [q for q in range(qubits) if q not in observed]
    mat = psi.reshape([2]*qubits).transpose(list(observed)+other).reshape(2**len(observed), -1)
    return mat@mat.conj().T


def local_readouts(supports, pred, states, Vs, qubits):
    rng = np.random.default_rng(20260910+qubits)
    psi = rng.normal(size=2**qubits)+1j*rng.normal(size=2**qubits)
    psi /= la.norm(psi)
    evolved = {mask: Vs[mask]@psi for mask in states}
    wires = {q: [v for v, support in enumerate(supports) if q in support] for q in range(qubits)}
    tests, maximum_error, maximum_bits = 0, 0., 0
    probabilities = []
    for size in range(1, qubits+1):
        for observed in itertools.combinations(range(qubits), size):
            groups = {}
            for mask in states:
                reading = tuple(sum(bool(mask & (1 << v)) for v in wires[q]) for q in observed)
                groups.setdefault(reading, []).append(mask)
            for reading, selected in groups.items():
                requirements, causal_past = {}, 0
                for q, j in zip(observed, reading):
                    if j:
                        last = wires[q][j-1]
                        requirements[last] = 1
                        causal_past |= pred[last] | (1 << last)
                    if j < len(wires[q]):
                        requirements[wires[q][j]] = 0
                assert len(requirements) <= 2*len(observed)
                matching = [mask for mask in states
                            if all(bool(mask & (1 << v)) == bool(value) for v, value in requirements.items())]
                assert matching == selected and causal_past in selected
                expected = reduced(evolved[causal_past], observed, qubits)
                actual = sum(reduced(evolved[mask], observed, qubits) for mask in selected)/len(selected)
                error = float(la.norm(actual-expected, 2))
                assert error < 1e-12
                maximum_error = max(maximum_error, error)
                maximum_bits = max(maximum_bits, len(requirements))
                probabilities.append(len(selected)/len(states))
                tests += 1
    # The last bit without the next-bit guard need not specify a local cut.
    selected = [mask for mask in states if mask & 1]
    earliest = pred[0] | 1
    q = min(supports[0])
    actual = sum(reduced(evolved[mask], (q,), qubits) for mask in selected)/len(selected)
    incomplete_error = float(la.norm(actual-reduced(evolved[earliest], (q,), qubits), 2))
    assert incomplete_error > .001
    return dict(compatible_local_readouts=tests, maximum_reduced_state_error=maximum_error,
                maximum_distinct_clock_bits_read=maximum_bits,
                minimum_readout_probability=min(probabilities),
                missing_next_bit_reduced_state_mismatch=incomplete_error,
                initial_state='Seeded generally entangled pure work state; analytic theorem covers arbitrary density matrices.')


def verify_model(supports, gates, full_spectrum=False):
    edges, previous, following, weights = wiring(supports)
    pred = order(len(supports), edges)
    states = ideals(pred)
    dim, qubits = len(gates[0]), int(round(np.log2(len(gates[0]))))
    C, violations = clock_operator(gates, edges, previous, following, weights)
    assert [i for i, v in enumerate(violations) if v == 0] == states
    indices = np.array([mask*dim+i for mask in states for i in range(dim)])
    illegal = np.ones(C.shape[0], dtype=bool)
    illegal[indices] = False
    leakage = float(sp.linalg.norm(C[:, indices][illegal]))
    assert leakage == 0
    D = sp.diags(np.repeat(violations, dim))
    commutator = float(sp.linalg.norm(C@D-D@C))
    assert commutator == 0
    Vs = {mask: transport([v for v in range(len(supports)) if mask & (1 << v)],
                          lambda _, v: gates[v], dim) for mask in states}
    W = sp.block_diag([Vs[mask] for mask in states], format='csr')
    L = ideal_laplacian(pred, states, weights)
    legal = C[indices][:, indices]
    equivalence = float(sp.linalg.norm(W.conj().T@legal@W-sp.kron(L, sp.eye(dim))))
    assert equivalence < 1e-10
    legal_spectrum = la.eigvalsh(legal.toarray())
    nullity = int(np.sum(np.abs(legal_spectrum) < 1e-10))
    assert nullity == dim and legal_spectrum[0] > -1e-12
    illegal_minimum = None
    if full_spectrum:
        bad = C[illegal][:, illegal].toarray()
        illegal_minimum = float(la.eigvalsh(bad)[0])
        assert illegal_minimum >= 1.3-1e-12
    Cbad, _ = clock_operator(gates, edges, previous, following, weights, successor_guard=False)
    missing_guard_leakage = float(sp.linalg.norm(Cbad[:, indices][illegal]))
    assert missing_guard_leakage > .1
    readouts = local_readouts(supports, pred, states, Vs, qubits)
    return dict(events=len(supports), work_qubits=qubits, joint_dimension=C.shape[0],
                ideal_count=len(states), legal_dimension=len(indices), legal_kernel_dimension=nullity,
                maximum_immediate_predecessors=max(map(len, previous)),
                maximum_immediate_successors=max(map(len, following)),
                legal_illegal_coupling=leakage, violation_commutator=commutator,
                weighted_laplacian_equivalence_error=equivalence,
                minimum_illegal_energy=illegal_minimum,
                missing_successor_guard_leakage=missing_guard_leakage,
                readouts=readouts)


def examples():
    I, X, Z = np.eye(2), np.array([[0, 1], [1, 0]], complex), np.diag([1., -1.])
    supports = [{0}, {1}, {0, 1}, {0}, {1}]
    generators = [np.kron(X, I), np.kron(I, Z), np.kron(Z, X), np.kron(Z, I), np.kron(I, X)]
    gates = [la.expm(-1j*a*h) for a, h in zip([.2, .3, .4, .5, .6], generators)]
    small = verify_model(supports, gates, full_spectrum=True)
    def on_site(matrix, position):
        result = np.array([[1.]])
        for q in range(5):
            result = np.kron(result, matrix if q == position else I)
        return result
    number = on_site(np.diag([0., 1.]), 0)
    lower = np.array([[0, 1], [0, 0]], complex)
    lowers = [on_site(lower, q) for q in range(5)]
    def hop(i, j):
        return lowers[i].conj().T@lowers[j]+lowers[j].conj().T@lowers[i]
    terms = [-.4*on_site(X, 0)+.31*number, -.25*hop(1, 2), -.25*hop(2, 3), -.25*hop(3, 4),
             .25*number@hop(1, 2), .25*number@hop(3, 4), -.25*number@hop(1, 3), -.25*number@hop(2, 4)]
    motif_supports = [{0}, {1, 2}, {2, 3}, {3, 4}, {0, 1, 2}, {0, 3, 4}, {0, 1, 3}, {0, 2, 4}]
    motif = verify_model(motif_supports, [la.expm(-.23j*h) for h in terms])
    return small, motif, motif_supports


def strength_loads(base_supports):
    rows = []
    for rounds in [1, 4, 16, 64, 256]:
        supports = base_supports*rounds
        edges, prev, following, weights = wiring(supports)
        work = [2*sum(w for w, support in zip(weights, supports) if q in support) for q in range(5)]
        clock = [2*weights[v]+2*sum(weights[u] for u in prev[v] | following[v])
                 +1.3*(len(prev[v])+len(following[v])) for v in range(len(supports))]
        unweighted = [2*sum(q in support for support in supports) for q in range(5)]
        assert max(work) <= 2+1e-12
        assert max(clock) <= 7+6*1.3+1e-12
        rows.append(dict(rounds=rounds, clock_bits=len(supports),
                         maximum_weighted_work_load=max(work), maximum_clock_load=max(clock),
                         maximum_unweighted_work_load=max(unweighted), minimum_weight=min(weights)))
    return rows


def reachable_ideals(pred):
    found, frontier = {0}, [0]
    while frontier:
        mask = frontier.pop()
        for v in addable(pred, mask):
            new = mask | (1 << v)
            if new not in found:
                found.add(new)
                frontier.append(new)
    return sorted(found)


def bottleneck_family():
    rows = []
    for n in [2, 3, 4, 6, 8, 10]:
        supports = [{q} for q in range(n)]
        supports += [{q, q+1} for q in range(n-1)]
        central = len(supports)
        supports += [{n-1}]
        supports += [{q, q+1} for q in reversed(range(n-1))]
        supports += [{q} for q in range(n)]
        edges, prev, following, weights = wiring(supports)
        pred = order(len(supports), edges)
        states = reachable_ideals(pred)
        A = 3*2**(n-1)-1
        assert len(supports) == 4*n-1 and len(states) == 2*A
        signs = np.array([1. if not mask & (1 << central) else -1. for mask in states])
        assert signs.sum() == 0 and abs(weights[central]-1/12) < 1e-15
        assert sum(central in addable(pred, mask) for mask in states) == 1
        assert max(sum(q in s for s in supports) for q in range(n)) <= 6
        L = ideal_laplacian(pred, states, weights)
        rayleigh = float(signs@(L@signs)/(signs@signs))
        upper = 2*weights[central]/A
        assert abs(rayleigh-upper) < 1e-14
        spectrum = np.sort(eigsh(L, k=2, which='SM', tol=1e-10, return_eigenvectors=False))
        assert abs(spectrum[0]) < 1e-11 and 0 < spectrum[1] <= upper+1e-11
        rows.append(dict(work_qubits=n, events=len(supports), ideal_clock_states=len(states),
                         states_each_side=A, bridge_weight=weights[central],
                         rayleigh_upper_bound=upper, measured_constraint_gap=float(spectrum[1])))
    return rows


def continuum_clock_bounds():
    rows = []
    for side in [24, 48, 96, 192]:
        a, N, M = 1./side, side**3, (side//12)**3
        Jstar, omega = 2.71, np.sqrt(.31**2+4*.4**2)
        product = .5*(N+M)*Jstar**2*a**4
        rounding = a**6*(M*omega+3.)
        rows.append(dict(side=side, lattice_spacing=a, work_sites=N+M,
                         microscopic_round_duration=a**6, macroscopic_round_duration=a**8,
                         rounds_at_T_one=side**8, event_bits_at_T_one=(3*N+5*M)*side**8,
                         product_error_bound=product, rounding_error_bound=rounding))
    assert all(rows[i+1]['product_error_bound'] < .51*rows[i]['product_error_bound']
               for i in range(len(rows)-1))
    return dict(rows=rows, scope='Analytic resource/error bounds, not exponentially large circuit simulations. The previous dressed-band error must also be added.')


def main():
    root = Path(__file__).resolve().parents[1]
    small, motif, supports = examples()
    report = dict(two_work_qubit_clock=small, coupled_geometry_matter_clock=motif,
                  uniform_strength_loads=strength_loads(supports),
                  local_bottleneck=bottleneck_family(), continuum_encoding=continuum_clock_bounds())
    names = ['LOCAL_CAUSAL_CLOCK.md', 'scripts/local_causal_clock_audit.py',
             'UnifiedTheory/Audit/KFCausalLocalClock.lean', 'CAUSAL_ORDER_CLOCK_BRIDGE.md',
             'scripts/causal_order_clock_audit.py', 'UnifiedTheory/Audit/KFCausalOrderClock.lean',
             'PROJECTED_GEOMETRY_AND_LOCAL_DYNAMICS.md', 'COLLECTIVE_SPACETIME_TEST.md']
    report['source_sha256'] = {name: hashlib.sha256((root/name).read_bytes()).hexdigest() for name in names}
    report['scope'] = ('An exact local constraint and local single-readout clock for supplied circuits, '
                       'with a conditional Schroedinger continuum encoding. Event selection, physical '
                       'duration calibration, preparation, Lorentzian geometry, and Einstein dynamics '
                       'remain unproved. Constraint spectrum is not physical frequency.')
    (root/'data/local_causal_clock_audit.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
