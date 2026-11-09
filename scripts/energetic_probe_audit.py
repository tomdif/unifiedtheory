#!/usr/bin/env python3
"""Energetic constraints: exact algebra, finite dynamics, and graph locality.

The size-uniform theorem and graph support proof are analytic. Numerical
state-vector checks below do not certify a full fluctuating spacetime cone.
"""
import hashlib
import json
from collections import Counter
from fractions import Fraction as F
from pathlib import Path

import numpy as np
import sympy as sy
from scipy.linalg import expm, norm
from scipy import sparse as sp
from scipy.sparse.linalg import expm_multiply

from autonomous_geometry_audit import ball, flip_in_place, paths
from patch_geometry_audit import rectangular_torus, patch_tester


def comm(a, b):
    return a @ b - b @ a


def row_bound(a):
    return float(np.max(np.asarray(abs(a).sum(axis=1))))


def exact_algebra():
    P = sy.diag(1, 1, 0, 0)
    R = sy.eye(4)-P
    K = sy.Matrix([[2, sy.I, 1, 2-sy.I], [-sy.I, -1, sy.I, 3],
                   [1, -sy.I, 4, 1+sy.I], [2+sy.I, 3, 1-sy.I, -2]])
    D = P*K*P+R*K*R
    V = P*K*R+R*K*P
    S = comm(R, V)
    delta = sy.symbols('Delta', real=True)
    H0 = delta*R+D
    identities = [K-D-V, comm(P, comm(P, K))-V,
                  comm(R, S)-V, S.conjugate().T+S,
                  comm(K, V)+comm(P, comm(K, comm(K, P))),
                  (H0+V)*S-S*H0-delta*V-comm(D, S)-V*S]
    assert all(a.applyfunc(sy.simplify) == sy.zeros(4) for a in identities)
    # A two-bad-site bridge leaves a nonzero virtual good-to-good entry.
    C = sy.Matrix([[delta, -1], [-1, delta]])
    effective = -C.inv()
    assert sy.simplify(effective[0, 1]+1/(delta**2-1)) == 0
    return dict(exact_operator_identities=len(identities),
                virtual_two_bad_site_bridge_at_energy_zero='-1/(Delta^2-1)',
                bridge_scope='Unit hopping, Delta>1; exact energy-dependent Schur complement at E=0.')


def generic_dynamics():
    rng = np.random.default_rng(73129)
    raw = rng.normal(size=(6, 6))+1j*rng.normal(size=(6, 6))
    K = (raw+raw.conj().T)/6
    P = np.diag([1., 1., 1., 0., 0., 0.])
    R = np.eye(6)-P
    D, V = P@K@P+R@K@R, P@K@R+R@K@P
    v, c = norm(V, 2), norm(comm(D, V), 2)
    assert c <= norm(comm(K, comm(K, P)), 2)+1e-12
    rows = []
    for delta in [8., 32., 128.]:
        for t in [.2, 1., 3.]:
            U = expm(-1j*t*(delta*R+K))
            U0 = expm(-1j*t*(delta*R+D))
            error = norm(U-U0, 2)
            bound = (2*v+t*(c+v*v))/delta
            leakage = norm(R@U@P, 2)
            assert error <= bound+1e-11 and leakage <= error+1e-11
            rows.append(dict(penalty=delta, time=t, full_operator_error=error,
                             commutator_bound=bound, leakage_amplitude=leakage))
    # Large, independently evolving spectator energies need not increase c.
    remote = np.diag(np.arange(5)*10000.)
    Kbig = np.kron(K, np.eye(5))+np.kron(np.eye(6), remote)
    Pbig = np.kron(P, np.eye(5))
    actual = comm(Kbig, comm(Kbig, Pbig))
    expected = np.kron(comm(K, comm(K, P)), np.eye(5))
    assert norm(actual-expected, 2) < 1e-10
    return dict(rows=rows, off_diagonal_norm=v, diagonal_off_diagonal_commutator_norm=c,
                spectator_dimension=5, bare_norm=norm(K, 2),
                spectator_bare_norm=norm(Kbig, 2),
                spectator_double_commutator_residual=norm(actual-expected, 2))


def adjacency_matrix(adj):
    rows, cols = [], []
    for a, neighbors in enumerate(adj):
        for b in sorted(neighbors):
            rows.append(a)
            cols.append(b)
    return sp.csr_matrix((np.ones(len(rows)), (rows, cols)), shape=(len(adj), len(adj)))


def actual_joint_snapshots():
    coords, adj0 = rectangular_torus((8, 8, 8))
    lookup = {v: i for i, v in enumerate(coords)}
    path = tuple(lookup[(x, 0, 0)] for x in range(4))
    assert path in set(paths(adj0, [path[0]]))
    good = patch_tester()
    assert good(adj0, 0)  # all other roots by exact torus translation
    adj1 = [set(a) for a in adj0]
    affected = ball(adj0, path, 3)
    flip_in_place(adj1, path)
    q0 = np.ones(len(adj0))
    q1 = np.ones(len(adj0))
    for v in sorted(affected):
        q1[v] = int(good(adj1, v))
    assert 0 < int(sum(1-q1)) <= 748
    # Independently recognize every supposedly untouched root in this example.
    assert all(good(adj1, v) for v in range(len(adj1)) if v not in affected)
    n = len(adj0)
    rho, J, kappa = .3, .04, .2
    G = rho*sp.kron(sp.csr_matrix([[1., -1.], [-1., 1.]]), sp.eye(n), format='csr')
    E = sp.diags(np.repeat([0., J*sum(1-q1)], n), format='csr')
    T = -kappa*sp.block_diag([adjacency_matrix(adj0), adjacency_matrix(adj1)], format='csr')
    K, P = G+E+T, sp.diags(np.r_[q0, q1], format='csr')
    R = sp.eye(2*n, format='csr')-P
    D, V = P@K@P+R@K@R, P@K@R+R@K@P
    second = comm(K, comm(K, P))
    assert row_bound(comm(K, V)+comm(P, second)) < 1e-12
    assert row_bound(comm(G, comm(T, P))+comm(T, comm(G, P))
                     -comm(comm(G, T), P)-2*comm(T, comm(G, P))) < 1e-12
    assert row_bound(comm(E, comm(T, P))) == 0
    vbound, cbound = row_bound(V), row_bound(comm(D, V))
    assert row_bound(comm(G, T)) > 0
    # A local state, a delocalized good state, and a geometry superposition.
    states = np.zeros((2*n, 3), dtype=complex)
    states[0, 0] = 1
    states[:, 1] = np.r_[q0, q1]/np.sqrt(sum(q0)+sum(q1))
    protected = int(np.flatnonzero(q1)[0])
    states[protected, 2] = 1/np.sqrt(2)
    states[n+protected, 2] = 1j/np.sqrt(2)
    assert np.linalg.norm(P@states-states) == 0
    rows = []
    for t in [.5, 2.]:
        gated = expm_multiply(-1j*t*(P@K@P), states)
        for delta in [8., 32., 128.]:
            actual = expm_multiply(-1j*t*(K+delta*R), states)
            errors = np.linalg.norm(actual-gated, axis=0)
            leakages = np.linalg.norm(R@actual, axis=0)
            bound = (2*vbound+t*(cbound+vbound**2))/delta
            assert np.all(errors <= bound+1e-9)
            assert np.all(leakages <= errors+1e-9)
            assert max(abs(np.linalg.norm(actual, axis=0)-1)) < 1e-9
            rows.append(dict(time=t, penalty=delta, state_errors=errors.tolist(),
                             leakage_probabilities=(leakages**2).tolist(),
                             operator_error_upper_bound=bound))
    # Projection must retain diagonal move cost; it is not a new Markov Laplacian.
    projected_G = P@G@P
    assert projected_G[0, 0] == rho
    if q1[0] == 0:
        assert projected_G[0, n] == 0
    return dict(vertices=n, joint_dimension=2*n, exchange_path=list(path),
                defects_after_flip=int(sum(1-q1)), recognized_roots_after_flip=n,
                rho=rho, J=J, kappa=kappa, off_diagonal_row_bound=vbound,
                commutator_row_bound=cbound,
                mixed_geometry_hopping_row_bound=row_bound(comm(G, T)), rows=rows,
                scope='Two actual cubic/one-flip graph snapshots with one exchange channel, not the all-graph operator.')


def graph_commutator_cancellation():
    coords, original = rectangular_torus((16, 16, 16))
    lookup = {v: i for i, v in enumerate(coords)}
    original = tuple(frozenset(a) for a in original)
    good = patch_tester()
    qpath = tuple(lookup[(x, 0, 0)] for x in range(4))
    remote = tuple(lookup[(8+x, 8, 8)] for x in range(4))
    assert set(remote).isdisjoint(ball(original, [0], 15))
    values, moves = {}, {}

    def value(state):
        if state not in values:
            values[state] = int(good(state, 0))
        return values[state]

    def move(state, path):
        key = state, path
        if key not in moves:
            a, b, c, d = path
            forward = b in state[a] and d in state[c] and c not in state[a] and d not in state[b]
            backward = c in state[a] and d in state[b] and b not in state[a] and d not in state[c]
            if c not in state[b] or not (forward or backward):
                moves[key] = None
            else:
                new = [set(x) for x in state]
                flip_in_place(new, path)
                moves[key] = tuple(frozenset(x) for x in new)
        return moves[key]

    def apply_h(vector, path):
        out = Counter()
        for state, coeff in vector.items():
            new = move(state, path)
            if new is not None:
                out[state] += coeff
                out[new] -= coeff
        return {a: b for a, b in out.items() if b}

    def apply_p(vector):
        return {a: b*value(a) for a, b in vector.items() if value(a)}

    def inner(vector, path):
        left, right = apply_h(apply_p(vector), path), apply_p(apply_h(vector, path))
        result = Counter(left)
        for a, b in right.items():
            result[a] -= b
        return {a: b for a, b in result.items() if b}

    def nested(state, p, q):
        vector = {state: 1}
        left, right = apply_h(inner(vector, q), p), inner(apply_h(vector, p), q)
        result = Counter(left)
        for a, b in right.items():
            result[a] -= b
        return {a: b for a, b in result.items() if b}

    assert value(original) == 1 and value(move(original, qpath)) == 0
    cases = [(remote, qpath), (qpath, remote), (qpath, qpath)]
    for p in list(paths(original, [0]))[::10]:
        cases.extend([(p, qpath), (qpath, p)])
    # Exercise activation controls that become available only after q.
    after_q = move(original, qpath)
    newly_active = [p for p in paths(after_q, [0]) if move(original, p) is None][:12]
    assert newly_active
    for p in newly_active:
        cases.extend([(p, qpath), (qpath, p)])
    nonzero = 0
    for p, q in cases:
        result = nested(original, p, q)
        if remote in (p, q):
            assert not result
        if result:
            nonzero += 1
            assert set(p+q) <= ball(original, [0], 15)
            assert sum(map(abs, result.values())) <= 16
    assert nonzero > 0
    return dict(vertices=len(original), tested_ordered_channel_pairs=len(cases),
                nonzero_pairs=nonzero, remote_pairs_cancel_exactly=2,
                channels_active_only_after_first_flip=len(newly_active),
                distinct_rooted_neighborhoods_recognized=len(values),
                scope='Exact selected columns; the general radius-15 cancellation lemma is proved in the note.')


def constants_and_shortcut():
    b3 = 1+6*sum(5**i for i in range(3))
    b15 = 1+6*sum(5**i for i in range(15))
    cg = 1200*b3
    assert b3 == 187 and cg == 224400
    assert b15 == (3*5**15-1)//2
    # The old nine-edge route has H^m_uv=0 for m<9 even with onsite penalties.
    # A ten-vertex bridge checks these coefficients exactly; the graph family
    # supplies good endpoints whose old distance diverges.
    delta = 4
    H = sy.zeros(10)
    for i in range(9):
        H[i, i+1] = H[i+1, i] = -1
    for i in range(1, 9):
        H[i, i] = delta
    assert all((H**m)[0, 9] == 0 for m in range(9))
    assert (H**9)[0, 9] == -1
    tail_rows = []
    for penalty in [1, 4, 16, 64]:
        M = penalty+6
        t = F(1, M**10)
        mt = M*t
        exp_upper = 1/(1-mt)
        relative_tail_upper = exp_upper*F(M**10, 10)*t
        assert mt < 1 and exp_upper < 2 and relative_tail_upper < F(1, 5)
        tail_rows.append(dict(penalty=penalty, unit_hopping_time=str(t),
                              relative_taylor_tail_bound=str(relative_tail_upper)))
    return dict(degree_six_ball3=b3, degree_six_ball15=b15,
                geometry_first_commutator_coefficient=cg,
                geometry_second_commutator_coefficient=str(16*b15**8),
                geometry_energy_mixed_coefficient=748*cg,
                geometry_hopping_mixed_coefficient=4800+24*cg,
                probe_second_commutator_coefficient=144,
                finite_penalty_shortcut_time='kappa^9/(Delta+6*kappa)^10',
                finite_penalty_shortcut_amplitude_lower_bound='kappa^90/(2*9!*(Delta+6*kappa)^90)',
                exact_tail_checks=tail_rows)


def main():
    root = Path(__file__).resolve().parents[1]
    report = dict(exact_algebra=exact_algebra(), generic_dynamics=generic_dynamics(),
                  joint_snapshots=actual_joint_snapshots(),
                  graph_cancellation=graph_commutator_cancellation(),
                  constants_and_shortcut=constants_and_shortcut())
    names = ['ENERGETIC_PROBE_SECTOR.md', 'scripts/energetic_probe_audit.py',
             'UnifiedTheory/Audit/KFCausalEnergeticProbe.lean',
             'PATCH_GROWTH_AND_NONCOLLAPSE.md', 'scripts/patch_growth_audit.py',
             'PATCH_GEOMETRY_PROTECTION.md', 'scripts/patch_geometry_audit.py',
             'AUTONOMOUS_GEOMETRY_SELECTION.md', 'scripts/autonomous_geometry_audit.py',
             'RELATIONAL_QUANTUM_GEOMETRY_V2.md']
    report['source_sha256'] = {name: hashlib.sha256((root/name).read_bytes()).hexdigest() for name in names}
    report['scope'] = ('Finite-time energetic approximation uniform in graph size for a supplied neutral '
                       'one-probe extension on the degree-six regular carrier. No exact finite-penalty '
                       'spatial cone, selected geometry, physical charged matter, continuum, or Einstein equation.')
    (root/'data/energetic_probe_audit.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
