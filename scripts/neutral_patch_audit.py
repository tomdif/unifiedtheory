#!/usr/bin/env python3
"""Neutral first-patch paths and a scoped quantum Markov construction.

The mixing/counting asymptotics are external analytic suppliers. The
Lindblad model is not derived from the previous Hamiltonian reservoir.
"""
import hashlib
import itertools as it
import json
import math
from collections import Counter
from pathlib import Path

import networkx as nx
import sympy as s

from autonomous_geometry_audit import connected, flip_in_place
from geometry_entropy_audit import regular_graphs, flip_neighbors
from patch_geometry_audit import patch_tester
from quantum_geometry_phase_audit import square_count


def plateau_graph():
    projective = set()
    for v in it.product(range(5), repeat=3):
        if any(v):
            inverse = pow(next(x for x in v if x), -1, 5)
            projective.add(tuple(x*inverse % 5 for x in v))
    points = sorted(projective)
    edges = [(i, 31+j) for i, p in enumerate(points) for j, line in enumerate(points)
             if sum(a*b for a, b in zip(p, line)) % 5 == 0]
    adj = [set() for _ in range(124)]
    for index, (a, b) in enumerate(edges):
        for sheet in range(2):
            x, y = 2*a+sheet, 2*b+(sheet ^ int(index == 0))
            adj[x].add(y)
            adj[y].add(x)
    assert connected(adj) and square_count(adj) == 0
    return adj


def patch_gadget(n=88):
    vertices = sorted(v for v in it.product(range(-3, 4), repeat=3)
                      if sum(map(abs, v)) <= 3)
    lookup = {v: i for i, v in enumerate(vertices)}
    adj = [set() for _ in range(n)]
    for i, v in enumerate(vertices):
        for axis in range(3):
            w = list(v)
            w[axis] += 1
            j = lookup.get(tuple(w))
            if j is not None:
                adj[i].add(j)
                adj[j].add(i)
    assert sum(map(len, adj))//2 == 114
    deficit = [6-len(adj[i]) for i in range(63)]
    assert Counter(deficit) == {0: 25, 3: 8, 4: 24, 5: 6}
    cursor = 0
    for i in range(63):
        for _ in range(deficit[i]):
            j = 63+cursor % (n-63)
            cursor += 1
            adj[i].add(j)
            adj[j].add(i)
    assert cursor == 150
    remaining = [6-len(adj[j]) for j in range(63, n)]
    outside = nx.havel_hakimi_graph(remaining)
    # Havel-Hakimi may move zero-degree entries to the end of its labels.
    buckets = {d: [j for j, value in enumerate(remaining) if value == d]
               for d in set(remaining)}
    labels = {j: buckets[outside.degree(j)].pop() for j in outside}
    for i, j in outside.edges():
        a, b = labels[i]+63, labels[j]+63
        adj[a].add(b)
        adj[b].add(a)
    assert connected(adj) and all(len(a) == 6 for a in adj)
    return adj, lookup[(0, 0, 0)]


def edge_list(adj):
    return [(i, j) for i, row in enumerate(adj) for j in sorted(row) if i < j]


def attach_core(gadget, core):
    # Counting injection only; this switch joins initially separate graphs.
    a, b = next((i, j) for i, j in edge_list(gadget) if j >= 63)
    u, v = edge_list(core)[0]
    offset = len(gadget)
    joined = [set(row) for row in gadget] + [{j+offset for j in row} for row in core]
    for x, y in [(a, b), (u+offset, v+offset)]:
        joined[x].remove(y)
        joined[y].remove(x)
    for x, y in [(a, u+offset), (b, v+offset)]:
        joined[x].add(y)
        joined[y].add(x)
    assert connected(joined) and all(len(row) == 6 for row in joined)
    # Invert using the fixed gadget/core partition and its two crossing edges.
    crossing = [(i, j-offset) for i in range(offset) for j in joined[i] if j >= offset]
    assert len(crossing) == 2
    recovered = [{j-offset for j in joined[i+offset] if j >= offset}
                 for i in range(len(core))]
    u1, v1 = [j for _, j in crossing]
    recovered[u1].add(v1)
    recovered[v1].add(u1)
    assert recovered == core
    return joined


def gadget_checks():
    good = patch_tester()
    gadget, root = patch_gadget()
    assert [i for i in range(88) if good(gadget, i)] == [root]
    assert not list(nx.bridges(nx.Graph(edge_list(gadget))))
    for n in range(89, 95):
        adj, r = patch_gadget(n)
        assert good(adj, r)
    pairs, masks = regular_graphs(8, 6)
    assert len(masks) == 105
    outputs = set()
    for mask in masks:
        core, _ = flip_neighbors(8, pairs, mask)
        joined = attach_core(gadget, core)
        assert good(joined, root)
        outputs.add(tuple(edge_list(joined)))
    assert len(outputs) == 105
    for size in [7, 16, 36, 64]:
        graph = nx.random_regular_graph(6, size, seed=size)
        core = [set(graph[i]) for i in range(size)]
        assert good(attach_core(gadget, core), root)
    # Exact finite ratio of pairing counts; the simplicity factors tend to
    # the same constant in numerator/denominator by the cited theorem.
    rows = []
    for n in [1000, 10000, 100000, 1000000]:
        k = 88
        log_ratio = (sum(math.log(3*n-j) for j in range(3*k))
                     - sum(math.log(6*n-j) for j in range(6*k))
                     + 3*k*math.log(2)+k*math.log(720))
        asymptotic = 88*math.log(10/3)-264*math.log(n)
        rows.append(dict(vertices=n, log_ratio_error=log_ratio-asymptotic))
    assert abs(rows[-1]['log_ratio_error']) < 0.02
    return dict(minimum_vertices_for_one_good_root=88, ball_vertices=63,
                ball_edges=114, outgoing_stubs=150, required_outside_vertices=25,
                minimal_gadget_good_roots=[root], small_sizes_checked=list(range(88, 95)),
                exhaustive_core_states=105, injective_images=105,
                asymptotic_event_mass_lower_bound='((10/3)^88+o(1))*N^(-264)',
                expected_proposal_bound='O(N^280 log N)',
                expected_physical_time_bound='O(N^279 log N / gamma)',
                pairing_ratio_checks=rows)


def replay_plateau(root):
    witness = json.loads((root/'data/neutral_patch_path.json').read_text())
    adj, good = plateau_graph(), patch_tester()
    assert all(len(a) == 6 for a in adj)
    assert not any(good(adj, v) for v in range(124))
    tested = 124
    for index, path in enumerate(witness['path']):
        a, b, c, d = path
        assert len(set(path)) == 4 and b in adj[a] and c in adj[b] and d in adj[c]
        assert c not in adj[a] and d not in adj[b]
        flip_in_place(adj, path)
        assert connected(adj) and all(len(a) == 6 for a in adj)
        roots = [v for v in range(124) if good(adj, v)]
        tested += 124
        if index+1 < len(witness['path']):
            assert not roots
        else:
            assert roots == witness['good_roots'] == [31]
    assert len(witness['path']) == 3360 and witness['final_defects'] == 123
    return dict(vertices=124, certified_moves=3360, neutral_moves=3359,
                final_defect_drop=1, final_good_roots=[31], rooted_patch_tests=tested,
                valid_degree_and_connectivity_at_every_step=True,
                scope='Existence witness found with target-guided search, not a typical stochastic trajectory.')


def quantum_markov_checks():
    def unit(i, j):
        return s.SparseMatrix(4, 4, {(i, j): 1})
    target, hub = 0, 3
    H = unit(1, hub)+unit(hub, 1)+unit(2, hub)+unit(hub, 2)
    cooling = unit(target, hub)
    dark = s.Matrix([0, 1, -1, 0])/s.sqrt(2)
    rho_dark = dark*dark.T

    def dissipator(L, rho):
        gram = L.conjugate().T*L
        return L*rho*L.conjugate().T-(gram*rho+rho*gram)/2

    assert H*dark == s.zeros(4, 1) and cooling*dark == s.zeros(4, 1)
    assert -s.I*(H*rho_dark-rho_dark*H)+dissipator(cooling, rho_dark) == s.zeros(4)
    jumps = [unit(3, 1), unit(1, 3), unit(3, 2), unit(2, 3), cooling]
    diagonal_H = s.diag(0, 1, 1, 1)

    def generator(rho):
        return (-s.I*(diagonal_H*rho-rho*diagonal_H)
                + sum((dissipator(L, rho) for L in jumps), s.zeros(4)))

    Q = s.Matrix([[0, 0, 0, 1], [0, -1, 0, 1], [0, 0, -1, 1], [0, 1, 1, -3]])
    superop = s.zeros(16)
    for i, j in it.product(range(4), repeat=2):
        E = unit(i, j)
        out = generator(E)
        assert s.trace(out) == 0
        assert s.Matrix([out[k, k] for k in range(4)]) == Q*s.Matrix([E[k, k] for k in range(4)])
        superop[:, 4*i+j] = s.Matrix(list(out))
    killed = Q[1:4, 1:4]
    assert killed.eigenvals() == {-1: 1, -2-s.sqrt(3): 1, -2+s.sqrt(3): 1}
    assert -killed.T.inv()*s.ones(3, 1) == s.Matrix([4, 4, 3])
    assert superop.nullspace() == [s.Matrix([1]+[0]*15)]
    # Exact finite collision step, with distinct zero-energy neutral records.
    # Fresh pure registers are supplied; this is not an autonomous bath limit.
    gram_sum = sum((L.T*L for L in jumps), s.zeros(4))
    K0 = s.diag(1, s.sqrt(3)/2, s.sqrt(3)/2, s.Rational(1, 2))
    assert K0.T*K0+gram_sum/4 == s.eye(4)
    V = K0.col_join(s.Matrix.vstack(*(L/2 for L in jumps)))
    bath_energy = [0, 0, 0, 0, 0, 1]
    total_energy = s.diag(*(bath_energy[b]+int(i != 0) for b in range(6) for i in range(4)))
    assert V.T*V == s.eye(4) and total_energy*V == V*diagonal_H
    # A weighted permutation jump has the same diagonal closure; it need
    # not identify the complete input graph in its emitted record.
    perm, weights = [2, 3, 0, 1], [1, 0, 2, 1+s.I]
    M = s.zeros(4)
    for j, i in enumerate(perm):
        M[i, j] = weights[j]
    gram = M.conjugate().T*M
    assert gram.is_diagonal()
    for i, j in it.product(range(4), repeat=2):
        E = unit(i, j)
        out = dissipator(M, E)
        expected = s.zeros(4, 1)
        if i == j:
            rate = s.expand_complex(weights[j]*s.conjugate(weights[j]))
            expected[perm[j]] += rate
            expected[j] -= rate
        assert s.simplify(s.Matrix([out[k, k] for k in range(4)])-expected) == s.zeros(4, 1)
    # Exact block absorption bound from mixing of an unrestricted chain.
    symmetric_Q = Q.copy()
    symmetric_Q[0, 0], symmetric_Q[3, 0] = -1, 1
    P = s.eye(4)+symmetric_Q/4
    block = P**8
    assert all(sum(abs(block[i, j]-s.Rational(1, 4)) for i in range(4))/2
               <= s.Rational(1, 8) for j in range(4))
    killed_P = P[1:4, 1:4]
    assert all(sum((killed_P**8)[:, j]) <= s.Rational(7, 8) for j in range(3))
    return dict(coherent_classically_accessible_dark_state='(|1>-|2>)/sqrt(2)',
                coherent_dark_stationarity_exact=True, all_matrix_units_checked=16,
                weighted_partial_permutation_units_checked=16,
                killed_generator_eigenvalues=['-1', '-2-sqrt(3)', '-2+sqrt(3)'],
                exact_mean_absorption_times=[4, 4, 3], unique_markov_stationary_state='|0><0|',
                finite_collision_isometry_dimension=[24, 4], exact_collision_energy_intertwining=True,
                mixing_block_steps=8, block_survival_bound='7/8',
                scope='Exact finite Lindblad model; no autonomous Hamiltonian bath limit is derived.')


def main():
    root = Path(__file__).resolve().parents[1]
    report = dict(gadget=gadget_checks(), plateau_path=replay_plateau(root),
                  quantum_markov=quantum_markov_checks())
    names = ['NEUTRAL_PATCH_NUCLEATION.md', 'scripts/neutral_patch_audit.py',
             'UnifiedTheory/Audit/KFCausalNeutralPatch.lean', 'data/neutral_patch_path.json',
             'RESERVOIR_GEOMETRY_PREPARATION.md', 'scripts/reservoir_geometry_audit.py',
             'PATCH_GEOMETRY_PROTECTION.md', 'scripts/patch_geometry_audit.py',
             'GEOMETRY_ENTROPY_OBSTRUCTION.md', 'scripts/geometry_entropy_audit.py']
    report['source_sha256'] = {name: hashlib.sha256((root/name).read_bytes()).hexdigest() for name in names}
    report['scope'] = ('First supplied cubic neighborhood in a specified quantum Markov model; '
                       'positive-density order and a physical unitary reservoir remain open.')
    (root/'data/neutral_patch_audit.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
