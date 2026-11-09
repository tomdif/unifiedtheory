#!/usr/bin/env python3
"""Exact finite entropy/sector checks and a reproducible local-flip stress test.

The stochastic stress test is not real-time quantum evolution or a certified
equilibrium sample. The large-size claims use the proofs and cited theorems
in GEOMETRY_ENTROPY_OBSTRUCTION.md, not finite numerical extrapolation.
"""
import hashlib
import itertools as it
import json
import math
import random
from collections import Counter, defaultdict, deque
from fractions import Fraction as F
from pathlib import Path

import numpy as np
import sympy as s

from balanced_quantum_geometry_audit import build, edge, structure
from quantum_geometry_phase_audit import torus


def regular_graphs(n, degree):
    pairs = list(it.combinations(range(n), 2))
    bits = {e: 1 << i for i, e in enumerate(pairs)}

    def visit(v, remaining, mask):
        if v == n:
            yield mask
            return
        candidates = [j for j in range(v+1, n) if remaining[j]]
        if remaining[v] > len(candidates):
            return
        for chosen in it.combinations(candidates, remaining[v]):
            new = remaining[:]
            new[v] = 0
            added = 0
            for j in chosen:
                new[j] -= 1
                added |= bits[v, j]
            active = sum(r > 0 for r in new)
            if active and max(new) >= active:
                continue
            yield from visit(v+1, new, mask | added)

    return pairs, list(visit(0, [degree]*n, 0))


def flip_neighbors(n, pairs, mask):
    bits = {e: 1 << i for i, e in enumerate(pairs)}
    adj = [set() for _ in range(n)]
    for e, (a, b) in enumerate(pairs):
        if mask >> e & 1:
            adj[a].add(b)
            adj[b].add(a)
    weights = Counter()
    for a in range(n):
        for b in adj[a]:
            for c in adj[b]-{a}:
                if c in adj[a]:
                    continue
                for d in adj[c]-{a, b}:
                    if d not in adj[b]:
                        changed = mask ^ bits[edge(a, b)] ^ bits[edge(c, d)]
                        changed ^= bits[edge(a, c)] ^ bits[edge(b, d)]
                        # S sums forward AND reverse for every ordered tuple.
                        weights[changed] += 2
    return adj, weights


def exact_regular_checks():
    results = []
    for n, degree, total_expected, connected_expected in [(6, 3, 70, 70), (8, 3, 19355, 19320), (8, 4, 19355, 19355)]:
        pairs, graphs = regular_graphs(n, degree)
        assert len(graphs) == total_expected and len(set(graphs)) == len(graphs)
        connected = []
        for mask in graphs:
            links = tuple((mask >> e) & 1 for e in range(len(pairs)))
            adj, _, parts = structure(n, pairs, links)
            assert all(len(a) == degree for a in adj)
            if len(parts) == 1:
                connected.append(mask)
        assert len(connected) == connected_expected
        lookup = {mask: j for j, mask in enumerate(connected)}
        parents = list(range(len(connected)))

        def find(i):
            while parents[i] != i:
                parents[i] = parents[parents[i]]
                i = parents[i]
            return i

        triangle_histogram, row_histogram = Counter(), Counter()
        directed_transitions = 0
        for i, mask in enumerate(connected):
            adj, weights = flip_neighbors(n, pairs, mask)
            triangles = sum(len(adj[a] & adj[b]) for a, b in pairs if b in adj[a])//3
            triangle_histogram[triangles] += 1
            row_histogram[sum(weights.values())] += 1
            directed_transitions += len(weights)
            for changed, weight in weights.items():
                assert weight > 0 and changed in lookup
                parents[find(i)] = find(lookup[changed])
            if n == 6:
                # Independent ordered-quadruple construction checks the factor two.
                bits = {e: 1 << j for j, e in enumerate(pairs)}
                direct = Counter()
                for a, b, c, d in it.permutations(range(n), 4):
                    control = bits[edge(b, c)]
                    old = bits[edge(a, b)] | bits[edge(c, d)]
                    new = bits[edge(a, c)] | bits[edge(b, d)]
                    if mask & control and (((mask & old) == old and (mask & new) == 0)
                                           or ((mask & new) == new and (mask & old) == 0)):
                        direct[mask ^ old ^ new] += 1
                assert direct == weights
                for changed, weight in weights.items():
                    assert flip_neighbors(n, pairs, changed)[1][mask] == weight
        components = len({find(i) for i in range(len(connected))})
        assert components == 1
        results.append(dict(sites=n, degree=degree, all_regular_graphs=len(graphs),
                            connected_regular_graphs=len(connected), flip_components=components,
                            directed_distinct_transitions=directed_transitions,
                            triangles=dict(sorted(triangle_histogram.items())),
                            ordered_exchange_row_sums=dict(sorted(row_histogram.items()))))
    return results


def exact_sector_checks():
    # An actual full capped Gauss Hamiltonian has the uniform regular vacuum.
    p = dict(U=F(1), dbar=F(2), epsilon=F(1), kappa=F(0), rho=F(1),
             t=F(0), m0=F(0), **{'lambda': F(0)})
    pairs, states, info, H, _ = build(4, 2, p)
    support = [i for i, (links, (adj, matter, parts)) in enumerate(zip(states, info))
               if all(len(a) == 2 for a in adj) and 2 not in links and len(parts) == 1]
    assert len(support) == 3
    vector = [int(i in support) for i in range(len(states))]
    output = [F(0)]*len(states)
    for (i, j), value in H.items():
        output[i] += value*vector[j]
    assert not any(output)

    # Project the genuine v2 matrix onto K4, empty matter and trivial flux.
    # Nonzero wedge couplings survive as diagonal energies after compression.
    p.update(U=F(7, 5), dbar=F(3), epsilon=F(2, 7), kappa=F(2, 5))
    p['lambda'] = F(3, 11)
    pairs, states, info, H, _ = build(4, 3, p)
    k4 = states.index((1,)*6)
    assert H[k4, k4] == 12*p['kappa']+4*p['lambda']
    # Exact coefficient -PVQ H0^{-1} QVP in a finite-size expansion.
    second_order = F(0)
    excursions = Counter()
    for (i, j), value in H.items():
        if j == k4 and i != k4:
            adj, matter, _ = info[i]
            assert not any(matter)
            denominator = p['U']/2*sum((len(a)-3)**2 for a in adj)+p['epsilon']*states[i].count(2)
            assert denominator > 0
            second_order -= value**2/denominator
            excursions['magnetic' if states[i].count(2) else 'wedge'] += 1
    predicted = -24*p['kappa']**2/p['U']-4*p['lambda']**2/(3*p['epsilon'])
    assert second_order == predicted and excursions == dict(wedge=6, magnetic=4)
    return dict(uniform_cycle_support=3, full_gauss_dimension=249, exact_ground_vector=True,
                k4_compressed_diagonal=str(H[k4, k4]), k4_expected_diagonal='12*kappa+4*lambda',
                k4_second_order_coefficient=str(second_order), excursions=dict(excursions),
                scope='Exact projection and perturbative coefficient; no uniform thermodynamic expansion claimed.')


def quantum_weight_checks():
    # Rational positive matrices B=e^{-H}; H=-log B is well-defined Hermitian.
    # Event projectors need not commute with H or B.
    trials = []
    lo, hi = s.Rational(1, 4), s.Integer(4)
    for v in [s.Matrix([1, 2, 3]), s.Matrix([2, 1, 1])]:
        Q = s.eye(3)-2*v*v.T/(v.T*v)[0]
        assert Q.T*Q == s.eye(3)
        B = Q*s.diag(lo, 1, hi)*Q.T
        for rank in [1, 2]:
            for selected in it.combinations(range(3), rank):
                P = s.diag(*[int(i in selected) for i in range(3)])
                probability = s.factor(s.trace(P*B)/s.trace(B))
                sharp = rank*hi/(rank*hi+(3-rank)*lo)
                simple = s.Rational(rank, 3)*hi/lo
                assert probability <= sharp <= simple
                assert P*B != B*P
                trials.append(dict(rank=rank, probability=str(probability), sharp_bound=str(sharp)))
    # Extremal commuting choice saturates the sharper bound exactly.
    assert hi/(hi+2*lo) == s.Rational(8, 9)
    return dict(noncommuting_exact_trials=len(trials), spectral_ratio='16',
                trials=trials, rank_one_sharp_saturation='8/9')


def graph_metrics(adj):
    n = len(adj)
    distances_sum, diameter, balls = 0, 0, [0]*5
    for start in range(n):
        distances = [-1]*n
        distances[start] = 0
        todo = deque([start])
        while todo:
            v = todo.popleft()
            for w in adj[v]:
                if distances[w] < 0:
                    distances[w] = distances[v]+1
                    todo.append(w)
        assert min(distances) == 0
        diameter = max(diameter, max(distances))
        distances_sum += sum(distances)
        for r in range(5):
            balls[r] += sum(d <= r for d in distances)
    A = np.zeros((n, n))
    for v, neighbors in enumerate(adj):
        A[v, neighbors] = 1
    eigenvalues = np.linalg.eigvalsh(6*np.eye(n)-A)
    assert abs(eigenvalues[0]) < 1e-10 and eigenvalues[1] > 0
    return dict(diameter=diameter, mean_pair_distance=distances_sum/(n*(n-1)),
                mean_balls=[b/n for b in balls], spatial_laplacian_gap=float(eigenvalues[1]))


def local_flip_stress():
    results = []
    for length in [4, 6, 8]:
        vertices, edges = torus(length)
        n = len(vertices)
        initial = [set() for _ in range(n)]
        for a, b in edges:
            initial[a].add(b)
            initial[b].add(a)
        before = graph_metrics([sorted(a) for a in initial])
        expected_gap = 2-2*math.cos(2*math.pi/length)
        assert abs(before['spatial_laplacian_gap']-expected_gap) < 1e-10
        assert before['diameter'] == 3*(length//2)
        trials = []
        for seed in [1729, 2718, 3141]:
            rng = random.Random(seed)
            adj = [sorted(a) for a in initial]
            accepted = 0
            attempts = 100*n
            for _ in range(attempts):
                a = rng.randrange(n)
                b = rng.choice(adj[a])
                c = rng.choice(adj[b])
                d = rng.choice(adj[c])
                if len({a, b, c, d}) == 4 and c not in adj[a] and d not in adj[b]:
                    for v, old, new in [(a, b, c), (b, a, d), (c, d, a), (d, c, b)]:
                        adj[v].remove(old)
                        adj[v].append(new)
                        adj[v].sort()
                    accepted += 1
            assert all(len(a) == 6 and len(set(a)) == 6 for a in adj)
            assert all(v in adj[w] for v, row in enumerate(adj) for w in row)
            trials.append(dict(seed=seed, attempts=attempts, accepted=accepted,
                               metrics=graph_metrics(adj)))
        results.append(dict(cubic_length=length, sites=n, before=before, trials=trials))
    return dict(rows=results, scope='Finite stochastic stress test, not real-time unitary evolution; no mixing certificate.')


def main():
    root = Path(__file__).resolve().parents[1]
    report = dict(exact_regular_graphs=exact_regular_checks(), exact_sectors=exact_sector_checks(),
                  quantum_event_bounds=quantum_weight_checks(), local_flip_stress=local_flip_stress(),
                  scope='Analytic entropy obstruction and cited asymptotic graph results; full TOE remains open.')
    names = ['GEOMETRY_ENTROPY_OBSTRUCTION.md', 'scripts/geometry_entropy_audit.py',
             'UnifiedTheory/Audit/KFCausalGeometryEntropy.lean', 'RELATIONAL_QUANTUM_GEOMETRY_V2.md',
             'scripts/balanced_quantum_geometry_audit.py', 'scripts/quantum_geometry_phase_audit.py']
    report['source_sha256'] = {name: hashlib.sha256((root/name).read_bytes()).hexdigest() for name in names}
    (root/'data/geometry_entropy_audit.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
