#!/usr/bin/env python3
"""Exact coarse-partition counting, reversible preparation, and encoding tests.

No finite scan is a continuum proof. Preparation permutations saturate a
resource bound; they are not claimed to be local physical Hamiltonians.
"""
import hashlib
import itertools as it
import json
import math
from collections import Counter
from fractions import Fraction as F
from pathlib import Path

import numpy as np
import sympy as s

from geometry_entropy_audit import regular_graphs, flip_neighbors


def popcount(value):
    return bin(value).count('1')


def balanced_assignments(n, cells, size):
    assert n == cells*size

    def visit(remaining, groups):
        if len(groups) == cells-1:
            yield groups+[tuple(remaining)]
            return
        for chosen in it.combinations(remaining, size):
            yield from visit(tuple(v for v in remaining if v not in chosen), groups+[chosen])

    for groups in visit(tuple(range(n)), []):
        assignment = [0]*n
        for c, group in enumerate(groups):
            for v in group:
                assignment[v] = c
        yield assignment


def far_mask(pairs, assignment, coarse_edges):
    mask = 0
    for i, (a, b) in enumerate(pairs):
        x, y = assignment[a], assignment[b]
        if x != y and tuple(sorted((x, y))) not in coarse_edges:
            mask |= 1 << i
    return mask


def coarse_partition_checks():
    rows = []
    cases = [(6, 3, 3, 2, {(0, 1), (1, 2)}, 'path3'),
             (8, 3, 4, 2, {(0, 1), (1, 2), (2, 3), (0, 3)}, 'cycle4'),
             (8, 4, 4, 2, {(0, 1), (1, 2), (2, 3), (0, 3)}, 'cycle4')]
    for n, degree, cells, size, coarse_edges, label in cases:
        pairs, graphs = regular_graphs(n, degree)
        assignments = list(balanced_assignments(n, cells, size))
        assert len(assignments) == math.factorial(n)//math.factorial(size)**cells
        masks = sorted({far_mask(pairs, a, coarse_edges) for a in assignments})
        hist = Counter()
        for graph in graphs:
            best = n*degree//2
            for mask in masks:
                best = min(best, popcount(graph & mask))
                if best == 0:
                    break
            hist[best] += 1
        assert sum(hist.values()) == len(graphs)
        rows.append(dict(sites=n, degree=degree, coarse_template=label, cells=cells,
                         cell_size=size, labeled_balanced_assignments=len(assignments),
                         distinct_locality_masks=len(masks), all_regular_graphs=len(graphs),
                         minimum_far_edge_histogram=dict(sorted(hist.items()))))
    return rows


def weighted_generating_function_checks():
    n, cells, size, cap = 6, 3, 2, 3
    pairs = list(it.combinations(range(n), 2))
    far = far_mask(pairs, [0, 0, 1, 1, 2, 2], {(0, 1), (1, 2)})
    nfar, nlocal = popcount(far), len(pairs)-popcount(far)
    assert (nlocal, nfar) == (11, 4)
    histogram, capped = Counter(), Counter()
    for graph in range(1 << len(pairs)):
        count, distant = popcount(graph), popcount(graph & far)
        histogram[count, distant] += 1
        degrees = [0]*n
        for i, (a, b) in enumerate(pairs):
            if graph >> i & 1:
                degrees[a] += 1
                degrees[b] += 1
        if max(degrees) <= cap:
            capped[count, distant] += 1
    weight = lambda e, r: F(1, size)**e * F(1, cells)**r
    summed = sum(count*weight(e, r) for (e, r), count in histogram.items())
    product = (1+F(1, size))**nlocal*(1+F(1, n))**nfar
    assert summed == product
    budget = cap*n//2
    rows = []
    for far_budget in [0, 1, 3, 6]:
        lower = weight(budget, far_budget)
        actual = sum(count for (e, r), count in capped.items() if r <= far_budget)
        flux_rank = sum(count*2**e for (e, r), count in capped.items() if r <= far_budget)
        bound = product/lower
        assert actual <= bound and flux_rank <= 2**budget*bound
        assert all(weight(e, r) >= lower for (e, r) in capped if r <= far_budget)
        rows.append(dict(far_edge_budget=far_budget, allowed_graphs=actual,
                         full_gauss_rank=flux_rank, graph_count_bound=str(bound)))
    # Count every subset independently of the degree constraint.
    assert sum(histogram.values()) == 32768
    return dict(subsets=32768, weighted_sum=str(summed), product=str(product), tests=rows)


def preparation_permutation(D, rank, register):
    # Map |i,0> to the i-th basis vector of system x record, then extend
    # this injection to a permutation of the complete tensor-product basis.
    size = D*register
    mapping = {i*register: i for i in range(D)}
    unused_domain = [i for i in range(size) if i not in mapping]
    unused_range = [i for i in range(size) if i not in set(mapping.values())]
    mapping.update(zip(unused_domain, unused_range))
    assert len(mapping) == size and set(mapping.values()) == set(range(size))
    U = s.SparseMatrix(size, size, {(dest, source): 1 for source, dest in mapping.items()})
    assert U.T*U == s.eye(size)
    rho = s.SparseMatrix(size, size, {(i*register, i*register): s.Rational(1, D) for i in range(D)})
    out = U*rho*U.T
    probability = sum(out[i, i] for i in range(rank*register))
    assert probability == min(s.Integer(1), s.Rational(rank*register, D))
    assert U.T*out*U == rho
    # A coherent input is returned exactly too; no information is deleted.
    psi = s.SparseMatrix(size, 1, {(i*register, 0): s.Integer(i+1) for i in range(D)})
    assert U.T*(U*psi) == psi
    return dict(input_dimension=D, target_rank=rank, record_dimension=register,
                exact_success=str(probability), unitary=True, coherent_recovery=True)


def preparation_checks():
    rows = [preparation_permutation(*case) for case in [(12, 3, 1), (12, 3, 2),
             (12, 3, 4), (70, 10, 7), (70, 1, 70)]]
    return dict(cases=rows, scope='Unrestricted reversible register construction; locality and covariance not asserted.')


def graph_state_encoding_and_leakage():
    n = 6
    pairs, graphs = regular_graphs(n, 3)
    assert len(graphs) == 70
    bits = {e: 1 << i for i, e in enumerate(pairs)}
    control, old, new = bits[1, 2], bits[0, 1] | bits[2, 3], bits[0, 2] | bits[1, 3]

    def flip(graph):
        if graph & control and (((graph & old) == old and (graph & new) == 0)
                                or ((graph & new) == new and (graph & old) == 0)):
            return graph ^ old ^ new
        return graph

    def graph_vector(graph):
        return np.array([(-1)**sum(bool(graph >> i & 1) and bool(x >> a & 1) and bool(x >> b & 1)
                                   for i, (a, b) in enumerate(pairs)) for x in range(1 << n)], dtype=np.int64)

    vectors = {g: graph_vector(g) for g in graphs}
    witness = None
    violations = 0
    for a, b in it.combinations(graphs, 2):
        before = F(int(vectors[a] @ vectors[b]), 1 << n)
        after = F(int(vectors[flip(a)] @ vectors[flip(b)]), 1 << n)
        if abs(before) != abs(after):
            violations += 1
            if witness is None:
                witness = dict(before_graphs=[a, b], after_graphs=[flip(a), flip(b)],
                               before_overlap=str(before), after_overlap=str(after),
                               edge_lists=[[list(e) for i, e in enumerate(pairs) if g >> i & 1]
                                           for g in [a, b, flip(a), flip(b)]])
    assert witness is not None and violations > 0
    assert all(flip(flip(g)) == g for g in graphs)
    # Build the actual 70-state balanced exchange Hamiltonian.
    index = {g: i for i, g in enumerate(graphs)}
    entries, triangles = {}, []
    for g in graphs:
        i = index[g]
        adj, row = flip_neighbors(n, pairs, g)
        entries[i, i] = sum(row.values())
        for changed, w in row.items():
            entries[index[changed], i] = -w
        triangles.append(sum(len(adj[a] & adj[b]) for a, b in pairs if b in adj[a])//3)
    H = s.SparseMatrix(70, 70, entries)
    W = s.zeros(70, 2)
    for i, count in enumerate(triangles):
        W[i, 0 if count == 0 else 1] = 1/s.sqrt(10 if count == 0 else 60)
    assert W.T*W == s.eye(2)
    reduced = s.simplify(W.T*H*W)
    expected = s.Matrix([[144, -24*s.sqrt(6)], [-24*s.sqrt(6), 24]])
    assert reduced == expected and H*W == W*reduced
    assert reduced**2 == 168*reduced
    U = s.eye(2)-reduced/84  # time pi/168, rho=1
    assert s.simplify(U.T*U) == s.eye(2)
    leakage = s.simplify(U[1, 0]**2)
    assert leakage == s.Rational(24, 49)
    # A known coherent uniform reference state can be amplified without a
    # record register. The triangle-occupancy phase is a supplied control.
    omega = s.Matrix([1/s.sqrt(7), s.sqrt(6)/s.sqrt(7)])
    phase = s.diag(1, -1)  # exp(-i*pi*triangle_count/2), since counts are 0 or 2
    assert s.simplify(reduced*omega) == s.zeros(2, 1)
    assert s.simplify(U-(2*omega*omega.T-s.eye(2))) == s.zeros(2)
    assert s.diag(*[(-1)**(count//2) for count in triangles])*W == W*phase
    amplified = s.simplify(U*phase*omega)
    amplified_probability = s.simplify(amplified[0]**2)
    assert amplified_probability == s.Rational(289, 343)
    assert s.simplify(phase*U*amplified-omega) == s.zeros(2, 1)
    return dict(graph_states=70, qubits=6, hilbert_dimension=64,
                pair_comparisons=70*69//2, overlap_magnitude_violations=violations,
                witness=witness, coherent_exchange=dict(
                    reduced_hamiltonian=[['144', '-24*sqrt(6)'], ['-24*sqrt(6)', '24']],
                    leakage_formula='(24/49)*sin(84*rho*t)^2',
                    time_at_rho_one='pi/168', exact_leakage=str(leakage),
                    coherent_initial_target_probability='1/7',
                    coherent_amplified_target_probability=str(amplified_probability),
                    amplified_state=[str(a) for a in amplified],
                    coherent_protocol_inverse_verified=True,
                    maximally_mixed_target_probability_unchanged='1/7',
                    controls='Triangle-occupancy phase followed by exchange pulse; independent controls, not autonomous v2.'),
                scope='Graph-state encoding fails the original conditional flip; six-site class leakage is not a spacetime observable.')


def decoding_bound_checks():
    # Four qubit states with a nonorthogonal, noncommuting tetrahedral POVM.
    I = s.eye(2)
    X, Y, Z = s.Matrix([[0, 1], [1, 0]]), s.Matrix([[0, -s.I], [s.I, 0]]), s.diag(1, -1)
    states = [(I+(a*X+b*Y+c*Z)/s.sqrt(3))/2
              for a, b, c in [(1, 1, 1), (1, -1, -1), (-1, 1, -1), (-1, -1, 1)]]
    effects = [rho/2 for rho in states]
    assert s.simplify(sum(effects, s.zeros(2))) == I
    success = s.simplify(sum(s.trace(e*rho) for e, rho in zip(effects, states))/4)
    assert success == s.Rational(1, 2)
    assert all(s.simplify(rho*rho-rho) == s.zeros(2) for rho in states)
    return dict(states=4, dimension=2, exact_success=str(success), dimension_bound='1/2')


def main():
    root = Path(__file__).resolve().parents[1]
    report = dict(coarse_partitions=coarse_partition_checks(),
                  generating_function=weighted_generating_function_checks(),
                  preparation=preparation_checks(), encoding_and_leakage=graph_state_encoding_and_leakage(),
                  decoding=decoding_bound_checks(),
                  scope='Finite resource and coarse-counting results; no selected geometric phase or TOE.')
    names = ['COARSE_GEOMETRY_AND_PREPARATION.md', 'scripts/coarse_geometry_audit.py',
             'UnifiedTheory/Audit/KFCausalCoarseGeometry.lean', 'GEOMETRY_ENTROPY_OBSTRUCTION.md',
             'scripts/geometry_entropy_audit.py']
    report['source_sha256'] = {name: hashlib.sha256((root/name).read_bytes()).hexdigest() for name in names}
    (root/'data/coarse_geometry_audit.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
