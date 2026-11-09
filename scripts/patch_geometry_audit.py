#!/usr/bin/env python3
"""Finite checks for patch protection, square packing, and virtual exchanges.

Perturbative entries are diagonal matrix coefficients, not a calculation
of the full thermodynamic ground phase or a preparation algorithm.
"""
import hashlib
import itertools as it
import json
import math
from collections import Counter, defaultdict
from fractions import Fraction as F
from pathlib import Path

import networkx as nx
import numpy as np

from autonomous_geometry_audit import (ball, changed_edges, connected,
                                     flip_in_place, paths, triangle_count)
from geometry_entropy_audit import regular_graphs, flip_neighbors


def rectangular_torus(periods):
    vertices = list(it.product(*(range(a) for a in periods)))
    lookup = {v: i for i, v in enumerate(vertices)}
    adj = [set() for _ in vertices]
    for i, v in enumerate(vertices):
        for axis, period in enumerate(periods):
            w = list(v)
            w[axis] = (w[axis]+1) % period
            j = lookup[tuple(w)]
            adj[i].add(j)
            adj[j].add(i)
    return vertices, adj


def patch_tester():
    coordinates = [v for v in it.product(range(-3, 4), repeat=3) if sum(abs(x) for x in v) <= 3]
    reference = nx.Graph()
    reference.add_nodes_from((v, {'root': v == (0, 0, 0)}) for v in coordinates)
    for v in coordinates:
        for axis in range(3):
            w = list(v)
            w[axis] += 1
            if tuple(w) in reference:
                reference.add_edge(v, tuple(w))
    degrees = sorted(dict(reference.degree()).values())
    assert len(reference) == 63

    def good(adj, root):
        sites = ball(adj, [root], 3)
        if len(sites) != 63:
            return False
        patch = nx.Graph()
        patch.add_nodes_from((v, {'root': v == root}) for v in sites)
        patch.add_edges_from((a, b) for a in sites for b in adj[a] & sites)
        if sorted(dict(patch.degree()).values()) != degrees:
            return False
        return nx.is_isomorphic(reference, patch, node_match=lambda x, y: x['root'] == y['root'])

    return good


def canonical_steps(steps, periods):
    # Only actual automorphisms of the given rectangular torus are used.
    representatives = []
    for perm in it.permutations(range(3)):
        if any(periods[i] != periods[perm[i]] for i in range(3)):
            continue
        for signs in it.product([-1, 1], repeat=3):
            sequence = []
            for step in steps:
                new = [0]*3
                for i in range(3):
                    new[perm[i]] = signs[i]*step[i]
                sequence.append(tuple(new))
            representatives.append(tuple(sequence))
            representatives.append(tuple(tuple(-x for x in step) for step in reversed(sequence)))
    return min(representatives)


def virtual_exchange_checks():
    good = patch_tester()
    rows = []
    for periods in [(8, 8, 8), (10, 10, 10), (16, 16, 16), (8, 8, 64),
                    (20, 20, 20), (10, 10, 80)]:
        vertices, adj = rectangular_torus(periods)
        assert good(adj, 0)  # every root follows by translation symmetry
        classes = defaultdict(list)
        for path in paths(adj, [0]):
            steps = [tuple((vertices[b][j]-vertices[a][j]+periods[j]//2) % periods[j]-periods[j]//2
                           for j in range(3)) for a, b in zip(path, path[1:])]
            classes[canonical_steps(steps, periods)].append(path)
        assert sum(map(len, classes.values())) == 150
        coefficient, cost_histogram, class_rows = F(0), Counter(), []
        row_sum_per_vertex = 0
        for signature, members in sorted(classes.items()):
            path = members[0]
            # Independently count every ordered path giving this same graph.
            edge_changes = set(changed_edges(path))
            weight = 0
            for a, b, c, d in it.permutations(path):
                if (b in adj[a] and c in adj[b] and d in adj[c]
                        and c not in adj[a] and d not in adj[b]
                        and set(changed_edges((a, b, c, d))) == edge_changes):
                    weight += 2
            assert weight == (8 if path[3] in adj[path[0]] else 4)
            near = ball(adj, path, 3)
            flip_in_place(adj, path)
            assert ball(adj, path, 3) == near
            defects = sum(not good(adj, v) for v in near)
            assert defects > 0
            flip_in_place(adj, path)
            # Each output graph is counted weight/2 times by oriented paths.
            coefficient += F(2*weight*len(members), defects)
            row_sum_per_vertex += 2*len(members)
            cost_histogram[defects] += len(members)
            class_rows.append(dict(steps=signature, oriented_paths_per_root=len(members),
                                   transition_weight=weight, defective_roots=defects))
        assert row_sum_per_vertex == 300
        rows.append(dict(periods=periods, sites=len(vertices), symmetry_classes=len(classes),
                         oriented_cost_histogram=dict(sorted(cost_histogram.items())),
                         second_order_diagonal_magnitude_per_site=str(coefficient),
                         classes=class_rows))
        print('Verified patch excursions on {}.'.format(periods), flush=True)
    coefficients = [F(row['second_order_diagonal_magnitude_per_site']) for row in rows]
    assert coefficients[1]-coefficients[0] == F(2, 11)
    assert rows[2]['sites'] == rows[3]['sites'] == 4096
    assert coefficients[2]-coefficients[3] == F(4, 33)
    assert rows[4]['sites'] == rows[5]['sites'] == 8000
    assert coefficients[4] == coefficients[5]
    return dict(tori=rows, equal_size_eight_period_difference='4/33',
                equal_size_ten_period_difference='0',
                scope='Exact diagonal entries of finite second-order effective Hamiltonians; off-diagonal mixing and uniform remainders are not computed.')


def squares(adj):
    result = set()
    for a in range(len(adj)):
        for b in adj[a]:
            for c in adj[b]-{a}:
                for d in (adj[c] & adj[a])-{b}:
                    result.add(tuple(sorted([tuple(sorted(e)) for e in [(a, b), (b, c), (c, d), (d, a)]])))
    return sorted(result)


def packing_and_moment_checks():
    n, degree = 8, 4
    pairs, graphs = regular_graphs(n, degree)
    bits = {e: 1 << i for i, e in enumerate(pairs)}
    fixed = []
    for k in [1, 2]:
        mask = 0
        for start in range(0, 4*k, 4):
            for a, b in [(start, start+1), (start+1, start+2), (start+2, start+3), (start+3, start)]:
                mask |= bits[tuple(sorted((a, b))) ]
        fixed.append(mask)
    motif_counts, fixed_counts = [0, 0], [0, 0]
    for graph in graphs:
        adj = [set() for _ in range(n)]
        for i, (a, b) in enumerate(pairs):
            if graph >> i & 1:
                adj[a].add(b)
                adj[b].add(a)
        cycles = squares(adj)
        vertex_sets = [set(x for e in c for x in e) for c in cycles]
        incidence = Counter(v for c in vertex_sets for v in c)
        assert max(incidence.values(), default=0) <= degree*(degree-1)**2//2
        assert sum(incidence.values()) == 4*len(cycles)
        remaining, packed = list(vertex_sets), 0
        while remaining:
            chosen = remaining.pop()
            remaining = [c for c in remaining if c.isdisjoint(chosen)]
            packed += 1
        assert len(cycles) <= 4*(degree*(degree-1)**2//2)*packed
        motif_counts[0] += len(cycles)
        motif_counts[1] += sum(a.isdisjoint(b) for a, b in it.combinations(vertex_sets, 2))
        for i, mask in enumerate(fixed):
            fixed_counts[i] += (graph & mask) == mask
    moments = []
    for i, k in enumerate([1, 2]):
        collections = math.factorial(n)//math.factorial(n-4*k)//(8**k*math.factorial(k))
        assert motif_counts[i] == collections*fixed_counts[i]
        moments.append(dict(disjoint_squares=k, collections_in_complete_graph=collections,
                            fixed_motif_occurrences=fixed_counts[i],
                            exact_expected_collection_count=str(F(motif_counts[i], len(graphs)))))
    # Check the finite simplification of the cited Theorem 3(a), using exact
    # rational arithmetic. This checks its application, not the external theorem.
    bounds = []
    for n in [144, 216, 512, 1000]:
        for k in sorted({1, n//100, n//4}):
            assert 4*k+72 <= 3*n
            denominator = math.prod(2*(3*n-72-j) for j in range(4*k))
            edge_bound = F(30**(4*k), denominator)
            assert edge_bound <= F(10, n)**(4*k)
            collections = math.factorial(n)//math.factorial(n-4*k)//(8**k*math.factorial(k))
            assert collections*edge_bound <= F(1250**k, math.factorial(k))
            bounds.append(dict(sites=n, disjoint_squares=k,
                               simplified_log_bound=k*math.log(1250)-math.lgamma(k+1)))
    return dict(exhaustive_sites=8, exhaustive_degree=4, graphs_checked=len(graphs),
                first_moment_identities=moments, finite_edge_bound_checks=bounds,
                degree_six_incidence_cap=75, greedy_square_intersection_cap=300,
                good_vertex_to_disjoint_square_factor=100,
                asymptotic_local_order_exponent='-(alpha/100)*N*log(N)+O_alpha(N)')


def finite_energy_checks():
    # Full 70-state exchange. The toy patch is the six-site K3,3 graph,
    # explicitly distinct from the radius-three Z^3 template of the theorem.
    pairs, graphs = regular_graphs(6, 3)
    lookup = {mask: i for i, mask in enumerate(graphs)}
    L = np.zeros((70, 70))
    defects = np.zeros(70)
    for i, mask in enumerate(graphs):
        adj, neighbors = flip_neighbors(6, pairs, mask)
        assert connected(adj)
        defects[i] = 6 if triangle_count(adj) else 0
        for other, weight in neighbors.items():
            L[i, i] += weight
            L[i, lookup[other]] -= weight
    assert np.array_equal(L, L.T)
    assert np.all(L@np.ones(70) == 0)
    spectrum = np.linalg.eigvalsh(L)
    assert spectrum[0] > -1e-10 and spectrum[-1] <= 288+1e-10
    omega = np.ones(70)/math.sqrt(70)
    prepared = (defects == 0).astype(float)/math.sqrt(10)
    assert abs(prepared@L@prepared-144) < 1e-10
    assert abs(np.sum(defects*omega**2)/6-F(6, 7)) < 1e-10
    rows = []
    for J in [1, 10, 100, 1000]:
        H = L+J*np.diag(defects)
        energies, vectors = np.linalg.eigh(H)
        ground_defect = float(np.sum(defects*vectors[:, 0]**2)/6)
        assert ground_defect <= 24/J+1e-10
        row = dict(J_over_rho=J, ground_defect_fraction=ground_defect)
        for name, initial in [('prepared', prepared), ('uniform', omega)]:
            energy = float(initial@H@initial)
            coefficients = vectors.T@initial
            measured = []
            for time in np.linspace(0, 1, 101):
                state = vectors@(np.exp(-1j*energies*time)*coefficients)
                d = float(np.sum(defects*np.abs(state)**2)/6)
                assert abs(np.linalg.norm(state)-1) < 1e-10
                assert abs(np.vdot(state, H@state).real-energy) < 1e-7
                if name == 'prepared':
                    assert d <= 24/J+1e-10
                else:
                    assert d >= 6/7-48/J-1e-10
                measured.append(d)
            row[name+'_sampled_defect_range'] = [min(measured), max(measured)]
        rows.append(row)
    return dict(toy_template='Six-site K3,3; not the spatial cubic patch',
                hilbert_dimension=70, dynamics_samples=808, checks=rows,
                scope='Numerical full finite Hamiltonian checks; the all-time, all-size bounds are analytic.')


def main():
    root = Path(__file__).resolve().parents[1]
    report = dict(virtual_exchanges=virtual_exchange_checks())
    report['cycle_packing'] = packing_and_moment_checks()
    print('Cycle packing and exact motif first moments passed.', flush=True)
    report['finite_energy'] = finite_energy_checks()
    report['scope'] = ('Uniform expected patch protection with an imposed 3D template; '
                       'fixed-temperature local-order exclusion on the regular carrier. '
                       'No autonomous cooling, noncollapsed continuum, or TOE.')
    names = ['PATCH_GEOMETRY_PROTECTION.md', 'scripts/patch_geometry_audit.py',
             'UnifiedTheory/Audit/KFCausalPatchGeometry.lean',
             'AUTONOMOUS_GEOMETRY_SELECTION.md', 'scripts/autonomous_geometry_audit.py',
             'UnifiedTheory/Audit/KFCausalAutonomousGeometry.lean',
             'GEOMETRY_ENTROPY_OBSTRUCTION.md', 'scripts/geometry_entropy_audit.py']
    report['source_sha256'] = {name: hashlib.sha256((root/name).read_bytes()).hexdigest() for name in names}
    (root/'data/patch_geometry_audit.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
