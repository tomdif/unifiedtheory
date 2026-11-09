#!/usr/bin/env python3
"""Seed growth, almost-everywhere cubic geometry, and operational locality.

Graph limits and propagation estimates are analytic; finite evidence below
does not derive a fluctuating quantum spacetime or Einstein dynamics.
"""
import hashlib
import itertools as it
import json
import random
from collections import deque
from fractions import Fraction as F
from pathlib import Path

import numpy as np
from scipy.sparse import csr_matrix

from autonomous_geometry_audit import connected, flip_in_place
from neutral_patch_audit import plateau_graph
from patch_geometry_audit import rectangular_torus, patch_tester


def replay_growth(root):
    initial = json.loads((root/'data/neutral_patch_path.json').read_text())
    witness = json.loads((root/'data/patch_growth_path.json').read_text())
    adj = plateau_graph()
    for path in initial['path']:
        flip_in_place(adj, path)
    good, frozen = patch_tester(), set(witness['frozen_vertices'])
    frozen_edges = {v: frozenset(adj[v] & frozen) for v in frozen}
    assert len(frozen) == 63 and sum(map(len, frozen_edges.values()))//2 == 114
    assert [v for v in range(124) if good(adj, v)] == [31]
    for index, path in enumerate(witness['path']):
        a, b, c, d = path
        assert len(set(path)) == 4 and b in adj[a] and c in adj[b] and d in adj[c]
        assert c not in adj[a] and d not in adj[b]
        changed = [(a, b), (c, d), (a, c), (b, d)]
        assert not any(x in frozen and y in frozen for x, y in changed)
        flip_in_place(adj, path)
        assert connected(adj) and all(len(row) == 6 for row in adj)
        assert all(frozenset(adj[v] & frozen) == frozen_edges[v] for v in frozen)
        roots = [v for v in range(124) if good(adj, v)]
        assert roots == ([31] if index+1 < len(witness['path']) else [31, 50])
    assert len(witness['path']) == 2065 and 50 in adj[31]
    return dict(vertices=124, moves=2065, neutral_moves=2064, final_defect_drop=1,
                initial_good_roots=[31], final_good_roots=[31, 50], adjacent_final_roots=True,
                frozen_ball_vertices=63, frozen_ball_edges=114,
                rooted_patch_tests=124*2066,
                scope='Target-guided finite existence witness retaining the original seed; no general growth-time claim.')


def cubic_ball_size(radius):
    numerator = 4*radius**3+6*radius**2+8*radius+3
    assert numerator % 3 == 0
    return numerator//3


def rewired_torus(cells_per_axis, cell_side):
    k, ell = cells_per_axis, cell_side
    assert k >= 2 and ell >= 16 and ell % 2 == 0
    side, count = k*ell, k**3
    coordinates, adj = rectangular_torus((side, side, side))
    lookup = {v: i for i, v in enumerate(coordinates)}
    cells = list(it.product(range(k), repeat=3))
    used = [0]*count
    removed, cross, routes, endpoints = set(), [], {}, set()
    for child in range(1, count):
        parent = (child-1)//2
        ends = []
        for cell in [child, parent]:
            port = used[cell]
            used[cell] += 1
            base = cells[cell]
            coordinate = tuple(base[j]*ell+[4+2*port, 4, 4][j] for j in range(3))
            other = (coordinate[0]+1, coordinate[1], coordinate[2])
            ends.extend([lookup[coordinate], lookup[other]])
        a, b, c, d = ends
        for x, y in [(a, b), (c, d)]:
            adj[x].remove(y)
            adj[y].remove(x)
            removed.add(tuple(sorted((x, y))))
            endpoints.update([x, y])
        for x, y in [(a, d), (b, c)]:
            assert y not in adj[x]
            adj[x].add(y)
            adj[y].add(x)
            cross.append((x, y))
        routes[child, parent], routes[parent, child] = (a, d), (d, a)
    assert max(used) <= 3 and len(endpoints) == 4*(count-1)
    offsets = [v for v in it.product(range(-3, 4), repeat=3) if sum(map(abs, v)) <= 3]
    affected = set()
    for vertex in endpoints:
        coordinate = coordinates[vertex]
        affected.update(lookup[tuple((coordinate[j]+v[j]) % side for j in range(3))] for v in offsets)
    protected = {i for i, v in enumerate(coordinates)
                 if not (1 <= v[0] % ell <= 12 and 1 <= v[1] % ell <= 7 and 1 <= v[2] % ell <= 7)}
    assert affected.isdisjoint(protected)
    assert len(protected) == count*(ell**3-588)
    return coordinates, lookup, adj, affected, protected, removed, cross, routes


def component_sizes(adj, vertices):
    left, result = set(vertices), []
    while left:
        seed = next(iter(left))
        left.remove(seed)
        todo, size = [seed], 1
        while todo:
            v = todo.pop()
            new = adj[v] & left
            left.difference_update(new)
            size += len(new)
            todo.extend(new)
        result.append(size)
    return sorted(result, reverse=True)


def graph_distances(adj, source, allowed=None):
    distances = [-1]*len(adj)
    distances[source] = 0
    todo = deque([source])
    while todo:
        v = todo.popleft()
        for w in (adj[v] if allowed is None else adj[v] & allowed):
            if distances[w] < 0:
                distances[w] = distances[v]+1
                todo.append(w)
    return distances


def finite_shortcut_checks(k, ell):
    coordinates, lookup, adj, affected, protected, removed, cross, routes = rewired_torus(k, ell)
    side, count, n = k*ell, k**3, len(adj)
    assert connected(adj) and all(len(row) == 6 for row in adj)
    assert all((sum(coordinates[v])-sum(coordinates[w])) % 2 for v in range(n) for w in adj[v])
    good = patch_tester()
    bad = {v for v in sorted(affected) if not good(adj, v)}
    # Untouched balls are certified by the old-torus endpoint-neighborhood
    # inclusion; additionally check representatives outside that inclusion.
    rng = random.Random(k*100+ell)
    for v in rng.sample(sorted(set(range(n))-affected), 8):
        assert good(adj, v)
    for a, b in cross:
        assert a in bad and b in bad
        assert sum(len((adj[x] & adj[b])-{a}) for x in adj[a]-{b}) == 0
    assert len(bad) <= 252*(count-1)
    assert component_sizes(adj, protected) == [len(protected)]
    good_vertices = set(range(n))-bad
    good_components = component_sizes(adj, good_vertices)
    assert good_components[0] >= len(protected)
    antipode = lookup[(side//2, side//2, side//2)]
    hard_antipode_distance = graph_distances(adj, 0, good_vertices)[antipode]
    assert hard_antipode_distance == 3*side//2

    def cell(vertex):
        x, y, z = coordinates[vertex]
        return ((x//ell)*k+y//ell)*k+z//ell

    def local_walk(source, target):
        assert cell(source) == cell(target)
        walk, current = [source], source
        for axis in range(3):
            while coordinates[current][axis] != coordinates[target][axis]:
                v = list(coordinates[current])
                v[axis] += 1 if coordinates[target][axis] > v[axis] else -1
                nxt = lookup[tuple(v)]
                if tuple(sorted((current, nxt))) in removed:
                    p, q = list(coordinates[current]), list(coordinates[nxt])
                    p[1] += 1
                    q[1] += 1
                    walk.extend([lookup[tuple(p)], lookup[tuple(q)]])
                walk.append(nxt)
                current = nxt
        assert len(walk)-1 <= 3*ell+3
        assert all(b in adj[a] for a, b in zip(walk, walk[1:]))
        return walk

    def ancestors(v):
        result = [v]
        while v:
            v = (v-1)//2
            result.append(v)
        return result

    height = count.bit_length()-1
    upper = (2*height+1)*(3*ell+3)+2*height
    for a, b in removed:
        assert len(local_walk(a, b)) == 4
    for _ in range(32):
        start, finish = rng.randrange(n), rng.randrange(n)
        aa, bb = ancestors(cell(start)), ancestors(cell(finish))
        common = next(v for v in aa if v in bb)
        cells = aa[:aa.index(common)+1]+list(reversed(bb[:bb.index(common)]))
        walk, current = [start], start
        for u, v in zip(cells, cells[1:]):
            x, y = routes[u, v]
            walk.extend(local_walk(current, x)[1:])
            walk.append(y)
            current = y
        walk.extend(local_walk(current, finish)[1:])
        assert len(walk)-1 <= upper
        assert all(b in adj[a] for a, b in zip(walk, walk[1:]))

    # Hard probe gate removes every non-lattice edge. A soft gate with
    # epsilon=1/2 has integer 4*A entries, allowing exact walk moments.
    def torus_distance(a, b):
        return sum(min(abs(x-y), side-abs(x-y)) for x, y in zip(coordinates[a], coordinates[b]))
    a, b = routes[count-1, (count-2)//2]
    ga, gb = list(coordinates[a]), list(coordinates[b])
    ga[1] += 4
    gb[1] += 4
    source, target = lookup[tuple(ga)], lookup[tuple(gb)]
    assert source in protected and target in protected
    assert torus_distance(source, target) > 9
    assert graph_distances(adj, source)[target] == 9
    row, col, hard_values, soft_values = [], [], [], []
    for i in range(n):
        for j in adj[i]:
            row.append(i)
            col.append(j)
            hard_values.append(int(i not in bad and j not in bad))
            soft_values.append((1 if i in bad else 2)*(1 if j in bad else 2))
            if hard_values[-1]:
                assert torus_distance(i, j) == 1
    hard = csr_matrix((np.array(hard_values, dtype=np.int64), (row, col)), shape=(n, n))
    soft = csr_matrix((np.array(soft_values, dtype=np.int64), (row, col)), shape=(n, n))
    vh, vs = np.zeros(n, dtype=np.int64), np.zeros(n, dtype=np.int64)
    vh[source] = vs[source] = 1
    moments = []
    for order in range(10):
        assert vh[target] == 0
        assert vs[target] == 0 if order < 9 else vs[target] > 0
        moments.append(int(vs[target]))
        if order < 9:
            vh, vs = hard@vh, soft@vs
            assert max(vs) <= 24**(order+1)
    print('Checked growth geometry K={}, ell={}, N={}.'.format(k, ell, n), flush=True)
    return dict(cells_per_axis=k, cell_side=ell, vertices=n, binary_tree_height=height,
                changed_endpoints=4*(count-1), affected_root_tests=len(affected),
                untouched_root_spot_checks=8, defective_roots=len(bad),
                good_components=good_components, certified_connected_good_subset=len(protected),
                exact_good_fraction=str(F(len(good_vertices), n)),
                exact_hard_probe_antipode_distance=hard_antipode_distance,
                constructed_diameter_upper_bound=upper, sampled_routes=32,
                cross_edges_without_squares=len(cross),
                soft_gate_good_endpoint_pair=[source, target],
                original_torus_distance=torus_distance(source, target), actual_graph_distance=9,
                exact_soft_walk_moments_of_4A=moments, hard_walk_moments_through_order_9=0)


def scaling_checks():
    for radius in range(11):
        assert cubic_ball_size(radius) == sum(1 for v in it.product(range(-radius, radius+1), repeat=3)
                                              if sum(map(abs, v)) <= radius)
    rows = []
    for h in [1, 2, 4, 8, 16, 32]:
        k, ell = 2**h, 2*h*h+16
        count = k**3
        upper = (6*h+1)*(3*ell+3)+6*h
        radius_density = F(4*(count-1)*cubic_ball_size(h), count*ell**3)
        assert radius_density <= F(7, 2*h**3)
        ratio = F(upper, k*ell)
        assert ratio <= F(27*h+4, 2**h)
        rows.append(dict(h=h, growing_test_radius=h, cell_side=ell, cells_per_axis=k,
                         vertices=(k*ell)**3, radius_test_failure_bound=str(radius_density),
                         fixed_radius_three_failure_bound=str(F(252, ell**3)),
                         giant_good_fraction_lower_bound=str(1-F(588, ell**3)),
                         normalized_diameter_upper_bound=str(ratio),
                         required_cubic_volume_constant_lower_bound=str(1/ratio**3)))
    # epsilon in (0,1], tau=epsilon^18/6^10. e^(6*tau)<2; the
    # exponential-series remainder is at most 1/5 of the ninth-order term.
    assert F(1, 1)/(1-F(1, 6**9)) < 2
    assert F(2, 10) < F(1, 2)
    return dict(asymptotic_sequence=rows, cubic_ball_formula='(4R^3+6R^2+8R+3)/3',
                exact_basis_patch_energy='300*rho*N+J*D3',
                hard_probe_propagation_bound='exp(6*kappa*abs(t)*exp(mu)-mu*d_original)',
                soft_probe_time='epsilon^18/(kappa*6^10)',
                soft_probe_amplitude_lower_bound='epsilon^180/(2*9!*6^90)',
                scope='Static graph family and supplied neutral-probe coupling; no full fluctuating-model locality theorem.')


def main():
    root = Path(__file__).resolve().parents[1]
    report = dict(seed_growth=replay_growth(root),
                  rewired_graphs=[finite_shortcut_checks(k, ell) for k, ell in [(2, 16), (2, 20), (3, 16)]],
                  scaling=scaling_checks())
    names = ['PATCH_GROWTH_AND_NONCOLLAPSE.md', 'scripts/patch_growth_audit.py',
             'UnifiedTheory/Audit/KFCausalPatchGrowth.lean', 'data/patch_growth_path.json',
             'NEUTRAL_PATCH_NUCLEATION.md', 'scripts/neutral_patch_audit.py', 'data/neutral_patch_path.json',
             'PATCH_GEOMETRY_PROTECTION.md', 'scripts/patch_geometry_audit.py',
             'RESERVOIR_GEOMETRY_PREPARATION.md', 'scripts/reservoir_geometry_audit.py']
    report['source_sha256'] = {name: hashlib.sha256((root/name).read_bytes()).hexdigest() for name in names}
    report['scope'] = ('Finite seed growth; vanishing local defects and a giant good component do not imply '
                       'noncollapse of the full graph metric. A hard neutral-probe gate restores a scoped '
                       'propagation bound; a fixed soft gate does not.')
    (root/'data/patch_growth_audit.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
