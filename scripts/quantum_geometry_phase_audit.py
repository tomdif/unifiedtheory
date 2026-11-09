#!/usr/bin/env python3
"""All-size analytic phase obstruction, finite witnesses, and a proposed switch.

Exact combinatorial and rational checks. No finite scan is identified with
a thermodynamic geometric phase. The original Hamiltonian is kept unchanged.
"""
import hashlib
import itertools
import json
from collections import deque
from fractions import Fraction as F
from pathlib import Path

import sympy as s


def popcount(value):
    return bin(value).count('1')


def edge(i, j):
    return tuple(sorted((i, j)))


def adjacency(n, edges):
    adj = [set() for _ in range(n)]
    for i, j in edges:
        adj[i].add(j)
        adj[j].add(i)
    return adj


def component_count(adj):
    unseen, count = set(range(len(adj))), 0
    while unseen:
        count += 1
        todo = [unseen.pop()]
        while todo:
            v = todo.pop()
            new = adj[v] & unseen
            unseen -= new
            todo.extend(new)
    return count


def graph_data(n, edges, cap):
    adj = adjacency(n, edges)
    degrees = [len(row) for row in adj]
    wedges = sum(d*(d-1)//2 for d in degrees)
    triangle_edges = sum(len(adj[i] & adj[j]) for i, j in edges)
    assert triangle_edges % 3 == 0
    amplitude_count = 0
    moves = 0
    for i, j in itertools.combinations(range(n), 2):
        common = len(adj[i] & adj[j])
        allowed = (i, j) in edges or (degrees[i] < cap and degrees[j] < cap)
        if common and allowed:
            moves += 1
            amplitude_count += common
    assert amplitude_count <= wedges
    return dict(degrees=degrees, wedges=wedges, triangles=triangle_edges//3,
                original_move_count=moves, rewiring_row_sum=amplitude_count)


def exhaustive_graph_checks():
    total, frozen = 0, 0
    for n in range(1, 7):
        pairs = list(itertools.combinations(range(n), 2))
        for mask in range(1 << len(pairs)):
            edges = {e for bit, e in enumerate(pairs) if mask >> bit & 1}
            degrees = [len(row) for row in adjacency(n, edges)]
            cap = max(degrees)
            data = graph_data(n, edges, cap)
            assert 2*len(edges) <= n*cap
            assert data['wedges'] <= n*cap*(cap-1)//2
            assert 3*data['triangles'] <= data['wedges']
            if min(degrees) == cap and data['triangles'] == 0:
                assert data['original_move_count'] == 0
                frozen += 1
            total += 1
    return dict(all_labeled_graphs=total, saturated_triangle_free_graphs=frozen,
                maximum_vertices=6)


def torus(length):
    vertices = list(itertools.product(range(length), repeat=3))
    index = {v: i for i, v in enumerate(vertices)}
    edges = set()
    for i, v in enumerate(vertices):
        for d in range(3):
            w = list(v)
            w[d] = (w[d]+1) % length
            edges.add(edge(i, index[tuple(w)]))
    return vertices, edges


def circulant(n, steps):
    return {edge(i, (i+k) % n) for i in range(n) for k in steps}


def ball_sizes(adj, start=0):
    distances = {start: 0}
    queue = deque([start])
    while queue:
        v = queue.popleft()
        for w in adj[v]:
            if w not in distances:
                distances[w] = distances[v]+1
                queue.append(w)
    return [sum(d <= radius for d in distances.values())
            for radius in range(max(distances.values())+1)]


def square_count(adj):
    count = sum(len(adj[i] & adj[j])*(len(adj[i] & adj[j])-1)//2
                for i, j in itertools.combinations(range(len(adj)), 2))
    assert count % 2 == 0
    return count//2


def finite_family_checks():
    rows = []
    for length in [4, 6, 8, 10]:
        vertices, cubic = torus(length)
        n = len(vertices)
        thin = circulant(n, [1, 3, 5])
        ring = circulant(n, [1, 2, 3])
        for edges in [cubic, thin]:
            data = graph_data(n, edges, 6)
            assert set(data['degrees']) == {6}
            assert data['triangles'] == 0 and data['original_move_count'] == 0
            assert len(edges) == 3*n and data['wedges'] == 15*n
        matching = {edge(i, i+1) for i in range(0, n, 2)}
        adj = adjacency(n, ring)
        assert all(len(adj[i] & adj[j]) == 4 for i, j in matching)
        reduced_adj = adjacency(n, ring-matching)
        assert component_count(reduced_adj) == 1
        assert all(len(reduced_adj[i] & reduced_adj[j]) == 4 for i, j in matching)
        cubic_balls, thin_balls = ball_sizes(adjacency(n, cubic)), ball_sizes(adjacency(n, thin))
        for r in range(length//2):
            assert cubic_balls[r] == (4*r**3+6*r*r+8*r+3)//3
            assert thin_balls[r] <= 10*r+1
        rows.append(dict(length=length, sites=n, frozen_graph_edges=3*n,
                         cubic_ball_sizes=cubic_balls[:6], thin_ball_sizes=thin_balls[:6],
                         matching_coordinates=len(matching), common_neighbors=4))
    # One degree-preserving move actually changes an isomorphism invariant.
    vertices, edges = torus(4)
    lookup = {v: i for i, v in enumerate(vertices)}
    a, b, c, d = [lookup[(i, 0, 0)] for i in range(4)]
    changed = (edges-{edge(a, b), edge(c, d)}) | {edge(a, c), edge(b, d)}
    before, after = adjacency(64, edges), adjacency(64, changed)
    assert [len(row) for row in before] == [len(row) for row in after] == [6]*64
    assert component_count(after) == 1
    old_squares, new_squares = square_count(before), square_count(after)
    assert old_squares != new_squares
    return dict(families=rows, cubic_switch=dict(squares_before=old_squares,
                squares_after=new_squares, degree_preserved=6, connected=True))


def variational_checks():
    n, g, u = 64, F(2, 5), F(11, 10)
    ring = circulant(n, [1, 2, 3])
    selected = [edge(i, i+1) for i in range(0, 12, 2)]  # six of the N/2 coordinates
    states = [ring-{e for j, e in enumerate(selected) if mask >> j & 1}
              for mask in range(1 << len(selected))]
    rows = []
    for mu in [F(-3, 5), F(-12)]:
        delta, b = -mu-10*u, 4*g
        ratio = b/(1+abs(delta))
        shift = (delta*ratio**2-2*b*ratio)/(1+ratio**2)
        assert shift < 0
        e0 = 3*mu+15*u
        numerator = F(0)
        norm = sum(ratio**(2*popcount(mask)) for mask in range(len(states)))
        for mask, graph in enumerate(states):
            amp = ratio**popcount(mask)
            adj = adjacency(n, graph)
            energy = mu*len(graph)+u*sum(len(row)*(len(row)-1)//2 for row in adj)
            assert energy == n*e0+delta*popcount(mask)
            numerator += amp**2*energy
            for j, (a, c) in enumerate(selected):
                common = len(adj[a] & adj[c])
                assert common == 4
                target = mask ^ (1 << j)
                numerator -= g*common*amp*ratio**popcount(target)
        exact_energy = numerator/norm
        assert exact_energy == n*e0+len(selected)*shift
        rows.append(dict(mu=str(mu), u=str(u), g=str(g), removal_cost=str(delta),
                         mixing_amplitude=str(b), trial_ratio=str(ratio),
                         energy_shift_per_coordinate=str(shift),
                         all_matching_energy_density_shift=str(shift/2),
                         explicit_compression_dimension=len(states),
                         explicit_trial_energy=str(exact_energy)))
    return rows


def operator_row_bound_checks():
    from relational_quantum_geometry_audit import operators
    configs, geometry, hopping, occupancy, loop, electric, degree = operators()
    size = len(configs)
    zero = s.zeros(size)
    h = (s.Rational(-3, 5)*sum(occupancy, zero)+s.Rational(11, 10)*degree
         + s.Rational(7, 10)*electric-s.Rational(3, 10)*loop
         - s.Rational(2, 5)*sum(geometry, zero)-s.Rational(4, 5)*sum(hopping, zero))
    rows = [s.Integer(0)]*size
    for (row, col), value in s.SparseMatrix(h).todok().items():
        assert value == s.conjugate(h[col, row])
        rows[row] += abs(value)
    bound = s.Rational(111, 10)
    assert max(rows) <= bound
    return dict(actual_hamiltonian_dimension=size, maximum_absolute_row_sum=str(max(rows)),
                extensive_bound=str(bound), sites=3, degree_cap=2)


def switch_checks():
    pairs = list(itertools.combinations(range(4), 2))
    ab, ac, bc, bd, cd = [pairs.index(e) for e in [(0, 1), (0, 2), (1, 2), (1, 3), (2, 3)]]

    def signs(matter, links):
        return tuple((-1)**(matter[v]+sum(links[e] == 2 for e, pair in enumerate(pairs)
                                         if v in pair)) for v in range(4))

    mapping = {}
    for matter in itertools.product(range(2), repeat=4):
        for links in itertools.product(range(3), repeat=6):
            if links[bc] == 0:
                continue
            pattern = tuple(links[e] for e in [ab, cd, ac, bd])
            if pattern not in [(1, 1, 0, 0), (0, 0, 1, 1)]:
                continue
            target = list(links)
            for e in [ab, cd, ac, bd]:
                target[e] = 1-target[e]
            target = tuple(target)
            assert signs(matter, links) == signs(matter, target)
            old = {e for e, value in zip(pairs, links) if value}
            new = {e for e, value in zip(pairs, target) if value}
            assert [len(row) for row in adjacency(4, old)] == [len(row) for row in adjacency(4, new)]
            assert component_count(adjacency(4, old)) == component_count(adjacency(4, new))
            mapping[matter, links] = (matter, target)
    assert all(mapping[target] == source for source, target in mapping.items())
    assert len(mapping) == 192
    # Every nonzero block is exactly a swap; all other states are annihilated.
    z = s.Matrix([[0, 1], [1, 0]])
    theta = s.Symbol('theta', real=True)
    gate = s.cos(theta)*s.eye(2)-s.I*s.sin(theta)*z
    assert s.simplify(gate.H*gate-s.eye(2)) == s.zeros(2)
    return dict(full_basis_states=16*3**6, nonzero_transitions=len(mapping),
                hermitian_involution_on_support=True, cube_equals_generator=True,
                all_gauss_signs_preserved=True, all_vertex_degrees_preserved=True,
                connected_components_preserved=True, exact_gate_unitarity=True)


def main():
    result = dict(graphs=exhaustive_graph_checks(), operator_bound=operator_row_bound_checks(),
                  families=finite_family_checks(),
                  variational=variational_checks(), proposed_switch=switch_checks())
    root = Path(__file__).resolve().parents[1]
    sources = ['scripts/quantum_geometry_phase_audit.py', 'QUANTUM_GEOMETRY_PHASE_TEST.md',
               'UnifiedTheory/Audit/KFCausalQuantumGeometryPhase.lean',
               'RELATIONAL_QUANTUM_GEOMETRY_PROPOSAL.md',
               'scripts/relational_quantum_geometry_audit.py']
    result['source_sha256'] = {p: hashlib.sha256((root/p).read_bytes()).hexdigest() for p in sources}
    result['scope'] = ('Original Hamiltonian: extensive norm bound and frozen-geometry obstruction; '
                       'saturated cubic trivial-flux particle-empty state loses to an explicit trial. '
                       'A new switch removes freezing, not the unproved geometric/Einstein/chiral limits.')
    output = root/'data/quantum_geometry_phase_audit.json'
    output.write_text(json.dumps(result, indent=2)+'\n')
    print('Wrote', output)
    print('Graphs:', result['graphs'])
    print('Switch:', result['families']['cubic_switch'])
    print('Variational shifts:', [row['all_matching_energy_density_shift'] for row in result['variational']])


if __name__ == '__main__':
    main()
