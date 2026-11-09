#!/usr/bin/env python3
"""Autonomous focusing, exact regular-graph quotients, and local cubic tests.

Finite tests support, but do not replace, the asymptotic proof and its
external random-regular graph inputs in AUTONOMOUS_GEOMETRY_SELECTION.md.
"""
import hashlib
import itertools as it
import json
import math
from collections import Counter
from fractions import Fraction as F
from pathlib import Path

import numpy as np
import networkx as nx
import sympy as s
from scipy.linalg import eigh

from geometry_entropy_audit import regular_graphs, flip_neighbors
from quantum_geometry_phase_audit import adjacency, edge, square_count, torus


def autonomous_six_site():
    rho, v = s.symbols('rho v', positive=True, real=True)
    L = s.Matrix([[144, -24*s.sqrt(6)], [-24*s.sqrt(6), 24]])
    T = s.diag(0, 2)
    omega = s.Matrix([1, s.sqrt(6)])/s.sqrt(7)
    target = s.Matrix([1, 0])
    H = rho*L+v*T
    initial_energy = s.simplify((omega.T*H*omega)[0])
    target_energy = (target.T*H*target)[0]
    assert initial_energy == 12*v/7 and target_energy == 144*rho
    assert s.solve(initial_energy-target_energy, v) == [84*rho]
    Hstar = H.subs(v, 84*rho)
    R = s.simplify((168*rho*s.eye(2)-Hstar)/(24*s.sqrt(7)*rho))
    assert s.simplify(R*R) == s.eye(2)
    assert s.simplify(R*omega-target) == s.zeros(2, 1)
    theta = s.symbols('theta', real=True)
    state = s.cos(theta)*omega+s.I*s.sin(theta)*target
    prob = s.trigsimp(s.expand_complex(s.conjugate(state[0])*state[0]))
    assert s.simplify(prob-(1+6*s.sin(theta)**2)/7) == 0
    assert s.simplify(state.subs(theta, s.pi/2)-s.I*target) == s.zeros(2, 1)
    assert s.simplify(state.subs(theta, s.pi)+omega) == s.zeros(2, 1)
    ground_prob = (1+(v-60*rho)/s.sqrt((v-60*rho)**2+3456*rho**2))/2
    assert s.simplify(ground_prob.subs(v, 84*rho)-(1+1/s.sqrt(7))/2) == 0
    return dict(resonant_triangle_coefficient='84*rho',
                exact_target_probability='(1+6*sin(24*sqrt(7)*rho*t)^2)/7',
                first_perfect_time='pi/(48*sqrt(7)*rho)',
                target_probability_at_first_perfect_time='1',
                target_probability_at_twice_that_time='1/7',
                initial_energy=str(initial_energy), target_energy=str(target_energy),
                stationary_ground_target_probability_at_resonance='(1+1/sqrt(7))/2',
                stationary_ground_target_probability_formula=str(ground_prob),
                scope='Known pure input and supplied constant occupancy coupling; focusing recurs, without capture.')


def connected(adj):
    seen, todo = {0}, [0]
    while todo:
        a = todo.pop()
        for b in adj[a]-seen:
            seen.add(b)
            todo.append(b)
    return len(seen) == len(adj)


def triangle_count(adj):
    return sum(len(adj[a] & adj[b]) for a in range(len(adj)) for b in adj[a])//6


def exact_quotient(n, degree, expected_classes):
    pairs, all_graphs = regular_graphs(n, degree)
    graphs, transitions, invariants = [], [], []
    for mask in all_graphs:
        adj, weights = flip_neighbors(n, pairs, mask)
        if connected(adj):
            graphs.append(mask)
            transitions.append(weights)
            invariants.append((triangle_count(adj), square_count(adj)))
    lookup = {mask: i for i, mask in enumerate(graphs)}
    values = sorted(set(invariants))
    labels = [values.index(a) for a in invariants]
    # Refine until actual weighted row sums are constant in each cell.
    # Triangle count alone is not assumed to define an invariant subspace.
    for _ in range(len(graphs)):
        signatures = []
        for i, weights in enumerate(transitions):
            counts = Counter()
            for mask, weight in weights.items():
                counts[labels[lookup[mask]]] += weight
            signatures.append((labels[i], tuple(sorted(counts.items()))))
        keys = sorted(set(signatures))
        new = [keys.index(a) for a in signatures]
        if new == labels:
            break
        labels = new
    else:
        raise AssertionError('partition refinement did not terminate')
    sizes = Counter(labels)
    k = len(sizes)
    assert k == expected_classes
    reps = [labels.index(j) for j in range(k)]
    B = [[0]*k for _ in range(k)]
    for j, i in enumerate(reps):
        for mask, weight in transitions[i].items():
            B[j][labels[lookup[mask]]] += weight
    # Verify every row, every reverse weight, and configuration connectivity.
    for i, weights in enumerate(transitions):
        row = [0]*k
        for mask, weight in weights.items():
            j = lookup[mask]
            assert transitions[j][graphs[i]] == weight
            row[labels[j]] += weight
        assert row == B[labels[i]]
    visited, todo = {0}, [0]
    while todo:
        i = todo.pop()
        for mask in transitions[i]:
            j = lookup[mask]
            if j not in visited:
                visited.add(j)
                todo.append(j)
    assert len(visited) == len(graphs)
    assert all(sizes[i]*B[i][j] == sizes[j]*B[j][i] for i in range(k) for j in range(k))
    Q = s.Matrix(k, k, lambda i, j:
                 (sum(B[i]) if i == j else 0)-B[i][j]*s.sqrt(s.Rational(sizes[i], sizes[j])))
    assert Q == Q.T
    omega = s.Matrix([s.sqrt(s.Rational(sizes[i], len(graphs))) for i in range(k)])
    assert s.simplify(Q*omega) == s.zeros(k, 1)
    triangles = [invariants[i][0] for i in reps]
    triangle_free = [i for i, t in enumerate(triangles) if t == 0]
    identified_classes = {}
    if (n, degree) == (8, 3):
        templates = [(triangle_free[0], 'Mobius ladder', nx.circulant_graph(8, [1, 4])),
                     (triangle_free[1], 'cube', nx.hypercube_graph(3))]
    elif (n, degree) == (8, 4):
        templates = [(triangle_free[0], 'K4,4', nx.complete_bipartite_graph(4, 4))]
    elif (n, degree) == (6, 3):
        templates = [(0, 'K3,3', nx.complete_bipartite_graph(3, 3)),
                     (1, 'triangular prism', nx.circular_ladder_graph(3))]
    else:
        templates = []
    for label, name, template in templates:
        representative = nx.Graph()
        representative.add_nodes_from(range(n))
        representative.add_edges_from(e for bit, e in enumerate(pairs) if graphs[reps[label]] >> bit & 1)
        assert nx.is_isomorphic(representative, template)
        automorphisms = sum(1 for _ in nx.algorithms.isomorphism.GraphMatcher(template, template).isomorphisms_iter())
        # Refinement uses isomorphism invariants, so an orbit lies in a cell.
        # Matching its orbit size certifies that it fills the whole cell.
        assert sizes[label]*automorphisms == math.factorial(n)
        identified_classes[label] = dict(name=name, automorphisms=automorphisms)
    # The uniform triangle-free trial has only its escape boundary energy.
    tf_count = sum(sizes[i] for i in triangle_free)
    escape_sum = 0
    max_escape_ratio = F(0)
    for i, weights in enumerate(transitions):
        if invariants[i][0] != 0:
            continue
        escape = sum(w for mask, w in weights.items() if invariants[lookup[mask]][0] != 0)
        c4 = invariants[i][1]
        assert escape <= 32*(degree-1)*c4
        if c4:
            max_escape_ratio = max(max_escape_ratio, F(escape, c4))
        escape_sum += escape
    tf_vector = s.Matrix([s.sqrt(s.Rational(sizes[i], tf_count)) if i in triangle_free else 0
                          for i in range(k)])
    trial_energy = s.simplify((tf_vector.T*Q*tf_vector)[0])
    assert trial_energy == s.Rational(escape_sum, tf_count)
    Qn = np.array(Q, dtype=float)
    ground_rows = []
    for v in [0, 84, 168, 1000, 1000000]:
        H = Qn+v*np.diag(triangles)
        energies, vectors = eigh(H)
        ground = vectors[:, 0]
        if ground.sum() < 0:
            ground = -ground
        assert np.all(ground > 0)
        residual = float(np.linalg.norm(H@ground-energies[0]*ground))
        assert residual < 1e-8*max(1, float(np.linalg.norm(H)))
        # Positive lifting and connected negative off-diagonals certify that
        # this quotient eigenvector is the full configuration ground state.
        ground_rows.append(dict(v_over_rho=v, energy_over_rho=float(energies[0]),
                                class_probabilities=(ground**2).tolist(), residual=residual))
    strong = Q.extract(triangle_free, triangle_free)
    strong_result = dict(matrix=[[str(a) for a in row] for row in strong.tolist()])
    if (n, degree) == (8, 3):
        expected = s.Matrix([[128, -32*s.sqrt(3)], [-32*s.sqrt(3), 192]])
        assert strong == expected
        psi = s.Matrix([s.sqrt(3)/2, s.Rational(1, 2)])
        assert strong*psi == 96*psi
        assert set(str(x) for x in strong.eigenvals()) == {'96', '224'}
        assert [invariants[reps[i]][1] for i in triangle_free] == [4, 6]
        strong_result.update(energy_over_rho='96', class_probabilities=['3/4', '1/4'],
                             cube_probability='1/4')
    elif len(triangle_free) == 1:
        strong_result.update(energy_over_rho=str(strong[0, 0]), class_probabilities=['1'])
    return dict(sites=n, degree=degree, all_regular_graphs=len(all_graphs),
                connected_regular_graphs=len(graphs), verified_equitable_classes=k,
                directed_distinct_transitions=sum(len(w) for w in transitions),
                classes=[dict(size=sizes[j], triangles=invariants[i][0], squares=invariants[i][1])
                         for j, i in enumerate(reps)],
                identified_classes=identified_classes,
                exact_weighted_adjacency_rows=B,
                normalized_laplacian=[[str(a) for a in row] for row in Q.tolist()],
                ground_states=ground_rows, strong_triangle_limit=strong_result,
                triangle_free_trial_energy_over_rho=str(trial_energy),
                maximum_escape_per_square=str(max_escape_ratio),
                triangle_escape_bound_coefficient=32*(degree-1))


def paths(adj, starts=None):
    for a in (range(len(adj)) if starts is None else starts):
        for b in sorted(adj[a]):
            for c in sorted(adj[b]-{a}):
                if c in adj[a]:
                    continue
                for d in sorted(adj[c]-{a, b}):
                    if d not in adj[b]:
                        yield a, b, c, d


def changed_edges(path):
    a, b, c, d = path
    return [edge(a, b), edge(c, d), edge(a, c), edge(b, d)]


def flip_in_place(adj, path):
    for a, b in changed_edges(path):
        if b in adj[a]:
            adj[a].remove(b)
            adj[b].remove(a)
        else:
            adj[a].add(b)
            adj[b].add(a)


def touching_squares(adj, links):
    found = set()
    for a, b in links:
        if b not in adj[a]:
            continue
        for c in adj[b]-{a}:
            for d in (adj[c] & adj[a])-{b}:
                found.add(tuple(sorted([edge(a, b), edge(b, c), edge(c, d), edge(d, a)])))
    return found


def square_change(adj, path):
    links = changed_edges(path)
    before = len(touching_squares(adj, links))
    flip_in_place(adj, path)
    after = len(touching_squares(adj, links))
    flip_in_place(adj, path)
    return after-before


def ball(adj, roots, radius):
    seen, frontier = set(roots), set(roots)
    for _ in range(radius):
        new = set().union(*(adj[v] for v in frontier))-seen
        seen |= new
        frontier = new
    return seen


def cubic_local_checks():
    rows = []
    for length in [6, 8, 10, 12]:
        vertices, links = torus(length)
        n = len(vertices)
        adj = adjacency(n, links)
        assert square_count(adj) == 3*n
        candidates = list(paths(adj, [0]))
        assert len(candidates) == 150
        hist, witnesses = Counter(), {}
        for path in candidates:
            delta = square_change(adj, path)
            a, b, c, d = path
            assert delta == (-6 if d in adj[a] else -8)
            hist[delta] += 1
            witnesses.setdefault(delta, path)
        assert hist == {-8: 126, -6: 24}
        checks = []
        # Fully enumerate repair candidates at N=216. The proof uses a
        # size-independent bound, not an extrapolation of these counts.
        if length == 6:
            for deficit, path in sorted(witnesses.items()):
                damaged = [a.copy() for a in adj]
                flip_in_place(damaged, path)
                assert square_count(damaged) == 3*n+deficit
                near = ball(damaged, path, 3)
                assert len(near) <= 4*(1+6+6*5+6*5**2)
                repairs, total, remote = 0, 0, 0
                for p in paths(damaged):
                    delta = square_change(damaged, p)
                    total += 2
                    if not (set(p) & near):
                        remote += 2
                        assert delta in [-8, -6]
                    if delta == -deficit:
                        assert set(p) & near
                        repairs += 2
                assert 0 < repairs <= 897600
                checks.append(dict(initial_square_deficit=-deficit,
                                   weighted_valid_moves=total,
                                   weighted_square_restoring_moves=repairs,
                                   weighted_remote_moves=remote, radius_three_sites=len(near)))
        rows.append(dict(side_length=length, sites=n, squares=3*n,
                         oriented_paths_per_root=len(candidates),
                         square_change_histogram=dict(sorted(hist.items())),
                         weighted_row_sum=300*n, repair_checks=checks))
    return dict(families=rows, analytic_repair_weight_bound=897600,
                analytic_ground_weight_bound='D*r/((D-E0/rho)^2+D*r), D=300*N, r=897600',
                asymptotic_scope='O(1/N) exact cubic-orbit ground weight; external short-cycle inputs required.')


def patch_criterion_checks():
    # Independent local template in Z^3, with the root explicitly marked.
    coords = [v for v in it.product(range(-3, 4), repeat=3) if sum(abs(x) for x in v) <= 3]
    reference = nx.Graph()
    reference.add_nodes_from((v, {'root': v == (0, 0, 0)}) for v in coords)
    for v in coords:
        for axis in range(3):
            w = list(v)
            w[axis] += 1
            if tuple(w) in reference:
                reference.add_edge(v, tuple(w))
    assert len(reference) == 63

    def certificate(adj, start=0):
        sites = ball(adj, [start], 3)
        if len(sites) != len(reference):
            return False
        patch = nx.Graph()
        patch.add_nodes_from((v, {'root': v == start}) for v in sites)
        patch.add_edges_from((a, b) for a in sites for b in adj[a] & sites)
        return nx.is_isomorphic(reference, patch,
                                node_match=lambda x, y: x['root'] == y['root'])

    rows = []
    for periods in [(8, 8, 8), (8, 8, 128)]:
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
        assert certificate(adj)
        # Translations act transitively; one root represents every root here.
        radii = [3, 8, 16, 32] if periods[-1] == 128 else [3]
        volumes = {r: len(ball(adj, [0], r)) for r in radii}
        if periods[-1] == 128:
            assert all(volumes[r] == 128*r-448 for r in radii if r >= 8)
        rows.append(dict(periods=periods, sites=len(vertices), rooted_patch_matches=True,
                         all_roots_by_translation_symmetry=True, ball_volumes=volumes))
        if periods == (8, 8, 8):
            damaged = [a.copy() for a in adj]
            path = next(paths(damaged, [0]))
            flip_in_place(damaged, path)
            assert not certificate(damaged, path[0])
            rows.append(dict(sites=len(vertices), one_exchange_from_cubic=True,
                             rooted_patch_matches_at_changed_endpoint=False))
    # A deterministic degree-six triangle-free nonlattice competitor.
    n = 512
    links = {edge(i, (i+k) % n) for i in range(n) for k in [1, 3, 5]}
    adj = adjacency(n, links)
    assert triangle_count(adj) == 0 and not certificate(adj)
    rows.append(dict(sites=n, family='circulant(512;1,3,5)', triangles=0,
                     rooted_patch_matches=False, radius_three_ball=len(ball(adj, [0], 3))))
    return dict(reference_ball_sites=63, checks=rows,
                scope='Supplied radius-three template; the thin-torus example demonstrates missing noncollapse.')


def main():
    root = Path(__file__).resolve().parents[1]
    report = dict(autonomous_six_site=autonomous_six_site())
    print('Exact autonomous six-site transfer passed.', flush=True)
    report['regular_quotients'] = []
    for n, d, k in [(6, 3, 2), (8, 3, 5), (8, 4, 6)]:
        report['regular_quotients'].append(exact_quotient(n, d, k))
        print('Verified complete regular quotient: N={}, degree={}.'.format(n, d), flush=True)
    report['cubic_local_checks'] = cubic_local_checks()
    report['patch_criterion_checks'] = patch_criterion_checks()
    report['scope'] = ('Autonomous finite focusing and a scoped zero-temperature cubic exclusion; '
                       'no stable preparation, general geometric phase, Einstein dynamics, or TOE.')
    names = ['AUTONOMOUS_GEOMETRY_SELECTION.md', 'scripts/autonomous_geometry_audit.py',
             'UnifiedTheory/Audit/KFCausalAutonomousGeometry.lean',
             'COARSE_GEOMETRY_AND_PREPARATION.md', 'scripts/coarse_geometry_audit.py',
             'GEOMETRY_ENTROPY_OBSTRUCTION.md', 'scripts/geometry_entropy_audit.py',
             'scripts/quantum_geometry_phase_audit.py']
    report['source_sha256'] = {name: hashlib.sha256((root/name).read_bytes()).hexdigest() for name in names}
    (root/'data/autonomous_geometry_audit.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
