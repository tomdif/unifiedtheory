#!/usr/bin/env python3
"""Exact finite checks of Relational Quantum Geometry v2.

Independent Gauss-basis Hamiltonian assembly, a labeled six-site benchmark,
and coherent-feedback checks. These do not establish a geometric phase.
"""
import hashlib
import itertools as it
import json
from collections import defaultdict, deque
from fractions import Fraction as F
from pathlib import Path

import sympy as s


def edge(i, j):
    return tuple(sorted((i, j)))


def structure(n, pairs, links):
    adj = [set() for _ in range(n)]
    matter = [0]*n
    for (i, j), q in zip(pairs, links):
        if q:
            adj[i].add(j)
            adj[j].add(i)
        if q == 2:
            matter[i] ^= 1
            matter[j] ^= 1
    unseen, parts = set(range(n)), []
    while unseen:
        part = {unseen.pop()}
        todo = list(part)
        while todo:
            new = adj[todo.pop()] & unseen
            unseen -= new
            part |= new
            todo.extend(new)
        parts.append(tuple(sorted(part)))
    return adj, tuple(matter), tuple(sorted(parts))


def build(n, cap, p):
    """Assemble H2 directly in the complete capped Z2 Gauss basis.

    One matter assignment is forced by every electric-link assignment.
    K contains the balanced wedge, exchange, and magnetic terms. Each
    elementary transition is balanced before conductances are summed.
    """
    pairs = list(it.combinations(range(n), 2))
    ei = {e: i for i, e in enumerate(pairs)}
    states, info = [], []
    for links in it.product(range(3), repeat=len(pairs)):
        data = structure(n, pairs, links)
        if max(map(len, data[0])) <= cap:
            states.append(links)
            info.append(data)
    lookup = {links: i for i, links in enumerate(states)}
    H, K = defaultdict(F), defaultdict(F)

    def move(col, changed, weight, balanced):
        row = lookup[tuple(changed)]
        H[row, col] -= weight
        if balanced:
            H[col, col] += weight
            K[row, col] -= weight
            K[col, col] += weight

    patterns = [(ei[edge(b, c)], (ei[edge(a, b)], ei[edge(c, d)]),
                 (ei[edge(a, c)], ei[edge(b, d)]))
                for a, b, c, d in it.permutations(range(n), 4)]
    faces = [tuple(ei[edge(a, b)] for a, b in it.combinations(tri, 2))
             for tri in it.combinations(range(n), 3)]
    for col, links in enumerate(states):
        adj, matter, _ = info[col]
        H[col, col] += (p['U']/2*sum((len(a)-p['dbar'])**2 for a in adj)
                       + p['epsilon']*links.count(2) + p['m0']*sum(matter))
        for e, (i, j) in enumerate(pairs):
            common = len(adj[i] & adj[j])
            if (common and links[e] in (0, 1)
                    and (links[e] == 1 or (len(adj[i]) < cap and len(adj[j]) < cap))):
                changed = list(links)
                changed[e] = 1-links[e]
                move(col, changed, p['kappa']*common, True)
            if links[e] and matter[i] != matter[j]:
                changed = list(links)
                changed[e] = 3-links[e]
                move(col, changed, p['t'], False)
        for face in faces:
            if all(links[e] for e in face):
                changed = list(links)
                for e in face:
                    changed[e] = 3-links[e]
                move(col, changed, p['lambda'], True)
        for control, old, new in patterns:
            if not links[control]:
                continue
            forward = all(links[e] == 1 for e in old) and all(links[e] == 0 for e in new)
            reverse = all(links[e] == 1 for e in new) and all(links[e] == 0 for e in old)
            if forward or reverse:
                changed = list(links)
                for e in old+new:
                    changed[e] = 1-links[e]
                move(col, changed, p['rho'], True)
    return pairs, states, info, {k: v for k, v in H.items() if v}, {k: v for k, v in K.items() if v}


PARAMETERS = dict(U=F(7, 5), dbar=F(3, 2), epsilon=F(2, 7),
                  **{'lambda': F(3, 11)}, kappa=F(2, 5), rho=F(1, 13),
                  t=F(4, 5), m0=F(-1, 3))


def finite_hamiltonian_checks():
    rows = []
    for n, cap in [(3, 2), (4, 2), (4, 3)]:
        pairs, states, info, H, K = build(n, cap, PARAMETERS)
        size = len(states)
        assert all(H.get((j, i), 0) == a for (i, j), a in H.items())
        assert all(K.get((j, i), 0) == a for (i, j), a in K.items())
        col_sums, absolute = [F(0)]*size, [F(0)]*size
        for (i, j), a in K.items():
            col_sums[j] += a
            assert i == j or a < 0
        assert not any(col_sums)
        for (i, j), a in H.items():
            absolute[j] += abs(a)
            assert sum(info[i][1]) == sum(info[j][1])
            assert info[i][2] == info[j][2]
        # Exact complex quadratic form, evaluated as two real integer forms.
        x = [((i*17) % 19)-9 for i in range(size)]
        y = [((i*13) % 23)-11 for i in range(size)]
        quadratic = sum(a*(x[i]*x[j]+y[i]*y[j]) for (i, j), a in K.items())
        differences = sum(-a*((x[i]-x[j])**2+(y[i]-y[j])**2)
                          for (i, j), a in K.items() if i < j)
        assert quadratic == differences and quadratic >= 0
        p = PARAMETERS
        bound = n*(p['U']*cap**2/2+(p['epsilon']+abs(p['t']))*cap/2
                   + p['lambda']*cap*(cap-1)/3+p['kappa']*cap*(cap-1)
                   + 4*p['rho']*cap*(cap-1)**2+abs(p['m0']))
        assert max(absolute) <= bound
        # A cyclic relabeling transports the complete Hamiltonian exactly.
        ei = {e: j for j, e in enumerate(pairs)}
        lookup = {links: j for j, links in enumerate(states)}
        permutation = []
        for links in states:
            moved = [0]*len(pairs)
            for (a, b), q in zip(pairs, links):
                moved[ei[edge((a+1) % n, (b+1) % n)]] = q
            permutation.append(lookup[tuple(moved)])
        assert all(H.get((permutation[i], permutation[j]), 0) == a
                   for (i, j), a in H.items())
        rows.append(dict(sites=n, cap=cap, gauss_dimension=size,
                         matrix_nonzero_entries=len(H), max_absolute_column_sum=str(max(absolute)),
                         extensive_bound=str(bound), exact_complex_quadratic_form=str(quadratic),
                         hermitian=True, matter_number_preserved=True,
                         connected_components_preserved=True, relabeling_covariant=True,
                         balanced_row_sums_zero=True))
    return rows


def independent_matrix_and_feedback_checks():
    from relational_quantum_geometry_audit import operators, gauss_signs, equal, clean, gate
    configs, geometry, hopping, occupancy, loop, electric, _ = operators()
    physical = [j for j, c in enumerate(configs) if gauss_signs(c) == (1, 1, 1)]
    matrices = [M.extract(physical, physical) for M in geometry+hopping+occupancy+[loop, electric]]
    R, B, N, T, E = matrices[:3], matrices[3:6], matrices[6:9], matrices[9], matrices[10]
    pairs, states, info, entries, _ = build(3, 2, PARAMETERS)
    assert [configs[j][1] for j in physical] != []
    old_lookup = {configs[j][1]: k for k, j in enumerate(physical)}
    order = [old_lookup[links] for links in states]
    p, size = PARAMETERS, len(physical)
    I = s.eye(size)
    degrees = [sum((N[e] for e, pair in enumerate(pairs) if v in pair), s.zeros(size))
               for v in range(3)]
    expected = sum((s.Rational(p['U'])/2*(D-p['dbar']*I)**2 for D in degrees), s.zeros(size))
    expected += p['epsilon']*E+p['lambda']*(T*T-T)
    expected += sum((p['kappa']*(A*A-A) for A in R), s.zeros(size))
    expected -= sum((p['t']*A for A in B), s.zeros(size))
    expected += s.diag(*[p['m0']*sum(configs[j][0]) for j in physical])
    equal(s.SparseMatrix(size, size, entries), expected.extract(order, order))
    for A in R+[T]:
        L = A*A-A
        equal(L.H, L)
        equal(L*L, 2*L)
        equal(L.H*L, 2*L)
    # Same prepared physical state and matter pulse as v1; geometry gate updated.
    initial = ((1, 1, 0), (2, 0, 1))
    physical_lookup = {configs[j]: k for k, j in enumerate(physical)}
    ket = s.zeros(size, 1)
    ket[physical_lookup[initial]] = 1
    L = R[1]**2-R[1]
    U = clean(I+(-s.I-1)*L/2)  # theta = pi/4
    equal(U.H*U, I)
    results = []
    for label, cosine, sine, want_present, want_arrival in [
            ('0', 1, 0, 0, 0), ('pi/2', 0, 1, s.Rational(3, 4), s.Rational(1, 2)),
            ('pi', -1, 0, 1, 0)]:
        V = gate(B[1], cosine, sine)
        final = clean(U.H*V*U*ket)
        probability = lambda predicate: s.simplify(sum(s.conjugate(final[k])*final[k]
                    for k, j in enumerate(physical) if predicate(configs[j])))
        present = probability(lambda c: c[1][1] != 0)
        arrival = probability(lambda c: c[0][2] == 1)
        assert present == want_present and arrival == want_arrival
        equal(final.H*final, s.ones(1))
        results.append(dict(matter_pulse=label, edge_presence=str(present), arrival=str(arrival)))
    # Multiplicity-two negative control catches balancing an aggregated move.
    X = s.Matrix([[0, 1], [1, 0]])
    correct, wrong = 2*(s.eye(2)-X), (2*X)**2-2*X
    assert correct*s.ones(2, 1) == s.zeros(2, 1)
    assert wrong*s.ones(2, 1) == 2*s.ones(2, 1)
    b, delta = s.Rational(8, 5), s.Integer(1)
    block = s.Matrix([[b, -b], [-b, b+delta]])
    assert block.det() == b*delta and block[0, 0] > 0
    return dict(independent_gauss_matrix_dimension=size, exact_matrix_match=True,
                balanced_move_identity_verified=True, unitary_feedback=results,
                multiplicity_two_correct_eigenvalues=['0', '4'],
                multiplicity_two_wrong_eigenvalues=['2', '6'],
                previous_dense_witness_balanced_block_determinant=str(block.det()))


def six_site_exchange_benchmark():
    n = 6
    pairs = list(it.combinations(range(n), 2))
    ei = {e: i for i, e in enumerate(pairs)}
    bit = lambda a, b: 1 << ei[edge(a, b)]
    patterns = [(bit(b, c), bit(a, b) | bit(c, d), bit(a, c) | bit(b, d))
                for a, b, c, d in it.permutations(range(n), 4)]
    states, triangles = [], []
    for mask in range(1 << len(pairs)):
        links = tuple((mask >> e) & 1 for e in range(len(pairs)))
        adj, _, parts = structure(n, pairs, links)
        if all(len(a) == 3 for a in adj):
            assert len(parts) == 1
            states.append(mask)
            triangles.append(sum(b in adj[a] and c in adj[a] and c in adj[b]
                                 for a, b, c in it.combinations(range(n), 3)))
    assert len(states) == 70 and triangles.count(0) == 10 and triangles.count(2) == 60
    lookup = {mask: j for j, mask in enumerate(states)}
    adjacency = [defaultdict(int) for _ in states]
    for i, mask in enumerate(states):
        for control, old, new in patterns:
            if mask & control and (((mask & old) == old and (mask & new) == 0)
                                   or ((mask & new) == new and (mask & old) == 0)):
                adjacency[i][lookup[mask ^ old ^ new]] += 1
    visited, todo = {0}, deque([0])
    while todo:
        i = todo.popleft()
        for j in adjacency[i]:
            assert adjacency[i][j] == adjacency[j][i]
            if j not in visited:
                visited.add(j)
                todo.append(j)
    assert len(visited) == 70
    for i, row in enumerate(adjacency):
        quotient_row = [sum(v for j, v in row.items() if triangles[j] == t) for t in [0, 2]]
        assert quotient_row == ([0, 144] if triangles[i] == 0 else [24, 48])
    # Positive lifted eigenvector and connectedness identify the Perron root.
    eigenvalue = 24*(1+s.sqrt(7))
    a = s.simplify(144/eigenvalue)
    amplitudes = [a if t == 0 else s.Integer(1) for t in triangles]
    for i, row in enumerate(adjacency):
        assert s.simplify(sum(v*amplitudes[j] for j, v in row.items())
                          - eigenvalue*amplitudes[i]) == 0
    A = s.SparseMatrix(70, 70, {(i, j): v for i, row in enumerate(adjacency) for j, v in row.items()})
    L = s.diag(*[sum(row.values()) for row in adjacency])-A
    assert L*s.ones(70, 1) == s.zeros(70, 1)
    raw_probability = s.simplify(10*a*a/(10*a*a+60))
    assert s.simplify(raw_probability-(1-1/s.sqrt(7))/2) == 0
    return dict(sites=6, degree=3, labeled_configurations=70, move_components=1,
                triangle_free_configurations=10, prism_configurations=60,
                ordered_exchange_row_sums=dict(triangle_free=144, prism=72),
                adjacency_quotient=[[0, 144], [24, 48]],
                raw_ground_energy=str(-eigenvalue), raw_triangle_free_probability=str(raw_probability),
                balanced_ground_energy='0', balanced_triangle_free_probability='1/7',
                balanced_prism_probability='6/7',
                scope='Fixed-degree trivial-flux exchange-only benchmark; labeled basis, not a continuum phase.')


def main():
    root = Path(__file__).resolve().parents[1]
    report = dict(model='Relational Quantum Geometry v2',
                  finite_hamiltonians=finite_hamiltonian_checks(),
                  independent_matrices_and_feedback=independent_matrix_and_feedback_checks(),
                  six_site_exchange=six_site_exchange_benchmark(),
                  scope='Exact finite checks plus supporting Lean lemmas; geometry/GR/chiral continuum remain unproved.')
    sources = ['RELATIONAL_QUANTUM_GEOMETRY_V2.md', 'scripts/balanced_quantum_geometry_audit.py',
               'UnifiedTheory/Audit/KFCausalBalancedGeometry.lean',
               'scripts/relational_quantum_geometry_audit.py', 'QUANTUM_GEOMETRY_PHASE_TEST.md']
    report['source_sha256'] = {name: hashlib.sha256((root/name).read_bytes()).hexdigest() for name in sources}
    target = root/'data/balanced_quantum_geometry_audit.json'
    target.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
