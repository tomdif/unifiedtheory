#!/usr/bin/env python3
"""Exact charged-matter/dynamical-connection prototype for a TOE candidate.

Z2 gauge theory with hard-core charged matter, not chiral fermions or GR.
Every equality and probability in this audit uses exact SymPy arithmetic.
"""
import hashlib
import itertools
import json
from pathlib import Path

import sympy as s


EDGES = list(itertools.combinations(range(3), 2))


def clean(a):
    return s.SparseMatrix(a.applyfunc(s.simplify))


def equal(a, b):
    assert not clean(a-b).todok(), 'Exact matrix equality failed'


def connected(links):
    return sum(link != 0 for link in links) >= 2


def gauss_signs(config):
    matter, links = config
    return tuple((-1)**(matter[v]+sum(links[e] == 2 for e, pair in enumerate(EDGES)
                                     if v in pair)) for v in range(3))


def operators():
    # Link basis: 0=absent, 1=present electric +, 2=present electric -.
    configs = list(itertools.product(itertools.product(range(2), repeat=3),
                                    itertools.product(range(3), repeat=3)))
    index = {config: i for i, config in enumerate(configs)}
    size = len(configs)
    geometry, hopping, occupancies = [], [], []
    for e, (i, j) in enumerate(EDGES):
        re, be, ne = {}, {}, {}
        other_edges = [f for f in range(3) if f != e]
        for col, (matter, links) in enumerate(configs):
            if links[e] != 0:
                ne[col, col] = 1
            # Creation/deletion in the trivial electric representation only.
            # The other two links supply an existing length-two path.
            if all(links[f] != 0 for f in other_edges) and links[e] in (0, 1):
                changed = list(links)
                changed[e] = 1-links[e]
                re[index[matter, tuple(changed)], col] = 1
            if links[e] != 0 and matter[i] != matter[j]:
                changed_links, changed_matter = list(links), list(matter)
                changed_links[e] = 3-links[e]
                changed_matter[i], changed_matter[j] = matter[j], matter[i]
                be[index[tuple(changed_matter), tuple(changed_links)], col] = 1
        geometry.append(s.SparseMatrix(size, size, re))
        hopping.append(s.SparseMatrix(size, size, be))
        occupancies.append(s.SparseMatrix(size, size, ne))
    loop_entries = {}
    electric_entries, degree_entries = {}, {}
    for col, (matter, links) in enumerate(configs):
        electric_entries[col, col] = sum(link == 2 for link in links)
        degrees = [sum(links[e] != 0 for e, pair in enumerate(EDGES) if v in pair)
                   for v in range(3)]
        degree_entries[col, col] = sum(d*(d-1)//2 for d in degrees)
        if all(links):
            loop_entries[index[matter, tuple(3-link for link in links)], col] = 1
    loop = s.SparseMatrix(size, size, loop_entries)
    electric = s.SparseMatrix(size, size, electric_entries)
    degree = s.SparseMatrix(size, size, degree_entries)
    return configs, geometry, hopping, occupancies, loop, electric, degree


def gate(generator, cosine, sine):
    equal(generator.H, generator)
    equal(generator**3, generator)
    result = clean(s.eye(generator.rows)+(cosine-1)*generator**2-s.I*sine*generator)
    equal(result.H*result, s.eye(generator.rows))
    return result


def audit():
    configs, geometry, hopping, occupancy, loop, electric, degree = operators()
    size = len(configs)
    index = {config: i for i, config in enumerate(configs)}
    signs = [gauss_signs(config) for config in configs]
    checked_operators = geometry+hopping+occupancy+[loop, electric, degree]
    for operator in checked_operators:
        equal(operator.H, operator)
        for (row, col), amplitude in operator.todok().items():
            assert amplitude != 0 and signs[row] == signs[col]
    physical = [i for i, signs_i in enumerate(signs) if signs_i == (1, 1, 1)]
    retained = [i for i in physical if connected(configs[i][1])]
    retained_set = set(retained)
    assert size == 216 and len(physical) == 27 and len(retained) == 20
    for operator in checked_operators:
        assert all((row in retained_set) == (col in retained_set)
                   for row, col in operator.todok())

    def reduced(operator):
        return s.SparseMatrix(operator.extract(retained, retained))

    # A specified symmetric Hamiltonian from the proposed six-term family.
    zero = s.zeros(size)
    hamiltonian = (s.Rational(11, 10)*degree-s.Rational(3, 5)*sum(occupancy, zero)
                   + s.Rational(7, 10)*electric-s.Rational(3, 10)*loop
                   - s.Rational(2, 5)*sum(geometry, zero)
                   - s.Rational(4, 5)*sum(hopping, zero))
    hamiltonian = s.SparseMatrix(hamiltonian)
    equal(hamiltonian.H, hamiltonian)
    assert all(sum(configs[row][0]) == sum(configs[col][0])
               for row, col in hamiltonian.todok())
    # Full vertex-relabeling covariance, including links and matter registers.
    entries = hamiltonian.todok()
    for permutation in itertools.permutations(range(3)):
        mapping = []
        for matter, links in configs:
            new_matter, new_links = [0]*3, [0]*3
            for v in range(3):
                new_matter[permutation[v]] = matter[v]
            for e, (i, j) in enumerate(EDGES):
                new_e = EDGES.index(tuple(sorted((permutation[i], permutation[j]))))
                new_links[new_e] = links[e]
            mapping.append(index[tuple(new_matter), tuple(new_links)])
        assert {(mapping[row], mapping[col]): value for (row, col), value in entries.items()} == entries

    # Path 0--1--2, with charges on 0 and 1 and electric flux on 0--1.
    # The connection 0--2 is coherently created, used, and recombined.
    initial_full = index[(1, 1, 0), (2, 0, 1)]
    initial = s.zeros(len(retained), 1)
    initial[retained.index(initial_full)] = 1
    shortcut = EDGES.index((0, 2))
    R, B, N = map(reduced, (geometry[shortcut], hopping[shortcut], occupancy[shortcut]))
    assert clean(R*B-B*R).todok()
    U = gate(R, s.sqrt(2)/2, s.sqrt(2)/2)
    V = gate(B, 0, 1)
    after_creation = clean(U*initial)
    after_transport = clean(V*after_creation)
    final = clean(U.H*after_transport)
    control = clean(U.H*after_creation)

    def expectation(state, observable):
        equal(state.H*state, s.ones(1))
        return s.simplify((state.H*observable*state)[0])

    present_before_transport = expectation(after_creation, N)
    present_final = expectation(final, N)
    present_control = expectation(control, N)
    detector = s.diag(*[configs[i][0][2] for i in retained])
    charge_arrival = expectation(final, detector)
    # A coherent matter return leaves no transported charge, but its phase
    # still changes the connection interferometer from absent to present.
    V_return = gate(B, -1, 0)
    returned = clean(U.H*V_return*after_creation)
    present_after_return = expectation(returned, N)
    charge_after_return = expectation(returned, detector)
    phi = s.Symbol('phi', real=True)
    general_final = clean(U.H*gate(B, s.cos(phi), s.sin(phi))*after_creation)
    predicted = s.zeros(len(retained), 1)
    predicted[retained.index(initial_full)] = (1+s.cos(phi))/2
    predicted[retained.index(index[(1, 1, 0), (2, 1, 1)])] = s.I*(1-s.cos(phi))/2
    predicted[retained.index(index[(0, 1, 1), (2, 2, 1)])] = -s.sin(phi)/s.sqrt(2)
    equal(general_final, predicted)
    assert present_before_transport == s.Rational(1, 2)
    assert present_final == s.Rational(3, 4)
    assert present_control == 0
    assert charge_arrival == s.Rational(1, 2)
    assert present_after_return == 1 and charge_after_return == 0
    # The occupied flux branch cannot be annihilated by the geometry-only move.
    flux_projector = s.diag(*[int(configs[i][1][shortcut] == 2) for i in retained])
    equal(R*flux_projector, s.zeros(len(retained)))
    assert expectation(final, flux_projector) == s.Rational(1, 2)

    # An unrecorded intermediate measurement is still a physical dephasing.
    # This deliberately changes the control protocol; it is not coarse graining.
    rho = clean(after_creation*after_creation.H)
    off = s.eye(len(retained))-N
    dephased = clean(N*rho*N+off*rho*off)
    recombined = clean(U.H*dephased*U)
    measured_control = s.simplify((recombined*N).trace())
    assert measured_control == s.Rational(1, 2)

    return dict(total_dimension=size, gauss_dimension=len(physical),
                connected_gauss_dimension=len(retained),
                exactly_checked_gauge_invariant_generators=len(checked_operators),
                vertex_permutations=6, matter_number_conserved=True,
                symbolic_matter_angle_identity=True,
                hamiltonian_coefficients=dict(degree='11/10', edge='-3/5', electric='7/10',
                                              loop='-3/10', geometry='-2/5', hopping='-4/5'),
                probabilities={key: str(value) for key, value in dict(
                    connection_after_creation=present_before_transport,
                    connection_after_matter_transport_and_recombination=present_final,
                    connection_without_matter_transport=present_control,
                    matter_arrival=charge_arrival,
                    connection_after_coherent_matter_return=present_after_return,
                    matter_arrival_after_coherent_return=charge_after_return,
                    connection_in_measured_control=measured_control).items()},
                charged_flux_blocks_bare_deletion=True,
                scope='Exact Z2 charged hard-core matter and quantum connection prototype; '
                      'no geometric phase, Lorentz symmetry, Einstein gravity, chiral matter, or TOE proof')


def main():
    result = audit()
    root = Path(__file__).resolve().parents[1]
    sources = ['scripts/relational_quantum_geometry_audit.py',
               'RELATIONAL_QUANTUM_GEOMETRY_PROPOSAL.md',
               'EMERGENCE_SUPPORT_AND_GAUGE_COMPACTNESS.md', 'QUANTUM_MEMORY_CLOSURE.md']
    result['source_sha256'] = {p: hashlib.sha256((root/p).read_bytes()).hexdigest() for p in sources}
    output = root/'data/relational_quantum_geometry_audit.json'
    output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result['probabilities'], indent=2))
    print('Wrote', output)


if __name__ == '__main__':
    main()
