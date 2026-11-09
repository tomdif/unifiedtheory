#!/usr/bin/env python3
"""Projected cubic rigidity and a supplied local fluctuating-geometry sector.

Exact finite checks and numerical diagnostics accompany the analytic
metric/propagation proofs. A reference spatial regulator remains an input.
"""
import hashlib
import itertools as it
import json
from collections import Counter
from pathlib import Path

import numpy as np
import sympy as sy
from scipy import sparse as sp
from scipy.linalg import expm, norm
from scipy.sparse.linalg import expm_multiply

from autonomous_geometry_audit import (ball, changed_edges, connected,
                                     flip_in_place, paths, triangle_count)
from patch_geometry_audit import rectangular_torus, patch_tester
from patch_growth_audit import graph_distances
from energetic_probe_audit import adjacency_matrix


def root_squares(adj, root):
    return sum(len((adj[a] & adj[b])-{root}) for a, b in it.combinations(adj[root], 2))


def rooted_obstruction():
    coords = [v for v in it.product(range(-3, 4), repeat=3) if sum(map(abs, v)) <= 3]
    lookup = {v: i for i, v in enumerate(coords)}
    adj = [set() for _ in coords]
    for i, v in enumerate(coords):
        for axis in range(3):
            for sign in [-1, 1]:
                w = list(v)
                w[axis] += sign
                if tuple(w) in lookup:
                    adj[i].add(lookup[tuple(w)])
    root = lookup[(0, 0, 0)]
    assert len(coords) == 63 and root_squares(adj, root) == 12
    histogram, positions, examples = Counter(), Counter(), {}
    candidates = [p for p in paths(adj) if root in p]
    assert len(candidates) == 600
    for path in candidates:
        flip_in_place(adj, path)
        value = root_squares(adj, root)
        assert value in [7, 8, 9]
        histogram[value] += 1
        positions[path.index(root)] += 1
        examples.setdefault(value, [coords[v] for v in path])
        flip_in_place(adj, path)
    assert histogram == Counter({7: 192, 8: 312, 9: 96})
    assert positions == Counter({i: 150 for i in range(4)})
    # Independently compare against complete rooted isomorphism on a torus.
    _, full = rectangular_torus((10, 10, 10))
    good = patch_tester()
    actual = Counter()
    candidates = [p for p in paths(full, sorted(ball(full, [0], 3))) if 0 in p]
    assert len(candidates) == 600
    for path in candidates:
        flip_in_place(full, path)
        actual[root_squares(full, 0)] += 1
        assert not good(full, 0)
        flip_in_place(full, path)
    assert actual == histogram
    return dict(template_vertices=63, exhaustive_forward_rooted_paths=600,
                squares_before=12, squares_after=dict(sorted(histogram.items())),
                root_positions=dict(positions), representative_paths=examples,
                independent_torus_vertices=len(full), independent_isomorphism_checks=600,
                scope='Radius-three data determines every post-flip square at an affected root; all completions covered.')


def local_switch_family():
    side = 24
    coords, reference = rectangular_torus((side, side, side))
    lookup = {v: i for i, v in enumerate(coords)}
    switches = [tuple(lookup[(base+x, base, base)] for x in range(4)) for base in [4, 16]]
    affected = [ball(reference, p, 3) for p in switches]
    assert affected[0].isdisjoint(affected[1])
    good = patch_tester()
    assert good(reference, 0)
    graphs, rows = [], []
    source = switches[0][0]
    source_coord = coords[source]
    d0 = np.array([sum(min((x-y) % side, (y-x) % side) for x, y in zip(v, source_coord))
                   for v in coords])
    antipode = lookup[tuple((x+side//2) % side for x in source_coord)]
    for mask in range(4):
        adj = [set(a) for a in reference]
        active = bin(mask).count('1')
        for bit, p in enumerate(switches):
            if mask & (1 << bit):
                flip_in_place(adj, p)
        assert all(len(a) == 6 for a in adj) and connected(adj)
        assert triangle_count(adj) == 0
        squares = sum(root_squares(adj, v) for v in range(len(adj)))//4
        assert squares == 3*len(adj)-8*active
        defects = sum(not good(adj, v) for v in sorted(set().union(*affected)))
        assert defects == 62*active
        for bit, p in enumerate(switches):
            a, b, c, d = p
            if mask & (1 << bit):
                # Every removed old edge has a two-step replacement.
                assert c in adj[a] and b in adj[c] and d in adj[b]
            else:
                assert b in adj[a] and c in adj[b] and d in adj[c]
            # Ordered all-move Hamiltonian assigns weight four to this toggle.
            target = set(changed_edges(p))
            weight = 0
            for q in it.permutations(p):
                u, v, w, z = q
                if (v in adj[u] and w in adj[v] and z in adj[w]
                        and w not in adj[u] and z not in adj[v]
                        and set(changed_edges(q)) == target):
                    weight += 2
            assert weight == 4
        for a, neighbors in enumerate(adj):
            for b in neighbors:
                dist = sum(min((x-y) % side, (y-x) % side) for x, y in zip(coords[a], coords[b]))
                assert dist <= 2
        dg = np.array(graph_distances(adj, source))
        assert np.all(d0 <= 2*dg) and np.all(dg <= 2*d0)
        balls = []
        for radius in [1, 2, 4, 8]:
            lower, actual, upper = int(sum(d0 <= radius//2)), int(sum(dg <= radius)), int(sum(d0 <= 2*radius))
            assert lower <= actual <= upper
            balls.append(dict(radius=radius, reference_lower=lower, actual=actual, reference_upper=upper))
        rows.append(dict(mask=mask, active_switches=active, triangles=0, squares=squares,
                         defects=defects, antipode_distance=int(dg[antipode]), ball_checks=balls))
        graphs.append(adj)
    report = dict(vertices=len(reference), reference_side=side, selected_switches=2,
                  full_extensive_construction_switches_at_this_size=8,
                  configurations=4, switched_paths=[list(p) for p in switches], rows=rows,
                  all_compressed_move_weights=4, all_move_diagonal_per_vertex=300,
                  scope='Two selected switches out of eight possible separated cells; analytic construction allows all cells.')
    return report, graphs, switches, d0


def joint_dynamics(graphs, switches, d0):
    n = len(graphs[0])
    rho, J, kappa = .1, .005, .25
    G = np.zeros((4, 4))
    for mask in range(4):
        G[mask, mask] = 8*rho+62*J*bin(mask).count('1')
        for bit in range(2):
            G[mask, mask ^ (1 << bit)] = -4*rho
    T = -kappa*sp.block_diag([adjacency_matrix(adj) for adj in graphs], format='csr')
    Kgeom = sp.kron(sp.csr_matrix(G), sp.eye(n), format='csr')
    H = Kgeom+T
    assert (H-H.T).nnz == 0
    start = np.zeros(4*n, dtype=complex)
    start[switches[0][0]] = 1
    initial_energy = float(np.vdot(start, H@start).real)
    # The old occupied-root projector deletes this exact entry; the new sector keeps it.
    geometry_entry = H[n+switches[0][0], switches[0][0]]
    assert geometry_entry == -4*rho
    rows = []
    for t in [.3, 1.]:
        evolved = expm_multiply(-1j*t*H, start)
        psi = evolved.reshape((4, n))
        geometry_probabilities = np.sum(abs(psi)**2, axis=1)
        reduced = psi@psi.conj().T
        purity = float(np.trace(reduced@reduced).real)
        amplitudes = np.sqrt(np.sum(abs(psi)**2, axis=0))
        mu = .35
        bound = np.exp(6*kappa*t*np.exp(2*mu)-mu*d0)
        assert np.all(amplitudes <= bound+1e-12)
        assert abs(np.vdot(evolved, evolved)-1) < 1e-10
        energy = float(np.vdot(evolved, H@evolved).real)
        assert abs(energy-initial_energy) < 1e-10
        assert geometry_probabilities[1:].sum() > 0 and purity < 1-1e-10
        rows.append(dict(time=t, geometry_probabilities=geometry_probabilities.tolist(),
                         geometry_reduced_purity=purity, energy=energy,
                         maximum_transport_to_bound_ratio_beyond_distance_eight=float(np.max(amplitudes[d0 >= 8]/bound[d0 >= 8]))))
    return dict(joint_dimension=4*n, rho=rho, J=J, kappa=kappa,
                retained_root_touching_geometry_entry=float(geometry_entry),
                old_occupied_root_projected_entry=0, rows=rows,
                scope='Four full 13,824-site graph configurations and one neutral probe; arbitrary-state bound is analytic.')


def extensive_geometry_and_interactions():
    coords, adj = rectangular_torus((24, 24, 24))
    lookup = {v: i for i, v in enumerate(coords)}
    switches = [tuple(lookup[(cx+4+x, cy+4, cz+4)] for x in range(4))
                for cx, cy, cz in it.product([0, 12], repeat=3)]
    affected = [ball(adj, p, 3) for p in switches]
    assert all(not a & b for a, b in it.combinations(affected, 2))
    # Support/norm accounting for the complete many-body interaction list,
    # with rho=J=kappa=1 for the exact integer coefficient check.
    loads = [6]*len(adj)+[66]*len(switches)
    for bit, p in enumerate(switches):
        a, b, c, d = p
        leaf = len(adj)+bit
        for u, v in [(a, b), (c, d), (a, c), (b, d)]:
            loads[u] += 1
            loads[v] += 1
            loads[leaf] += 1
            du = sum(abs(x-y) for x, y in zip(coords[a], coords[u]))+1
            dv = sum(abs(x-y) for x, y in zip(coords[a], coords[v]))+1
            assert du <= 4 and dv <= 4
    assert max(loads[:len(adj)]) == 8 and max(loads[len(adj):]) == 70
    assert max(loads) <= 74
    for p in switches:
        flip_in_place(adj, p)
    assert connected(adj) and all(len(a) == 6 for a in adj)
    assert triangle_count(adj) == 0
    good = patch_tester()
    defects = sum(not good(adj, v) for v in sorted(set().union(*affected)))
    squares = sum(root_squares(adj, v) for v in range(len(adj)))//4
    assert defects == 62*len(switches) and squares == 3*len(adj)-8*len(switches)
    d0 = np.array([sum(min(x, 24-x) for x in v) for v in coords])
    dg = np.array(graph_distances(adj, 0))
    assert np.all(d0 <= 2*dg) and np.all(dg <= 2*d0)
    return dict(vertices=len(adj), switches=len(switches), full_carrier_configurations=256,
                all_switches_active_defects=defects, all_switches_active_squares=squares,
                recognized_affected_roots=len(set().union(*affected)),
                matter_site_interaction_coefficient=8, geometry_site_interaction_coefficient=70,
                common_envelope_at_unit_couplings=74, maximum_interaction_diameter=4,
                scope='Full eight-cell interaction list and all-active configuration; not all 256 states enumerated.')


def local_many_body_and_ground_state():
    # Four matter qubits and one switch qubit; complete local path motif.
    dim = 32
    rho, J, kappa = sy.Rational(1, 10), sy.Rational(1, 100), sy.Rational(1, 4)
    X = sy.zeros(dim)
    ngeom = sy.diag(*[(s >> 4) & 1 for s in range(dim)])
    Nm = sy.diag(*[bin(s & 15).count('1') for s in range(dim)])
    for state in range(dim):
        X[state ^ 16, state] = 1

    def hop(a, b):
        out = sy.zeros(dim)
        for state in range(dim):
            if ((state >> a) & 1) != ((state >> b) & 1):
                out[state ^ (1 << a) ^ (1 << b), state] = 1
        return out

    hab, hbc, hcd, hac, hbd = [hop(*edge) for edge in [(0, 1), (1, 2), (2, 3), (0, 2), (1, 3)]]
    H = -4*rho*X+62*J*ngeom-kappa*(hab+hbc+hcd)+kappa*ngeom*(hab+hcd-hac-hbd)
    assert H == H.T and H*Nm == Nm*H
    assert H*ngeom != ngeom*H
    # Every occupation sector sees the selected connectivity, not just one particle.
    for state in range(dim):
        selected = [(0, 2), (1, 2), (1, 3)] if state & 16 else [(0, 1), (1, 2), (2, 3)]
        expected = {state ^ (1 << a) ^ (1 << b): -kappa for a, b in selected
                    if ((state >> a) & 1) != ((state >> b) & 1)}
        for target in range(dim):
            if target != state and (target >> 4) == (state >> 4):
                assert H[target, state] == expected.get(target, 0)
    Hdense = np.array(H, dtype=float)
    A = np.array(ngeom, dtype=float)
    B = np.diag([(s >> 3) & 1 for s in range(dim)])
    observations = []
    envelope = float(8*kappa+4*rho+62*J)
    for t in [.0001, .02, .5]:
        U = expm(-1j*t*Hdense)
        At = U.conj().T@A@U
        c = norm(At@B-B@At, 2)
        mu = 1.
        lr_bound = 2*np.exp(min(0., 6*envelope*np.exp(4*mu)*t-mu*4))
        assert c <= lr_bound+1e-12
        observations.append(dict(time=t, mixed_geometry_matter_commutator_norm=c,
                                 general_lr_bound=lr_bound))
    # Exact independent-switch ground spectrum when matter is absent.
    b, d = sy.symbols('b d', positive=True)
    one = sy.Matrix([[b, -b], [-b, b+d]])
    gap = sy.sqrt(d*d+4*b*b)
    low = b+d/2-gap/2
    assert sy.simplify((one-low*sy.eye(2)).det()) == 0
    p = (1-d/gap)/2
    assert sy.simplify(sy.diff(low, d)-p) == 0
    return dict(local_hilbert_dimension=dim, exact_matter_number_conservation=True,
                all_occupation_columns_checked=dim, mixed_commutators=observations,
                graph_only_switch_gap='sqrt((62*J)^2+64*rho^2)',
                graph_only_ground_active_probability='(1-62*J/sqrt((62*J)^2+64*rho^2))/2',
                scope='Full local neutral hard-core field motif; global common cone follows from uniform interaction support.')


def main():
    root = Path(__file__).resolve().parents[1]
    obstruction = rooted_obstruction()
    print('Rooted obstruction verified.', flush=True)
    family, graphs, switches, d0 = local_switch_family()
    print('Metric and all four graph configurations verified.', flush=True)
    report = dict(rooted_obstruction=obstruction, regulated_family=family,
                  joint_dynamics=joint_dynamics(graphs, switches, d0),
                  extensive_geometry=extensive_geometry_and_interactions(),
                  local_many_body=local_many_body_and_ground_state())
    names = ['PROJECTED_GEOMETRY_AND_LOCAL_DYNAMICS.md', 'scripts/projected_geometry_audit.py',
             'UnifiedTheory/Audit/KFCausalProjectedGeometry.lean',
             'ENERGETIC_PROBE_SECTOR.md', 'scripts/energetic_probe_audit.py',
             'PATCH_GROWTH_AND_NONCOLLAPSE.md', 'scripts/patch_growth_audit.py',
             'PATCH_GEOMETRY_PROTECTION.md', 'scripts/patch_geometry_audit.py',
             'AUTONOMOUS_GEOMETRY_SELECTION.md', 'scripts/autonomous_geometry_audit.py']
    report['source_sha256'] = {name: hashlib.sha256((root/name).read_bytes()).hexdigest() for name in names}
    report['scope'] = ('Exact cubic-root flip obstruction and frozen all-good graph sector. A supplied '
                       'bounded-distortion reference carrier permits extensive quantum geometry, uniform '
                       'noncollapse, and joint neutral-matter/geometry locality. No emergent regulator, '
                       'physical charged matter, Lorentz symmetry, Einstein dynamics, or completed TOE.')
    (root/'data/projected_geometry_audit.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
