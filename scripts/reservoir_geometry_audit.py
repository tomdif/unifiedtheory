#!/usr/bin/env python3
"""Exact repair channels and a unitary reservoir dilation for the 70-state toy.

The semi-infinite-chain limit and finite-retention bound are analytic.
No scalable preparation of the spatial patch Hamiltonian is claimed.
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
from scipy.integrate import quad
from scipy.linalg import eigh_tridiagonal
from scipy.special import j1

from autonomous_geometry_audit import (connected, paths, square_change, triangle_count)
from geometry_entropy_audit import regular_graphs, flip_neighbors
from quantum_geometry_phase_audit import square_count


def edge(a, b):
    return tuple(sorted((a, b)))


def repair_channels():
    pairs, graphs = regular_graphs(6, 3)
    lookup = {g: i for i, g in enumerate(graphs)}
    bits = {e: 1 << i for i, e in enumerate(pairs)}
    triangles = [triangle_count(flip_neighbors(6, pairs, g)[0]) for g in graphs]
    good = [i for i, t in enumerate(triangles) if t == 0]
    bad = [i for i, t in enumerate(triangles) if t == 2]
    ai, bi = {v: i for i, v in enumerate(good)}, {v: i for i, v in enumerate(bad)}
    assert (len(good), len(bad)) == (10, 60)
    copies = Counter()
    for a, b, c, d in it.permutations(range(6), 4):
        control = bits[edge(b, c)]
        old = bits[edge(a, b)] | bits[edge(c, d)]
        new = bits[edge(a, c)] | bits[edge(b, d)]
        entries = []
        for j in bad:
            graph = graphs[j]
            if graph & control and (((graph & old) == old and (graph & new) == 0)
                                    or ((graph & new) == new and (graph & old) == 0)):
                i = lookup[graph ^ old ^ new]
                if i in ai:
                    entries.append((ai[i], bi[j]))
        assert len(entries) == 4
        copies[tuple(sorted(entries))] += 1
    assert len(copies) == 45 and set(copies.values()) == {8}
    keys = sorted(copies)
    operators = [s.SparseMatrix(10, 60, {p: 1 for p in key}) for key in keys]
    outgoing = sum((m.T*m for m in operators), s.zeros(60))
    incoming = sum((m*m.T for m in operators), s.zeros(10))
    assert outgoing == 3*s.eye(60) and incoming == 18*s.eye(10)
    channel_gram = s.Matrix(45, 45, lambda i, j: len(set(keys[i]) & set(keys[j])))
    assert channel_gram == 4*s.eye(45)
    C = sum(operators, s.zeros(10, 60))
    assert C*C.T == 14*s.eye(10)+4*s.ones(10)
    assert C.rank() == 10
    dark = C.nullspace()[0]
    assert C*dark == s.zeros(10, 1)
    assert sum((m*dark).dot(m*dark) for m in operators) == 3*dark.dot(dark)
    # The induced channel permutation is checked for generators of S6.
    channel_set = set(keys)
    for k in range(5):
        perm = list(range(6))
        perm[k], perm[k+1] = perm[k+1], perm[k]
        relabeled = []
        for graph in graphs:
            image = 0
            for bit, (a, b) in enumerate(pairs):
                if graph >> bit & 1:
                    image |= bits[edge(perm[a], perm[b])]
            relabeled.append(lookup[image])
        transformed = {tuple(sorted((ai[relabeled[good[a]]], bi[relabeled[bad[b]]])
                                    for a, b in key)) for key in keys}
        assert transformed == channel_set
    # Exact eventual output states and a finite-time channel isometry.
    rho_b = s.ones(60)/60
    emitted = sum((m*rho_b*m.T for m in operators), s.zeros(10))/3
    final_pure_uniform = s.ones(10)/70+6*emitted/7
    assert emitted == s.eye(10)/15+s.ones(10)/30
    assert final_pure_uniform.eigenvals() == {s.Rational(17, 35): 1, s.Rational(2, 35): 9}
    assert s.trace(final_pure_uniform**2) == s.Rational(13, 49)
    final_mixed = s.eye(10)/70+incoming/210
    assert final_mixed == s.eye(10)/10
    c = s.Rational(3, 5)
    # Rows: vacuum graph states (10+60), followed by 45 emitted channels x 10.
    V = s.SparseMatrix(520, 70, {})
    for i in range(70):
        V[i, i] = 1 if i < 10 else c
    for mu, key in enumerate(keys):
        for a, b in key:
            V[70+10*mu+a, 10+b] = 4/(5*s.sqrt(3))
    assert V.T*V == s.eye(70)
    report = dict(graph_states=70, target_rank=10, unwanted_rank=60,
                  original_ordered_moves=360, distinct_channels=45,
                  duplicate_multiplicity=8, rank_per_channel=4,
                  outgoing_gram='3*I_60', incoming_gram='18*I_10',
                  hilbert_schmidt_channel_gram='4*I_45',
                  collective_channel_rank=10, collective_dark_dimension=50,
                  relabeling_generators_checked=5, finite_channel_isometry_verified=True,
                  mixed_input_final_graph='I_10/10', mixed_input_bath_vacuum_probability='1/7',
                  mixed_input_probability_per_emission_channel='2/105',
                  mixed_input_effective_bath_rank=46,
                  pure_uniform_final_graph_eigenvalues={'17/35': 1, '2/35': 9},
                  pure_uniform_final_graph_purity='13/49',
                  channels=[dict(entries=key, original_copies=copies[key]) for key in keys])
    return keys, report


def exact_dilation(keys):
    length, gap = 2, 4
    ambient = 70+450*length
    bright = 10+60*(length+1)
    h, w, k = {}, {}, {}
    for i in range(70):
        w[i, i] = 1
    for i in range(10, ambient):
        h[i, i] = gap
    for i in range(10, bright):
        k[i, i] = gap
    for position in range(1, length+1):
        for mu, entries in enumerate(keys):
            for a, b in entries:
                row = 70+450*(position-1)+10*mu+a
                w[row, 10+60*position+b] = 1/s.sqrt(3)
                if position == 1:
                    h[row, 10+b] = h[10+b, row] = -1/s.sqrt(3)
        if position > 1:
            for a in range(450):
                row = 70+450*(position-1)+a
                h[row, row-450] = h[row-450, row] = -1
        for b in range(60):
            row = 10+60*position+b
            k[row, row-60] = k[row-60, row] = -1
    H, W, K = s.SparseMatrix(ambient, ambient, h), s.SparseMatrix(ambient, bright, w), s.SparseMatrix(bright, bright, k)
    assert H == H.T and K == K.T
    assert W.T*W == s.eye(bright)
    assert H*W == W*K
    assert all((i < 10) == (j < 10) for i, j in h)
    return dict(reservoir_sites_per_channel=length, invariant_excitation_sector_dimension=ambient,
                represented_bright_dimension=bright, exact_intertwining=True,
                hermiticity=True, bare_energy_conservation=True, gap=gap, hopping=1)


def transport_checks():
    rows = []
    for length in [1, 2, 16, 64, 128]:
        energies, vectors = eigh_tridiagonal(np.zeros(length+1), -np.ones(length))
        weights = vectors[0]**2
        times = np.unique(np.r_[np.linspace(0, 20, 161), math.pi, 11])
        max_error, max_window_failure = 0.0, 0.0
        for t in times:
            amplitude = np.sum(weights*np.exp(-1j*energies*t))
            reference = 1.0 if t == 0 else j1(2*t)/t
            assert abs(amplitude) <= 1+1e-12
            max_error = max(max_error, abs(amplitude-reference))
            if 11 <= t <= 20:
                max_window_failure = max(max_window_failure, abs(amplitude)**2)
            if length == 1 and t == math.pi:
                assert abs(amplitude+1) < 1e-12  # exact finite return, up to gap phase
        rows.append(dict(chain_length=length, sampled_times=len(times),
                         max_return_amplitude_error_on_0_to_20=float(max_error),
                         max_sampled_unwanted_probability_on_11_to_20=float(max_window_failure)))
    # Independently check the spectral integral giving the Bessel amplitude.
    for t in [0, 0.1, 1, 3, 10, 20]:
        integral = 2/math.pi*quad(lambda q: math.sin(q)**2*math.cos(2*t*math.cos(q)),
                                  0, math.pi, epsabs=1e-12)[0]
        expected = 1 if t == 0 else j1(2*t)/t
        assert abs(integral-expected) < 1e-11
    # Finite and infinite return moments first differ at order 2R+2.
    moment_checks = []
    for length in range(1, 9):
        state = [1]+[0]*length
        for order in range(2*length+3):
            if order % 2 == 0:
                m = order//2
                catalan = math.comb(2*m, m)//(m+1)
                assert state[0] == catalan-(1 if order == 2*length+2 else 0)
            else:
                assert state[0] == 0
            state = [(state[j-1] if j else 0)+(state[j+1] if j < length else 0)
                     for j in range(length+1)]
        moment_checks.append(dict(chain_length=length, first_differing_return_moment=2*length+2))
    # e^40 < 3^40 makes this retention certificate entirely rational.
    tail = F(2*3**40*40**258, math.factorial(258))
    assert tail < F(1, 1000)
    failure_bound = (F(1, 11)+F(1, 1000))**2
    assert failure_bound < F(1, 100)
    return dict(finite_chains=rows, moment_checks=moment_checks,
                infinite_return_amplitude='J_1(2*kappa*t)/(kappa*t)',
                exact_unwanted_probability='p_B(0)*abs(J_1(2*kappa*t)/(kappa*t))^2',
                rigorous_envelope='p_B(t) <= p_B(0)/(kappa*t)^2',
                retention_certificate=dict(channels=45, sites_per_channel=128,
                    physical_chain_sites=5760, scaled_time_interval=[11, 20],
                    amplitude_truncation_error_less_than='1/1000',
                    exact_failure_upper_bound=str(failure_bound), target_probability_greater_than='99/100'),
                scope='Infinite-reservoir asymptotic preparation; finite reservoirs have a certified finite retention interval and recur.')


def patch_plateau():
    # Incidence graph of PG(2,5), then a connected double cover. The cover
    # exceeds the 63-site patch size, so the obstruction is not a size artefact.
    q = 5
    projective = set()
    for v in it.product(range(q), repeat=3):
        if v == (0, 0, 0):
            continue
        first = next(x for x in v if x)
        inverse = pow(first, -1, q)
        projective.add(tuple(x*inverse % q for x in v))
    points = sorted(projective)
    assert len(points) == 31
    base_edges = [(i, 31+j) for i, p in enumerate(points) for j, line in enumerate(points)
                  if sum(a*b for a, b in zip(p, line)) % q == 0]
    adj = [set() for _ in range(124)]
    for index, (a, b) in enumerate(base_edges):
        for sheet in range(2):
            x, y = 2*a+sheet, 2*b+(sheet ^ int(index == 0))
            adj[x].add(y)
            adj[y].add(x)
    assert connected(adj) and all(len(a) == 6 for a in adj)
    assert all((a < 62) != (b < 62) for a in range(124) for b in adj[a])
    assert triangle_count(adj) == 0 and square_count(adj) == 0
    outputs = set()
    total = 0
    for path in paths(adj):
        assert square_change(adj, path) == 0
        a, b, c, d = path
        outputs.add(tuple(sorted([edge(a, b), edge(c, d), edge(a, c), edge(b, d)])))
        total += 1
    assert total == 124*6*25 and len(outputs) == total//2
    return dict(vertices=124, degree=6, connected=True, bipartite=True,
                initial_squares=0, oriented_moves_checked=total,
                distinct_output_graphs=len(outputs), weighted_row_sum=2*total,
                initial_patch_defects=124, defects_after_every_one_step_move=124,
                strictly_downhill_patch_moves=0,
                scope='Strict descent cannot start here; zero-energy motion or other interactions are not excluded.')


def main():
    root = Path(__file__).resolve().parents[1]
    keys, channel_report = repair_channels()
    print('All 45 repair channels and information identities passed.', flush=True)
    report = dict(repair_channels=channel_report, exact_unitary_dilation=exact_dilation(keys))
    print('Exact full-to-chain intertwining passed.', flush=True)
    report['transport'] = transport_checks()
    report['patch_plateau'] = patch_plateau()
    report['scope'] = ('Autonomous universal preparation of the six-site graph class with an explicit reservoir; '
                       'the target is supplied and not a spatial continuum. Scalable patch repair remains open.')
    names = ['RESERVOIR_GEOMETRY_PREPARATION.md', 'scripts/reservoir_geometry_audit.py',
             'UnifiedTheory/Audit/KFCausalReservoirGeometry.lean',
             'PATCH_GEOMETRY_PROTECTION.md', 'scripts/patch_geometry_audit.py',
             'AUTONOMOUS_GEOMETRY_SELECTION.md', 'scripts/autonomous_geometry_audit.py',
             'GEOMETRY_ENTROPY_OBSTRUCTION.md', 'scripts/geometry_entropy_audit.py']
    report['source_sha256'] = {name: hashlib.sha256((root/name).read_bytes()).hexdigest() for name in names}
    (root/'data/reservoir_geometry_audit.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
