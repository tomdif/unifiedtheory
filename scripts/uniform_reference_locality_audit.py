#!/usr/bin/env python3
"""Checks for the reference-locality proof, not an all-volume certificate.

The reference changes below keep the endpoint field fixed. In particular,
the pure-gradient reference check is different from a physical gauge change.
"""
import hashlib
import itertools
import json
from pathlib import Path

import numpy as np
import sympy as sym

from radial_measure_audit import SPECIES, curvature, density
from local_cohomology_audit import (CubicalTorus, pack, unpack, gradient,
                                    field_strength, jacobian_resolvent)
from second_cohomology_audit import DoubleComplex, density_hessian
from reference_phase_descent_audit import example


def weighted_primitive(model, base, a, field_nodes=4, resolvent_nodes=32):
    """Actual phase-weighted descent with a possibly nonconstant flat base."""
    c = DoubleComplex(model.lengths)
    smap = c.phi_map()
    n, edges = model.n, 4*model.n
    first = np.zeros((n, edges))
    second = np.zeros((6*n, edges))
    avg = np.zeros(n)
    nodes, weights = np.polynomial.legendre.leggauss(field_nodes)
    for t, weight in zip((nodes+1)/2, weights/2):
        for _, q, multiplicity in SPECIES:
            jac, sp = jacobian_resolvent(model, base+t*a, q, resolvent_nodes)
            hess = density_hessian(model, base+t*a, q, resolvent_nodes)
            first += multiplicity*weight*(1-t)*jac
            second += multiplicity*weight*(1-t)**2/2*(smap@hess.reshape(n*edges, edges))
            avg += multiplicity*weight*density(model, sp['p'], q)
    current, audit = c.finish(a, first, second, avg)
    return dict(current=current, phase=-float(a.ravel()@current), avg=avg, audit=audit)


def flat_triangle(model, base, a, shift, count=8):
    nodes, weights = np.polynomial.legendre.leggauss(count)
    value = 0.
    minimum_gap = np.inf
    for s, ws in zip((nodes+1)/2, weights/2):
        tangent = a-s*shift
        for t, wt in zip((nodes+1)/2, weights/2):
            links = np.exp(1j*(base+s*shift+t*tangent))
            for _, q, multiplicity in SPECIES:
                sp = model.operator(links, q)
                pa = model.projector_derivative(links, q, sp, tangent)
                pr = model.projector_derivative(links, q, sp, shift)
                value += multiplicity*ws*wt*(1-t)*curvature(sp['p'], pa, pr)
                minimum_gap = min(minimum_gap, sp['gap'])
    return float(value), float(minimum_gap)


def reference_checks():
    model, refs, fields = example()
    base = np.broadcast_to((refs[0]/model.lengths)[:, None], fields[0].shape)
    a = fields[0]
    c = CubicalTorus(model.lengths)
    r = np.broadcast_to(((refs[1]-refs[0])/model.lengths)[:, None], a.shape)
    sites = np.array(model.geom.sites)
    lengths = np.array(model.lengths)
    centered = (sites+lengths//2) % lengths-lengths//2
    sawtooth = np.sum(centered*r[:, 0], axis=1)
    seam = r-gradient(model, sawtooth)
    # Moderate nonconstant reference change; all its paths are gauge-related.
    omega = np.random.default_rng(2026091011).uniform(-.03, .03, model.n)
    pure = gradient(model, omega)
    original = weighted_primitive(model, base, a)
    print('Original phase evaluated', flush=True)
    shifted = {}
    for name, shift in [('gradient', pure), ('uniform', r), ('seam', seam)]:
        flatness = float(np.linalg.norm(field_strength(c, shift)))
        endpoint = float(np.linalg.norm(base+shift+a-shift-(base+a)))
        assert flatness < 1e-14 and endpoint < 1e-14
        target = weighted_primitive(model, base+shift, a-shift)
        flux, gap = flat_triangle(model, base, a, shift)
        k = flux+target['phase']-original['phase']
        shifted[name] = dict(phase=target['phase'], flux=flux, comparison=k,
                             minimum_kernel_gap=gap, flatness_error=flatness,
                             endpoint_error=endpoint, ward_error=target['audit']['ward_error'])
        if name == 'gradient':
            moment = float(omega@original['avg'])
            shifted[name].update(
                weighted_primitive_change=float(np.linalg.norm(target['current']-original['current'])),
                phase_ward_error=abs(target['phase']-original['phase']-moment),
                flux_ward_error=abs(flux+moment))
            assert abs(k) < 1e-10
            assert shifted[name]['weighted_primitive_change'] < 1e-10
            assert max(shifted[name]['phase_ward_error'], shifted[name]['flux_ward_error']) < 1e-10
        print(name, 'reference comparison', k, flush=True)
    relocation_error = abs(shifted['uniform']['comparison']-shifted['seam']['comparison'])
    assert relocation_error < 1e-10
    assert abs(shifted['uniform']['comparison']) > 1e-9
    # This independent run must reproduce the earlier uniform comparison.
    root = Path(__file__).resolve().parents[1]
    previous = json.loads((root/'data/reference_phase_descent_audit.json').read_text())
    prior = previous['corrected']['canonical_adjustments'][1]
    prior_error = abs(shifted['uniform']['comparison']-prior)
    assert prior_error < 1e-10
    return dict(original_phase=original['phase'], reference_changes=shifted,
                uniform_to_seam_error=relocation_error, previous_comparison_error=prior_error,
                maximum_seam_amplitude=float(abs(seam).max()),
                scope='Independent finite operator checks; no numerical all-volume inference')


def marked_homotopy_checks(length):
    """Every input basis, two centers, and every marked site on this torus."""
    torus = CubicalTorus((length,)*4)
    sites = np.array(list(itertools.product(range(length), repeat=4)))
    n = len(sites)
    delta = abs(sites[:, None, :]-sites[None, :, :])
    distances = np.minimum(delta, length-delta).max(axis=2)
    basis_count = 0
    triples = 0
    for center_index in [0, np.ravel_multi_index((length//2,)*4, (length,)*4)]:
        center = tuple(sites[center_index])
        radii = distances[center_index]
        for degree in range(4):
            count = len(torus.cells[degree])*n
            for column in range(count):
                vector = np.zeros(count, dtype=np.int64)
                vector[column] = 1
                output = pack(torus.homotopy(unpack(torus, vector, degree), center))
                nz = np.flatnonzero(output) % n
                u = radii[column % n]
                assert np.all(radii[nz] <= u)
                # u + d(output,mark) <= 3 max(u,d(center,mark)).
                assert np.all(u+distances[nz] <= 3*np.maximum(u, radii))
                # The output plus the retained center and mark has diameter <= 2M.
                assert np.all(distances[nz] <= 2*np.maximum(u, radii))
                basis_count += 1
                triples += len(nz)*n
    print('Marked homotopy supports pass at length', length, flush=True)
    return dict(length=length, basis_vectors=basis_count, marked_output_checks=triples,
                arithmetic='exact int64', all_marked_sites=True)


def exact_mean_and_action_checks():
    x, y, r, s, volume = sym.symbols('x y r s V', positive=True)
    k = x*x*y + x*r*s + y*s*s + r*r*s + x*y*r*s
    # Background contributions to each mean can be arbitrary constants.
    rx, sy = 2+x/volume, 3+y/volume
    composed = -k.subs({r: rx, s: sy}, simultaneous=True)
    expanded = -(sym.diff(k, x, y)+(sym.diff(k, x, s)+sym.diff(k, r, y))/volume
                 + sym.diff(k, r, s)/volume**2).subs({r: rx, s: sy}, simultaneous=True)
    assert sym.simplify(sym.diff(composed, x, y)-expanded) == 0
    incomplete = -sym.diff(k, x, y).subs({r: rx, s: sy}, simultaneous=True)
    assert sym.simplify(expanded-incomplete) != 0
    model, _, fields = example()
    torus = CubicalTorus(model.lengths)
    a = fields[0]
    omega = np.random.default_rng(2026091012).uniform(-1, 1, model.n)
    f = field_strength(torus, a)
    fg = field_strength(torus, a+gradient(model, omega))
    assert np.linalg.norm(fg-f) < 1e-13
    # 2 sin^2(F/2) is 1-cos(F), evaluated without cancellation near F=0.
    cost = float(np.sum(2*np.sin(f/2)**2))
    weights = [float(np.exp(-coupling*cost)) for coupling in [1, 2]]
    assert cost > 0 and weights[0] > weights[1] > 0
    return dict(mean_hessian_all_four_terms_exact=True,
                dropping_mean_derivatives_fails_exactly=True,
                wilson_plaquette_cost=cost, couplings=[1, 2], boltzmann_weights=weights,
                action_gauge_error=float(np.linalg.norm(fg-f)),
                conclusion='The measure conditions leave the gauge-action coupling undetermined')


def write_report(result):
    root = Path(__file__).resolve().parents[1]
    paths = ['scripts/uniform_reference_locality_audit.py',
             'scripts/reference_phase_descent_audit.py', 'scripts/toron_locality_audit.py',
             'scripts/second_cohomology_audit.py', 'scripts/local_cohomology_audit.py',
             'scripts/radial_measure_audit.py', 'scripts/compact_measure_holonomy_audit.py',
             'scripts/chiral_measure_audit.py', 'scripts/overlap_chirality_audit.py',
             'scripts/gauge_dressed_measure_audit.py', 'scripts/positive_measure_audit.py',
             'UnifiedTheory/Audit/KFCausalUniformReferenceLocality.lean',
             'UNIFORM_REFERENCE_LOCALITY.md', 'data/reference_phase_descent_audit.json']
    result['source_sha256'] = {p: hashlib.sha256((root/p).read_bytes()).hexdigest() for p in paths}
    result['scope'] = 'Finite diagnostics and exact controls; locality proof is analytic; TOE not proved'
    output = root/'data/uniform_reference_locality_audit.json'
    output.write_text(json.dumps(result, indent=2)+'\n')
    print('Wrote', output, flush=True)


def main():
    write_report(dict(marked_homotopy=[marked_homotopy_checks(n) for n in [3, 4]],
                      mean_and_action=exact_mean_and_action_checks(), reference=reference_checks()))


if __name__ == '__main__':
    main()
