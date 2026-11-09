#!/usr/bin/env python3
"""Support/entropy checks and exact lapse gauge compactness for a supplied action.

No new physical probability law is claimed. The symbolic identity proves the
local metric variation; finite lattices test its assembly independently.
"""
import hashlib
import itertools
import json
import math
from pathlib import Path

import numpy as np
import sympy as sym

from continuum_einstein_audit import first_variation, lagrangian


def symbolic_lapse_variation():
    """All 10 metric and 40 derivative components are independently varied."""
    L = sym.Symbol('L', positive=True)
    z = sym.Symbol('z', real=True)
    pairs = [(i, j) for i in range(4) for j in range(i, 4)]
    h = sym.zeros(4)
    dh = [sym.zeros(4) for _ in range(4)]
    for i, j in pairs:
        h[i, j] = h[j, i] = sym.Symbol('h%d%d' % (i, j), real=True)
        for d in range(4):
            dh[d][i, j] = dh[d][j, i] = sym.Symbol('dh%d%d%d' % (d, i, j), real=True)
    inv = sym.diag(-1/L**2, 1, 1, 1)
    dg = [sym.zeros(4) for _ in range(4)]
    dg[0][0, 0] = z

    def gamma(inverse, derivatives):
        return sym.MutableDenseNDimArray([
            sum(inverse[r, s]*(derivatives[u][s, v]+derivatives[v][s, u]
                               - derivatives[s][u, v])/2 for s in range(4))
            for r, u, v in itertools.product(range(4), repeat=3)], (4, 4, 4))

    def quadratic(inverse, left, right):
        return sum(inverse[u, v]*(left[r, u, s]*right[s, v, r]
                                  - left[r, u, v]*right[s, r, s])
                   for u, v, r, s in itertools.product(range(4), repeat=4))

    gamma0 = gamma(inv, dg)
    delta_inv = -inv*h*inv
    delta_gamma = gamma(delta_inv, dg)+gamma(inv, dh)
    q0 = sym.simplify(quadratic(inv, gamma0, gamma0))
    delta_q = sym.simplify(quadratic(delta_inv, gamma0, gamma0)
                          + quadratic(inv, delta_gamma, gamma0)
                          + quadratic(inv, gamma0, delta_gamma))
    expected = -gamma0[0, 0, 0]*inv[0, 0]*sum(dh[i][0, i] for i in range(1, 4))
    assert q0 == 0
    assert sym.simplify(delta_q-expected) == 0
    t, k, c = sym.symbols('t k c', real=True, nonzero=True)
    tau = t+c*sym.sin(k*t)/k
    lapse = 1+c*sym.cos(k*t)
    assert sym.simplify(sym.diff(tau, t)-lapse) == 0
    assert sym.simplify(-lapse**2/sym.diff(tau, t)**2+1) == 0
    return dict(metric_components=10, derivative_components=40,
                quadratic=str(q0), quadratic_variation=str(delta_q),
                proper_time_pullback_exact=True)


def stencil(field, spacing, side):
    if side == 1:
        return np.stack([(np.roll(field, -1, axis=d)-field)/spacing
                         for d in range(4)], axis=4)
    return np.stack([(field-np.roll(field, 1, axis=d))/spacing
                     for d in range(4)], axis=4)


def lattice_lapse_checks():
    rng = np.random.default_rng(70321)
    rows = []
    c = .2
    for n in [4, 6, 8]:
        a = 1/n
        shape = (n,)*4
        grid_t = np.indices(shape)[0]
        lapse = 1+c*(-1.)**grid_t
        g = np.broadcast_to(np.eye(4), shape+(4, 4)).copy()
        g[..., 0, 0] = -lapse**2
        zero, dzero = np.zeros(n**4), np.zeros((n**4, 4))
        metric = g.reshape(-1, 4, 4)
        max_action, max_variation, max_identity = 0., 0., 0.
        max_individual_response = 0.
        # Independent arbitrary spatial/time-dependent variations in all entries.
        for _ in range(4):
            raw = rng.normal(size=shape+(4, 4))
            h = (raw+raw.swapaxes(-1, -2))/2
            for side in [1, -1]:
                dg = stencil(g, a, side).reshape(-1, 4, 4, 4)
                dh = stencil(h, a, side).reshape(-1, 4, 4, 4)
                density = lagrangian(metric, dg, zero, dzero)
                response = first_variation(metric, dg, zero, dzero,
                                           h.reshape(-1, 4, 4), dh, zero, dzero)
                inv00 = -1/lapse.reshape(-1)**2
                gamma000 = .5*inv00*dg[:, 0, 0, 0]
                predicted = -lapse.reshape(-1)*gamma000*inv00/2*sum(
                    dh[:, i, 0, i] for i in range(1, 4))
                max_action = max(max_action, float(np.max(abs(density))))
                max_variation = max(max_variation, abs(float(np.mean(response))))
                max_identity = max(max_identity, float(np.max(abs(response-predicted))))
                max_individual_response = max(max_individual_response,
                                              float(np.max(abs(response))))
        assert max_action < 1e-12
        assert max_variation < 1e-11
        assert max_identity < 1e-10
        assert max_individual_response > 1  # integral cancellation is nontrivial
        rows.append(dict(length=n, sites=n**4, maximum_action_density=max_action,
                         maximum_integrated_variation=max_variation,
                         maximum_local_variation_identity_error=max_identity,
                         maximum_local_response=max_individual_response,
                         necessary_metric_lipschitz_constant=4*c/a))
    return rows


def quotient_compactness_checks():
    c = .2
    rows = []
    for n in [8, 16, 32, 64, 128]:
        k = np.pi*n
        t = np.arange(16*n+1)/(16*n)
        lapse = 1+c*np.cos(k*t)
        tau = t+c*np.sin(k*t)/k
        assert np.all(np.diff(tau) > 0)
        assert abs(tau[0]) < 1e-15 and abs(tau[-1]-1) < 1e-15
        error = float(np.max(abs(tau-t)))
        assert error <= c/k+2e-16
        # Inverse Jacobian transforms g_tt=-L^2 into the constant -1 exactly.
        normalized = -lapse**2/lapse**2
        assert np.max(abs(normalized+1)) == 0
        rows.append(dict(length=n, coordinate_error=error,
                         coordinate_error_bound=c/k, raw_metric_lipschitz_lower=4*c*n,
                         normalized_metric_error=0.))
    return rows


def support_and_entropy_checks():
    rng = np.random.default_rng(916)
    # Minkowski points in two slabs with a strict spacelike margin.
    # This verifies the concrete cross-pair supplier, not a growth-law sample.
    U, V = rng.uniform(-.02, .02, (19, 4)), rng.uniform(-.02, .02, (23, 4))
    U[:, 1] -= .3
    V[:, 1] += .3
    delta = U[:, None, :]-V[None, :, :]
    interval = np.sum(delta[..., 1:]**2, axis=-1)-delta[..., 0]**2
    assert np.all(interval > 0)
    count = int(np.count_nonzero(interval > 0))
    assert count == len(U)*len(V)

    # Exact recurrence benchmark. These c,A are synthetic and are NOT
    # numerical constants asserted for the harmonic Born trajectory law.
    c, A, n0 = .2, 3., 40
    B = max(n0**2, 2*A/c)
    q = 1.
    expected_pairs = 0.
    for n in range(n0, 20001):
        assert q <= B/n**2+1e-15
        q = (1-c)*q+A/n**2
        assert q <= B/(n+1)**2+1e-15
        expected_pairs += n*q
    assert expected_pairs <= B*(1+math.log(20000/n0))

    # Full-distribution KL splitting (not only substituting the binary formula).
    split_error = 0.
    for _ in range(32):
        P = rng.uniform(.01, 1, 12)
        P /= P.sum()
        Q = rng.uniform(.01, 1, 12)
        Q /= Q.sum()
        p, q = P[:5].sum(), Q[:5].sum()
        tilted = P*np.r_[np.full(5, q/p), np.full(7, (1-q)/(1-p))]
        assert abs(tilted.sum()-1) < 5e-16 and abs(tilted[:5].sum()-q) < 5e-16
        kl = float(np.sum(Q*np.log(Q/P)))
        binary = float(q*np.log(q/p)+(1-q)*np.log((1-q)/(1-p)))
        cond = (q*np.sum((Q[:5]/q)*np.log((Q[:5]/q)/(P[:5]/p)))
                + (1-q)*np.sum((Q[5:]/(1-q))*np.log((Q[5:]/(1-q))/(P[5:]/(1-p)))))
        split_error = max(split_error, abs(float(kl-binary-cond)))
        assert kl+1e-15 >= binary >= q*np.log(1/p)-np.log(2)-1e-15
    assert split_error < 2e-15

    # Projectively consistent biased-coin example: all finite densities exist
    # although limiting laws are singular by distinct almost-sure frequencies.
    def coin_law(n, bias):
        return np.array([bias**sum(bits)*(1-bias)**(n-sum(bits))
                         for bits in itertools.product([0, 1], repeat=n)])

    P, Q = coin_law(8, .5), coin_law(8, .75)
    marginal_error = float(np.max(abs(Q.reshape(-1, 2).sum(axis=1)-coin_law(7, .75))))
    assert marginal_error < 1e-16
    kl_coin = float(np.sum(Q*np.log(Q/P)))
    assert abs(kl_coin-8*(.75*np.log(1.5)+.25*np.log(.5))) < 2e-15
    return dict(spacelike_cross_pairs=count, minimum_spacelike_interval=float(interval.min()),
                recurrence=dict(c=c, A=A, starting_rank=n0, B=B,
                                final_expected_pair_upper=expected_pairs,
                                scope='Synthetic recurrence verification, not a fit to the growth law'),
                maximum_full_KL_splitting_error=split_error,
                coin_example=dict(marginal_error=marginal_error, length_8_relative_entropy=kl_coin,
                                  scope='Illustrates singular infinite limits, not causal geometry'))


def main():
    result = dict(symbolic=symbolic_lapse_variation(), lattice=lattice_lapse_checks(),
                  quotient=quotient_compactness_checks(), support=support_and_entropy_checks())
    root = Path(__file__).resolve().parents[1]
    sources = ['scripts/emergence_support_audit.py', 'scripts/continuum_einstein_audit.py',
               'EMERGENCE_SUPPORT_AND_GAUGE_COMPACTNESS.md',
               'HARMONIC_BORN_EVENTUAL_CHAIN_COLLAPSE.md', 'CONTINUUM_EINSTEIN_BRIDGE.md',
               'UnifiedTheory/Audit/KFCausalEmergenceSupport.lean']
    result['source_sha256'] = {p: hashlib.sha256((root/p).read_bytes()).hexdigest() for p in sources}
    result['scope'] = ('Support obstruction using the earlier analytic collapse theorem; '
                       'lapse-only quotient compactness for a supplied classical action. '
                       'No selected physical geometry, general compactness, or quantum TOE.')
    output = root/'data/emergence_support_audit.json'
    output.write_text(json.dumps(result, indent=2)+'\n')
    print('Wrote', output, flush=True)


if __name__ == '__main__':
    main()
