#!/usr/bin/env python3
"""Numerics, not proof. Straight line across a box with flat boundary condition.

TwistedBridge.loop_cross_bound proves, for the links at a vertex (ell = 1), that the boundary influence on a line
through the box is at least the conditional expectation of a closed rectangular Wilson loop running straight through
the box. With exterior links equal to the identity the rest of the loop is the identity, so that expectation is the
number w measured here. So w is the box expectation of a gauge-invariant observable, not only of an open line.
TwistedBridge.star_margin_of_expectation proves, at every coupling, that the star criterion has margin at most 2 - 4 w
if every rectangle has expectation at least w at flat boundary condition. Lean only bounds that expectation below for
large repo beta (line_expectation). Matching the Lean flat boundary, including near the seam, with the identity exterior
used here is a hand argument.
A hand count, not in Lean, gives for a cube of side ell: the criterion needs w <= (ell + 1)/(ell + 3), where w is the
average over straight lines of length ell + 1 across the box. The count is a sufficient condition for failure only.

This script measures w for SU(2), repo beta = beta_std / 2, weight exp(beta Re tr P), by a checkerboard heat bath.
Links with an endpoint in the cube are dynamical. All others are fixed to the identity. Untwisted: the flat boundary
condition is pure gauge in a box away from the seam, and the twist only moves the seam. No reflection positivity.

w carries the lattice self-energy of a bare line, so its decay in ell is not a physical length. The test probes one
family of observables. Being below the threshold is not evidence that the criterion holds.

Errors are sigma * sqrt(2 tau_int / N) with tau_int from a self-consistent window. Runs start cold. Each point is one
Markov chain. The check at small beta compares with the strong-coupling value w = (3/8) beta_std^2 (1 + beta_std) + O(beta_std^4)
for ell = 1, derived by hand.

History: an earlier version of this script had np.roll(inW, 1, axis=mu) in the dynamical mask, which froze the first
link of each line and made links outside the cube dynamical. All numbers from that version were wrong and are replaced.
"""
import os
for k in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "VECLIB_MAXIMUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[k] = "1"
import json
import math
import sys
import time

import numpy as np


def qmul(a, b):
    w = a[..., 0] * b[..., 0] - a[..., 1] * b[..., 1] - a[..., 2] * b[..., 2] - a[..., 3] * b[..., 3]
    x = a[..., 0] * b[..., 1] + a[..., 1] * b[..., 0] + a[..., 2] * b[..., 3] - a[..., 3] * b[..., 2]
    y = a[..., 0] * b[..., 2] - a[..., 1] * b[..., 3] + a[..., 2] * b[..., 0] + a[..., 3] * b[..., 1]
    z = a[..., 0] * b[..., 3] + a[..., 1] * b[..., 2] - a[..., 2] * b[..., 1] + a[..., 3] * b[..., 0]
    return np.stack((w, x, y, z), axis=-1)


def qconj(a):
    return a * np.array([1.0, -1.0, -1.0, -1.0])


def staple_sum(U, mu):
    """A with weight exp(beta * 2 Re(U_mu A)) for each link of direction mu."""
    A = np.zeros_like(U[mu])
    for nu in range(4):
        if nu == mu:
            continue
        U_nu_xmu = np.roll(U[nu], -1, axis=mu)
        U_mu_xnu = np.roll(U[mu], -1, axis=nu)
        A += qmul(qmul(U_nu_xmu, qconj(U_mu_xnu)), qconj(U[nu]))
        U_nu_xmu_mnu = np.roll(U_nu_xmu, 1, axis=nu)
        U_mu_mnu = np.roll(U[mu], 1, axis=nu)
        U_nu_mnu = np.roll(U[nu], 1, axis=nu)
        A += qmul(qmul(qconj(U_nu_xmu_mnu), qconj(U_mu_mnu)), U_nu_mnu)
    return A


def sample_x0(a, rng):
    """Density proportional to sqrt(1-x^2) exp(a x) on [-1,1], with a >= 0."""
    x = np.zeros_like(a)
    todo = np.ones_like(a, dtype=bool)
    big = a > 1.0
    while todo.any():
        idx = np.nonzero(todo)[0]
        ai = a[idx]
        trial = np.zeros_like(ai)
        accept = np.zeros_like(ai, dtype=bool)
        b = big[idx]
        if b.any():
            r1, r2, r3, r4 = (1.0 - rng.random((4, b.sum())))
            lam2 = -(np.log(r1) + np.cos(2 * np.pi * r2) ** 2 * np.log(r3)) / (2.0 * ai[b])
            trial[b] = 1.0 - 2.0 * lam2
            accept[b] = r4 ** 2 <= 1.0 - lam2
        s = ~b
        if s.any():
            m = s.sum()
            as_ = np.maximum(ai[s], 1e-12)
            u = rng.random(m)
            lo = np.exp(-as_)
            hi = np.exp(as_)
            t = np.log(lo + u * (hi - lo)) / as_
            t = np.clip(t, -1.0, 1.0)
            trial[s] = t
            accept[s] = rng.random(m) ** 2 <= 1.0 - t ** 2
        x[idx[accept]] = trial[accept]
        todo[idx[accept]] = False
    return x


def heat_bath(U, masks, beta, rng):
    for mu in range(4):
        for par in (0, 1):
            m = masks[mu][par]
            if not m.any():
                continue
            A = staple_sum(U, mu)[m]
            k = np.sqrt((A ** 2).sum(axis=-1))
            k = np.maximum(k, 1e-14)
            Ahat = A / k[..., None]
            x0 = sample_x0(2.0 * beta * k, rng)
            v = rng.normal(size=(x0.size, 3))
            v /= np.sqrt((v ** 2).sum(axis=-1, keepdims=True))
            V = np.concatenate((x0[:, None], np.sqrt(np.maximum(1 - x0 ** 2, 0.0))[:, None] * v), axis=-1)
            U[mu][m] = qmul(V, qconj(Ahat))


def line_average(U, ell):
    """Mean Re hol over straight lines from coordinate 1 to ell+2 across W = 2..ell+1, all directions."""
    vals = []
    trans = tuple(slice(2, ell + 2) for _ in range(3))
    for mu in range(4):
        Umu = np.moveaxis(U[mu], mu, 0)[(slice(None),) + trans]
        hol = Umu[1]
        for t in range(2, ell + 2):
            hol = qmul(hol, Umu[t])
        vals.append(hol[..., 0].ravel())
    return np.concatenate(vals).mean()




def run(ell, beta_std, sweeps, therm, seed):
    rng = np.random.default_rng(seed)
    beta = beta_std / 2.0
    L = ell + 4
    shape = (L, L, L, L)
    U = np.zeros((4,) + shape + (4,))
    U[..., 0] = 1.0
    coords = np.indices(shape)
    inW = np.all((coords >= 2) & (coords <= ell + 1), axis=0)
    parity = coords.sum(axis=0) % 2
    masks = []
    for mu in range(4):
        touching = inW | np.roll(inW, -1, axis=mu)
        masks.append([touching & (parity == p) for p in (0, 1)])
    # a link touches the cube exactly when its base or its endpoint is in it
    n_dyn = sum(int(m[0].sum() + m[1].sum()) for m in masks)
    assert n_dyn == 4 * (ell + 1) * ell ** 3, n_dyn
    for mu in range(4):
        line = [slice(2, ell + 2)] * 4
        line[mu] = slice(1, ell + 2)
        assert (masks[mu][0] | masks[mu][1])[tuple(line)].all()
    for _ in range(therm):
        heat_bath(U, masks, beta, rng)
    series = []
    for _ in range(sweeps):
        heat_bath(U, masks, beta, rng)
        series.append(line_average(U, ell))
    series = np.array(series)
    tau = tau_int(series)
    return float(series.mean()), float(series.std(ddof=1) * math.sqrt(2.0 * tau / series.size)), tau


def tau_int(x, c=6.0):
    """Integrated autocorrelation time with a self-consistent window (Madras-Sokal)."""
    y = x - x.mean()
    n = y.size
    if y.var() == 0.0:
        return 0.5
    f = np.fft.rfft(y, 2 * n)
    acf = np.fft.irfft(f * np.conj(f))[:n] / np.arange(n, 0, -1)
    rho = acf / acf[0]
    tau = 0.5
    for m in range(1, n):
        tau += rho[m]
        if m >= c * tau:
            break
    return max(float(tau), 0.5)


def line_defect(beta):
    """The Lean bound lineDefect beta = (16/beta) log cap(24 beta), evaluated numerically, with cap(s) = 4 sqrt(pi) s sqrt(s)
    taken by hand. That constant is not proved in Lean; only the existence of a threshold is."""
    s = 24.0 * beta
    return 16.0 / beta * math.log(4.0 * math.sqrt(math.pi) * s * math.sqrt(s))


def main():
    out_path = sys.argv[1]
    plan = {
        1: (6000, 500),
        2: (3000, 300),
        3: (1200, 200),
        4: (600, 150),
        6: (300, 100),
    }
    betas = [1.0, 1.5, 2.0, 2.2, 2.4, 2.6, 3.0, 4.0, 6.0, 8.0, 16.0, 64.0]
    t0 = time.time()
    checks = []
    for b in (0.2, 0.3, 0.5):
        w, e, tau = run(1, b, 30000, 500, seed=7000 + int(10 * b))
        lead = 3.0 / 8.0 * b ** 2 * (1.0 + b)
        checks.append(dict(ell=1, beta_std=b, w=w, err=e, tau=tau, strong_coupling_through_cubic=lead))
        print(f"check beta_std={b}: w={w:+.5f}({e:.5f}) through cubic={lead:.5f}", flush=True)
    rows = []

    def dump(extra=None):
        res = dict(kind="numerics, not proof", note=__doc__, small_beta_checks=checks, rows=rows)
        res.update(extra or {})
        with open(out_path, "w") as f:
            json.dump(res, f, indent=1)

    for ell, (sw, th) in plan.items():
        thr = (ell + 1) / (ell + 3)
        for b in betas:
            w, e, tau = run(ell, b, sw, th, seed=1000 * ell + int(10 * b))
            rows.append(dict(ell=ell, beta_std=b, w=w, err=e, tau=tau, sweeps=sw, threshold=thr,
                             above=bool(w > thr), sigma_from_threshold=(w - thr) / e if e > 0 else None,
                             elapsed=time.time() - t0))
            print(f"ell={ell} beta_std={b:5.1f} w={w:+.4f}({e:.4f}) tau={tau:.1f} thr={thr:.3f} {'ABOVE' if w > thr else ''} t={time.time()-t0:.0f}s",
                  flush=True)
            dump()
    # where the Lean bound becomes nontrivial
    b = 1.0
    while line_defect(b) >= 0.5:
        b *= 1.01
    dump(dict(lean_threshold_estimate_repo_beta=b, lean_threshold_estimate_beta_std=2 * b))
    print("lineDefect < 1/2 from repo beta about", b)


if __name__ == "__main__":
    main()
