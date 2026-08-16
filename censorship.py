#!/usr/bin/env python3
"""THICKENED-ANTICHAIN GROWTH vs DOUBLE CONSERVATION (registered).

DEFINITION (the class under test).  Width-w thickened-antichain
growth = sequential growth in which each new element's past must be
D = down-closure of a w-antichain, i.e. the allowed children at each
step are exactly the downsets D of the current causet with
|max(D)| = w (w maximal elements).  w=1: principal pasts (tree-like);
larger w: the new element caps a wide antichain (spatial extent -
the proposed 4D route).  Where NO width-w downset exists, we allow
the largest available width (documented fallback; counted).  The
free-downset control is w=None.  D = empty set (width 0, new
minimum) is EXCLUDED for w >= 1.

DOUBLE CONSERVATION on the restricted family: per parent, amplitudes
a_D = x_{g(D)} e^{i phi g(D)} with x >= 0 on the RESTRICTED gap
spectrum must satisfy
   sum mu_g x_g cos(phi g) = 1,  sum mu_g x_g sin(phi g) = 0,
   sum mu_g x_g^2 = 1
(gap-max-entropy selection among solutions, same as the free law).
THEORETICAL RISK: restriction shrinks the gap spectrum; the linear
part needs (1,0) in the cone of {(cos phi g, sin phi g)} over
available gaps, and the min-norm solution must have sum mu x^2 <= 1.
Fewer distinct gaps => both can fail.  A degenerate spectrum (single
gap g, multiplicity mu) is feasible iff sin(phi g) = 0, cos(phi g)=1
and mu = 1 - essentially never.  So feasibility is a REAL question,
not a formality.

MEASUREMENTS per width w in {1,2,3,4,5,None} at phi = pi/4:
  - feasibility: fraction of paths aborted by an infeasible parent
    (law None / empty child set), and the abort-depth profile;
  - fallback rate (steps where width-w unavailable);
  - on surviving paths: global r, and interval dimension d_int by
    size bin (CORRECTED monotone MM inverter) - does thickening
    actually raise the discreteness-scale dimension?

REGISTERED READINGS:
  (i)  SURVIVES + LIFTS: feasibility comparable to free growth
       (>= ~90% paths complete) at some w >= 2 AND d_int(k~4..8)
       rises materially above the free-growth value (toward 3+):
       the 4D route through thickened growth is ALIVE with double
       conservation intact.
  (ii) OBSTRUCTION: feasibility collapses (most paths abort) at all
       w >= 2 - thickening and double conservation are in tension;
       report the abort-depth profile; candidate package-deal
       theorem (quantum structure <=> thin growth) to be sharpened.
  (iii) SURVIVES BUT FLAT: feasible but d_int does not rise -
       thickening (in this exact-width form) is not the dimension
       lever; the 4D route needs a different mechanism.
  (iv) MIXED: width- or depth-dependent boundary; map it.
"""
import math, os, sys, time
import numpy as np
from scipy.optimize import linprog, minimize

T0 = time.time()
def log(*a): print(f"[{time.time()-T0:7.1f}s]", *a, flush=True)
NBIG = int(sys.argv[1]) if len(sys.argv) > 1 else 26
NPATH = int(sys.argv[2]) if len(sys.argv) > 2 else 25
PHI = float(eval(os.environ.get("PHI", "math.pi/4"), {"math": math}))
rng = np.random.default_rng(43)
W2 = {0: 2, 1: -4, 2: 2}
POP16 = np.array([bin(i).count("1") for i in range(1 << 16)], dtype=np.int16)
def popcount(a):
    # FIXED 2026-08-16: previous version counted only 32 bits,
    # corrupting interval counts for element labels >= 32 (all
    # thickened/rate results at n > 32 are tainted; reruns required).
    return (POP16[a & 0xFFFF] + POP16[(a >> 16) & 0xFFFF]
            + POP16[(a >> 32) & 0xFFFF] + POP16[(a >> 48) & 0x7FFF])
LIMB = 60; LOWM = (1 << LIMB) - 1

MM_D = np.array([1.5, 2, 3, 4, 5, 6, 8], float)
MM_F = np.array([0.75, 0.5000, 0.2296, 0.0994, 0.0417, 0.0170, 0.00287])
_ORD = np.argsort(-np.log(MM_F))
_XP = (-np.log(MM_F))[_ORD]; _FP = MM_D[_ORD]
def d_from_f(f):
    if f is None or f <= 0: return float("nan")
    return float(np.interp(-math.log(f), _XP, _FP))

CV = [math.cos(k * PHI) for k in range(64)]
SV = [math.sin(k * PHI) for k in range(64)]
LAW_CACHE = {}
def maxent_gap_law(gapcounts):
    key = tuple(sorted(gapcounts.items()))
    if key in LAW_CACHE: return LAW_CACHE[key]
    gaps = sorted(gapcounts); mu = np.array([gapcounts[g] for g in gaps], float)
    A = np.vstack([mu * np.array([CV[g % 64] for g in gaps]),
                   mu * np.array([SV[g % 64] for g in gaps])])
    b = np.array([1.0, 0.0]); K = len(gaps)
    r = linprog(np.zeros(K), A_eq=A, b_eq=b, bounds=[(0, None)] * K, method="highs")
    if not r.success: LAW_CACHE[key] = None; return None
    res = minimize(lambda x: float(np.dot(mu, x * x)), r.x, jac=lambda x: 2 * mu * x,
                   constraints=[{"type": "eq", "fun": lambda x: A @ x - b, "jac": lambda x: A}],
                   bounds=[(0, None)] * K, method="SLSQP", options={"maxiter": 200, "ftol": 1e-12})
    xm = res.x if res.success else r.x
    if float(np.dot(mu, xm * xm)) > 1 + 1e-7: LAW_CACHE[key] = None; return None
    xhi = None
    for t in range(8):
        c = -np.ones(K) if t == 0 else rng.normal(size=K)
        v = linprog(c, A_eq=A, b_eq=b, bounds=[(0, None)] * K, method="highs")
        if v.success and float(np.dot(mu, v.x * v.x)) >= 1 - 1e-9: xhi = v.x; break
    if xhi is None:
        rc = linprog(-np.ones(K), A_eq=A, b_eq=np.zeros(2), bounds=[(0, 1)] * K, method="highs")
        if rc.success and (-rc.fun) > 1e-9:
            d = rc.x / np.linalg.norm(rc.x); t = 1.0
            while float(np.dot(mu, (xm + t * d) ** 2)) < 1: t *= 2
            xhi = xm + t * d
        else: LAW_CACHE[key] = None; return None
    f = lambda t: float(np.dot(mu, ((1 - t) * xm + t * xhi) ** 2)) - 1.0
    lo, hi = 0.0, 1.0
    for _ in range(80):
        mid = 0.5 * (lo + hi)
        if f(mid) <= 0: lo = mid
        else: hi = mid
    xfe = np.maximum((1 - lo) * xm + lo * xhi, 0.0)
    # FIXED 2026-08-16: previous version stopped at the feasibility-
    # boundary point xfe (a different selection-band member); the
    # program's law is gap-MAX-ENTROPY - refinement stage restored.
    def negH(x):
        qq = mu * x * x
        return float(np.sum(qq * np.log(qq + 1e-300)))
    cons = [{"type": "eq", "fun": lambda x: A @ x - b, "jac": lambda x: A},
            {"type": "eq", "fun": lambda x: float(np.dot(mu, x * x)) - 1.0,
             "jac": lambda x: 2 * mu * x}]
    best = (negH(xfe), xfe)
    r2m = minimize(negH, xfe, constraints=cons, bounds=[(0, None)] * K,
                   method="SLSQP", options={"maxiter": 200, "ftol": 1e-11})
    if r2m.success:
        x2 = np.maximum(r2m.x, 0.0)
        if (abs(float(np.dot(mu, x2 * x2)) - 1) < 1e-6
                and np.max(np.abs(A @ x2 - b)) < 1e-6 and negH(x2) < best[0]):
            best = (negH(x2), x2)
    x = best[1]
    out = {g: x[i] ** 2 for i, g in enumerate(gaps)}
    LAW_CACHE[key] = out; return out

RAMP = 10; LINW = 5; BAND = 1
CG = np.array([-1, 9, -16, 8, 0], dtype=np.int64)
PROBES = [16, 22, 28, 34, 40]

log(f"CENSORSHIP: grow wide (w=n/5), probe collapse family feasibility")
from collections import defaultdict
res = defaultdict(list)   # (probe_n) -> list of (W_causet, wmax_feasible)
got = 0
while got < 30:
    below = [0]; above = [0]
    ids0 = np.array([0, 1], dtype=np.int64); ids1 = np.array([0, 0], dtype=np.int64)
    ok = True
    for n in range(1, max(PROBES) + 1):
        m = len(ids0)
        gaps = np.ones(m, dtype=np.int64)
        maxcnt = np.zeros(m, dtype=np.int64)
        for y in range(n):
            iy = (((ids0 if y < LIMB else ids1) >> (y % LIMB)) & 1) == 1
            if not iy.any(): continue
            A0 = np.int64(above[y] & LOWM); A1 = np.int64(above[y] >> LIMB)
            k = popcount(ids0 & A0) + popcount(ids1 & A1)
            kk = np.minimum(k, 4)
            gaps += np.where(iy, CG[kk], 0)
            maxcnt += (iy & (k == 0)).astype(np.int64)
        if n in PROBES:
            W = int(maxcnt.max())
            wmax = 0
            for wmin in range(2, W + 1):
                sel = maxcnt >= wmin
                if not sel.any(): break
                gsel = gaps[sel]; gc = {}
                for gg in gsel.tolist(): gc[gg] = gc.get(gg, 0) + 1
                if maxent_gap_law(gc) is not None: wmax = wmin
            res[n].append((W, wmax))
        # growth step with width rule w = n/5
        wn = max(2, n // LINW)
        if n < RAMP:
            sel = np.ones(m, dtype=bool)
        else:
            sel = (maxcnt >= wn - BAND) & (maxcnt <= wn + BAND)
            if not sel.any(): sel = np.ones(m, dtype=bool)
        gsel = gaps[sel]; gc = {}
        for gg in gsel.tolist(): gc[gg] = gc.get(gg, 0) + 1
        law = maxent_gap_law(gc)
        if law is None: ok = False; break
        probs = np.array([law[gg] for gg in gsel.tolist()])
        probs = np.maximum(probs, 0); s = probs.sum()
        if s <= 0: ok = False; break
        idxs = np.nonzero(sel)[0]
        j = idxs[rng.choice(len(idxs), p=probs / s)]
        D = int(ids0[j]) | (int(ids1[j]) << LIMB)
        D0 = np.int64(D & LOWM); D1 = np.int64(D >> LIMB)
        keep = ((ids0 & D0) == D0) & ((ids1 & D1) == D1)
        nb0, nb1 = (np.int64(1 << n), np.int64(0)) if n < LIMB else (np.int64(0), np.int64(1 << (n - LIMB)))
        ids0 = np.concatenate([ids0, ids0[keep] | nb0]); ids1 = np.concatenate([ids1, ids1[keep] | nb1])
        if len(ids0) > 4_000_000: ok = False; break
        below.append(D); above.append(0)
        mm = D
        while mm:
            d = (mm & -mm).bit_length() - 1
            above[d] |= 1 << n; mm &= mm - 1
    if ok: got += 1
log("== censorship curve: max Born-feasible simultaneous convergence ==")
log("   n    width_W    wmax_feasible   censored fraction (1 - wmax/W)   n/wmax")
for n in sorted(res):
    Ws = [w for w, _ in res[n]]; wm = [x for _, x in res[n]]
    W = np.mean(Ws); w = np.mean(wm)
    log(f"  {n:2d}   {W:5.1f}      {w:5.1f}          {1 - w/W:+.2f}                  {n/max(w,0.1):.1f}")
log("DONE-CENS")
