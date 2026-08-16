#!/usr/bin/env python3
"""HOW TO GET EMERGENT 4D (landscape search).

The bare and spectral dimensions of the pi/4 / 4-over-sqrt6 law sit
at ~1.7 (super-ordered, r->0.66, nearly chain-like) - the OPPOSITE
of high-dimensional (4D needs r~0.10, sparse/antichain-rich).  So the
question is mechanistic: what makes the sequential growth produce
PARALLEL, manifold-4D causets, and is it in this family at all?

Two levers, both scanned here:
  (A) THE ACTION PHASE phi.  d_eff depends on phi through the
      gap-max-entropy weighting.  We sweep phi and map d_eff(phi) -
      the dimension LANDSCAPE.  phi = pi/4 (2D Born-quadrature) and
      phi = 4/sqrt6 (gravitational 4D normalization) are the
      physically-selected points; the sweep shows whether ANY phi in
      the family reaches d = 4, and whether the selected phases are
      special in the dimension landscape.
  (B) LOCAL vs GLOBAL.  The global ordering-fraction dimension mixes
      all scales and is dominated by large-scale hyper-ordering.  The
      MANIFOLD-FAITHFUL probe is the interval (Alexandrov) dimension:
      for an order-interval I(x,y) = {z : x < z < y}, its internal
      ordering fraction inverts (Myrheim-Meyer) to a dimension that
      is meaningful because the interval IS a causal diamond by
      construction.  We report d_int binned by interval size: local
      4D (d_int -> 4 on small intervals) would be emergent-4D at
      short scales even if the global figure is ~1.7.

Myrheim-Meyer inversion: for a d-dimensional Alexandrov interval the
expected ordering fraction is
    f_d = 1.5 * Gamma(d/2)*Gamma(d+1) / (Gamma(3d/2)*Gamma(d/2)) ...
we use the exact MM relation  f = 1.5 * B(d+1, d/2... ) via the
tabulated continuum values and monotone interpolation:
    d:  2     3      4      5      6
    f: .5000 .2296 .0994 .0417 .0170   (Myrheim 1978 / Meyer 1988)
d_int = monotone-interp of f -> d.

REGISTERED READINGS:
  (i)  LOCAL 4D FOUND: at some phi (ideally 4/sqrt6), d_int on the
       smallest resolvable intervals sits at 4.0 +- 0.3 and is
       STABLE across small sizes -> emergent LOCAL 4D; the ~1.7
       global figure is then a large-scale (curvature/defect) effect,
       and "how to get 4D" = read it locally at the gravitational
       phase.  Report the interval-size window.
  (ii) DIMENSION LANDSCAPE: d_eff(phi) reaches 4 at some phi* != the
       selected phases -> 4D is in the family but needs a different
       (unselected) phase; report phi* and the tension.
  (iii) LOCKED LOW: d_int and d_eff stay < 2.5 for all phi and all
       interval sizes -> the family is dimension-locked below
       manifold-4D; emergent 4D is NOT in this growth class (the
       honest strong negative), and a different growth rule (more
       branching / a different measure) is required.
"""
import math, sys, time
import numpy as np
from scipy.optimize import linprog, minimize

T0 = time.time()
def log(*a): print(f"[{time.time()-T0:7.1f}s]", *a, flush=True)
NBIG = int(sys.argv[1]) if len(sys.argv) > 1 else 50
NPATH = int(sys.argv[2]) if len(sys.argv) > 2 else 40
rng = np.random.default_rng(41)
W2 = {0: 2, 1: -4, 2: 2}
POP16 = np.array([bin(i).count("1") for i in range(1 << 16)], dtype=np.int8)
def popcount(a): return POP16[a & 0xFFFF] + POP16[(a >> 16) & 0xFFFF]
LIMB = 60; LOWM = (1 << LIMB) - 1

# MM continuum ordering-fraction -> dimension table
# CORRECTED 2026-08-15: the previous version passed a non-monotonic
# xp to np.interp, which SILENTLY CLAMPED every f <= 0.5 to d = 2.00
# - a broken estimator that produced the spurious "d_int = 2 at all
# phases" result (retracted; see HOW_TO_GET_4D.md correction).
MM_D = np.array([1.5, 2, 3, 4, 5, 6, 8], float)
MM_F = np.array([0.75, 0.5000, 0.2296, 0.0994, 0.0417, 0.0170, 0.00287])
_ORD = np.argsort(-np.log(MM_F))          # ascending in -log f
_XP = (-np.log(MM_F))[_ORD]; _FP = MM_D[_ORD]
def d_from_f(f):
    if f is None or f <= 0: return float("nan")
    return float(np.interp(-math.log(f), _XP, _FP))

def make_law(PHI):
    C8 = [math.cos(k * PHI) for k in range(64)]
    S8 = [math.sin(k * PHI) for k in range(64)]
    cache = {}
    def law(gapcounts):
        key = tuple(sorted(gapcounts.items()))
        if key in cache: return cache[key]
        gaps = sorted(gapcounts); mu = np.array([gapcounts[g] for g in gaps], float)
        A = np.vstack([mu * np.array([C8[g % 64] for g in gaps]),
                       mu * np.array([S8[g % 64] for g in gaps])])
        b = np.array([1.0, 0.0]); K = len(gaps)
        r = linprog(np.zeros(K), A_eq=A, b_eq=b, bounds=[(0, None)] * K, method="highs")
        if not r.success: cache[key] = None; return None
        x0 = r.x
        res = minimize(lambda x: float(np.dot(mu, x * x)), x0, jac=lambda x: 2 * mu * x,
                       constraints=[{"type": "eq", "fun": lambda x: A @ x - b, "jac": lambda x: A}],
                       bounds=[(0, None)] * K, method="SLSQP", options={"maxiter": 200, "ftol": 1e-12})
        xm = res.x if res.success else x0
        if float(np.dot(mu, xm * xm)) > 1 + 1e-7: cache[key] = None; return None
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
            else: cache[key] = None; return None
        f = lambda t: float(np.dot(mu, ((1 - t) * xm + t * xhi) ** 2)) - 1.0
        lo, hi = 0.0, 1.0
        for _ in range(80):
            mid = 0.5 * (lo + hi)
            if f(mid) <= 0: lo = mid
            else: hi = mid
        xfe = np.maximum((1 - lo) * xm + lo * xhi, 0.0)
        def negH(x):
            q = mu * x * x
            return float(np.sum(q * np.log(q + 1e-300)))
        cons = [{"type": "eq", "fun": lambda x: A @ x - b, "jac": lambda x: A},
                {"type": "eq", "fun": lambda x: float(np.dot(mu, x * x)) - 1.0, "jac": lambda x: 2 * mu * x}]
        best = (negH(xfe), xfe)
        r2 = minimize(negH, xfe, constraints=cons, bounds=[(0, None)] * K, method="SLSQP", options={"maxiter": 200, "ftol": 1e-11})
        if r2.success:
            x2 = np.maximum(r2.x, 0.0)
            if abs(float(np.dot(mu, x2 * x2)) - 1) < 1e-6 and np.max(np.abs(A @ x2 - b)) < 1e-6 and negH(x2) < best[0]:
                best = (negH(x2), x2)
        x = best[1]; out = {g: x[i] ** 2 for i, g in enumerate(gaps)}
        cache[key] = out; return out
    return law

CGAP = np.array([-1, 9, -16, 8, 0], dtype=np.int64)   # 4D coefficients

def grow(N, law, coeffs):
    below = [0]; above = [0]
    ids0 = np.array([0, 1], dtype=np.int64); ids1 = np.array([0, 0], dtype=np.int64)
    for n in range(1, N):
        gaps = np.ones(len(ids0), dtype=np.int64)
        for y in range(n):
            iy = (((ids0 if y < LIMB else ids1) >> (y % LIMB)) & 1) == 1
            if not iy.any(): continue
            A0 = np.int64(above[y] & LOWM); A1 = np.int64(above[y] >> LIMB)
            k = popcount(ids0 & A0) + popcount(ids1 & A1)
            k = np.minimum(k, len(coeffs) - 1)
            gaps += np.where(iy, coeffs[k], 0)
        gu, inv, mult = np.unique(gaps, return_inverse=True, return_counts=True)
        gc = {int(g): int(m) for g, m in zip(gu, mult)}
        x = law(gc)
        if x is None: return None
        xa = np.array([x[int(g)] for g in gaps.tolist()])
        probs = np.maximum(xa, 0); s = probs.sum()
        if s <= 0: return None
        j = rng.choice(len(ids0), p=probs / s)
        D = int(ids0[j]) | (int(ids1[j]) << LIMB)
        D0 = np.int64(D & LOWM); D1 = np.int64(D >> LIMB)
        keep = ((ids0 & D0) == D0) & ((ids1 & D1) == D1)
        if n < LIMB: nb0, nb1 = np.int64(1 << n), np.int64(0)
        else: nb0, nb1 = np.int64(0), np.int64(1 << (n - LIMB))
        ids0 = np.concatenate([ids0, ids0[keep] | nb0])
        ids1 = np.concatenate([ids1, ids1[keep] | nb1])
        if len(ids0) > 4_000_000: return None
        below.append(D); above.append(0)
        m = D
        while m:
            d = (m & -m).bit_length() - 1
            above[d] |= 1 << n; m &= m - 1
    return below, above

def global_r(below, N):
    nrel = sum(bin(below[x]).count("1") for x in range(N))
    return nrel / (N * (N - 1) / 2)

def interval_dims(below, above, N, samples=400):
    """sample order-intervals, bin d_int by interval cardinality."""
    bins = {}   # size-bucket -> list of internal ordering fractions
    tries = 0
    got = 0
    while got < samples and tries < samples * 20:
        tries += 1
        x = rng.integers(N); y = rng.integers(N)
        if not ((above[x] >> y) & 1):   # need x < y
            x, y = y, x
        if not ((above[x] >> y) & 1): continue
        # interval = elements strictly between x and y = above[x] & below[y]
        inter = above[x] & below[y]
        k = bin(inter).count("1")
        if k < 4: continue
        # internal relations among interval elements
        elems = []
        m = inter
        while m:
            e = (m & -m).bit_length() - 1; elems.append(e); m &= m - 1
        nrel = sum(bin(below[e] & inter).count("1") for e in elems)
        f = nrel / (k * (k - 1) / 2)
        bucket = 2 ** int(math.log2(k))   # size bucket by powers of 2
        bins.setdefault(bucket, []).append(f)
        got += 1
    return bins

import os
if os.environ.get("PHASES"):
    PHASES = [(p, float(eval(p, {"pi": math.pi, "sqrt": math.sqrt})))
              for p in os.environ["PHASES"].split(",")]
else:
    PHASES = [("pi/4", math.pi/4), ("4/sqrt6", 4/math.sqrt(6)),
              ("pi/6", math.pi/6), ("pi/3", math.pi/3),
              ("1.0", 1.0), ("2.0", 2.0), ("2.5", 2.5)]

log(f"NBIG={NBIG} NPATH={NPATH}; scanning {len(PHASES)} phases")
results = []
for name, phi in PHASES:
    law = make_law(phi)
    rs = []; allbins = {}
    got = 0; fails = 0
    while got < NPATH and fails < NPATH * 3:
        res = grow(NBIG, law, CGAP)
        if res is None: fails += 1; continue
        below, above = res
        rs.append(global_r(below, NBIG))
        b = interval_dims(below, above, NBIG)
        for k, v in b.items(): allbins.setdefault(k, []).extend(v)
        got += 1
    if not rs:
        log(f"  phi={name:8s}: INFEASIBLE ({fails} fails)")
        continue
    rG = float(np.mean(rs))
    # continuum-diamond global inversion uses d_from_f too (interval-faithful table)
    dG = d_from_f(rG)
    # interval dims by bucket
    idims = {}
    for k in sorted(allbins):
        fm = float(np.mean(allbins[k]))
        idims[k] = (d_from_f(fm), len(allbins[k]), fm)
    results.append((name, phi, rG, dG, idims))
    istr = "  ".join(f"[k~{k}] d={idims[k][0]:.2f}(n{idims[k][1]})"
                     for k in sorted(idims))
    log(f"  phi={name:8s}: global r={rG:.3f} d={dG:.2f} | intervals: {istr}")

log("== VERDICT (registered readings) ==")
# local 4D?
best_local = None
for name, phi, rG, dG, idims in results:
    for k in sorted(idims):
        d, cnt, _ = idims[k]
        if cnt >= 30 and 3.7 <= d <= 4.3:
            best_local = (name, k, d)
# landscape 4D (global)?
best_global = max(results, key=lambda t: t[3]) if results else None
if best_local:
    log(f"  reading (i) LOCAL 4D at phi={best_local[0]}, interval "
        f"size ~{best_local[1]}: d_int={best_local[2]:.2f} - emergent "
        "local 4D; global ~1.7 is a large-scale effect.")
elif best_global and best_global[3] >= 3.5:
    log(f"  reading (ii) LANDSCAPE: global d reaches {best_global[3]:.2f} "
        f"at phi={best_global[0]} - 4D in the family at that phase.")
else:
    dmax = max((idims[k][0] for _,_,_,_,idims in results for k in idims),
               default=float('nan'))
    log(f"  reading (iii) LOCKED LOW: max interval dimension over all "
        f"phases = {dmax:.2f} < manifold-4D; emergent 4D is NOT in this "
        "growth class - a different growth rule / measure is required.")
log("DONE")
