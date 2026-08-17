#!/usr/bin/env python3
"""SYNTHESIS PROBES (Gudder x ours, registered 2026-08-15).

PROBE A - THE SELECTION THEOREM CANDIDATE.  Gudder's Theorem 2.1
gives the full solution continuum of the double-conservation pair at
a binary node (free phase theta).  On the full downset tree, bulk
feasibility alone does NOT pin the phase (other phi grow via partial
determinism).  Candidate theorem: pi/4 is the UNIQUE phase whose
gap-phased law is feasible AND nowhere-degenerate (the law never
collapses to a deterministic or support-1 choice) on the 2D-weight
tree.  We scan phi and measure, per step: feasibility, support
fraction (children with prob > 1e-9), and normalized entropy of the
law.  READINGS:
  (i)  pi/4 (and mirror pi - pi/4 if parity permits) uniquely
       maximizes nondegeneracy: selection theorem candidate stands -
       'the full tree collapses Gudder's continuum to the symmetric
       point IF the dynamics must keep genuinely branching'.
  (ii) a band of phi equally nondegenerate: selection needs more
       than nondegeneracy; report the flatness.
  (iii) pi/4 not special at all: the root-pinning was an artifact of
       the exact +-1 gap convention; honest demotion.

PROBE B - ACTION TELESCOPING (phase = geometry dictionary).
Gudder's stationary amplitudes meter HEIGHT (quarter-turn per new
shell); our S26 meter is WIDTH (octant per cell).  Candidate: the
cumulative action A = sum of chosen gaps telescopes into a closed
form in final-causet invariants (n, relations R, links L, minima m,
height h, width w).  We regress A on invariants across many paths.
  (i)  exact integer relation (residual 0): the causal action is a
       TOPOLOGICAL/combinatorial invariant - phase quantization is
       counting geometry; report the identity.
  (ii) tight but inexact fit: report R^2 and residual structure.
  (iii) no low-dimensional relation: action is path-dependent
       beyond final geometry (genuinely historical).
2D gap convention throughout: g(D) = 1 - sum_{y in D} W2(k_y),
W2 = {0:2, 1:-4, 2:2} (the +-1-root convention where pi/4 is pinned).
"""
import math, os, sys, time
import numpy as np
from scipy.optimize import linprog, minimize

T0 = time.time()
def log(*a): print(f"[{time.time()-T0:7.1f}s]", *a, flush=True)
NS = int(sys.argv[1]) if len(sys.argv) > 1 else 16
NPATH = int(sys.argv[2]) if len(sys.argv) > 2 else 25
MODE = os.environ.get("MODE", "A")
rng = np.random.default_rng(53)
W2 = {0: 2, 1: -4, 2: 2}
POP16 = np.array([bin(i).count("1") for i in range(1 << 16)], dtype=np.int8)
def popcount(a): return POP16[a & 0xFFFF] + POP16[(a >> 16) & 0xFFFF]
ARANGE = {n: np.arange(1 << n, dtype=np.int64) for n in range(1, 33)}

def make_law(PHI):
    C = [math.cos(k * PHI) for k in range(256)]
    S = [math.sin(k * PHI) for k in range(256)]
    cache = {}
    def law(gc):
        key = tuple(sorted(gc.items()))
        if key in cache: return cache[key]
        gaps = sorted(gc); mu = np.array([gc[g] for g in gaps], float)
        A = np.vstack([mu * np.array([C[g % 256] for g in gaps]),
                       mu * np.array([S[g % 256] for g in gaps])])
        b = np.array([1.0, 0.0]); K = len(gaps)
        r = linprog(np.zeros(K), A_eq=A, b_eq=b, bounds=[(0, None)] * K, method="highs")
        if not r.success: cache[key] = None; return None
        res = minimize(lambda x: float(np.dot(mu, x * x)), r.x, jac=lambda x: 2 * mu * x,
                       constraints=[{"type": "eq", "fun": lambda x: A @ x - b, "jac": lambda x: A}],
                       bounds=[(0, None)] * K, method="SLSQP", options={"maxiter": 200, "ftol": 1e-12})
        xm = res.x if res.success else r.x
        if float(np.dot(mu, xm * xm)) > 1 + 1e-7: cache[key] = None; return None
        # DETERMINISM FIX (2026-08-16): restart directions from a per-key
        # seeded generator (was: global rng -> member depended on process
        # history; measured tex-observable jitter ~0.004-0.011 across runs,
        # comparable to decision thresholds).  Plus multi-start best-of on
        # the max-entropy stage (single SLSQP start on a nonconvex sphere
        # slice landed in different near-optima).
        import zlib as _zlib
        rk = np.random.default_rng(_zlib.crc32(repr(key).encode()) ^ 0x5A17)
        xhis = []
        for t in range(12):
            c = -np.ones(K) if t == 0 else rk.normal(size=K)
            v = linprog(c, A_eq=A, b_eq=b, bounds=[(0, None)] * K, method="highs")
            if v.success and float(np.dot(mu, v.x * v.x)) >= 1 - 1e-9:
                xhis.append(v.x)
                if len(xhis) >= 4: break
        if not xhis:
            rc = linprog(-np.ones(K), A_eq=A, b_eq=np.zeros(2), bounds=[(0, 1)] * K, method="highs")
            if rc.success and (-rc.fun) > 1e-9:
                dvec = rc.x / np.linalg.norm(rc.x); t = 1.0
                while float(np.dot(mu, (xm + t * dvec) ** 2)) < 1: t *= 2
                xhis = [xm + t * dvec]
            else: cache[key] = None; return None
        def negH(x):
            qq = mu * x * x
            return float(np.sum(qq * np.log(qq + 1e-300)))
        cons = [{"type": "eq", "fun": lambda x: A @ x - b, "jac": lambda x: A},
                {"type": "eq", "fun": lambda x: float(np.dot(mu, x * x)) - 1.0, "jac": lambda x: 2 * mu * x}]
        best = None
        for xhi in xhis:
            f = lambda t: float(np.dot(mu, ((1 - t) * xm + t * xhi) ** 2)) - 1.0
            lo, hi = 0.0, 1.0
            for _ in range(80):
                mid = 0.5 * (lo + hi)
                if f(mid) <= 0: lo = mid
                else: hi = mid
            xfe = np.maximum((1 - lo) * xm + lo * xhi, 0.0)
            if best is None or negH(xfe) < best[0]: best = (negH(xfe), xfe)
            r2 = minimize(negH, xfe, constraints=cons, bounds=[(0, None)] * K, method="SLSQP", options={"maxiter": 500, "ftol": 1e-13})
            if r2.success:
                x2 = np.maximum(r2.x, 0.0)
                if abs(float(np.dot(mu, x2 * x2)) - 1) < 1e-6 and np.max(np.abs(A @ x2 - b)) < 1e-6 and negH(x2) < best[0]:
                    best = (negH(x2), x2)
        x = best[1]; out = {g: x[i] ** 2 for i, g in enumerate(gaps)}
        cache[key] = out; return out
    return law

def downsets_vec(n, below_arr):
    masks = ARANGE[n]; ok = np.ones(masks.shape[0], dtype=bool)
    for x in range(n):
        bx = below_arr[x]
        if bx == 0: continue
        has_x = (masks >> x) & 1 == 1
        ok &= ~(has_x & ((masks & bx) != bx))
    return masks[ok]

def gaps_vec(dlist, n, above_arr):
    g = np.ones(dlist.shape[0], dtype=np.int64)
    warr = np.zeros(n + 2, dtype=np.int64)
    for k, w in W2.items(): warr[k] = w
    for d in range(n):
        sel = ((dlist >> d) & 1) == 1
        if not sel.any(): continue
        k = popcount(dlist[sel] & above_arr[d]).astype(np.int64)
        g[sel] -= warr[np.minimum(k, n + 1)]
    return g

def grow(N, law, record_action=False):
    below = [0]; above = [0]
    stats = []
    action = 0
    for n in range(1, N):
        barr = np.array(below, dtype=np.int64); aarr = np.array(above, dtype=np.int64)
        dlist = downsets_vec(n, barr)
        garr = gaps_vec(dlist, n, aarr)
        gc = {}
        for g in garr.tolist(): gc[g] = gc.get(g, 0) + 1
        lw = law(gc)
        if lw is None: return None, stats, None
        probs = np.array([lw[g] for g in garr.tolist()])
        probs = np.maximum(probs, 0); s = probs.sum()
        if s <= 0: return None, stats, None
        probs = probs / s
        # nondegeneracy stats
        supp = float((probs > 1e-9).sum()) / len(probs)
        H = float(-(probs * np.log(probs + 1e-300)).sum())
        Hmax = math.log(len(probs)) if len(probs) > 1 else 1.0
        stats.append((supp, H / max(Hmax, 1e-9)))
        j = rng.choice(dlist.shape[0], p=probs)
        D = int(dlist[j])
        action += int(garr[j])
        below.append(D); above.append(0)
        m = D
        while m:
            d = (m & -m).bit_length() - 1
            above[d] |= 1 << n; m &= m - 1
    return below, stats, (action if record_action else None)

if MODE == "A":
    log(f"PROBE A: phase nondegeneracy scan, n={NS}, {NPATH} paths/phi")
    PHIS = [0.2, 0.4, 0.6, math.pi/4, 0.9, 1.1, 1.3, math.pi/2,
            1.8, 2.1, math.pi - math.pi/4, 2.6, 2.9]
    log("   phi      feas   supp_frac   norm_entropy")
    for phi in PHIS:
        law = make_law(phi)
        feas = 0; supps = []; ents = []
        for _ in range(NPATH):
            below, stats, _ = grow(NS, law)
            if below is None:
                if stats: supps.extend(s for s, _ in stats); ents.extend(e for _, e in stats)
                continue
            feas += 1
            supps.extend(s for s, _ in stats); ents.extend(e for _, e in stats)
        name = ("pi/4" if abs(phi - math.pi/4) < 1e-9 else
                "pi/2" if abs(phi - math.pi/2) < 1e-9 else
                "3pi/4" if abs(phi - (math.pi - math.pi/4)) < 1e-9 else f"{phi:.2f}")
        log(f"  {name:6s}  {feas:3d}/{NPATH}   {np.mean(supps):.4f}      {np.mean(ents):.4f}")
    log("DONE-A")
else:
    log(f"PROBE B: action telescoping at pi/4, n={NS}, {NPATH} paths")
    law = make_law(math.pi / 4)
    rows = []
    got = 0
    while got < NPATH:
        below, _, action = grow(NS, law, record_action=True)
        if below is None: continue
        N = len(below)
        R = sum(bin(below[x]).count("1") for x in range(N))
        # links
        above = [0] * N
        for x in range(N):
            m = below[x]
            while m:
                y = (m & -m).bit_length() - 1
                above[y] |= 1 << x; m &= m - 1
        L = 0
        for x in range(N):
            m = below[x]
            while m:
                y = (m & -m).bit_length() - 1
                if (below[x] & above[y]) == 0: L += 1
                m &= m - 1
        minima = sum(1 for x in range(N) if below[x] == 0)
        h = [1] * N
        for x in sorted(range(N), key=lambda x: bin(below[x]).count("1")):
            m = below[x]; best = 0
            while m:
                y = (m & -m).bit_length() - 1
                if h[y] > best: best = h[y]
                m &= m - 1
            h[x] = best + 1
        height = max(h)
        # maximal-antichain width (greedy layers = h-level max size)
        from collections import Counter
        width = max(Counter(h).values())
        rows.append((action, N, R, L, minima, height, width))
        got += 1
    arr = np.array(rows, float)
    A = arr[:, 0]; X = arr[:, 1:]
    names = ["n", "R", "L", "minima", "height", "width"]
    # least squares with intercept
    Xa = np.hstack([X, np.ones((len(A), 1))])
    coef, res, rank, _ = np.linalg.lstsq(Xa, A, rcond=None)
    pred = Xa @ coef
    resid = A - pred
    ss = 1 - np.var(resid) / max(np.var(A), 1e-12)
    log("  action A vs invariants: coefficients")
    for nm, c in zip(names + ["const"], coef):
        log(f"    {nm:7s}: {c:+.4f}")
    log(f"  R^2 = {ss:.6f}, max|resid| = {np.max(np.abs(resid)):.4f}, "
        f"A range [{A.min():.0f}, {A.max():.0f}]")
    # try pure integer combos on (n, R, L)
    best = None
    for cn in range(-4, 5):
        for cR in range(-4, 5):
            for cL in range(-4, 5):
                r0 = A - (cn * arr[:, 1] + cR * arr[:, 2] + cL * arr[:, 3])
                if np.all(r0 == r0[0]):
                    best = (cn, cR, cL, r0[0])
    if best:
        log(f"  EXACT: A = {best[0]}*n + {best[1]}*R + {best[2]}*L + ({best[3]:+.0f})  <- TELESCOPING IDENTITY")
    else:
        log("  no exact integer (n,R,L) relation; see lstsq above")
    log("DONE-B")
