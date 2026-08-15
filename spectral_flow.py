#!/usr/bin/env python3
"""
[ STATUS (2026-08-15): standalone grow() here uses the 2^n bitmask
scan (caps at n~22); superseded by deep_dimension_ideals.py which
computes d_s at n=80 via the two-limb ideal sampler (result: monotone
fall, no rise). See DIMENSION_FLOW_FINDINGS.md. ]
SPECTRAL DIMENSION FLOW (corrected flagship RG probe).

The ordering-fraction (Myrheim-Meyer) dimension is THINNING-INVARIANT
(random deletion preserves relation density in expectation), so it is
structurally blind to RG flow - a coarse-graining test on it only
re-reads the r(n) growth curve.  The correct scale-dependent probe is
the SPECTRAL DIMENSION d_s(sigma), which genuinely runs with the
diffusion time sigma and is the standard dimensional-reduction /
dimensional-flow diagnostic (CDT, Horava, asymptotic safety).

d_s(sigma) = -2 * d ln P_return / d ln sigma, where P_return(sigma) is
the return probability of a lazy random walk on the UNDIRECTED Hasse
(covering-relation) graph of the grown quantum (pi/4) causet, run for
sigma steps and averaged over start vertices and causets.

Windows:
  UV (small sigma): d_s ~ local dimension ~ 2 (dimensional reduction).
  intermediate sigma: the IR dimension appears HERE, before the
    finite-size cutoff - a rise toward ~4 in this window is the
    emergent-large-scale-4D signal.
  large sigma: P -> 1/N (uniform), d_s -> 0 (finite-size artifact,
    excluded).

REGISTERED READINGS (on d_s over the resolvable window
2 <= sigma <= sigma_max, sigma_max set where P_return > 2/N):
  (i)  RISE: d_s increases by > 0.3 across an intermediate decade and
       trends above the UV value toward 4 -> emergent-4D via spectral
       flow; report the peak d_s and the window.
  (ii) MONOTONE FALL / FLAT ~2: d_s only decreases or sits near the
       UV plateau with no intermediate rise -> no spectral emergence
       of higher dimension at accessible size; emergent-4D route
       closed at n = NBIG.
  (iii) NOISE-LIMITED: window too short (sigma_max < 8) to read a
       slope -> report reachable window; needs larger n (MCMC).
"""
import math, sys, time
import numpy as np
from scipy.optimize import linprog, minimize

T0 = time.time()
def log(*a): print(f"[{time.time()-T0:8.1f}s]", *a, flush=True)
NBIG = int(sys.argv[1]) if len(sys.argv) > 1 else 80
NPATH = int(sys.argv[2]) if len(sys.argv) > 2 else 30
NWALK = int(sys.argv[3]) if len(sys.argv) > 3 else 4000
PHI = math.pi / 4
rng = np.random.default_rng(37)
W2 = {0: 2, 1: -4, 2: 2}
C8 = [math.cos(k * PHI) for k in range(8)]
S8 = [math.sin(k * PHI) for k in range(8)]
def cg(g): return C8[g % 8]
def sg(g): return S8[g % 8]
POP16 = np.array([bin(i).count("1") for i in range(1 << 16)], dtype=np.int8)
def popcount(a): return POP16[a & 0xFFFF] + POP16[(a >> 16) & 0xFFFF]
LIMB = 60; LOWM = (1 << LIMB) - 1
LAW_CACHE = {}

def maxent_gap_law(gapcounts):
    key = tuple(sorted(gapcounts.items()))
    if key in LAW_CACHE: return LAW_CACHE[key]
    gaps = sorted(gapcounts); mu = np.array([gapcounts[g] for g in gaps], float)
    A = np.vstack([mu * np.array([cg(g) for g in gaps]), mu * np.array([sg(g) for g in gaps])])
    b = np.array([1.0, 0.0]); K = len(gaps)
    r = linprog(np.zeros(K), A_eq=A, b_eq=b, bounds=[(0, None)] * K, method="highs")
    if not r.success: LAW_CACHE[key] = None; return None
    x0 = r.x
    res = minimize(lambda x: float(np.dot(mu, x * x)), x0, jac=lambda x: 2 * mu * x,
                   constraints=[{"type": "eq", "fun": lambda x: A @ x - b, "jac": lambda x: A}],
                   bounds=[(0, None)] * K, method="SLSQP", options={"maxiter": 200, "ftol": 1e-12})
    xm = res.x if res.success else x0
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
    LAW_CACHE[key] = out; return out

def downsets_two(n, b0, b1):
    masks = np.arange(1 << n, dtype=np.int64); ok = np.ones(1 << n, dtype=bool)
    for x in range(n):
        bx0 = int(b0[x]); bx1 = int(b1[x])
        if bx0 == 0 and bx1 == 0: continue
        has_x = (masks >> x) & 1 == 1
        # below(x) lives in low bits only for n<=60; use single limb (NBIG<=?)
        ok &= ~(has_x & ((masks & bx0) != bx0))
    return masks[ok]

def grow_links(N):
    """grow to N; return list of covering-relation edges (Hasse)."""
    below = [0]; above = [0]
    for n in range(1, N):
        barr = np.array(below, dtype=np.int64); aarr = np.array(above, dtype=np.int64)
        masks = np.arange(1 << n, dtype=np.int64); ok = np.ones(1 << n, dtype=bool)
        for x in range(n):
            bx = int(barr[x])
            if bx == 0: continue
            has_x = (masks >> x) & 1 == 1
            ok &= ~(has_x & ((masks & bx) != bx))
        dlist = masks[ok]
        g = np.ones(dlist.shape[0], dtype=np.int64)
        warr = np.zeros(n + 2, dtype=np.int64)
        for k, w in W2.items(): warr[k] = w
        for d in range(n):
            sel = ((dlist >> d) & 1) == 1
            if not sel.any(): continue
            k = popcount(dlist[sel] & aarr[d]).astype(np.int64)
            g[sel] -= warr[np.minimum(k, n + 1)]
        gc = {}
        for gg in g.tolist(): gc[gg] = gc.get(gg, 0) + 1
        law = maxent_gap_law(gc)
        if law is None: return None
        probs = np.array([law[gg] for gg in g.tolist()]); probs = np.maximum(probs, 0); probs = probs / probs.sum()
        D = int(dlist[rng.choice(dlist.shape[0], p=probs)])
        below.append(D); above.append(0)
        m = D
        while m:
            d = (m & -m).bit_length() - 1
            above[d] |= 1 << n; m &= m - 1
    # covering relations: y<x with no z strictly between
    adj = [[] for _ in range(N)]
    for x in range(N):
        m = below[x]
        while m:
            y = (m & -m).bit_length() - 1
            if (below[x] & above[y]) == 0:
                adj[x].append(y); adj[y].append(x)
            m &= m - 1
    return adj

def spectral(adj, sigmas):
    """lazy random walk return prob at times in `sigmas`."""
    N = len(adj)
    deg = np.array([len(a) for a in adj], float)
    # transition rows (lazy: stay w.p. 1/2)
    P0 = np.zeros((N, N))
    for x in range(N):
        if deg[x] == 0: P0[x, x] = 1.0; continue
        P0[x, x] = 0.5
        for y in adj[x]:
            P0[x, y] += 0.5 / deg[x]
    ret = {}
    maxs = max(sigmas)
    # evolve delta from each start; track diagonal return
    M = np.eye(N)
    diag_acc = {}
    for s in range(1, maxs + 1):
        M = M @ P0
        if s in sigmas:
            diag_acc[s] = float(np.mean(np.diag(M)))
    return diag_acc

log(f"NBIG={NBIG} NPATH={NPATH}")
sigmas = sorted(set([2, 3, 4, 6, 8, 12, 16, 24, 32, 48, 64]))
acc = {s: [] for s in sigmas}
got = 0
while got < NPATH:
    adj = grow_links(NBIG)
    if adj is None: continue
    d = spectral(adj, sigmas)
    for s in sigmas: acc[s].append(d[s])
    got += 1
    if got % 5 == 0: log(f"  {got}/{NPATH}")

log("== P_return(sigma) and spectral dimension d_s ==")
Ns = NBIG
prev = None
rows = []
for s in sigmas:
    P = float(np.mean(acc[s])); se = float(np.std(acc[s]) / math.sqrt(len(acc[s])))
    rows.append((s, P, se))
log("  sigma   P_return       floor=1/N   d_s(local)")
floor = 1.0 / Ns
window = []
for i, (s, P, se) in enumerate(rows):
    if i == 0:
        log(f"  {s:5d}   {P:.5f}±{se:.5f}   {floor:.5f}   --")
        continue
    s0, P0, _ = rows[i - 1]
    ds = -2 * (math.log(P) - math.log(P0)) / (math.log(s) - math.log(s0))
    resolvable = P > 2 * floor
    flag = "" if resolvable else "  (floor-limited)"
    if resolvable: window.append((s, ds))
    log(f"  {s:5d}   {P:.5f}±{se:.5f}   {floor:.5f}   {ds:.2f}{flag}")

log("== VERDICT (registered readings) ==")
if len(window) < 3:
    log(f"  reading (iii) NOISE/FLOOR-LIMITED: only {len(window)} "
        "resolvable points; needs larger n (MCMC).")
else:
    dss = [d for _, d in window]
    uv = dss[0]; peak = max(dss); last = dss[-1]
    rise = peak - uv
    if rise > 0.3 and peak > uv:
        smax = window[dss.index(peak)][0]
        log(f"  reading (i) RISE: d_s climbs from {uv:.2f} (UV) to "
            f"{peak:.2f} at sigma={smax} - intermediate-scale dimension "
            "GROWTH; emergent-4D via spectral flow ALIVE.")
    else:
        log(f"  reading (ii) NO RISE: d_s = {uv:.2f} (UV) -> {last:.2f} "
            f"(peak {peak:.2f}); no intermediate growth toward 4 at "
            f"n={NBIG}; emergent-4D route closed at accessible size.")
log("DONE")
