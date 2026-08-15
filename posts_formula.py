#!/usr/bin/env python3
"""POSTS FORMULA (derivation front 5): the bounce suppression is
entropic (posts_survival v2), so per-post survival s_count = fraction
of downsets containing the post = (#ideals of the causet that include
p) / (#ideals total).  A post p at step n has EVERYTHING below it and
nothing incomparable, so an ideal contains p iff it contains p's
entire down-set (automatic for a post: below(p) = the past cone) OR
sits above; concretely s_count(p) = |{I ideal : p in I}| / |ideals|.

We instrument the RATIO directly and test the factorization
    s_count(p)  ?=  N_below(p) / N_total,
N_below(p) = # ideals containing p (a down-closed count on the
sub-lattice above p's past), against the naive independent model
    s_naive = (n - depth(p)) / n   (fraction of elements p sees).

REGISTERED READINGS:
  (i)  FACTORIZES: s_count matches an ideal-count ratio to ~1% and
       its tail exponent is DERIVED from the ideal-growth exponent
       (both chains): the posts pair reduces to a single
       combinatorial ratio; report the closed form.
  (ii) s_count tracks s_naive (elements-seen) not the ideal ratio:
       survival is geometric, not entropic-combinatorial; revise.
  (iii) neither within errors.
"""
import math, os, sys, time
import numpy as np
from scipy.optimize import linprog, minimize

LAW = os.environ.get("LAW", "maxent")
T0 = time.time()
def log(*a): print(f"[{time.time()-T0:8.1f}s]", *a, flush=True)
NS = int(sys.argv[1]) if len(sys.argv) > 1 else 20
NQ = int(sys.argv[2]) if len(sys.argv) > 2 else 3000
NC = int(sys.argv[3]) if len(sys.argv) > 3 else 8000
PHI = math.pi / 4
rng = np.random.default_rng(23)
W2 = {0: 2, 1: -4, 2: 2}
C8 = [math.cos(k * PHI) for k in range(8)]
S8 = [math.sin(k * PHI) for k in range(8)]
def cg(g): return C8[g % 8]
def sg(g): return S8[g % 8]
POP16 = np.array([bin(i).count("1") for i in range(1 << 16)], dtype=np.int8)
def popcount(a): return POP16[a & 0xFFFF] + POP16[(a >> 16) & 0xFFFF]
ARANGE = {n: np.arange(1 << n, dtype=np.int64) for n in range(1, NS)}
LAW_CACHE = {}

def maxent_gap_law(gapcounts):
    key = tuple(sorted(gapcounts.items()))
    if key in LAW_CACHE: return LAW_CACHE[key]
    gaps = sorted(gapcounts)
    mu = np.array([gapcounts[g] for g in gaps], float)
    A = np.vstack([mu * np.array([cg(g) for g in gaps]),
                   mu * np.array([sg(g) for g in gaps])])
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
        if (abs(float(np.dot(mu, x2 * x2)) - 1) < 1e-6 and np.max(np.abs(A @ x2 - b)) < 1e-6 and negH(x2) < best[0]):
            best = (negH(x2), x2)
    x = best[1]; out = {g: x[i] ** 2 for i, g in enumerate(gaps)}
    LAW_CACHE[key] = out; return out

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

def n_ideals(n, below):
    """count order ideals of the current n-causet via bitmask scan."""
    return int(downsets_vec(n, np.array(below, dtype=np.int64)).shape[0])

def sample_path(quantum, acc):
    below = [0]; above = [0]
    for n in range(1, NS):
        barr = np.array(below, dtype=np.int64); aarr = np.array(above, dtype=np.int64)
        dlist = downsets_vec(n, barr)
        if quantum:
            garr = gaps_vec(dlist, n, aarr); gc = {}
            for g in garr.tolist(): gc[g] = gc.get(g, 0) + 1
            law = maxent_gap_law(gc)
            if law is None: return False
            probs = np.array([law[g] for g in garr.tolist()]); probs = np.maximum(probs, 0); probs = probs / probs.sum()
        else:
            probs = np.full(dlist.shape[0], 1.0 / dlist.shape[0])
        full = (1 << n) - 1
        Ntot = dlist.shape[0]
        posts = [x for x in range(n) if (below[x] | above[x]) == full & ~(1 << x)]
        # per-post: count-fraction survival and ideal-ratio model
        for p in posts:
            sel = ((dlist >> p) & 1) == 1
            s_count = float(sel.sum()) / Ntot        # fraction of ideals containing p
            # N_below: ideals of the sub-poset on elements <= p (its past cone incl p)
            past = below[p] | (1 << p)
            past_elems = [e for e in range(n) if (past >> e) & 1]
            # relabel and count ideals of the induced subposet
            idx = {e: i for i, e in enumerate(past_elems)}
            sub_below = [0] * len(past_elems)
            for e in past_elems:
                m = below[e] & past
                while m:
                    y = (m & -m).bit_length() - 1
                    sub_below[idx[e]] |= 1 << idx[y]
                    m &= m - 1
            Nb = n_ideals_sub(len(past_elems), sub_below)
            depth = bin(below[p]).count("1")
            s_naive = (n - 1 - depth) / max(n - 1, 1)   # fraction of strictly-later slots seen
            acc.setdefault(n, []).append((s_count, Nb, Ntot, s_naive, len(past_elems)))
        D = int(dlist[rng.choice(dlist.shape[0], p=probs)])
        below.append(D); above.append(0)
        m = D
        while m:
            d = (m & -m).bit_length() - 1
            above[d] |= 1 << n; m &= m - 1
    return True

def n_ideals_sub(k, sub_below):
    if k == 0: return 1
    masks = np.arange(1 << k, dtype=np.int64); ok = np.ones(1 << k, dtype=bool)
    for x in range(k):
        bx = sub_below[x]
        if bx == 0: continue
        has_x = (masks >> x) & 1 == 1
        ok &= ~(has_x & ((masks & bx) != bx))
    return int(ok.sum())

def run(quantum, npaths, tag):
    acc = {}; got = 0; t_last = time.time()
    while got < npaths:
        if sample_path(quantum, acc): got += 1
        if time.time() - t_last > 120: log(f"  [{tag}] {got}/{npaths}"); t_last = time.time()
    return acc

for tag, quantum, npaths in (("quantum", True, NQ), ("classical", False, NC)):
    log(f"sampling {tag} ({npaths} paths, LAW={LAW})")
    acc = run(quantum, npaths, tag)
    log(f"--- {tag}: s_count vs ideal-ratio N_below/N_total vs s_naive ---")
    log("   n   s_count   Nb/Ntot   s_naive   #past   verdict")
    for n in sorted(acc):
        rows = acc[n]
        sc = float(np.mean([r[0] for r in rows]))
        ratio = float(np.mean([r[1] / r[2] for r in rows]))
        sn = float(np.mean([r[3] for r in rows]))
        npast = float(np.mean([r[4] for r in rows]))
        d_ratio = abs(sc - ratio); d_naive = abs(sc - sn)
        v = "IDEAL" if d_ratio < d_naive else "naive"
        log(f"  {n:2d}  {sc:.5f}   {ratio:.5f}   {sn:.5f}   {npast:5.1f}   {v}")
log("DONE")
