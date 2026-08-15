#!/usr/bin/env python3
"""POSTS SURVIVAL MODEL v2 (entropic-reduction instrumentation:
records the downset count D_n, the entropy diagnostic tau_n*D_n --
constant means the full-downset suppression is ENTROPIC, reducing
the posts pair to downset-count asymptotics -- and the COUNT-measure
survival s_count vs the law-weighted s_n): deriving the bounce-suppression exponent
from one-step quantities (registered attack on the persistent
quantum-classical separation; theta-chart showed path counting
carries the post suppression - here we decompose it mechanistically).

A post at time n is an element comparable to all others.  In
sequential growth new elements are maximal, so an element p is
comparable to a later element e iff p lies in e's downset.  Hence:
  - a new TOP is born when the chosen downset is the full set;
  - an existing post SURVIVES a step iff the chosen downset
    contains it.
So E[posts] obeys the survival recursion
  posts(n+1) = posts(n)*s_n + tau_n,
with tau_n = P(full downset chosen at step n) and s_n = mean
per-post survival probability.  Both are ONE-STEP quantities of the
law, measurable to depth 20 for the quantum (pi/4 gap-max-entropy)
and classical (uniform-downset) chains.

REGISTERED READINGS:
  (i)  MODEL CLOSES: the recursion built from measured (tau_n, s_n)
       reproduces the directly measured posts(n) within errors for
       BOTH chains, and the exponent gap is attributed:
       quantum suppression = (smaller tau) x (smaller s), with the
       dominant factor identified.  The persistent separation is
       then DERIVED from one-step law properties - next step is the
       asymptotics of tau_n, s_n under the maxent gap law.
  (ii) MODEL FAILS (correlations matter): survival is not
       one-step-Markov in the causet; report the correlation
       diagnostic (joint survival vs product).
"""
import math, os, sys, time
import numpy as np
from scipy.optimize import linprog, minimize

LAW = os.environ.get("LAW", "maxent")
T0 = time.time()
def log(*a): print(f"[{time.time()-T0:8.1f}s]", *a, flush=True)

NS = int(sys.argv[1]) if len(sys.argv) > 1 else 20
NQ = int(sys.argv[2]) if len(sys.argv) > 2 else 4000
NC = int(sys.argv[3]) if len(sys.argv) > 3 else 12000
PHI = math.pi / 4
rng = np.random.default_rng(11)
W2 = {0: 2, 1: -4, 2: 2}
C8 = [math.cos(k * PHI) for k in range(8)]
S8 = [math.sin(k * PHI) for k in range(8)]
def cg(g): return C8[g % 8]
def sg(g): return S8[g % 8]
POP16 = np.array([bin(i).count("1") for i in range(1 << 16)], dtype=np.int8)
def popcount(a):
    return POP16[a & 0xFFFF] + POP16[(a >> 16) & 0xFFFF]
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
    r = linprog(np.zeros(K), A_eq=A, b_eq=b, bounds=[(0, None)] * K,
                method="highs")
    if not r.success: LAW_CACHE[key] = None; return None
    x0 = r.x
    res = minimize(lambda x: float(np.dot(mu, x * x)), x0,
                   jac=lambda x: 2 * mu * x,
                   constraints=[{"type": "eq", "fun": lambda x: A @ x - b,
                                 "jac": lambda x: A}],
                   bounds=[(0, None)] * K, method="SLSQP",
                   options={"maxiter": 200, "ftol": 1e-12})
    xm = res.x if res.success else x0
    if float(np.dot(mu, xm * xm)) > 1 + 1e-7:
        LAW_CACHE[key] = None; return None
    xhi = None
    for t in range(8):
        c = -np.ones(K) if t == 0 else rng.normal(size=K)
        v = linprog(c, A_eq=A, b_eq=b, bounds=[(0, None)] * K,
                    method="highs")
        if v.success and float(np.dot(mu, v.x * v.x)) >= 1 - 1e-9:
            xhi = v.x; break
    if xhi is None:
        rc = linprog(-np.ones(K), A_eq=A, b_eq=np.zeros(2),
                     bounds=[(0, 1)] * K, method="highs")
        if rc.success and (-rc.fun) > 1e-9:
            d = rc.x / np.linalg.norm(rc.x); t = 1.0
            while float(np.dot(mu, (xm + t * d) ** 2)) < 1: t *= 2
            xhi = xm + t * d
        else:
            LAW_CACHE[key] = None; return None
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
            {"type": "eq", "fun": lambda x: float(np.dot(mu, x * x)) - 1.0,
             "jac": lambda x: 2 * mu * x}]
    best = (negH(xfe), xfe)
    r2 = minimize(negH, xfe, constraints=cons, bounds=[(0, None)] * K,
                  method="SLSQP", options={"maxiter": 200, "ftol": 1e-11})
    if r2.success:
        x2 = np.maximum(r2.x, 0.0)
        if (abs(float(np.dot(mu, x2 * x2)) - 1) < 1e-6 and
                np.max(np.abs(A @ x2 - b)) < 1e-6 and negH(x2) < best[0]):
            best = (negH(x2), x2)
    x = best[1]
    out = {g: x[i] ** 2 for i, g in enumerate(gaps)}
    LAW_CACHE[key] = out
    return out

def downsets_vec(n, below_arr):
    masks = ARANGE[n]
    ok = np.ones(masks.shape[0], dtype=bool)
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

def current_posts(n, below, above):
    full = (1 << n) - 1
    return [x for x in range(n)
            if (below[x] | above[x]) == full & ~(1 << x)]

def sample_path(quantum, acc):
    below = [0]; above = [0]
    for n in range(1, NS):
        barr = np.array(below, dtype=np.int64)
        aarr = np.array(above, dtype=np.int64)
        dlist = downsets_vec(n, barr)
        if quantum:
            garr = gaps_vec(dlist, n, aarr)
            gc = {}
            for g in garr.tolist(): gc[g] = gc.get(g, 0) + 1
            law = maxent_gap_law(gc)
            if law is None: return False
            probs = np.array([law[g] for g in garr.tolist()])
            probs = np.maximum(probs, 0); probs = probs / probs.sum()
        else:
            probs = np.full(dlist.shape[0], 1.0 / dlist.shape[0])
        # one-step statistics BEFORE sampling:
        full = (1 << n) - 1
        # tau: probability mass of the full downset
        tau = float(probs[dlist == full].sum())
        Dn = int(dlist.shape[0])
        posts = current_posts(n, below, above)
        # s: measure-weighted mean survival over current posts
        surv = []
        csurv = []
        for p in posts:
            sel = ((dlist >> p) & 1) == 1
            surv.append(float(probs[sel].sum()))
            csurv.append(float(sel.sum()) / Dn)
        acc.setdefault(n, []).append(
            (tau, np.mean(surv) if surv else np.nan, len(posts),
             Dn, np.mean(csurv) if csurv else np.nan))
        D = int(dlist[rng.choice(dlist.shape[0], p=probs)])
        below.append(D); above.append(0)
        m = D
        while m:
            d = (m & -m).bit_length() - 1
            above[d] |= 1 << n
            m &= m - 1
    return True

def run(quantum, npaths, tag):
    acc = {}
    got = 0
    t_last = time.time()
    while got < npaths:
        if sample_path(quantum, acc): got += 1
        if time.time() - t_last > 120:
            log(f"  [{tag}] {got}/{npaths}")
            t_last = time.time()
    return acc

for tag, quantum, npaths in (("quantum", True, NQ),
                             ("classical", False, NC)):
    log(f"sampling {tag} ({npaths} paths, LAW={LAW})")
    acc = run(quantum, npaths, tag)
    log(f"--- {tag}: one-step quantities and survival model ---")
    model = 0.0
    log("   n   tau_n      s_n      posts_dir  model    D_n     tau*D_n  s_count")
    for n in sorted(acc):
        rows = acc[n]
        tau = float(np.mean([r[0] for r in rows]))
        svals = [r[1] for r in rows if not math.isnan(r[1])]
        s = float(np.mean(svals)) if svals else float("nan")
        direct = float(np.mean([r[2] for r in rows]))
        Dn = float(np.mean([r[3] for r in rows]))
        cs = [r[4] for r in rows if not math.isnan(r[4])]
        scount = float(np.mean(cs)) if cs else float("nan")
        if not math.isnan(s):
            model = model * s + tau
        else:
            model = model + tau
        log(f"  {n:2d}  {tau:.5f}  {s:.5f}  {direct:8.4f} {model:8.4f} "
            f"{Dn:8.1f}  {tau*Dn:.4f}  {scount:.5f}")
    # local exponents of tau and (1-s)
    ns = sorted(acc)[NS//2:]
    taus = [float(np.mean([r[0] for r in acc[n]])) for n in ns]
    ss = [float(np.mean([r[1] for r in acc[n]
                         if not math.isnan(r[1])])) for n in ns]
    lt = np.polyfit(np.log(ns), np.log(np.maximum(taus, 1e-12)), 1)[0]
    ls = np.polyfit(np.log(ns),
                    np.log(np.maximum([1 - s for s in ss], 1e-12)), 1)[0]
    log(f"  tail fits: tau ~ n^{lt:+.2f},  (1-s) ~ n^{ls:+.2f}")
log("DONE")
