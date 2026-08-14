#!/usr/bin/env python3
"""DEEP r(n) FLOW: does the quantized ordering fraction converge to the
classical value, or to a distinct number?  (Registered follow-up of the
KPZ run, which reached n = 12 with gap r_cl - r_q = 0.026 and
narrowing: the sharpest open new-physics question of the 2D program
that is computable without hardware.)

The quantized (pi/4, bi-normalized, gap-max-entropy) growth chain and
the classical uniform-downset chain are sampled to n = NS with the SAME
estimator r(n) = E[#relations] / C(n,2).  The n=3..8 exact-engine trend
gave r_q(8) = 0.414 vs classical 0.508 (the first sharp dynamical
number); the n<=12 sampler gave r_q = 0.4933 vs r_cl = 0.5186 with the
gap shrinking 0.094 -> 0.026.  This run extends both chains to n = 20
and fits the gap.

REGISTERED READINGS (decided by the gap sequence g(n) = r_cl - r_q on
n = 8..20 and its tail behavior):
  (i)   CONVERGENCE: g(n) keeps shrinking; log-log fit of g(n) on the
        last 8 points has slope < -0.5 and extrapolated g(30) < 0.008
        -> the ordering-fraction separation is a FINITE-SIZE effect;
        the asymptotic zero-parameter separation DIES (honest
        negative); the finite-n curve r_q(n) remains the prediction.
  (ii)  PERSISTENCE: g(n) flattens: g(20) > 0.010 AND the last-5-point
        slope of g vs n is consistent with 0 within 2 sigma
        -> candidate PERSISTENT separation; new-physics number
        strengthened; register larger-n / limit-theory follow-up.
  (iii) INCONCLUSIVE: neither pattern (SEs too large or the gap
        sequence non-monotone beyond noise).

Byproducts recorded (no readings attached): posts, minima, links,
height at n up to 20 for both chains - continuation of the anti-KPZ
exponent table.

Method notes: downset enumeration and action-gap evaluation fully
vectorized (numpy mask arithmetic + 16-bit popcount table); the
per-parent gap law is the same penalized max-entropy solver as the
KPZ run (gap-group covariant, no canonicalization).  Infeasible
parents are counted (pi/4 feasibility has never failed through
depth 11; depth 19 is new territory - a nonzero count is itself
reportable).
"""
import math, sys, time
import numpy as np
from scipy.optimize import linprog, minimize

T0 = time.time()
def log(*a): print(f"[{time.time()-T0:8.1f}s]", *a, flush=True)

NS = int(sys.argv[1]) if len(sys.argv) > 1 else 20
NQ = int(sys.argv[2]) if len(sys.argv) > 2 else 2500
NC = int(sys.argv[3]) if len(sys.argv) > 3 else 10000
PHI = math.pi / 4
rng = np.random.default_rng(7)

W2 = {0: 2, 1: -4, 2: 2}
C8 = [math.cos(k * PHI) for k in range(8)]
S8 = [math.sin(k * PHI) for k in range(8)]
def cg(g): return C8[g % 8]
def sg(g): return S8[g % 8]

POP16 = np.array([bin(i).count("1") for i in range(1 << 16)], dtype=np.int8)
def popcount(a):
    return POP16[a & 0xFFFF] + POP16[(a >> 16) & 0xFFFF]

ARANGE = {n: np.arange(1 << n, dtype=np.int64) for n in range(1, NS)}

QP_FAIL = 0
LAW_CACHE = {}

def maxent_gap_law(gapcounts):
    key = tuple(sorted(gapcounts.items()))
    if key in LAW_CACHE:
        return LAW_CACHE[key]
    gaps = sorted(gapcounts)
    mu = np.array([gapcounts[g] for g in gaps], float)
    A = np.vstack([mu * np.array([cg(g) for g in gaps]),
                   mu * np.array([sg(g) for g in gaps])])
    b = np.array([1.0, 0.0])
    K = len(gaps)
    r = linprog(np.zeros(K), A_eq=A, b_eq=b, bounds=[(0, None)] * K,
                method="highs")
    if not r.success:
        LAW_CACHE[key] = None
        return None
    x0 = r.x
    res = minimize(lambda x: float(np.dot(mu, x * x)), x0,
                   jac=lambda x: 2 * mu * x,
                   constraints=[{"type": "eq", "fun": lambda x: A @ x - b,
                                 "jac": lambda x: A}],
                   bounds=[(0, None)] * K, method="SLSQP",
                   options={"maxiter": 200, "ftol": 1e-12})
    xm = res.x if res.success else x0
    if float(np.dot(mu, xm * xm)) > 1 + 1e-7:
        LAW_CACHE[key] = None
        return None
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
            d = rc.x / np.linalg.norm(rc.x)
            t = 1.0
            while float(np.dot(mu, (xm + t * d) ** 2)) < 1: t *= 2
            xhi = xm + t * d
        else:
            LAW_CACHE[key] = None
            return None
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
    """all downward-closed masks over n elements, vectorized."""
    masks = ARANGE[n]
    ok = np.ones(masks.shape[0], dtype=bool)
    for x in range(n):
        bx = below_arr[x]
        if bx == 0: continue
        has_x = (masks >> x) & 1 == 1
        viol = has_x & ((masks & bx) != bx)
        ok &= ~viol
    return masks[ok]

def gaps_vec(dlist, n, above_arr):
    """action gaps for each downset mask in dlist."""
    g = np.ones(dlist.shape[0], dtype=np.int64)
    warr = np.zeros(n + 2, dtype=np.int64)
    for k, w in W2.items():
        if k <= n + 1: warr[k] = w
    for d in range(n):
        sel = ((dlist >> d) & 1) == 1
        if not sel.any(): continue
        k = popcount(dlist[sel] & above_arr[d]).astype(np.int64)
        g[sel] -= warr[np.minimum(k, n + 1)]
    return g

def observables(n, below, above):
    full = (1 << n) - 1
    posts = minima = links = 0
    for x in range(n):
        comp = below[x] | above[x]
        if comp == full & ~(1 << x): posts += 1
        if below[x] == 0: minima += 1
        m = below[x]
        while m:
            y = (m & -m).bit_length() - 1
            if not (below[x] & above[y]): links += 1
            m &= m - 1
    h = [1] * n
    order = sorted(range(n), key=lambda x: bin(below[x]).count("1"))
    for x in order:
        m = below[x]
        best = 0
        while m:
            y = (m & -m).bit_length() - 1
            if h[y] > best: best = h[y]
            m &= m - 1
        h[x] = best + 1
    nrel = sum(bin(below[x]).count("1") for x in range(n))
    return posts, minima, links, max(h), nrel

def sample_path(quantum):
    global QP_FAIL
    below = [0]
    above = [0]
    recs = {}
    for n in range(1, NS):
        barr = np.array(below, dtype=np.int64)
        aarr = np.array(above, dtype=np.int64)
        dlist = downsets_vec(n, barr)
        if quantum:
            garr = gaps_vec(dlist, n, aarr)
            gc = {}
            for g in garr.tolist(): gc[g] = gc.get(g, 0) + 1
            law = maxent_gap_law(gc)
            if law is None:
                QP_FAIL += 1
                return None
            probs = np.array([law[g] for g in garr.tolist()])
            probs = np.maximum(probs, 0)
            probs = probs / probs.sum()
        else:
            probs = np.full(dlist.shape[0], 1.0 / dlist.shape[0])
        D = int(dlist[rng.choice(dlist.shape[0], p=probs)])
        below.append(D)
        above.append(0)
        m = D
        while m:
            d = (m & -m).bit_length() - 1
            above[d] |= 1 << n
            m &= m - 1
        nn = n + 1
        if nn >= 4:
            recs[nn] = observables(nn, below, above)
    return recs

def run(quantum, npaths, tag):
    acc = {n: np.zeros(5) for n in range(4, NS + 1)}
    acc2 = {n: np.zeros(5) for n in range(4, NS + 1)}
    got = 0
    t_last = time.time()
    while got < npaths:
        r = sample_path(quantum)
        if r is None: continue
        for n, obs in r.items():
            v = np.array(obs, float)
            acc[n] += v
            acc2[n] += v * v
        got += 1
        if time.time() - t_last > 120:
            log(f"  [{tag}] {got}/{npaths} paths (QP fails {QP_FAIL}, "
                f"law cache {len(LAW_CACHE)})")
            t_last = time.time()
    out = {}
    for n in range(4, NS + 1):
        mean = acc[n] / got
        se = np.sqrt(np.maximum(acc2[n] / got - mean ** 2, 0) / got)
        out[n] = (mean, se)
    return out, got

log(f"NS={NS} NQ={NQ} NC={NC}")
log("sampling QUANTUM pi/4 gap-max-entropy chain")
Q, gotQ = run(True, NQ, "quantum")
log(f"quantum done ({gotQ} paths, {QP_FAIL} infeasible kills, "
    f"{len(LAW_CACHE)} distinct gap systems)")
log("sampling CLASSICAL uniform chain")
C, gotC = run(False, NC, "classical")
log("classical done")

names = ["posts", "minima", "links", "height", "nrel"]
for tag, T, got in (("quantum", Q, gotQ), ("classical", C, gotC)):
    log(f"--- {tag} ({got} paths) ---")
    for n in range(4, NS + 1):
        mean, se = T[n]
        r = mean[4] / (n * (n - 1) / 2)
        rse = se[4] / (n * (n - 1) / 2)
        log(f"  n={n:2d}: posts {mean[0]:7.4f}±{se[0]:.4f}  "
            f"minima {mean[1]:6.3f}  links {mean[2]:7.3f}  "
            f"height {mean[3]:6.3f}   r = {r:.4f}±{rse:.4f}")

log("--- THE GAP SEQUENCE g(n) = r_cl - r_q ---")
gaps_seq = []
for n in range(4, NS + 1):
    rq = Q[n][0][4] / (n * (n - 1) / 2)
    rc = C[n][0][4] / (n * (n - 1) / 2)
    sq = Q[n][1][4] / (n * (n - 1) / 2)
    sc = C[n][1][4] / (n * (n - 1) / 2)
    g = rc - rq
    sg_ = math.sqrt(sq * sq + sc * sc)
    gaps_seq.append((n, g, sg_))
    log(f"  n={n:2d}: g = {g:+.4f} ± {sg_:.4f}")

tail = [(n, g, s) for n, g, s in gaps_seq if n >= NS - 7 and g > 0]
if len(tail) >= 4:
    ns = np.array([t[0] for t in tail], float)
    gs = np.array([t[1] for t in tail], float)
    A = np.vstack([np.log(ns), np.ones(len(ns))]).T
    coef, *_ = np.linalg.lstsq(A, np.log(gs), rcond=None)
    beta, lnA = coef
    g30 = math.exp(lnA) * 30 ** beta
    log(f"  log-log fit on n={int(ns[0])}..{int(ns[-1])}: "
        f"slope beta = {beta:+.3f}, extrapolated g(30) = {g30:.4f}")
else:
    beta, g30 = float("nan"), float("nan")
    log("  tail fit unavailable (gap non-positive in tail)")

tail5 = gaps_seq[-5:]
ns5 = np.array([t[0] for t in tail5], float)
gs5 = np.array([t[1] for t in tail5], float)
ss5 = np.array([t[2] for t in tail5], float)
w = 1.0 / np.maximum(ss5, 1e-9) ** 2
xm = np.average(ns5, weights=w)
ym = np.average(gs5, weights=w)
slope5 = np.sum(w * (ns5 - xm) * (gs5 - ym)) / np.sum(w * (ns5 - xm) ** 2)
se5 = math.sqrt(1.0 / np.sum(w * (ns5 - xm) ** 2))
log(f"  last-5-point linear slope: {slope5:+.5f} ± {se5:.5f} per element")

gN, sN = gaps_seq[-1][1], gaps_seq[-1][2]
log("--- VERDICT (registered readings) ---")
if not math.isnan(beta) and beta < -0.5 and g30 < 0.008:
    log(f"  reading (i) CONVERGENCE: gap is a finite-size effect "
        f"(beta={beta:.2f}, g30={g30:.4f}); asymptotic separation dies.")
elif gN > 0.010 and abs(slope5) < 2 * se5:
    log(f"  reading (ii) PERSISTENCE: g({NS}) = {gN:.4f} > 0.010 and "
        f"tail slope consistent with 0; candidate persistent separation.")
else:
    log(f"  reading (iii) INCONCLUSIVE: g({NS}) = {gN:.4f}±{sN:.4f}, "
        f"beta = {beta:.2f}, tail slope {slope5:+.5f}±{se5:.5f}.")
log("DONE")
