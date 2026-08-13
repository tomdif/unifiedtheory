#!/usr/bin/env python3
"""ARROW-OF-TIME + TRACY-WIDOM SAMPLER (directions 1 and 6).

2D pi/4 gap-max-entropy law via the ideal-lattice engine.  Records per
path: final height (TW test: skew vs TW-GUE 0.2241 vs Gaussian 0) and
the ideal-count trajectory (S_ideal = ln #ideals = causal state-space
entropy).  Also runs the CLASSICAL uniform chain for the entropy
comparison, and d=2 sprinkling ideal counts as manifold baseline.
Registered readings: (arrow) quantum S_ideal/n sits BELOW classical
and sprinkling -> the quantum law minimizes causal state-space
entropy (arrow-of-time extremum claim); (TW) height skewness within
2 sigma of 0.2241 and far from 0 -> KPZ/TW class contact (RH-adjacent);
skew ~ 0 -> quantization broke the KPZ class.

Method: EXACT ideal-lattice sampling.  The 2^n wall of the previous
sampler was bitmask scanning; the number of actual order ideals of the
quantum law's causets is far smaller (relation-dense => narrow => few
antichains) and updates INCREMENTALLY: when a birth with downset D
occurs, ideals' = ideals + [I | newbit for I in ideals if I & D == D].
One vectorized pass per step, cost ~ #ideals, so depth is limited by
the measured ideal count, not 2^n.  We log that count (it is itself a
geometry observable) and abort a path above IDEAL_CAP.

Observables:
  - r(n), height, minima at n = 5,10,...,60;
  - d_eff(n) = 2 + ln(r/0.5)/ln(0.44), calibrated on the measured
    log-linear diamond baselines (0.501, 0.229, 0.099, 0.043 for
    d = 2..5; constant ratio 0.44);
  - spectral dimension at n = 60: random-walk return probability on
    the undirected Hasse (link) graph, d_s(sigma) = -2 dlnP/dlnsigma;
  - ideal-count trajectory.

Registered readings:
  (a) SATURATION: d_eff(60) - d_eff(40) > -0.10 and r-increments
      falling toward 0: UV plateau at d ~ 2 from a parameter-free law
      (the dimensional-reduction narrative; headline).  A subsequent
      UPTURN (d_eff rising by > 0.1) would be the emergent-growth
      signal - report separately if seen.
  (b) CONTINUED FALL: d_eff declines roughly linearly through the
      range: degenerate hyper-ordering at all scales.
  (c) METHOD-LIMITED: ideal counts exceed the cap before n = 60 on
      most paths: report the reachable depth; MCMC fallback next.
"""
import math, sys, time
import numpy as np
from scipy.optimize import linprog, minimize

T0 = time.time()
def log(*a): print(f"[{time.time()-T0:7.1f}s]", *a, flush=True)

NS = 28
PHI = math.pi / 4
NPATH = int(sys.argv[1]) if len(sys.argv) > 1 else 40
IDEAL_CAP = 2_000_000
rng = np.random.default_rng(20260812)

POP16 = np.array([bin(i).count("1") for i in range(1 << 16)],
                 dtype=np.int64)
def popcount(arr):
    return (POP16[arr & 0xFFFF] + POP16[(arr >> 16) & 0xFFFF] +
            POP16[(arr >> 32) & 0xFFFF] + POP16[(arr >> 48) & 0x7FFF])

CGAP = np.array([-2, 4, -2, 0, 0], dtype=np.int64)  # 2D: -W2(k)

def maxent_gap_law(gaps_unique, mults):
    mu = mults.astype(float)
    A = np.vstack([mu * np.cos(gaps_unique * PHI),
                   mu * np.sin(gaps_unique * PHI)])
    b = np.array([1.0, 0.0])
    K = len(gaps_unique)
    r = linprog(np.zeros(K), A_eq=A, b_eq=b, bounds=[(0, None)] * K,
                method="highs")
    if not r.success: return None
    res = minimize(lambda x: float(np.dot(mu, x * x)), r.x,
                   jac=lambda x: 2 * mu * x,
                   constraints=[{"type": "eq", "fun": lambda x: A @ x - b,
                                 "jac": lambda x: A}],
                   bounds=[(0, None)] * K, method="SLSQP",
                   options={"maxiter": 200, "ftol": 1e-12})
    xm = res.x if res.success else r.x
    if float(np.dot(mu, xm * xm)) > 1 + 1e-7: return None
    xhi = None
    for tr in range(8):
        c = -np.ones(K) if tr == 0 else rng.normal(size=K)
        v = linprog(c, A_eq=A, b_eq=b, bounds=[(0, None)] * K,
                    method="highs")
        if v.success and float(np.dot(mu, v.x * v.x)) >= 1 - 1e-9:
            xhi = v.x; break
    if xhi is None:
        rc = linprog(-np.ones(K), A_eq=A, b_eq=np.zeros(2),
                     bounds=[(0, 1)] * K, method="highs")
        if rc.success and (-rc.fun) > 1e-9:
            d = rc.x / np.linalg.norm(rc.x)
            tt = 1.0
            while float(np.dot(mu, (xm + tt * d) ** 2)) < 1: tt *= 2
            xhi = xm + tt * d
        else:
            return None
    f = lambda tt: float(np.dot(mu, ((1 - tt) * xm + tt * xhi) ** 2)) - 1.0
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
    return best[1]

def observables(n, below, above):
    minima = sum(1 for x in range(n) if below[x] == 0)
    nrel = sum(bin(below[x]).count("1") for x in range(n))
    h = [1] * n
    order = sorted(range(n), key=lambda x: bin(below[x]).count("1"))
    for x in order:
        m = below[x]; best = 0
        while m:
            y = (m & -m).bit_length() - 1
            if h[y] > best: best = h[y]
            m &= m - 1
        h[x] = best + 1
    return nrel, max(h), minima

def hasse_links(n, below, above):
    links = []
    for x in range(n):
        m = below[x]
        while m:
            y = (m & -m).bit_length() - 1
            if (below[x] & above[y]) == 0: links.append((y, x))
            m &= m - 1
    return links

def sample_path(quantum=True):
    below = [0]; above = [0]
    ids = np.array([0, 1], dtype=np.int64)      # ideals of the 1-causet
    recs = {}; counts = {}
    for n in range(1, NS):
        # gaps for every candidate downset (ideal)
        gaps = np.ones(len(ids), dtype=np.int64)
        for y in range(n):
            iy = ((ids >> y) & 1) == 1
            if not iy.any(): continue
            k = popcount(ids & np.int64(above[y]))
            k = np.minimum(k, 4)
            gaps += np.where(iy, CGAP[k], 0)
        if quantum:
            gu, inv, mult = np.unique(gaps, return_inverse=True,
                                      return_counts=True)
            x = maxent_gap_law(gu.astype(float), mult)
            if x is None: return recs, counts, (below, above)
            probs = np.maximum(x[inv] ** 2, 0)
            s = probs.sum()
            if s <= 0: return recs, counts, (below, above)
        else:
            probs = np.full(len(ids), 1.0 / len(ids))
            s = 1.0
        D = int(ids[rng.choice(len(ids), p=probs / s if quantum else probs)])
        newbit = np.int64(1) << np.int64(n)
        keep = (ids & np.int64(D)) == np.int64(D)
        ids = np.concatenate([ids, ids[keep] | newbit])
        if len(ids) > IDEAL_CAP: return recs, counts, (below, above)
        below.append(D); above.append(0)
        m = D
        while m:
            d = (m & -m).bit_length() - 1
            above[d] |= 1 << n
            m &= m - 1
        nn = n + 1
        counts[nn] = len(ids)
        if nn % 5 == 0 or nn == NS:
            recs[nn] = observables(nn, below, above)
    return recs, counts, (below, above)

def d_eff(r):
    if r <= 0: return float("nan")
    return 2 + math.log(r / 0.5) / math.log(0.44)


def run(quantum, npaths, tag):
    hts, cnts = [], {}
    got = 0; t_last = time.time()
    while got < npaths:
        recs, counts, fin = sample_path(quantum)
        if not recs or max(recs) < NS: continue
        hts.append(recs[NS][1])
        for n, c in counts.items(): cnts.setdefault(n, []).append(c)
        got += 1
        if time.time() - t_last > 120:
            log(f"  [{tag}] {got}/{npaths}"); t_last = time.time()
    return hts, cnts

NQ = int(sys.argv[1]) if len(sys.argv) > 1 else 1200
NC = int(sys.argv[2]) if len(sys.argv) > 2 else 300
log(f"QUANTUM 2D pi/4 law: {NQ} paths to n={NS}")
htsQ, cntsQ = run(True, NQ, "Q")
log(f"CLASSICAL uniform: {NC} paths")
htsC, cntsC = run(False, NC, "C")

log("== (6) Tracy-Widom test: height distribution at n=%d ==" % NS)
h = np.array(htsQ, float)
m, sd = h.mean(), h.std()
sk = float(((h - m) ** 3).mean() / sd ** 3)
ku = float(((h - m) ** 4).mean() / sd ** 4 - 3)
se_sk = math.sqrt(6.0 / len(h))
log(f"  N={len(h)}  mean={m:.3f}  sd={sd:.3f}  skew={sk:+.4f} "
    f"(SE {se_sk:.3f})  ex-kurt={ku:+.3f}")
log(f"  TW-GUE: skew 0.2241, ex-kurt 0.0934;  Gaussian: 0, 0")
log(f"  z(skew vs TW) = {(sk-0.2241)/se_sk:+.2f}   "
    f"z(skew vs 0) = {sk/se_sk:+.2f}")
hC = np.array(htsC, float)
skC = float(((hC - hC.mean()) ** 3).mean() / hC.std() ** 3)
log(f"  classical baseline: N={len(hC)} mean={hC.mean():.3f} "
    f"skew={skC:+.4f} (SE {math.sqrt(6/len(hC)):.3f})")

log("== (1) ideal-count entropy S/n = ln(#ideals)/n ==")
log("   n    quantum        classical")
for n in range(6, NS + 1, 2):
    q = np.log(cntsQ.get(n, [1])); c = np.log(cntsC.get(n, [1]))
    log(f"  {n:3d}  {np.mean(q)/n:.4f}+-{np.std(q)/n:.4f}   "
        f"{np.mean(c)/n:.4f}+-{np.std(c)/n:.4f}")

log("d=2 sprinkling ideal counts (200 samples)")
def sprinkle_ideals(n):
    tt = rng.uniform(-1, 1, 4 * n); need_x = rng.uniform(-1, 1, 4 * n)
    keep = np.abs(need_x) <= 1 - np.abs(tt)
    t2, x2 = tt[keep][:n], need_x[keep][:n]
    o = np.argsort(t2); t2, x2 = t2[o], x2[o]
    below = [0] * n
    for i in range(n):
        for j in range(i):
            if t2[i] - t2[j] > abs(x2[i] - x2[j]):
                below[i] |= (1 << j) | below[j]
    ids = np.array([0], dtype=np.int64)
    for i in range(n):
        bi = np.int64(below[i])
        keep2 = (ids & bi) == bi
        ids = np.concatenate([ids, ids[keep2] | (np.int64(1) << np.int64(i))])
        if len(ids) > 3_000_000: return None
    return len(ids)
sc = []
for _ in range(200):
    v = sprinkle_ideals(NS)
    if v: sc.append(math.log(v))
log(f"  n={NS}: sprinkling S/n = {np.mean(sc)/NS:.4f}+-{np.std(sc)/NS:.4f}"
    f"  ({len(sc)} ok)")
log("DONE")
