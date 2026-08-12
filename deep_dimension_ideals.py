#!/usr/bin/env python3
"""THE SATURATION-VS-COLLAPSE DISCRIMINATOR (registered in
EMERGENT_DIMENSION_4D.md follow-up 1).

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

NS = 60
PHI = 4.0 / math.sqrt(6.0)
NPATH = int(sys.argv[1]) if len(sys.argv) > 1 else 40
IDEAL_CAP = 2_000_000
rng = np.random.default_rng(20260812)

POP16 = np.array([bin(i).count("1") for i in range(1 << 16)],
                 dtype=np.int64)
def popcount(arr):
    return (POP16[arr & 0xFFFF] + POP16[(arr >> 16) & 0xFFFF] +
            POP16[(arr >> 32) & 0xFFFF] + POP16[(arr >> 48) & 0x7FFF])

CGAP = np.array([-1, 9, -16, 8, 0], dtype=np.int64)

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

def sample_path():
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
        gu, inv, mult = np.unique(gaps, return_inverse=True,
                                  return_counts=True)
        x = maxent_gap_law(gu.astype(float), mult)
        if x is None: return recs, counts, (below, above)
        probs = np.maximum(x[inv] ** 2, 0)
        s = probs.sum()
        if s <= 0: return recs, counts, (below, above)
        D = int(ids[rng.choice(len(ids), p=probs / s)])
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

acc = {}; cacc = {}; finals = []
got = 0; kills = 0
t_last = time.time()
while got < NPATH:
    recs, counts, fin = sample_path()
    if recs is None or not recs:
        kills += 1
        if kills > 3 * NPATH: break
        continue
    if max(recs) < NS: kills += 1          # partial path (cap), still used
    for n, obs in recs.items(): acc.setdefault(n, []).append(obs)
    for n, c in counts.items(): cacc.setdefault(n, []).append(c)
    finals.append(fin)
    got += 1
    if time.time() - t_last > 60:
        log(f"  {got}/{NPATH} paths (kills {kills}); ideal count at "
            f"deepest logged n: "
            f"{np.median(cacc[max(cacc)]):.0f} median")
        t_last = time.time()
log(f"paths: {got} complete, {kills} killed (cap/infeasible)")

log("== r(n), d_eff(n), height, minima, ideal counts ==")
prev_r = None
for n in sorted(acc):
    arr = acc[n]
    r = np.mean([a[0] for a in arr]) / (n * (n - 1) / 2)
    rse = np.std([a[0] for a in arr]) / (n * (n - 1) / 2) / \
        math.sqrt(len(arr))
    hgt = np.mean([a[1] for a in arr])
    mnm = np.mean([a[2] for a in arr])
    cmed = np.median(cacc[n]); cmax = np.max(cacc[n])
    log(f"  n={n:3d}: r = {r:.4f}±{rse:.4f}  d_eff = {d_eff(r):.3f}  "
        f"height = {hgt:5.2f}  minima = {mnm:4.2f}  "
        f"ideals med/max = {cmed:.0f}/{cmax:.0f}")
    prev_r = r

ns = sorted(acc)
if len(ns) >= 3:
    rs = {n: np.mean([a[0] for a in acc[n]]) / (n * (n - 1) / 2)
          for n in ns}
    d40 = d_eff(rs[ns[-3]]); d60 = d_eff(rs[ns[-1]])
    log(f"== discriminator: d_eff({ns[-3]}) = {d40:.3f}  "
        f"d_eff({ns[-1]}) = {d60:.3f}  Delta = {d60 - d40:+.3f} ==")
    if d60 - d40 > -0.10:
        log("   reading (a): SATURATION - UV plateau")
    else:
        log("   reading (b): CONTINUED FALL")

# spectral dimension on final causets
log("== spectral dimension (Hasse-graph random walk, final causets) ==")
SIG = 30
P = np.zeros(SIG + 1); cnt = 0
for below, above in finals:
    n = len(below)
    links = hasse_links(n, below, above)
    adj = [[] for _ in range(n)]
    for y, x in links:
        adj[y].append(x); adj[x].append(y)
    deg = np.array([max(len(a), 1) for a in adj])
    for start in range(0, n, 2):
        if not adj[start]: continue
        # exact return probability by transition-matrix powers is
        # O(n^2 SIG); n = 60 so do it exactly per start
        p = np.zeros(n); p[start] = 1.0
        for s in range(1, SIG + 1):
            pn = np.zeros(n)
            for v in range(n):
                if p[v] > 0 and adj[v]:
                    pn[[adj[v]]] += p[v] / len(adj[v])
            p = pn
            P[s] += p[start]
        cnt += 1
P /= max(cnt, 1)
for s in (2, 4, 6, 8, 10, 14, 20, 28):
    if P[s] > 0 and P[s + 2] > 0:
        ds = -2 * (math.log(P[s + 2]) - math.log(P[s])) / \
            (math.log(s + 2) - math.log(s))
        log(f"  sigma = {s:2d}: P_return = {P[s]:.5f}   d_s = {ds:.2f}")
log("DONE")
