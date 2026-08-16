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
        xhi = None
        for t in range(8):
            c = -np.ones(K) if t == 0 else rng.normal(size=K)
            v = linprog(c, A_eq=A, b_eq=b, bounds=[(0, None)] * K, method="highs")
            if v.success and float(np.dot(mu, v.x * v.x)) >= 1 - 1e-9: xhi = v.x; break
        if xhi is None:
            rc = linprog(-np.ones(K), A_eq=A, b_eq=np.zeros(2), bounds=[(0, 1)] * K, method="highs")
            if rc.success and (-rc.fun) > 1e-9:
                dvec = rc.x / np.linalg.norm(rc.x); t = 1.0
                while float(np.dot(mu, (xm + t * dvec) ** 2)) < 1: t *= 2
                xhi = xm + t * dvec
            else: cache[key] = None; return None
        f = lambda t: float(np.dot(mu, ((1 - t) * xm + t * xhi) ** 2)) - 1.0
        lo, hi = 0.0, 1.0
        for _ in range(80):
            mid = 0.5 * (lo + hi)
            if f(mid) <= 0: lo = mid
            else: hi = mid
        xfe = np.maximum((1 - lo) * xm + lo * xhi, 0.0)
        def negH(x):
            qq = mu * x * x
            return float(np.sum(qq * np.log(qq + 1e-300)))
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


log(f"HAMILTONIAN SPECTRUM at pi/4: n={NS}, {NPATH} paths")
law = make_law(math.pi / 4)
from collections import defaultdict
occ = defaultdict(lambda: defaultdict(float))   # n -> level -> weight
cnt = defaultdict(int)
raw = defaultdict(list)                          # n -> chosen gap values
wl = defaultdict(float); wln = defaultdict(float)  # (level,width) joint
meanE = defaultdict(list)
got = 0
while got < NPATH:
    below = [0]; above = [0]
    ok = True
    for n in range(1, NS):
        barr = np.array(below, dtype=np.int64); aarr = np.array(above, dtype=np.int64)
        dlist = downsets_vec(n, barr)
        garr = gaps_vec(dlist, n, aarr)
        gc = {}
        for g in garr.tolist(): gc[g] = gc.get(g, 0) + 1
        lw = law(gc)
        if lw is None: ok = False; break
        probs = np.array([lw[g] for g in garr.tolist()])
        probs = np.maximum(probs, 0); s = probs.sum()
        if s <= 0: ok = False; break
        probs = probs / s
        # Born-weighted level occupation at this step
        for g, p in zip(garr.tolist(), probs.tolist()):
            occ[n][g % 8] += p
        cnt[n] += 1
        meanE[n].append(float(np.dot(probs, garr)) * math.pi / 4)
        # width of each child (# maximal elements of D)
        maxcnt = np.zeros(dlist.shape[0], dtype=np.int64)
        for y in range(n):
            iy = ((dlist >> y) & 1) == 1
            k = popcount(dlist & np.int64(above[y]))
            maxcnt += (iy & (k == 0)).astype(np.int64)
        for g, w, p in zip(garr.tolist(), maxcnt.tolist(), probs.tolist()):
            wl[(g % 8, min(w, 6))] += p; wln[g % 8] += p
        j = rng.choice(dlist.shape[0], p=probs)
        D = int(dlist[j]); raw[n].append(int(garr[j]))
        below.append(D); above.append(0)
        m = D
        while m:
            d = (m & -m).bit_length() - 1
            above[d] |= 1 << n; m &= m - 1
    if ok: got += 1
log("== Born-weighted level occupation O_n(k), k = gap mod 8 ==")
log("   n    k=0     1      2      3      4      5      6      7    <E>/(pi/4)")
for n in sorted(occ):
    if n < 3: continue
    tot = sum(occ[n].values())
    row = "  ".join(f"{occ[n][k]/tot:.3f}" for k in range(8))
    mE = np.mean(meanE[n]) / (math.pi/4)
    log(f"  {n:2d}  {row}   {mE:+.2f}")
log("== width-level joint (Born weight, all steps pooled) ==")
for k in range(8):
    if wln[k] <= 0: continue
    row = "  ".join(f"w{w}:{wl[(k,w)]/wln[k]:.2f}" for w in range(7) if wl[(k,w)] > 0.005*wln[k])
    log(f"  level {k}: share {wln[k]/sum(wln.values()):.3f} | {row}")
log("DONE-H")
