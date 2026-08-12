#!/usr/bin/env python3
"""THE IR FLOW TEST: scale-resolved interval dimension of the
quantized 4D law (registered follow-up 1 of DEEP_DIMENSION_VERDICT).

Does dimension RUN with scale inside the quantum causets - 2 at the
discreteness scale, higher in the IR - completing the CDT-style
running-dimension story from a zero-parameter law?

DESIGN NOTE (correction made before running): the ordering fraction r
is invariant in expectation under random thinning (a kept pair keeps
its relatedness), so the r-chart d_eff CANNOT see RG flow; a naive
"thin then compare d_eff at matched size" test would manufacture a
spurious downward flow (thinned causets inherit the parent's r).  The
correct scale-resolved instrument is the INTERVAL-SCALING dimension:
for each related pair (y, x), proper time L = longest-chain links
y -> x and closed interval volume V; in d-dimensional Minkowski
V ~ c_d L^d, so the local log-slope of V against L is a dimension AT
SCALE L: small L = UV, large L = IR.  Computed by an O(n * #pairs)
all-pairs longest-chain DP.  Calibration: the same estimator on
d = 2, 3, 4 diamond sprinklings at the SAME n (the estimator has
finite-size shape; only curve-vs-curve comparisons count).  Thinning
appears only as a secondary magnifier check (thinned small-L intervals
probe parent large-scale structure) plus the r-invariance sanity test.

Registered readings:
  (i)   IR FLOW UP: the quantum d_int(L) curve rises with L
        significantly beyond the d = 2 sprinkling calibration's shape
        (and crosses toward the d = 3/4 curves at large L): dimension
        runs upward toward the IR - the running-dimension story from
        a parameter-free law.  HEADLINE.
  (ii)  SCALE-INVARIANT: quantum curve parallels the d = 2
        calibration (flat relative shape): the UV phase persists at
        all internal scales; the bare causet is 2D-like everywhere.
  (iii) DOWN: relative slope negative: deepening degeneracy.

Ensembles: quantum phi4 law n = 60 (fresh paths, finals SAVED to
ir_flow_finals.npz for reuse); diamond sprinklings d = 2, 3, 4
(400 each at n = 60); classical uniform growth attempted (cap-guarded,
may be method-limited at n = 60 - reported either way).
"""
import math, sys, time
import numpy as np
from scipy.optimize import linprog, minimize

T0 = time.time()
def log(*a): print(f"[{time.time()-T0:7.1f}s]", *a, flush=True)

NS = 60
PHI = 4.0 / math.sqrt(6.0)
NPATH = int(sys.argv[1]) if len(sys.argv) > 1 else 40
NSPR = 400
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

def sample_path(quantum=True):
    below = [0]; above = [0]
    ids = np.array([0, 1], dtype=np.int64)
    for n in range(1, NS):
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
            if x is None: return None
            probs = np.maximum(x[inv] ** 2, 0)
            s = probs.sum()
            if s <= 0: return None
            probs = probs / s
        else:
            probs = np.full(len(ids), 1.0 / len(ids))
        D = int(ids[rng.choice(len(ids), p=probs)])
        newbit = np.int64(1) << np.int64(n)
        keep = (ids & np.int64(D)) == np.int64(D)
        ids = np.concatenate([ids, ids[keep] | newbit])
        if len(ids) > IDEAL_CAP: return None
        below.append(D); above.append(0)
        m = D
        while m:
            d = (m & -m).bit_length() - 1
            above[d] |= 1 << n
            m &= m - 1
    return below, above

# ---------------- interval machinery ----------------------------------------
def interval_pairs(below, above, n):
    """all related pairs: (L links of longest chain, closed volume).
       O(n * relations) DP in birth order (a linear extension)."""
    LP = [dict() for _ in range(n)]        # LP[x][y] = longest links y->x
    out = []
    for x in range(n):
        bx = below[x]
        m = bx
        while m:
            y = (m & -m).bit_length() - 1
            m &= m - 1
            I = bx & above[y]
            best = 1
            mm = I
            while mm:
                z = (mm & -mm).bit_length() - 1
                mm &= mm - 1
                v = LP[z].get(y)
                if v is not None and v + 1 > best: best = v + 1
            LP[x][y] = best
            out.append((best, bin(I).count("1") + 2))
    return out

def dint_curve(pairs_list, Lmax=12):
    """mean ln V per L; local dimension between successive L values."""
    from collections import defaultdict
    acc = defaultdict(list)
    for L, V in pairs_list:
        if L <= Lmax: acc[L].append(math.log(V))
    Ls = sorted(acc)
    mlnV = {L: float(np.mean(acc[L])) for L in Ls}
    cnt = {L: len(acc[L]) for L in Ls}
    dint = {}
    for i in range(len(Ls) - 1):
        L1, L2 = Ls[i], Ls[i + 1]
        if cnt[L1] >= 30 and cnt[L2] >= 30:
            dint[(L1, L2)] = (mlnV[L2] - mlnV[L1]) / \
                (math.log(L2) - math.log(L1))
    return mlnV, cnt, dint

def sprinkle(d, n):
    pts_t = []; pts_x = []
    need = n
    while need > 0:
        tt = rng.uniform(-1, 1, 4 * need)
        if d > 1:
            xx = rng.normal(size=(4 * need, d - 1))
            rr = np.linalg.norm(xx, axis=1)
            uu = rng.random(4 * need) ** (1 / (d - 1))
            xx = xx / np.maximum(rr[:, None], 1e-30) * uu[:, None]
        else:
            xx = np.zeros((4 * need, 0))
        keep = np.linalg.norm(xx, axis=1) <= 1 - np.abs(tt)
        tk = tt[keep][:need]; xk = xx[keep][:need]
        pts_t.append(tk); pts_x.append(xk)
        need -= len(tk)
    tt = np.concatenate(pts_t); xx = np.vstack(pts_x)
    order = np.argsort(tt)
    tt = tt[order]; xx = xx[order]
    below = [0] * n; above = [0] * n
    for i in range(n):
        for j in range(i + 1, n):
            if tt[j] - tt[i] > np.linalg.norm(xx[j] - xx[i]):
                below[j] |= 1 << i
                above[i] |= 1 << j
    return below, above

# ---------------- run: quantum ensemble -------------------------------------
log(f"QUANTUM ensemble: {NPATH} paths to n = {NS}")
finals = []
got = 0; kills = 0
t_last = time.time()
while got < NPATH:
    fin = sample_path(True)
    if fin is None:
        kills += 1
        if kills > 3 * NPATH: break
        continue
    finals.append(fin); got += 1
    if time.time() - t_last > 120:
        log(f"  {got}/{NPATH}"); t_last = time.time()
log(f"quantum done: {got} paths, {kills} kills")
np.savez("ir_flow_finals.npz",
         below=np.array([f[0] for f in finals], dtype=np.int64),
         above=np.array([f[1] for f in finals], dtype=np.int64))

pairsQ = []
for below, above in finals:
    pairsQ += interval_pairs(below, above, NS)
log(f"quantum interval pairs: {len(pairsQ)}")

# ---------------- sprinkling calibrations -----------------------------------
pairsS = {}
for d in (2, 3, 4):
    ps = []
    for _ in range(NSPR):
        below, above = sprinkle(d, NS)
        ps += interval_pairs(below, above, NS)
    pairsS[d] = ps
    log(f"sprinkling d={d}: {len(ps)} pairs")

# ---------------- classical uniform (cap-guarded attempt) -------------------
pairsC = []
cgot = 0; ckills = 0
while cgot < 12 and ckills < 24:
    fin = sample_path(False)
    if fin is None: ckills += 1; continue
    pairsC += interval_pairs(fin[0], fin[1], NS)
    cgot += 1
log(f"classical uniform: {cgot} paths ({ckills} cap-kills)")

# ---------------- curves and verdict ----------------------------------------
log("== d_int(L) curves (local log-slope of V against L) ==")
curves = {}
for tag, ps in [("quantum", pairsQ), ("d2-sprink", pairsS[2]),
                ("d3-sprink", pairsS[3]), ("d4-sprink", pairsS[4])] + \
               ([("uniform", pairsC)] if pairsC else []):
    mlnV, cnt, dint = dint_curve(ps)
    curves[tag] = dint
    row = "  ".join(f"L{a}-{b}:{v:.2f}" for (a, b), v in sorted(dint.items()))
    log(f"  {tag:10s} {row}")

log("== relative flow: quantum minus d2-calibration ==")
flow = []
for key in sorted(curves["quantum"]):
    if key in curves["d2-sprink"]:
        dq = curves["quantum"][key]; d2 = curves["d2-sprink"][key]
        flow.append((key, dq - d2))
        log(f"  L{key[0]}-{key[1]}: quantum {dq:.2f}  d2 {d2:.2f}  "
            f"excess {dq - d2:+.2f}")
if len(flow) >= 3:
    early = np.mean([f[1] for f in flow[:2]])
    late = np.mean([f[1] for f in flow[-2:]])
    log(f"  UV excess (first 2 windows) = {early:+.2f}; "
        f"IR excess (last 2) = {late:+.2f}; TREND = {late - early:+.2f}")
    if late - early > 0.3:
        log("  reading (i): IR FLOW UP")
    elif late - early < -0.3:
        log("  reading (iii): FLOW DOWN")
    else:
        log("  reading (ii): SCALE-INVARIANT (within calibration)")

# ---------------- thinning secondary checks ---------------------------------
log("== thinning checks ==")
rs_parent = []; rs_thin = []
pairsT = []
for below, above in finals:
    rs_parent.append(sum(bin(b).count("1") for b in below) /
                     (NS * (NS - 1) / 2))
    for _ in range(4):
        keep = sorted(rng.choice(NS, size=20, replace=False))
        idx = {v: i for i, v in enumerate(keep)}
        nb = [0] * 20; na = [0] * 20
        for i, v in enumerate(keep):
            for j, w in enumerate(keep):
                if (below[w] >> v) & 1:
                    nb[j] |= 1 << i; na[i] |= 1 << j
        rs_thin.append(sum(bin(b).count("1") for b in nb) / (20 * 19 / 2))
        pairsT += interval_pairs(nb, na, 20)
log(f"  r-invariance sanity: parent r = {np.mean(rs_parent):.4f}, "
    f"thinned-to-20 r = {np.mean(rs_thin):.4f} (must match)")
_, _, dintT = dint_curve(pairsT, Lmax=8)
row = "  ".join(f"L{a}-{b}:{v:.2f}" for (a, b), v in sorted(dintT.items()))
log(f"  thinned-magnifier d_int: {row}")
log("  (thinned small-L windows probe parent ~3x-larger scales; compare")
log("   with the quantum bare small-L values above)")
log("DONE")
