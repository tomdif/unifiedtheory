#!/usr/bin/env python3
"""
[ STATUS (2026-08-15): DIAGNOSED VOID. The Myrheim-Meyer /
ordering-fraction dimension is THINNING-INVARIANT under random deletion,
so this coarse-graining test cannot see RG flow - it only re-reads the
r(n) growth curve. See DIMENSION_FLOW_FINDINGS.md. Kept for the record. ]
DIMENSIONAL RG FLOW (registered flagship follow-up after the n=80
bare-dimension NEGATIVE): does the COARSE-GRAINED dimension flow UP
toward 4 over the UV~1.7 plateau?

Method (Sorkin-standard random-deletion coarse-graining): grow a
quantum (pi/4 gap-max-entropy) causet to size N; coarse-grain by
keeping each element iid with probability q, inducing the sub-causal-
order; measure the Myrheim-Meyer / ordering-fraction dimension
d_MM(r) of the coarse-grained set (r = #relations / C(m,2), same
estimator as the bare run).  Compare d_MM at coarse-grained size m
against the NATIVE d_MM of a freshly-grown causet of the same size m.

  d_MM(coarse) > d_MM(native @ same m)  ==>  the large-scale
  (coarse-grained) dimension is HIGHER than the bare dimension at
  that size: DIMENSION FLOWS UP under coarse-graining - the
  emergent-large-scale-4D signal the bare run could not see.
  d_MM(coarse) ~ d_MM(native)          ==>  scale-invariant: the
  ~1.7 plateau is a genuine fixed dimension, no IR growth.
  d_MM(coarse) < d_MM(native)          ==>  flows further down.

d_MM inversion: the Myrheim-Meyer relation for a d-dim causal-set
interval is  r = ordering fraction, and d solves
  r = 1.5 * Gamma(d/2+1) Gamma(d) / (Gamma(3d/2) ... )  -- we instead
use the SAME empirical diamond-baseline calibration as the bare run
(d_eff = 2 + ln(r/0.5)/ln(0.44)) so the two dimensions are directly
comparable on one scale.  (This calibration is a chart; only the
SIGN of d_coarse - d_native is claimed, which is calibration-free
since both use the same monotone r->d map.)

REGISTERED READINGS (on the sign of d_coarse(m) - d_native(m),
averaged over keep-fractions giving coarse size ~ m, for several m):
  (i)  UP: sign > 0 by > 2 sigma at the largest m for a range of q
       -> dimensional RG flow toward larger d; emergent-4D route
       ALIVE; report the flow curve and extrapolated IR dimension.
  (ii) FLAT: |sign| < 2 sigma -> scale-invariant plateau; the ~1.7
       dimension is a true fixed point; emergent-4D route CLOSED.
  (iii) DOWN: sign < 0 -> hyper-ordering deepens with coarse-graining.
Because r is thinning-INVARIANT in expectation for a RANDOM subset
(each kept pair keeps its relation), the naive expectation is (ii);
a deviation either way is the physics.  We therefore ALSO report the
thinning-invariance control explicitly (r_coarse vs r_native at
matched m) - the whole test is whether the quantum causet's
r departs from thinning-invariance, i.e. whether its relation
structure is self-similar or scale-dependent.
"""
import math, sys, time
import numpy as np
from scipy.optimize import linprog, minimize

T0 = time.time()
def log(*a): print(f"[{time.time()-T0:8.1f}s]", *a, flush=True)
NBIG = int(sys.argv[1]) if len(sys.argv) > 1 else 60
NPATH = int(sys.argv[2]) if len(sys.argv) > 2 else 200
PHI = math.pi / 4
rng = np.random.default_rng(31)
W2 = {0: 2, 1: -4, 2: 2}
C8 = [math.cos(k * PHI) for k in range(8)]
S8 = [math.sin(k * PHI) for k in range(8)]
def cg(g): return C8[g % 8]
def sg(g): return S8[g % 8]
POP16 = np.array([bin(i).count("1") for i in range(1 << 16)], dtype=np.int8)
def popcount(a): return POP16[a & 0xFFFF] + POP16[(a >> 16) & 0xFFFF]
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

def downsets_vec(n, below_arr):
    masks = np.arange(1 << n, dtype=np.int64); ok = np.ones(1 << n, dtype=bool)
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

def grow(N):
    """grow one quantum causet to size N; return below[] (int masks)."""
    below = [0]; above = [0]
    for n in range(1, N):
        barr = np.array(below, dtype=np.int64); aarr = np.array(above, dtype=np.int64)
        dlist = downsets_vec(n, barr)
        garr = gaps_vec(dlist, n, aarr); gc = {}
        for g in garr.tolist(): gc[g] = gc.get(g, 0) + 1
        law = maxent_gap_law(gc)
        if law is None: return None
        probs = np.array([law[g] for g in garr.tolist()]); probs = np.maximum(probs, 0); probs = probs / probs.sum()
        D = int(dlist[rng.choice(dlist.shape[0], p=probs)])
        below.append(D); above.append(0)
        m = D
        while m:
            d = (m & -m).bit_length() - 1
            above[d] |= 1 << n; m &= m - 1
    return below

def r_of_subset(below, keep):
    """ordering fraction of the sub-causal-order induced on `keep`
    (a boolean array over 0..N-1). uses transitive below-masks."""
    idxs = np.nonzero(keep)[0]
    m = len(idxs)
    if m < 2: return None
    keepmask = 0
    for i in idxs: keepmask |= (1 << int(i))
    nrel = 0
    for i in idxs:
        nrel += bin(below[i] & keepmask).count("1")
    return nrel / (m * (m - 1) / 2), m

def d_eff(r):
    if r is None or r <= 0: return float("nan")
    return 2 + math.log(r / 0.5) / math.log(0.44)

# keep-fractions -> coarse sizes; native reference grown to those sizes
QS = [1.0, 0.75, 0.5, 0.35, 0.25]
log(f"NBIG={NBIG} NPATH={NPATH}; growing quantum causets + coarse-graining")

# coarse-grained: grow to NBIG, delete
coarse = {q: [] for q in QS}
got = 0
while got < NPATH:
    below = grow(NBIG)
    if below is None: continue
    for q in QS:
        if q == 1.0:
            r, m = r_of_subset(below, np.ones(NBIG, dtype=bool))
            coarse[q].append((r, m))
        else:
            keep = rng.random(NBIG) < q
            res = r_of_subset(below, keep)
            if res is not None: coarse[q].append(res)
    got += 1
    if got % 50 == 0: log(f"  coarse {got}/{NPATH}")

# native reference: grow directly to each target size (median coarse size)
target_sizes = sorted(set(int(round(np.median([m for _, m in coarse[q]]))) for q in QS))
log(f"native reference sizes: {target_sizes}")
native = {s: [] for s in target_sizes}
for s in target_sizes:
    cnt = 0
    while cnt < max(NPATH // 2, 60):
        below = grow(s)
        if below is None: continue
        r, m = r_of_subset(below, np.ones(s, dtype=bool))
        native[s].append(r); cnt += 1
    log(f"  native n={s}: {len(native[s])} causets")

log("== COARSE-GRAINED vs NATIVE (matched size) ==")
log("  q     m_coarse   r_coarse    d_coarse | r_native  d_native | d_coarse-d_native")
results = []
for q in QS:
    rs = np.array([r for r, _ in coarse[q]]); ms = np.array([m for _, m in coarse[q]])
    m_c = float(np.mean(ms)); r_c = float(np.mean(rs)); se_c = float(np.std(rs) / math.sqrt(len(rs)))
    d_c = d_eff(r_c)
    # nearest native size
    s = min(target_sizes, key=lambda t: abs(t - m_c))
    r_n = float(np.mean(native[s])); se_n = float(np.std(native[s]) / math.sqrt(len(native[s])))
    d_n = d_eff(r_n)
    # dd sign via r (monotone map): sign(d_c-d_n)=sign(r_c-r_n)
    dd = d_c - d_n
    sedr = math.sqrt(se_c ** 2 + se_n ** 2)
    # propagate to d via local slope of d_eff(r)=2+ln(r/.5)/ln(.44): dd/dr = 1/(r ln.44)
    slope = 1.0 / (r_c * math.log(0.44))
    sedd = abs(slope) * sedr
    results.append((q, m_c, r_c, r_n, dd, sedd))
    log(f"  {q:.2f}  {m_c:7.1f}   {r_c:.4f}     {d_c:.3f}  | {r_n:.4f}   {d_n:.3f}  | "
        f"{dd:+.3f} ± {sedd:.3f} ({dd/sedd:+.1f}σ)")

log("== VERDICT (registered readings) ==")
# use the most-coarse-grained points (q<=0.5) as the RG signal
sig = [(q, dd, sedd) for q, _, _, _, dd, sedd in results if q <= 0.5]
best = max(sig, key=lambda t: t[1] / t[2]) if sig else None
worst = min(sig, key=lambda t: t[1] / t[2]) if sig else None
up = best and best[1] > 2 * best[2]
down = worst and worst[1] < -2 * worst[2]
if up:
    log(f"  reading (i) UP: coarse-grained dimension EXCEEDS native by "
        f"{best[1]:+.3f} ({best[1]/best[2]:+.1f}σ) at q={best[0]} - "
        "dimensional RG flow toward larger d; emergent-4D route ALIVE.")
elif down:
    log(f"  reading (iii) DOWN: coarse dimension below native "
        f"({worst[1]:+.3f}, {worst[1]/worst[2]:+.1f}σ) - hyper-ordering "
        "deepens under coarse-graining.")
else:
    log(f"  reading (ii) FLAT: |d_coarse - d_native| < 2σ at all coarse "
        "scales - scale-invariant plateau; the ~1.7 dimension is a true "
        "fixed point; emergent-4D route CLOSED (bare AND coarse).")
log("DONE")
