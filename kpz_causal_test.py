#!/usr/bin/env python3
"""THE CAUSAL-SET KPZ TEST (registered follow-up of
STRUCTURAL_4_SQRT6_NOTE.md section 5.4).

If the quantized (pi/4, bi-normalized) growth measure defines a random
geometry in a gamma-LQG class, then classical vs quantum scaling
exponents of order observables must be related by the KPZ quadratic
    x = (gamma^2/4) Delta^2 + (1 - gamma^2/4) Delta,
with the SAME gamma as the mating-of-trees chart extracts from the
ordering fraction (gamma^2_mating = (4/pi) arccos(-sin(pi(r - 1/2)))).
Two independent gamma measurements agreeing = class assignment.

Dictionary (Duplantier-Sheffield count convention): a feature whose
expected count at size n scales ~ n^a has weight 1 - a; classical
weight x = 1 - a_cl, quantum weight Delta = 1 - a_q; KPZ endpoints
x = 0 and x = 1 are gamma-INSENSITIVE (Delta = x), giving null
controls.

Observables (all order-invariants, computed per sampled causet):
  posts   (elements comparable to all others)  classical ~ n^-1, x ~ 2:
          PRIMARY gamma-sensitive probe; at gamma^2 = 1.65 (mating,
          n=8) KPZ predicts delta-a = x - Delta = +0.40; at gamma^2 = 2
          (c=-2 drift target) +0.44.
  height  (longest chain)  classical ~ n^{1/2}, x = 1/2: secondary
          probe, predicted delta-a = -0.10; CAVEAT: extremal object,
          violates the KPZ independence hypothesis - reported with
          that flag.
  minima  x ~ 1 null control: KPZ forces Delta = 1 at every gamma ->
          quantum and classical slopes must MATCH.
  links   (covering pairs) a_cl ~ 1 (x ~ 0) null control: slopes must
          match.
  nrel    -> ordering fraction r(n): extends the mating trend to n=12
          (the 2/3-vs-1/2 discriminator gets four new points).

Method: direct sampling of both Markov chains to n = 12.  KEY
SIMPLIFICATION: the double-conservation constraints at a parent see
only the multiset of child ACTION GAPS, so the max-entropy law over
gap-groups is covariant and requires NO canonicalization - each step
enumerates downsets, computes gaps incrementally
(dS = 1 - sum_{d in D} W2[#{z in D : d < z}]), groups by gap, solves
the (coherent + Born) system by penalized max-entropy, and samples a
labeled child with probability rho_g^2.  (This "gap-max-entropy" law
is a member of the registered selection band; its r(8) is compared to
the class-max-entropy value 0.4136 as a consistency check.)  The
sampler also extends the pi/4 feasibility test to depth-11 parents on
all visited states (infeasible visits are counted and reported).

Registered readings:
  (i)   KPZ-CONSISTENT: null slopes match (|delta-a| < 0.05); posts and
        height give a common gamma^2 within +-0.3, agreeing with
        gamma^2_mating(r(12)) within +-0.3 -> class assignment: the
        quantized causal measure IS a gamma-LQG geometry (structural).
  (ii)  KPZ-INCONSISTENT: nulls pass but the gamma^2's disagree ->
        no single-gamma description; the mating chart stays a chart.
  (iii) NULLS FAIL: finite-size effects dominate; inconclusive at
        accessible depth.
"""
import itertools, math, sys, time
import numpy as np
from scipy.optimize import linprog, minimize

T0 = time.time()
def log(*a): print(f"[{time.time()-T0:7.1f}s]", *a, flush=True)

NS = 12                      # max causet size sampled
PHI = math.pi / 4
NQ = 8000                    # quantum paths
NC = 20000                   # classical paths
rng = np.random.default_rng(1)

W2 = {0: 2, 1: -4, 2: 2}

# exact 8th-root trig for integer gaps at pi/4
C8 = [math.cos(k * PHI) for k in range(8)]
S8 = [math.sin(k * PHI) for k in range(8)]
def cg(g): return C8[g % 8]
def sg(g): return S8[g % 8]

# ---------------- per-parent gap system ------------------------------------
QP_FAIL = 0
def maxent_gap_law(gapcounts):
    """gapcounts: dict gap -> multiplicity (labeled children).
       returns dict gap -> per-labeled-child probability rho^2, or None."""
    gaps = sorted(gapcounts)
    mu = np.array([gapcounts[g] for g in gaps], float)
    A = np.vstack([mu * np.array([cg(g) for g in gaps]),
                   mu * np.array([sg(g) for g in gaps])])
    b = np.array([1.0, 0.0])
    K = len(gaps)
    r = linprog(np.zeros(K), A_eq=A, b_eq=b, bounds=[(0, None)] * K,
                method="highs")
    if not r.success: return None
    x0 = r.x
    res = minimize(lambda x: float(np.dot(mu, x * x)), x0,
                   jac=lambda x: 2 * mu * x,
                   constraints=[{"type": "eq", "fun": lambda x: A @ x - b,
                                 "jac": lambda x: A}],
                   bounds=[(0, None)] * K, method="SLSQP",
                   options={"maxiter": 200, "ftol": 1e-12})
    xm = res.x if res.success else x0
    if float(np.dot(mu, xm * xm)) > 1 + 1e-7: return None
    # >=1 endpoint
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
    return {g: x[i] ** 2 for i, g in enumerate(gaps)}

# ---------------- incremental growth state ---------------------------------
def downset_masks(n, below):
    """below[x] = bitmask of elements strictly below x.  Yield masks D
       (downward closed subsets)."""
    out = []
    for mask in range(1 << n):
        ok = True
        m = mask
        while m:
            x = (m & -m).bit_length() - 1
            if below[x] & ~mask & ((1 << n) - 1):
                ok = False; break
            m &= m - 1
        if ok: out.append(mask)
    return out

def gap_of(mask, n, below):
    """action gap of adding a maximal element with downset mask."""
    ds = 1
    m = mask
    while m:
        d = (m & -m).bit_length() - 1
        # k = number of z in D strictly above d
        k = 0
        mm = mask
        while mm:
            z = (mm & -mm).bit_length() - 1
            if below[z] >> d & 1: k += 1
            mm &= mm - 1
        ds -= W2.get(k, 0)
        m &= m - 1
    return ds

def observables(n, below, above):
    full = (1 << n) - 1
    posts = minima = 0
    links = 0
    for x in range(n):
        comp = below[x] | above[x]
        if comp == full & ~(1 << x): posts += 1
        if below[x] == 0: minima += 1
    # links: covering pairs: y < x with no z in between
    for x in range(n):
        m = below[x]
        while m:
            y = (m & -m).bit_length() - 1
            if not (below[x] & above[y]): links += 1
            m &= m - 1
    # height: longest chain via DP in birth order (all below sets known)
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
    """grow one path to NS; record observables at each n in 4..NS.
       returns list of tuples or None if an infeasible parent killed it."""
    global QP_FAIL
    below = [0]
    above = [0]
    recs = {}
    for n in range(1, NS):
        masks = downset_masks(n, below)
        if quantum:
            gaps = [gap_of(m, n, below) for m in masks]
            gc = {}
            for g in gaps: gc[g] = gc.get(g, 0) + 1
            law = maxent_gap_law(gc)
            if law is None:
                QP_FAIL += 1
                return None
            probs = np.array([law[g] for g in gaps])
            probs = np.maximum(probs, 0)
            s = probs.sum()
            probs = probs / s
        else:
            probs = np.full(len(masks), 1.0 / len(masks))
        D = masks[rng.choice(len(masks), p=probs)]
        # add element n with below-set D (downward closed already)
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

# ---------------- run -------------------------------------------------------
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
        if time.time() - t_last > 60:
            log(f"  [{tag}] {got}/{npaths} paths (QP fails so far {QP_FAIL})")
            t_last = time.time()
    out = {}
    for n in range(4, NS + 1):
        mean = acc[n] / got
        se = np.sqrt(np.maximum(acc2[n] / got - mean ** 2, 0) / got)
        out[n] = (mean, se)
    return out, got

log(f"sampling QUANTUM pi/4 gap-max-entropy chain: {NQ} paths to n={NS}")
Q, gotQ = run(True, NQ, "quantum")
log(f"quantum done ({gotQ} paths, {QP_FAIL} infeasible-parent kills)")
log(f"sampling CLASSICAL uniform chain: {NC} paths")
C, gotC = run(False, NC, "classical")
log("classical done")

names = ["posts", "minima", "links", "height", "nrel"]
for tag, T in (("quantum", Q), ("classical", C)):
    log(f"--- {tag} expectations (n: posts minima links height r) ---")
    for n in range(4, NS + 1):
        mean, se = T[n]
        r = mean[4] / (n * (n - 1) / 2)
        rse = se[4] / (n * (n - 1) / 2)
        log(f"  n={n:2d}: " + "  ".join(f"{m:8.4f}±{s:.4f}"
            for m, s in zip(mean[:4], se[:4])) + f"   r = {r:.4f}±{rse:.4f}")

# ---------------- slopes, nulls, gamma -------------------------------------
def slope(T, idx, nlo=6, nhi=NS):
    ns = np.arange(nlo, nhi + 1)
    ys = np.array([max(T[n][0][idx], 1e-12) for n in ns])
    A = np.vstack([np.log(ns), np.ones(len(ns))]).T
    coef, res, *_ = np.linalg.lstsq(A, np.log(ys), rcond=None)
    return coef[0]

log("--- slopes (log-log fit n=6..12) and KPZ extraction ---")
report = {}
for i, nm in enumerate(names[:4]):
    aq = slope(Q, i); ac = slope(C, i)
    report[nm] = (ac, aq)
    log(f"  {nm:7s}: a_cl = {ac:+.4f}  a_q = {aq:+.4f}  "
        f"delta-a = {aq - ac:+.4f}")
def gamma2_from(ac, aq):
    x = 1 - ac; D = 1 - aq
    if abs(D * (D - 1)) < 1e-9: return float("nan")
    return 4 * (x - D) / (D * (D - 1))
for nm in ("posts", "height"):
    ac, aq = report[nm]
    g2 = gamma2_from(ac, aq)
    log(f"  KPZ gamma^2 from {nm}: {g2:.4f}"
        + ("  (independence caveat)" if nm == "height" else ""))
r12 = Q[NS][0][4] / (NS * (NS - 1) / 2)
rho = math.sin(math.pi * (r12 - 0.5))
g2m = 4 * math.acos(-rho) / math.pi
log(f"  mating gamma^2 from r({NS}) = {r12:.4f}: {g2m:.4f}")
log("  nulls: minima and links delta-a should be ~0 if finite-size is")
log("  under control; posts/height gamma^2 vs mating gamma^2 decides")
log("  readings (i)/(ii).")
log("DONE")
