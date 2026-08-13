#!/usr/bin/env python3
"""THE REPLICA EXPONENT-DOUBLING TEST.

Insight under test (fact-stability-mechanism arc): phase telescoping
makes the covariant quantum measure the SQUARE of a positive partition
function, Q(C) = R(C)^2 — two independent classical growths agreeing.
If so, the measure-fraction of RARE geometry classes should decay with
size at roughly TWICE the one-replica exponent:

    f_Q(rare, n) ~ f_R(rare, n)^2-ish  =>  a_Q ~ 2 a_R,

while BULK observables (dominated by typical classes) should show no
doubling.  The anti-KPZ signature (posts n^-2.03 quantum vs n^-0.90
classical, ratio 2.25) was the accidental first instance.

Method: EXACT tree DP on the 2D pi/4 class-max-entropy law to n = 8
(no sampling noise).  Four weightings of the SAME tree:
    R  : one-replica positive amplitude, R(c) += R(p) mu rho
    Q  : two-replica, Q = R^2 per class (the coherent measure;
         phases idle by the telescoping theorem)
    P  : Born diagonal, W(c) += W(p) mu rho^2 (the martingale)
    U  : uniform labeled chain (classical counting reference)
Observables per level n = 4..8, per weighting:
    RARE-EVENT FRACTIONS: f(has post), f(is n-chain),
      f(is n-antichain), f(single minimum ... complement rare side)
    BULK CONTROLS: E[links]/n, E[minima], E[N1]/n
Exponents: lstsq slope of ln f against ln n (n = 4..8; short window,
stated).  Corroboration: sampled 4D-engine P(post now) slopes from
posts_cosmology_probe.log (n = 6..12).

Registered readings:
  (i)   DOUBLING: for the rare-event fractions, a_Q / a_R = 2 +- 0.3
        while bulk controls have ratio ~ 1: the replica mechanism is
        quantitative — the anti-KPZ class IS squared-partition-
        function statistics.
  (ii)  PARTIAL: posts double but the other rare events do not:
        observable-specific accident, mechanism needs refinement.
  (iii) NO: ratios scatter away from 2: the doubling heuristic dies.
"""
import math
import numpy as np

src = open("pi4_first_prediction.py").read()
head = src[:src.index('log("=== pi/4 feasibility')]
exec(head)

FORBID = set()

# ---------------- class-max-entropy law (as in factstab_probe) --------------
law = {}
support = {root}; frontier = [root]
while frontier:
    nxt = []
    for p in frontier:
        if nelem(p) >= NMAX: continue
        cls, keep, mu, A, b = parent_system(p)
        x = born_point(mu, A, b, want="maxent")
        if x is None: continue
        for idx, i in enumerate(keep):
            ck, muc, g = cls[i]
            if x[idx] > 1e-12:
                law[(p, ck)] = (x[idx], g, muc)
                if ck not in support:
                    support.add(ck); nxt.append(ck)
    frontier = nxt
log(f"law built: {len(law)} edges")

# ---------------- four weightings by exact DP -------------------------------
R = {root: 1.0}; W = {root: 1.0}; U = {root: 1.0}
for k in allkeys:
    if k != root: R[k] = 0.0; W[k] = 0.0; U[k] = 0.0
Ktot = {p: sum(mu for _, (mu, g) in children[p].items())
        for p in allkeys if p in children}
for p in allkeys:
    for ck, (mu, g) in children.get(p, {}).items():
        U[ck] += U[p] * mu / Ktot[p]
        if (p, ck) not in law: continue
        rho, gg, muc = law[(p, ck)]
        R[ck] += R[p] * mu * rho
        W[ck] += W[p] * mu * rho * rho
Q = {k: R[k] ** 2 for k in allkeys}

# ---------------- per-class observables -------------------------------------
def class_obs(key):
    m, rel = key
    relset = set(rel)
    below = [set() for _ in range(m)]; above = [set() for _ in range(m)]
    for a_, b_ in rel:
        below[b_].add(a_); above[a_].add(b_)
    posts = sum(1 for x in range(m)
                if len(below[x]) + len(above[x]) == m - 1)
    minima = sum(1 for x in range(m) if not below[x])
    links = sum(1 for a_, b_ in rel if not (below[b_] & above[a_]))
    N1 = sum(1 for a_, b_ in rel if len(below[b_] & above[a_]) == 1)
    is_chain = len(rel) == m * (m - 1) // 2
    is_anti = len(rel) == 0
    return posts, minima, links, N1, is_chain, is_anti

OBS = {}
for n in range(4, NMAX + 1):
    for k in levels[n]:
        OBS[k] = class_obs(k)

# ---------------- tables ----------------------------------------------------
WEIGHTS = {"R": R, "Q": Q, "P": W, "U": U}
def frac(wname, n, pred):
    w = WEIGHTS[wname]
    tot = sum(w[k] for k in levels[n])
    num = sum(w[k] for k in levels[n] if pred(OBS[k]))
    return num / tot if tot > 0 else float("nan")
def expec(wname, n, val):
    w = WEIGHTS[wname]
    tot = sum(w[k] for k in levels[n])
    num = sum(w[k] * val(OBS[k]) for k in levels[n])
    return num / tot if tot > 0 else float("nan")

RARE = [("has_post", lambda o: o[0] > 0),
        ("is_chain", lambda o: o[4]),
        ("is_antichain", lambda o: o[5]),
        ("3+_minima", lambda o: o[1] >= 3)]
BULK = [("links/n", lambda o: o[2]),
        ("minima", lambda o: o[1]),
        ("N1/n", lambda o: o[3])]

ns = list(range(4, NMAX + 1))
lnn = np.log(ns)
def slope(ys):
    ys = np.array(ys)
    if np.any(ys <= 0): return float("nan")
    A2 = np.vstack([lnn, np.ones(len(ns))]).T
    return float(np.linalg.lstsq(A2, np.log(ys), rcond=None)[0][0])

log("== rare-event fractions: exponent a (ln f vs ln n, n=4..8) ==")
log("   event         a_R      a_Q      a_P      a_U     a_Q/a_R")
verdicts = []
for name, pred in RARE:
    aa = {}
    for wname in WEIGHTS:
        aa[wname] = slope([frac(wname, n, pred) for n in ns])
    ratio = aa["Q"] / aa["R"] if aa["R"] and not math.isnan(aa["R"]) \
        and abs(aa["R"]) > 0.05 else float("nan")
    verdicts.append((name, ratio))
    log(f"   {name:12s} {aa['R']:+7.3f}  {aa['Q']:+7.3f}  {aa['P']:+7.3f}"
        f"  {aa['U']:+7.3f}   {ratio:6.2f}")
    for wname in ("R", "Q"):
        vals = "  ".join(f"{frac(wname, n, pred):.5f}" for n in ns)
        log(f"      f_{wname}: {vals}")

log("== bulk controls: exponent of E[X] ==")
log("   observable    a_R      a_Q      a_P      a_U     a_Q/a_R")
for name, val in BULK:
    aa = {}
    for wname in WEIGHTS:
        aa[wname] = slope([max(expec(wname, n, val), 1e-300) for n in ns])
    ratio = aa["Q"] / aa["R"] if abs(aa["R"]) > 0.05 else float("nan")
    log(f"   {name:12s} {aa['R']:+7.3f}  {aa['Q']:+7.3f}  {aa['P']:+7.3f}"
        f"  {aa['U']:+7.3f}   {ratio:6.2f}")

# direct squared-fraction check: is f_Q ~ f_R^2 * (typicality corr)?
log("== direct check: ln f_Q vs 2 ln f_R (has_post) ==")
for n in ns:
    fq = frac("Q", n, RARE[0][1]); fr = frac("R", n, RARE[0][1])
    log(f"   n={n}: f_Q = {fq:.5f}   f_R^2 = {fr*fr:.5f}   "
        f"ratio = {fq/(fr*fr):.2f}")

# ---------------- corroboration: sampled 4D posts ---------------------------
log("== corroboration: 4D-engine sampled P(post now) slopes (n=6..12) ==")
qs = [0.1092, 0.0998, 0.0798, 0.0690, 0.0517, 0.0445, 0.0357]
cs = [0.2625, 0.2335, 0.2083, 0.1901, 0.1788, 0.1703, 0.1652]
nn = np.log(np.arange(6, 13))
A2 = np.vstack([nn, np.ones(7)]).T
aq = float(np.linalg.lstsq(A2, np.log(qs), rcond=None)[0][0])
ac = float(np.linalg.lstsq(A2, np.log(cs), rcond=None)[0][0])
log(f"   quantum a = {aq:+.3f}   classical a = {ac:+.3f}   "
    f"ratio = {aq/ac:.2f}")
log("DONE")
