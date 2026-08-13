#!/usr/bin/env python3
"""P2 SHORE-UP (b): the tilt law on a SECOND ENGINE - the 4D bracket.

Same unlabeled tree (n <= 8), but gaps from the 4D BD integer bracket
(coefficients 1, -9, 16, -8) and phase phi4 = 4/sqrt6, class-level
max-entropy double-conservation law.  Tests engine-robustness of:
  - T2 linear law a_Q + a_count = 2 a_R (tilt identity)
  - c * f_count ~ O(1) flat
  - ln R approximate Gaussianity and sigma(n) growth
"""
import math
import numpy as np

src = open("pi4_first_prediction.py").read()
head = src[:src.index('log("=== pi/4 feasibility')]
exec(head)
FORBID = set()
PHI4D = 4.0 / math.sqrt(6.0)

def action4(rel, n):
    relset = set(rel)
    tot = 0
    for x in range(n):
        nk = [0, 0, 0, 0]
        for y in range(n):
            if (y, x) not in relset: continue
            k = sum(1 for z in range(n)
                    if (y, z) in relset and (z, x) in relset)
            if k <= 3: nk[k] += 1
        tot += 1 - nk[0] + 9 * nk[1] - 16 * nk[2] + 8 * nk[3]
    return tot

S4 = {k: action4(levels[nelem(k)][k][1], nelem(k)) for k in allkeys}

def parent_system4(p):
    cls = [(ck, mu, S4[ck] - S4[p]) for ck, (mu, g) in children[p].items()]
    mu = np.array([m for _, m, _ in cls], float)
    g = np.array([gg for _, _, gg in cls], float)
    A = np.vstack([mu * np.cos(g * PHI4D), mu * np.sin(g * PHI4D)])
    return cls, list(range(len(cls))), mu, A, np.array([1.0, 0.0])

law = {}
support = {root}; frontier = [root]
nfail = 0
while frontier:
    nxt = []
    for p in frontier:
        if nelem(p) >= NMAX: continue
        cls, keep, mu, A, b = parent_system4(p)
        x = born_point(mu, A, b, want="maxent")
        if x is None:
            nfail += 1
            continue
        for idx, i in enumerate(keep):
            ck, muc, g = cls[i]
            if x[idx] > 1e-12:
                law[(p, ck)] = (x[idx], g, muc)
                if ck not in support:
                    support.add(ck); nxt.append(ck)
    frontier = nxt
log(f"4D law built: {len(law)} edges, infeasible parents: {nfail}")

R = {root: 1.0}
for k in allkeys:
    if k != root: R[k] = 0.0
for p in allkeys:
    for ck, (mu, g) in children.get(p, {}).items():
        if (p, ck) not in law: continue
        rho, gg, muc = law[(p, ck)]
        R[ck] += R[p] * mu * rho

def class_obs(key):
    m, rel = key
    below = [set() for _ in range(m)]; above = [set() for _ in range(m)]
    for a_, b_ in rel:
        below[b_].add(a_); above[a_].add(b_)
    posts = sum(1 for x in range(m)
                if len(below[x]) + len(above[x]) == m - 1)
    minima = sum(1 for x in range(m) if not below[x])
    return posts, minima, len(rel) == 0
OBS = {}
for n in range(4, NMAX + 1):
    for k in levels[n]: OBS[k] = class_obs(k)
stems3 = sorted(levels[3]); stems4 = sorted(levels[4])
STEMS = stems3 + stems4[:6]
def contains_stem(key, stem):
    m, rel = key
    sm, srel = stem
    for D in downsets_of(m, rel):
        if len(D) != sm: continue
        di = {d: i for i, d in enumerate(sorted(D))}
        sub = canon_fast(sm, tuple(sorted((di[x], di[y])
              for (x, y) in rel if x in D and y in D)))
        if sub == stem: return True
    return False
EVENTS = [("has_post", lambda k: OBS[k][0] > 0),
          ("3+_minima", lambda k: OBS[k][1] >= 3)]
for i, s in enumerate(STEMS):
    EVENTS.append((f"stem{i}", lambda k, s=s: contains_stem(k, s)))

SUP = {n: [k for k in levels[n] if R[k] > 1e-300]
       for n in range(4, NMAX + 1)}
ns = list(range(4, NMAX + 1))
lnn = np.log(ns)
A2f = np.vstack([lnn, np.ones(len(ns))]).T
def slope(ys):
    return float(np.linalg.lstsq(A2f, np.log(ys), rcond=None)[0][0])

log("== 4D engine: T2 residuals and c*f_count ==")
resids = []
for name, pred in EVENTS:
    fc, fr, fq, cf = [], [], [], []
    ok = True
    for n in ns:
        sup = SUP[n]
        Ak = [k for k in sup if pred(k)]
        if not Ak: ok = False; break
        fc.append(len(Ak) / len(sup))
        fR = sum(R[k] for k in Ak) / sum(R[k] for k in sup)
        fQ = sum(R[k] ** 2 for k in Ak) / sum(R[k] ** 2 for k in sup)
        fr.append(fR); fq.append(fQ)
        cf.append((fQ / fR ** 2) * fc[-1])
    if not ok or min(fr) <= 0: continue
    ac, ar, aq = slope(fc), slope(fr), slope(fq)
    resid = aq + ac - 2 * ar
    resids.append(resid)
    log(f"   {name:12s} a_cnt {ac:+7.3f}  a_R {ar:+7.3f}  a_Q {aq:+7.3f}"
        f"  resid {resid:+7.3f}  c*fc(8) = {cf[-1]:5.2f}")
rs = np.array(resids)
log(f"  T2 residual: mean {np.mean(rs):+.3f}  max|.| {np.max(np.abs(rs)):.3f}"
    f"  (2D engine was mean +0.074)")
log("== 4D engine: ln R Gaussianity / sigma(n) ==")
for n in (5, 6, 7, 8):
    x = np.log(np.array([R[k] for k in SUP[n]]))
    sk = float(((x - x.mean()) ** 3).mean() / x.std() ** 3)
    log(f"   n={n}: sigma = {x.std():.3f}  skew = {sk:+.2f}  "
        f"classes = {len(x)}")
log("DONE")
