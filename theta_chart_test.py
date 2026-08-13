#!/usr/bin/env python3
"""THE COMPLETE STATISTICAL CHART: path-level tilt unification.

One layer below the class-level tilt law.  At the PATH level every
measure in the theory is one family:

    T_theta(C) = sum_{paths -> C} e^{theta x_path},   x = ln prod rho

    theta = 0 : path counting  (N_paths)
    theta = 1 : R              (coherent one-replica)
    theta = 2 : W = P          (Born diagonal)
    and Q = T_1^2              (the r = 2 axis, already charted by the
                                class-level tilt law)

Gaussian path-ensemble ansatz => three parameter-free predictions:

  D1 (THETA-LINEARITY): per event, exponents are equally spaced:
      a_P - a_R = a_R - a_path0.  If true, the P-vs-U ~ 2 posts
      regularity becomes a theorem of the chart (a_P ~ 2 a_R - a_0).
  D2 (SPREAD UNIFORMITY): N_eff(C) = R^2/W = N_paths(C) e^{-s^2} with
      s^2 the within-class path-log spread; if s^2 is class-uniform,
      ln N_eff = ln N_paths - const, slope 1, small residual.  This
      would explain corr(ln N_eff, ln P) and complete the I2 identity.
  D3 (CASCADE SEMI-ANALYTICS): g ~ E_child[1/nu_eff] with
      nu_eff(c) = 1/sum_p share_p^2 the effective parent number
      (equality iff parent log-weights uncorrelated); excess of
      measured g over E[1/nu] measures sibling-parent correlation.
      And v vs Var(ln aggregation gain).
"""
import math
import numpy as np

src = open("pi4_first_prediction.py").read()
head = src[:src.index('log("=== pi/4 feasibility')]
exec(head)
FORBID = set()

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

R = {root: 1.0}; W = {root: 1.0}; NP = {root: 1.0}
parents_of = {}
for k in allkeys:
    if k != root: R[k] = 0.0; W[k] = 0.0; NP[k] = 0.0
for p in allkeys:
    for ck, (mu, g) in children.get(p, {}).items():
        if (p, ck) not in law: continue
        rho, gg, muc = law[(p, ck)]
        R[ck] += R[p] * mu * rho
        W[ck] += W[p] * mu * rho * rho
        NP[ck] += NP[p] * mu
        parents_of.setdefault(ck, []).append((p, mu * rho))

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
          ("is_antichain", lambda k: OBS[k][2]),
          ("3+_minima", lambda k: OBS[k][1] >= 3)]
for i, s in enumerate(STEMS):
    EVENTS.append((f"stem{i}", lambda k, s=s: contains_stem(k, s)))

SUP = {n: [k for k in levels[n] if R[k] > 1e-300]
       for n in range(4, NMAX + 1)}
ns = list(range(4, NMAX + 1))
lnn = np.log(ns)
A2f = np.vstack([lnn, np.ones(len(ns))]).T
def slope(ys):
    ys = np.array(ys)
    if np.any(ys <= 0): return float("nan")
    return float(np.linalg.lstsq(A2f, np.log(ys), rcond=None)[0][0])

log("== D1: theta-linearity a_0 (paths), a_1 (R), a_2 (P) ==")
log("   event         a_0      a_1      a_2     (a2-a1)-(a1-a0)")
d1res = []
for name, pred in EVENTS:
    fs = {0: [], 1: [], 2: []}
    ok = True
    for n in ns:
        sup = SUP[n]
        Ak = [k for k in sup if pred(k)]
        if not Ak: ok = False; break
        for th, Wgt in ((0, NP), (1, R), (2, W)):
            fs[th].append(sum(Wgt[k] for k in Ak) /
                          sum(Wgt[k] for k in sup))
    if not ok: continue
    a0, a1, a2 = slope(fs[0]), slope(fs[1]), slope(fs[2])
    curv = (a2 - a1) - (a1 - a0)
    d1res.append(curv)
    log(f"   {name:12s} {a0:+7.3f}  {a1:+7.3f}  {a2:+7.3f}   {curv:+7.3f}")
cs = np.array([c for c in d1res if not math.isnan(c)])
log(f"  curvature: mean {np.mean(cs):+.3f}  max|.| {np.max(np.abs(cs)):.3f}"
    f"  (0 = perfect theta-linearity)")

log("== D2: N_eff vs N_paths (spread uniformity) ==")
for n in (6, 7, 8):
    ks = [k for k in SUP[n] if W[k] > 1e-300 and NP[k] > 0]
    lnNe = np.array([math.log(R[k] ** 2 / W[k]) for k in ks])
    lnNp = np.array([math.log(NP[k]) for k in ks])
    A3 = np.vstack([lnNp, np.ones(len(ks))]).T
    (sl, ic), *_ = np.linalg.lstsq(A3, lnNe, rcond=None)
    resid = float(np.std(lnNe - (A3 @ [sl, ic])))
    s2impl = lnNp - lnNe
    log(f"  n={n}: slope = {sl:.3f} (predict 1)  intercept = {ic:+.3f}  "
        f"resid-std = {resid:.3f}  s^2_impl mean = {np.mean(s2impl):.3f} "
        f"std = {np.std(s2impl):.3f}  corr = "
        f"{np.corrcoef(lnNp, lnNe)[0,1]:+.3f}")

log("== D3: cascade constants semi-analytics ==")
for n in (6, 7, 8):
    chd = SUP[n + 1] if n + 1 <= NMAX else []
    if not chd: continue
    invnu, lnnu = [], []
    for c in chd:
        contribs = parents_of.get(c, [])
        tot = sum(R[p] * w for p, w in contribs)
        if tot <= 0: continue
        sh = np.array([R[p] * w / tot for p, w in contribs])
        nu = 1.0 / float((sh ** 2).sum())
        invnu.append(1.0 / nu); lnnu.append(math.log(nu))
    log(f"  {n}->{n+1}: E[1/nu_eff] = {np.mean(invnu):.3f}  "
        f"(measured g ~ 0.83-0.91)  E[nu] = "
        f"{np.mean([1/x for x in invnu]):.2f}  Var(ln nu) = "
        f"{np.var(lnnu):.3f}  (v ~ 0.24-0.30)")
log("  g >> E[1/nu] would mean parent log-weights are strongly")
log("  correlated across a child's parent set (sibling correlation).")
log("DONE")
