#!/usr/bin/env python3
"""DERIVING THE 0.7: the lognormal-tilt mechanism test.

Empirical law to explain (replica-identities-2026-08-13):
gamma_A = -0.7 a_R (corr -0.974), i.e. f_Q ~ f_R^{1.3}.

MECHANISM UNDER TEST.  Ansatz: per level, ln R across classes is
~Gaussian(m, sigma^2), and conditioning on an event A shifts the mean
(x -> m + delta_A) without changing the variance.  Then under the
theta-tilted measures (weights e^{theta x}: theta = 0 counting, 1 = R,
2 = Q):
      f_theta(A) = f_count(A) * e^{theta delta_A}
which yields three PARAMETER-FREE testable identities:
  T1:  c(A) := f_Q/f_R^2 = 1/f_count(A)          (overlap = inverse
       counting fraction)
  T2:  a_Q + a_count = 2 a_R  (exponent linear law; gamma_A =
       -a_count exactly)
  T3:  N_part(A)/|A| = N_part(Omega)/|Omega|      (participation
       density uniform across events; equivalent to T1 via the
       overlap identity)
and 0.7 = a_count/a_R averaged over events (no longer fundamental).

Registered readings:
  (i)   TILT CONFIRMED: c*f_count within ~2x of 1 with no systematic
        n-trend, and a_Q + a_count - 2 a_R ~ 0 (|.| < 0.3) across
        events: mechanism identified; the anti-KPZ class is the
        lognormal-tilt class and 0.7 is derived as a_count/a_R.
  (ii)  PARTIAL: linear law holds for most events but c*f_count drifts:
        variance also shifts under conditioning (second-order tilt);
        report the quadratic correction.
  (iii) FAIL: no relation: mechanism wrong.
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
          ("is_antichain", lambda k: OBS[k][2]),
          ("3+_minima", lambda k: OBS[k][1] >= 3)]
for i, s in enumerate(STEMS):
    EVENTS.append((f"stem{i}", lambda k, s=s: contains_stem(k, s)))

ns = list(range(4, NMAX + 1))
lnn = np.log(ns)
A2 = np.vstack([lnn, np.ones(len(ns))]).T
def slope(ys):
    return float(np.linalg.lstsq(A2, np.log(ys), rcond=None)[0][0])

# support-restricted counting: classes with R > 0 (the law's support)
SUP = {n: [k for k in levels[n] if R[k] > 1e-300] for n in ns}

log("== T1/T2: tilt identities per event ==")
log("   event         a_cnt    a_R      a_Q     resid(T2)  "
    "c*f_cnt: n=4 ... n=8")
resids = []
for name, pred in EVENTS:
    fc, fr, fq, cf = [], [], [], []
    ok = True
    for n in ns:
        sup = SUP[n]
        Ak = [k for k in sup if pred(k)]
        if not Ak: ok = False; break
        fcount = len(Ak) / len(sup)
        fR = sum(R[k] for k in Ak) / sum(R[k] for k in sup)
        fQ = sum(R[k] ** 2 for k in Ak) / sum(R[k] ** 2 for k in sup)
        fc.append(fcount); fr.append(fR); fq.append(fQ)
        cf.append((fQ / fR ** 2) * fcount)
    if not ok: continue
    ac, ar, aq = slope(fc), slope(fr), slope(fq)
    resid = aq + ac - 2 * ar
    resids.append((name, resid, ac, ar))
    cfs = "  ".join(f"{x:6.2f}" for x in cf)
    log(f"   {name:12s} {ac:+7.3f} {ar:+7.3f} {aq:+7.3f}  {resid:+8.3f}"
        f"   {cfs}")
rs = np.array([r[1] for r in resids])
log(f"  T2 residual a_Q + a_cnt - 2 a_R: mean {np.mean(rs):+.3f}  "
    f"max|.| {np.max(np.abs(rs)):.3f}")
acs = np.array([r[2] for r in resids]); ars = np.array([r[3] for r in resids])
sel = np.abs(ars) > 0.05
if sel.sum() >= 3:
    log(f"  k = a_cnt/a_R: mean {np.mean(acs[sel]/ars[sel]):.3f} "
        f"+- {np.std(acs[sel]/ars[sel]):.3f}  (the '0.7')")

log("== T3: participation density N_part(A)/|A| across events (n=8) ==")
n = 8
sup = SUP[n]
def npart(keys):
    return sum(R[k] for k in keys) ** 2 / sum(R[k] ** 2 for k in keys)
dens_omega = npart(sup) / len(sup)
log(f"   Omega: N_part = {npart(sup):.1f}  |Omega| = {len(sup)}  "
    f"density = {dens_omega:.4f}")
for name, pred in EVENTS:
    Ak = [k for k in sup if pred(k)]
    if not Ak: continue
    d = npart(Ak) / len(Ak)
    log(f"   {name:12s} N_part = {npart(Ak):8.1f}  |A| = {len(Ak):5d}  "
        f"density = {d:.4f}  ratio-to-Omega = {d/dens_omega:5.2f}")

log("== Gaussianity check: ln R distribution per level ==")
for n in (5, 6, 7, 8):
    x = np.log(np.array([R[k] for k in SUP[n]]))
    sk = float(((x - x.mean()) ** 3).mean() / x.std() ** 3)
    ku = float(((x - x.mean()) ** 4).mean() / x.std() ** 4 - 3)
    log(f"   n={n}: mean {x.mean():+7.3f}  sigma {x.std():5.3f}  "
        f"skew {sk:+5.2f}  ex-kurt {ku:+5.2f}  classes {len(x)}")
log("DONE")
