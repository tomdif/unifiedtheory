#!/usr/bin/env python3
"""DEEPER: the replica overlap decomposed into exact identities.

Two hand-derived identities to verify and then measure:

  I1 (overlap = participation ratio):
      c(A, n) = f_Q(A)/f_R(A)^2 = N_part(Omega, n) / N_part(A, n),
      N_part(X) = (sum_X R)^2 / sum_X R^2
      - the overlap is the ratio of effective-geometry counts.

  I2 (coherent = Born x history multiplicity), per class:
      Q(C) = P(C) * N_eff(C),   N_eff(C) = R(C)^2 / W(C)
      - with R(C) = sum of path products of rho and W(C) = sum of
      path products of rho^2, N_eff is the participation number of
      the LABELED PATHS reaching C (1 <= N_eff <= #paths).  The
      coherent measure is the Born measure reweighted by effective
      history multiplicity: the history-counting axiom made dynamical.

Measurements (exact DP, 2D pi/4 class-max-ent law, n <= 8):
  M1: verify I1, I2 to machine precision.
  M2: gamma_A scan - overlap growth exponent c(A,n) ~ n^gamma_A for a
      family of events (has_post, is_antichain, 3+minima, the 11
      stems), against the event's own rarity exponent a_R(A):
      is gamma_A a function of rarity (candidate scaling law)?
  M3: N_eff statistics per level: E_P[N_eff] (= Q(Omega) growth
      factor, the anti-decoherence rate), spread of ln N_eff across
      classes, correlation of ln N_eff with ln P (are path-rich
      geometries also Born-likely?).
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
for k in allkeys:
    if k != root: R[k] = 0.0; W[k] = 0.0; NP[k] = 0.0
for p in allkeys:
    for ck, (mu, g) in children.get(p, {}).items():
        if (p, ck) not in law: continue
        rho, gg, muc = law[(p, ck)]
        R[ck] += R[p] * mu * rho
        W[ck] += W[p] * mu * rho * rho
        NP[ck] += NP[p] * mu

# ---------------- M1: identities --------------------------------------------
log("== M1: identity checks ==")
worst2 = 0.0
for n in range(2, NMAX + 1):
    for k in levels[n]:
        if W[k] > 1e-300:
            neff = R[k] ** 2 / W[k]
            # I2 is definitional (Q = R^2 = P * (R^2/W)); the CONTENT
            # is the bound 1 <= N_eff <= #paths:
            if neff < 1 - 1e-9 or neff > NP[k] * (1 + 1e-9):
                worst2 = max(worst2, 1.0)
log(f"  I2 bounds 1 <= R^2/W <= #paths: violations = "
    f"{'NONE' if worst2 == 0 else 'FOUND'}")
def Npart(keys, n):
    num = sum(R[k] for k in keys) ** 2
    den = sum(R[k] ** 2 for k in keys)
    return num / den if den > 0 else float("nan")
# I1 spot check at n=8, has_post
def class_obs(key):
    m, rel = key
    relset = set(rel)
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
for n in (5, 8):
    Akeys = [k for k in levels[n] if OBS[k][0] > 0]
    fQ = sum(R[k] ** 2 for k in Akeys) / sum(R[k] ** 2 for k in levels[n])
    fR = sum(R[k] for k in Akeys) / sum(R[k] for k in levels[n])
    lhs = fQ / fR ** 2
    rhs = Npart(levels[n], n) / Npart(Akeys, n)
    log(f"  I1 at n={n} (has_post): c = {lhs:.6f}  "
        f"Npart-ratio = {rhs:.6f}  match {abs(lhs-rhs)<1e-9}")

# ---------------- M2: gamma_A vs rarity -------------------------------------
log("== M2: overlap exponent gamma_A vs rarity exponent a_R(A) ==")
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
rows = []
for name, pred in EVENTS:
    fRs, cs = [], []
    ok = True
    for n in ns:
        Ak = [k for k in levels[n] if pred(k)]
        if not Ak: ok = False; break
        fR = sum(R[k] for k in Ak) / sum(R[k] for k in levels[n])
        fQ = sum(R[k] ** 2 for k in Ak) / sum(R[k] ** 2
                                              for k in levels[n])
        fRs.append(fR); cs.append(fQ / fR ** 2)
    if not ok or min(fRs) <= 0: continue
    aR = float(np.linalg.lstsq(A2, np.log(fRs), rcond=None)[0][0])
    gA = float(np.linalg.lstsq(A2, np.log(cs), rcond=None)[0][0])
    rows.append((name, aR, gA, cs[-1]))
    log(f"  {name:12s} a_R = {aR:+7.3f}   gamma_A = {gA:+6.3f}   "
        f"c(8) = {cs[-1]:7.2f}")
aRs = np.array([r[1] for r in rows]); gAs = np.array([r[2] for r in rows])
if len(rows) >= 4:
    sel = aRs < -0.05
    if sel.sum() >= 3:
        ratio = gAs[sel] / (-aRs[sel])
        log(f"  scaling-law candidate gamma_A = -k a_R: k = "
            f"{np.mean(ratio):.3f} +- {np.std(ratio):.3f} "
            f"(over {sel.sum()} decaying events)")
    corr = np.corrcoef(aRs, gAs)[0, 1]
    log(f"  corr(a_R, gamma_A) over all {len(rows)} events = {corr:+.3f}")

# ---------------- M3: N_eff statistics --------------------------------------
log("== M3: effective history multiplicity N_eff = R^2/W per level ==")
for n in range(3, NMAX + 1):
    ks = [k for k in levels[n] if W[k] > 1e-300]
    neff = np.array([R[k] ** 2 / W[k] for k in ks])
    pw = np.array([W[k] for k in ks]); pw = pw / pw.sum()
    EP = float(np.dot(pw, neff))
    Qtot = sum(R[k] ** 2 for k in levels[n])
    Ptot = sum(W[k] for k in levels[n])
    lnN = np.log(neff)
    lnP = np.log(np.array([W[k] for k in ks]))
    cr = float(np.corrcoef(lnN, lnP)[0, 1]) if len(ks) > 3 else float("nan")
    log(f"  n={n}: E_P[N_eff] = {EP:8.2f}  Q(Omega)/P(Omega) = "
        f"{Qtot/Ptot:8.2f}  spread(ln N_eff) = {np.std(lnN):5.2f}  "
        f"corr(ln N_eff, ln P) = {cr:+.3f}")
log("  (Q(Omega)/P(Omega) = E_P[N_eff] is I2 aggregated: the")
log("   anti-decoherence rate IS the mean effective history count)")
log("DONE")
