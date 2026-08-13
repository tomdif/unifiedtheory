#!/usr/bin/env python3
"""DERIVING sigma(n): the R-DP as a random multiplicative cascade.

The tilt law reduced every measured exponent to one dynamical input:
the growth of sigma(n) = std of ln R across classes (1.31 -> 1.59
over n = 5..8).  This script derives its dynamics from the R-recursion
itself.  EXACT decomposition per growth step: for each child class c,

    ln R(c) = m(c) + delta(c),
    m(c)     = sum_p share_p(c) * ln R(p)      (share-weighted parent
               mean; share_p = R(p) mu rho / R(c) ... normalized
               contribution shares)
    delta(c) = ln R(c) - m(c)                  (increment: branching
               log-weights + aggregation/N_eff gain)

so   Var_c[ln R] = Var(m) + Var(delta) + 2 Cov(m, delta),

with Var(m) = g_n * Var_p[ln R] (g_n < 1: multi-parent SMOOTHING) and
Var(delta) = v_n (the cascade increment variance, fed by the law's
branching spread).  The cascade model: sigma^2_{n+1} =
g sigma^2_n + v + 2c, constants fitted on early transitions.

Outputs:
  1. per-transition table: Var(child), g_n, v_n, cov_n, mean drift
     decomposition;
  2. HOLDOUT TEST: constants averaged over transitions 4->5..6->7
     predict sigma(8); compare to measured 1.587;
  3. local-vs-global: mean per-parent branching spread s_p^2 of
     ln(mu rho) (share-weighted) vs v_n - how much of the increment
     is local branching vs aggregation;
  4. drift: E[ln R] decrement per step and its split.

Reading: if g, v, c are stable and the holdout hits sigma(8) within a
few %, sigma(n) dynamics = measured-constant multiplicative cascade,
and the remaining analytic step (deriving g and v from the max-ent
double-conservation structure) is sharply posed.
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
parents_of = {}
for p in allkeys:
    for ck, (mu, g) in children.get(p, {}).items():
        if (p, ck) not in law: continue
        rho, gg, muc = law[(p, ck)]
        R[ck] += R[p] * mu * rho
        parents_of.setdefault(ck, []).append((p, mu * rho))

SUP = {n: [k for k in levels[n] if R[k] > 1e-300] for n in range(1, NMAX + 1)}

log("== cascade decomposition per transition ==")
log("   n->n+1  Var_par  Var_chd    Var(m)   g_n    v_n=V(d)  2Cov   "
    "E[dlnR]  E[delta]  s_loc^2")
rows = []
for n in range(3, NMAX):
    par = SUP[n]; chd = SUP[n + 1]
    lnRp = {p: math.log(R[p]) for p in par}
    Vp = float(np.var([lnRp[p] for p in par]))
    Ls, ms, ds = [], [], []
    for c in chd:
        contribs = parents_of.get(c, [])
        tot = sum(R[p] * w for p, w in contribs)
        if tot <= 0: continue
        L = math.log(R[c])
        m = sum((R[p] * w / tot) * lnRp[p] for p, w in contribs)
        Ls.append(L); ms.append(m); ds.append(L - m)
    Ls = np.array(Ls); ms = np.array(ms); ds = np.array(ds)
    Vc = float(np.var(Ls)); Vm = float(np.var(ms)); Vd = float(np.var(ds))
    Cv = float(np.cov(ms, ds)[0, 1]) if len(ms) > 2 else 0.0
    gn = Vm / Vp if Vp > 0 else float("nan")
    # local branching spread: per parent, share-weighted var of ln(mu rho)
    slocs = []
    for p in par:
        kids = [(ck, law[(p, ck)]) for ck, (mu, g) in
                children.get(p, {}).items() if (p, ck) in law]
        if len(kids) < 2: continue
        ws = np.array([mu_ * rho for ck, (rho, gg, mu_) in
                       [(ck, v) for ck, v in kids]])
        lw = np.log(ws)
        sh = ws / ws.sum()
        mloc = float((sh * lw).sum())
        slocs.append(float((sh * (lw - mloc) ** 2).sum()))
    sloc = float(np.mean(slocs)) if slocs else 0.0
    drift = float(np.mean(Ls)) - float(np.mean([lnRp[p] for p in par]))
    rows.append((n, Vp, Vc, gn, Vd, 2 * Cv))
    log(f"   {n}->{n+1}   {Vp:7.3f}  {Vc:7.3f}   {Vm:7.3f}  {gn:5.3f}"
        f"  {Vd:7.3f}  {2*Cv:+6.3f}  {drift:+7.3f}  "
        f"{float(np.mean(ds)):+7.3f}  {sloc:7.3f}")

log("== holdout: fit constants on 4->5..6->7, predict sigma(8) ==")
fit = [r for r in rows if 4 <= r[0] <= 6]
g_ = float(np.mean([r[3] for r in fit]))
v_ = float(np.mean([r[4] for r in fit]))
c_ = float(np.mean([r[5] for r in fit]))
log(f"   constants: g = {g_:.3f}  v = {v_:.3f}  2cov = {c_:+.3f}")
s2 = float(np.var([math.log(R[k]) for k in SUP[7]]))
pred = g_ * s2 + v_ + c_
meas = float(np.var([math.log(R[k]) for k in SUP[8]]))
log(f"   sigma^2(8): predicted = {pred:.3f}  measured = {meas:.3f}  "
    f"(sigma: {math.sqrt(pred):.3f} vs {math.sqrt(meas):.3f}, "
    f"err {100*abs(math.sqrt(pred)-math.sqrt(meas))/math.sqrt(meas):.1f}%)")
log("== asymptotic cascade fixed line ==")
if g_ < 1:
    s2inf_rate = v_ + c_
    log(f"   with g < 1 the cascade tends to sigma^2* = (v + 2cov)/(1-g)"
        f" = {(v_ + c_)/(1 - g_):.2f} if constants persist "
        f"(sigma* = {math.sqrt(max((v_ + c_)/(1 - g_), 0)):.2f}) - "
        f"a SATURATING lognormal spread, not runaway multifractality")
log("DONE")
