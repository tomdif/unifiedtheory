#!/usr/bin/env python3
"""THE LAST TWO LEMMAS of the statistical program: analytic structure
of the cascade constants g and v.

L1 (SIBLING SMOOTHING LEMMA).  Exact split of the smoothing constant:
with X_p = ln R(p), mu = E[X], shares sh_p(c), m(c) = sum sh X:

   Var_c(m) = E_c[ sum_p sh_p^2 (X_p-mu)^2 ]          (diagonal D)
            + E_c[ sum_{p!=q} sh_p sh_q (X_p-mu)(X_q-mu) ]  (off O)
            - (E_c[m] - mu)^2                          (centering B)

so g = (D + O - B)/sigma^2, with D/sigma^2 ~ E[1/nu_eff] and O the
sibling-covariance term.  Define the measured share-weighted co-parent
correlation rho_sib = O / (sigma^2 * E_c[sum_{p!=q} sh_p sh_q]).
TREE-MODEL CLOSURE: siblings share all ancestry except their last
element => X_p = shared(c) + xi_p with unshared variance w:
   rho_sib = 1 - w/sigma^2  and  g = 1 - (1-rho_sib)(1 - E[1/nu]).
Prediction to verify: rho_sib_measured ~ 1 - (1-g)/(1-E[1/nu]).

L2 (INJECTION LEMMA).  In the strong-sibling-correlation regime
(X_p ~ equal across a child's parents), the increment collapses to
   delta(c) ~ delta_hat(c) := ln sum_p mu rho(p->c)
- the log TOTAL INCOMING BORN-SHELL WEIGHT, a purely level-local
combinatorial quantity of the law.  Verify: corr(delta, delta_hat),
regression slope, and Var(delta_hat) vs v; then v is derived from the
law's local weight structure plus a computable residual.
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
parents_of = {}
for k in allkeys:
    if k != root: R[k] = 0.0
for p in allkeys:
    for ck, (mu, g) in children.get(p, {}).items():
        if (p, ck) not in law: continue
        rho, gg, muc = law[(p, ck)]
        R[ck] += R[p] * mu * rho
        parents_of.setdefault(ck, []).append((p, mu * rho))
SUP = {n: [k for k in levels[n] if R[k] > 1e-300]
       for n in range(3, NMAX + 1)}

for n in (5, 6, 7):
    par = SUP[n]; chd = SUP[n + 1]
    X = {p: math.log(R[p]) for p in par}
    muX = float(np.mean([X[p] for p in par]))
    s2 = float(np.var([X[p] for p in par]))
    D = O = Woff = B = 0.0
    ms, ds, dhat, lnnu = [], [], [], []
    nch = 0
    for c in chd:
        contribs = parents_of.get(c, [])
        tot = sum(R[p] * w for p, w in contribs)
        if tot <= 0: continue
        nch += 1
        sh = [(p, R[p] * w / tot) for p, w in contribs]
        m = sum(s * X[p] for p, s in sh)
        ms.append(m)
        L = math.log(R[c])
        ds.append(L - m)
        dhat.append(math.log(sum(w for _, w in contribs)))
        nu_inv = sum(s * s for _, s in sh)
        lnnu.append(-math.log(nu_inv))
        D += sum(s * s * (X[p] - muX) ** 2 for p, s in sh)
        for i, (p, sp) in enumerate(sh):
            for j, (q, sq) in enumerate(sh):
                if i != j:
                    O += sp * sq * (X[p] - muX) * (X[q] - muX)
                    Woff += sp * sq
    D /= nch; O /= nch; Woff /= nch
    mbar = float(np.mean(ms))
    B = (mbar - muX) ** 2
    Vm = float(np.var(ms))
    g_meas = Vm / s2
    g_ident = (D + O - B) / s2
    rho_sib = O / (s2 * Woff) if Woff > 0 else float("nan")
    Einv = D / s2 / (1 - Woff) if False else None
    Einvnu = float(np.mean([math.exp(-x) for x in lnnu]))
    rho_pred = 1 - (1 - g_meas) / (1 - Einvnu) if Einvnu < 1 else float("nan")
    log(f"== L1 at {n}->{n+1} ==")
    log(f"  sigma^2 = {s2:.3f}  g_measured = {g_meas:.3f}  "
        f"g_identity = {g_ident:.3f}  (exactness check)")
    log(f"  D/s2 = {D/s2:.3f}  (E[1/nu] = {Einvnu:.3f})   "
        f"O/s2 = {O/s2:.3f}   B/s2 = {B/s2:.4f}")
    log(f"  rho_sib measured = {rho_sib:.3f}   tree-model predicted "
        f"= {rho_pred:.3f}")
    # L2
    ds = np.array(ds); dh = np.array(dhat); ln_nu = np.array(lnnu)
    v_meas = float(np.var(ds))
    corr1 = float(np.corrcoef(ds, dh)[0, 1])
    A2 = np.vstack([dh, np.ones(len(dh))]).T
    (sl, ic), *_ = np.linalg.lstsq(A2, ds, rcond=None)
    resid = ds - (A2 @ [sl, ic])
    log(f"== L2 at {n}->{n+1} ==")
    log(f"  v = Var(delta) = {v_meas:.3f}   Var(delta_hat) = "
        f"{float(np.var(dh)):.3f}   corr(delta, delta_hat) = {corr1:.3f}")
    log(f"  regression delta ~ delta_hat: slope = {sl:.3f}  "
        f"R^2 = {1 - float(np.var(resid))/v_meas:.3f}  "
        f"residual var = {float(np.var(resid)):.3f}")
    A3 = np.vstack([dh, ln_nu, np.ones(len(dh))]).T
    coef, *_ = np.linalg.lstsq(A3, ds, rcond=None)
    res3 = ds - A3 @ coef
    log(f"  two-predictor (delta_hat, ln nu): coeffs = "
        f"({coef[0]:.3f}, {coef[1]:.3f})  R^2 = "
        f"{1 - float(np.var(res3))/v_meas:.3f}")
log("DONE")
