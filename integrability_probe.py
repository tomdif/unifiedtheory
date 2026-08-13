#!/usr/bin/env python3
"""INTEGRABILITY PROBE: is the Born chain an exponentially tilted
Plancherel measure?

Motivation (user-referee note 2026-08-13): a TW-consistent skew at one
size is phenomenology; only EXACT structure (RSK/Schur/determinantal)
could transfer into the RH program.  The sharpest computable question:
the uniform-PERMUTATION measure on 2-orders is the integrable/BDJ case
(RSK -> Plancherel -> discrete Airy); our Born chain is measurably NOT
it (mean height 6.91 vs ~7.5; the uniform-DOWNSET chain is not it
either, skew +0.65).  If

    ln [ P_Born(C) / P_Plancherel(C) ]  =  alpha + beta S(C)   (+ ...)

EXACTLY (affine in the BD action, possibly plus one more local
invariant), then the Born measure is a tilted Schur-type measure and
the determinantal toolkit transfers with a potential.  Tests, all
exact at n <= 8:

  P1: TV distance between Born-class measure (class-max-ent DP, W
      channel) and Plancherel-class measure (perm counts / n!).
  P2: affine-tilt fit: regress ln ratio on S(C); report R^2 and max
      residual; then add #minima and #links as covariates - EXACTNESS
      means residuals at machine precision; approximate tilt means
      small but nonzero.
  P3: height marginals: exact Born height law at n = 8 vs exact LIS
      distribution over S_8 (and the uniform-downset chain's) - the
      fluctuation-class comparison at distribution level, no moments.

Readings: (i) EXACT tilt (residual < 1e-10): integrable transfer -
major; (ii) approximate tilt (R^2 > 0.95, residuals ~ 0.1): tilted-
Plancherel is the right coordinate system, exactness fails - pursue
which invariant closes it; (iii) no fit: Born measure is structurally
far from the Schur world; TW-consistency (if hardened) would then be
universality-class luck, not integrability.
"""
import math
from itertools import permutations
import numpy as np

src = open("pi4_first_prediction.py").read()
head = src[:src.index('log("=== pi/4 feasibility')]
exec(head)
FORBID = set()

# Born measure via class-max-ent DP (as committed)
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
W = {root: 1.0}
for k in allkeys:
    if k != root: W[k] = 0.0
for p in allkeys:
    for ck, (mu, g) in children.get(p, {}).items():
        if (p, ck) not in law: continue
        rho, gg, muc = law[(p, ck)]
        W[ck] += W[p] * mu * rho * rho

# Plancherel-class measure: canon class of each permutation's 2-order
def perm_class(perm):
    n = len(perm)
    rel = tuple(sorted((i, j) for i in range(n) for j in range(n)
                       if i < j and perm[i] < perm[j]))
    return canon_fast(n, rel)

S0 = {k: action(levels[nelem(k)][k][1], nelem(k)) for k in allkeys}

def class_obs(key):
    m, rel = key
    below = [set() for _ in range(m)]; above = [set() for _ in range(m)]
    for a_, b_ in rel:
        below[b_].add(a_); above[a_].add(b_)
    minima = sum(1 for x in range(m) if not below[x])
    links = sum(1 for a_, b_ in rel if not (below[b_] & above[a_]))
    height = 0
    hh = [1] * m
    order = sorted(range(m), key=lambda x: len(below[x]))
    for x in order:
        hh[x] = 1 + max([hh[y] for y in below[x]] + [0])
    return minima, links, max(hh)

for n in (5, 6, 7, 8):
    counts = {}
    for perm in permutations(range(n)):
        c = perm_class(perm)
        counts[c] = counts.get(c, 0) + 1
    tot = math.factorial(n)
    plan = {c: v / tot for c, v in counts.items()}
    wtot = sum(W[k] for k in levels[n])
    born = {k: W[k] / wtot for k in levels[n] if W[k] > 0}
    # P1: TV
    allc = set(plan) | set(born)
    tv = 0.5 * sum(abs(plan.get(c, 0.0) - born.get(c, 0.0)) for c in allc)
    # support comparison
    only_p = sum(1 for c in plan if c not in born)
    only_b = sum(1 for c in born if c not in plan)
    log(f"== n={n}: classes plan={len(plan)} born={len(born)} "
        f"(plan-only {only_p}, born-only {only_b})  TV = {tv:.4f} ==")
    # P2: tilt fit on common support
    common = [c for c in plan if c in born]
    lr = np.array([math.log(born[c] / plan[c]) for c in common])
    Svals = np.array([S0[c] for c in common], float)
    obs = np.array([class_obs(c) for c in common], float)
    for name, Xc in (("S only", [Svals]),
                     ("S+minima+links", [Svals, obs[:, 0], obs[:, 1]])):
        X = np.vstack(Xc + [np.ones(len(common))]).T
        beta, *_ = np.linalg.lstsq(X, lr, rcond=None)
        res = lr - X @ beta
        ss = 1 - np.var(res) / np.var(lr) if np.var(lr) > 0 else 1.0
        log(f"   tilt fit [{name}]: R^2 = {ss:.4f}  max|resid| = "
            f"{np.max(np.abs(res)):.4f}  beta_S = {beta[0]:+.4f}")
    # P3 at n=8: height marginals
    if n == 8:
        hp = {}; hb = {}; hu = {}
        # uniform-downset chain for contrast
        U = {root: 1.0}
        for k in allkeys:
            if k != root: U[k] = 0.0
        Ktot = {p: sum(mu for _, (mu, g) in children[p].items())
                for p in allkeys if p in children}
        for p in allkeys:
            for ck, (mu, g) in children.get(p, {}).items():
                U[ck] += U[p] * mu / Ktot[p]
        for c in levels[n]:
            h = class_obs(c)[2]
            hb[h] = hb.get(h, 0) + born.get(c, 0.0)
            hu[h] = hu.get(h, 0) + U[c]
        for c, pv in plan.items():
            h = class_obs(c)[2]
            hp[h] = hp.get(h, 0) + pv
        log("   height marginal at n=8 (h: Plancherel / Born / "
            "uniform-downset):")
        for h in sorted(set(hp) | set(hb) | set(hu)):
            log(f"     h={h}: {hp.get(h,0):.4f} / {hb.get(h,0):.4f} / "
                f"{hu.get(h,0):.4f}")
        tvh = 0.5 * sum(abs(hp.get(h, 0) - hb.get(h, 0))
                        for h in set(hp) | set(hb))
        log(f"   height-marginal TV(Born, Plancherel) = {tvh:.4f}")
log("DONE")
