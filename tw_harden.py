#!/usr/bin/env python3
"""HARDENING THE TRACY-WIDOM RESULT: three signatures, four sizes.

Registered readings:
 (i) HARDENED: skew(n) stable ~0.22 across n = 20..40; multinomial
     Delta-LL favors TW over Gaussian at every size; fluctuation
     exponent chi in [0.08, 0.28] (KPZ 1/6 = 0.167, Gaussian 0.5
     excluded): class membership upgraded to three-signature.
 (ii) MIXED: skew ok but exponent or LL disagrees - partial.
 (iii) skew drifts away with n: the n=28 hit was finite-size accident.
"""
import math, sys, time
import numpy as np
src = open("arrow_tw_sampler.py").read()
head = src[:src.index("def run(")]
exec(head)
from scipy.stats import gamma as gammadist, norm as normdist

K_TW, TH_TW, AL_TW = 79.6595, 0.101037, 9.81961   # Chiani TW2 approx
TW_MEAN, TW_SD = K_TW*TH_TW - AL_TW, math.sqrt(K_TW)*TH_TW

def sample_heights(quantum, size, npaths, tag):
    globals()['NS'] = size
    hts = []
    t0 = time.time()
    while len(hts) < npaths:
        recs, counts, fin = sample_path(quantum)
        if not recs or max(recs) < size: continue
        hts.append(recs[size][1])
        if time.time() - t0 > 180:
            log(f"  [{tag}] {len(hts)}/{npaths}"); t0 = time.time()
    return np.array(hts, float)

PLAN_Q = [(20, 4000), (28, 4000), (32, 2500), (40, 1200)]
PLAN_C = [(28, 800), (40, 400)]
H = {}
for size, npaths in PLAN_Q:
    log(f"quantum n={size}: {npaths} paths")
    H[f"q{size}"] = sample_heights(True, size, npaths, f"q{size}")
for size, npaths in PLAN_C:
    log(f"classical n={size}: {npaths} paths")
    H[f"c{size}"] = sample_heights(False, size, npaths, f"c{size}")
np.savez("tw_heights.npz", **H)

def moments(h):
    m, sd = h.mean(), h.std()
    sk = float(((h-m)**3).mean()/sd**3)
    ku = float(((h-m)**4).mean()/sd**4 - 3)
    return m, sd, sk, ku

def mll(h, law):
    m, sd = h.mean(), h.std()
    ks = np.arange(h.min()-1, h.max()+2)
    if law == "tw":
        # h = a + b T, moment-matched: b = sd/TW_SD, a = m - b*TW_MEAN
        b = sd/TW_SD; a = m - b*TW_MEAN
        cdf = lambda x: gammadist.cdf((x - a)/b + AL_TW, K_TW, scale=TH_TW)
    else:
        cdf = lambda x: normdist.cdf(x, m, sd)
    ll = 0.0
    for k in ks:
        p = max(cdf(k+0.5) - cdf(k-0.5), 1e-300)
        ll += (h == k).sum() * math.log(p)
    return ll

log("== signature (a): skew stability ==")
for size, _ in PLAN_Q:
    h = H[f"q{size}"]
    m, sd, sk, ku = moments(h)
    se = math.sqrt(6/len(h))
    log(f"  n={size}: N={len(h)} mean={m:.3f} sd={sd:.3f} "
        f"skew={sk:+.4f}+-{se:.3f} (z_TW {(sk-0.2241)/se:+.2f}, "
        f"z_0 {sk/se:+.2f})  ex-kurt={ku:+.3f}")
for size, _ in PLAN_C:
    h = H[f"c{size}"]
    m, sd, sk, ku = moments(h)
    log(f"  CLASSICAL n={size}: skew={sk:+.4f}+-{math.sqrt(6/len(h)):.3f}")

log("== signature (b): multinomial LL, TW vs Gaussian ==")
for size, _ in PLAN_Q:
    h = H[f"q{size}"]
    dll = mll(h, "tw") - mll(h, "gauss")
    log(f"  n={size}: Delta-LL(TW - Gauss) = {dll:+.2f} "
        f"({1000*dll/len(h):+.1f} per 1000 samples)")
for size, _ in PLAN_C:
    h = H[f"c{size}"]
    dll = mll(h, "tw") - mll(h, "gauss")
    log(f"  CLASSICAL n={size}: Delta-LL = {dll:+.2f}")

log("== signature (c): fluctuation exponent sd ~ n^chi ==")
ns = np.array([s for s, _ in PLAN_Q], float)
sds = np.array([H[f"q{s}"].std() for s, _ in PLAN_Q])
A2 = np.vstack([np.log(ns), np.ones(len(ns))]).T
(chi, c0), *_ = np.linalg.lstsq(A2, np.log(sds), rcond=None)
log(f"  sd: " + "  ".join(f"n={int(s)}:{H[f'q{int(s)}'].std():.3f}"
    for s, _ in PLAN_Q))
log(f"  chi = {chi:.3f}  (KPZ 1/6 = 0.167; additive-Gaussian 0.5)")
means = np.array([H[f"q{s}"].mean() for s, _ in PLAN_Q])
(bm, cm), *_ = np.linalg.lstsq(A2, np.log(means), rcond=None)
log(f"  mean-height exponent = {bm:.3f} (2D longest-chain 1/2)")
log("DONE")
