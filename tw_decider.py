#!/usr/bin/env python3
"""THE n=56-64 DECIDER: accelerated universality vs sub-TW drift.
Readings registered in TW_HARDENED.md / commit message."""
import math, sys, time
import numpy as np
src = open("arrow_tw_sampler.py").read()
head = src[:src.index("def run(")]
exec(head)
from bisect import bisect_left

def sample_heights(quantum, size, npaths, tag):
    globals()['NS'] = size
    hts = []
    t0 = time.time()
    while len(hts) < npaths:
        recs, counts, fin = sample_path(quantum)
        if not recs or max(recs) < size: continue
        hts.append(recs[size][1])
        if time.time() - t0 > 240:
            log(f"  [{tag}] {len(hts)}/{npaths}"); t0 = time.time()
    return np.array(hts, float)

def stats(h, tag, ref=None):
    m, sd = h.mean(), h.std()
    sk = float(((h-m)**3).mean()/sd**3)
    ku = float(((h-m)**4).mean()/sd**4 - 3)
    se = math.sqrt(6/len(h))
    line = (f"  {tag}: N={len(h)} mean={m:.3f} sd={sd:.3f} "
            f"skew={sk:+.4f}+-{se:.3f} exkurt={ku:+.3f}")
    if ref is not None:
        line += (f"  [z_TW {(sk-0.2241)/se:+.2f}  z_Plan "
                 f"{(sk-ref)/se:+.2f}  z_0 {sk/se:+.2f}]")
    log(line)
    return sk, se

def lis(perm):
    tails = []
    for x in perm:
        i = bisect_left(tails, x)
        if i == len(tails): tails.append(x)
        else: tails[i] = x
    return len(tails)

log("Plancherel finite-size references")
plan_ref = {}
for n in (56, 64):
    vals = np.array([lis(rng.permutation(n)) for _ in range(120000)], float)
    sk = float(((vals-vals.mean())**3).mean()/vals.std()**3)
    plan_ref[n] = sk
    log(f"  uniform-permutation LIS n={n}: skew {sk:+.4f}")

log("quantum n=56: 2000 paths")
h56 = sample_heights(True, 56, 2000, "q56")
np.savez("tw_decider_heights.npz", q56=h56)
sk56, se56 = stats(h56, "QUANTUM n=56", plan_ref[56])
log("classical n=56: 300 paths")
c56 = sample_heights(False, 56, 300, "c56")
stats(c56, "CLASSICAL n=56")
log("quantum n=64: 700 paths")
h64 = sample_heights(True, 64, 700, "q64")
np.savez("tw_decider_heights.npz", q56=h56, q64=h64, c56=c56)
sk64, se64 = stats(h64, "QUANTUM n=64", plan_ref[64])
log("== DECIDER ==")
log(f"  trajectory: 0.378(20) 0.281(28) 0.196(32) 0.209(40) "
    f"{sk56:.3f}(56) {sk64:.3f}(64)")
if abs(sk56 - 0.2241) < 2*se56 and sk56 - plan_ref[56] < -2*se56:
    log("  reading (i): ACCELERATED UNIVERSALITY - on TW asymptote, "
        "below the integrable finite-size curve")
elif sk56 < 0.15 and sk64 < sk56:
    log("  reading (ii): SUB-TW DRIFT - distinct law")
else:
    log("  reading (iii)/mixed - report trajectory")
log("DONE")
