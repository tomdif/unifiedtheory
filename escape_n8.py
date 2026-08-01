#!/usr/bin/env python3
"""The n = 8 escape: refutation test of the blocking lemma.

PER-ELEMENT CRITERION (the tool): a causet is hereditarily real iff
every element z satisfies sum_k Delta_k(z) c_k in Z, where
Delta_k(z) = #{x < z with exactly k elements strictly between}.
(Every link's interval lies in the past of its top, so a downset's
phase is the sum of its members' jumps; conversely jumps are
differences of downset phases.)

ANALYTIC CONSTRUCTIONS (to be machine-checked here):
  FAN-CHAIN (n=8):  x1..x4 < t3 < t2 < t1 < apex (x's below all).
    apex jump: 4*c3 + c2 + c1 = -9/2 - 1/2 - 1 = -6 in Z; t1 jump has
    Delta_2 = 4 even; all others trivial.  Four interval-3 links,
    N2 = 5 odd: the referee's N3=4/N2-odd escape branch, populated at
    the FIRST size beyond exhaustive verification.  Contains the
    5-chain x < t3 < t2 < t1 < apex: HEIGHT 5.
  FAN-V (n=8): same but t1, t2 incomparable above t3 (apex jump
    4*c3 + c2 = -5): height 4 variant.
  K_{8,3}+apex (n=12): pure layer-3 escape, jump 8*c3 = -9.

PRE-REGISTERED READINGS:
  (a) depth-8 gate survivors == hereditary-real at n = 8 AND the
      fan-chain survives -> blocking lemma FALSE; the height <= 4
      ('arrested time') cap is an n <= 7 finite-size phenomenon,
      broken at n = 8; Paper 1 / DUST notes corrected on the record.
  (b) fan-chain predicate-real but gate-DEAD -> first divergence of
      funding from phase arithmetic; hereditary reality is necessary
      but not sufficient at depth 8 — a new mechanism, report as such.
Gate: tree n <= 8 (16999 at level 8; A000112-validated), equations
n <= 7, exact dyadic phases, LP + proven-death removal loops.
"""
import itertools, math
from fractions import Fraction
import numpy as np
from scipy.optimize import linprog

src = open("resonant_sector_scan.py").read()
cut = src.index("NMAX = 7")
exec(src[:cut])          # W_exact (2D), canon_fast

NMAX = 8
levels = {1: {canon_fast(1, ()): (1, ())}}
for n in range(1, NMAX):
    nxt = {}
    for key, (m, rel) in levels[n].items():
        below = {x: {a for (a, b) in rel if b == x} for x in range(m)}
        for mask in range(1 << m):
            D = [i for i in range(m) if mask >> i & 1]
            if not all(below[x] <= set(D) for x in D): continue
            nr = tuple(sorted(set(rel) | {(d, m) for d in D}))
            nxt[canon_fast(m + 1, nr)] = (m + 1, nr)
    levels[n + 1] = nxt
counts = {n: len(v) for n, v in levels.items()}
print("causets per level:", counts, flush=True)
assert [counts[i] for i in range(1, 9)] == [1, 2, 5, 16, 63, 318, 2045, 16999], \
    "A000112 validation FAILED at depth 8"
root = canon_fast(1, ())
allkeys = [key for n in range(1, NMAX + 1) for key in sorted(levels[n])]
def nelem(key): return key[0]

eps, q = Fraction(1, 4), 4
W = {k: W_exact(k, eps) for k in range(0, NMAX)}
linkang = {k: (-W[k] * 2 * q) % 2 for k in W}

def link_ks(rel, m):
    relset = set(rel)
    return [sum(1 for z in range(m) if (a, z) in relset and (z, b) in relset)
            for (a, b) in rel]

def hereditary_real(key):
    """Per-element criterion: every element's jump sum integral."""
    m, rel = key
    relset = set(rel)
    for z in range(m):
        tot = Fraction(0)
        for (a, b) in rel:
            if b != z: continue
            k = sum(1 for w in range(m)
                    if (a, w) in relset and (w, z) in relset)
            tot += linkang[k]
        if tot % 1 != 0: return False
    return True

# ---- machine-check the constructions --------------------------------------
def mk(rel, m): return canon_fast(m, tuple(sorted(rel)))
# fan-chain: 0..3 = x's, 4 = t3, 5 = t2, 6 = t1, 7 = apex  (a,b) = a below b
fanchain = []
for x in range(4):
    fanchain += [(x, 4), (x, 5), (x, 6), (x, 7)]
fanchain += [(4, 5), (4, 6), (4, 7), (5, 6), (5, 7), (6, 7)]
FC = mk(fanchain, 8)
# fan-V: t1,t2 incomparable above t3
fanv = []
for x in range(4):
    fanv += [(x, 4), (x, 5), (x, 6), (x, 7)]
fanv += [(4, 5), (4, 6), (4, 7), (5, 7), (6, 7)]
FV = mk(fanv, 8)
def height(rel, m):
    if not rel: return 1
    succ = {v: [b for (a, b) in rel if a == v] for v in range(m)}
    memo = {}
    def h(v):
        if v not in memo:
            memo[v] = 1 + max((h(w) for w in succ[v]), default=0)
        return memo[v]
    return max(h(v) for v in range(m))
from collections import Counter
for name, K in (("FAN-CHAIN", FC), ("FAN-V", FV)):
    ks = Counter(link_ks(K[1], K[0]))
    print(f"{name}: n={K[0]} height={height(K[1], K[0])} "
          f"k-census={dict(ks)} hereditary-real={hereditary_real(K)}",
          flush=True)

# ---- predicate census at n = 8 --------------------------------------------
pred = set()
esc = []
for n in range(1, NMAX + 1):
    for key in sorted(levels[n]):
        if hereditary_real(key):
            pred.add(key)
            ks = link_ks(key[1], key[0])
            if any(k >= 3 for k in ks): esc.append(key)
per = {n: sum(1 for k in pred if nelem(k) == n) for n in range(1, NMAX + 1)}
print(f"hereditary-real per level: {per}", flush=True)
print(f"ESCAPEES (k>=3 links, predicate-real): {len(esc)}")
for k in esc[:10]:
    print(f"   n={k[0]} h={height(k[1], k[0])} "
          f"census={dict(Counter(link_ks(k[1], k[0])))}")
h5 = [k for k in pred if height(k[1], k[0]) >= 5]
print(f"height>=5 predicate-real causets: {len(h5)}", flush=True)

# ---- the depth-8 gate ------------------------------------------------------
def S_angle(rel, m):
    ang = (Fraction(m) * 2 * q) % 2
    for k in link_ks(rel, m):
        ang = (ang + linkang[k]) % 2
    return ang
children = {}
for n in range(1, NMAX):
    for key, (m, rel) in sorted(levels[n].items()):
        below = {x: {a for (a, b) in rel if b == x} for x in range(m)}
        SA = S_angle(rel, m)
        kid = {}
        for mask in range(1 << m):
            D = [i for i in range(m) if mask >> i & 1]
            if not all(below[x] <= set(D) for x in D): continue
            nr = tuple(sorted(set(rel) | {(d, m) for d in D}))
            ck = canon_fast(m + 1, nr)
            gang = (S_angle(nr, m + 1) - SA) % 2
            if ck in kid:
                mu, gg = kid[ck]; kid[ck] = (mu + 1, gg)
            else: kid[ck] = (1, gang)
        children[key] = kid
print("children built", flush=True)
def cph(ang):
    a = float(ang) * np.pi
    return complex(np.cos(a), np.sin(a))
def descendants(seed):
    out = set(seed); frontier = list(seed)
    while frontier:
        k = frontier.pop()
        for ck in children.get(k, {}):
            if ck not in out: out.add(ck); frontier.append(ck)
    return out
U = set(allkeys)
for rnd in range(200):
    kk = sorted(U); ii = {k: i for i, k in enumerate(kk)}
    A_eq, b_eq = [], []
    r0 = np.zeros(len(kk)); r0[ii[root]] = 1
    A_eq.append(r0); b_eq.append(1.0)
    for key in kk:
        if nelem(key) >= NMAX: continue
        rr = np.zeros(len(kk)); ri = np.zeros(len(kk))
        rr[ii[key]] -= 1
        for ck, (mu, g) in children[key].items():
            if ck not in U: continue
            z = mu * cph(g)
            rr[ii[ck]] += z.real; ri[ii[ck]] += z.imag
        A_eq.append(rr); b_eq.append(0.0); A_eq.append(ri); b_eq.append(0.0)
    A_eq = np.array(A_eq); b_eq = np.array(b_eq)
    cobj = np.zeros(len(kk))
    for key in U:
        if nelem(key) >= 6: cobj[ii[key]] = -1.0
    res = linprog(cobj, A_eq=A_eq, b_eq=b_eq, bounds=[(0, 1000)] * len(kk),
                  method="highs")
    if not res.success:
        print("root infeasible"); U = set(); break
    Av = {k: res.x[ii[k]] for k in kk}
    dead = set()
    for key in kk:
        if Av[key] > 1e-9: continue
        c2o = np.zeros(len(kk)); c2o[ii[key]] = -1.0
        r2 = linprog(c2o, A_eq=A_eq, b_eq=b_eq, bounds=[(0, 1000)] * len(kk),
                     method="highs")
        if (not r2.success) or -r2.fun < 1e-9: dead.add(key)
    print(f"round {rnd}: support {len(U)}, proven dead this round {len(dead)}",
          flush=True)
    if not dead: break
    U = U - descendants(dead)
    if root not in U:
        U = set(); break

perU = {n: sum(1 for k in U if nelem(k) == n) for n in range(1, NMAX + 1)}
print(f"\nGATE survivors per level: {perU}")
print(f"gate == hereditary-real: {U == pred}")
if U != pred:
    print(f"   pred-only: {len(pred - U)}, gate-only: {len(U - pred)}")
    for k in sorted(pred - U)[:6]:
        print(f"   pred-only: n={k[0]} census="
              f"{dict(Counter(link_ks(k[1], k[0])))}")
print(f"FAN-CHAIN survives gate: {FC in U}")
print(f"FAN-V survives gate: {FV in U}")
print(f"height>=5 gate survivors: "
      f"{sum(1 for k in U if height(k[1], k[0]) >= 5)}")
print("DONE", flush=True)
