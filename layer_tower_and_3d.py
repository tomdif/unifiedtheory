#!/usr/bin/env python3
"""A: the layer tower at 2D eps=1/4, phi=8pi (referee's mod-64 extension).
B: the 3D {2,5}-adic gate at eps=1/5, phi=10pi (referee's cheap 3D test).

A — THE MODULUS IS A TOWER.  From madic_numerator each layer k adds a
term c_k with denominator dividing m^(k+1); the k <= 3 predicate is a
truncation.  At eps = 1/4, phi = 8pi the referee's layer-4 congruence
32N2 + 8N3 + 17N4 = 0 (mod 64) is verified (17 a unit mod 64 forces
N4 = 0 mod 8), and the ladder continues: N3 = 0 (4), N4 = 0 (8),
N5 = 0 (4).  Reachability scan: max N4 and N5 over all 2045
seven-element causets — the N3 = 4 escape branch needs N4 in {0, 8+},
and n <= 7 cannot come close, further pruning the blocking-lemma
counterexample space.

B — 3D COEFFICIENTS (Dowker–Glaser 1305.2588, Table 1):
C^(3) = (1, -27/8, 9/4), three layers, prefactor beta3/|alpha3| = 1
(Table 2).  Cross-checks: 2D/4D rows match (1,-2,1)/(1,-9,16,-8);
W1 = eps(1 - 35 eps/8) reproduces from C2 = -27/8.  Common
denominator D = 8 -> primes {2}: the m-adic law predicts 3D webs
carry 2-adic structure at EVERY m (and Table 1 shows all odd d have
2-power D: 16 in 5D, 128 in 7D — the prediction is odd-dimensional,
not 3D-specific).  At m = 5: 2D gives purely 5-adic contributions
(2/5, 46/25, ...) while 3D gives c1 = -1/4 (pure 2-adic!),
c2 = 7/10 (mixed), c3 = 142/125 — a qualitative dimensional
difference.

PRE-REGISTERED (B): (i) the 3D eps=1/5 phi=10pi gate returns
survivors == hereditary-real (set equality, as at all five previous
resonances); (ii) the realized moduli mix primes 2 and 5 (N1 enters
mod 4 from c1 = -1/4 — e.g. a single k=1 link with everything else
neutral is dead in 3D at m=5, where 2D at m=5 killed it mod 5);
(iii) nonemptiness (dust at minimum).  NOTE the law itself states
only where moduli live; nonemptiness is a separate claim for which
each gate is a data point.
"""
import itertools, math
from fractions import Fraction
from functools import reduce
import numpy as np
from scipy.optimize import linprog

src = open("resonant_sector_scan.py").read()
cut = src.index("def run_point")
exec(src[:cut])   # canon_fast, levels, counts, root, allkeys, NMAX, W_exact(2D)

def nelem(key): return key[0]

def link_ks(rel, m):
    relset = set(rel)
    return [sum(1 for z in range(m) if (a, z) in relset and (z, b) in relset)
            for (a, b) in rel]

# ---- A: tower + reachability ----------------------------------------------
eps2, q2 = Fraction(1, 4), 4
print("A. Layer tower at 2D eps=1/4, phi=8pi:")
cs = {k: (-W_exact(k, eps2) * 2 * q2) % 2 for k in range(0, 9)}
def lcm(a, b): return a * b // math.gcd(a, b)
for K in (3, 4, 5):
    L = reduce(lcm, [cs[k].denominator for k in range(1, K + 1)])
    coeffs = {k: int((cs[k] * L) % (2 * L)) for k in range(1, K + 1)}
    g_low = reduce(math.gcd, [coeffs[k] for k in range(1, K)] + [2 * L])
    forced = g_low // math.gcd(coeffs[K], g_low)
    print(f"   layers<={K}: sum a_k N_k = 0 (mod {2*L}), a = {coeffs}"
          f"  -> N_{K} = 0 (mod {forced})")
maxN = {4: 0, 5: 0}
argm = {}
for key in sorted(levels[7]):
    ks = link_ks(key[1], key[0])
    for kk in (4, 5):
        c = sum(1 for k in ks if k == kk)
        if c > maxN[kk]: maxN[kk] = c; argm[kk] = key
print(f"   reachability at n=7: max N4 = {maxN[4]}, max N5 = {maxN[5]} "
      f"(vs N4 = 8 required for the escape branch)")

# ---- B: 3D gate ------------------------------------------------------------
C3 = [Fraction(1), Fraction(-27, 8), Fraction(9, 4)]
def W3(k, eps):
    x = eps / (1 - eps)
    tot = sum(C3[i] * math.comb(k, i) * x**i for i in range(3))
    return eps * (1 - eps)**k * tot     # prefactor beta3/|alpha3| = 1

# sanity: W1 = eps(1 - 35 eps/8)
e = Fraction(1, 7)
assert W3(1, e) == e * (1 - Fraction(35, 8) * e), "3D W1 cross-check failed"
print("\nB. 3D gate at eps=1/5, phi=10pi (C3 = 1, -27/8, 9/4; pref 1):")
eps3, q3 = Fraction(1, 5), 5
linkang = {k: (-W3(k, eps3) * 2 * q3) % 2 for k in range(0, NMAX)}
print("   per-link c_k (pi units): " +
      ", ".join(f"k={k}: {linkang[k]} (den {linkang[k].denominator})"
                for k in range(0, 5)))
def S_angle(rel, m):
    ang = (Fraction(m) * 2 * q3) % 2
    for k in link_ks(rel, m):
        ang = (ang + linkang[k]) % 2
    return ang
def hereditary_real(key):
    m, rel = key
    ks = link_ks(rel, m)
    below = {x: {a for (a, b) in rel if b == x} for x in range(m)}
    for mask in range(1 << m):
        D = set(i for i in range(m) if mask >> i & 1)
        if not D or not all(below[x] <= D for x in D): continue
        ang = (Fraction(len(D)) * 2 * q3) % 2
        for (a, b), k in zip(rel, ks):
            if b in D and a in D: ang = (ang + linkang[k]) % 2
        if ang != 0 and ang != 1: return False
    return True
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
for rnd in range(80):
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
        if nelem(key) >= 5: cobj[ii[key]] = -1.0
    res = linprog(cobj, A_eq=A_eq, b_eq=b_eq, bounds=[(0, 1000)] * len(kk),
                  method="highs")
    if not res.success: U = set(); break
    Av = {k: res.x[ii[k]] for k in kk}
    dead = set()
    for key in kk:
        if Av[key] > 1e-9: continue
        c2o = np.zeros(len(kk)); c2o[ii[key]] = -1.0
        r2 = linprog(c2o, A_eq=A_eq, b_eq=b_eq, bounds=[(0, 1000)] * len(kk),
                     method="highs")
        if (not r2.success) or -r2.fun < 1e-9: dead.add(key)
    if not dead: break
    U = U - descendants(dead)
per = {}
for key in U: per[nelem(key)] = per.get(nelem(key), 0) + 1
print(f"   gate survivors: {len(U)}  [" +
      "  ".join(f"n={n}:{per.get(n,0)}/{counts[n]}"
                for n in range(1, NMAX + 1)) + "]")
pred = {key for n in range(1, NMAX + 1) for key in sorted(levels[n])
        if hereditary_real(key)}
print(f"   hereditary-real predicate: {len(pred)}; EQUAL: {pred == U}")
# 2-adic witness: is the single-k1-link causet (3-chain) dead, and WHY:
chain3 = canon_fast(3, ((1, 0), (2, 0), (2, 1)))
print(f"   3-chain (N1=1) alive: {chain3 in U}   "
      f"[c1 = {linkang[1]} -> 2-adic kill, vs mod-5 kill in 2D at m=5]")
def height(rel, m):
    if not rel: return 1
    succ = {v: [b for (a, b) in rel if a == v] for v in range(m)}
    memo = {}
    def h(v):
        if v not in memo:
            memo[v] = 1 + max((h(w) for w in succ[v]), default=0)
        return memo[v]
    return max(h(v) for v in range(m))
hh, th = {}, {}
for key in allkeys:
    h = height(key[1], key[0]); th[h] = th.get(h, 0) + 1
    if key in U: hh[h] = hh.get(h, 0) + 1
print("   height profile: " + "  ".join(
    f"h={h}:{hh.get(h,0)}/{th[h]}" for h in sorted(th)))
cplx = sum(1 for key in sorted(U) if key in children and nelem(key) < NMAX
           and any(g not in (0, 1) for ck, (mu, g) in children[key].items()
                   if ck in U))
print(f"   surviving equations with complex coefficients: {cplx}")
print("DONE", flush=True)
