#!/usr/bin/env python3
"""B: does the wave gate share the probe's closure blind spot?
C: the broom/dust jurisdiction test at the 4D intersection point.

B — CLOSURE AUDIT OF THE GATE.  The convexity argument: the gate's
pull-up step certifies, for each survivor C, a member with Ã(C) > 0;
the average of those members (the LP feasible set is convex) is a
single member strictly positive on ALL of U; and U is downward-closed
by construction (descendants of proven-dead removed).  A member
positive exactly on a downward-closed set respects support closure.
Hence the gate's counts are exact supports of legitimate members —
the blind spot is confined to slices that FORCE interior zeros (e.g.
factorization).  Mechanical verification: maximize t subject to the
wave equations and Ã(C) >= t for all C in U; t* > 0 exhibits the
strictly positive member directly.  Run at all four 2D resonances.

C — JURISDICTION (pre-registered).  In 4D at eps = 1/4 the
broom-restoring deterministic phases phi = 2*pi*j/(1-eps) = 8*pi*j/3
intersect the resonance family (W0*phi = eps*phi in 2*pi*Z) at j = 3:
phi = 8*pi.  Both mechanisms claim this point.  4D per-link
contributions there (weights eps*f_4, C = (1,-9,16,-8)):
c1 = 3 (sign, real), c2 = 29/8, c3 = 5/2, ... — so the congruence
machinery predicts: antichains (all-neutral) LIVE; 5-chains (N3 = 1,
half-integer) DIE; broom-class era structures die when their N2/N3
census violates 29*N2/8 + 5*N3/2 + ... integrality.  READINGS:
dust in / broom out  -> both theorems consistent; broom-restoration
is scoped to non-resonant deterministic phases (the physband_n7 band
points have j*eps/(1-eps) not integer, so no retroactive conflict).
broom in            -> the congruence machinery is WRONG in 4D.
dust out            -> the resonance analysis is WRONG.
"""
import itertools, math
from fractions import Fraction
import numpy as np
from scipy.optimize import linprog

src = open("resonant_sector_scan.py").read()
cut = src.index("def run_point")
exec(src[:cut])   # canon_fast, levels, counts, root, allkeys, W_exact(2D), NMAX

def nelem(key): return key[0]

def link_ks(rel, m):
    relset = set(rel)
    return [sum(1 for z in range(m) if (a, z) in relset and (z, b) in relset)
            for (a, b) in rel]

C4 = [1, -9, 16, -8]
def W4_exact(k, eps):
    x = eps / (1 - eps)
    tot = sum(Fraction(C4[i-1]) * math.comb(k, i-1) * x**(i-1)
              for i in range(1, 5))
    return eps * (1 - eps)**k * tot

def build_and_gate(Wfun, eps, q, nmax, minamp=False):
    W = {k: Wfun(k, eps) for k in range(0, nmax)}
    linkang = {k: (-W[k] * 2 * q) % 2 for k in W}
    def S_angle(rel, m):
        ang = (Fraction(m) * 2 * q) % 2
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
            ang = (Fraction(len(D)) * 2 * q) % 2
            for (a, b), k in zip(rel, ks):
                if b in D and a in D: ang = (ang + linkang[k]) % 2
            if ang != 0 and ang != 1: return False
        return True
    lv = {n: levels[n] for n in range(1, nmax + 1)}
    children = {}
    for n in range(1, nmax):
        for key, (m, rel) in sorted(lv[n].items()):
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
    keys = [key for n in range(1, nmax + 1) for key in sorted(lv[n])]
    U = set(keys)
    for rnd in range(80):
        kk = sorted(U); ii = {k: i for i, k in enumerate(kk)}
        A_eq, b_eq = [], []
        r0 = np.zeros(len(kk)); r0[ii[root]] = 1
        A_eq.append(r0); b_eq.append(1.0)
        for key in kk:
            if nelem(key) >= nmax: continue
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
            if nelem(key) >= nmax - 2: cobj[ii[key]] = -1.0
        res = linprog(cobj, A_eq=A_eq, b_eq=b_eq,
                      bounds=[(0, 1000)] * len(kk), method="highs")
        if not res.success: return set(), None, children, hereditary_real
        Av = {k: res.x[ii[k]] for k in kk}
        dead = set()
        for key in kk:
            if Av[key] > 1e-9: continue
            c2o = np.zeros(len(kk)); c2o[ii[key]] = -1.0
            r2 = linprog(c2o, A_eq=A_eq, b_eq=b_eq,
                         bounds=[(0, 1000)] * len(kk), method="highs")
            if (not r2.success) or -r2.fun < 1e-9: dead.add(key)
        if not dead: break
        U = U - descendants(dead)
        if root not in U: return set(), None, children, hereditary_real
    tstar = None
    if minamp and U:
        # max t s.t. equations hold and A(C) >= t for all C in U
        kk = sorted(U); ii = {k: i for i, k in enumerate(kk)}
        nv = len(kk) + 1                      # last var = t
        A_eq, b_eq = [], []
        r0 = np.zeros(nv); r0[ii[root]] = 1
        A_eq.append(r0); b_eq.append(1.0)
        for key in kk:
            if nelem(key) >= nmax: continue
            rr = np.zeros(nv); ri = np.zeros(nv)
            rr[ii[key]] -= 1
            for ck, (mu, g) in children[key].items():
                if ck not in U: continue
                z = mu * cph(g)
                rr[ii[ck]] += z.real; ri[ii[ck]] += z.imag
            A_eq.append(rr); b_eq.append(0.0); A_eq.append(ri); b_eq.append(0.0)
        A_ub, b_ub = [], []
        for key in kk:                        # t - A(C) <= 0
            row = np.zeros(nv); row[ii[key]] = -1; row[-1] = 1
            A_ub.append(row); b_ub.append(0.0)
        c = np.zeros(nv); c[-1] = -1.0
        r = linprog(c, A_eq=np.array(A_eq), b_eq=np.array(b_eq),
                    A_ub=np.array(A_ub), b_ub=np.array(b_ub),
                    bounds=[(0, 1000)] * len(kk) + [(None, None)],
                    method="highs")
        tstar = -r.fun if r.success else None
    return U, tstar, children, hereditary_real

print("B. Closure audit — strictly positive member (t* > 0 = counts exact):")
for eps, q, label in ((Fraction(1,4), 4, "2D eps=1/4 phi=8pi (1081)"),
                      (Fraction(1,6), 3, "2D eps=1/6 phi=6pi (949)"),
                      (Fraction(1,5), 5, "2D eps=1/5 phi=10pi (258)"),
                      (Fraction(1,4), 2, "2D eps=1/4 phi=4pi (500)")):
    U, tstar, _, _ = build_and_gate(W_exact, eps, q, NMAX, minamp=True)
    print(f"  {label}: survivors {len(U)}, min-amplitude t* = {tstar:.6g} "
          f"-> {'EXACT (positive member exists)' if tstar and tstar > 1e-9 else 'UPPER BOUND ONLY'}",
          flush=True)

print("\nC. 4D jurisdiction gate at eps=1/4, phi=8pi (n <= 6):")
eps4, q4 = Fraction(1, 4), 4
W = {k: W4_exact(k, eps4) for k in range(0, 6)}
print("   4D weights:", {k: str(W[k]) for k in range(4)})
print("   per-link c_k = -2q W(k) mod 2 (pi units):",
      {k: str((-W[k] * 2 * q4) % 2) for k in range(4)})
U4, t4, ch4, hred = build_and_gate(W4_exact, eps4, q4, 6, minamp=True)
per = {}
for key in U4: per[nelem(key)] = per.get(nelem(key), 0) + 1
print(f"   survivors: {len(U4)}  [" +
      "  ".join(f"n={n}:{per.get(n,0)}/{counts[n]}" for n in range(1, 7)) + "]")
pred = {key for key in U4 | set(k for n in range(1, 7)
        for k in sorted(levels[n])) if hred(key)}
pred = {key for n in range(1, 7) for key in sorted(levels[n]) if hred(key)}
print(f"   hereditary-real predicate: {len(pred)}; EQUAL: {pred == U4}")
def height(rel, m):
    if not rel: return 1
    succ = {v: [b for (a, b) in rel if a == v] for v in range(m)}
    memo = {}
    def h(v):
        if v not in memo:
            memo[v] = 1 + max((h(w) for w in succ[v]), default=0)
        return memo[v]
    return max(h(v) for v in range(m))
hh, tot_h = {}, {}
for n in range(1, 7):
    for key in sorted(levels[n]):
        h = height(key[1], key[0]); tot_h[h] = tot_h.get(h, 0) + 1
        if key in U4: hh[h] = hh.get(h, 0) + 1
print("   height profile: " + "  ".join(
    f"h={h}:{hh.get(h,0)}/{tot_h[h]}" for h in sorted(tot_h)))
# dust in?  antichains = height-1 causets
nA_alive = all(any(key in U4 and key[0] == n and not key[1]
               for key in levels[n]) for n in range(1, 7))
# chains: pure m-chains
def chain_key(m):
    rel = tuple(sorted((a, b) for b in range(m) for a in range(b + 1, m)))
    # build chain 0<1<...<m-1 in (below, above) = (a,b) with a below b
    rel = tuple(sorted((a, b) for a in range(m) for b in range(m) if a < b))
    return canon_fast(m, rel)
chains = {m: chain_key(m) in U4 for m in range(2, 7)}
print(f"   DUST (all antichains) in: {nA_alive}")
print(f"   pure chains alive by length: {chains}")
print(f"   min-amplitude t* over survivors: {t4}")
print("DONE", flush=True)
