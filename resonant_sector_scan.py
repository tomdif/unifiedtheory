#!/usr/bin/env python3
"""The resonant (third) sector: generality scan.

phi = 8pi at eps = 1/4 is the delta = 0 boundary of the j = 4 window:
W0*phi = 4pi, both root channels phase-neutral.  The general resonance
family is phi = 2*pi*q with 2*eps*q integer.  Two more members sit
INSIDE the 2D physical band [0.16, 0.25]:

  eps = 1/6, phi = 6pi  (W0 = 1/3):  per-link phase contributions
      k=1 -> pi (sign), k=2 -> -pi/3, k=3 -> +5pi/54, ...
      PRE-REGISTERED prediction: survivors == hereditary-real ==
      {no k>=3 link; every downset has #k2 = 0 mod 3; k1 free}.
  eps = 1/5, phi = 10pi (W0 = 2/5):  contributions
      k=1 -> -8pi/5, k=2 -> -4pi/25, k=3 -> +16pi/25, ...
      PRE-REGISTERED: survivors == hereditary-real; practically
      a*(-40) + b*(-4) + c*16 = 0 mod 50 on (k1,k2,k3) counts in every
      downset (pi-units scaled by 25, mod 2pi -> mod 50); heights >= 3
      nearly vanish; the surviving height-3 class at n = 7 includes the
      5-broom (5 bottoms, 1 middle covering all, 1 top) which jumps
      #k1 0 -> 5 in a single growth step.

Readings (pre-registered): equality at both points -> the third sector
is general, with eps-dependent congruence webs (mod 2 / mod 3 / mod 5
realized).  Gate STRICTLY INSIDE predicate -> funding obstructions
beyond phase-reality; report the over-killed classes.  Gate exceeding
predicate would falsify the mechanism outright.
"""
import itertools, math
from fractions import Fraction
import numpy as np
from scipy.optimize import linprog

C2 = [1, -2, 1]
def W_exact(k, eps):
    x = eps / (1 - eps)
    tot = sum(Fraction(C2[i-1]) * math.comb(k, i-1) * x**(i-1)
              for i in range(1, 4))
    return 2 * eps * (1 - eps)**k * tot

def canon_fast(n, rel):
    if not rel: return (n, ())
    up = [[] for _ in range(n)]; dn = [[] for _ in range(n)]
    for a, b in rel:
        up[a].append(b); dn[b].append(a)
    col = [(len(up[v]), len(dn[v])) for v in range(n)]
    vals = sorted(set(col)); m = {c: i for i, c in enumerate(vals)}
    col = [m[c] for c in col]
    for _ in range(n):
        nc = [(col[v], tuple(sorted(col[w] for w in up[v])),
               tuple(sorted(col[w] for w in dn[v]))) for v in range(n)]
        vals = sorted(set(nc)); m = {c: i for i, c in enumerate(vals)}
        nc = [m[c] for c in nc]
        if nc == col: break
        col = nc
    classes = {}
    for v in range(n): classes.setdefault(col[v], []).append(v)
    parts = [classes[c] for c in sorted(classes)]
    best = None
    for perm_parts in itertools.product(
            *[itertools.permutations(cls) for cls in parts]):
        pos = {}
        i = 0
        for part in perm_parts:
            for v in part:
                pos[v] = i; i += 1
        r = tuple(sorted((pos[a], pos[b]) for (a, b) in rel))
        if best is None or r < best: best = r
    return (n, best)

NMAX = 7
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
assert [counts[i] for i in range(1, 8)] == [1, 2, 5, 16, 63, 318, 2045]
print("tree validated (A000112)", flush=True)
root = canon_fast(1, ())
allkeys = [key for n in range(1, NMAX + 1) for key in sorted(levels[n])]
def nelem(key): return key[0]

def link_ks(rel, m):
    relset = set(rel)
    return [sum(1 for z in range(m) if (a, z) in relset and (z, b) in relset)
            for (a, b) in rel]

def height(rel, m):
    if not rel: return 1
    succ = {v: [b for (a, b) in rel if a == v] for v in range(m)}
    memo = {}
    def h(v):
        if v not in memo:
            memo[v] = 1 + max((h(w) for w in succ[v]), default=0)
        return memo[v]
    return max(h(v) for v in range(m))

def run_point(eps, q):
    phi_desc = f"{2*q}pi"
    W = {k: W_exact(k, eps) for k in range(0, NMAX)}
    # per-link pi-unit phase of a link with interval k:  -W(k)*2q  mod 2
    linkang = {k: (-W[k] * 2 * q) % 2 for k in W}
    print(f"\n=== eps = {eps} ({float(eps):.4f}), phi = {phi_desc}: "
          f"W0*phi = {2*q*W[0]}pi ===")
    print("   per-link phase (pi units): " +
          ", ".join(f"k={k}: {linkang[k]}" for k in range(0, 6)))
    # exact action angle of causet (pi units)
    def S_angle(rel, m):
        ang = (Fraction(m) * 2 * q) % 2
        for k in link_ks(rel, m):
            ang = (ang + linkang[k]) % 2
        return ang
    # hereditary-real predicate
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
    pred = {key for key in allkeys if hereditary_real(key)}
    # children with exact gaps -> phases
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
                    mu, gg = kid[ck]
                    assert gg == gang
                    kid[ck] = (mu + 1, gg)
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
            A_eq.append(rr); b_eq.append(0.0)
            A_eq.append(ri); b_eq.append(0.0)
        A_eq = np.array(A_eq); b_eq = np.array(b_eq)
        cobj = np.zeros(len(kk))
        for key in U:
            if nelem(key) >= 5: cobj[ii[key]] = -1.0
        res = linprog(cobj, A_eq=A_eq, b_eq=b_eq,
                      bounds=[(0, 1000)] * len(kk), method="highs")
        if not res.success: U = set(); break
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
        if root not in U: U = set(); break
    per = {}
    for key in U: per[nelem(key)] = per.get(nelem(key), 0) + 1
    print(f"   gate survivors: {len(U)}  [" +
          "  ".join(f"n={n}:{per.get(n,0)}/{counts[n]}"
                    for n in range(1, NMAX + 1)) + "]")
    print(f"   hereditary-real predicate: {len(pred)}; "
          f"EQUAL: {pred == U}", flush=True)
    if pred != U:
        po, go = pred - U, U - pred
        print(f"     predicate-only (over-predicted): {len(po)}; "
              f"gate-only (mechanism falsified!): {len(go)}")
        for k in sorted(po)[:4]: print(f"       pred-only: {k}")
        for k in sorted(go)[:4]: print(f"       GATE-ONLY: {k}")
    # height profile + interference structure
    hh = {}
    for key in U:
        h = height(key[1], key[0]); hh[h] = hh.get(h, 0) + 1
    tot_h = {}
    for key in allkeys:
        h = height(key[1], key[0]); tot_h[h] = tot_h.get(h, 0) + 1
    print("   height profile: " +
          "  ".join(f"h={h}:{hh.get(h,0)}/{tot_h[h]}" for h in sorted(tot_h)))
    cplx = 0
    for key in sorted(U):
        if key not in children or nelem(key) >= NMAX: continue
        if any(g not in (0, 1) for ck, (mu, g) in children[key].items()
               if ck in U): cplx += 1
    print(f"   surviving equations with complex coefficients: {cplx}")
    # 5-broom check at eps=1/5
    if eps == Fraction(1, 5):
        broom = [key for key in U if nelem(key) == 7
                 and height(key[1], key[0]) >= 3]
        print(f"   height>=3 survivors at n=7: {len(broom)}")
        for key in broom[:6]:
            m, rel = key
            ks = link_ks(rel, m)
            from collections import Counter
            print(f"     rel={rel} k-census={dict(Counter(ks))}")
    return U, pred

run_point(Fraction(1, 6), 3)    # eps=1/6, phi=6pi
run_point(Fraction(1, 5), 5)    # eps=1/5, phi=10pi
print("\nDONE", flush=True)
