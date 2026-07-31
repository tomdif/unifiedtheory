#!/usr/bin/env python3
"""The smeared-4D gate: is the 4D classical collapse an artifact of the
sharp action?

Dowker-Glaser (1305.2588, eq. 26): f_d(n,eps) = (1-eps)^n *
sum_i C_i^(d) * C(n, i-1) * (eps/(1-eps))^(i-1); 4D C = (1,-9,16,-8).
Subtracted weights W_eps(k) = eps * f_4(k, eps); sharp limit eps = 1
recovers (1,-9,16,-8) on layers 0..3.

Structure: minimal-cover gap = 1 - eps != 0 for eps < 1 (zero mode
destroyed); root gaps (1-eps, 1) both positive => root branching
possible only in the window  pi < phi < pi/(1-eps)  (one sine must
flip).  Gate: exact support search (wave equation, downward closure,
proven-death removal) on the full 4D tree n <= 6 at a grid of
(eps, phi) inside and outside the window.
"""
import itertools, math
import numpy as np
from scipy.optimize import linprog

C4 = [1.0, -9.0, 16.0, -8.0]
def W_eps(k, eps):
    tot = 0.0
    for i in range(1, 5):
        tot += C4[i-1] * math.comb(k, i-1) * (eps/(1-eps))**(i-1)
    return eps * (1-eps)**k * tot

def action_eps(rel, n, eps):
    relset = set(rel)
    tot = float(n)
    for (a, b) in rel:
        k = sum(1 for z in range(n) if (a, z) in relset and (z, b) in relset)
        tot -= W_eps(k, eps)
    return tot

def canon(n, rel):
    best = None
    for p in itertools.permutations(range(n)):
        r = tuple(sorted((p[a], p[b]) for (a, b) in rel))
        if best is None or r < best: best = r
    return (n, best)

def downsets(n, rel):
    below = {x: {a for (a, b) in rel if b == x} for x in range(n)}
    out = []
    for mask in range(1 << n):
        D = frozenset(i for i in range(n) if mask >> i & 1)
        if all(below[x] <= D for x in D): out.append(D)
    return out

levels = {1: {canon(1, ()): (1, ())}}
for n in range(1, 6):
    nxt = {}
    for key, (m, rel) in levels[n].items():
        for D in downsets(m, rel):
            nr = tuple(sorted(set(rel) | {(d, m) for d in D}))
            nxt[canon(m + 1, nr)] = (m + 1, nr)
    levels[n + 1] = nxt
root = canon(1, ())
def nelem(key): return key[0]
allkeys = [key for n in range(1, 7) for key in sorted(levels[n])]
print("4D tree:", {n: len(v) for n, v in levels.items()}, flush=True)

def build(eps):
    children = {}
    for n in range(1, 6):
        for key, (m, rel) in sorted(levels[n].items()):
            S0 = action_eps(rel, m, eps)
            kid = {}
            for D in downsets(m, rel):
                nr = tuple(sorted(set(rel) | {(d, m) for d in D}))
                ck = canon(m + 1, nr)
                g = action_eps(nr, m + 1, eps) - S0
                if ck in kid:
                    mu, gg = kid[ck]
                    kid[ck] = (mu + 1, gg)
                else: kid[ck] = (1, g)
            children[key] = kid
    return children

def descendants(children, seed):
    out = set(seed); frontier = list(seed)
    while frontier:
        k = frontier.pop()
        for ck in children.get(k, {}):
            if ck not in out: out.add(ck); frontier.append(ck)
    return out

def gate(children, phi):
    U = set(allkeys)
    for _ in range(40):
        kk = sorted(U); ii = {k: i for i, k in enumerate(kk)}
        nvu = len(kk)
        A_eq, b_eq = [], []
        r0 = np.zeros(nvu); r0[ii[root]] = 1
        A_eq.append(r0); b_eq.append(1.0)
        for key in kk:
            if nelem(key) >= 6: continue
            rr = np.zeros(nvu); ri = np.zeros(nvu)
            rr[ii[key]] -= 1
            for ck, (mu, g) in children[key].items():
                if ck not in U: continue
                z = mu * np.exp(1j * g * phi)
                rr[ii[ck]] += z.real; ri[ii[ck]] += z.imag
            A_eq.append(rr); b_eq.append(0.0)
            A_eq.append(ri); b_eq.append(0.0)
        A_eq = np.array(A_eq); b_eq = np.array(b_eq)
        cobj = np.zeros(nvu)
        for key in U:
            if nelem(key) >= 4: cobj[ii[key]] = -1.0
        res = linprog(cobj, A_eq=A_eq, b_eq=b_eq, bounds=[(0, 1000)] * nvu,
                      method="highs")
        if not res.success: return set(), 0
        A = {k: res.x[ii[k]] for k in kk}
        dead = set()
        for key in kk:
            if A[key] > 1e-9: continue
            c2 = np.zeros(nvu); c2[ii[key]] = -1.0
            r2 = linprog(c2, A_eq=A_eq, b_eq=b_eq, bounds=[(0, 1000)] * nvu,
                         method="highs")
            if (not r2.success) or -r2.fun < 1e-9: dead.add(key)
        if not dead:
            br = sum(1 for key in U if key in children
                     and sum(1 for ck in children[key] if ck in U) >= 2)
            return U, br
        U = U - descendants(children, dead)
        if root not in U: return set(), 0
    return U, -1

for eps in (0.5, 0.2, 0.8):
    ch = build(eps)
    gaps = sorted(set(round(g, 6) for kid in ch.values()
                      for (mu, g) in kid.values()))
    mingap = min(abs(g) for g in gaps)
    wlo, whi = np.pi, np.pi / (1 - eps)
    print(f"eps = {eps}: min |gap| = {mingap:.4f} (zero mode destroyed); "
          f"predicted root window phi in ({wlo:.3f}, {whi:.3f})", flush=True)
    probes = [0.9, wlo * 0.8, (wlo + min(whi, 2*np.pi)) / 2,
              min(whi, 2 * np.pi) * 1.05]
    for phi in probes:
        U, br = gate(ch, phi)
        inwin = wlo < phi < whi
        per = {}
        for key in U: per[nelem(key)] = per.get(nelem(key), 0) + 1
        desc = "  ".join(f"n={n}:{per.get(n, 0)}" for n in range(1, 7)) \
               if U else "EMPTY"
        print(f"  phi = {phi:.3f} ({'in window' if inwin else 'outside'}): "
              f"support {len(U)} [{desc}] branching nodes {br}", flush=True)
