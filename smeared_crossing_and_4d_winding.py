#!/usr/bin/env python3
"""Follow-ups to smeared_2d_wave_gate.py, pre-registered.

A. 2D full-gate crossing: bisect eps* in (0.16, 0.20) at frac=0.5, j=1;
   plus frac scan at eps=0.18/0.20 to distinguish sharp-crossing vs
   archipelago, and t2 cross-check at every full-gate point.
B. 4D high-winding full gate (reviewer's arc test at dynamics level):
   eps=0.055, j=5 (t2-feasible), fracs {0.25, 0.5, 0.75}; control j=1
   frac=0.5 (funding-theorem covered: must be EMPTY).

t2 = truncation-2 LP (necessary).  Full = wave hierarchy, tree n<=NMAX,
equations n<=NMAX-1, exact LP + proven-death removal.
"""
import itertools, math
import numpy as np
from scipy.optimize import linprog

def make_W(C, pref):
    imax = len(C)
    def W(k, eps):
        tot = 0.0
        for i in range(1, imax + 1):
            tot += C[i-1] * math.comb(k, i-1) * (eps/(1-eps))**(i-1)
        return pref * eps * (1-eps)**k * tot
    return W

W2D = make_W([1.0, -2.0, 1.0], 2.0)
W4D = make_W([1.0, -9.0, 16.0, -8.0], 1.0)

def canon_fast(n, rel):
    if not rel:
        return (n, ())
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

def build_levels(nmax):
    levels = {1: {canon_fast(1, ()): (1, ())}}
    for n in range(1, nmax):
        nxt = {}
        for key, (m, rel) in levels[n].items():
            below = {x: {a for (a, b) in rel if b == x} for x in range(m)}
            for mask in range(1 << m):
                D = [i for i in range(m) if mask >> i & 1]
                if not all(below[x] <= set(D) for x in D): continue
                nr = tuple(sorted(set(rel) | {(d, m) for d in D}))
                nxt[canon_fast(m + 1, nr)] = (m + 1, nr)
        levels[n + 1] = nxt
    return levels

def action_eps(W, rel, n, eps):
    relset = set(rel)
    tot = float(n)
    for (a, b) in rel:
        k = sum(1 for z in range(n) if (a, z) in relset and (z, b) in relset)
        tot -= W(k, eps)
    return tot

def build_children(levels, W, eps, nmax):
    children = {}
    for n in range(1, nmax):
        for key, (m, rel) in sorted(levels[n].items()):
            S0 = action_eps(W, rel, m, eps)
            below = {x: {a for (a, b) in rel if b == x} for x in range(m)}
            kid = {}
            for mask in range(1 << m):
                D = [i for i in range(m) if mask >> i & 1]
                if not all(below[x] <= set(D) for x in D): continue
                nr = tuple(sorted(set(rel) | {(d, m) for d in D}))
                ck = canon_fast(m + 1, nr)
                g = action_eps(W, nr, m + 1, eps) - S0
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

def gate(levels, children, phi, nmax):
    root = canon_fast(1, ())
    allkeys = [key for n in range(1, nmax + 1) for key in sorted(levels[n])]
    def nelem(key): return key[0]
    U = set(allkeys)
    for rnd in range(60):
        kk = sorted(U); ii = {k: i for i, k in enumerate(kk)}
        nvu = len(kk)
        A_eq, b_eq = [], []
        r0 = np.zeros(nvu); r0[ii[root]] = 1
        A_eq.append(r0); b_eq.append(1.0)
        for key in kk:
            if nelem(key) >= nmax: continue
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
            if nelem(key) >= nmax - 2: cobj[ii[key]] = -1.0
        res = linprog(cobj, A_eq=A_eq, b_eq=b_eq, bounds=[(0, 1000)] * nvu,
                      method="highs")
        if not res.success: return set(), rnd
        A = {k: res.x[ii[k]] for k in kk}
        dead = set()
        for key in kk:
            if A[key] > 1e-9: continue
            c2 = np.zeros(nvu); c2[ii[key]] = -1.0
            r2 = linprog(c2, A_eq=A_eq, b_eq=b_eq, bounds=[(0, 1000)] * nvu,
                         method="highs")
            if (not r2.success) or -r2.fun < 1e-9: dead.add(key)
        if not dead:
            return U, rnd
        U = U - descendants(children, dead)
        if root not in U: return set(), rnd
    return U, 60

def trunc2(W0, W1, phi):
    th = lambda s: (1 - s) * phi
    rows, b = [], []
    def eq(channels, rhs_var):
        rr = np.zeros(7); ri = np.zeros(7)
        for var, mu, s in channels:
            z = mu * np.exp(1j * th(s))
            rr[var] += z.real; ri[var] += z.imag
        if rhs_var is not None: rr[rhs_var] -= 1
        rows.append(rr); b.append(0.0 if rhs_var is not None else 1.0)
        rows.append(ri); b.append(0.0)
    eq([(0, 1, W0), (1, 1, 0.0)], None)
    eq([(2, 1, W0), (3, 1, W0 + W1), (4, 1, 0.0)], 0)
    eq([(5, 1, 0.0), (4, 2, W0), (6, 1, 2 * W0)], 1)
    res = linprog(np.zeros(7), A_eq=np.array(rows), b_eq=np.array(b),
                  bounds=[(0, None)] * 7, method="highs")
    return res.success

def phi_of(W0, j, frac):
    delta = frac * W0 * 2 * np.pi * j / (1 - frac * W0)
    return 2 * np.pi * j + delta

NMAX = 7
levels = build_levels(NMAX)
counts = {n: len(v) for n, v in levels.items()}
assert [counts[i] for i in range(1, 8)] == [1, 2, 5, 16, 63, 318, 2045]
print("tree validated (A000112)", flush=True)

def run2d(eps, j, frac):
    W0, W1 = W2D(0, eps), W2D(1, eps)
    phi = phi_of(W0, j, frac)
    t2 = trunc2(W0, W1, phi)
    ch = build_children(levels, W2D, eps, NMAX)
    U, rnds = gate(levels, ch, phi, NMAX)
    full = len(U) == sum(counts.values())
    tag = "FULL" if full else (f"partial:{len(U)}" if U else "EMPTY")
    print(f"  2D eps={eps:.4f} j={j} frac={frac:.2f} "
          f"t2={'alive' if t2 else 'dead'} full-gate={tag} (rnds {rnds})",
          flush=True)
    return bool(U)

print("A1. 2D frac scan at eps=0.18, 0.20 (j=1):", flush=True)
for eps in (0.18, 0.20):
    for frac in (0.10, 0.25, 0.50, 0.75, 0.90):
        run2d(eps, j=1, frac=frac)

print("A2. 2D crossing bisection at frac=0.5, j=1:", flush=True)
lo, hi = 0.16, 0.20
for _ in range(7):
    mid = (lo + hi) / 2
    alive = run2d(mid, 1, 0.5)
    if alive: lo = mid
    else: hi = mid
print(f"  2D full-gate crossing: eps* in ({lo:.5f}, {hi:.5f})", flush=True)

print("B. 4D high-winding full gate at NMAX=6:", flush=True)
NMAX4 = 6
levels4 = {n: levels[n] for n in range(1, NMAX4 + 1)}
def run4d(eps, j, frac):
    W0, W1 = W4D(0, eps), W4D(1, eps)
    phi = phi_of(W0, j, frac)
    t2 = trunc2(W0, W1, phi)
    ch = build_children(levels4, W4D, eps, NMAX4)
    U, rnds = gate(levels4, ch, phi, NMAX4)
    fullct = sum(len(levels4[n]) for n in range(1, NMAX4 + 1))
    tag = "FULL" if len(U) == fullct else (f"partial:{len(U)}" if U else "EMPTY")
    per = {}
    for key in U: per[key[0]] = per.get(key[0], 0) + 1
    desc = "  ".join(f"n={n}:{per.get(n,0)}/{len(levels4[n])}"
                     for n in range(1, NMAX4 + 1)) if U else "EMPTY"
    print(f"  4D eps={eps:.4f} j={j} frac={frac:.2f} phi={phi:.4f} "
          f"t2={'alive' if t2 else 'dead'} full-gate={tag} (rnds {rnds})\n"
          f"    [{desc}]", flush=True)

run4d(0.055, 1, 0.50)   # control: funding-theorem covered, must be EMPTY
for frac in (0.10, 0.25, 0.50, 0.75, 0.90):
    run4d(0.055, 5, frac)
run4d(0.045, 6, 0.50)
run4d(0.0625, 4, 0.50)
print("DONE", flush=True)
