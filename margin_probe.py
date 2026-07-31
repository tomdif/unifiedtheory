#!/usr/bin/env python3
"""Infeasibility margin vs depth for the physical band (reviewer-ordered).

L1 margin: min sum |slack| over x >= 0 for the wave system with
equations through n-1 on the tree to n, n = 5, 6, 7, at eps = 0.045
and the corrected in-window phase (phi = 2*pi + delta, delta inside
the true root window of width ~2*pi*eps).  Flat/growing margin =>
'structurally empty' earned; shrinking => depth race.  Per-equation
attribution localizes the global obstruction.
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

def canon_fast(n, rel):
    if not rel: return (n, ())
    up = [[] for _ in range(n)]; dn = [[] for _ in range(n)]
    for a, b in rel: up[a].append(b); dn[b].append(a)
    col = [(len(up[v]), len(dn[v])) for v in range(n)]
    vals = sorted(set(col)); mm = {c: i for i, c in enumerate(vals)}
    col = [mm[c] for c in col]
    for _ in range(n):
        nc = [(col[v], tuple(sorted(col[w] for w in up[v])),
               tuple(sorted(col[w] for w in dn[v]))) for v in range(n)]
        vals = sorted(set(nc)); mm = {c: i for i, c in enumerate(vals)}
        nc = [mm[c] for c in nc]
        if nc == col: break
        col = nc
    classes = {}
    for v in range(n): classes.setdefault(col[v], []).append(v)
    parts = [classes[c] for c in sorted(classes)]
    best = None
    for pp in itertools.product(*[itertools.permutations(c) for c in parts]):
        pos = {}
        i = 0
        for part in pp:
            for v in part: pos[v] = i; i += 1
        r = tuple(sorted((pos[a], pos[b]) for (a, b) in rel))
        if best is None or r < best: best = r
    return (n, best)

def downsets_of(m, rel):
    below = {x: {a for (a, b) in rel if b == x} for x in range(m)}
    out = []
    for mask in range(1 << m):
        D = frozenset(i for i in range(m) if mask >> i & 1)
        if all(below[x] <= D for x in D): out.append(D)
    return out

NMAX = 7
levels = {1: {canon_fast(1, ()): (1, ())}}
for n in range(1, NMAX):
    nxt = {}
    for key, (m, rel) in levels[n].items():
        for D in downsets_of(m, rel):
            nr = tuple(sorted(set(rel) | {(d, m) for d in D}))
            nxt[canon_fast(m + 1, nr)] = (m + 1, nr)
    levels[n + 1] = nxt
print("tree:", {n: len(v) for n, v in levels.items()}, flush=True)
root = canon_fast(1, ())
def nelem(key): return key[0]

eps = 0.045
children = {}
for n in range(1, NMAX):
    for key, (m, rel) in sorted(levels[n].items()):
        S0 = action_eps(rel, m, eps)
        kid = {}
        for D in downsets_of(m, rel):
            nr = tuple(sorted(set(rel) | {(d, m) for d in D}))
            ck = canon_fast(m + 1, nr)
            g = action_eps(nr, m + 1, eps) - S0
            if ck in kid:
                mu, gg = kid[ck]; kid[ck] = (mu + 1, gg)
            else: kid[ck] = (1, g)
        children[key] = kid

delta = 0.5 * 2 * np.pi * eps          # mid true root window
phi = 2 * np.pi + delta
print(f"eps = {eps}, phi = 2pi + {delta:.4f} = {phi:.4f}", flush=True)
for NN in (5, 6, 7):
    keys = [k for n in range(1, NN + 1) for k in sorted(levels[n])]
    ii = {k: i for i, k in enumerate(keys)}
    nvu = len(keys)
    rows, bvec, labels = [], [], []
    r0 = np.zeros(nvu); r0[ii[root]] = 1
    rows.append(r0); bvec.append(1.0); labels.append(("norm", 1))
    for key in keys:
        if nelem(key) >= NN: continue
        rr = np.zeros(nvu); ri = np.zeros(nvu)
        rr[ii[key]] -= 1
        for ck, (mu, g) in children[key].items():
            if ck not in ii: continue
            z = mu * np.exp(1j * g * phi)
            rr[ii[ck]] += z.real; ri[ii[ck]] += z.imag
        rows.append(rr); bvec.append(0.0); labels.append((key, "re"))
        rows.append(ri); bvec.append(0.0); labels.append((key, "im"))
    A = np.array(rows); b = np.array(bvec)
    ns = A.shape[0]
    Afull = np.hstack([A, np.eye(ns), -np.eye(ns)])
    c = np.concatenate([np.zeros(nvu), np.ones(2 * ns)])
    res = linprog(c, A_eq=Afull, b_eq=b,
                  bounds=[(0, 1000)] * nvu + [(0, None)] * (2 * ns),
                  method="highs")
    sl = res.x[nvu:nvu + ns] + res.x[nvu + ns:]
    margin = sl.sum()
    per_level = {}
    for (lab, part), s in zip(labels, sl):
        lev = 0 if lab == "norm" else nelem(lab)
        per_level[lev] = per_level.get(lev, 0.0) + s
    top = np.argsort(-sl)[:4]
    tops = [(labels[t][0] if labels[t][0] == "norm" else
             f"n={nelem(labels[t][0])}", labels[t][1], round(sl[t], 4))
            for t in top]
    print(f"depth {NN}: L1 margin = {margin:.5f}; by level "
          f"{ {k: round(v, 4) for k, v in sorted(per_level.items())} }; "
          f"top rows {tops}", flush=True)
