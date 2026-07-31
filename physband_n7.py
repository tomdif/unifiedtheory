#!/usr/bin/env python3
"""Depth-7 probe of the physical band (and the deterministic-root phases).

Does depth revive the physically-smeared 4D gate?  Tree to n = 7
(2045 causets, canon_fast validated), smeared Dowker-Glaser weights,
wave gate with equations through n = 6, at mid-band eps (no
gate-visible resonances), probing the k = 1, 2, 3 branching windows,
the deterministic-root phases phi = 2*pi*j/(1-eps), and a control.
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
counts = {n: len(v) for n, v in levels.items()}
print("4D tree:", counts, flush=True)
assert counts[7] == 2045
root = canon_fast(1, ())
def nelem(key): return key[0]
allkeys = [key for n in range(1, NMAX + 1) for key in sorted(levels[n])]

def build(eps):
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
            if nelem(key) >= NMAX: continue
            rr = np.zeros(nvu); ri = np.zeros(nvu)
            rr[ii[key]] -= 1
            for ck, (mu, g) in children[key].items():
                if ck not in U: continue
                z = mu * np.exp(1j * g * phi)
                rr[ii[ck]] += z.real; ri[ii[ck]] += z.imag
            A_eq.append(rr); b_eq.append(0.0)
            A_eq.append(ri); b_eq.append(0.0)
        A_eq = np.array(A_eq); b_eq = np.array(b_eq)
        res = linprog(np.zeros(nvu), A_eq=A_eq, b_eq=b_eq,
                      bounds=[(0, 1000)] * nvu, method="highs")
        if not res.success: return 0, 0
        A = {k: res.x[ii[k]] for k in kk}
        zeros = [k for k in kk if A[k] <= 1e-9 and nelem(k) < NMAX]
        dead = set()
        for k in zeros[:400]:
            c2 = np.zeros(nvu); c2[ii[k]] = -1.0
            r2 = linprog(c2, A_eq=A_eq, b_eq=b_eq, bounds=[(0, 1000)] * nvu,
                         method="highs")
            if (not r2.success) or -r2.fun < 1e-9: dead.add(k)
        if not dead:
            br = sum(1 for key in U if key in children
                     and sum(1 for ck in children[key] if ck in U) >= 2)
            return len(U), br
        U = U - descendants(children, dead)
        if root not in U: return 0, 0
    return len(U), -1

for eps in (0.045, 0.030):
    ch = build(eps)
    gaps = [g for kid in ch.values() for (mu, g) in kid.values()]
    print(f"eps = {eps}: min|gap| = {min(abs(g) for g in gaps):.5f}",
          flush=True)
    probes = []
    for k in (1, 2, 3):
        lo, hi = k * np.pi, k * np.pi / (1 - eps)
        for t in (0.25, 0.5, 0.8):
            probes.append((f"w{k}", lo + t * (hi - lo)))
    probes.append(("det1", 2 * np.pi / (1 - eps)))
    probes.append(("det2", 4 * np.pi / (1 - eps)))
    probes.append(("ctrl", 2.0))
    for lab, phi in probes:
        s, br = gate(ch, phi)
        print(f"  [{lab}] phi = {phi:.4f}: support {s}, branching {br}",
              flush=True)
