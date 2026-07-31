#!/usr/bin/env python3
"""Continuum-limit selection: let emergence be the selector.

Criterion: 2D causal sets are 2-orders (intersections of two linear
orders).  A poset is 2D-compatible iff its order dimension is <= 2;
the smallest dim-3 posets (3+3 crown family) appear at n = 6.
Test (dim <= 2): exists a linear extension L such that P together with
all incomparable pairs REVERSED from L is acyclic (then P = L cap L2).

Gate: kill every dim>=3 causet (n <= 7) + covariance cones; is the
covariance-only wave family still feasible (equations through n = 6,
generic phase)?  If yes: the 2D-selected family exists -- report its
support and how much freedom the selector consumes.  If no: every
covariant dynamics must amplitude-populate non-2D-embeddable geometry.
"""
import itertools, math
import numpy as np
from scipy.optimize import linprog

W2 = {0: 2, 1: -4, 2: 2}
def action(rel, n):
    relset = set(rel)
    tot = n
    for (a, b) in rel:
        k = sum(1 for z in range(n) if (a, z) in relset and (z, b) in relset)
        tot -= W2.get(k, 0)
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

levels = {1: {canon_fast(1, ()): (1, ())}}
for n in range(1, 7):
    nxt = {}
    for key, (m, rel) in levels[n].items():
        for D in downsets_of(m, rel):
            nr = tuple(sorted(set(rel) | {(d, m) for d in D}))
            nxt[canon_fast(m + 1, nr)] = (m + 1, nr)
    levels[n + 1] = nxt
counts = {n: len(v) for n, v in levels.items()}
print("levels:", counts)
assert [counts[i] for i in range(1, 8)] == [1, 2, 5, 16, 63, 318, 2045]
root = canon_fast(1, ())
def nelem(key): return key[0]
allkeys = [key for n in range(1, 8) for key in sorted(levels[n])]

children = {}
for n in range(1, 7):
    for key, (m, rel) in sorted(levels[n].items()):
        S0 = action(rel, m)
        kid = {}
        for D in downsets_of(m, rel):
            nr = tuple(sorted(set(rel) | {(d, m) for d in D}))
            ck = canon_fast(m + 1, nr)
            g = action(nr, m + 1) - S0
            if ck in kid: kid[ck] = (kid[ck][0] + 1, g)
            else: kid[ck] = (1, g)
        children[key] = kid

# ---- order dimension <= 2 test --------------------------------------------
def dim_le_2(key):
    m, rel = key
    if m <= 2 or not rel: return True
    relset = set(rel)
    succ = {v: {b for (a, b) in rel if a == v} for v in range(m)}
    incomp = [(a, b) for a in range(m) for b in range(a + 1, m)
              if (a, b) not in relset and (b, a) not in relset]
    if not incomp: return True                      # chain
    # enumerate linear extensions via DFS
    indeg = {v: 0 for v in range(m)}
    for (a, b) in rel: indeg[b] += 1
    def linexts(order, indeg):
        if len(order) == m:
            yield order; return
        for v in range(m):
            if indeg[v] == 0 and v not in order:
                nd = dict(indeg); nd[v] = -1
                for w in succ[v]: nd[w] -= 1
                yield from linexts(order + [v], nd)
    for L in linexts([], indeg):
        pos = {v: i for i, v in enumerate(L)}
        # Q = P + reversed incomparables of L; acyclic?
        edges = set(rel)
        for (a, b) in incomp:
            if pos[a] < pos[b]: edges.add((b, a))
            else: edges.add((a, b))
        # topological check
        ind = {v: 0 for v in range(m)}
        adj = {v: [] for v in range(m)}
        for (a, b) in edges:
            adj[a].append(b); ind[b] += 1
        stack = [v for v in range(m) if ind[v] == 0]
        seen = 0
        while stack:
            v = stack.pop(); seen += 1
            for w in adj[v]:
                ind[w] -= 1
                if ind[w] == 0: stack.append(w)
        if seen == m: return True
    return False

dim3 = set()
for n in range(1, 8):
    bad = [key for key in levels[n] if not dim_le_2(key)]
    dim3.update(bad)
    print(f"n={n}: dim>=3 causets: {len(bad)}/{counts[n]}")

# ---- covariance cones of the dim-3 kill -----------------------------------
anc = {}
for key in allkeys:
    m, rel = key
    a = set()
    for D in downsets_of(m, rel):
        if not D or len(D) == m: continue
        di = {d: i for i, d in enumerate(sorted(D))}
        a.add(canon_fast(len(D), tuple(sorted((di[x], di[y])
              for (x, y) in rel if x in D and y in D))))
    anc[key] = a
U0 = {key for key in allkeys if key not in dim3 and not (anc[key] & dim3)}
extra = 2450 - len(U0) - len(dim3)
print(f"killed: {len(dim3)} dim-3 + {extra} cone members; "
      f"candidate support {len(U0)}/2450")

# ---- LP feasibility + removal loop at two phases ---------------------------
for lab, phi in [("0.90 rad", 0.90), ("pi/3", np.pi / 3)]:
    U = set(U0)
    result = None
    for round_ in range(60):
        kk = sorted(U); ii = {k: i for i, k in enumerate(kk)}
        nvu = len(kk)
        A_eq, b_eq = [], []
        r0 = np.zeros(nvu); r0[ii[root]] = 1
        A_eq.append(r0); b_eq.append(1.0)
        for key in kk:
            if nelem(key) >= 7: continue
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
            if nelem(key) >= 5: cobj[ii[key]] = -1.0
        res = linprog(cobj, A_eq=A_eq, b_eq=b_eq, bounds=[(0, 1000)] * nvu,
                      method="highs")
        if not res.success:
            print(f"phi = {lab}: INFEASIBLE at round {round_} -- "
                  "no covariant dynamics avoids dim-3 geometry")
            break
        A = {k: res.x[ii[k]] for k in kk}
        dead = set()
        for key in kk:
            if A[key] > 1e-9: continue
            c2 = np.zeros(nvu); c2[ii[key]] = -1.0
            r2 = linprog(c2, A_eq=A_eq, b_eq=b_eq, bounds=[(0, 1000)] * nvu,
                         method="highs")
            if (not r2.success) or -r2.fun < 1e-9: dead.add(key)
        if not dead:
            rank = np.linalg.matrix_rank(A_eq)
            per = {}
            for key in U: per[nelem(key)] = per.get(nelem(key), 0) + 1
            print(f"phi = {lab}: FEASIBLE; final support {len(U)}  "
                  + "  ".join(f"n={n}: {per.get(n, 0)}/{counts[n]}"
                              for n in range(1, 8)))
            print(f"    freedom: {nvu} vars, rank {rank} -> "
                  f"dim {nvu - rank}  (unrestricted family: 1639)")
            break
        U = {key for key in U if key not in dead and not (anc[key] & dead)}
        if root not in U:
            print(f"phi = {lab}: root died"); break
