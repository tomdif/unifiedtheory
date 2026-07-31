#!/usr/bin/env python3
"""Depth-8 asymptotic-selection probe for the manifold-confined family.

Wave equations couple levels (n, n+1) only, so depth pins earlier
amplitudes ONLY through death cascades: a causet whose surviving
children cannot balance its equation dies, reshaping earlier equations.
At n <= 7 the dim-3 kill triggered no cascade.  Here: n = 8 (16999
posets, A000112), the dim-3 census with the monotonicity shortcut
(dim-3 downset => dim-3 host, no search needed), the confined LP with
equations through n = 7, and the removal loop watching for REACH-BACK
deaths.  Plus: consumed-dimension curve point, and the first physics
profile of a canonical confined member (ordering-fraction statistics
of |Psi|^2 at the deepest stems vs the 2-order support).
"""
import itertools, math
import numpy as np
from scipy.optimize import linprog, least_squares
from scipy.sparse import csr_matrix

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

NMAX = 8
levels = {1: {canon_fast(1, ()): (1, ())}}
for n in range(1, NMAX):
    nxt = {}
    done = 0
    for key, (m, rel) in levels[n].items():
        for D in downsets_of(m, rel):
            nr = tuple(sorted(set(rel) | {(d, m) for d in D}))
            nxt[canon_fast(m + 1, nr)] = (m + 1, nr)
        done += 1
        if done % 400 == 0:
            print(f"  level {n}: {done}/{len(levels[n])} parents", flush=True)
    levels[n + 1] = nxt
counts = {n: len(v) for n, v in levels.items()}
print("levels:", counts, flush=True)
assert [counts[i] for i in range(1, 9)] == [1, 2, 5, 16, 63, 318, 2045, 16999]
root = canon_fast(1, ())
def nelem(key): return key[0]
allkeys = [key for n in range(1, NMAX + 1) for key in sorted(levels[n])]

children = {}
for n in range(1, NMAX):
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
print("children built", flush=True)

parents = {}
for key, kid in children.items():
    for ck in kid: parents.setdefault(ck, []).append(key)
def descendants(seed):
    out = set(seed); frontier = list(seed)
    while frontier:
        k = frontier.pop()
        for ck in children.get(k, {}):
            if ck not in out: out.add(ck); frontier.append(ck)
    return out
print("parent graph built", flush=True)

def dim_le_2(key):
    m, rel = key
    if m <= 2 or not rel: return True
    relset = set(rel)
    succ = {v: {b for (a, b) in rel if a == v} for v in range(m)}
    incomp = [(a, b) for a in range(m) for b in range(a + 1, m)
              if (a, b) not in relset and (b, a) not in relset]
    if not incomp: return True
    indeg0 = {v: 0 for v in range(m)}
    for (a, b) in rel: indeg0[b] += 1
    def linexts(order, indeg):
        if len(order) == m:
            yield order; return
        for v in range(m):
            if indeg[v] == 0 and v not in order:
                nd = dict(indeg); nd[v] = -1
                for w in succ[v]: nd[w] -= 1
                yield from linexts(order + [v], nd)
    for L in linexts([], indeg0):
        pos = {v: i for i, v in enumerate(L)}
        edges = set(rel)
        for (a, b) in incomp:
            edges.add((b, a) if pos[a] < pos[b] else (a, b))
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
for n in range(1, NMAX + 1):
    bad = []
    for key in sorted(levels[n]):
        if any(p in dim3 for p in parents.get(key, [])):
            bad.append(key); continue          # taint via parents
        if not dim_le_2(key):
            bad.append(key)
    dim3.update(bad)
    print(f"n={n}: dim>=3: {len(bad)}/{counts[n]}", flush=True)

def run_gate(kill):
    U = set(allkeys) - descendants(kill) if kill else set(allkeys)
    for round_ in range(30):
        kk = sorted(U); ii = {k: i for i, k in enumerate(kk)}
        nvu = len(kk)
        rows, cols, vals, b_eq = [], [], [], []
        rr = 0
        rows.append(rr); cols.append(ii[root]); vals.append(1.0)
        b_eq.append(1.0); rr += 1
        for key in kk:
            if nelem(key) >= NMAX: continue
            e_r, e_i = [], []
            e_r.append((ii[key], -1.0))
            for ck, (mu, g) in children[key].items():
                if ck not in U: continue
                z = mu * np.exp(1j * g * 0.90)
                e_r.append((ii[ck], z.real)); e_i.append((ii[ck], z.imag))
            for j, v in e_r:
                rows.append(rr); cols.append(j); vals.append(v)
            b_eq.append(0.0); rr += 1
            for j, v in e_i:
                rows.append(rr); cols.append(j); vals.append(v)
            b_eq.append(0.0); rr += 1
        A = csr_matrix((vals, (rows, cols)), shape=(rr, nvu))
        b = np.array(b_eq)
        cobj = np.zeros(nvu)
        for key in U:
            if nelem(key) >= 6: cobj[ii[key]] = -1.0
        res = linprog(cobj, A_eq=A, b_eq=b, bounds=[(0, 1000)] * nvu,
                      method="highs")
        if not res.success:
            return None, U, round_
        Av = {k: res.x[ii[k]] for k in kk}
        # reach-back watch: test zeros at levels <= NMAX-1 only
        zeros = [k for k in kk if Av[k] <= 1e-9 and nelem(k) < NMAX]
        dead = set()
        for k in zeros[:400]:
            c2 = np.zeros(nvu); c2[ii[k]] = -1.0
            r2 = linprog(c2, A_eq=A, b_eq=b, bounds=[(0, 1000)] * nvu,
                         method="highs")
            if (not r2.success) or -r2.fun < 1e-9: dead.add(k)
        print(f"    round {round_}: support {len(U)}, zeros {len(zeros)}, "
              f"forced dead {len(dead)} "
              f"{sorted(set(nelem(k) for k in dead)) if dead else ''}",
              flush=True)
        if not dead:
            return (A, b, ii, Av), U, round_
        U = U - descendants(dead)
    return None, U, -1

print("=" * 72)
print("CONFINED gate (kill dim>=3, equations through n = 7):", flush=True)
sysc, Uc, _ = run_gate(dim3)
if sysc is None:
    print("  INFEASIBLE or stuck -- reach-back cascade killed the family")
else:
    A, b, ii, Av = sysc
    per = {}
    for key in Uc: per[nelem(key)] = per.get(nelem(key), 0) + 1
    print("  FEASIBLE; support " + "  ".join(
        f"n={n}: {per.get(n, 0)}/{counts[n]}" for n in range(1, 9)))
    G = (A @ A.T).toarray()
    rank = np.linalg.matrix_rank(G)
    print(f"  freedom: {len(Uc)} vars, rank {rank} -> dim {len(Uc) - rank}",
          flush=True)
print("=" * 72)
print("UNRESTRICTED gate at depth 8 (for the dimension curve):", flush=True)
sysu, Uu, _ = run_gate(set())
if sysu is not None:
    A, b, ii, Av = sysu
    G = (A @ A.T).toarray()
    rank = np.linalg.matrix_rank(G)
    print(f"  support {len(Uu)}; freedom dim {len(Uu) - rank}", flush=True)
print("=" * 72)
print("Consumed-dimension curve: depth 6: 234 vs ?; depth 7: 1639 vs 1553;")
print("depth 8: see above.")
# canonical confined member: ordering-fraction profile at n = 7
if sysc is not None:
    A, b, ii, Av = sysc
    kk = sorted(Uc)
    ext = {root: 1}
    for n in range(1, NMAX):
        for key in sorted(levels[n]):
            if key not in ext: continue
            for ck, (mu, g) in children[key].items():
                ext[ck] = ext.get(ck, 0) + mu * ext[key]
    phi = 0.90
    stems = [k for k in Uc if nelem(k) == 7]
    Psi = {k: ext.get(k, 0) * Av.get(k, 0.0)
           * np.exp(1j * action(k[1], k[0]) * phi) for k in stems}
    tot = sum(Psi.values())
    w = {k: abs(Psi[k])**2 for k in stems}
    wsum = sum(w.values())
    def ofrac(k):
        return len(k[1]) / (k[0] * (k[0] - 1) / 2)
    rmean_w = sum(w[k] * ofrac(k) for k in stems) / wsum
    rmean_u = np.mean([ofrac(k) for k in stems])
    print(f"canonical member, n=7 stems: |sum Psi|^2 = {abs(tot)**2:.4f}; "
          f"|Psi|^2-weighted mean ordering fraction = {rmean_w:.4f}")
    print(f"  (uniform over 2-order support: {rmean_u:.4f}; "
          "2D continuum benchmark: 0.5)")
