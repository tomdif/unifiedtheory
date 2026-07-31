#!/usr/bin/env python3
"""Depth-7 persistence test for the 2D survivor + structure probes.

1. Fast canonical form (WL color refinement + class-restricted perms),
   validated by the unlabeled poset counts 1,2,5,16,63,318,2045 (A000112).
2. The wave-equation gate with equations through n = 6 (free boundary at
   n = 7): does full support persist once the level-6 equations bite?
3. Solution-space dimension (rank deficiency): how underdetermined is
   the surviving family?
4. Witness probes: which 5-geometries dominate |Psi|^2; do action
   sectors decohere at the stem level?
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

levels = {1: {canon_fast(1, ()): (1, ())}}
for n in range(1, 7):
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
print("causets per level:", counts)
assert [counts[i] for i in range(1, 8)] == [1, 2, 5, 16, 63, 318, 2045], \
    "canonical form validation FAILED"
print("canon_fast validated against A000112 (1,2,5,16,63,318,2045)")

children = {}
allkeys = []
for n in range(1, 8):
    for key, (m, rel) in sorted(levels[n].items()):
        allkeys.append(key)
        if n == 7: continue
        S0 = action(rel, m)
        below = {x: {a for (a, b) in rel if b == x} for x in range(m)}
        kid = {}
        for mask in range(1 << m):
            D = [i for i in range(m) if mask >> i & 1]
            if not all(below[x] <= set(D) for x in D): continue
            nr = tuple(sorted(set(rel) | {(d, m) for d in D}))
            ck = canon_fast(m + 1, nr)
            g = action(nr, m + 1) - S0
            if ck in kid: kid[ck] = (kid[ck][0] + 1, g)
            else: kid[ck] = (1, g)
        children[key] = kid
root = canon_fast(1, ())
def nelem(key): return key[0]

anc = {}
for key in allkeys:
    m, rel = key
    below = {x: {a for (a, b) in rel if b == x} for x in range(m)}
    a = set()
    for mask in range(1 << m):
        D = [i for i in range(m) if mask >> i & 1]
        if not D or len(D) == m: continue
        if not all(below[x] <= set(D) for x in D): continue
        idx = {d: i for i, d in enumerate(sorted(D))}
        a.add(canon_fast(len(D), tuple(sorted((idx[x], idx[y])
              for (x, y) in rel if x in set(D) and y in set(D)))))
    anc[key] = a

ext = {root: 1}
for n in range(1, 7):
    for key in sorted(levels[n].keys()):
        if key not in ext: continue
        for ck, (mu, g) in children.get(key, {}).items():
            ext[ck] = ext.get(ck, 0) + mu * ext[key]

def gate(phi, maxdepth_eq=6):
    U = set(allkeys)
    A = None
    for _ in range(80):
        idx = {key: i for i, key in enumerate(sorted(U))}
        nv = len(idx)
        A_eq, b_eq = [], []
        row = np.zeros(nv); row[idx[root]] = 1
        A_eq.append(row); b_eq.append(1.0)
        for key in sorted(U):
            if nelem(key) > maxdepth_eq: continue
            if key not in children: continue
            rr = np.zeros(nv); ri = np.zeros(nv)
            rr[idx[key]] -= 1
            for ck, (mu, g) in children[key].items():
                if ck not in U: continue
                z = mu * np.exp(1j * g * phi)
                rr[idx[ck]] += z.real
                ri[idx[ck]] += z.imag
            A_eq.append(rr); b_eq.append(0.0)
            A_eq.append(ri); b_eq.append(0.0)
        A_eq = np.array(A_eq); b_eq = np.array(b_eq)
        cobj = np.zeros(nv)
        for key in U:
            if nelem(key) >= 5: cobj[idx[key]] = -1.0
        res = linprog(cobj, A_eq=A_eq, b_eq=b_eq,
                      bounds=[(0, 1000)] * nv, method="highs")
        if not res.success: return set(), None, None
        A = {key: res.x[idx[key]] for key in U}
        dead = set()
        zeros = [key for key in sorted(U) if A[key] <= 1e-9]
        for key in zeros:
            c2 = np.zeros(nv); c2[idx[key]] = -1.0
            r2 = linprog(c2, A_eq=A_eq, b_eq=b_eq,
                         bounds=[(0, 1000)] * nv, method="highs")
            if (not r2.success) or -r2.fun < 1e-9:
                dead.add(key)
        if not dead:
            return U, A, (A_eq, b_eq)
        U = {key for key in U if key not in dead and not (anc[key] & dead)}
        if root not in U: return set(), None, None
    return U, A, None

for label, phi in [("0.90 rad", 0.90), ("pi/3", np.pi / 3)]:
    U, A, sys_ = gate(phi)
    if not U:
        print(f"phi = {label}: DEATH at depth 7"); continue
    per = {}
    for key in U: per[nelem(key)] = per.get(nelem(key), 0) + 1
    desc = "  ".join(f"n={n}: {per.get(n, 0)}/{counts[n]}"
                     for n in range(1, 8))
    resid = []
    for n in range(2, 8):
        tot = sum(ext.get(key, 0) * A.get(key, 0.0)
                  * np.exp(1j * (action(key[1], key[0]) - 1) * phi)
                  for key in levels[n] if key in U)
        resid.append(abs(tot - 1))
    print(f"phi = {label}: support {len(U)}  [{desc}]")
    print(f"    unitarity residuals (levels 2-7): "
          f"{[f'{r:.1e}' for r in resid]}")
    if sys_ is not None:
        A_eq, b_eq = sys_
        rank = np.linalg.matrix_rank(A_eq)
        print(f"    solution space: {A_eq.shape[1]} vars, rank {rank} "
              f"-> affine dimension {A_eq.shape[1] - rank}")
    # |Psi|^2 ranking at n=5 and action-sector decoherence
    stems = [key for key in levels[5] if key in U]
    Psi = {key: ext[key] * A[key]
           * np.exp(1j * action(key[1], key[0]) * phi) for key in stems}
    tot = sum(Psi.values())
    print(f"    n=5 stems: |sum Psi|^2 = {abs(tot)**2:.4f} (=1 check); "
          f"sum |Psi|^2 = {sum(abs(p)**2 for p in Psi.values()):.4f}")
    rank5 = sorted(Psi.items(), key=lambda kv: -abs(kv[1]))[:5]
    print("    top-5 |Psi| 5-geometries:")
    for key, p in rank5:
        print(f"      S={action(key[1], key[0]):3d}  |Psi|={abs(p):8.3f}  "
              f"rel={key[1]}")
    sectors = {}
    for key in stems:
        sectors.setdefault(action(key[1], key[0]), []).append(Psi[key])
    svals = sorted(sectors)
    Z = {s: sum(sectors[s]) for s in svals}
    offmax = 0.0
    for s1 in svals:
        for s2 in svals:
            if s1 < s2:
                offmax = max(offmax, abs(Z[s1] * np.conj(Z[s2])))
    diag = {s: abs(Z[s])**2 for s in svals}
    print(f"    action sectors at n=5: {len(svals)}; "
          f"diag D = {[f'{diag[s]:.3f}' for s in svals]}")
    print(f"    max |off-diag| between action sectors: {offmax:.4f}")
