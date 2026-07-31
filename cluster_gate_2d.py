#!/usr/bin/env python3
"""The cluster-decomposition gate on the 2D survivor.

Forms tested (all at n <= 6, exact machinery as before):
  C1 per-path cluster:  A(C1 |_| C2) = A(C1) A(C2).  Root equation +
     cluster PINS THE PHASE: A(2A) = 1 forces 2 cos phi = 1, phi = pi/3
     (hbar = 3 sigma_2/pi).  Then the 2-antichain node demands
     A(3A) = 2 A(L) (multiplicity mu = 2) against cluster's 1 = 1: dead.
  C2 event cluster:  ext*A factorizes (binomial absorbed by paths):
     root forces cos phi = 1: dead at every nondegenerate phase.
  C3 orbit-counted sum rule + per-path cluster: transitions counted per
     Aut(parent)-orbit of downsets instead of per labeled downset (a
     different, unlabeled-tree normalization).  Hand-check passes n = 3
     with deaths (A(3ch) = A(Lambda) = 0) and no contradiction; here we
     run the exact support search with orbit multiplicities at phi = pi/3
     and then test cluster compatibility on the surviving family.
"""
import itertools, math
import numpy as np
from scipy.optimize import linprog, least_squares

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
for n in range(1, 6):
    nxt = {}
    for key, (m, rel) in levels[n].items():
        for D in downsets_of(m, rel):
            nr = tuple(sorted(set(rel) | {(d, m) for d in D}))
            nxt[canon_fast(m + 1, nr)] = (m + 1, nr)
    levels[n + 1] = nxt
root = canon_fast(1, ())
def nelem(key): return key[0]
allkeys = [key for n in range(1, 7) for key in sorted(levels[n])]
idx = {key: i for i, key in enumerate(allkeys)}
nv = len(allkeys)

# components (comparability-graph connectivity)
def components(key):
    m, rel = key
    par = list(range(m))
    def find(x):
        while par[x] != x: par[x] = par[par[x]]; x = par[x]
        return x
    for a, b in rel:
        ra, rb = find(a), find(b)
        if ra != rb: par[ra] = rb
    comp = {}
    for v in range(m): comp.setdefault(find(v), []).append(v)
    out = []
    for vs in comp.values():
        vidx = {v: i for i, v in enumerate(sorted(vs))}
        out.append(canon_fast(len(vs), tuple(sorted((vidx[a], vidx[b])
                   for (a, b) in rel if a in vidx and b in vidx))))
    return out
conn_count = {n: sum(1 for key in levels[n] if len(components(key)) == 1)
              for n in range(1, 7)}
print("connected causets per level:", conn_count, "(A000608: 1,1,3,10,44,238)")

# labeled and orbit multiplicities + gaps
children_lab, children_orb = {}, {}
for n in range(1, 6):
    for key, (m, rel) in sorted(levels[n].items()):
        S0 = action(rel, m)
        auts = [p for p in itertools.permutations(range(m))
                if tuple(sorted((p[a], p[b]) for (a, b) in rel))
                == tuple(sorted(rel))]
        seen_orbits = set()
        kidl, kido = {}, {}
        for D in downsets_of(m, rel):
            nr = tuple(sorted(set(rel) | {(d, m) for d in D}))
            ck = canon_fast(m + 1, nr)
            g = action(nr, m + 1) - S0
            if ck in kidl: kidl[ck] = (kidl[ck][0] + 1, g)
            else: kidl[ck] = (1, g)
            orb = frozenset(frozenset(p[d] for d in D) for p in auts)
            if (ck, orb) not in seen_orbits:
                seen_orbits.add((ck, orb))
                if ck in kido: kido[ck] = (kido[ck][0] + 1, g)
                else: kido[ck] = (1, g)
        children_lab[key] = kidl
        children_orb[key] = kido
ext = {root: 1}
for n in range(1, 6):
    for key in sorted(levels[n].keys()):
        if key not in ext: continue
        for ck, (mu, g) in children_lab[key].items():
            ext[ck] = ext.get(ck, 0) + mu * ext[key]

disconnected = [key for key in allkeys if len(components(key)) > 1]
print(f"disconnected causets n<=6: {len(disconnected)}")

def cluster_rows(use_event):
    rows = []
    for key in disconnected:
        row = np.zeros(nv)
        row[idx[key]] += 1
        c0 = 0.0
        if use_event: c0 -= math.log(ext[key])
        for comp in components(key):
            row[idx[comp]] -= 1
            if use_event: c0 += math.log(ext[comp])
        rows.append((row, c0))
    return rows

def wave_matrix(children, phi):
    Aeqs = []
    for n in range(1, 6):
        for key in sorted(levels[n]):
            rowz = np.zeros(nv, dtype=complex)
            rowz[idx[key]] -= 1
            for ck, (mu, g) in children[key].items():
                rowz[idx[ck]] += mu * np.exp(1j * g * phi)
            Aeqs.append(rowz)
    W = np.array(Aeqs)
    Ar = np.vstack([W.real, W.imag])
    r0 = np.zeros((1, nv)); r0[0, idx[root]] = 1
    return np.vstack([r0, Ar]), np.concatenate([[1.0], np.zeros(2 * len(W))])

def ls_gate(children, phi, use_event, label):
    A_eq, b_eq = wave_matrix(children, phi)
    crows = cluster_rows(use_event)
    M = np.array([r for r, c in crows]); c0 = np.array([c for r, c in crows])
    res = linprog(np.zeros(nv), A_eq=A_eq, b_eq=b_eq,
                  bounds=[(1e-4, 1000)] * nv, method="highs")
    if not res.success:
        print(f"  {label}: no strictly-positive wave solution"); return
    u0 = np.log(res.x)
    def resid(u):
        return np.concatenate([A_eq @ np.exp(u) - b_eq,
                               0.5 * (M @ u + c0)])
    sol = least_squares(resid, u0, method="trf", max_nfev=6000)
    r1 = A_eq @ np.exp(sol.x) - b_eq
    r2 = M @ sol.x + c0
    print(f"  {label}: |wave| = {np.linalg.norm(r1):.2e}, "
          f"|cluster| = {np.linalg.norm(r2):.2e}  -> "
          f"{'FEASIBLE' if np.linalg.norm(r1) < 1e-7 and np.linalg.norm(r2) < 1e-6 else 'dead'}")

print("=" * 72)
print("C1 per-path cluster (labeled wave), scan:")
for lab, phi in [("pi/3", np.pi / 3), ("0.90", 0.90), ("pi/6", np.pi / 6)]:
    ls_gate(children_lab, phi, False, f"phi={lab}")
print("  (root+cluster pins phi = pi/3; the 2A node then demands"
      " A(3A) = 2 A(L) vs cluster 1 = 1: mu = 2 kill)")
print("=" * 72)
print("C2 event cluster (labeled wave), scan:")
for lab, phi in [("pi/3", np.pi / 3), ("0.90", 0.90)]:
    ls_gate(children_lab, phi, True, f"phi={lab}")
print("  (root forces cos phi = 1: dead at all nondegenerate phases)")
print("=" * 72)
print("C3 ORBIT-counted sum rule + per-path cluster at phi = pi/3:")
# exact support search with orbit multiplicities
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
phi = np.pi / 3
U = set(allkeys)
Afin = None
for _ in range(80):
    kk = sorted(U); ii = {k: i for i, k in enumerate(kk)}
    nvu = len(kk)
    A_eq, b_eq = [], []
    r0 = np.zeros(nvu); r0[ii[root]] = 1
    A_eq.append(r0); b_eq.append(1.0)
    for key in kk:
        if nelem(key) >= 6: continue
        rr = np.zeros(nvu); ri = np.zeros(nvu)
        rr[ii[key]] -= 1
        for ck, (mu, g) in children_orb[key].items():
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
    if not res.success:
        U = set(); break
    A = {k: res.x[ii[k]] for k in kk}
    dead = set()
    for key in kk:
        if A[key] > 1e-9: continue
        c2 = np.zeros(nvu); c2[ii[key]] = -1.0
        r2 = linprog(c2, A_eq=A_eq, b_eq=b_eq, bounds=[(0, 1000)] * nvu,
                     method="highs")
        if (not r2.success) or -r2.fun < 1e-9:
            dead.add(key)
    if not dead:
        Afin = A; break
    U = {key for key in U if key not in dead and not (anc[key] & dead)}
    if root not in U:
        U = set(); break
if not U:
    print("  orbit-wave support search: EMPTY at pi/3")
else:
    per = {}
    for key in U: per[nelem(key)] = per.get(nelem(key), 0) + 1
    print(f"  orbit-wave support at pi/3: {len(U)} causets  "
          + "  ".join(f"n={n}: {per.get(n,0)}/{len(levels[n])}"
                      for n in range(1, 7)))
    # cluster compatibility on the support: rows with all members in U
    okrows, broken = [], 0
    for key in disconnected:
        comps = components(key)
        inU = (key in U)
        allc = all(c in U for c in comps)
        if inU and not allc:
            broken += 1
        elif inU and allc:
            row = np.zeros(len(U))
            iiU = {k: i for i, k in enumerate(sorted(U))}
            row[iiU[key]] += 1
            for c in comps: row[iiU[c]] -= 1
            okrows.append(row)
    print(f"  disconnected members of support: cluster rows usable "
          f"{len(okrows)}, broken (component dead) {broken}")
    kk = sorted(U); iiU = {k: i for i, k in enumerate(kk)}
    nvu = len(kk)
    A_eq, b_eq = [], []
    r0 = np.zeros(nvu); r0[iiU[root]] = 1
    A_eq.append(r0); b_eq.append(1.0)
    for key in kk:
        if nelem(key) >= 6: continue
        rr = np.zeros(nvu); ri = np.zeros(nvu)
        rr[iiU[key]] -= 1
        for ck, (mu, g) in children_orb[key].items():
            if ck not in U: continue
            z = mu * np.exp(1j * g * phi)
            rr[iiU[ck]] += z.real; ri[iiU[ck]] += z.imag
        A_eq.append(rr); b_eq.append(0.0)
        A_eq.append(ri); b_eq.append(0.0)
    A_eq = np.array(A_eq); b_eq = np.array(b_eq)
    res = linprog(np.zeros(nvu), A_eq=A_eq, b_eq=b_eq,
                  bounds=[(1e-4, 1000)] * nvu, method="highs")
    if not res.success:
        print("  no strictly-positive orbit-wave solution on support")
    else:
        u0 = np.log(res.x)
        M = np.array(okrows) if okrows else np.zeros((0, nvu))
        def resid(u):
            return np.concatenate([A_eq @ np.exp(u) - b_eq, 0.5 * (M @ u)])
        sol = least_squares(resid, u0, method="trf", max_nfev=8000)
        r1 = A_eq @ np.exp(sol.x) - b_eq
        r2 = M @ sol.x
        feas = np.linalg.norm(r1) < 1e-7 and np.linalg.norm(r2) < 1e-6
        print(f"  orbit-wave + cluster LS: |wave| = {np.linalg.norm(r1):.2e},"
              f" |cluster| = {np.linalg.norm(r2):.2e} -> "
              f"{'FEASIBLE' if feas else 'dead'}")
        if feas:
            Asol = np.exp(sol.x)
            Jw = A_eq * Asol[None, :]
            Jall = np.vstack([Jw, M])
            print(f"  dimension: orbit-wave-only {nvu - np.linalg.matrix_rank(Jw)};"
                  f" +cluster {nvu - np.linalg.matrix_rank(Jall)}")
