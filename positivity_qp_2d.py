#!/usr/bin/env python3
"""Positivity-clean pinned range + coherence check (gates paper 3).

1. The pinned range, rigorously: psi = ext*A >= 0, so the psi-weighted
   mean ordering fraction  r_psi = sum r psi / sum psi  is a ratio of
   linear functionals.  max/min r_psi over the POSITIVE self-similar
   polytope {wave rows, subsample-6 rows, A >= 0} is solved by LP +
   tau-bisection:  exists member with r_psi >= tau  <=>  LP with extra
   row sum (r - tau) psi >= 0 is feasible.  No penalties anywhere.
   Same scan over the plain confined polytope = the steering-capacity
   comparison, positivity-clean on both sides.
2. The sqrt(p_2o) fit, positivity-clean: rho-continuation on lsq_linear
   (variables A and lambda, native bounds >= 0), driving the equality
   residual below 1e-8; report fit quality and psi^2-weighted r.
3. Coherence check: is the canonical confined member (LP witness,
   maximize deep support) anomalously close to the Bombelli fixed
   point?  Defect |Psi_6 - T Psi_7| / |Psi_6| for the canonical member
   vs random vertices of the same polytope.
"""
import itertools, math
import numpy as np
from scipy.optimize import linprog, lsq_linear

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

NMAX = 7
levels = {1: {canon_fast(1, ()): (1, ())}}
for n in range(1, NMAX):
    nxt = {}
    for key, (m, rel) in levels[n].items():
        for D in downsets_of(m, rel):
            nr = tuple(sorted(set(rel) | {(d, m) for d in D}))
            nxt[canon_fast(m + 1, nr)] = (m + 1, nr)
    levels[n + 1] = nxt
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
parents = {}
for key, kid in children.items():
    for ck in kid: parents.setdefault(ck, []).append(key)

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
    for key in sorted(levels[n]):
        if any(p in dim3 for p in parents.get(key, [])):
            dim3.add(key); continue
        if not dim_le_2(key): dim3.add(key)
def descendants(seed):
    out = set(seed); frontier = list(seed)
    while frontier:
        k = frontier.pop()
        for ck in children.get(k, {}):
            if ck not in out: out.add(ck); frontier.append(ck)
    return out
U = set(allkeys) - descendants(dim3)
kk = sorted(U); ii = {k: i for i, k in enumerate(kk)}
nvu = len(kk)
phi = 0.90
ext = {root: 1}
for n in range(1, NMAX):
    for key in sorted(levels[n]):
        if key not in ext: continue
        for ck, (mu, g) in children[key].items():
            ext[ck] = ext.get(ck, 0) + mu * ext[key]
print(f"confined support {nvu}", flush=True)

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
Aw = np.array(A_eq); bw = np.array(b_eq)

stems7 = [k for k in kk if nelem(k) == 7]
Tcol = {}
for C in stems7:
    m, rel = C
    cnt = {}
    for S in itertools.combinations(range(m), 6):
        si = {v: i for i, v in enumerate(S)}
        sub = canon_fast(6, tuple(sorted((si[a], si[b])
              for (a, b) in rel if a in si and b in si)))
        cnt[sub] = cnt.get(sub, 0) + 1
    Tcol[C] = {c: v / 7.0 for c, v in cnt.items()}
rows6, rhs6 = [], []
for c in sorted(k for k in kk if nelem(k) == 6):
    rr = np.zeros(nvu); ri = np.zeros(nvu)
    zc = np.exp(1j * action(c[1], c[0]) * phi) * ext.get(c, 0)
    rr[ii[c]] -= zc.real; ri[ii[c]] -= zc.imag
    for C in stems7:
        t = Tcol[C].get(c, 0.0)
        if t == 0: continue
        z = t * ext.get(C, 0) * np.exp(1j * action(C[1], C[0]) * phi)
        rr[ii[C]] += z.real; ri[ii[C]] += z.imag
    rows6.append(rr); rhs6.append(0.0)
    rows6.append(ri); rhs6.append(0.0)
Ass = np.vstack([Aw, np.array(rows6)])
bss = np.concatenate([bw, np.array(rhs6)])
print("systems built", flush=True)

def ofrac(k): return len(k[1]) / (k[0] * (k[0] - 1) / 2)
rvec = np.zeros(nvu); evec = np.zeros(nvu)
for kkey in stems7:
    rvec[ii[kkey]] = ofrac(kkey) * ext.get(kkey, 0)
    evec[ii[kkey]] = ext.get(kkey, 0)

def r_range(A, b, label):
    lo, hi = None, None
    for sense in (+1, -1):
        a, c = 0.0, 1.0
        for _ in range(24):
            tau = (a + c) / 2
            row = sense * (rvec - tau * evec)
            res = linprog(np.zeros(nvu), A_eq=A, b_eq=b,
                          A_ub=-row[None, :], b_ub=[-1e-6],
                          bounds=[(0, 1000)] * nvu, method="highs")
            if res.success:
                a = tau if sense > 0 else a
                c = c if sense > 0 else tau
                # feasible: can push further in this sense
                if sense > 0: a = tau
                else: c = tau
            else:
                if sense > 0: c = tau
                else: a = tau
        if sense > 0: hi = a
        else: lo = c
    print(f"  [{label}] psi-weighted mean r range under positivity: "
          f"[{lo:.4f}, {hi:.4f}]", flush=True)
    return lo, hi

print("=" * 72)
print("1. Rigorous pinned range (LP + tau-bisection, positivity exact):",
      flush=True)
r_range(Aw, bw, "plain confined")
r_range(Ass, bss, "self-similar (one-step)")

print("=" * 72)
print("2. sqrt(p_2o) fit, rho-continuation, positivity native:", flush=True)
rng = np.random.default_rng(11)
p2o = {}
NS = 120000
for _ in range(NS):
    a = rng.permutation(7); b2 = rng.permutation(7)
    pos1 = np.empty(7, dtype=int); pos1[a] = np.arange(7)
    pos2 = np.empty(7, dtype=int); pos2[b2] = np.arange(7)
    rel = tuple(sorted((i, j) for i in range(7) for j in range(7)
                if i != j and pos1[i] < pos1[j] and pos2[i] < pos2[j]))
    c = canon_fast(7, rel)
    p2o[c] = p2o.get(c, 0) + 1
for c in p2o: p2o[c] /= NS
targ = np.array([math.sqrt(p2o.get(k, 0.0)) for k in stems7])
x = None
for rho in (1e2, 1e4, 1e6, 1e8):
    M = np.zeros((Ass.shape[0] + len(stems7), nvu + 1))
    y = np.zeros(Ass.shape[0] + len(stems7))
    M[:Ass.shape[0], :nvu] = math.sqrt(rho) * Ass
    y[:Ass.shape[0]] = math.sqrt(rho) * bss
    for i, kkey in enumerate(stems7):
        M[Ass.shape[0] + i, ii[kkey]] = ext.get(kkey, 0)
        M[Ass.shape[0] + i, nvu] = -targ[i]
    sol = lsq_linear(M, y, bounds=(np.zeros(nvu + 1),
                                   np.full(nvu + 1, np.inf)),
                     max_iter=400, tol=1e-14)
    x = sol.x
hard = np.linalg.norm(Ass @ x[:nvu] - bss)
psi = np.array([ext.get(k, 0) * x[ii[k]] for k in stems7])
lam = x[nvu]
rel_fit = (np.linalg.norm(psi - lam * targ)
           / max(lam * np.linalg.norm(targ), 1e-12))
w2 = psi ** 2
r2 = (sum(wi * ofrac(k) for wi, k in zip(w2, stems7)) / w2.sum()
      if w2.sum() > 0 else float("nan"))
r1 = (sum(wi * ofrac(k) for wi, k in zip(psi, stems7)) / psi.sum()
      if psi.sum() > 0 else float("nan"))
print(f"  hard residual {hard:.2e}; min amplitude "
      f"{x[:nvu].min():.2e}; relative fit {rel_fit:.3f}; "
      f"psi-weighted r = {r1:.4f}; psi^2-weighted r = {r2:.4f}", flush=True)

print("=" * 72)
print("3. Coherence check: Bombelli defect of the canonical member vs "
      "random vertices:", flush=True)
def defect(x):
    d = np.array(rows6) @ x
    n6 = [k for k in kk if nelem(k) == 6]
    scale = np.linalg.norm([ext.get(k, 0) * x[ii[k]] for k in n6])
    return np.linalg.norm(d) / max(scale, 1e-12)
cobj = np.zeros(nvu)
for key in U:
    if nelem(key) >= 5: cobj[ii[key]] = -1.0
res = linprog(cobj, A_eq=Aw, b_eq=bw, bounds=[(0, 1000)] * nvu,
              method="highs")
dc = defect(res.x)
rands = []
for s in range(6):
    rngo = np.random.default_rng(100 + s)
    res2 = linprog(rngo.normal(size=nvu), A_eq=Aw, b_eq=bw,
                   bounds=[(0, 1000)] * nvu, method="highs")
    if res2.success: rands.append(defect(res2.x))
print(f"  canonical-member defect: {dc:.4f}; random-vertex defects: "
      f"{[f'{d:.4f}' for d in rands]}", flush=True)
