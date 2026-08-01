#!/usr/bin/env python3
"""Depth-8 extension of the self-similar exclusion — the falsification
program's next point (Paper 3: "compute the self-similar sup r at each
accessible depth; the exclusion survives exactly as long as the sup
stays bounded away from 1/2").

Depth-7 record (positivity_qp_2d.py, phi = 0.90):
    plain confined:        r_psi in [0.1241, 0.7687]
    one-step self-similar: r_psi in [0.2533, 0.4639]   <- the exclusion

This script: same construction one level deeper.  Sharp 2D weights
(2, -4, 2), generic phase phi = 0.90, confined family (order dim <= 2
+ cone closure) at depth 8, wave rows through level 7, one-step
Bombelli sub-sampling Psi_7 = T_78 Psi_8, psi-weighted mean ordering
fraction over 8-stems by LP + tau-bisection (positivity exact, no
penalties).

PRE-REGISTERED READINGS:
  sup r_psi(8) <= ~0.464           -> exclusion persists, sharpened by
                                      depth (the falsification target
                                      survives its first depth test);
  sup drifts toward 1/2 (>= ~0.48) -> the exclusion dissolves visibly,
                                      one number per depth, reported;
  infeasible                       -> halt and reconcile (cf. the
                                      multi-step/semigroup finite-size
                                      precedent).
Also reported: the plain confined range at depth 8 (bracket check:
does it still straddle 1/2 and 0.533?), and the dimension consumed by
the one-step constraint.
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

NMAX = 8
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
assert [counts[i] for i in range(1, 9)] == [1, 2, 5, 16, 63, 318, 2045, 16999]
print("tree validated (A000112 through 16999)", flush=True)
root = canon_fast(1, ())
allkeys = [key for n in range(1, NMAX + 1) for key in sorted(levels[n])]
def nelem(key): return key[0]

children = {}
for n in range(1, NMAX):
    for key, (m, rel) in sorted(levels[n].items()):
        below = {x: {a for (a, b) in rel if b == x} for x in range(m)}
        S0 = action(rel, m)
        kid = {}
        for mask in range(1 << m):
            D = [i for i in range(m) if mask >> i & 1]
            if not all(below[x] <= set(D) for x in D): continue
            nr = tuple(sorted(set(rel) | {(d, m) for d in D}))
            ck = canon_fast(m + 1, nr)
            g = action(nr, m + 1) - S0
            if ck in kid:
                mu, gg = kid[ck]; kid[ck] = (mu + 1, gg)
            else: kid[ck] = (1, g)
        children[key] = kid
print("children built", flush=True)

parents = {}
for key in allkeys:
    m, rel = key
    if m == 1: parents[key] = []; continue
    above = {v: [b for (a, b) in rel if a == v] for v in range(m)}
    mx = [v for v in range(m) if not above[v]]
    ps = set()
    for v in mx:
        keep = [u for u in range(m) if u != v]
        gi = {u: i for i, u in enumerate(keep)}
        ps.add(canon_fast(m - 1, tuple(sorted((gi[a], gi[b])
              for (a, b) in rel if a in gi and b in gi))))
    parents[key] = sorted(ps)

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
per = {n: sum(1 for k in U if nelem(k) == n) for n in range(1, NMAX + 1)}
print(f"confined support {nvu} {per}", flush=True)

phi = 0.90
ext = {root: 1}
for n in range(1, NMAX):
    for key in sorted(levels[n]):
        if key not in ext: continue
        for ck, (mu, g) in children[key].items():
            ext[ck] = ext.get(ck, 0) + mu * ext[key]

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
print(f"wave rows {Aw.shape}", flush=True)

stems8 = [k for k in kk if nelem(k) == 8]
rows7, rhs7 = [], []
Tcol = {}
for C in stems8:
    m, rel = C
    cnt = {}
    for v in range(m):
        keep = [u for u in range(m) if u != v]
        gi = {u: i for i, u in enumerate(keep)}
        sub = canon_fast(7, tuple(sorted((gi[a], gi[b])
              for (a, b) in rel if a in gi and b in gi)))
        cnt[sub] = cnt.get(sub, 0) + 1
    Tcol[C] = {c: v / 8.0 for c, v in cnt.items()}
for c in sorted(k for k in kk if nelem(k) == 7):
    rr = np.zeros(nvu); ri = np.zeros(nvu)
    zc = np.exp(1j * action(c[1], c[0]) * phi) * ext.get(c, 0)
    rr[ii[c]] -= zc.real; ri[ii[c]] -= zc.imag
    for C in stems8:
        t = Tcol[C].get(c, 0.0)
        if t == 0: continue
        z = t * ext.get(C, 0) * np.exp(1j * action(C[1], C[0]) * phi)
        rr[ii[C]] += z.real; ri[ii[C]] += z.imag
    rows7.append(rr); rhs7.append(0.0)
    rows7.append(ri); rhs7.append(0.0)
Ass = np.vstack([Aw, np.array(rows7)])
bss = np.concatenate([bw, np.array(rhs7)])
print(f"self-similar rows added: {len(rows7)}", flush=True)

def ofrac(k): return len(k[1]) / (k[0] * (k[0] - 1) / 2)
rvec = np.zeros(nvu); evec = np.zeros(nvu)
for kkey in stems8:
    rvec[ii[kkey]] = ofrac(kkey) * ext.get(kkey, 0)
    evec[ii[kkey]] = ext.get(kkey, 0)

def r_range(A, b, label, iters=18):
    lo, hi = None, None
    for sense in (+1, -1):
        a, c = 0.0, 1.0
        for _ in range(iters):
            tau = (a + c) / 2
            row = sense * (rvec - tau * evec)
            res = linprog(np.zeros(nvu), A_eq=A, b_eq=b,
                          A_ub=-row[None, :], b_ub=[-1e-6],
                          bounds=[(0, 1000)] * nvu, method="highs")
            feas = res.success
            if sense > 0:
                if feas: a = tau
                else: c = tau
            else:
                if feas: c = tau
                else: a = tau
        if sense > 0: hi = a
        else: lo = c
        print(f"    [{label}] {'sup' if sense > 0 else 'inf'} pass done",
              flush=True)
    print(f"  [{label}] r_psi range at depth 8: [{lo:.4f}, {hi:.4f}]",
          flush=True)
    return lo, hi

print("plain confined range:", flush=True)
r_range(Aw, bw, "plain confined d8")
print("one-step self-similar range (THE NUMBER):", flush=True)
r_range(Ass, bss, "self-similar d8")
print("DONE", flush=True)
