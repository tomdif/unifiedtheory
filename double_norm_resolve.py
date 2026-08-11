#!/usr/bin/env python3
"""Resolve the dangling double_norm_probe (2026-08-03, script lost):
does the WAVE FAMILY contain a bi-normalized member?

Question: is there A >= 0 on the depth-5 growth tree (87 causets),
A(root)=1, satisfying BOTH, at every parent p with A_p > 0,
  coherent:  sum_c mu_c e^{i g_c phi} A_c = A_p          (wave family)
  Born:      sum_c mu_c A_c^2            = A_p^2         (diagonal)
If yes: bi-normalization is a SELECTION principle inside the old
theory (the completion would also resolve the selection crisis).
If no (residual floor across many starts): the bi-normalized law is
genuinely a SECOND theory (phases must move, as Born-shell does).

Method: least_squares on stacked residuals (coherent Re/Im + Born,
Born rows scaled by 1/(1+A_p) for balance), bounds A >= 0, root pinned,
200 random starts + the LP members as starts.  Report best rms and
per-block residuals.  Registered readings:
  (a) rms -> ~1e-10: member EXISTS, completion = selection.
  (b) rms floor ~1e-3-1e-4 across all starts: near-miss is structural,
      genuine second theory at depth 5.
"""
import itertools, math, sys
import numpy as np
from scipy.optimize import least_squares, linprog

PHI = 0.90
NMAX = 5

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

kk = allkeys; ii = {k: i for i, k in enumerate(kk)}
nv = len(kk)
parents = [k for k in kk if nelem(k) < NMAX]
print(f"causets {nv} (expect 87), parents {len(parents)}", flush=True)

# Null-space formulation: coherent equations C A = b are LINEAR and are
# satisfied EXACTLY by construction (A = A0 + N t, N = null space of C);
# minimize only the Born residual over the coherent solution space with
# a hinge penalty keeping A >= 0.  The reported number is then THE
# minimum Born defect over the (exactly coherent) wave family.
import scipy.sparse as sp
rows_lin = []; cols_lin = []; vals_lin = []; nlin = 0
def add(r, c, v):
    rows_lin.append(r); cols_lin.append(c); vals_lin.append(v)
add(0, ii[root], 1.0); nlin = 1
blin = [1.0]
for p_ in parents:
    rr = nlin; ri = nlin + 1; nlin += 2
    add(rr, ii[p_], -1.0)
    for ck, (mu, g) in children[p_].items():
        z = mu * np.exp(1j * g * PHI)
        add(rr, ii[ck], z.real); add(ri, ii[ck], z.imag)
    blin += [0.0, 0.0]
C = np.zeros((nlin, nv))
for r, c, v in zip(rows_lin, cols_lin, vals_lin):
    C[r, c] += v
blin = np.array(blin)
PARIDX = np.array([ii[p_] for p_ in parents])
CHILD = [ (np.array([ii[ck] for ck in children[p_]]),
           np.array([children[p_][ck][0] for ck in children[p_]], float))
          for p_ in parents ]

# particular solution + null space
A0, *_ = np.linalg.lstsq(C, blin, rcond=None)
U, S, Vt = np.linalg.svd(C)
rank = int(np.sum(S > 1e-10 * S[0]))
N = Vt[rank:].T                       # nv x kdim
kdim = N.shape[1]
print(f"coherent system rank {rank}, null-space dim {kdim}, "
      f"|C A0 - b| = {np.linalg.norm(C @ A0 - blin):.2e}", flush=True)

def amp_of(t):
    return A0 + N @ t

def born_res(A):
    return np.array([np.dot(mu, A[cix] ** 2) for cix, mu in CHILD]) \
           - A[PARIDX] ** 2

EPS2 = 1e-4
def born_res_norm(A):
    raw = born_res(A)
    return raw / (A[PARIDX] ** 2 + EPS2)

def make_res(wneg):
    def residuals(t):
        A = amp_of(t)
        return np.concatenate([born_res_norm(A), wneg * np.minimum(A, 0.0)])
    return residuals

from scipy.optimize import least_squares as lsq
rng = np.random.default_rng(0)
# LP members as starts (projected): solve LP then t = N^T (A_lp - A0)
lp_starts = []
for obj in ("deep", "flat"):
    c = np.zeros(nv)
    if obj == "deep":
        for key in kk:
            if nelem(key) >= 4: c[ii[key]] = -1.0
    else:
        c[:] = -1.0
    r = linprog(c, A_eq=C, b_eq=blin, bounds=[(0, 1000)] * nv,
                method="highs")
    if r.success: lp_starts.append(N.T @ (r.x - A0))
starts = lp_starts + [np.zeros(kdim)] \
    + [rng.normal(0, sc, kdim) for sc in (0.3, 1.0, 3.0) for _ in range(19)]

best = None; best_any = None
for i, t0 in enumerate(starts):
    t = t0
    for wneg in (30.0, 300.0, 3000.0, 30000.0):
        sol = lsq(make_res(wneg), t, xtol=1e-14, ftol=1e-14, gtol=1e-14,
                  max_nfev=4000)
        t = sol.x
        if amp_of(t).min() > -1e-8: break
    A = amp_of(t)
    rms = math.sqrt(np.mean(born_res_norm(A) ** 2))
    if best_any is None or rms < best_any[0]:
        best_any = (rms, t.copy(), i, A.min())
    if A.min() > -1e-6 and (best is None or rms < best[0]):
        best = (rms, t.copy(), i)
        print(f"start {i}: NEW BEST born-rms = {rms:.3e} "
              f"(minA = {A.min():.2e})", flush=True)
if best is None:
    print(f"no start reached minA > -1e-6; best-any: born-rms = "
          f"{best_any[0]:.3e} at minA = {best_any[3]:.2e}", flush=True)
    best = best_any[:3]

rms, t, i0 = best
A = amp_of(t)
sup = int(np.sum(A > 1e-7))
print(f"\nBEST over exactly-coherent nonneg family: normalized born-rms = "
      f"{rms:.6e} (start {i0}), support {sup}/{nv}, minA = {A.min():.3e}")
print(f"  raw born-rms at best point = "
      f"{math.sqrt(np.mean(born_res(A) ** 2)):.6e}")
dn = born_res_norm(A)
print("  worst 5 normalized parent defects:",
      " ".join(f"{x:.3f}" for x in sorted(np.abs(dn))[-5:]))
print(f"  coherent check |C A - b| = {np.linalg.norm(C @ A - blin):.2e}")
per = {}
for k in kk:
    if A[ii[k]] > 1e-7: per[nelem(k)] = per.get(nelem(k), 0) + 1
print("  support per level:", per)
print("READING: (a) exists if born-rms ~ 1e-10; "
      "(b) structural floor otherwise")
print("DONE")
