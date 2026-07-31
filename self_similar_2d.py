#!/usr/bin/env python3
"""The self-similarity gate + the Minkowski-statistics optimization.

S1 (noted, not run): level-stationarity of transition amplitudes implies
same-precursor ratio equality => Bell causality => signature factoring
=> dead by the collision table (Gate A).  The native viable form is:

S2 SUB-SAMPLING SELF-SIMILARITY (Bombelli coarse-graining fixed point):
    Psi_n(c) = sum_C T_{n,N}(c, C) Psi_N(C),
T(c,C) = (#n-subsets of C inducing c)/binom(N,n) -- row-stochastic, so
the constraint is exactly normalized (sum Psi = 1 both sides); order
dimension is monotone under induced suborders, so it preserves manifold
confinement.  LINEAR in the amplitudes: 2 real rows per (n, c).  Gate:
add these rows to the confined depth-7 family for n in {6}, {5,6},
{4,5,6}: feasibility + dimension cut per strength.

O  R -> 1/2 OPTIMIZATION: within the (self-similar) confined family,
fit the boundary event amplitudes ext*A on n=7 stems to lambda *
sqrt(p_2o), where p_2o = the exact random-2-order distribution
(sampled): |Psi|^2 proportional to p_2o <=> psi proportional to
sqrt(p_2o).  Bounded linear least squares; report fit quality, the
|Psi|^2-weighted mean ordering fraction, and unitarity.
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
counts = {n: len(v) for n, v in levels.items()}
print("levels:", counts, flush=True)
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
print(f"confined support: {len(U)}", flush=True)
kk = sorted(U); ii = {k: i for i, k in enumerate(kk)}
nvu = len(kk)
phi = 0.90
ext = {root: 1}
for n in range(1, NMAX):
    for key in sorted(levels[n]):
        if key not in ext: continue
        for ck, (mu, g) in children[key].items():
            ext[ck] = ext.get(ck, 0) + mu * ext[key]

def wave_rows():
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
    return np.array(A_eq), np.array(b_eq)
Aw, bw = wave_rows()

# ---- sub-sampling kernel rows: Psi_n = T Psi_7 -----------------------------
def subsample_rows(nsmall):
    rows, rhs = [], []
    stems7 = [k for k in kk if nelem(k) == 7]
    # T columns
    Tcol = {}
    for C in stems7:
        m, rel = C
        relset = set(rel)
        cnt = {}
        for S in itertools.combinations(range(m), nsmall):
            si = {v: i for i, v in enumerate(S)}
            sub = canon_fast(nsmall, tuple(sorted((si[a], si[b])
                  for (a, b) in rel if a in si and b in si)))
            cnt[sub] = cnt.get(sub, 0) + 1
        tot = math.comb(m, nsmall)
        Tcol[C] = {c: v / tot for c, v in cnt.items()}
    for c in sorted(k for k in kk if nelem(k) == nsmall):
        Sc = action(c[1], c[0])
        rr = np.zeros(nvu); ri = np.zeros(nvu)
        ph_c = np.exp(1j * Sc * phi) * ext.get(c, 0)
        rr[ii[c]] -= ph_c.real; ri[ii[c]] -= ph_c.imag
        for C in stems7:
            t = Tcol[C].get(c, 0.0)
            if t == 0: continue
            z = t * ext.get(C, 0) * np.exp(1j * action(C[1], C[0]) * phi)
            rr[ii[C]] += z.real; ri[ii[C]] += z.imag
        rows.append(rr); rhs.append(0.0)
        rows.append(ri); rhs.append(0.0)
    return np.array(rows), np.array(rhs)

print("=" * 72)
print("S2 sub-sampling self-similarity gate (confined family, depth 7):",
      flush=True)
strengths = [("n=6 only", [6]), ("n=5,6", [5, 6]), ("n=4,5,6", [4, 5, 6])]
best_sys = None
for lab, ns in strengths:
    A = [Aw]; b = [bw]
    for nn in ns:
        Ar, br = subsample_rows(nn)
        A.append(Ar); b.append(br)
    A = np.vstack(A); b = np.concatenate(b)
    res = linprog(np.zeros(nvu), A_eq=A, b_eq=b, bounds=[(0, 1000)] * nvu,
                  method="highs")
    if res.success:
        rank = np.linalg.matrix_rank(A)
        print(f"  {lab}: FEASIBLE; dim {nvu - rank} "
              f"(wave-only confined: {nvu - np.linalg.matrix_rank(Aw)})",
              flush=True)
        best_sys = (lab, A, b)
    else:
        print(f"  {lab}: INFEASIBLE", flush=True)

# ---- random-2-order target at n = 7 ----------------------------------------
print("=" * 72)
print("sampling random 2-orders at n=7...", flush=True)
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
print(f"  distinct 2-order classes sampled: {len(p2o)}", flush=True)

def fit_and_report(lab, A, b):
    stems7 = [k for k in kk if nelem(k) == 7]
    targ = np.array([math.sqrt(p2o.get(k, 0.0)) for k in stems7])
    # variables: A_tilde (nvu) and lambda; hard rows: [A | 0]; soft rows:
    # ext*A_tilde(stem) - lambda*sqrt(p): weight w_s
    HW, SW = 300.0, 1.0
    nrow_h = A.shape[0]
    M = np.zeros((nrow_h + len(stems7), nvu + 1))
    y = np.zeros(nrow_h + len(stems7))
    M[:nrow_h, :nvu] = HW * A; y[:nrow_h] = HW * b
    for i, kkey in enumerate(stems7):
        M[nrow_h + i, ii[kkey]] = SW * ext.get(kkey, 0)
        M[nrow_h + i, nvu] = -SW * targ[i]
    lb = np.zeros(nvu + 1); ub = np.full(nvu + 1, np.inf)
    sol = lsq_linear(M, y, bounds=(lb, ub), max_iter=300, tol=1e-12)
    At = sol.x[:nvu]; lam = sol.x[nvu]
    hard = np.linalg.norm(A @ At - b)
    psi = np.array([ext.get(kkey, 0) * At[ii[kkey]] for kkey in stems7])
    soft = np.linalg.norm(psi - lam * targ) / max(np.linalg.norm(lam * targ),
                                                  1e-12)
    w = psi ** 2
    if w.sum() > 0:
        def ofrac(k): return len(k[1]) / (k[0] * (k[0] - 1) / 2)
        rmean = sum(wi * ofrac(kkey) for wi, kkey in zip(w, stems7)) / w.sum()
    else:
        rmean = float("nan")
    print(f"  [{lab}] hard-constraint residual {hard:.2e}; "
          f"relative fit to sqrt(p_2o): {soft:.3f}; "
          f"|Psi|^2-weighted mean r = {rmean:.4f} (target 0.5)", flush=True)

print("=" * 72)
print("O: Minkowski-statistics fit (psi ~ sqrt(p_2o)):", flush=True)
fit_and_report("wave-only confined", Aw, bw)
if best_sys is not None:
    lab, A, b = best_sys
    fit_and_report(f"self-similar ({lab})", A, b)

# ---- proper composed fit: nullspace elimination ----------------------------
print("=" * 72)
print("composed fit, exact elimination (wave + subsample-6):", flush=True)
if best_sys is not None:
    lab, Ac, bc = best_sys
    # particular solution + nullspace
    from numpy.linalg import svd, lstsq
    x0, *_ = lstsq(Ac, bc, rcond=None)
    U_, S_, Vt = svd(Ac, full_matrices=True)
    tol = S_.max() * 1e-10
    rk = int((S_ > tol).sum())
    Nb = Vt[rk:].T                       # nvu x (nvu - rk)
    print(f"  rank {rk}, nullspace dim {Nb.shape[1]}", flush=True)
    stems7 = [k for k in kk if nelem(k) == 7]
    targ = np.array([math.sqrt(p2o.get(k, 0.0)) for k in stems7])
    Erow = np.zeros((len(stems7), nvu))
    for i, kkey in enumerate(stems7):
        Erow[i, ii[kkey]] = ext.get(kkey, 0)
    from scipy.optimize import least_squares as LSQ
    def resid(zz):
        z = zz[:-1]; lam = zz[-1]
        At = x0 + Nb @ z
        fit = Erow @ At - lam * targ
        pen = np.minimum(At, 0.0) * 30.0
        return np.concatenate([fit, pen])
    zz0 = np.zeros(Nb.shape[1] + 1); zz0[-1] = 1.0
    sol = LSQ(resid, zz0, method="trf", max_nfev=300)
    z = sol.x[:-1]; lam = sol.x[-1]
    At = x0 + Nb @ z
    hard = np.linalg.norm(Ac @ At - bc)
    negs = float(np.abs(np.minimum(At, 0)).max())
    psi = Erow @ At
    rel = np.linalg.norm(psi - lam * targ) / max(abs(lam) * np.linalg.norm(targ), 1e-12)
    w = np.maximum(psi, 0) ** 2
    def ofrac(k): return len(k[1]) / (k[0] * (k[0] - 1) / 2)
    rmean = (sum(wi * ofrac(kkey) for wi, kkey in zip(w, stems7)) / w.sum()
             if w.sum() > 0 else float("nan"))
    print(f"  hard residual {hard:.2e}; max negativity {negs:.2e}; "
          f"relative fit {rel:.3f}; |Psi|^2-weighted mean r = {rmean:.4f}",
          flush=True)
