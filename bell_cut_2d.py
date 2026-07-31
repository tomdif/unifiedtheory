#!/usr/bin/env python3
"""The selection-principle gates on the 2D survivor.

GATE A (strict quantum Bell causality = SZ ratio condition = signature
factoring): does ANY complex-RS dynamics carry the 2D action phases?
Amplitudes lambda(sig; t)/lambda(n,0; t) with arg = g*phi.  Gregarious
gap is identically +1 in 2D, so arg lambda(n,0) = -phi for all n and
each signature needs arg lambda(sig) = (g_sig - 1) phi -- unique gap per
signature required (collisions force lambda = 0), then a zero-pattern +
linear-feasibility search exactly as in 4D.

GATE B (modulus Bell causality, MBC): the ratio condition imposed on
MODULI only -- phases are automatically Bell-causal by gap locality.
On the coboundary family  a(C->C') = [A(C')/A(C)] e^{i g phi}  this is
LINEAR in u = log A:   u(C1) - u(C2) = u(B1) - u(B2)   for every parent
C with births p1, p2, reduced parent B = precursor-union stem, and the
same births from B.  Questions: (i) is the wave equation + MBC + strict
positivity feasible?  (ii) how far does MBC cut the 1639-dimensional
freedom (Jacobian rank at a solution)?
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
    for pp in itertools.product(*[itertools.permutations(c) for c in parts]):
        pos = {}
        i = 0
        for part in pp:
            for v in part:
                pos[v] = i; i += 1
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
print("levels:", {n: len(v) for n, v in levels.items()})
root = canon_fast(1, ())
def nelem(key): return key[0]
allkeys = [key for n in range(1, 7) for key in sorted(levels[n])]
children = {}
for n in range(1, 6):
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

# ===================== GATE A: strict QBC (factoring) ======================
print("=" * 72)
print("GATE A: strict quantum Bell causality (signature factoring) in 2D")
# signature -> set of (gap) over all transitions from parents n <= 4
sig_gaps = {}
for n in range(1, 5):
    for key, (m, rel) in levels[n].items():
        for D in downsets_of(m, rel):
            sig = (len(D), len([d for d in D
                                if not any((d, e) in rel for e in D)]))
            idx = {d: i for i, d in enumerate(sorted(D))}
            Dp = canon_fast(len(D), tuple(sorted((idx[x], idx[y])
                 for (x, y) in rel if x in D and y in D)))
            nr = tuple(sorted(set(rel) | {(d, m) for d in D}))
            g = action(nr, m + 1) - action(rel, m)
            sig_gaps.setdefault(sig, {})[Dp] = g
for sig in sorted(sig_gaps):
    gaps = sorted(set(sig_gaps[sig].values()))
    print(f"  sig {sig}: gaps {gaps}"
          + ("  [COLLISION -> lambda = 0 at generic phi]"
             if len(gaps) > 1 else ""))
SIGS = [(v, mm) for v in range(1, 5) for mm in range(1, v + 1)]
def lam_coeff(v, mm):
    c = np.zeros(5)
    for j in range(mm, v + 1):
        c[j] = math.comb(v - mm, j - mm)
    return c
LAM = {s: lam_coeff(*s) for s in SIGS}
def gateA(phi):
    best = None
    for nz in range(len(SIGS) + 1):
        for zero in itertools.combinations(SIGS, nz):
            zero = set(zero)
            # reachability + live constraint collection
            reach = {root}
            frontier = [root]
            while frontier:
                key = frontier.pop()
                if nelem(key) >= 5 or key not in children: continue
                m, rel = levels[nelem(key)][key]
                for D in downsets_of(m, rel):
                    sig = (len(D), len([d for d in D
                           if not any((d, e) in rel for e in D)]))
                    if sig != (0, 0) and sig in zero: continue
                    nr = tuple(sorted(set(rel) | {(d, m) for d in D}))
                    ck = canon_fast(m + 1, nr)
                    if ck not in reach:
                        reach.add(ck); frontier.append(ck)
            req = {}
            ok = True
            for key in reach:
                if nelem(key) >= 5 or key not in children: continue
                m, rel = levels[nelem(key)][key]
                for D in downsets_of(m, rel):
                    sig = (len(D), len([d for d in D
                           if not any((d, e) in rel for e in D)]))
                    if sig == (0, 0) or sig in zero: continue
                    nr = tuple(sorted(set(rel) | {(d, m) for d in D}))
                    g = action(nr, m + 1) - action(rel, m)
                    req.setdefault(sig, set()).add(g)
            for sig, gs in req.items():
                if len(gs) > 1: ok = False    # generic phi: no reconciliation
            if not ok: continue
            # linear feasibility: t1..t4 complex; phases:
            # arg lambda(sig) = (g_sig - 1) phi; denominators arg = -phi
            A_eq, b_eq, A_ub, b_ub = [], [], [], []
            EPS = 1e-4
            def rows(cvec, phase):
                rr = np.zeros(8); ri = np.zeros(8)
                for j in range(1, 5):
                    c = cvec[j] * np.exp(-1j * phase)
                    rr[2*(j-1)] += c.real; rr[2*(j-1)+1] += -c.imag
                    ri[2*(j-1)] += c.imag; ri[2*(j-1)+1] += c.real
                return rr, ri
            for sig in SIGS:
                cvec = LAM[sig]
                if sig in zero:
                    rr, ri = rows(cvec, 0.0)
                    A_eq += [rr, ri]; b_eq += [0.0, 0.0]
                elif sig in req:
                    g = next(iter(req[sig]))
                    rr, ri = rows(cvec, (g - 1) * phi)
                    A_eq.append(ri); b_eq.append(0.0)
                    A_ub.append(-rr); b_ub.append(-EPS)
            for r in range(1, 5):   # denominators: arg = -phi, modulus > 0
                cvec = np.array([math.comb(r, j) if j <= r else 0
                                 for j in range(5)], dtype=float)
                rr, ri = rows(cvec, -phi)
                # lambda(r,0) = 1 + sum_{j>=1}: e^{i phi}(1) + rotated rest
                z0 = np.exp(1j * phi)   # constant term rotated
                A_eq.append(ri); b_eq.append(-z0.imag)
                A_ub.append(-rr); b_ub.append(z0.real - EPS)
            res = linprog(np.zeros(8),
                          A_ub=np.array(A_ub) if A_ub else None,
                          b_ub=np.array(b_ub) if b_ub else None,
                          A_eq=np.array(A_eq) if A_eq else None,
                          b_eq=np.array(b_eq) if b_eq else None,
                          bounds=[(-50, 50)] * 8, method="highs")
            if res.success:
                live = [s for s in SIGS if s not in zero and s in req]
                cand = (len(live), live)
                if best is None or cand > best: best = cand
    return best

for phi, lab in [(0.90, "0.90 rad"), (np.pi / 3, "pi/3")]:
    b = gateA(phi)
    if b is None:
        print(f"  phi={lab}: NO factored dynamics at any zero-pattern")
    else:
        print(f"  phi={lab}: max factored dynamics: live signatures {b[1]}")

# ===================== GATE B: modulus Bell causality ======================
print("=" * 72)
print("GATE B: modulus Bell causality on the coboundary family (n <= 6)")
idx = {key: i for i, key in enumerate(allkeys)}
nv = len(idx)
# wave equations (complex) at n <= 5
wave = []
for n in range(1, 6):
    for key in sorted(levels[n]):
        rowz = np.zeros(nv, dtype=complex)
        rowz[idx[key]] -= 1
        for ck, (mu, g) in children[key].items():
            rowz[idx[ck]] += mu * np.exp(1j * g * 0.90)
        wave.append(rowz)
wave = np.array(wave)
# MBC rows in u-space
mbc_rows = set()
for n in range(2, 6):
    for key, (m, rel) in levels[n].items():
        ds = downsets_of(m, rel)
        for D1, D2 in itertools.combinations(ds, 2):
            Bset = D1 | D2
            if len(Bset) == m: continue           # no spectators
            Bl = sorted(Bset)
            bidx = {d: i for i, d in enumerate(Bl)}
            Brel = tuple(sorted((bidx[x], bidx[y]) for (x, y) in rel
                                if x in Bset and y in Bset))
            nb = len(Bl)
            def child(baserel, basen, DD, remap=None):
                DDm = {remap[d] for d in DD} if remap else set(DD)
                nr = tuple(sorted(set(baserel) | {(d, basen) for d in DDm}))
                return canon_fast(basen + 1, nr)
            C1 = child(rel, m, D1); C2 = child(rel, m, D2)
            B1 = child(Brel, nb, D1, bidx); B2 = child(Brel, nb, D2, bidx)
            if C1 == C2 or B1 == B2: continue
            row = np.zeros(nv)
            row[idx[C1]] += 1; row[idx[C2]] -= 1
            row[idx[B1]] -= 1; row[idx[B2]] += 1
            if np.any(row):
                mbc_rows.add(tuple(np.nonzero(row)[0].tolist())
                             + tuple(row[np.nonzero(row)[0]].tolist()))
M = []
for t in mbc_rows:
    half = len(t) // 2
    row = np.zeros(nv)
    for i in range(half):
        row[int(t[i])] = t[half + i]
    M.append(row)
M = np.array(M)
print(f"  MBC constraints: {len(M)} distinct rows, rank "
      f"{np.linalg.matrix_rank(M)}")
# strictly positive wave witness via LP (real embedding), then refine
Awr = np.vstack([np.hstack([wave.real]), np.hstack([wave.imag])])
rows0 = np.zeros((1, nv)); rows0[0, idx[root]] = 1
A_eq = np.vstack([rows0, Awr]); b_eq = np.zeros(A_eq.shape[0]); b_eq[0] = 1
res = linprog(np.zeros(nv), A_eq=A_eq, b_eq=b_eq,
              bounds=[(1e-3, 1000)] * nv, method="highs")
print(f"  strictly-positive wave solution exists: {res.success}")
if res.success:
    u0 = np.log(res.x)
    scale = np.concatenate([np.ones(1 + 2 * len(wave)),
                            np.zeros(0)])
    def resid(u):
        A = np.exp(u)
        r1 = A_eq @ A - b_eq
        r2 = M @ u
        return np.concatenate([r1, 0.3 * r2])
    sol = least_squares(resid, u0, method="lm", max_nfev=8000)
    r1 = A_eq @ np.exp(sol.x) - b_eq
    r2 = M @ sol.x
    print(f"  combined wave+MBC least-squares: |wave| = "
          f"{np.linalg.norm(r1):.2e}, |MBC| = {np.linalg.norm(r2):.2e}")
    feasible = np.linalg.norm(r1) < 1e-7 and np.linalg.norm(r2) < 1e-6
    print(f"  => wave + MBC + positivity feasible: {feasible}")
    Asol = np.exp(sol.x)
    Jwave = A_eq * Asol[None, :]
    Jall = np.vstack([Jwave, M])
    rk_w = np.linalg.matrix_rank(Jwave)
    rk_a = np.linalg.matrix_rank(Jall)
    print(f"  dimension: wave-only {nv - rk_w}; wave+MBC {nv - rk_a}"
          f"  (cut: {rk_a - rk_w})")
