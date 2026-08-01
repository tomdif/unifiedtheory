#!/usr/bin/env python3
"""Characterization of the phi = 8pi partial-support survivor.

At 2D smearing eps = 1/4 (band top, l/xi = 1/2, W0 = 1/2 exactly) the
window (1/(4W0), 1/(2W0)) = (1/2, 1) contains no integer winding, yet
the full wave gate found partial support 1081/2450 at phi = 8pi
exactly (delta = 2pi: the resonant window BOUNDARY).  This script
characterizes the surviving set.

Arithmetic setting: at eps = 1/4 the smeared weights are dyadic
rationals (W(0)=1/2, W(1)=1/8, W(2)=-1/16, W(3)=-9/64, W(4)=-81/512,
...; W(k) = 2*(1/4)*f_2(k,1/4) with denominator 4^k), so at phi = 8pi
every channel phase e^{i g phi} is a dyadic root of unity: the system
is exact arithmetic in Z[zeta_{2^m}].  In particular both root
channels (gaps 1 and 1/2) carry phase +1 - the root equation is REAL,
branching with no phase, the resonant analog of the 4D null web's
real root.

Profiled invariants per causet: survival; order dimension <= 2;
height; max antichain width; interval-size census {k: #links with k
elements strictly between}; the causet's own phase e^{i S phi}
(dyadic angle, exact); whether all its outgoing channel phases are
real (+-1) vs genuinely complex.  Plus: solution-space dimension,
unitarity telescoping, per-level branching, and the interference
test - does any surviving equation carry a non-real coefficient on a
surviving child (genuine interference), or is the surviving web
phase-real throughout (branching without interference, null-web
class)?
"""
import itertools, math
from fractions import Fraction
import numpy as np
from scipy.optimize import linprog

# ---- exact dyadic weights at eps = 1/4 ------------------------------------
C2 = [1, -2, 1]
def W_exact(k):
    # 2 * eps * (1-eps)^k * sum_i C_i * C(k, i-1) * (eps/(1-eps))^(i-1)
    eps = Fraction(1, 4)
    x = eps / (1 - eps)
    tot = sum(Fraction(C2[i-1]) * math.comb(k, i-1) * x**(i-1)
              for i in range(1, 4))
    return 2 * eps * (1 - eps)**k * tot

def action_exact(rel, n):
    relset = set(rel)
    tot = Fraction(n)
    for (a, b) in rel:
        k = sum(1 for z in range(n) if (a, z) in relset and (z, b) in relset)
        tot -= W_exact(k)
    return tot

# phase of e^{i g * 8pi} for dyadic rational g: angle = 8*g mod 2 (in pi units)
def phase_angle_piunits(g):           # g Fraction -> Fraction in [0,2)
    return (8 * g) % 2

def canon_fast(n, rel):
    if not rel: return (n, ())
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

NMAX = 7
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
assert [counts[i] for i in range(1, 8)] == [1, 2, 5, 16, 63, 318, 2045]
print("tree validated (A000112)", flush=True)
root = canon_fast(1, ())
allkeys = [key for n in range(1, NMAX + 1) for key in sorted(levels[n])]
def nelem(key): return key[0]

# ---- children with EXACT gaps ---------------------------------------------
children = {}
for n in range(1, NMAX):
    for key, (m, rel) in sorted(levels[n].items()):
        S0 = action_exact(rel, m)
        below = {x: {a for (a, b) in rel if b == x} for x in range(m)}
        kid = {}
        for mask in range(1 << m):
            D = [i for i in range(m) if mask >> i & 1]
            if not all(below[x] <= set(D) for x in D): continue
            nr = tuple(sorted(set(rel) | {(d, m) for d in D}))
            ck = canon_fast(m + 1, nr)
            g = action_exact(nr, m + 1) - S0
            if ck in kid:
                mu, gg = kid[ck]
                assert gg == g
                kid[ck] = (mu + 1, gg)
            else: kid[ck] = (1, g)
        children[key] = kid

def descendants(seed):
    out = set(seed); frontier = list(seed)
    while frontier:
        k = frontier.pop()
        for ck in children.get(k, {}):
            if ck not in out: out.add(ck); frontier.append(ck)
    return out

# ---- the gate at phi = 8pi (exact phases as complex from dyadic angles) ----
def cphase(g):                        # e^{i g 8pi} exactly-angled
    ang = float(phase_angle_piunits(g)) * np.pi
    return complex(np.cos(ang), np.sin(ang))

def gate():
    U = set(allkeys)
    for rnd in range(80):
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
                z = mu * cphase(g)
                rr[ii[ck]] += z.real; ri[ii[ck]] += z.imag
            A_eq.append(rr); b_eq.append(0.0)
            A_eq.append(ri); b_eq.append(0.0)
        A_eq = np.array(A_eq); b_eq = np.array(b_eq)
        cobj = np.zeros(nvu)
        for key in U:
            if nelem(key) >= 5: cobj[ii[key]] = -1.0
        res = linprog(cobj, A_eq=A_eq, b_eq=b_eq, bounds=[(0, 1000)] * nvu,
                      method="highs")
        if not res.success: return set(), rnd
        Avals = {k: res.x[ii[k]] for k in kk}
        dead = set()
        for key in kk:
            if Avals[key] > 1e-9: continue
            c2 = np.zeros(nvu); c2[ii[key]] = -1.0
            r2 = linprog(c2, A_eq=A_eq, b_eq=b_eq, bounds=[(0, 1000)] * nvu,
                         method="highs")
            if (not r2.success) or -r2.fun < 1e-9: dead.add(key)
        if not dead: return U, rnd
        U = U - descendants(dead)
        if root not in U: return set(), rnd
    return U, 80

U, rnds = gate()
per = {}
for key in U: per[nelem(key)] = per.get(nelem(key), 0) + 1
print(f"\nsurvivors: {len(U)} (rounds {rnds})")
print("  per level: " + "  ".join(f"n={n}:{per.get(n,0)}/{counts[n]}"
                                  for n in range(1, NMAX + 1)), flush=True)

# ---- invariants ------------------------------------------------------------
def height(rel, m):
    if not rel: return 1
    succ = {v: [b for (a, b) in rel if a == v] for v in range(m)}
    memo = {}
    def h(v):
        if v not in memo:
            memo[v] = 1 + max((h(w) for w in succ[v]), default=0)
        return memo[v]
    return max(h(v) for v in range(m))

def width(rel, m):
    relset = set(rel)
    best = 1
    for mask in range(1 << m):
        S = [i for i in range(m) if mask >> i & 1]
        if all((a, b) not in relset and (b, a) not in relset
               for a in S for b in S if a < b):
            best = max(best, len(S))
    return best

def interval_census(rel, m):
    relset = set(rel)
    cen = {}
    for (a, b) in rel:
        k = sum(1 for z in range(m) if (a, z) in relset and (z, b) in relset)
        cen[k] = cen.get(k, 0) + 1
    return cen

def dim_le_2(key):
    m, rel = key
    if m <= 2 or not rel: return True
    relset = set(rel)
    succ = {v: {b for (a, b) in rel if a == v} for v in range(m)}
    incomp = [(a, b) for a in range(m) for b in range(a + 1, m)
              if (a, b) not in relset and (b, a) not in relset]
    if not incomp: return True
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
        edges = set(rel)
        for (a, b) in incomp:
            if pos[a] < pos[b]: edges.add((b, a))
            else: edges.add((a, b))
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

print("\n1. Channel-phase census (angle in units of pi, over ALL channels):")
angcount = {}
for key in allkeys:
    for ck, (mu, g) in children.get(key, {}).items():
        a = phase_angle_piunits(g)
        angcount[a] = angcount.get(a, 0) + 1
for a in sorted(angcount):
    print(f"   angle {str(a):>8}*pi : {angcount[a]} channels"
          f"{'   [REAL +1]' if a == 0 else '   [REAL -1]' if a == 1 else ''}")

print("\n2. Survivor predicate tests:")
# (a) order dimension
dimtab = {True: [0, 0], False: [0, 0]}   # dim<=2 -> [survive, die]
for key in allkeys:
    d2 = dim_le_2(key)
    dimtab[d2][0 if key in U else 1] += 1
print(f"   dim<=2: survive {dimtab[True][0]}, die {dimtab[True][1]}; "
      f"dim>=3: survive {dimtab[False][0]}, die {dimtab[False][1]}")
# (b) does survival = 'no non-real channel on the path'? test: causet's own
#     phase e^{iS phi} real?
sreal = {True: [0, 0], False: [0, 0]}
for key in allkeys:
    m, rel = key
    ang = phase_angle_piunits(action_exact(rel, m))
    isreal = (ang == 0) or (ang == 1)
    sreal[isreal][0 if key in U else 1] += 1
print(f"   e^(iS*phi) real: survive {sreal[True][0]}, die {sreal[True][1]}; "
      f"complex: survive {sreal[False][0]}, die {sreal[False][1]}")
# (c) height / width profile
print("   height x survival:")
for h in range(1, 8):
    s = sum(1 for key in U if height(key[1], key[0]) == h)
    t = sum(1 for key in allkeys if height(key[1], key[0]) == h)
    if t: print(f"     height {h}: {s}/{t}")
print("   width x survival:")
for w in range(1, 8):
    s = sum(1 for key in U if width(key[1], key[0]) == w)
    t = sum(1 for key in allkeys if width(key[1], key[0]) == w)
    if t: print(f"     width {w}: {s}/{t}")
# (d) interval census: max k present
print("   max interval size k x survival:")
for kmax in range(0, 6):
    s = t = 0
    for key in allkeys:
        cen = interval_census(key[1], key[0])
        mk = max(cen) if cen else -1
        if mk == kmax if kmax else mk <= 0:
            pass
    # recompute cleanly
print("     (recomputed)")
maxk = {}
for key in allkeys:
    cen = interval_census(key[1], key[0])
    maxk[key] = max(cen) if cen else 0
for kmax in sorted(set(maxk.values())):
    s = sum(1 for key in allkeys if maxk[key] == kmax and key in U)
    t = sum(1 for key in allkeys if maxk[key] == kmax)
    print(f"     max-k {kmax}: {s}/{t}")

print("\n3. Structure of the surviving web:")
# interference test: any surviving equation with a non-real coefficient on
# a surviving child?
cplx_eq = 0; real_eq = 0; cplx_pairs = 0
for key in sorted(U):
    if nelem(key) >= NMAX or key not in children: continue
    coeffs = [phase_angle_piunits(g) for ck, (mu, g) in children[key].items()
              if ck in U]
    if any(a not in (0, 1) for a in coeffs): cplx_eq += 1
    else: real_eq += 1
print(f"   surviving equations with complex coefficients: {cplx_eq}; "
      f"all-real: {real_eq}")
# branching among survivors
br = sum(1 for key in U if key in children
         and sum(1 for ck in children[key] if ck in U) >= 2)
print(f"   branching nodes among survivors: {br}")
# solution-space dimension at the survivor set
kk = sorted(U); ii = {k: i for i, k in enumerate(kk)}
rows = []
r0 = np.zeros(len(kk)); r0[ii[root]] = 1; rows.append(r0)
for key in kk:
    if nelem(key) >= NMAX: continue
    rr = np.zeros(len(kk)); ri = np.zeros(len(kk))
    rr[ii[key]] -= 1
    for ck, (mu, g) in children[key].items():
        if ck not in U: continue
        z = mu * cphase(g)
        rr[ii[ck]] += z.real; ri[ii[ck]] += z.imag
    rows.append(rr); rows.append(ri)
M = np.array(rows)
rank = np.linalg.matrix_rank(M, tol=1e-9)
print(f"   equations {M.shape[0]} x vars {M.shape[1]}, rank {rank}, "
      f"solution dim {M.shape[1] - rank}")
# unitarity telescoping on a feasible member: sum over stems of
# ext * A * e^{i(S-1)phi} per level
cobj = np.zeros(len(kk))
for key in U:
    if nelem(key) >= 5: cobj[ii[key]] = -1.0
res = linprog(cobj, A_eq=M[:1], b_eq=[1.0], bounds=[(0, 1000)] * len(kk),
              method="highs")   # placeholder solve; redo with full eqs
b = np.zeros(M.shape[0]); b[0] = 1.0
res = linprog(cobj, A_eq=M, b_eq=b, bounds=[(0, 1000)] * len(kk),
              method="highs")
if res.success:
    Avals = {k: res.x[ii[k]] for k in kk}
    for n in range(2, NMAX + 1):
        tot = 0j
        for key in kk:
            if nelem(key) != n: continue
            m, rel = key
            S = action_exact(rel, m)
            # ext = number of labeled paths root->key: recover by counting
            # (use multiplicity product along tree: approximate via LP not
            # needed - report amplitude-weighted phase sum instead)
            tot += Avals[key] * cphase(S - 1)
        print(f"   level {n}: sum A*e^(i(S-1)phi) = "
              f"{tot.real:+.6f}{tot.imag:+.6f}i  (ext-weights omitted)")
print("\n4. Smallest DEAD causets (the kill seeds):")
for n in range(2, 6):
    dead_n = [key for key in sorted(levels[n]) if key not in U]
    for key in dead_n:
        m, rel = key
        cen = interval_census(rel, m)
        print(f"   n={n}: rel={rel}  height={height(rel, m)} "
              f"width={width(rel, m)} intervals={cen} "
              f"S_angle={str(phase_angle_piunits(action_exact(rel, m)))}pi")
    if n >= 4 and len(dead_n) > 8: break
print("DONE", flush=True)
