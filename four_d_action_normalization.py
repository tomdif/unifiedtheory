#!/usr/bin/env python3
"""THE 4D ACTION-NORMALIZATION CONSISTENCY CHECK.

The discrete action enters the framework twice:
  QUANTUM: growth amplitudes rho e^{i g phi} with g the INTEGER
    Benincasa-Dowker bracket gap; double conservation (sum b = 1,
    sum |b|^2 = 1 per parent) restricts phi (in the 2D engine it
    forced phi = pi/4 uniquely).
  GRAVITATIONAL: the same integer bracket carries (4/sqrt6) hbar per
    unit in 4D (LayerA/CausalActionCoefficient.lean: prefactor 4/sqrt6
    + layer coefficients (1,-9,16,-8) normalize to Box - R/2; matching
    EH gives c = 1/2, l_disc = sqrt(8 pi) l_P, M_disc = 2.44e18 GeV).
Consistency: the amplitude must be e^{iS/hbar}, i.e. the 4D quantum
phase unit must be phi4 = 4/sqrt6 = 1.63299... (mod 2pi).  This script
computes where the 4D action-phased bi-normalized theory EXISTS WITH
GENUINE BRANCHING (a deterministic single-history law is the
VR-gate death), and locates 4/sqrt6 relative to that set.

4D action here: g4(C) = sum_x [1 - n0(x) + 9 n1(x) - 16 n2(x) + 8 n3(x)],
n_k(x) = #{y < x : |open interval (y,x)| = k} — the integer bracket of
the repo's 4D BD action, on the same unlabeled growth tree (2045
causets to n = 7).  Hand-verified anchors: g4 = 1, 1, 2, 10, 1, 1, 2,
3, 3 for point, 2-chain, 2-antichain, 3-chain, Lambda, V, chain+iso,
3-antichain, 4-chain.  KEY STRUCTURAL DIFFERENCE from 2D: the 2-chain
gap from the root is ZERO (chain growth is action-free in 4D), so the
root does NOT quantize phi; instead Im-cancellation forces the
2-antichain child to weight zero at every generic phi — the 4D root is
chain-deterministic, and branching must be earned at deeper parents
(e.g. the 2-chain parent, child gaps (+1, 0, +9), branches only where
sin(phi) and sin(9 phi) have OPPOSITE signs; phi = 4/sqrt6 = 1.633
lies between 4pi/9 = 1.396 and 5pi/9 = 1.745 where both are positive —
a dead zone at that parent).

Registered readings:
  (i)   CONSISTENT: 4/sqrt6 is in the branching set -> bare 4D
        consistency passes (report if additionally quantized).
  (ii)  RECALIBRATION: branching set nonempty but excludes 4/sqrt6 ->
        bare check fails; the nearest branching phi* rescales the
        matching: l^2 = 8 pi G (phi*/(4/sqrt6)), i.e.
        M_disc' = M_P / sqrt(8 pi phi*/(4/sqrt6)); report whether the
        shift keeps M_disc near the reduced-Planck/unification window.
  (iii) EMPTY: no phi gives branching -> the bare 4D BD phases kill
        branching double conservation (echoes the VR-gate determinism
        kill of the coherent 4D route); the 4D theory then requires
        the smeared/mesoscale action S_eps, and this check becomes a
        constraint on eps (registered follow-up).
"""
import itertools, math, sys, time
import numpy as np
from scipy.optimize import linprog, minimize

T0 = time.time()
def log(*a): print(f"[{time.time()-T0:7.1f}s]", *a, flush=True)

NMAX = 7
PHI_GRAV = 4.0 / math.sqrt(6.0)

# ---------------- engine ----------------------------------------------------
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

def action4(rel, n):
    """4D BD integer bracket: sum_x [1 - n0 + 9 n1 - 16 n2 + 8 n3]."""
    relset = set(rel)
    tot = 0
    for x in range(n):
        nk = [0, 0, 0, 0]
        for y in range(n):
            if (y, x) not in relset: continue
            k = sum(1 for z in range(n)
                    if (y, z) in relset and (z, x) in relset)
            if k <= 3: nk[k] += 1
        tot += 1 - nk[0] + 9 * nk[1] - 16 * nk[2] + 8 * nk[3]
    return tot

levels = {1: {canon_fast(1, ()): (1, ())}}
for n in range(1, NMAX):
    nxt = {}
    for key, (m, rel) in levels[n].items():
        for D in downsets_of(m, rel):
            nr = tuple(sorted(set(rel) | {(d, m) for d in D}))
            nxt[canon_fast(m + 1, nr)] = (m + 1, nr)
    levels[n + 1] = nxt
log("levels:", {n: len(v) for n, v in levels.items()})
root = canon_fast(1, ())
def nelem(key): return key[0]
allkeys = [key for n in range(1, NMAX + 1) for key in sorted(levels[n])]
G4 = {key: action4(levels[nelem(key)][key][1], nelem(key)) for key in allkeys}

# hand-verification anchors
anchors = {}
for key in sorted(levels[2]) + sorted(levels[3]):
    anchors[key] = G4[key]
log("g4 level-2:", [G4[k] for k in sorted(levels[2])],
    " level-3:", [G4[k] for k in sorted(levels[3])])
assert sorted(G4[k] for k in levels[2]) == [1, 2]
assert sorted(G4[k] for k in levels[3]) == [1, 1, 2, 3, 10]

children = {}
for n in range(1, NMAX):
    for key, (m, rel) in sorted(levels[n].items()):
        kid = {}
        for D in downsets_of(m, rel):
            nr = tuple(sorted(set(rel) | {(d, m) for d in D}))
            ck = canon_fast(m + 1, nr)
            g = G4[ck] - G4[key]
            if ck in kid: kid[ck] = (kid[ck][0] + 1, g)
            else: kid[ck] = (1, g)
        children[key] = kid
parents = [k for k in allkeys if nelem(k) < NMAX]
gaps = sorted(set(g for p in parents for _, (mu, g) in children[p].items()))
log(f"parents {len(parents)}; distinct 4D gaps range "
    f"{gaps[0]}..{gaps[-1]} ({len(gaps)} values)")

# ---------------- per-parent machinery (as in pi/4 unit) --------------------
rng = np.random.default_rng(0)
def parent_system(p, phi):
    cls = [(ck, mu, g) for ck, (mu, g) in children[p].items()]
    mu = np.array([m for _, m, _ in cls], float)
    g = np.array([gg for _, _, gg in cls], float)
    A = np.vstack([mu * np.cos(g * phi), mu * np.sin(g * phi)])
    return cls, mu, A, np.array([1.0, 0.0])

def born_point(mu, A, b, maxent=True):
    K = A.shape[1]
    r = linprog(np.zeros(K), A_eq=A, b_eq=b, bounds=[(0, None)] * K,
                method="highs")
    if not r.success: return None
    x0 = r.x
    res = minimize(lambda x: float(np.dot(mu, x * x)), x0,
                   jac=lambda x: 2 * mu * x,
                   constraints=[{"type": "eq", "fun": lambda x: A @ x - b,
                                 "jac": lambda x: A}],
                   bounds=[(0, None)] * K, method="SLSQP",
                   options={"maxiter": 300, "ftol": 1e-14})
    xm = res.x if res.success else x0
    m = float(np.dot(mu, xm * xm))
    if m > 1 + 1e-7: return None
    xhi = None
    for t in range(10):
        c = -np.ones(K) if t == 0 else rng.normal(size=K)
        v = linprog(c, A_eq=A, b_eq=b, bounds=[(0, None)] * K,
                    method="highs")
        if v.success and float(np.dot(mu, v.x * v.x)) >= 1 - 1e-9:
            xhi = v.x; break
    if xhi is None:
        rc = linprog(-np.ones(K), A_eq=A, b_eq=np.zeros(2),
                     bounds=[(0, 1)] * K, method="highs")
        if rc.success and (-rc.fun) > 1e-9:
            d = rc.x / np.linalg.norm(rc.x)
            t = 1.0
            while float(np.dot(mu, (xm + t * d) ** 2)) < 1: t *= 2
            xhi = xm + t * d
        else:
            best = None
            for i, j in itertools.combinations(range(K), 2):
                M2 = A[:, [i, j]]
                det = M2[0, 0] * M2[1, 1] - M2[0, 1] * M2[1, 0]
                if abs(det) < 1e-12: continue
                s = np.linalg.solve(M2, b)
                if s.min() < -1e-12: continue
                v = np.zeros(K); v[i], v[j] = s
                val = float(np.dot(mu, v * v))
                if best is None or val > best[0]: best = (val, v)
            if best is None or best[0] < 1 - 1e-7: return None
            xhi = best[1]
    f = lambda t: float(np.dot(mu, ((1 - t) * xm + t * xhi) ** 2)) - 1.0
    lo, hi = 0.0, 1.0
    for _ in range(100):
        mid = 0.5 * (lo + hi)
        if f(mid) <= 0: lo = mid
        else: hi = mid
    xfe = np.maximum((1 - lo) * xm + lo * xhi, 0.0)
    if not maxent: return xfe
    def negH(x):
        q = mu * x * x
        return float(np.sum(q * np.log(q + 1e-300)))
    cons = [{"type": "eq", "fun": lambda x: A @ x - b, "jac": lambda x: A},
            {"type": "eq", "fun": lambda x: float(np.dot(mu, x * x)) - 1.0,
             "jac": lambda x: 2 * mu * x}]
    best = (negH(xfe), xfe)
    r2 = minimize(negH, xfe, constraints=cons, bounds=[(0, None)] * K,
                  method="SLSQP", options={"maxiter": 300, "ftol": 1e-12})
    if r2.success:
        x2 = np.maximum(r2.x, 0.0)
        if (abs(float(np.dot(mu, x2 * x2)) - 1) < 1e-6 and
                np.max(np.abs(A @ x2 - b)) < 1e-6 and negH(x2) < best[0]):
            best = (negH(x2), x2)
    return best[1]

def theory_at(phi, detail=False):
    """build max-entropy law from the root; return effN(n) profile."""
    law = {}
    support = {root}; frontier = [root]
    dead_end = False
    while frontier:
        nxt = []
        for p in frontier:
            if nelem(p) >= NMAX: continue
            cls, mu, A, b = parent_system(p, phi)
            x = born_point(mu, A, b)
            if x is None:
                dead_end = True
                continue
            for i, (ck, muc, g) in enumerate(cls):
                if x[i] > 1e-9:
                    law[(p, ck)] = x[i] * np.exp(1j * g * phi)
                    if ck not in support:
                        support.add(ck); nxt.append(ck)
        frontier = nxt
    W = {root: 1.0}
    for key in allkeys:
        if key != root: W[key] = 0.0
    for p in allkeys:
        for ck, (mu, g) in children.get(p, {}).items():
            if (p, ck) in law:
                W[ck] += W[p] * mu * abs(law[(p, ck)]) ** 2
    prof = {}
    for n in range(2, NMAX + 1):
        tot = sum(W[k] for k in levels[n])
        pr = tot ** 2 / max(sum(W[k] ** 2 for k in levels[n]), 1e-300)
        prof[n] = (tot, pr)
    if detail:
        sup = {}
        for k in support: sup[nelem(k)] = sup.get(nelem(k), 0) + 1
        r7 = sum(W[k] * len(levels[NMAX][k][1]) for k in levels[NMAX]) / \
            max(sum(W[k] for k in levels[NMAX]), 1e-300) / (NMAX * (NMAX - 1) / 2)
        return prof, sup, dead_end, r7
    return prof

# ---------------- scan ------------------------------------------------------
log("=== scan phi in (0, pi], effN(7) of the max-entropy 4D law ===")
grid = list(np.arange(0.01, math.pi + 1e-9, 0.01)) + [PHI_GRAV]
grid = sorted(set(round(p, 6) for p in grid))
branchy = []
results = []
for phi in grid:
    prof = theory_at(phi)
    m7, e7 = prof[NMAX]
    results.append((phi, m7, e7))
    if e7 > 1.5 and m7 > 0.99:
        branchy.append(phi)
# report branching windows
log(f"phis with effN(7) > 1.5 and no mass leak: {len(branchy)}/{len(grid)}")
if branchy:
    # compress into windows
    wins = []
    start = prev = branchy[0]
    for x in branchy[1:]:
        if x - prev > 0.015:
            wins.append((start, prev)); start = x
        prev = x
    wins.append((start, prev))
    log("branching windows (phi): " +
        "  ".join(f"[{a:.3f},{b:.3f}]" for a, b in wins))
maxe = max(results, key=lambda t: t[2])
log(f"max branching: phi = {maxe[0]:.4f} effN(7) = {maxe[2]:.1f} "
    f"mass = {maxe[1]:.4f}")

# ---------------- the gravitational phase -----------------------------------
log(f"=== the gravitational phase phi4 = 4/sqrt6 = {PHI_GRAV:.6f} ===")
prof, sup, dead, r7 = theory_at(PHI_GRAV, detail=True)
log(f"profile at 4/sqrt6: " + "  ".join(
    f"n={n}: mass={prof[n][0]:.4f} effN={prof[n][1]:.2f}"
    for n in range(2, NMAX + 1)))
log(f"support per level: {sup}   dead-end parents hit: {dead}")
log(f"r(7) at 4/sqrt6: {r7:.4f}")
in_branch = any(abs(PHI_GRAV - p) < 0.006 for p in branchy)
log(f"4/sqrt6 in branching set: {in_branch}")
if branchy and not in_branch:
    near = min(branchy, key=lambda p: abs(p - PHI_GRAV))
    xfac = near / PHI_GRAV
    MP = 1.22089e19
    Mdisc = MP / math.sqrt(8 * math.pi)
    Mdisc2 = MP / math.sqrt(8 * math.pi * xfac)
    log(f"nearest branching phi* = {near:.4f}; ratio phi*/(4/sqrt6) = "
        f"{xfac:.4f}")
    log(f"M_disc: bare-matching {Mdisc:.3e} GeV -> quantum-corrected "
        f"{Mdisc2:.3e} GeV (factor {1/math.sqrt(xfac):.4f})")
log("DONE")
