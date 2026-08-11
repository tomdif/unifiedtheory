#!/usr/bin/env python3
"""GATE 1: does the quantum sector survive bi-normalization?

Sharp form: an ACTION-PHASED bi-normalized growth law assigns, at each
parent p, per-child-class weights rho_c >= 0 with amplitudes
b_c = rho_c e^{i g_c phi} (g_c = action gap, integer), satisfying
  coherent:  sum_c mu_c rho_c e^{i g_c phi} = 1
  Born:      sum_c mu_c rho_c^2            = 1
This keeps the wave family's rho e^{iS/hbar} structure (real weight x
action phase) inside the double-conservation law.  Covariance = weights
depend only on (parent class, child class).

HAND-DERIVED ANCHOR (registered before the scan): at the ROOT (children
2-chain/2-antichain, gaps -1/+1), Im forces rho1 = rho2, Re gives
2 rho cos phi = 1, Born gives 2 rho^2 = 1  =>  cos phi = 1/sqrt2:
**phi = pi/4 exactly** (or the conjugate -pi/4 = arrow mirror).  The
Born constraint QUANTIZES the phase at the Born-quadrature point.
Depth-2 hand checks: 2-antichain parent feasible at pi/4 with positive
rho in Z[sqrt2]; 2-chain parent feasible but forces the 3-chain child
to weight zero.

Registered readings:
  (i)  pi/4 closure survives to depth 7 with substantial support:
       quantum sector SURVIVES and SHARPENS (phase pinned, not free).
  (ii) closure collapses by depth <= 4: action phases and double
       conservation incompatible; completion #3 loses the quantum
       sector.
  (iii) scan finds other phi feasible for ALL parents incl. root:
       root analysis wrong (checked exactly).

Method per parent (classes (g_c, mu_c), phase phi):
  polytope P = {rho >= 0 : 2 linear eqs}; feasible for Born=1 iff
  P nonempty AND minQP(sum mu rho^2) <= 1 AND (unbounded OR
  max-over-vertices >= 1); vertices have <= 2 nonzero coords.
Then at phi = pi/4: fixed-point closure (forbid infeasible parents,
re-solve with forced zeros, propagate), construct explicit law
(bisect Born=1 on segment from QP-argmin to a >=1 vertex/ray), and run
the records test (Q/P stems, X_minus/X_plus) on the constructed law.
"""
import itertools, math, sys, time
import numpy as np
from scipy.optimize import linprog, minimize

T0 = time.time()
def log(*a): print(f"[{time.time()-T0:7.1f}s]", *a, flush=True)

NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 7

# ---------------- engine ----------------------------------------------------
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
counts = {n: len(v) for n, v in levels.items()}
log("levels:", counts)
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
parents = [k for k in allkeys if nelem(k) < NMAX]
log(f"parents: {len(parents)}")

# ---------------- per-parent feasibility ------------------------------------
EPS = 1e-9

def parent_system(p, phi, forbid=()):
    cls = [(ck, mu, g) for ck, (mu, g) in children[p].items()]
    K = len(cls)
    cos = np.array([math.cos(g * phi) for _, _, g in cls])
    sin = np.array([math.sin(g * phi) for _, _, g in cls])
    mu = np.array([m for _, m, _ in cls], float)
    A = np.vstack([mu * cos, mu * sin])
    b = np.array([1.0, 0.0])
    fixzero = [i for i, (ck, _, _) in enumerate(cls) if ck in forbid]
    return cls, K, A, b, mu, fixzero

def feasible_born(p, phi, forbid=(), want_point=False):
    """is there rho >= 0 (forbidden classes = 0) with A rho = b and
       sum mu rho^2 = 1?  returns (bool, rho or None)."""
    cls, K, A, b, mu, fz = parent_system(p, phi, forbid)
    keep = [i for i in range(K) if i not in fz]
    if not keep: return False, None
    Ak = A[:, keep]; muk = mu[keep]
    # polytope nonempty?
    r = linprog(np.zeros(len(keep)), A_eq=Ak, b_eq=b,
                bounds=[(0, None)] * len(keep), method="highs")
    if not r.success: return False, None
    x0 = r.x
    # min QP
    res = minimize(lambda x: float(np.dot(muk, x * x)), x0,
                   jac=lambda x: 2 * muk * x,
                   constraints=[{"type": "eq",
                                 "fun": lambda x: Ak @ x - b,
                                 "jac": lambda x: Ak}],
                   bounds=[(0, None)] * len(keep), method="SLSQP",
                   options={"maxiter": 200, "ftol": 1e-14})
    xm = res.x if res.success else x0
    m = float(np.dot(muk, xm * xm))
    if m > 1 + 1e-7: return False, None
    # max: vertices (<=2 nonzeros) and recession cone
    best_hi = None; xv = None
    for i in range(len(keep)):
        if abs(Ak[1, i]) < 1e-12 and Ak[0, i] > 1e-12:
            rho = 1.0 / Ak[0, i]
            v = np.zeros(len(keep)); v[i] = rho
            val = muk[i] * rho * rho
            if best_hi is None or val > best_hi: best_hi, xv = val, v
    for i, j in itertools.combinations(range(len(keep)), 2):
        M2 = Ak[:, [i, j]]
        det = M2[0, 0] * M2[1, 1] - M2[0, 1] * M2[1, 0]
        if abs(det) < 1e-12: continue
        s = np.linalg.solve(M2, b)
        if s[0] < -1e-12 or s[1] < -1e-12: continue
        v = np.zeros(len(keep)); v[i], v[j] = max(s[0], 0), max(s[1], 0)
        val = float(np.dot(muk, v * v))
        if best_hi is None or val > best_hi: best_hi, xv = val, v
    # recession cone: max sum rho on {A rho = 0, 0<=rho<=1}
    rc = linprog(-np.ones(len(keep)), A_eq=Ak, b_eq=np.zeros(2),
                 bounds=[(0, 1)] * len(keep), method="highs")
    unbounded = rc.success and (-rc.fun) > 1e-9
    if best_hi is None and not unbounded:
        return False, None
    hi_ok = unbounded or (best_hi is not None and best_hi >= 1 - 1e-7)
    if not hi_ok: return False, None
    if not want_point:
        return True, None
    # construct a point with sum mu rho^2 = 1: bisect on segment/ray
    if best_hi is not None and best_hi >= 1 - 1e-12:
        xhi = xv
    else:
        d = rc.x / max(np.linalg.norm(rc.x), 1e-30)
        t = 1.0
        while float(np.dot(muk, (xm + t * d) ** 2)) < 1: t *= 2
        xhi = xm + t * d
    lo, hi = 0.0, 1.0
    f = lambda t: float(np.dot(muk, ((1 - t) * xm + t * xhi) ** 2)) - 1.0
    if f(0) > 0: xsol = xm
    else:
        for _ in range(200):
            mid = 0.5 * (lo + hi)
            if f(mid) <= 0: lo = mid
            else: hi = mid
        xsol = (1 - lo) * xm + lo * xhi
        # polish scale on the segment endpoint
    rho = np.zeros(K)
    for idx, i in enumerate(keep): rho[i] = max(xsol[idx], 0.0)
    return True, (cls, rho)

# ---------------- Stage A: phase scan ---------------------------------------
log("=== STAGE A: per-parent feasibility scan over phi ===")
PHIS = list(np.linspace(0.02, 1.55, 154)) + [math.pi / 4]
scan_parents = parents if NMAX <= 7 else [k for k in parents if nelem(k) <= 5]
summary = []
for phi in PHIS:
    nf = 0; per = {}
    root_ok = feasible_born(root, phi)[0]
    for p in scan_parents:
        ok, _ = feasible_born(p, phi)
        if ok:
            nf += 1
            per[nelem(p)] = per.get(nelem(p), 0) + 1
    summary.append((phi, nf, root_ok, dict(per)))
    if abs(phi - math.pi / 4) < 1e-12 or nf == len(scan_parents) or root_ok:
        log(f"phi={phi:.4f}: feasible {nf}/{len(scan_parents)} "
            f"root={'Y' if root_ok else 'n'} per-level {per}")
allfeas = [s for s in summary if s[1] == len(scan_parents)]
rootfeas = [s for s in summary if s[2]]
log(f"phis with ALL parents feasible: "
    f"{[f'{s[0]:.4f}' for s in allfeas] or 'NONE'}")
log(f"phis with ROOT feasible: {[f'{s[0]:.4f}' for s in rootfeas]}")

# ---------------- Stage B: pi/4 closure -------------------------------------
log("=== STAGE B: closure + explicit law at phi = pi/4 ===")
PHI4 = math.pi / 4
forbidden = set()
for it in range(60):
    newly = set()
    for p in parents:
        if p in forbidden: continue
        ok, _ = feasible_born(p, PHI4, forbid=forbidden)
        if not ok: newly.add(p)
    if not newly:
        log(f"closure converged after {it} rounds; "
            f"forbidden parents {len(forbidden)}")
        break
    forbidden |= newly
    log(f"round {it}: newly forbidden {len(newly)} "
        f"(total {len(forbidden)})")
if root in forbidden:
    log("ROOT FORBIDDEN — reading (ii), theory empty"); sys.exit(0)

# construct law + reachable support
law = {}
support = {root}
frontier = [root]
while frontier:
    nxt = []
    for p in frontier:
        if nelem(p) >= NMAX or p in forbidden: continue
        ok, pt = feasible_born(p, PHI4, forbid=forbidden, want_point=True)
        assert ok, p
        cls, rho = pt
        for i, (ck, mu, g) in enumerate(cls):
            if rho[i] > 1e-10:
                law[(p, ck)] = rho[i] * np.exp(1j * g * PHI4)
                if ck not in support:
                    support.add(ck); nxt.append(ck)
    frontier = nxt
per = {}
for k in support: per[nelem(k)] = per.get(nelem(k), 0) + 1
log(f"pi/4 law support per level: {per}")
# verify double conservation on constructed law
worst_c = worst_b = 0.0
for p in support:
    if nelem(p) >= NMAX or p in forbidden: continue
    cs = sum(children[p][ck][0] * law.get((p, ck), 0.0)
             for ck, _ in children[p].items())
    bs = sum(children[p][ck][0] * abs(law.get((p, ck), 0.0)) ** 2
             for ck, _ in children[p].items())
    worst_c = max(worst_c, abs(cs - 1)); worst_b = max(worst_b, abs(bs - 1))
log(f"law checks: worst |coherent-1| = {worst_c:.2e}, "
    f"worst |Born-1| = {worst_b:.2e}")

# ---------------- Stage C: records test on the pi/4 law ---------------------
log("=== STAGE C: records test on the action-phased pi/4 law ===")
stems3 = sorted(levels[3]); stems4 = sorted(levels[4])
STEMS = stems3 + stems4[:6]
def contains_stem(key, stem):
    m, rel = key
    sm, srel = stem
    for D in downsets_of(m, rel):
        if len(D) != sm: continue
        di = {d: i for i, d in enumerate(sorted(D))}
        sub = canon_fast(sm, tuple(sorted((di[x], di[y])
              for (x, y) in rel if x in D and y in D)))
        if sub == stem: return True
    return False
CONT = {}
for s in STEMS:
    for T in range(4, NMAX + 1):
        for key in levels[T]:
            CONT[(s, key)] = contains_stem(key, s)

Psi = {root: 1.0 + 0j}; W = {root: 1.0}
for key in allkeys:
    if key == root: continue
    Psi[key] = 0.0 + 0j; W[key] = 0.0
for p in allkeys:
    for ck, (mu, g) in children.get(p, {}).items():
        if (p, ck) not in law: continue
        Psi[ck] += Psi[p] * mu * law[(p, ck)]
        W[ck] += W[p] * mu * abs(law[(p, ck)]) ** 2
for T in range(1, NMAX + 1):
    log(f"  P(Omega) T={T}: {sum(W[k] for k in levels[T]):.12f}   "
        f"Q_classid(Omega): "
        f"{sum(abs(Psi[k])**2 for k in levels[T]):.4f}")

def table(meas):
    out = {}
    for T in range(4, NMAX + 1):
        om = sum(meas[k] for k in levels[T])
        for s in STEMS:
            num = sum(meas[k] for k in levels[T] if CONT[(s, k)])
            out.setdefault(s, []).append(num / om if om > 0 else float("nan"))
    return out
def churn(tab):
    X = Xm = Xp = 0.0
    for s in STEMS:
        v = tab[s]
        for j in range(1, len(v) - 1):
            d = v[j + 1] - v[j]
            X += abs(d); Xm += max(0, -d); Xp += max(0, d)
    return X, Xm, Xp
Qm = {k: abs(Psi[k]) ** 2 for k in allkeys}
Pm = {k: W[k] for k in allkeys}
names = {}
for i, s in enumerate(stems3): names[s] = f"s{i}"
for i, s in enumerate(stems4): names[s] = f"s{i+5}"
for lab, meas in (("Q", Qm), ("P", Pm)):
    tab = table(meas)
    log(f"--- stems under {lab} (pi/4 action-phased law, T=4..{NMAX}) ---")
    for s in STEMS:
        log(f"  {names[s]:4s} " + "  ".join(f"{x:.4f}" for x in tab[s]))
    X, Xm, Xp = churn(tab)
    log(f"  {lab}: X = {X:.4f}  X_minus = {Xm:.4f}  X_plus = {Xp:.4f}")
dmax = 0.0
tq, tp = table(Qm), table(Pm)
for s in STEMS:
    for q, p_ in zip(tq[s], tp[s]):
        dmax = max(dmax, abs(q - p_))
log(f"interference on stems: max|Q-P| = {dmax:.4f}")
log("DONE")
