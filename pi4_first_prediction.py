#!/usr/bin/env python3
"""THE pi/4 THEORY'S FIRST NUMBER: ordering fraction under the
quantized-phase Born chain, versus manifold and entropic baselines —
plus the depth trend of record interference.

Why this is the "new physics from here" move: the coherent program's
terminus was existence-abundant/nothing-selects — at depth 8 the wave
family's ordering fraction was a POLYTOPE, r_psi(8) in [0.105, 0.804]
(selfsim_depth8.log), and every selection principle died.  The
bi-normalized action-phased theory has NO free phase (pi/4 forced,
quadrature-phase-gates-2026-08-11) and its Born diagonal is a genuine
Markov chain, so it outputs NUMBERS.  At parents with <= 3 child
classes the three constraints (Re, Im, Born) generically pin the
weights uniquely (2-chain parent exactly forced; 2-antichain unique
positive root); residual freedom lives only at high-branching parents.

Computed here (all exact tree DP at depth 8; NO LP polytopes):
  1. pi/4 feasibility at ALL 2450 parents n <= 7 (first test beyond
     n = 6), with forbidden-closure if needed.
  2. Selections on the residual freedom: (a) MAX-ENTROPY of the Born
     child distribution q_c = mu rho^2 (canonical maximal-ignorance
     growth, registered); (b) five RANDOM feasible laws (random LP
     objective -> Born bisection) to measure selection sensitivity.
  3. THE NUMBER: mean ordering fraction r(n) = <#related pairs>/C(n,2)
     under the Born chain, n = 2..8.
  4. Baselines: (i) uniform-growth chain (each labeled child equally
     likely — the entropic/counting baseline); (ii) 2D causal-diamond
     sprinkling (n = 8 uniform points, related iff |dx| <= dt) — the
     manifold value; (iii) the wave family's logged polytope range
     [0.105, 0.804] (nothing-selects baseline).
  5. Record interference on stems, max|Q - P| and X_minus(Q), T = 4..8:
     does interference on records decay with horizon?

Registered readings (BEFORE the run):
  NUMBER: (i) MANIFOLD: |r_pi4(8) - r_sprink(8)| < 0.02 and closer to
          sprinkling than to uniform -> the quantized law selects
          manifold-like order statistics (emergent-2D signal).
          (ii) ENTROPIC: closer to uniform-growth -> dynamics adds
          ~nothing beyond counting (echoes entropy-dominance).
          (iii) NOVEL: >= 0.05 from both -> a new characteristic
          constant of the theory, meaning TBD.
          (iv) SELECTION-DOMINATED: spread across selections exceeds
          the baseline separation -> no sharp number; the selection
          principle becomes the binding problem.
  INTERFERENCE: (alpha) max|Q-P| on stems decays with T -> lambda < 1
          macroscopically viable with a scale-dependent signature;
          (beta) flat or growing -> macroscopic fact stability forces
          lambda -> 1 (records fully dephased in the deep limit).
"""
import itertools, math, sys, time
import numpy as np
from scipy.optimize import linprog, minimize

T0 = time.time()
def log(*a): print(f"[{time.time()-T0:7.1f}s]", *a, flush=True)

NMAX = 8
PHI4 = math.pi / 4
rng = np.random.default_rng(0)

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
log("levels:", {n: len(v) for n, v in levels.items()})
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

# ---------------- per-parent pi/4 machinery ---------------------------------
def parent_system(p, forbid=()):
    cls = [(ck, mu, g) for ck, (mu, g) in children[p].items()]
    keep = [i for i, (ck, _, _) in enumerate(cls) if ck not in forbid]
    mu = np.array([cls[i][1] for i in keep], float)
    g = np.array([cls[i][2] for i in keep], float)
    A = np.vstack([mu * np.cos(g * PHI4), mu * np.sin(g * PHI4)])
    return cls, keep, mu, A, np.array([1.0, 0.0])

def solve_endpoint(mu, A, b, cvec):
    """LP-optimize cvec over the polytope, return vertex (or None)."""
    r = linprog(cvec, A_eq=A, b_eq=b, bounds=[(0, None)] * A.shape[1],
                method="highs")
    return r.x if r.success else None

def born_point(mu, A, b, want="maxent", nrand=0):
    """return rho >= 0 with A rho = b, sum mu rho^2 = 1, or None.
       want: 'maxent' (max entropy of q = mu rho^2) or 'random'."""
    K = A.shape[1]
    x0 = solve_endpoint(mu, A, b, np.zeros(K))
    if x0 is None: return None
    # minQP
    res = minimize(lambda x: float(np.dot(mu, x * x)), x0,
                   jac=lambda x: 2 * mu * x,
                   constraints=[{"type": "eq", "fun": lambda x: A @ x - b,
                                 "jac": lambda x: A}],
                   bounds=[(0, None)] * K, method="SLSQP",
                   options={"maxiter": 300, "ftol": 1e-14})
    xm = res.x if res.success else x0
    m = float(np.dot(mu, xm * xm))
    if m > 1 + 1e-7: return None
    # a >= 1 endpoint: try vertices via random objectives + recession ray
    xhi = None
    for _ in range(12):
        c = rng.normal(size=K) if _ else -np.ones(K)
        v = solve_endpoint(mu, A, b, c)
        if v is not None and float(np.dot(mu, v * v)) >= 1 - 1e-9:
            xhi = v; break
    if xhi is None:
        rc = linprog(-np.ones(K), A_eq=A, b_eq=np.zeros(2),
                     bounds=[(0, 1)] * K, method="highs")
        if rc.success and (-rc.fun) > 1e-9:
            d = rc.x / np.linalg.norm(rc.x)
            t = 1.0
            while float(np.dot(mu, (xm + t * d) ** 2)) < 1: t *= 2
            xhi = xm + t * d
        else:
            # max over <=2-support vertices
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
    # bisect Born = 1 on segment
    f = lambda t: float(np.dot(mu, ((1 - t) * xm + t * xhi) ** 2)) - 1.0
    lo, hi = 0.0, 1.0
    for _ in range(100):
        mid = 0.5 * (lo + hi)
        if f(mid) <= 0: lo = mid
        else: hi = mid
    xfe = np.maximum((1 - lo) * xm + lo * xhi, 0.0)
    if want == "random":
        # re-do with a random objective endpoint for diversity
        for _ in range(6):
            c = rng.normal(size=K)
            v = solve_endpoint(mu, A, b, c)
            if v is None: continue
            if float(np.dot(mu, v * v)) >= 1 - 1e-9:
                g2 = lambda t: float(np.dot(mu,
                     ((1 - t) * xm + t * v) ** 2)) - 1.0
                lo2, hi2 = 0.0, 1.0
                for _ in range(100):
                    mid = 0.5 * (lo2 + hi2)
                    if g2(mid) <= 0: lo2 = mid
                    else: hi2 = mid
                return np.maximum((1 - lo2) * xm + lo2 * v, 0.0)
        return xfe
    # max-entropy of q = mu rho^2 subject to both constraints
    def negH(x):
        q = mu * x * x
        return float(np.sum(q * np.log(q + 1e-300)))
    cons = [{"type": "eq", "fun": lambda x: A @ x - b, "jac": lambda x: A},
            {"type": "eq", "fun": lambda x: float(np.dot(mu, x * x)) - 1.0,
             "jac": lambda x: 2 * mu * x}]
    bestH = (negH(xfe), xfe)
    for x0e in (xfe, xm + 0.5 * (xfe - xm)):
        r2 = minimize(negH, x0e, constraints=cons,
                      bounds=[(0, None)] * K, method="SLSQP",
                      options={"maxiter": 300, "ftol": 1e-12})
        if r2.success:
            x2 = np.maximum(r2.x, 0.0)
            ok = (abs(float(np.dot(mu, x2 * x2)) - 1) < 1e-6 and
                  np.max(np.abs(A @ x2 - b)) < 1e-6)
            if ok and negH(x2) < bestH[0]: bestH = (negH(x2), x2)
    return bestH[1]

# ---------------- feasibility at all parents + uniqueness hint --------------
log("=== pi/4 feasibility at all parents (incl. n=7) ===")
infeasible = []
free_dim = {}
for p in parents:
    cls, keep, mu, A, b = parent_system(p)
    x = born_point(mu, A, b)
    if x is None:
        infeasible.append(p)
        continue
    K = len(keep)
    free_dim[p] = max(0, K - 3)     # generic residual dimension
per = {}
for p in infeasible: per[nelem(p)] = per.get(nelem(p), 0) + 1
log(f"infeasible parents: {len(infeasible)} per level {per}")
nfree = sum(1 for p in free_dim if free_dim[p] > 0)
log(f"parents with generic residual freedom (K>3): {nfree}/{len(free_dim)}; "
    f"forced-or-discrete (K<=3): {len(free_dim) - nfree}")
FORBID = set(infeasible)
for _ in range(30):
    newly = []
    for p in parents:
        if p in FORBID: continue
        cls, keep, mu, A, b = parent_system(p, FORBID)
        if born_point(mu, A, b) is None: newly.append(p)
    if not newly: break
    FORBID.update(newly)
    log(f"closure: newly forbidden {len(newly)}")
log(f"final forbidden: {len(FORBID)}")
assert root not in FORBID

# ---------------- build laws ------------------------------------------------
def build_law(kind):
    law = {}
    support = {root}; frontier = [root]
    while frontier:
        nxt = []
        for p in frontier:
            if nelem(p) >= NMAX or p in FORBID: continue
            cls, keep, mu, A, b = parent_system(p, FORBID)
            x = born_point(mu, A, b, want=kind)
            if x is None: continue
            for idx, i in enumerate(keep):
                ck, muc, g = cls[i]
                if x[idx] > 1e-10:
                    law[(p, ck)] = x[idx] * np.exp(1j * g * PHI4)
                    if ck not in support:
                        support.add(ck); nxt.append(ck)
        frontier = nxt
    return law, support

def observables(law, tag, do_interference=False):
    Psi = {root: 1.0 + 0j}; W = {root: 1.0}
    for key in allkeys:
        if key == root: continue
        Psi[key] = 0.0 + 0j; W[key] = 0.0
    for p in allkeys:
        for ck, (mu, g) in children.get(p, {}).items():
            if (p, ck) not in law: continue
            Psi[ck] += Psi[p] * mu * law[(p, ck)]
            W[ck] += W[p] * mu * abs(law[(p, ck)]) ** 2
    rs = []
    for n in range(2, NMAX + 1):
        tot = sum(W[k] for k in levels[n])
        mean_r = sum(W[k] * len(levels[n][k][1]) for k in levels[n]) \
            / (tot * (n * (n - 1) / 2))
        # participation ratio (effective # causets)
        pr = tot ** 2 / max(sum(W[k] ** 2 for k in levels[n]), 1e-300)
        rs.append((n, mean_r, tot, pr))
    log(f"[{tag}] r(n), mass, effN:")
    for n, r_, tot, pr in rs:
        log(f"   n={n}: r = {r_:.4f}   mass = {tot:.6f}   effN = {pr:.1f}")
    out = {"r": {n: r_ for n, r_, _, _ in rs}}
    if do_interference:
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
        Qs, Ps = {}, {}
        for T in range(4, NMAX + 1):
            qom = sum(abs(Psi[k]) ** 2 for k in levels[T])
            pom = sum(W[k] for k in levels[T])
            for s in STEMS:
                qq = sum(abs(Psi[k]) ** 2 for k in levels[T]
                         if contains_stem(k, s)) / qom
                pp = sum(W[k] for k in levels[T]
                         if contains_stem(k, s)) / pom
                Qs.setdefault(s, []).append(qq)
                Ps.setdefault(s, []).append(pp)
        for j, T in enumerate(range(4, NMAX + 1)):
            dmax = max(abs(Qs[s][j] - Ps[s][j]) for s in STEMS)
            davg = np.mean([abs(Qs[s][j] - Ps[s][j]) for s in STEMS])
            log(f"   T={T}: record interference max = {dmax:.4f} "
                f"mean = {davg:.4f}")
        xm = 0.0
        for s in STEMS:
            for j in range(1, NMAX - 4):
                xm += max(0.0, Qs[s][j] - Qs[s][j + 1])
        log(f"   X_minus(Q) over T=5..{NMAX}: {xm:.4f}")
    return out

log("=== LAW 1: max-entropy selection ===")
law_me, sup_me = build_law("maxent")
per = {}
for k in sup_me: per[nelem(k)] = per.get(nelem(k), 0) + 1
log(f"support per level: {per}")
res_me = observables(law_me, "pi/4 max-entropy", do_interference=True)

log("=== LAWS 2-6: random selections (sensitivity) ===")
r8s = []
for i in range(5):
    law_r, _ = build_law("random")
    res = observables(law_r, f"pi/4 random {i}")
    r8s.append(res["r"][NMAX])
log(f"r(8) across random selections: "
    + " ".join(f"{x:.4f}" for x in r8s))
log(f"r(8) selection spread: {max(r8s) - min(r8s):.4f} "
    f"(max-ent value {res_me['r'][NMAX]:.4f})")

# ---------------- baselines -------------------------------------------------
log("=== BASELINE: uniform labeled growth (counting) ===")
lawU = {}
for p in parents:
    K = sum(mu for _, (mu, g) in children[p].items())
    for ck, (mu, g) in children[p].items():
        lawU[(p, ck)] = math.sqrt(1.0 / K)   # |b|^2 = 1/K per labeled child
res_u = observables(lawU, "uniform growth")

log("=== BASELINE: 2D causal diamond sprinkling (MC, n=8) ===")
NS = 200000
vals = {n: [] for n in range(2, NMAX + 1)}
for _ in range(NS):
    # uniform in diamond via lightcone coords u,v ~ U(0,1)
    u = rng.uniform(0, 1, NMAX); v = rng.uniform(0, 1, NMAX)
    for n in range(2, NMAX + 1):
        rel = 0
        for i in range(n):
            for j in range(n):
                if u[i] < u[j] and v[i] < v[j]: rel += 1
        vals[n].append(rel / (n * (n - 1) / 2))
log("sprinkling r(n): " + "  ".join(
    f"n={n}: {np.mean(vals[n]):.4f}" for n in range(2, NMAX + 1)))

log("=== VERDICT TABLE (n=8) ===")
r_pi4 = res_me["r"][NMAX]
r_uni = res_u["r"][NMAX]
r_spr = float(np.mean(vals[NMAX]))
log(f"  pi/4 (max-ent):    r(8) = {r_pi4:.4f}  "
    f"[random-selection band {min(r8s):.4f}..{max(r8s):.4f}]")
log(f"  uniform growth:    r(8) = {r_uni:.4f}")
log(f"  2D sprinkling:     r(8) = {r_spr:.4f}")
log(f"  wave family:       r(8) in [0.105, 0.804] (logged; nothing-selects)")
log(f"  |pi/4 - sprinkling| = {abs(r_pi4 - r_spr):.4f}   "
    f"|pi/4 - uniform| = {abs(r_pi4 - r_uni):.4f}")
log("DONE")
