#!/usr/bin/env python3
"""Root-zero propagation through the Rideout-Sorkin t-family.

Gate logic (run BEFORE the labeled-tree walk, per plan):
  Stage 0. Tower forces p(2-antichain) = 0 at the root (phi not in 2*pi*Z).
           In RS form p(2-antichain) = t0/(t0+t1)  =>  t0 = 0.
  Stage 1. t0 = 0 kills the empty-past transition at EVERY stage
           (same t0 in every numerator) => originary causets only.
  Stage 2. Strict RS interior (t1 > 0): the 2-chain node has exactly two
           surviving children, V-up (gap 0, weight t1) and 3-chain
           (gap 9, weight t1+t2), both with p > 0.  Tower consistency
           sqrt(p0) + sqrt(p9) e^{i 9 phi} = 1 has NO solution with both
           p > 0 (im-part forces sin 9phi = 0; then strict concavity /
           sign kills both e^{i9phi} = +1 and -1).  => interior EMPTY.
  Stage 3. VR boundary t0 = t1 = 0, t2 > 0: stage-2 forces p(3-chain) = 1,
           tower needs 9 phi = 0 mod 2pi.  At the 3-chain node the two
           surviving children are cover-{x0,x1} (gap +9, weight t2) and
           4-chain (gap -7, weight 2 t2 + t3), the latter with p >= 2/3 > 0,
           so the tower needs sin 7 phi = 0.  gcd arithmetic: 9 phi in
           2 pi Z and 7 phi in pi Z  =>  phi in 2 pi Z (excluded). => DEAD.
  Deeper boundaries t0 = t1 = t2 = 0 leave stage 2 with ALL weights zero:
  no covariant assignment exists at all.  => intersection EMPTY at n <= 4.

This script verifies every numbered claim mechanically (weights, gaps,
signatures, minimizations) rather than trusting the hand computation.
"""
import itertools, math
import numpy as np

# ---------- causet enumeration (same conventions as commensurability_check) --
def canon(n, rel):
    best = None
    for p in itertools.permutations(range(n)):
        r = tuple(sorted((p[a], p[b]) for (a, b) in rel))
        if best is None or r < best: best = r
    return (n, best)

def downsets(n, rel):
    below = {x: {a for (a, b) in rel if b == x} for x in range(n)}
    out = []
    for mask in range(1 << n):
        D = {i for i in range(n) if mask >> i & 1}
        if all(below[x] <= D for x in D): out.append(frozenset(D))
    return out

W = {0: 1, 1: -9, 2: 16, 3: -8}
def action_units(n, rel):
    relset = set(rel)
    tot = n
    for (a, b) in rel:
        k = sum(1 for z in range(n) if (a, z) in relset and (z, b) in relset)
        tot -= W.get(k, 0)
    return tot

def minimals(n, rel):
    return [x for x in range(n) if not any(b == x for (a, b) in rel)]

def sig(n, rel, D):
    """RS transition signature (varpi, m) of birthing above downset D."""
    relset = set(rel)
    varpi = len(D)
    m = sum(1 for d in D if not any((d, e) in relset for e in D))
    return varpi, m

NT = 6  # t_0 .. t_5
def lam_vec(varpi, m):
    v = np.zeros(NT, dtype=np.int64)
    for k in range(m, varpi + 1):
        v[k] = math.comb(varpi - m, k - m)
    return v

# enumerate unlabeled causets, and per node the children with
# (gap, aggregated weight vector, #minimals of child)
levels = {1: {canon(1, ()): (1, ())}}
for n in range(1, 5):
    nxt = {}
    for key, (m, rel) in levels[n].items():
        for D in downsets(m, rel):
            newrel = tuple(sorted(set(rel) | {(d, m) for d in D}))
            nxt[canon(m + 1, newrel)] = (m + 1, newrel)
    levels[n + 1] = nxt

nodes = []   # (n, S0, n_minimals, [(gap, weightvec, child_minimals, child_key)])
for n in range(1, 5):
    for key, (m, rel) in sorted(levels[n].items()):
        S0 = action_units(m, rel)
        kids = {}
        for D in downsets(m, rel):
            newrel = tuple(sorted(set(rel) | {(d, m) for d in D}))
            ck = canon(m + 1, newrel)
            gap = action_units(m + 1, newrel) - S0
            varpi, mm = sig(m, rel, D)
            if ck not in kids:
                kids[ck] = [gap, np.zeros(NT, dtype=np.int64),
                            len(minimals(m + 1, newrel))]
            kids[ck][1] += lam_vec(varpi, mm)
        nodes.append((n, S0, len(minimals(m, rel)), key,
                      sorted(((g, w, cm) for g, w, cm in kids.values()),
                             key=lambda z: z[0])))

def wstr(w):
    return "+".join(f"{c}t{k}" for k, c in enumerate(w) if c) or "0"

# ---------- CHECK 0: zero-gap child == minimal-cover child (theorem) --------
print("=" * 72)
print("CHECK 0  (minimal-cover theorem): birth above one minimal has gap 0")
ok = True
for n in range(1, 5):
    for key, (m, rel) in levels[n].items():
        S0 = action_units(m, rel)
        for x in minimals(m, rel):
            newrel = tuple(sorted(set(rel) | {(x, m)}))
            g = action_units(m + 1, newrel) - S0
            if g != 0: ok = False
print("  all minimal-cover births have gap 0 at n=1..4:", ok)

# ---------- CHECK 1: t0 = 0 kills exactly the non-originary children --------
print("=" * 72)
print("CHECK 1  (originary propagation): with t0 = 0, killed children")
ok = True
for n, S0, nmin, key, kids in nodes:
    for g, w, cmin in kids:
        killed = (w[1:].sum() == 0)          # weight = c * t0 only
        adds_min = (cmin > nmin) or (n == 1 and cmin == nmin == 1 and False)
        # child adds a new minimal element iff its birth had empty past
        if killed != (cmin == nmin + 1): ok = False
print("  killed == 'child has one more minimal element' at every node:", ok)
print("  => empty-past births vanish at ALL stages; only ORIGINARY causets")
print("     (single minimal element) survive.  Combinatorial Big Bang.")

# ---------- the two decisive nodes, printed explicitly ----------------------
print("=" * 72)
print("Decisive node tables (gap : weight : child minimal-count):")
for n, S0, nmin, key, kids in nodes:
    if n <= 3 and nmin == 1:
        print(f"  n={n} S0={S0:3d} minimals={nmin} rel={key[1]}")
        for g, w, cmin in kids:
            print(f"      gap {g:4d}   weight {wstr(w):18s} child-minimals {cmin}")

# ---------- CHECK 2: strict-RS interior dies at the 2-chain node ------------
print("=" * 72)
print("CHECK 2  (strict RS, t0=0, t1>0): 2-chain node violation floor")
# p_chain = (t1+t2)/(2t1+t2) in [1/2,1), p_V = t1/(2t1+t2); violation
# |sqrt(pV) + sqrt(pch) e^{i 9 phi} - 1| minimized over r=t2/t1>=0, phi
r = np.concatenate([np.linspace(0, 50, 4001), np.geomspace(50, 1e6, 200)])
pch = (1 + r) / (2 + r); pV = 1 / (2 + r)
phi = np.linspace(1e-3, 2 * np.pi - 1e-3, 30000)
E = np.abs(np.sqrt(pV)[:, None]
           + np.sqrt(pch)[:, None] * np.exp(1j * 9 * phi[None, :]) - 1)
i, j = np.unravel_index(np.argmin(E), E.shape)
print(f"  min violation over r in [0,1e6], phi in (0,2pi): {E.min():.4f}")
print(f"    at r = t2/t1 = {r[i]:.3g}, phi = {phi[j]:.4f} "
      f"(drifts to r -> inf, 9phi -> 0 mod 2pi: the VR boundary)")
print(f"  min violation with r <= 10 (genuine interior): "
      f"{E[r <= 10].min():.4f}   [analytic floor sqrt2-1 = {np.sqrt(2)-1:.4f}]")

# ---------- CHECK 3: VR boundary t0=t1=0 dies at the 3-chain node -----------
print("=" * 72)
print("CHECK 3  (VR boundary t0=t1=0, t2>0): stage-2 forces p(3-chain)=1,")
print("         tower needs 9 phi = 0 mod 2pi; 3-chain node then:")
# surviving children of 3-chain: weights t2 (gap 9) and 2t2+t3 (gap -7)
s = np.concatenate([np.linspace(0, 50, 2001), np.geomspace(50, 1e6, 200)])
p9 = 1 / (3 + s); pm7 = (2 + s) / (3 + s)
best = 1e9; arg = None
for k in range(1, 9):                      # phi = 2 pi k / 9, k=1..8
    ph = 2 * np.pi * k / 9
    v = np.abs(np.sqrt(p9) * np.exp(1j * 9 * ph)
               + np.sqrt(pm7) * np.exp(-1j * 7 * ph) - 1)
    if v.min() < best: best, arg = v.min(), (k, s[np.argmin(v)])
print(f"  min violation over s=t3/t2 in [0,1e6], phi in (2pi/9)Z*: "
      f"{best:.4f}  at k={arg[0]}, s={arg[1]:.3g}")
# coprimality: 9 phi in 2piZ and 7 phi in piZ  =>  phi in 2piZ
sols = [k for k in range(1, 9) if abs(math.sin(7 * 2 * np.pi * k / 9)) < 1e-12]
print(f"  k in 1..8 with sin(7 phi)=0 as ALSO required: {sols}  (empty <=> "
      "gcd(9,14)=1 arithmetic)")

# ---------- CHECK 4: deeper boundary t0=t1=t2=0 is not a dynamics -----------
print("=" * 72)
print("CHECK 4  (t0=t1=t2=0): 2-chain node total weight vector:")
for n, S0, nmin, key, kids in nodes:
    if n == 2 and nmin == 1:
        tot = sum((w for _, w, _ in kids), np.zeros(NT, dtype=np.int64))
        print(f"  sum of child weights = {wstr(tot)}  -> all zero once "
              "t0=t1=t2=0: NO covariant assignment exists at stage 2.")

# ---------- CHECK 5: global numeric confirmation over the whole tree --------
print("=" * 72)
print("CHECK 5  (global): min over interior t>0, phi of MAX node violation,")
print("         originary (reachable) nodes n=1..4")
orig = [(n, kids) for n, S0, nmin, key, kids in nodes if nmin == 1]
rng = np.random.default_rng(0)
def objective(z):
    t = np.zeros(NT); t[1:5] = np.exp(np.clip(z[:4], -30, 30)); ph = z[4]
    if not (0.05 < ph % (2 * np.pi) < 2 * np.pi - 0.05): return 1e3
    worst = 0.0
    for n, kids in orig:
        ws = np.array([w @ t for g, w, cm in kids]); Z = ws.sum()
        if Z <= 0: return 1e3
        p = ws / Z
        amp = sum(np.sqrt(pc) * np.exp(1j * g * ph)
                  for (g, w, cm), pc in zip(kids, p))
        worst = max(worst, abs(amp - 1))
    return worst
from scipy.optimize import minimize
best = (1e9, None)
for _ in range(300):
    z0 = np.concatenate([rng.normal(0, 3, 4), [rng.uniform(0.1, 6.2)]])
    res = minimize(objective, z0, method="Nelder-Mead",
                   options={"maxiter": 2000, "fatol": 1e-10, "xatol": 1e-8})
    if res.fun < best[0]: best = (res.fun, res.x)
t = np.exp(best[1][:4])
print(f"  best max-violation found: {best[0]:.4f}")
print(f"    at t1..t4 = {np.array2string(t, precision=3)}, "
      f"phi = {best[1][4] % (2*np.pi):.4f}")
print(f"    t2/t1 = {t[1]/t[0]:.3g} (boundary drift indicator)")
print("=" * 72)
print("NOTE: the above analyzed the naive t0=0 boundary of the RS t-family.")
print("SUPERSEDED by vr_era_gate.py: the correct VR completion is the era/turtle")
print("structure (gr-qc/0504066), under which era-2 couplings are FREE, and the")
print("verdict changes: deterministic single histories survive; see vr_era_gate.py.")
print("Retained here: CHECK 0/1 (minimal-cover, originary forcing) remain valid.")
print("OBSOLETE VERDICT (strict t-family only):")
print("         = EMPTY, killed at n <= 4.  Strict interior dies at the")
print("         2-chain node (floor sqrt(2)-1); the only escape boundary")
print("         t0=t1=0 dies at the 3-chain node by 9/7 gap coprimality;")
print("         deeper boundaries leave stage 2 with no dynamics at all.")
