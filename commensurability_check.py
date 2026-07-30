#!/usr/bin/env python3
"""Commensurability check, analytic version.

Per node: consistency  sum_c a_c e^{i g_c phi} = 1, sum a_c^2 = 1, a_c >= 0.
Structure facts used:
 - 1-support solutions: a_i = 1 needs g_i phi = 0 mod 2pi  (g_i = 0: 'lazy').
 - 2-support solutions (our born_quadrature_law): need cos((g_i-g_j)phi) = 0
   AND cos(g_i phi) >= 0, cos(g_j phi) >= 0; then p = cos^2 of each phase.
 - general: minimal-norm point of the affine set {a.c = 1, a.s = 0} has
   norm^2 = (1,0) G^{-1} (1,0)^T with G the Gram of (c, s); sphere reachable
   iff that <= 1 (nonneg needs checking on the sphere slice).
"""
import itertools, numpy as np

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

def children(n, rel):
    kids = {}
    for D in downsets(n, rel):
        newrel = set(rel) | {(d, n) for d in D}
        kids[canon(n + 1, newrel)] = (n + 1, tuple(sorted(newrel)))
    return list(kids.values())

levels = {1: {canon(1, ()): (1, ())}}
for n in range(1, 5):
    nxt = {}
    for key, (m, rel) in levels[n].items():
        for (m2, rel2) in children(m, rel):
            nxt[canon(m2, rel2)] = (m2, rel2)
    levels[n + 1] = nxt
print("causets per level:", {n: len(v) for n, v in levels.items()})

nodes = []
for n in range(1, 5):
    for key, (m, rel) in levels[n].items():
        S0 = action_units(m, rel)
        gaps = sorted(action_units(*c) - S0 for c in children(m, rel))
        nodes.append((n, S0, gaps))
        
print("\nnode gap tables (S/sigma gaps of children):")
lazy_ok = True
for n, S0, gaps in nodes:
    has0 = 0 in gaps
    lazy_ok = lazy_ok and has0
    print(f"  n={n}  S0={S0:4d}  gaps={gaps}  zero-gap child: {has0}")
print(f"\nEVERY node has a zero-gap child: {lazy_ok}")
print("=> the LAZY tower (deterministic zero-gap steps) satisfies consistency for EVERY phi." if lazy_ok else "=> lazy tower fails somewhere")

# non-degenerate: 2-support windows per node, intersected over nodes
print("\n2-support (born-quadrature) solution windows in phi (0, pi]:")
def two_support_windows(gaps, grid):
    ok = np.zeros_like(grid, dtype=bool)
    for i in range(len(gaps)):
        for j in range(i+1, len(gaps)):
            gi, gj = gaps[i], gaps[j]
            if gi == gj: continue
            q = np.abs(np.cos((gi - gj) * grid)) < 1e-3
            pos = (np.cos(gi * grid) >= -1e-9) & (np.cos(gj * grid) >= -1e-9)
            ok |= (q & pos)
    return ok

grid = np.linspace(0.005, np.pi, 20000)
allok = np.ones_like(grid, dtype=bool)
for n, S0, gaps in nodes:
    win = two_support_windows(gaps, grid)
    # 1-support also counts as a consistent (degenerate) node solution
    one = np.zeros_like(grid, dtype=bool)
    for g in gaps:
        if g == 0: one |= np.ones_like(grid, dtype=bool)
        else: one |= (np.abs(np.mod(g * grid, 2*np.pi)) < 1e-3) | (np.abs(np.mod(g * grid, 2*np.pi) - 2*np.pi) < 1e-3)
    allok &= (win | one)
frac = allok.mean()
print(f"phi admitting (1- or 2-support) consistency at ALL nodes: {frac*100:.1f}% of grid")
# NON-degenerate demand: at least one node uses a genuine 2-support with both p in (0,1)
def strict_two_support(gaps, grid):
    ok = np.zeros_like(grid, dtype=bool)
    for i in range(len(gaps)):
        for j in range(i+1, len(gaps)):
            gi, gj = gaps[i], gaps[j]
            if gi == gj: continue
            q = np.abs(np.cos((gi - gj) * grid)) < 1e-3
            pos = (np.cos(gi * grid) > 1e-3) & (np.cos(gj * grid) > 1e-3)
            ok |= (q & pos)
    return ok
root_strict = strict_two_support(nodes[0][2], grid)
print(f"root node admits STRICT (both p>0) 2-support quadrature: {root_strict.mean()*100:.1f}% of grid")
if root_strict.any():
    idx = np.where(root_strict)[0][:5]
    print("  sample phi:", np.round(grid[idx], 4))
