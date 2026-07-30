#!/usr/bin/env python3
"""Price the resonant (era-exit) determinism for the first survivor branches.

Seam resolution (analytic): in-era the gregarious weight is s_0 = 1, so
p_greg = 1/(1+s_j) > 0 always; singleton support (the Lean kill lemmas)
forces support = {gregarious}.  A probability-1 timid step is definitionally
a VR era end.  So resonant wrong-way determinism at interior nodes = era
exits, priced by the sieve.  This script computes the sieve mechanically
one era deeper: for each surviving era-2 exit height m in {3,4,7,10}
(phase pinned to 2*pi*k/b, b = 3,3,3,9), enumerate era-3 exits at relative
heights j = 1..6: alive iff b | G_j(C)  AND  b | h(C') for the forced
era-4 first birth.  Reports the survivor geometry classes found.

Also: the neutral-extension census as an integer sequence for OEIS:
c(n) = sum over unlabeled n-causets of the number of distinct unlabeled
action-neutral children.
"""
import itertools

W = {0: 1, 1: -9, 2: 16, 3: -8}
def action_units(rel, n):
    relset = set(rel)
    tot = n
    for (a, b) in rel:
        k = sum(1 for z in range(n) if (a, z) in relset and (z, b) in relset)
        tot -= W.get(k, 0)
    return tot

def close(rel):
    rel = set(rel); changed = True
    while changed:
        changed = False
        for (a, b) in list(rel):
            for (c, d) in list(rel):
                if b == c and (a, d) not in rel:
                    rel.add((a, d)); changed = True
    return rel

def topped_broom(m):
    n = m + 2
    rel = {(0, i + 1) for i in range(m)}
    rel |= {(i, m + 1) for i in range(m + 1)}
    return close(rel), n

def add_above_all(rel, n):
    """add element n above everything (past = all)."""
    return close(set(rel) | {(i, n) for i in range(n)}), n + 1

def add_sibling_above(rel, n, seed_size):
    """add element n with past exactly the seed 0..seed_size-1."""
    return close(set(rel) | {(i, n) for i in range(seed_size)}), n + 1

print("=" * 72)
print("Era-3 exit menu for the first survivor branches")
print("(seed = topped broom-m; alive iff b | G_j and b | h'):")
for m, b in [(3, 3), (4, 3), (7, 3), (10, 9)]:
    rel, n = topped_broom(m)
    seed_size = n
    S_seed = action_units(tuple(rel), n)
    found = []
    for j in range(1, 7):
        relj, nj = rel, n
        for _ in range(j):
            relj, nj = add_sibling_above(relj, nj, seed_size)
        Sj = action_units(tuple(relj), nj)
        relc, nc = add_above_all(relj, nj)          # the timid cap: era-3 exit
        G = action_units(tuple(relc), nc) - Sj
        relh, nh = add_above_all(relc, nc)          # forced era-4 first birth
        h2 = action_units(tuple(relh), nh) - action_units(tuple(relc), nc)
        alive = (G % b == 0) and (h2 % b == 0)
        found.append((j, G, h2, alive))
    alive_js = [j for j, G, h2, a in found if a]
    print(f"  m={m:2d} (b={b}): " + "  ".join(
        f"j={j}: G={G:5d}, h'={h2:5d}, {'ALIVE' if a else 'dead'}"
        for j, G, h2, a in found))
    print(f"          era-3 exits alive at j in {alive_js} "
          + ("(era 3 can ONLY be the eternal broom)" if not alive_js else
         "(rapid-exit tails possible at these heights -- geometry note)"))

print("=" * 72)
print("Neutral-extension census c(n) = sum over unlabeled n-causets of")
print("distinct unlabeled action-neutral children (OEIS candidate):")
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

levels = {1: {canon(1, ()): (1, ())}}
for n in range(1, 6):
    nxt = {}
    for key, (mm, rel) in levels[n].items():
        for D in downsets(mm, rel):
            newrel = tuple(sorted(set(rel) | {(d, mm) for d in D}))
            nxt[canon(mm + 1, newrel)] = (mm + 1, newrel)
    levels[n + 1] = nxt

seq = []
for N in range(1, 7):
    tot = 0
    for key, (mm, rel) in levels[N].items():
        S0 = action_units(rel, mm)
        kids = set()
        for D in downsets(mm, rel):
            newrel = tuple(sorted(set(rel) | {(d, mm) for d in D}))
            if action_units(newrel, mm + 1) == S0:
                kids.add(canon(mm + 1, newrel))
        tot += len(kids)
    seq.append(tot)
print("  c(1..6) =", seq)
