#!/usr/bin/env python3
"""The 2D collision table: is the no-go dimension-universal?

2D BD action (layer kernel (1,-2,1), prefactor 2):
    S/sigma_2 = N - 2 N_link + 4 N_(1 between) - 2 N_(2 between),
i.e. subtracted weights W2 = {0: 2, 1: -4, 2: 2, >=3: 0}  (4D was
{0: 1, 1: -9, 2: 16, 3: -8}).  Both weight sets sum to zero.

Computed here, mirroring the 4D pipeline:
  1. sanity + gap locality (gap depends only on the precursor poset);
  2. the minimal-cover gap (4D: 0 -- the neutral-extension theorem;
     2D: ?) and the zero-gap-child census (4D: every causet has one);
  3. the collision table by absolute RS signature (|P|, #maximal) for
     precursor posets |P| <= 5, with per-signature gap differences and
     their gcds (the reconciling moduli -- the 2D analog of the 9);
  4. root-node structure (4D: forced deterministic; 2D: ?);
  5. era arithmetic first pass: g_m (top over broom-m), h_m (gregarious
     over topped broom-m), and gcd(|g_m|, |h_m|) -- the exit sieve.
"""
import itertools, math

W2 = {0: 2, 1: -4, 2: 2}
W4 = {0: 1, 1: -9, 2: 16, 3: -8}

def action(rel, n, W):
    relset = set(rel)
    tot = n
    for (a, b) in rel:
        k = sum(1 for z in range(n) if (a, z) in relset and (z, b) in relset)
        tot -= W.get(k, 0)
    return tot

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
        D = frozenset(i for i in range(n) if mask >> i & 1)
        if all(below[x] <= D for x in D): out.append(D)
    return out

def maximals(rel, S):
    return [d for d in S if not any((d, e) in rel for e in S)]

levels = {1: {canon(1, ()): (1, ())}}
for n in range(1, 6):
    nxt = {}
    for key, (m, rel) in levels[n].items():
        for D in downsets(m, rel):
            nr = tuple(sorted(set(rel) | {(d, m) for d in D}))
            nxt[canon(m + 1, nr)] = (m + 1, nr)
    levels[n + 1] = nxt

print("=" * 72)
print("1. Sanity (2D units):")
for name, (n, rel) in [("1-element", (1, ())), ("2-chain", (2, ((0, 1),))),
                       ("2-antichain", (2, ())),
                       ("3-chain", (3, ((0, 1), (0, 2), (1, 2))))]:
    print(f"   S({name}) = {action(rel, n, W2)}")
print(f"   minimal-cover gap in 2D: 1 - W2(0) = {1 - W2[0]}"
      "   (4D was 0: the neutral-extension theorem is 4D-SPECIFIC)")

# gap locality check + precursor gap table
gap2, gap4, sig_of = {}, {}, {}
ok = True
for n in range(1, 6):
    for key, (m, rel) in levels[n].items():
        S2h, S4h = action(rel, m, W2), action(rel, m, W4)
        for D in downsets(m, rel):
            if not D: continue
            idx = {d: i for i, d in enumerate(sorted(D))}
            Dp = canon(len(D), tuple(sorted((idx[a], idx[b]) for (a, b) in rel
                                            if a in D and b in D)))
            nr = tuple(sorted(set(rel) | {(d, m) for d in D}))
            g2 = action(nr, m + 1, W2) - S2h
            g4 = action(nr, m + 1, W4) - S4h
            if Dp in gap2 and (gap2[Dp] != g2 or gap4[Dp] != g4): ok = False
            gap2[Dp], gap4[Dp] = g2, g4
            sig_of[Dp] = (len(D), len(maximals(rel, D)))
print(f"   gap locality (2D and 4D): {ok}")

print("=" * 72)
print("2. Zero-gap-child census in 2D (4D: every causet has one):")
seq = []
for N in range(1, 6):
    tot0 = 0; lack = 0
    for key, (m, rel) in levels[N].items():
        S0 = action(rel, m, W2)
        kids = set()
        for D in downsets(m, rel):
            nr = tuple(sorted(set(rel) | {(d, m) for d in D}))
            if action(nr, m + 1, W2) == S0:
                kids.add(canon(m + 1, nr))
        tot0 += len(kids)
        if not kids: lack += 1
    seq.append(tot0)
    print(f"   n={N}: causets {len(levels[N]):3d}, WITHOUT any zero-gap "
          f"child: {lack:3d}, census c2 contribution: {tot0}")
print(f"   c2(1..5) = {seq}   (4D was 1, 2, 6, 22, 105)")

print("=" * 72)
print("3. The 2D collision table (absolute signature (|P|, m), |P| <= 5):")
by_sig = {}
for Dp, g in gap2.items():
    by_sig.setdefault(sig_of[Dp], set()).add(g)
first_collision = None
for s in sorted(by_sig):
    gaps = sorted(by_sig[s])
    diffs = [b - a for a, b in itertools.combinations(gaps, 2)]
    gg = math.gcd(*diffs) if len(diffs) > 1 else (diffs[0] if diffs else 0)
    tag = "coherent" if len(gaps) == 1 else f"COLLISION, diff-gcd {gg}"
    print(f"   sig {s}: gaps {gaps}  [{tag}]")
    if len(gaps) > 1 and first_collision is None:
        first_collision = (s, gaps)
print(f"   first collision at signature {first_collision[0]}: "
      f"gaps {first_collision[1]}")
print("   => the 2D action is NOT a function of the RS signature either.")
# reconciling moduli: a phase reconciles a pair iff (g1-g2) phi = 0 mod 2pi
alld = sorted({b - a for s in by_sig
               for a, b in itertools.combinations(sorted(by_sig[s]), 2)})
g_all = math.gcd(*alld) if len(alld) > 1 else alld[0]
print(f"   all per-signature gap differences: {alld}")
print(f"   gcd of all differences = {g_all}  (the 2D reconciling modulus;"
      " 1 => no phase reconciles everything)")

print("=" * 72)
print("4. Root node in 2D: gaps (cover, disjoint) = "
      f"({1 - W2[0]}, {1 - 0}):")
print("   two-support quadrature needs cos((g1-g2) phi) = 0: |Delta| = 2:")
print("   phi = pi/4 + j pi/2; at phi = pi/4: cos(-pi/4), cos(pi/4) > 0,")
print("   p = (1/2, 1/2): THE 2D ROOT BRANCHES (4D root was forced")
print("   deterministic).  The dimensional structure is inverted.")

print("=" * 72)
print("5. 2D era arithmetic (exit sieve first pass):")
def broom(m):
    return m + 1, tuple(sorted((0, i + 1) for i in range(m)))
def top(rel, n):
    return tuple(sorted(set(rel) | {(i, n) for i in range(n)})), n + 1
for m in range(1, 9):
    nb, rb = broom(m)
    rt, nt = top(rb, nb)
    g = action(rt, nt, W2) - action(rb, nb, W2)
    rh, nh = top(rt, nt)
    h = action(rh, nh, W2) - action(rt, nt, W2)
    b = math.gcd(abs(g), abs(h))
    print(f"   m={m}: g_m = {g:4d}, h_m = {h:4d}, gcd = {b}"
          + ("  ALIVE" if b > 1 else "  dead"))
