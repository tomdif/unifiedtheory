#!/usr/bin/env python3
"""Neutral-extension cross-check at n = 5 and 6, plus the converse question.

The theorem (Lean: actionUnits_coverExtension) says minimal covers always
have gap 0.  Here we cross-check the formalization against enumeration at
n <= 6, and ask the converse: which zero-gap children are NOT minimal
covers?  (Data for the paper: is the action-neutral child unique?)
"""
import itertools

W = {0: 1, 1: -9, 2: 16, 3: -8}
def action_units(n, rel):
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
        D = {i for i in range(n) if mask >> i & 1}
        if all(below[x] <= D for x in D): out.append(frozenset(D))
    return out

def minimals(n, rel):
    return [x for x in range(n) if not any(b == x for (a, b) in rel)]

levels = {1: {canon(1, ()): (1, ())}}
for n in range(1, 6):
    nxt = {}
    for key, (m, rel) in levels[n].items():
        for D in downsets(m, rel):
            newrel = tuple(sorted(set(rel) | {(d, m) for d in D}))
            nxt[canon(m + 1, newrel)] = (m + 1, newrel)
    levels[n + 1] = nxt
print("causets per level:", {n: len(v) for n, v in levels.items()})

for N in range(1, 7):
    total = has0 = 0
    nz_nonmin = 0       # zero-gap downsets that are not single-minimal
    nonmin_examples = []
    for key, (m, rel) in levels[N].items():
        total += 1
        S0 = action_units(m, rel)
        mins = set(minimals(m, rel))
        found0 = False
        for D in downsets(m, rel):
            newrel = tuple(sorted(set(rel) | {(d, m) for d in D}))
            g = action_units(m + 1, newrel) - S0
            if g == 0:
                found0 = True
                if not (len(D) == 1 and next(iter(D)) in mins):
                    nz_nonmin += 1
                    if len(nonmin_examples) < 3:
                        nonmin_examples.append((key[1], tuple(sorted(D))))
        has0 += found0
    print(f"n={N}: causets {total:4d}, with zero-gap child {has0:4d} "
          f"(theorem: all), non-minimal-cover zero-gap births: {nz_nonmin}"
          + (f"  e.g. {nonmin_examples}" if nonmin_examples else ""))
