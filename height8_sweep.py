#!/usr/bin/env python3
"""Direct residue sweep for minimal height-8 tower at eps=1/4, phi=8pi
(replaces height_tower.py's DFS for h >= 8, which was too slow).
Fans at depths 2,3,4 (deeper fans enter jumps only at layers <= 1).
Result: minimal (w2,w3,w4) = (63,47,59), n = 177, jumps integral.
h = 9 needs fans up to depth 7 with the z9 condition at denominator
1024; new knobs enter only at shallow layers, so the deep congruences
fall entirely on the already-pinned old knobs - lifting is NOT
automatic and h >= 9 is open in both directions."""
import math
from fractions import Fraction
C2 = [1, -2, 1]
def W_exact(k, eps):
    x = eps / (1 - eps)
    tot = sum(Fraction(C2[i-1]) * math.comb(k, i-1) * x**(i-1)
              for i in range(1, 4))
    return 2 * eps * (1 - eps)**k * tot
eps, q = Fraction(1, 4), 4
c = {k: (-W_exact(k, eps) * 2 * q) for k in range(0, 24)}
def jump_ok(h, w):
    for j in range(1, h + 1):
        tot = Fraction(0)
        for i in range(2, h):
            if i <= j: tot += w.get(i, 0) * c[j - i]
        for i in range(1, j):
            tot += c[j - i - 1]
        if tot % 1 != 0: return False
    return True
best = None
for a in range(0, 256):
    for b in range(0, 128):
        for cc in range(0, 64):
            w = {2: a, 3: b, 4: cc}
            if jump_ok(8, w):
                tot = a + b + cc
                if best is None or tot < best[0]:
                    best = (tot, dict(w))
print("h=8 minimal:", best, "n =", 8 + best[0])
print("verify:", jump_ok(8, best[1]))
print("DONE")
