#!/usr/bin/env python3
"""Height towers at eps = 1/4, phi = 8pi: the cap is not 5 — it moves
to infinity at exponential width cost.

Referee's height-6 block (single-fan family: w bottoms + 4-chain +
apex needs w = 56 mod 64 while its apex-free downset needs w = 4 mod
8 — incompatible) is CORRECT for one fan.  But each fan attachment
depth is an independent 2-adic knob: chain z_1 < ... < z_h with w_i
extra bottoms attached below z_i (i = 2..h-1, incomparable to z_1 and
to each other).  Per-element criterion: jump(z_j) = sum_i w_i c_{j-i}
+ sum_{i<j} c_{j-i-1} must be integral for each j (fan-at-i elements
sit at interval j-i from z_j; chain element z_i at j-i-1).  One new
congruence per level, one new knob per level: the triangular 2-adic
system lifts, and height h costs width ~ the tower modulus 2^(2h-6).

This script: (1) verifies the hand solution h=6, (w2, w3) = (15, 1),
n = 22, with the full independent hereditary_real check on the
constructed causet; (2) finds minimal-width solutions for h = 6..9 by
progressive congruence search; (3) machine-verifies constructed
causets for h = 6, 7 (larger h verified analytically via the jump
formula — the same formula the machine check validates at h <= 7).

Physical reading (this resonance): time is not arrested — it is
exponentially expensive.  Each unit of temporal depth beyond 5
requires exponentially many spatial elements.
"""
import math
from fractions import Fraction

C2 = [1, -2, 1]
def W_exact(k, eps):
    x = eps / (1 - eps)
    tot = sum(Fraction(C2[i-1]) * math.comb(k, i-1) * x**(i-1)
              for i in range(1, 4))
    return 2 * eps * (1 - eps)**k * tot

eps, q = Fraction(1, 4), 4
KMAX = 24
c = {k: (-W_exact(k, eps) * 2 * q) for k in range(0, KMAX)}   # signed, pi units

def jump_ok(h, w):
    """w = dict i -> width (i = 2..h-1).  Check jump(z_j) integral for all j."""
    for j in range(1, h + 1):
        tot = Fraction(0)
        for i in range(2, h):                     # fans
            if i <= j: tot += w.get(i, 0) * c[j - i]
        for i in range(1, j):                     # chain
            tot += c[j - i - 1]
        if tot % 1 != 0: return False, j
    return True, None

# ---- (1) verify the hand solution -----------------------------------------
ok, bad = jump_ok(6, {2: 15, 3: 1})
print(f"hand solution h=6 (w2,w3)=(15,1): jumps integral = {ok}")

def build_causet(h, w):
    """Elements: chain z_1..z_h = 0..h-1; fans appended after."""
    rel = set()
    for i in range(h):
        for j in range(i + 1, h): rel.add((i, j))
    idx = h
    for i, wi in w.items():
        for _ in range(wi):
            for j in range(i - 1, h): rel.add((idx, j))   # below z_i..z_h
            idx += 1
    return tuple(sorted(rel)), idx

def hereditary_real_raw(rel, m):
    relset = set(rel)
    for z in range(m):
        tot = Fraction(0)
        for (a, b) in rel:
            if b != z: continue
            k = sum(1 for x in range(m)
                    if (a, x) in relset and (x, z) in relset)
            tot += c[k]
        if tot % 1 != 0: return False
    return True

def height_raw(rel, m):
    succ = {v: [b for (a, b) in rel if a == v] for v in range(m)}
    memo = {}
    def hh(v):
        if v not in memo:
            memo[v] = 1 + max((hh(x) for x in succ[v]), default=0)
        return memo[v]
    return max((hh(v) for v in range(m)), default=1)

rel22, n22 = build_causet(6, {2: 15, 3: 1})
print(f"constructed causet: n = {n22}, height = {height_raw(rel22, n22)}, "
      f"hereditary-real (independent per-element check) = "
      f"{hereditary_real_raw(rel22, n22)}", flush=True)

# ---- (2) minimal solutions by progressive search ---------------------------
def find_min(h, cap):
    """DFS over w_2..w_{h-1} in [0, cap], minimizing total width; prune by
    checking condition j as soon as all fans i <= j-2 are fixed."""
    best = [None]
    ws = {}
    def cond_j_ok(j):
        tot = Fraction(0)
        for i in range(2, h):
            if i <= j:
                if i in ws: tot += ws[i] * c[j - i]
                elif j - i >= 2: return True    # not yet determined
        for i in range(1, j):
            tot += c[j - i - 1]
        return tot % 1 == 0
    order = list(range(2, h))
    def dfs(pos, total):
        if best[0] is not None and total >= best[0][0]: return
        if pos == len(order):
            ok, _ = jump_ok(h, ws)
            if ok: best[0] = (total, dict(ws))
            return
        i = order[pos]
        for v in range(0, cap + 1):
            ws[i] = v
            # prune: conditions j with all relevant fans fixed: j <= i + 2
            good = all(cond_j_ok(j) for j in range(4, min(i + 2, h) + 1))
            if good: dfs(pos + 1, total + v)
        del ws[i]
    dfs(0, 0)
    return best[0]

for h, cap in ((6, 80), (7, 300), (8, 1100), (9, 4200)):
    r = find_min(h, cap)
    if r is None:
        print(f"h = {h}: NO solution with widths <= {cap}")
    else:
        total, w = r
        n = h + total
        ok, _ = jump_ok(h, w)
        print(f"h = {h}: minimal fan widths {w}, total width {total}, "
              f"n = {n}, jumps integral = {ok}", flush=True)
        if n <= 400:
            rel, m = build_causet(h, w)
            print(f"        machine check: height = {height_raw(rel, m)}, "
                  f"hereditary-real = {hereditary_real_raw(rel, m)}",
                  flush=True)
print("DONE", flush=True)
