#!/usr/bin/env python3
"""Fan-tower fate at eps = 1/4, phi = 8pi by 2-adic elimination — the
referee's reframing: no scan, just compatibility of the tower moduli.

Fan family: chain z_1 < ... < z_h, w_i extra bottoms below z_i
(i = 2..h-1).  Per-element integrality of jump(z_j) for j = 4..h gives
one congruence per level:

  sum_{i=2}^{j-2} w_i c_{j-i} + chain_j  in  Z,
  chain_j = sum_{i=1}^{j-1} c_{j-i-1},

with c_k of 2-adic denominator 2^(2k-2).  Multiply condition j by
L_j = 2^(2(j-2)-2) -> integer congruence mod L_j; lift all to the top
modulus and solve the linear system over Z/2^K by 2-adic Gaussian
elimination (pivot on odd entries).  Output per height: solvable or
not; if solvable, the pinned residues and a minimal nonneg solution +
total width (the n(h) scaling data); if not, the height at which the
fan family terminates.  h = 6, 7, 8 must reproduce (15,1), (31,15),
(63,47,59).
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
c = {k: (-W_exact(k, eps) * 2 * q) for k in range(0, 40)}

def solve_height(h, verbose=True):
    vars_ = list(range(2, h - 1))            # w_i, i = 2..h-2 (effective)
    conds = list(range(4, h + 1))            # z_j conditions
    K = max(2 * (j - 2) - 2 for j in conds)
    MOD = 2 ** K
    rows = []
    for j in conds:
        Lj = 2 ** (2 * (j - 2) - 2)
        row = []
        for i in vars_:
            coef = c[j - i] * Lj if i <= j - 2 else Fraction(0)
            assert coef.denominator == 1
            row.append(int(coef) * (MOD // Lj) % MOD)
        chain = sum(c[j - i - 1] for i in range(1, j))
        rhs = (-chain * Lj)
        assert rhs.denominator == 1
        rows.append((row, int(rhs) * (MOD // Lj) % MOD, MOD))
    # row echelon over Z/MOD (2-adic): min-valuation pivots, eliminate
    # DOWNWARD only; then back-substitute in reverse pivot order with
    # exact divisibility checks.
    nv = len(vars_)
    aug = [[r[0][i] for i in range(nv)] + [r[1]] for r in rows]
    def v2(x):
        if x % MOD == 0: return 10**9
        v = 0
        while x % 2 == 0: x //= 2; v += 1
        return v
    pivots = []          # (row, col, val)
    used = set()
    for col in range(nv):
        piv, best = None, None
        for r in range(len(aug)):
            if r in used: continue
            a = aug[r][col] % MOD
            if a == 0: continue
            v = v2(a)
            if best is None or v < best: best, piv = v, r
        if piv is None: continue
        used.add(piv); pivots.append((piv, col, best))
        a = aug[piv][col] % MOD
        aodd = a >> best
        for r in range(len(aug)):
            if r in used: continue
            b = aug[r][col] % MOD
            if b == 0: continue
            assert v2(b) >= best
            f = ((b >> best) * pow(aodd, -1, MOD)) % MOD
            for k2 in range(nv + 1):
                aug[r][k2] = (aug[r][k2] - f * aug[piv][k2]) % MOD
    for r in range(len(aug)):
        if r in used: continue
        if any(aug[r][i] % MOD for i in range(nv)): continue
        if aug[r][nv] % MOD != 0: return None
    sol = {}
    solval = {i: 0 for i in vars_}          # free vars -> 0
    for piv, col, v in reversed(pivots):
        rhs = aug[piv][nv] % MOD
        for c2 in range(nv):
            if c2 == col: continue
            rhs = (rhs - aug[piv][c2] * solval[vars_[c2]]) % MOD
        a = aug[piv][col] % MOD
        if rhs % (1 << v): return None
        aodd = a >> v; m2 = MOD >> v
        w = ((rhs >> v) * pow(aodd, -1, m2)) % m2
        solval[vars_[col]] = w
        sol[vars_[col]] = (w, m2)
    wmin = dict(solval)
    # exact verification
    def jump_ok(h, w):
        for j in range(1, h + 1):
            tot = Fraction(0)
            for i in range(2, h):
                if i <= j: tot += w.get(i, 0) * c[j - i]
            for i in range(1, j):
                tot += c[j - i - 1]
            if tot % 1 != 0: return False
        return True
    ok = jump_ok(h, wmin)
    return wmin, sol, ok, K

print("Fan-tower 2-adic elimination, h = 6..16:")
prev = None
for h in range(6, 17):
    r = solve_height(h)
    if r is None:
        print(f"  h = {h}: INSOLVABLE — the fan family terminates here")
        break
    wmin, sol, ok, K = r
    tot = sum(wmin.values())
    pins = {i: f"{v} mod 2^{m.bit_length()-1}" for i, (v, m) in sol.items()}
    print(f"  h = {h}: solvable (mod 2^{K}); minimal rep {dict(wmin)}, "
          f"total width {tot}, n = {h + tot}, verified = {ok}")
    print(f"        pinned residues: {pins}", flush=True)
print("DONE", flush=True)
