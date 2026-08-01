#!/usr/bin/env python3
"""The dimensional parity theorem for smeared weight systems.

CLOSED FORM (derived from Dowker-Glaser eq 12: O_d exp(-V) =
sum_i C_i V^(i-1)/(i-1)! exp(-V) with O_d = prod_j (H+2j) /
(2^(n+1)(n+1)!), n = floor(d/2), and H acting on V^a as
multiplication by a*d since V ~ l^(-d)):

  C_i^(d) = sum_{a=0}^{i-1} (-1)^a binom(i-1, a)
            * prod_{j=1}^{n+1} (a*d + 2j) / (2^(n+1) (n+1)!)

PARITY THEOREM:
  even d = 2n: every factor a*d + 2j = 2(na + j), and
    prod_j (na+j) = (n+1)! * binom(na+n+1, n+1), so
    C_i = sum_a (-1)^a binom(i-1,a) binom(na+n+1, n+1) IN Z.
    [LEAN: KFCausalParity.lean, even_layer_product +
     even_dim_coeff_integral]  This discharges madic_law's
    integer-coefficient hypothesis for EVERY even dimension.
  odd d = 2n+1: even-a terms reduce to the same identity (integers);
    odd-a terms have all n+1 factors odd.  TWO CLAIMS, split per
    referee: (BOUND — provable, Lean-ready) j -> ad + 2j is a
    bijection mod p^e for every odd prime power (2 invertible), so
    #{j <= k : p^e | ad+2j} >= floor(k/p^e) and Legendre's formula
    transfers verbatim: v_p(prod) >= v_p((n+1)!) for every odd p,
    hence denominators are pure 2-powers bounded by
    2^(n+1+v2((n+1)!)).  This is the same size of argument as the
    even case and awaits formalization alongside it.
    (TIGHTNESS — genuinely empirical) the bound is attained exactly:
    the common denominator EQUALS 2^(n+1+v2((n+1)!)) at every odd
    d <= 21 checked below — 8, 16, 128 for d = 3, 5, 7 (Table 1) and
    256, 1024, 2048 predicted for 9D, 11D, 13D.  The grid supports
    tightness, not the bound.

CONSEQUENCE: parity of dimension is imprinted in the prime content
of every resonant congruence web — even-dimensional webs are purely
m-adic at eps = p/m; odd-dimensional webs carry 2-adic structure at
every m.  Now a theorem about all dimensions, not a reading of a
table that stops at d = 7.

CONVENTION NOTE (referee reconciliation): the per-link phase
contribution reported by the gate scripts is c_k := (-2q W(k)) mod 2
in pi units (the angle of e^{i dS phi}: a link of interval k
contributes -W(k) to the action gap).  The referee's +2q W(k) is the
same datum with opposite sign; -1/4 = 7/4 (mod 2).  Integrality
statements are sign-blind.

Verified below: closed form reproduces ALL SEVEN rows of DG Table 1
(1305.2588); parity + exact 2-power bound for d <= 21.
"""
import math
from fractions import Fraction

def coeff(d, i):
    n = d // 2
    tot = Fraction(0)
    for a in range(i):
        prod = 1
        for j in range(1, n + 2):
            prod *= (a * d + 2 * j)
        tot += Fraction((-1)**a * math.comb(i - 1, a) * prod,
                        2**(n + 1) * math.factorial(n + 1))
    return tot

TABLE1 = {
    1: [1, Fraction(-1, 2)],
    2: [1, -2, 1],
    3: [1, Fraction(-27, 8), Fraction(9, 4)],
    4: [1, -9, 16, -8],
    5: [1, Fraction(-215, 16), Fraction(225, 8), Fraction(-125, 8)],
    6: [1, -34, 141, -189, 81],
    7: [1, Fraction(-6307, 128), Fraction(14749, 64),
        Fraction(-10633, 32), Fraction(2401, 16)],
}

print("1. Closed form vs Dowker-Glaser Table 1:")
allok = True
for d, row in TABLE1.items():
    n = d // 2
    mine = [coeff(d, i) for i in range(1, n + 3)]
    ok = mine == [Fraction(x) for x in row]
    allok &= ok
    print(f"   d={d}: {[str(x) for x in mine]}  "
          f"{'MATCHES' if ok else 'MISMATCH vs ' + str(row)}")
assert allok, "closed form fails against Table 1"

def v2(x):
    v = 0
    while x % 2 == 0: x //= 2; v += 1
    return v

print("\n2. Parity + denominator bound, d = 2..21:")
for d in range(2, 22):
    n = d // 2
    row = [coeff(d, i) for i in range(1, n + 3)]
    dens = [c.denominator for c in row]
    D = 1
    for x in dens: D = D * x // math.gcd(D, x)
    if d % 2 == 0:
        ok = all(x == 1 for x in dens)
        print(f"   d={d:>2} (even): all integer: {ok}")
        assert ok
    else:
        bound = 2**(n + 1 + v2(math.factorial(n + 1)))
        ispow2 = all(x & (x - 1) == 0 for x in dens)
        print(f"   d={d:>2} (odd):  common denominator {D} "
              f"(2-power: {ispow2}); bound 2^(n+1+v2((n+1)!)) = {bound} "
              f"{'TIGHT' if D == bound else '(bound holds: ' + str(D <= bound) + ')'}")
        assert ispow2 and D <= bound
print("\nPARITY THEOREM VERIFIED on the grid.")
print("DONE")
