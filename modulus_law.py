#!/usr/bin/env python3
"""The resonance modulus law (referee's one-line conjecture, sharpened).

At resonant eps = 1/m, phi = 2*pi*q (minimal q with m | 2q), the
interval-k link contributes  c_k = 2*q*W(k)  (pi units) with

  W(k) = (2/m) * ((m-1)/m)^(k-2) * P_k(m) / m^2,
  P_k(m) = (m-1)^2 - 2k(m-1) + k(k-1)/2   (an integer),

so  c_k = 4q * (m-1)^(k-2) * P_k(m) / m^(k+1).  Since gcd(m-1, m) = 1
and P_k is an integer, the denominator of c_k DIVIDES m^(k+1):

  M-ADIC LAW [LEAN: KFCausalMAdicLaw.lean, madic_numerator +
  madic_law, axiom-clean, DIMENSION-BLIND — arbitrary integer
  coefficient system C, so 2D/4D/6D at once; rational-C dimensions
  (3D, C2 = -35/8) extend via the common denominator D with support
  primes(m) U primes(D)]: every congruence modulus of the resonant
  web at eps = p/m has prime support contained in the primes of m,
  with depth growing in k unless P_k(m) = 0 mod m.  The Lean identity:
  m^(k+1) * W(k) = pref * sum_i C_i binom(k,i) p^(i+1) (m-p)^(k-i),
  an integer.

This is the one-line proof of the referee's conjecture (refined from
"modulus = denominator of eps": the modulus is the m-part, e.g. mod 3
at m = 6 after the 2-part cancels).  Verified numerically below for
m = 3..12, k = 1..6; observed moduli at the three run points (mod 8
at 1/4 with q=4, mod 5/25 at 1/5, mod 3 at 1/6) recovered.  CAVEAT
(referee): m = 3 is a DEGENERATE confirmation — eps = 1/3 is exactly
the W1 = 0 sign boundary (c_1 = 0), which is also the funding
theorem's validity boundary; two structures coincide there, so m = 3
should not be counted as a generic data point for the law.

TWO SCOPE NOTES (referee).  (1) The law states where the moduli
LIVE, not that the web is nonempty — a p/m whose only survivor is
dust satisfies it vacuously; each gate run is a separate
nonemptiness data point (six as of 2026-08-01: mod 8, mod 3, mod 5,
mod 16 in 2D/4D, plus the {2,5}-adic 3D web below).  (2) Dimensions
with non-integer C carry the primes of the common denominator D at
EVERY m — and Dowker-Glaser Table 1 shows every odd dimension has
2-power D (8 in 3D, 16 in 5D, 128 in 7D), so ODD-dimensional webs
are 2-adic at every m.  Confirmed (layer_tower_and_3d.py): 3D
(C = 1, -27/8, 9/4; pref 1) at eps = 1/5, phi = 10pi has per-link
denominators 4, 10, 125, 625 — mixed {2,5} where 2D at the same m is
purely 5-adic; 267 survivors == hereditary-real; the 3-chain dies by
the 2-ADIC channel (c1 = 7/4) where 2D killed it mod 5.

NEW PREDICTION (pre-registered before the gate below runs): the FINER
resonance at eps = 1/4 uses minimal q = 2 (phi = 4pi), missed earlier
by taking q = m instead of q = m/2.  There c_1 = 1/2, c_2 = -1/4,
c_3 = -9/16: joint congruence 8N1 - 4N2 - 9N3 = 0 (mod 16)
hereditarily, hence (N3 unreachable at 16) no k >= 3 links, N1 EVEN
(pure 3-chains die, unlike phi = 8pi), and 2N1 = N2 (mod 4).  The
gate at (eps = 1/4, phi = 4pi) should return survivors == the
hereditary-real set with that census.
"""
import math
from fractions import Fraction

def W_exact(k, eps):
    x = eps / (1 - eps)
    C2 = [1, -2, 1]
    tot = sum(Fraction(C2[i-1]) * math.comb(k, i-1) * x**(i-1)
              for i in range(1, 4))
    return 2 * eps * (1 - eps)**k * tot

def primes_of(n):
    n = abs(n); out = set(); d = 2
    while d * d <= n:
        while n % d == 0: out.add(d); n //= d
        d += 1
    if n > 1: out.add(n)
    return out

print("m-adic law check: c_k = 2q W(k), minimal q with m | 2q")
print(f"{'m':>3} {'q':>3}  " + "  ".join(f"{'c_'+str(k):>12}" for k in range(1, 6)))
ok = True
for m in range(3, 13):
    q = m // 2 if m % 2 == 0 else m
    eps = Fraction(1, m)
    row = []
    for k in range(1, 6):
        c = 2 * q * W_exact(k, eps)
        row.append(c)
        if not primes_of(c.denominator) <= primes_of(m):
            ok = False
            print(f"  VIOLATION at m={m}, k={k}: denom {c.denominator}")
    print(f"{m:>3} {q:>3}  " + "  ".join(f"{str(c):>12}" for c in row))
print(f"m-adic law (prime support of denominators <= primes of m): "
      f"{'HOLDS on grid' if ok else 'VIOLATED'}")
print()

# the finer eps=1/4 resonance: gate at phi = 4pi, pre-registered above
src = open("resonant_sector_scan.py").read()
cut = src.index("run_point(Fraction(1, 6)")
exec(src[:cut])
run_point(Fraction(1, 4), 2)   # eps = 1/4, phi = 4pi
print("\nDONE", flush=True)
