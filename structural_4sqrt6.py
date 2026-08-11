#!/usr/bin/env python3
"""Structural probes of the 4/sqrt6 identity: BD 4D prefactor vs
pure-gravity Liouville coupling.  All arithmetic for
STRUCTURAL_4_SQRT6_NOTE.md, reproducible.

Facts used (literature-verified 2026-08-11):
  KPZ/DDK: gamma(c) = (sqrt(25-c) - sqrt(1-c))/sqrt(6)
  Watabiki: d_H(c) = 2 (sqrt(49-c) + sqrt(25-c)) / (sqrt(25-c) + sqrt(1-c))
  Mating of trees (DMS): walk correlation rho = -cos(pi gamma^2 / 4)
  Dowker-Glaser 3D: beta_3 = (pi/(3 sqrt2))^(2/3) / Gamma(5/3)
  Concordance dictionary: ordering fraction r = 1/2 + arcsin(rho)/pi
    (exchangeable coordinate pairs, Gaussian copula) -> rho_eff =
    sin(pi (r - 1/2)).
"""
import math

S6 = math.sqrt(6)
def gamma_of_c(c):
    return (math.sqrt(25 - c) - math.sqrt(1 - c)) / S6
def c_of_gamma(g):
    # invert gamma(c): sqrt(25-c) - sqrt(1-c) = g sqrt6; s = sqrt(1-c)
    t = g * S6
    s = (24 - t * t) / (2 * t)
    return 1 - s * s
def watabiki_dH(c):
    return 2 * (math.sqrt(49 - c) + math.sqrt(25 - c)) / \
        (math.sqrt(25 - c) + math.sqrt(1 - c))
def rho_of_gamma(g):
    return -math.cos(math.pi * g * g / 4)
def gamma_of_rho(rho):
    return math.sqrt(4 * math.acos(-rho) / math.pi)
def rho_eff_of_r(r):
    return math.sin(math.pi * (r - 0.5))
def r_of_rho(rho):
    return 0.5 + math.asin(rho) / math.pi

print("== point identities ==")
print(f"BD 4D prefactor 4/sqrt6           = {4/S6:.6f}")
print(f"gamma(c=0)                        = {gamma_of_c(0):.6f}")
print(f"sqrt(8/3)                         = {math.sqrt(8/3):.6f}")
print(f"Watabiki d_H(c=0)                 = {watabiki_dH(0):.6f}  (Le Gall theorem: 4)")
print(f"SLE kappa = gamma^2 at c=0        = {gamma_of_c(0)**2:.6f}  (= 8/3, SAW)")
print(f"Starobinsky exponent sqrt(2/3)    = {math.sqrt(2/3):.6f} = (4/sqrt6)/2 = {4/S6/2:.6f}")

print("\n== family-map tests (structure would need these to pass) ==")
beta3 = (math.pi / (3 * math.sqrt(2))) ** (2 / 3) / math.gamma(5 / 3)
print(f"Dowker-Glaser beta_3              = {beta3:.6f}")
print(f"  c with gamma(c) = beta_3        = {c_of_gamma(beta3):.3f}   (nothing distinguished)")
# gamma with Watabiki d_H = 3
lo, hi = 0.01, 1.99
for _ in range(200):
    mid = 0.5 * (lo + hi)
    if watabiki_dH(c_of_gamma(mid)) < 3: lo = mid
    else: hi = mid
g_dh3 = 0.5 * (lo + hi)
print(f"  gamma with Watabiki d_H = 3     = {g_dh3:.6f}  vs beta_3 = {beta3:.6f}  "
      f"(mismatch {abs(g_dh3-beta3)/beta3*100:.1f}%)")
print(f"  sqrt(2d/3) at d=2               = {math.sqrt(4/3):.6f}  vs 2D constants 2 and 4 (fails)")

print("\n== mating-of-trees dictionary (exploratory) ==")
for name, c in (("pure gravity c=0", 0.0), ("spanning trees c=-2", -2.0),
                ("c=1 barrier", 1.0)):
    g = gamma_of_c(c)
    rho = rho_of_gamma(g)
    print(f"{name:22s} gamma = {g:.4f}  rho = {rho:+.4f}  "
          f"target r = {r_of_rho(rho):.4f}")
print()
for name, r in (("pi/4 law r(8)", 0.4136), ("pi/4 law r(7)", 0.3942),
                ("4/sqrt6 4D law r(7)", 0.3905),
                ("uniform growth r(8)", 0.5080),
                ("2D sprinkling", 0.4997)):
    rho = rho_eff_of_r(r)
    try:
        g = gamma_of_rho(rho)
        c = c_of_gamma(g)
        print(f"{name:22s} r = {r:.4f}  rho_eff = {rho:+.4f}  "
              f"gamma_eff = {g:.4f}  c_eff = {c:+.2f}")
    except ValueError:
        print(f"{name:22s} r = {r:.4f}  rho_eff = {rho:+.4f}  (out of range)")
print("\nsharp asymptotic discriminators: r -> 1/2 <=> independent walks")
print("(c = -2 class); r -> 2/3 <=> pure gravity/Brownian map (c = 0).")
print("current pi/4 trend: 0.30 -> 0.41 rising, target undetermined,")
print("pointing at ~1/2 rather than 2/3 at accessible depth.")
