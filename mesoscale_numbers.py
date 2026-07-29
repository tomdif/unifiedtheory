#!/usr/bin/env python3
"""Mesoscale scaling law + Lambda-refinement numbers.

Assembles the machine-checked Lean constants (variance_rate, mesoscale_suppression,
f4Dsq_w_mass, g4sq_mass_half, dictionary a = pi*rho/24, BDG prefactor 4/sqrt6)
into the physical scaling law and evaluates it.  Every number that comes from a
Lean theorem is tagged [LEAN]; every physics-assembly step is tagged [PHYS].
"""
import numpy as np
from scipy import integrate

sqrt = np.sqrt
pi = np.pi

# ---------- [LEAN] machine-checked masses ----------
M_sharp_half = (315 / 2) * sqrt(pi)          # M[f4Dsq](1/2), f4Dsq_mass_half
w_mass_sharp = (315 / 4) * sqrt(pi)          # int f4Dsq(w^2) dw, f4Dsq_w_mass
C_F = (315 / 512) * sqrt(2) * sqrt(pi)       # M[f4D^2](1/2),  g4sq_mass_half
w_mass_damped_over_eps32 = C_F / 2           # int g4sq(w^2) dw = (1/2) M[g4sq](1/2)
# mesoscale_suppression: M[eps^2 g4sq(eps .)](1/2) = eps^(3/2) * C_F   [LEAN]
# damped mean: zeros at 1/2,1,3/2 carry for all eps; survivor = -1/eps [LEAN]

# numeric cross-check of the two Lean masses
P = lambda z: 1 - 9*z + 8*z**2 - (4/3)*z**3
chk1, _ = integrate.quad(lambda z: z**-0.5 * np.exp(-2*z) * P(z)**2, 0, 60)
chk2, _ = integrate.quad(lambda w: np.exp(-w**2) * (1 + 81*w**2 + 128*w**4 + (32/3)*w**6), 0, 30)
assert abs(chk1 - C_F) < 1e-10 and abs(chk2 - w_mass_sharp) < 1e-8

# ---------- [PHYS] assembly of the physical variance ----------
# B_k phi(x) = (4/sqrt6) l_k^-2 [ -phi(x) + eps sum_y f(n(x,y),eps) phi(y) ],
#   eps = rho_k/rho = (l_p/l_k)^4  (Aslanbeigi-Saravani-Sorkin smeared operator)
# Atomic (Campbell) variance channel:
#   Var = (8/3) l_k^-4 rho int d4y  eps^2 E[f^2](rho V(y)) phi(y)^2
# Cone reduction (exact bookkeeping, same chain as the committed mean proof):
#   d4y = 4pi r^2 dr dt -> null u,v with Jacobian 1/2, r^2 = (v-u)^2/4:
#   c_geom = 4pi * (1/2) * (1/4) = pi/2;   xi = rho V = a u^2 v^2, a = pi rho/24 [LEAN dictionary]
# Continuum damped kernel: eps^2 E[f^2](xi) -> eps^2 g4sq(eps xi)  (leading order)
# variance_rate [LEAN]: sqrt(atilde) * II -> w-mass * E,  atilde = eps a
#   => II = (eps a)^(-1/2) * (C_F/2) * E[phi^2]  * (1+o(1))
# Assemble:
#   Var = (8/3)(pi/2) l_k^-4 rho * eps^2 (eps a)^(-1/2) (C_F/2) E
#       = K * (l_p^4 / l_k^10) * E[phi^2],
#   K = (4pi/3) * sqrt(24/pi) * (C_F/2) = (105 sqrt3 / 64) * pi        [exact]
K = (105 * sqrt(3) / 64) * pi
K_check = (4*pi/3) * sqrt(24/pi) * (C_F/2)
assert abs(K - K_check) < 1e-12
print(f"[EXACT] assembly constant  K = 105*sqrt(3)*pi/64 = {K:.6f}")
print(f"[EXACT] K^(1/10) = {K**0.1:.4f}   sqrt(K) = {sqrt(K):.4f}")
print(f"[EXACT] damped/sharp variance-rate ratio = eps^(5/2) * sqrt(2)/256 "
      f"(= {sqrt(2)/256:.6e} at eps=1)")

# THE LAW:  sigma(B_k phi)/|box phi| = sqrt(K) * l_p^2 * L^3 / l_k^5   (per-point,
#   L = coherence/support scale of the field configuration; E ~ phi^2 L^2, |box phi| ~ phi/L^2)
# Reliability sigma <= delta * |box phi|  ==>
#   l_k >= K^(1/10) * delta^(-1/5) * l_p^(2/5) * L^(3/5)
print("\n=== MESOSCALE RELIABILITY LAW:  l_k = K^(1/10) delta^(-1/5) l_p^(2/5) L^(3/5) ===")
l_p = 1.616255e-35   # m
for name, L in [("nuclear 1 fm", 1e-15), ("atomic 1 A", 1e-10), ("lab 1 um", 1e-6),
                ("human 1 m", 1.0), ("LIGO arm 4 km", 4e3), ("LISA arm 2.5 Gm", 2.5e9),
                ("AU", 1.5e11), ("galaxy 30 kpc", 1e21),
                ("Hubble radius", 1.37e26), ("particle horizon", 4.4e26)]:
    lk = K**0.1 * l_p**0.4 * L**0.6
    print(f"  L = {name:>18s} ({L:8.1e} m):  l_k_min = {lk:9.3e} m")

# ---------- [PHYS] Lambda refinement ----------
print("\n=== LAMBDA REFINEMENT (everpresent-Lambda channel = constant mode, IR cut at horizon T) ===")
# sigma(B_k . 1) = sqrt(K) l_p^2 T / l_k^5   (E[1] = T^2, both null edges)
# Identify  deltaLambda ~ sigma(B_k . 1)  [PHYS hypothesis]
Lambda_obs = 1.1056e-52   # m^-2  (Planck 2018)
for name, T in [("Hubble radius", 1.37e26), ("particle horizon", 4.4e26)]:
    # reading 1: Lambda_obs fixes the mesoscale
    lk5 = sqrt(K) * l_p**2 * T / Lambda_obs
    lk = lk5**0.2
    # reading 2: reliability saturation at the horizon (delta = 1)
    lk_sat = K**0.1 * l_p**0.4 * T**0.6
    # the dimensionless check: Lambda * T^2 = delta at saturation
    delta_obs = Lambda_obs * T**2
    print(f"  T = {name:>16s}: l_k(Lambda_obs) = {lk:7.2f} m ;  "
          f"l_k(delta=1 at T) = {lk_sat:7.2f} m ;  Lambda_obs*T^2 = {delta_obs:6.2f}")
print("  => the observed Lambda sits at the reliability boundary delta = O(1-20):")
print("     Lambda(T) * T^2 = delta  identically under the law -- Lambda ~ 1/T^2 tracking")
print("     with EXACT prefactor: Lambda(T) = sqrt(K) * l_p^2 * T / l_k(T)^5.")

# crossover scale for a fixed mesoscale
print("\n=== per-point fluctuation-domination crossover  L_* = (l_k^5/(sqrt(K) l_p^2))^(1/3) ===")
for name, lk in [("l_k = 10 fm", 1e-14), ("l_k = 1 pm", 1e-12), ("l_k = 1 nm", 1e-9),
                 ("l_k = 1 um", 1e-6), ("l_k = 100 m (Lambda)", 79.0)]:
    Lstar = (lk**5 / (sqrt(K) * l_p**2))**(1/3)
    print(f"  {name:>22s}: L_* = {Lstar:9.3e} m")

# undamped growth for reference
print("\n=== undamped reference (eps=1): Var = K_s * rho^(3/2) * E,  sigma ~ rho^(3/4) ===")
K_sharp = (4*pi/3) * sqrt(24/pi) * (w_mass_sharp)   # same assembly, sharp w-mass
print(f"  K_sharp = (4pi/3) sqrt(24/pi) (315/4) sqrt(pi) = {K_sharp:.4f}")
print(f"  relative fluctuation of undamped B_rho at L: sqrt(K_s) (L/l_p)^3 -> "
      f"O(1) already at L ~ {l_p * K_sharp**(-1/6):.2e} m: sharp operator useless, "
      f"damping mandatory  [matches Sorkin 2007 / Dowker-Glaser 2013]")
