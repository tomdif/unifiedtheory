#!/usr/bin/env python3
"""The hbar-window law: truncation-2 feasibility in decoupled coordinates.

The truncation-2 system (root + 2-chain + 2-antichain; channels of
smeared size s in {0, W0, W0+W1, 2W0}; in-window phase phi = 2pi j +
delta) depends only on the three angles A = W0*phi (cover winding),
r = W1/W0, d = delta.  This script:

  1. maps feasibility over (A, r, frac = d/A) — finding a single band
     A in (pi/2, pi), independent of r in [0.3, 0.75] and frac, plus
     narrow slivers at A >~ 2.2pi near frac edges;
  2. bisects the band boundaries to 1e-9: EXACTLY pi/2 and pi;
  3. tests the winding-band consequence j in (1/(4W0), 1/(2W0))
     against every prior scan (4D eps 0.045/0.055/0.0625, 2D band,
     3D band) and two pre-registered predictions:
       - 3D eps=0.100 alive at j=3,4 (previously reported dead from a
         j<=2 scan)                          -> CONFIRMED
       - 4D eps=0.045 alive at j=10,11       -> CONFIRMED
     and one falsification: 2D eps=0.25 predicted dead at all j (its
     window (0.5, 1.0) contains no integer) comes back t2-alive at
     j=3..6 — but those hits are delta-aliasing artifacts of the
     window parametrization (delta wraps past 2pi onto resonant
     phases; the j=3 frac=0.5 point is phi = 8pi exactly, where the
     full gate finds a PARTIAL-support survivor, 1081/2450).  The
     genuine-window law stands; the high-winding sliver structure in
     angle space is real but its in-window pullback is open.

Companion Lean: KFCausalSmearedNoGo.lean, whose strengthened
hypotheses (gamma+delta < pi, eta+delta < pi, delta < pi/2, beta <
pi/2) cover ALL windings W0*phi < pi/2 given W1/W0 < 1 (true in every
smeared dimension) — so the lower band edge pi/2 is theorem-exact
from below.
"""
import numpy as np
from scipy.optimize import linprog

def trunc2_angles(A, r, d):
    """Feasibility of the truncation-2 LP given cover winding A = W0*phi,
    ratio r = W1/W0, and window offset d = delta (angles fed directly)."""
    def z(S, mu=1): return mu * np.exp(1j * (d - S))
    rows, b = [], []
    def eq(terms, rhs_var):
        rr = np.zeros(7); ri = np.zeros(7)
        for var, zz in terms:
            rr[var] += zz.real; ri[var] += zz.imag
        if rhs_var is not None: rr[rhs_var] -= 1
        rows.append(rr); b.append(0.0 if rhs_var is not None else 1.0)
        rows.append(ri); b.append(0.0)
    eq([(0, z(A)), (1, z(0))], None)
    eq([(2, z(A)), (3, z(A*(1+r))), (4, z(0))], 0)
    eq([(5, z(0)), (4, z(A, 2)), (6, z(2*A))], 1)
    res = linprog(np.zeros(7), A_eq=np.array(rows), b_eq=np.array(b),
                  bounds=[(0, None)] * 7, method="highs")
    return res.success

def trunc2(W0, W1, phi):
    """Same LP in raw (W0, W1, phi) window coordinates."""
    th = lambda s: (1 - s) * phi
    rows, b = [], []
    def eq(channels, rhs_var):
        rr = np.zeros(7); ri = np.zeros(7)
        for var, mu, s in channels:
            zz = mu * np.exp(1j * th(s))
            rr[var] += zz.real; ri[var] += zz.imag
        if rhs_var is not None: rr[rhs_var] -= 1
        rows.append(rr); b.append(0.0 if rhs_var is not None else 1.0)
        rows.append(ri); b.append(0.0)
    eq([(0, 1, W0), (1, 1, 0.0)], None)
    eq([(2, 1, W0), (3, 1, W0 + W1), (4, 1, 0.0)], 0)
    eq([(5, 1, 0.0), (4, 2, W0), (6, 1, 2 * W0)], 1)
    res = linprog(np.zeros(7), A_eq=np.array(rows), b_eq=np.array(b),
                  bounds=[(0, None)] * 7, method="highs")
    return res.success

print("1. Feasibility map over (A = W0*phi, r = W1/W0, frac = delta/A):")
for r in (0.30, 0.50, 0.75):
    print(f"\n r = {r}:  ('#'=feasible)")
    print("      frac: " + " ".join(f"{f:.2f}" for f in np.arange(0.05, 1.0, 0.1)))
    for Api in np.arange(0.1, 2.45, 0.1):
        A = Api * np.pi
        row = "".join("  # " if trunc2_angles(A, r, f * A) else "  . "
                      for f in np.arange(0.05, 1.0, 0.1))
        print(f"  A={Api:4.1f}pi {row}")

print("\n2. Boundary bisection (30 rounds, units of pi):")
for r in (0.30, 0.50, 0.75):
    for frac in (0.25, 0.50, 0.75):
        lo, hi = 0.5, 0.6
        for _ in range(30):
            mid = (lo + hi) / 2
            if trunc2_angles(mid*np.pi, r, frac*mid*np.pi): hi = mid
            else: lo = mid
        low_b = hi
        lo, hi = 0.9, 1.05
        for _ in range(30):
            mid = (lo + hi) / 2
            if trunc2_angles(mid*np.pi, r, frac*mid*np.pi): lo = mid
            else: hi = mid
        print(f"  r={r} frac={frac}: lower={low_b:.9f}pi upper={lo:.9f}pi")

print("\n3. Winding-band j in (1/(4W0), 1/(2W0)) vs scans + predictions:")
def scan(W0, W1, js, label, pred):
    alive = []
    for j in js:
        for frac in np.linspace(0.05, 0.95, 19):
            delta = frac * W0 * 2*np.pi*j / (1 - frac*W0)
            if trunc2(W0, W1, 2*np.pi*j + delta):
                alive.append(j); break
    print(f"  {label}: predicted {pred}; observed alive j={alive}")

for eps in (0.045, 0.055, 0.0625):
    W0 = eps
    lo, hi = 1/(4*W0), 1/(2*W0)
    scan(W0, eps*(1 - 10*eps), range(1, 13), f"4D eps={eps}",
         f"({lo:.2f}, {hi:.2f})")
eps = 0.100
scan(eps, eps*(1 - 35*eps/8), range(1, 7),
     "3D eps=0.100 [PRE-REGISTERED]", "(2.50, 5.00) -> {3,4}")
eps = 0.16
scan(2*eps, 2*eps*(1 - 3*eps), range(1, 5),
     "2D eps=0.16", "(0.78, 1.56) -> {1}")
eps = 0.25
scan(2*eps, 2*eps*(1 - 3*eps), range(1, 7),
     "2D eps=0.25 [FALSIFIER]",
     "(0.50, 1.00) -> {} but delta-aliasing gives resonant hits")
print("DONE")
