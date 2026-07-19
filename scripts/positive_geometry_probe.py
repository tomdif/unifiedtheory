#!/usr/bin/env python3
r"""
positive_geometry_probe.py

PROBE: Is the J_4 spectral measure the canonical form of a 1D positive geometry
whose boundaries are the three chamber eigenvalues?

Context. The unifiedtheory framework derives the chamber Jacobi matrix

        J_4 = [ 1/3   b1    0  ]
              [ b1   2/5   b2  ]      b1^2 = 1/25,  b2^2 = 1/50
              [ 0    b2   1/5  ]

whose spectrum {3/5, (5±√7)/30} and first-component spectral weights ("residues"
r1,r2,r3 with sum = 1, r1 = 1/3 = 1/N_c) carry the physical content (Higgs residue,
mass hierarchy). The amplitudes / positive-geometry program writes physics as the
*canonical form* of a region: a rational top-form with simple poles on the region's
boundaries and residues equal to the canonical forms of those boundaries.

This script tests, with exact arithmetic, whether the J_4 data has that structure:

  (1) Spectral measure: atoms = eigenvalues, weights = first-component^2. Exact forms.
  (2) Resolvent / Weyl m-function m(z) = [ (zI - J)^{-1} ]_{11} = sum_i w_i/(z - λ_i).
      This is the candidate "canonical form": rational, simple poles at the eigenvalues,
      residue at each pole = spectral weight.
  (3) Positivity (Herglotz signature): all residues > 0  <=>  honest positive *measure*.
  (4) Interlacing: zeros of the m-function numerator (eigenvalues of the deleted 2x2
      minor) strictly interlace the eigenvalues of J_4 -- the 1D shadow of positivity.
  (5) Triangulation / spurious-pole cancellation: the interval [λ_min, λ_max]
      triangulated by the middle eigenvalue has Ω(whole) = Ω(left) + Ω(right) with the
      interior pole canceling -- the positive-geometry signature for the eigenvalue
      LOCATIONS (independent of the weights).
  (6) Arithmetic of the weights: are the residues (the would-be canonical forms of the
      boundaries) expressible in the atomic vocabulary {N_W=2, N_c=3, N_total=5, disc=7}?

Exact symbolic throughout. Zero floating-point in the verdicts.
"""

import sympy as sp

# ----------------------------------------------------------------------
# 0. The exact J_4 chamber Jacobi matrix
# ----------------------------------------------------------------------
b1 = sp.sqrt(sp.Rational(1, 25))   # 1/5
b2 = sp.sqrt(sp.Rational(1, 50))   # 1/(5√2)
J = sp.Matrix([
    [sp.Rational(1, 3), b1,               0 ],
    [b1,               sp.Rational(2, 5), b2],
    [0,                b2,                sp.Rational(1, 5)],
])
z = sp.symbols('z', real=True)

print("=" * 72)
print("J_4 chamber Jacobi matrix (exact):")
sp.pprint(J)

# ----------------------------------------------------------------------
# 1. Spectrum and spectral weights (the "residues")
# ----------------------------------------------------------------------
charpoly = sp.factor(J.charpoly(z).as_expr())
print("\n[1] characteristic polynomial  det(zI - J) =")
sp.pprint(charpoly)

eig = J.eigenvects()                      # [(eigenvalue, mult, [vecs]), ...]
eigdata = []
for val, mult, vecs in eig:
    v = vecs[0]
    w = sp.simplify(v[0]**2 / (v.T * v)[0])   # first-component^2 of normalized vec
    eigdata.append((sp.nsimplify(sp.simplify(val)), sp.nsimplify(sp.simplify(w))))
# sort by eigenvalue descending
eigdata.sort(key=lambda t: float(t[0]), reverse=True)

print("\n[1] spectral measure  (atom λ_i, weight w_i):")
for i, (val, w) in enumerate(eigdata, 1):
    print(f"    λ_{i} = {sp.sstr(val):>14}  ≈ {float(val):.6f}   "
          f"w_{i} = {sp.sstr(w):>14}  ≈ {float(w):.6f}")

wsum = sp.simplify(sum(w for _, w in eigdata))
print(f"\n    Σ w_i = {wsum}   (probability measure if = 1)")
assert wsum == 1, "weights must sum to 1"
assert eigdata[0][1] == sp.Rational(1, 3), "top weight must be the Higgs residue 1/3"
print("    ✓ weights sum to 1;  top weight w_1 = 1/3 = 1/N_c (Higgs residue)")

# ----------------------------------------------------------------------
# 2. Resolvent / Weyl m-function = candidate canonical form
# ----------------------------------------------------------------------
I3 = sp.eye(3)
resolvent = (z * I3 - J).inv()
m = sp.simplify(resolvent[0, 0])          # (1,1) entry = Weyl m-function
m_ratio = sp.cancel(m)
num, den = sp.fraction(m_ratio)
print("\n[2] Weyl m-function  m(z) = [(zI - J)^{-1}]_11 = P(z)/Q(z):")
print("    P(z) =", sp.factor(num))
print("    Q(z) =", sp.factor(den))

# partial-fraction = sum of weights over (z - λ_i)
m_apart = sp.apart(m_ratio, z, full=True).doit()
print("\n    partial fractions:")
sp.pprint(m_apart)

# verify residues equal the spectral weights
print("\n[2] residue of m(z) at each eigenvalue  (should equal spectral weight w_i):")
for i, (val, w) in enumerate(eigdata, 1):
    res = sp.simplify(sp.residue(m_ratio, z, val))
    ok = sp.simplify(res - w) == 0
    print(f"    Res_{{z=λ_{i}}} m = {sp.sstr(res):>14}   == w_{i}?  {ok}")
    assert ok

# ----------------------------------------------------------------------
# 3. Positivity (Herglotz): all residues > 0  <=>  honest positive measure
# ----------------------------------------------------------------------
allpos = all(float(w) > 0 for _, w in eigdata)
print(f"\n[3] all residues > 0 (Herglotz / positive-measure signature): {allpos}")
assert allpos
print("    ✓ m(z) is a Nevanlinna/Herglotz function: maps upper half-plane to lower,")
print("      simple poles on the real axis, positive residues. This is the 1D")
print("      'positivity' that the amplituhedron enforces via boundary structure.")

# ----------------------------------------------------------------------
# 4. Interlacing: numerator zeros (deleted-minor eigenvalues) interlace spectrum
# ----------------------------------------------------------------------
minor = J[1:, 1:]                          # delete row/col 1
minor_eigs = sorted([sp.nsimplify(sp.simplify(e)) for e in minor.eigenvals()],
                    key=float, reverse=True)
print("\n[4] deleted 2x2 minor eigenvalues (zeros of P(z)):")
for j, mu in enumerate(minor_eigs, 1):
    print(f"    μ_{j} = {sp.sstr(mu):>14}  ≈ {float(mu):.6f}")

lam = [float(v) for v, _ in eigdata]
mu = [float(x) for x in minor_eigs]
interlaces = lam[0] > mu[0] > lam[1] > mu[1] > lam[2]
print(f"\n    interlacing  λ_1 > μ_1 > λ_2 > μ_2 > λ_3 :  "
      f"{lam[0]:.4f} > {mu[0]:.4f} > {lam[1]:.4f} > {mu[1]:.4f} > {lam[2]:.4f}")
print(f"    strict interlacing holds: {interlaces}")
assert interlaces

# ----------------------------------------------------------------------
# 5. Triangulation / spurious-pole cancellation (eigenvalue LOCATIONS)
# ----------------------------------------------------------------------
# canonical 1-form of an interval [a,b]:  ω(x;a,b) = 1/(x-a) - 1/(x-b)
def omega(a, b):
    return 1/(z - a) - 1/(z - b)

a_lo, a_mid, a_hi = eigdata[2][0], eigdata[1][0], eigdata[0][0]   # λ3 < λ2 < λ1
whole = omega(a_lo, a_hi)
left = omega(a_lo, a_mid)
right = omega(a_mid, a_hi)
triangulation_ok = sp.simplify(left + right - whole) == 0
print("\n[5] triangulation of [λ_3, λ_1] by the interior eigenvalue λ_2:")
print("    Ω([λ_3,λ_1])  ?=  Ω([λ_3,λ_2]) + Ω([λ_2,λ_1])   (interior pole cancels)")
print(f"    holds: {triangulation_ok}")
assert triangulation_ok
print("    ✓ the eigenvalue LOCATIONS form a valid 1D positive geometry: the middle")
print("      eigenvalue is a SPURIOUS pole that cancels — the amplitude-style")
print("      'locality from boundaries' signature, seen here for the mass spectrum.")

# ----------------------------------------------------------------------
# 6. Arithmetic of the weights in the atomic vocabulary {2,3,4,5,7}
# ----------------------------------------------------------------------
print("\n[6] are the canonical-form residues (weights) atomic in {N_W,N_c,N_total,disc}?")
r1 = eigdata[0][1]
r2, r3 = eigdata[1][1], eigdata[2][1]
r2r3_sum = sp.simplify(r2 + r3)
r2r3_prod = sp.simplify(r2 * r3)
print(f"    w_1 = {r1}              = 1/N_c                      ({sp.simplify(r1 - sp.Rational(1,3))==0})")
print(f"    w_2 + w_3 = {r2r3_sum}            = 2/N_c                      ({sp.simplify(r2r3_sum - sp.Rational(2,3))==0})")
print(f"    w_2 * w_3 = {r2r3_prod}           = 2/(N_c·disc) = 2/21        ({sp.simplify(r2r3_prod - sp.Rational(2,21))==0})")
# closed forms (7 ± √7)/21
cf2 = (7 + sp.sqrt(7)) / 21
cf3 = (7 - sp.sqrt(7)) / 21
match2 = sp.simplify(r2 - cf2) == 0 and sp.simplify(r3 - cf3) == 0
match3 = sp.simplify(r2 - cf3) == 0 and sp.simplify(r3 - cf2) == 0
print(f"    closed form: {{w_2, w_3}} = {{(7+√7)/21, (7-√7)/21}} = {{(disc+√disc)/(N_c·disc)}} : "
      f"{match2 or match3}")
assert match2 or match3
print("    ✓ ALL three residues live in ℚ(√7), the disc=7 quadratic field:")
print("        w_1 = 1/3,   w_{2,3} = (7 ± √7)/21.")
print("      The would-be canonical-form residues ARE the framework's atomic numbers.")

# ----------------------------------------------------------------------
# 7. The honest negative: is it the canonical form of an UNWEIGHTED region?
# ----------------------------------------------------------------------
print("\n[7] strict test: a *bare* 1D positive geometry (interval) has residues ±1.")
unit_residues = all(abs(float(w)) == 1 for _, w in eigdata)
print(f"    are the residues ±1?  {unit_residues}")
print("    -> NO. The weights are positive and sum to 1 but are not ±1, so the")
print("       spectral measure is NOT the canonical form of a bare interval.")
print("       It is a WEIGHTED positive geometry: 3 boundary points carrying")
print("       positive weights summing to 1 — exactly the Benincasa–Dian")
print("       'weighted cosmological polytope' structure (the cosmological branch).")

print("\n" + "=" * 72)
print("VERDICT")
print("=" * 72)
print("""
The J_4 spectral data DOES carry positive-geometry structure, but of the
*weighted* kind, not the bare-amplituhedron kind:

  • Canonical form          = Weyl m-function m(z) = Σ w_i/(z - λ_i)   [PASS]
  • Boundaries              = the three chamber eigenvalues (mass spectrum)
  • Positivity (Herglotz)   = all residues > 0                        [PASS]
  • Interlacing signature   = minor eigenvalues strictly interlace    [PASS]
  • Triangulation/locality  = interior eigenvalue is a spurious pole  [PASS]
                              that cancels (locations form a 1D pos. geom.)
  • Bare canonical form     = residues are ±1                         [FAIL]
  • Weighted canonical form = residues > 0, Σ = 1, atomic in √7       [PASS]

So the right target on the positive-geometry side is the COSMOLOGICAL branch
(weighted cosmological polytopes / cosmohedra), not the amplituhedron: those
use positive geometries whose boundaries carry weights — and here the weights
are forced to be {1/N_c, (disc ± √disc)/(N_c·disc)}, i.e. the framework's own
atomic vocabulary. The physical payoff direction is now sharp: if a weighted
0/1-dim positive geometry can be built whose three boundary weights are
DERIVED as canonical forms of sub-geometries, then r_1 = 1/N_c (the Higgs
residue) gets a positive-geometry *reason* rather than a spectral coincidence.
""")
