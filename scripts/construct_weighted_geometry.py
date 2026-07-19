#!/usr/bin/env python3
r"""
construct_weighted_geometry.py

GOAL: derive the three chamber spectral weights

        w_1 = 1/3 = 1/N_c          (the Higgs residue)
        w_2 = (7 + √7)/21
        w_3 = (7 - √7)/21

as canonical-form residues of a *weighted* positive geometry built from
sub-geometries -- not read off as eigenvector components.

The construction (all data exact, all closed forms atomic in {N_c, N_total, disc}):

  VERTICES (boundaries of the geometry) = chamber eigenvalues λ_i :
        λ_1 = N_c / N_total                      = 3/5
        λ_{2,3} = (N_total ± √disc)/(2 N_c N_total) = (5 ± √7)/30

  DUAL POINTS (interlacing partners) μ_k = spectrum of the sub-system with the
  TOP (Higgs / N_c) channel deleted = eigenvalues of the lower 2x2 minor :
        μ_{1,2} = (N_c ± √N_c)/(2 N_total)        = (3 ± √3)/10

  CANONICAL FORM:  Ω = m(z) = ∏_k (z - μ_k) / ∏_i (z - λ_i)   (monic Weyl m-function)

  THEOREM TO VERIFY:  the residue of Ω at each vertex λ_i is the weight w_i, and
  equals the DISTANCE RATIO

        w_i = ∏_k (λ_i - μ_k) / ∏_{j≠i} (λ_i - λ_j).

  Interpretation: each weight is the boundary's own lower canonical form, fixed by
  the configuration of the vertices AND the once-reduced sub-geometry (the μ's).
  The μ's are NOT arbitrary -- they are the framework with the N_c channel removed.
  So the weights are derived from two atomic spectra, not from a generic partial
  fraction.

Also verifies the recursive (continued-fraction) ladder of sub-geometries, in
which the Higgs residue 1/N_c is the BARE top atom before any coupling.
"""

import sympy as sp

z = sp.symbols('z', real=True)
Nc, Ntot, disc = 3, 5, 7          # atomic vocabulary

# ----------------------------------------------------------------------
# 0. Atomic closed forms for vertices and dual points
# ----------------------------------------------------------------------
lam1 = sp.Rational(Nc, Ntot)                                   # N_c/N_total
lam2 = (Ntot + sp.sqrt(disc)) / (2 * Nc * Ntot)                # (N_total+√disc)/(2 N_c N_total)
lam3 = (Ntot - sp.sqrt(disc)) / (2 * Nc * Ntot)
mu1 = (Nc + sp.sqrt(Nc)) / (2 * Ntot)                          # (N_c+√N_c)/(2 N_total)
mu2 = (Nc - sp.sqrt(Nc)) / (2 * Ntot)
verts = [lam1, lam2, lam3]
duals = [mu1, mu2]

print("=" * 72)
print("ATOMIC CONFIGURATION  (vertices λ, dual/interlacing points μ)")
print("=" * 72)
print(f"  λ_1 = N_c/N_total                  = {lam1}        ≈ {float(lam1):.6f}")
print(f"  λ_2 = (N_total+√disc)/(2 N_c N_tot) = {sp.nsimplify(lam2)}  ≈ {float(lam2):.6f}")
print(f"  λ_3 = (N_total-√disc)/(2 N_c N_tot) = {sp.nsimplify(lam3)}  ≈ {float(lam3):.6f}")
print(f"  μ_1 = (N_c+√N_c)/(2 N_total)        = {sp.nsimplify(mu1)}    ≈ {float(mu1):.6f}")
print(f"  μ_2 = (N_c-√N_c)/(2 N_total)        = {sp.nsimplify(mu2)}    ≈ {float(mu2):.6f}")
print("  vertices ∈ ℚ(√disc)=ℚ(√7) ;  dual points ∈ ℚ(√N_c)=ℚ(√3)")

# ----------------------------------------------------------------------
# 1. Cross-check the configuration against the actual J_4
# ----------------------------------------------------------------------
b1 = sp.sqrt(sp.Rational(1, 25)); b2 = sp.sqrt(sp.Rational(1, 50))
J = sp.Matrix([[sp.Rational(1,3), b1, 0],
               [b1, sp.Rational(2,5), b2],
               [0, b2, sp.Rational(1,5)]])
J_eigs = sorted([sp.nsimplify(sp.simplify(e)) for e in J.eigenvals()], key=float, reverse=True)
minor_eigs = sorted([sp.nsimplify(sp.simplify(e)) for e in J[1:,1:].eigenvals()], key=float, reverse=True)
assert all(sp.simplify(a-b)==0 for a,b in zip(J_eigs, verts)), "vertices must be J_4 spectrum"
assert all(sp.simplify(a-b)==0 for a,b in zip(minor_eigs, duals)), "duals must be deleted-minor spectrum"
print("\n[1] ✓ vertices = spectrum(J_4);  dual points = spectrum(J_4 with N_c channel deleted)")

# ----------------------------------------------------------------------
# 2. Canonical form and the distance-ratio derivation of the weights
# ----------------------------------------------------------------------
Q = sp.prod([z - v for v in verts])      # monic denominator (vertices)
P = sp.prod([z - d for d in duals])      # monic numerator   (dual points)
Omega = P / Q
print("\n[2] canonical form  Ω(z) = ∏_k (z-μ_k) / ∏_i (z-λ_i):")
print("    Ω(z) =", sp.simplify(Omega))

w_target = {1: sp.Rational(1,3),
            2: (7 + sp.sqrt(7))/21,
            3: (7 - sp.sqrt(7))/21}

print("\n[2] weight at each vertex  =  ∏(λ_i-μ_k) / ∏_{j≠i}(λ_i-λ_j)  =  Res_{λ_i} Ω :")
for i, vi in enumerate(verts, 1):
    dist_ratio = sp.simplify(sp.prod([vi - d for d in duals]) /
                             sp.prod([vi - vj for j, vj in enumerate(verts, 1) if j != i]))
    res = sp.simplify(sp.residue(Omega, z, vi))
    tgt = w_target[i]
    ok = sp.simplify(dist_ratio - tgt) == 0 and sp.simplify(res - tgt) == 0
    print(f"    w_{i}: distance-ratio = {sp.sstr(sp.nsimplify(dist_ratio)):>16}  "
          f"= Res Ω = {sp.sstr(sp.nsimplify(res)):>16}  = target?  {ok}")
    assert ok
print("    ✓ all three weights DERIVED as distance ratios / canonical-form residues")

# ----------------------------------------------------------------------
# 3. Higgs-residue spotlight: 1/N_c as a ratio of boundary distances
# ----------------------------------------------------------------------
print("\n[3] Higgs residue 1/N_c as pure geometry (top vertex λ_1 = N_c/N_total):")
num = sp.simplify((lam1 - mu1) * (lam1 - mu2))
den = sp.simplify((lam1 - lam2) * (lam1 - lam3))
print(f"    (λ_1-μ_1)(λ_1-μ_2) = {num}      [distance² to the two dual points]")
print(f"    (λ_1-λ_2)(λ_1-λ_3) = {den}      [distance² to the two other vertices]")
print(f"    ratio = {sp.simplify(num/den)} = 1/N_c")
assert sp.simplify(num/den - sp.Rational(1,3)) == 0
print("    ✓ the Higgs residue 1/N_c is the canonical-form residue at the top")
print("      boundary — a distance ratio among the atomic vertex/dual configuration,")
print("      NOT an eigenvector coincidence.")

# ----------------------------------------------------------------------
# 4. Recursive sub-geometry ladder (continued fraction): 1/N_c is the bare atom
# ----------------------------------------------------------------------
a1, a2, a3 = sp.Rational(1,3), sp.Rational(2,5), sp.Rational(1,5)   # = 1/N_c, N_W/N_tot, 1/N_tot
B1, B2 = sp.Rational(1,25), sp.Rational(1,50)                       # b1², b2² = 1/N_tot², 1/(N_W N_tot²)

C1 = 1/(z - a1)                                  # bare top atom
C2 = 1/(z - a1 - B1/(z - a2))                    # + 1 coupling
C3 = 1/(z - a1 - B1/(z - a2 - B2/(z - a3)))      # full geometry
assert sp.simplify(C3 - Omega) == 0, "continued fraction must rebuild the canonical form"
print("\n[4] recursive sub-geometry ladder (Jacobi continued fraction):")
print(f"    C_1 = 1/(z - 1/N_c)            -> single boundary at 1/N_c, residue 1  (BARE ATOM)")
print(f"    C_2 = 1/(z - 1/N_c - 1/N_tot²/(z - N_W/N_tot))     -> 2 boundaries")
print(f"    C_3 = full chamber canonical form Ω               -> 3 boundaries")
print("    ✓ C_3 == Ω ; the geometry is literally built by nesting atoms, and the")
print("      Higgs channel 1/N_c is the rank-1 sub-geometry before any coupling.")
# convergent poles
p1 = sp.Rational(1,3)
print(f"      C_1 pole = {p1} = 1/N_c (the bare Higgs atom location)")

# ----------------------------------------------------------------------
# 5. What is and isn't established
# ----------------------------------------------------------------------
print("\n" + "=" * 72)
print("VERDICT")
print("=" * 72)
print("""
DERIVED (exact, atomic):
  • A weighted positive geometry whose vertices are the chamber eigenvalues and
    whose dual points are the spectrum-with-the-N_c-channel-removed, all in closed
    atomic form (vertices ∈ ℚ(√disc), duals ∈ ℚ(√N_c)).
  • Each boundary weight = canonical-form residue = distance ratio
        w_i = ∏(λ_i - μ_k) / ∏_{j≠i}(λ_i - λ_j),
    reproducing {1/N_c, (disc ± √disc)/(N_c·disc)} EXACTLY.
  • The Higgs residue 1/N_c is now a *geometric* quantity: the residue at the top
    boundary, fixed by the configuration of two atomic spectra (full + reduced).
  • The whole form is the nested continued fraction of atomic (a_i, b_i²) data;
    1/N_c is the bare rank-1 atom.

NOT YET ESTABLISHED (the honest open step):
  • This is a 1D weighted positive geometry presented by its boundary+dual data.
    It is NOT yet exhibited as the canonical form (or a facet) of an actual convex
    COSMOLOGICAL POLYTOPE / cosmohedron in the Arkani-Hamed–Benincasa sense.
    The dual points μ play the role the *reduced graph* plays in a cosmological
    polytope, which is suggestive, but no polytope has been constructed whose
    triangulation yields these weights from sub-polytope volumes.
  • Bridging that gap = realize {λ_i} ∪ {μ_k} as the vertices of a cosmological
    polytope for a small graph, with the N_c-channel deletion = an edge contraction.
    That is the next bounded target.
""")
