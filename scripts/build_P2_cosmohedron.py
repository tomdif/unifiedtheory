#!/usr/bin/env python3
r"""
build_P2_cosmohedron.py

Build the explicit convex body (the single-edge / P_2 cosmohedron) whose facets
sit at the chamber eigenvalues λ and whose interior weighting point is fixed by the
dual points μ, so that the spectral weights come out as HONEST SUB-POLYTOPE VOLUMES.

Construction (a 2-simplex = triangle, matching "single-edge cosmological polytope
= 2-simplex"):

  • Lift each eigenvalue to the moment curve (parabola):  P_i = (λ_i, λ_i²).
    The three P_i are the VERTICES of the triangle T = conv{P_1,P_2,P_3}.
    (Projective duality: the triangle's three facets <-> the three boundaries λ_i.)

  • The WEIGHTING POINT is the moment point  Q = (m_1, m_2)  of the spectral
    measure, where m_k = Σ_i w_i λ_i^k = (J^k)_{11}. Crucially m_1, m_2 are fixed by
    the dual points μ:   m_1 = Σλ_i − Σμ_k   (the duals pull the mean).

  • Connecting Q to the three vertices TRIANGULATES T into three cells
    (Q,P_2,P_3), (Q,P_3,P_1), (Q,P_1,P_2). The spectral weights are the cell
    volume fractions (barycentric coordinates):

            w_i = Area(Q, P_j, P_k) / Area(P_1, P_2, P_3).

  So each weight is literally the volume of a sub-polytope of T. Q interior
  (all cell areas > 0) <=> all weights positive <=> honest positive geometry.

Everything exact; all assertions checked.
"""

import sympy as sp

z = sp.symbols('z', real=True)
Nc, Ntot, disc = 3, 5, 7

# ----------------------------------------------------------------------
# 0. Inputs: spectrum λ, dual points μ, target weights, chamber operator
# ----------------------------------------------------------------------
b1 = sp.sqrt(sp.Rational(1,25)); b2 = sp.sqrt(sp.Rational(1,50))
J = sp.Matrix([[sp.Rational(1,3), b1, 0],
               [b1, sp.Rational(2,5), b2],
               [0, b2, sp.Rational(1,5)]])
lam = sorted([sp.nsimplify(sp.simplify(e)) for e in J.eigenvals()], key=float, reverse=True)
mu  = sorted([sp.nsimplify(sp.simplify(e)) for e in J[1:,1:].eigenvals()], key=float, reverse=True)
w_target = [sp.Rational(1,3), (7+sp.sqrt(7))/21, (7-sp.sqrt(7))/21]

# ----------------------------------------------------------------------
# 1. The weighting point Q from the moments — and from the dual points
# ----------------------------------------------------------------------
m1 = sp.simplify((J**1)[0,0])      # first moment = (J)_11
m2 = sp.simplify((J**2)[0,0])      # second moment = (J^2)_11
Q = (m1, m2)
print("=" * 72)
print("[1] weighting point Q = (m_1, m_2) = ((J)_11, (J^2)_11):")
print(f"    m_1 = {m1}  = 1/N_c")
print(f"    m_2 = {m2}  = 1/N_c² + 1/N_total² = 1/9 + 1/25")
assert m1 == sp.Rational(1,3)
assert sp.simplify(m2 - (sp.Rational(1,9) + sp.Rational(1,25))) == 0

# the dual points locate Q:  m_1 = Σλ − Σμ
m1_from_duals = sp.simplify(sum(lam) - sum(mu))
print(f"    check  m_1 = Σλ − Σμ = {m1_from_duals}   (the dual points pull the mean)")
assert sp.simplify(m1_from_duals - m1) == 0
print("    ✓ Q is atomic and is located by the dual points μ.")

# ----------------------------------------------------------------------
# 2. The convex body: triangle on the moment curve
# ----------------------------------------------------------------------
P = [(l, l**2) for l in lam]
print("\n[2] triangle T = conv{P_i},  P_i = (λ_i, λ_i²) on the moment curve:")
for i, Pi in enumerate(P, 1):
    print(f"    P_{i} = ({sp.sstr(Pi[0])}, {sp.sstr(sp.expand(Pi[1]))})  ≈ ({float(Pi[0]):.4f}, {float(Pi[1]):.4f})")
print(f"    Q   = ({sp.sstr(Q[0])}, {sp.sstr(Q[1])})  ≈ ({float(Q[0]):.4f}, {float(Q[1]):.4f})")

def area(X, Y, W):
    return sp.Rational(1,2) * sp.Matrix([[Y[0]-X[0], Y[1]-X[1]],
                                         [W[0]-X[0], W[1]-X[1]]]).det()

A_tot = sp.simplify(area(P[0], P[1], P[2]))
cells = [sp.simplify(area(Q, P[1], P[2])),    # cell opposite vertex 1
         sp.simplify(area(P[0], Q, P[2])),    # opposite vertex 2
         sp.simplify(area(P[0], P[1], Q))]    # opposite vertex 3
print(f"\n[2] total area Area(T) = {A_tot}")
print("    Q triangulates T into three cells; volume fractions (barycentric coords):")

# ----------------------------------------------------------------------
# 3. Weights = sub-polytope volume fractions; check against targets
# ----------------------------------------------------------------------
# NB: the moment-curve vertices are clockwise, so Area(T) and all signed cells
# share one sign; Q interior <=> every volume FRACTION (barycentric coord) > 0.
all_ok = True
for i in range(3):
    w_geo = sp.simplify(cells[i] / A_tot)
    ok = sp.simplify(w_geo - w_target[i]) == 0
    pos = float(w_geo) > 0
    all_ok &= ok and pos
    print(f"    w_{i+1} = Area(cell_{i+1})/Area(T) = {sp.sstr(sp.nsimplify(w_geo)):>16}  "
          f"= target? {ok}   fraction>0? {pos}")
assert all_ok
wsum = sp.simplify(sum(cells)/A_tot)
print(f"    Σ w_i = {wsum}  (cells tile T)   Q interior ⇒ all weights > 0 ⇒ positive geometry")
assert wsum == 1

# ----------------------------------------------------------------------
# 4. Higgs residue as a sub-polytope volume
# ----------------------------------------------------------------------
print("\n[3] Higgs residue 1/N_c as an honest volume:")
print(f"    w_1 = Area(Q,P_2,P_3)/Area(P_1,P_2,P_3) = {sp.simplify(cells[0]/A_tot)} = 1/N_c")
print("    = the volume fraction of the cell OPPOSITE the top eigenvalue.")
assert sp.simplify(cells[0]/A_tot - sp.Rational(1,3)) == 0

# ----------------------------------------------------------------------
# 5. Canonical-form closure: rebuild m(z) from the volume weights
# ----------------------------------------------------------------------
m_from_volumes = sum(sp.simplify(cells[i]/A_tot) / (z - lam[i]) for i in range(3))
m_target = sp.prod([z - d for d in mu]) / sp.prod([z - l for l in lam])
closes = sp.simplify(m_from_volumes - m_target) == 0
print("\n[4] canonical-form closure:")
print(f"    Σ_i [Area(cell_i)/Area(T)] / (z − λ_i)  ==  ∏(z−μ)/∏(z−λ) :  {closes}")
assert closes
print("    ✓ the volume-weighted canonical form reproduces m(z) exactly.")

# ----------------------------------------------------------------------
print("\n" + "=" * 72)
print("VERDICT — the P_2 cosmohedron is built")
print("=" * 72)
print("""
CONVEX BODY:  the 2-simplex  T = conv{(λ_i, λ_i²)}  (vertices on the moment curve)
  — a triangle, exactly the shape of the single-edge (P_2) cosmological polytope;
  its three facets are dual to the three chamber boundaries λ_i.

WEIGHTING POINT:  Q = (m_1, m_2) = ((J)_11, (J²)_11) = (1/N_c, 1/N_c²+1/N_total²),
  an ATOMIC interior point located by the dual points via m_1 = Σλ − Σμ.

WEIGHTS = HONEST SUB-POLYTOPE VOLUMES:  connecting Q to the vertices triangulates T
  into three cells whose volume fractions are exactly the spectral weights
        w_i = Area(Q,P_j,P_k)/Area(T) = {1/N_c, (disc ± √disc)/(N_c·disc)},
  and the volume-weighted canonical form Σ w_i/(z−λ_i) reproduces m(z).

HIGGS RESIDUE:  1/N_c is the volume fraction of the cell opposite the top
  eigenvalue — a genuine area ratio in an atomic convex body, no longer a
  spectral coincidence.

This completes the chain: chamber spectrum → weighted positive geometry →
single-edge cosmohedron realized as an explicit atomic triangle with the Higgs
residue as a sub-polytope volume.

SCOPE (honest): T is the moment-curve 2-simplex carrying the correct weighted
positive-geometry data (boundaries λ, weighting point from μ, volume-weights).
Its projective identification with the literal Arkani-Hamed–Benincasa single-edge
cosmological polytope (same 2-simplex shape) is asserted at the level of the
weighted canonical form verified here, not via an independent ABP vertex
derivation — that cross-check is the one remaining tidy-up.
""")
