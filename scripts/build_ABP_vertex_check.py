#!/usr/bin/env python3
r"""
build_ABP_vertex_check.py  —  THE DECISIVE CHECK (pre-registered result: 0)

Construct the literal Arkani-Hamed–Benincasa–Postnikov (ABP) single-edge
cosmological polytope from its defining vertices, take its actual canonical form,
restrict it to the line matched to the chamber spectrum, and report the RESIDUE SUM.

Pre-registration (Parseval obstruction, standing since the smallest-graph round):
    m(z) = Σ_i w_i/(z−λ_i) has Σ residues = Σ w_i = Σ_i |v_i(Higgs)|² = 1.
    The canonical form of a 2-simplex has a CONSTANT numerator, so on any line it
    has Σ residues = 0. A projective map transports the canonical form covariantly
    and cannot raise the numerator degree 0 → 2. Therefore the literal ABP form,
    on the matched line, must have residue sum 0, NOT 1 — i.e. it is NOT m(z).

This script runs that check honestly. It does NOT multiply by any hand-inserted
numerator. The verdict is forced, not narrated.
"""

import sympy as sp

x1, x2, y, z = sp.symbols('x1 x2 y z', real=True)

# ----------------------------------------------------------------------
# 1. ABP vertices, facet covectors = the 3 connected-subgraph energies
# ----------------------------------------------------------------------
Z1 = sp.Matrix([1, -1, 1]); Z2 = sp.Matrix([-1, 1, 1]); Z3 = sp.Matrix([1, 1, -1])
Y = sp.Matrix([x1, x2, y])
facets = [Z1.cross(Z2), Z2.cross(Z3), Z3.cross(Z1)]
energies = []
for f in facets:
    fr = sp.Matrix([sp.nsimplify(c) for c in f]); fr = fr / sp.gcd(list(fr))
    # fix overall sign so the first nonzero entry is positive
    lead = next(c for c in fr if c != 0)
    if lead < 0:
        fr = -fr
    energies.append(sp.simplify((fr.T * Y)[0]))
assert set(energies) == {x1 + x2, x1 + y, x2 + y}
print("[1] ABP single-edge polytope: facet energies =", set(map(str, energies)))
print("    ✓ the genuine ABP cosmological polytope (vertices Z1,Z2,Z3).")

# ----------------------------------------------------------------------
# 2. Its actual canonical function (constant numerator)
# ----------------------------------------------------------------------
def br(A, B, C): return sp.Matrix.hstack(A, B, C).det()
psi_ABP = sp.simplify(br(Z1, Z2, Z3)**2 / (br(Y, Z1, Z2) * br(Y, Z2, Z3) * br(Y, Z3, Z1)))
print("\n[2] canonical function ψ_ABP =", psi_ABP)
print("    numerator is CONSTANT (degree 0).")
assert sp.simplify(psi_ABP - (-2/((x1+x2)*(x1+y)*(x2+y)))) == 0

# ----------------------------------------------------------------------
# 3. Match the line to the chamber spectrum, take the canonical form, RESIDUE SUM
# ----------------------------------------------------------------------
lam = [sp.Rational(3,5), (5 + sp.sqrt(7))/30, (5 - sp.sqrt(7))/30]
mu  = [(3 + sp.sqrt(3))/10, (3 - sp.sqrt(3))/10]
sol = sp.solve([x1 + x2 - (z - lam[0]),
                x1 + y  - (z - lam[1]),
                x2 + y  - (z - lam[2])], [x1, x2, y], dict=True)[0]
psi_line = sp.simplify(psi_ABP.subs(sol))
print("\n[3] literal ABP canonical form on the matched line:")
print("    ψ_ABP|line =", psi_line)
res_ABP = [sp.simplify(sp.residue(psi_line, z, l)) for l in lam]
sum_ABP = sp.simplify(sum(res_ABP))
print(f"    residues = {[sp.sstr(r) for r in res_ABP]}")
print(f"    >>> RESIDUE SUM of the literal ABP canonical form = {sum_ABP}")

# the spectral measure for comparison
m = sp.prod([z - d for d in mu]) / sp.prod([z - l for l in lam])
sum_m = sp.simplify(sum(sp.residue(m, z, l) for l in lam))
print(f"    residue sum of the spectral measure m(z)        = {sum_m}")

print("\n[4] verdict (forced):")
print(f"    Σres(ABP) = {sum_ABP}   ≠   Σres(m) = {sum_m}")
print(f"    ψ_ABP|line == m(z)?  {sp.simplify(psi_line - m) == 0}")
assert sum_ABP == 0
assert sum_m == 1
assert sp.simplify(psi_line - m) != 0
print("""
    The literal ABP single-edge canonical form has residue sum 0; the spectral
    measure m(z) has residue sum 1. They are NOT equal. The cosmological-polytope /
    cosmohedron identification FAILS on the residue sum — the same Parseval
    obstruction (Σ|v_i(Higgs)|² = 1) from the smallest-graph round, never revived.

    Earlier rounds reproduced m(z) only by MULTIPLYING ψ_ABP by a hand-inserted
    numerator ∏(z−μ). That multiplication is not a positive-geometry operation on
    the polytope; it inserts the answer. Removing it, the verdict is forced.
""")

# ----------------------------------------------------------------------
# 5. The deflated TRUE statement
# ----------------------------------------------------------------------
J = sp.Matrix([[sp.Rational(1,3), sp.sqrt(sp.Rational(1,25)), 0],
               [sp.sqrt(sp.Rational(1,25)), sp.Rational(2,5), sp.sqrt(sp.Rational(1,50))],
               [0, sp.sqrt(sp.Rational(1,50)), sp.Rational(1,5)]])
# Higgs-site spectral weight of the top eigenvalue = squared first component
val = sp.Rational(3,5)
vecs = [v for (e, m_, vs) in J.eigenvects() for v in vs if sp.simplify(e - val) == 0]
v = vecs[0]; w_higgs = sp.simplify(v[0]**2 / (v.T * v)[0])
print("[5] the deflated, true statement:")
print(f"    Higgs weight 1/N_c = |v(Higgs)|² of the top eigenvector = {w_higgs}")
assert w_higgs == sp.Rational(1,3)
print("""    The chamber weights are the Gauss-quadrature weights of the spectral
    measure of the Higgs-site Jacobi operator J — equivalently the
    eigenvector-eigenvalue identity — with a clean moment-curve picture
    (barycentric coords of the spectral moment point). That is a legitimate,
    tidy reformulation. It is NOT a cosmological polytope, a cosmohedron, or a
    derivation of 1/N_c from positive geometry. 1/N_c = 1/3 is the squared Higgs
    component of one eigenvector and stays a spectral quantity.""")
