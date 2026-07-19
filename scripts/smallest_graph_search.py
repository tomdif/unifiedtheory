#!/usr/bin/env python3
r"""
smallest_graph_search.py

GOAL: find the smallest graph whose cosmological-polytope structure realizes the
chamber weighted geometry (vertices = J_4 spectrum, dual points = leaf-deleted
spectrum, weights = {1/N_c, (disc±√disc)/(N_c·disc)}), with edge/leaf reduction =
the N_c (Higgs) channel deletion.

Strategy: match INVARIANTS, computed exactly.

  Our object  m(z) = ∏_k(z-μ_k)/∏_i(z-λ_i):
      - 3 poles (eigenvalues λ), 2 zeros (dual points μ)
      - Herglotz / positive residues
      - residues SUM TO 1  (m decays like 1/z)

  A cosmological-polytope WAVEFUNCTION ψ_G:
      - one pole per CONNECTED SUBGRAPH of G
      - decays like 1/E_total^2  =>  residues SUM TO 0
      - canonical form of a bounded positive geometry (projective: total residue 0)

The sum-of-residues invariant (1 vs 0) is decisive and is computed below.
"""

import sympy as sp
from itertools import combinations

z = sp.symbols('z', real=True)
Nc, Ntot, disc = 3, 5, 7

# ----------------------------------------------------------------------
# 0. The chamber operator as a weighted graph
# ----------------------------------------------------------------------
b1 = sp.sqrt(sp.Rational(1,25)); b2 = sp.sqrt(sp.Rational(1,50))
J = sp.Matrix([[sp.Rational(1,3), b1, 0],
               [b1, sp.Rational(2,5), b2],
               [0, b2, sp.Rational(1,5)]])

print("=" * 72)
print("[0] J_4 is tridiagonal  =>  it is a WEIGHTED PATH GRAPH P_3 (nearest-neighbour")
print("    chain on 3 sites):   (1)──b1──(2)──b2──(3)   on-site a1,a2,a3.")
offpath = (J[0,2] == 0)
print(f"    no 1–3 coupling (J[1,3]=0): {offpath}  -> exactly the path P_3, no chord.")
assert offpath

# leaf deletion P_3 -> P_2 (delete site 1 = the N_c/Higgs channel)
minor = J[1:,1:]
mu = sorted([sp.nsimplify(sp.simplify(e)) for e in minor.eigenvals()], key=float, reverse=True)
lam = sorted([sp.nsimplify(sp.simplify(e)) for e in J.eigenvals()], key=float, reverse=True)
print("\n[0] leaf deletion P_3 → P_2 (delete site 1 / N_c channel) = the lower 2×2 block:")
print(f"    spectrum(P_2) = dual points μ = {[sp.sstr(m) for m in mu]}  ∈ ℚ(√N_c)=ℚ(√3)")
print(f"    spectrum(P_3) = vertices   λ = {[sp.sstr(l) for l in lam]}  ∈ ℚ(√disc)=ℚ(√7)")

# ----------------------------------------------------------------------
# 1. Enumerate small graphs; pole count = # connected subgraphs
# ----------------------------------------------------------------------
def connected_subgraphs(n, edges):
    """count nonempty vertex subsets that induce a connected subgraph."""
    adj = {v: set() for v in range(n)}
    for (a, b) in edges:
        adj[a].add(b); adj[b].add(a)
    count = 0
    for r in range(1, n + 1):
        for S in combinations(range(n), r):
            Sset = set(S)
            # BFS connectivity within S
            seen = {S[0]}; stack = [S[0]]
            while stack:
                u = stack.pop()
                for w in adj[u] & Sset:
                    if w not in seen:
                        seen.add(w); stack.append(w)
            if seen == Sset:
                count += 1
    return count

graphs = [
    ("single vertex      ", 1, []),
    ("single edge  P_2    ", 2, [(0,1)]),
    ("path        P_3     ", 3, [(0,1),(1,2)]),
    ("triangle    C_3     ", 3, [(0,1),(1,2),(0,2)]),
]
print("\n[1] cosmological-polytope pole count (= # connected subgraphs):")
print(f"    {'graph':<20} {'#poles(ψ_G)':>12}")
for name, n, E in graphs:
    print(f"    {name:<20} {connected_subgraphs(n, E):>12}")
print("    our object has 3 poles.  The ONLY graph with exactly 3 connected")
print("    subgraphs is the SINGLE EDGE P_2 — whose cosmological polytope is the")
print("    2-simplex (a triangle in P^2), 3 facets ↔ our 3 boundaries.")

# ----------------------------------------------------------------------
# 2. The decisive invariant: sum of residues (normalization)
# ----------------------------------------------------------------------
print("\n[2] sum-of-residues invariant (THE decisive test):")

# (a) our object m(z): numerator degree 2 (the two dual points)
m = sp.prod([z - x for x in mu]) / sp.prod([z - x for x in lam])
res_m = [sp.simplify(sp.residue(m, z, l)) for l in lam]
sum_m = sp.simplify(sum(res_m))
print(f"    m(z)=∏(z-μ)/∏(z-λ): residues {[sp.sstr(r) for r in res_m]}")
print(f"        Σ residues = {sum_m}   (numerator degree 2 = 2 dual points → decays 1/z)")
assert sum_m == 1

# (b) bare simplex / cosmological canonical form: CONSTANT numerator
bare = 1 / sp.prod([z - x for x in lam])
sum_bare = sp.simplify(sum(sp.residue(bare, z, l) for l in lam))
print(f"    bare 3-facet simplex form 1/∏(z-λ) (const numerator): Σ residues = {sum_bare}")
assert sum_bare == 0

# (c) single-edge wavefunction shape: numerator degree 1
edge_like = (z - sp.Rational(1,4)) / sp.prod([z - x for x in lam])   # any degree-1 numerator
sum_edge = sp.simplify(sum(sp.residue(edge_like, z, l) for l in lam))
print(f"    single-edge ψ shape (numerator degree 1): Σ residues = {sum_edge}")
assert sum_edge == 0

print("""
    READ:
      • A bounded cosmological polytope's canonical form is PROJECTIVE: total
        residue 0 (numerator degree < #facets). Bare simplex and single-edge ψ
        both give Σ res = 0.
      • Our m(z) has Σ res = 1. The extra +1 comes from numerator degree 2 —
        i.e. from the TWO DUAL POINTS μ. They are exactly the data that promotes
        the bare simplex (Σ=0) to a PROBABILITY MEASURE (Σ=1).
""")

# ----------------------------------------------------------------------
# 3. The dual points ARE the weighting (cosmohedron upgrade)
# ----------------------------------------------------------------------
print("[3] the 2 dual points = the weighting that turns the simplex into a")
print("    weighted positive geometry (cosmohedron-style):")
print("      facets (3 eigenvalues)      -> bare simplex,    Σ res = 0")
print("      + 2 zeros (leaf-deleted μ)  -> probability form, Σ res = 1")
print("    and the residues are forced atomic:")
w_target = {0: sp.Rational(1,3), 1: (7+sp.sqrt(7))/21, 2: (7-sp.sqrt(7))/21}
for i, l in enumerate(lam):
    ok = sp.simplify(res_m[i] - w_target[i]) == 0
    print(f"      Res_{{λ_{i+1}}} = {sp.sstr(sp.nsimplify(res_m[i])):>16}   atomic? {ok}")
    assert ok
print("      top facet residue = 1/3 = 1/N_c  (the Higgs residue).")

# ----------------------------------------------------------------------
# 4. Verdict
# ----------------------------------------------------------------------
print("=" * 72)
print("VERDICT — the smallest graph")
print("=" * 72)
print("""
SMALLEST GRAPH (operator graph):  the PATH P_3  —  J_4 is literally the weighted
nearest-neighbour chain (1)–(2)–(3); the N_c/Higgs channel deletion is leaf
deletion P_3 → P_2, and spectrum(P_2) = the two dual points μ.

SMALLEST COSMOLOGICAL BUILDING BLOCK:  the SINGLE EDGE P_2  —  the only graph with
exactly 3 connected subgraphs, whose cosmological polytope is the 2-simplex
(triangle); its 3 facets ↔ the 3 chamber eigenvalues / boundaries.

WHY IT MUST BE THE *WEIGHTED* (cosmohedron) FORM, NOT A BARE ψ_G:
  the sum-of-residues invariant is 1 for our object but 0 for every bounded
  cosmological-polytope canonical form. The deficit is supplied precisely by the
  two dual points μ (the leaf-deleted P_2 spectrum), which raise the numerator to
  degree 2 and normalize the form to a probability measure. So:

      chamber geometry  =  (single-edge cosmological simplex: 3 facets = λ)
                           WEIGHTED BY the reduced-graph spectrum (P_2 = μ).

  This is exactly the Benincasa–Dian weighted-cosmological-polytope pattern, and it
  is forced to be atomic: facets ∈ ℚ(√disc), weights via μ ∈ ℚ(√N_c), top residue
  = 1/N_c.

STILL OPEN (next concrete step): exhibit a convex cosmohedron C whose facets sit at
λ and whose weighting section sits at μ, so the residues come out as honest
sub-polytope volumes. The graph is now fixed (P_3 chain / P_2 block); what remains
is the explicit convex body. That is a finite, bounded construction.
""")
