# Phase neutrality of flatness + the Clifford pair (2026-08-16)

Two derivations found by interrogating the two-integer octant
formula (octant = 1 - m0 + m1 mod 8) for further structure.

## 1. THE PHASE-NEUTRALITY IDENTITY (exact, new)

General identity (one-line proof, any dimension, any region): for
Poisson sprinklings at density N,
    E[m0 - m1]  =  d E[m0] / d ln N
- the phase charge q = m0 - m1 is the LOGARITHMIC DENSITY-
DERIVATIVE (RG flow) of the maximal-element count.  Proof:
E[m0] = N G(N) with G = int e^{-N V(x)} dx and
E[m1] = N int (N V) e^{-N V} dx; differentiate.

2D causal diamond, EXACT:  E[q] = 1 - e^{-N} -> 1, so the expected
octant exponent E[1 - m0 + m1] = e^{-N} -> 0 identically.
Verified: N = 50..3200, five densities, all within 1 sigma of
1.000 (400/400/300/300/200 trials).  The naive "q = boundary
length ~ sqrt(N)" (GHY-term) reading is REFUTED - m0 and m1 both
grow ~ ln N and cancel to exactly 1.

PHYSICS: FLAT PASTS ARE PHASE-NEUTRAL IN EXPECTATION.  The
two-integer phase charge detects deviation from flatness, not
boundary size: manifold-like caps carry (mean) zero phase
exponent, hence cos ~ +1, hence they feed the coherent constraint
(sum a = 1) maximally.  The Markov sum rule structurally FAVORS
manifoldlike growth options over crumpled ones (whose q scatters
across octants) - a candidate MECHANISM FOR EMERGENT FLATNESS
inside the double-conservation law.  In d dimensions
E[m0] ~ (ln N)^{d-1} gives E[q] ~ (d-1)(ln N)^{d-2}: near-neutral
at all d, exactly neutral-to-one in 2D.

## 2. THE FERMIONIC MINUS SIGN (Lean, section 30)

`clifford_anticommutation` (axiom-clean): the squares of the width
shift and the curvature clock anticommute, S^2 C^2 = -C^2 S^2,
because zeta^4 = e^{-i pi} = -1.  Two units of causal width
against a quarter turn of curvature phase form a genuine Clifford
(anticommuting) pair inside the Z8 meter algebra: the
characteristic minus sign of fermionic exchange is present in the
width-curvature bookkeeping itself.  (Whether meter-defects
therefore obey fermionic statistics requires an exchange
construction - registered, not claimed.)
