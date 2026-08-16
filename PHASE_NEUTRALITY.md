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

CLASSICAL ANCHOR (external cross-check, exact): in lightcone
coordinates the 2D diamond order is dominance order, so E[m0] is
the classical Poisson-maxima integral E[m0] = int_0^N (1-e^{-s})/s
ds (record statistics); differentiating in ln N gives 1 - e^{-N} -
the identity drops out of a sixty-year-old computation,
independently of our derivation route.  It also gives
E[m0] -> ln N + gamma, the growth that killed the GH reading.

MECHANISM RETRACTED (same day, concentration test): the coherence
reading ("flat pasts feed sum a = 1") required CONCENTRATION of
q mod 8 near 1.  Measured: Var(q) grows ~ 2 ln N and the q mod 8
histograms are UNIFORM at every density N = 50..3200 - flat
regions are phase-RANDOM, not phase-aligned; the mean-1 identity
is exact but the mod-8 distribution carries no alignment.  The
emergent-flatness-by-coherence mechanism is DEAD as stated.

THE CORRECTED STATEMENT (stronger, and unifying): uniform q mod 8
means flat regions provide MAXIMAL OCTANT COVERAGE - and by the
166/166 feasibility closure, octant coverage IS Born feasibility.
Hence: FLAT ENSEMBLES ARE UNCONDITIONALLY BORN-FEASIBLE; the
feasibility walls (expansion bound, collapse censorship) are
CURVATURE PHENOMENA - they can only occur in non-flat ensembles
whose phase distributions are skewed.  This unifies with the
parallel-chain (rotation-cancelling, uncensored) result: quantum
obstruction requires curvature.

DIMENSION SCOPING (4D sprinkling test, run): in d = 4 flat
diamonds E[m0] ~ N^alpha with measured alpha = 0.53-0.64 and
q/m0 = 0.55-0.59 ~ alpha - the identity's power-law prediction
E[q] ~ alpha E[m0] CONFIRMS in a second regime, the charge is
boundary-sized in d > 2, and exact neutrality is a 2D-marginal
(alpha = 0) fact.  One more structure singling out d = 2 - the
only dimension where the framework has produced its quantum
sector.

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

## SUMMIT, ALGEBRAIC HALF TAKEN (same day, Lean sec. 31)

`jw_exchange` (axiom-clean): the Jordan-Wigner meter operators
chi_i = (string of width double-shifts below rank i) x (local
quarter clock at i), acting on the growth level record, satisfy
    chi_i chi_j = - chi_j chi_i   for all i != j.
The minus sign is exactly the section-30 mechanism: the later
operator's string shifts the earlier site by two width units
before its clock reads it (zeta^{2(v+2)} = -zeta^{2v}).
Sequential growth supplies the canonical ordering the JW string
requires - the structure Jordan-Wigner needs is not imposed, it
is the growth order itself.  FERMIONIC EXCHANGE STATISTICS IS NOW
A MACHINE-CHECKED CONSTRUCTION inside the Z8 meter algebra.
Honest scope: chi_i^2 = (central parity/shift-4 cocycle), not 1 -
these are fermions up to a central Z2 x Z2 twist per site
(standard generalized-JW situation); and the operators act on the
KINEMATIC level record.  THE REMAINING (dynamical) HALF,
registered: whether growth transports the string - concretely,
the sibling-swap experiment: replace the rank-i choice by a
level-shifted sibling (guaranteed to exist generically by octant
coverage), continue growth, and measure the fidelity of
string-commutation with the step isometry U = V o U_+.
