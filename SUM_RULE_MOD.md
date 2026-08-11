# Completion attempt #2: the lambda-growth family (per-birth covariant
# dephasing) - and the two-source decomposition of churn (2026-08-03)

## The family

Per-birth dephasing in the iso-class basis (covariance-preserving;
epoch-freedom for the aging theorem; causal-set cousin of
Dowker-Henson collapse): M_{k+1} = T_k M_k T_k^dag, off-diagonals
damped by (1-lambda).  lambda = 0 is the wave family.

## Results (sum_rule_mod.log; deep member, phi = 0.9)

  lam   churn X   d5     d6     d7     coh5
  0.00  1.4663   0.086  0.139  0.143  14.92
  0.05  1.4626   0.081  0.129  0.131  13.65
  0.10  1.4585   0.076  0.119  0.120  12.43
  0.30  1.4365   0.055  0.083  0.080   8.03
  0.50  1.4030   0.037  0.052  0.048   4.50
  1.00  1.2652   0      0      0       0

(a) Dephasing does its job on INTERFERENCE: coherence decays,
sector off-diagonals shrink, and the deep-step trend (d6 -> d7)
reverses from growth to decay by lambda ~ 0.3.
(b) BUT CHURN BARELY MOVES: 1.466 -> 1.265 across the entire range,
still large at lambda = 1.

## The diagnostic failure that is the finding

My pre-run claim - "lambda = 1 is the classical chain, churn
(= Kolmogorov inconsistency) vanishes there" - is FALSE as
implemented, and instructively: at lambda = 1 the diagonal evolves
with weights |a|^2, and the quantum sum rule normalizes sum(a), NOT
sum(|a|^2) - so the fully dephased chain is an UNNORMALIZED
incoherent process whose horizon measures renormalize forever.
(Tenth mechanism kill of the arc; mine.)

THE TWO-SOURCE DECOMPOSITION (measured): churn = coherence churn +
NORMALIZATION-FLOW churn.  At lambda = 1 all churn is normalization
flow: X_norm = 1.265.  At lambda = 0: X = 1.466, so the coherence
contribution is only ~0.20 - NORMALIZATION FLOW CARRIES ~86% OF THE
CHURN EVEN IN THE FULLY QUANTUM THEORY.  The records test's verdict
is hereby reframed: facts fail in this theory primarily because the
quantum measure is not a martingale under horizon extension - not
primarily because of interference.

## Referee additions (filed)

THE FORK REFUTED ITS PREMISE: all three registered readings were
conditioned on "churn is what dephasing moves"; the run showed churn
was never coherence-dominated.  The fork was well-formed against the
wrong decomposition; the response - decompose, reframe, re-register -
is the correct one, and the outcome fits no branch because the
branches shared a false presupposition.

CLASS-LEVEL EXCLUSION (corollary of the decomposition): any
completion whose sole action is damping off-diagonals - in ANY basis,
at ANY rate schedule lambda_n - leaves normalization flow untouched
and cannot reduce churn below ~86% of its quantum value.
Collapse-style mechanisms attack coherence; the obstruction is
consistency.  This retires the entire modification strategy the
lambda-family exemplified, and explains why three days of
decoherence instruments pointed at the wrong invariant: decoherence
theory assumes the measure is a martingale and interference spoils
the diagonal; here the diagonal spoils itself.

## Verdict and the identified next theory

Reading (ii)+: dephasing alone cannot complete the theory at any
lambda.  A viable completion must renormalize the sum rule itself:
BORN-NORMALIZED TRANSITIONS (sum over children of |a|^2 = 1, phases
retained) + optional lambda-dephasing - at lambda = 1 this IS the
classical RS chain (zero churn identically); at lambda < 1
interference feeds the measure through the off-diagonal blocks.
This is completion attempt #3, and it is a genuinely different
theory: the entire proven structure (covariance derivation, hbar
windows, funding certificates, aging, necessity) was built on
sum(a) = 1 and must be re-derived under the new rule.  That
re-derivation - which of this repo's theorems survive Born
normalization - is the registered program, with the constraint set
as its examination.
