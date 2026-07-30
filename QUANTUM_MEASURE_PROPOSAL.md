# The Born-from-Growth Quantum Measure — Proposal and Formal Core

**2026-07-30.** The missing half of the causal-set program is the quantum
measure on growth histories. The field's approach — searching for exotic
complex quantum-sequential-growth couplings — has been stuck on the axioms
(strong positivity in particular). The outside-the-box move proposed here:
COMPOSE the two structures this repository has already formalized.

    A(gamma) = sqrt(P_RS(gamma)) * exp(i S_BD(gamma)/hbar)
    D(gamma, gamma') = A(gamma) * conj A(gamma')

P_RS = the classical Rideout-Sorkin sequential-growth measure (discrete
general covariance + Bell causality: formalized in KFCausalSetSequential-
Growth / KFCausalSetBellCausality). S_BD = the Benincasa-Dowker action
(order-invariant; its mean and fluctuation calculus machine-checked in this
repo). Formal core: KFCausalQuantumMeasure.lean, 8 theorems axiom-clean.

## What is theorem (Lean)

| axiom / property | status |
|---|---|
| hermiticity | `D_hermitian` |
| STRONG positivity | `strong_positivity` — Gram identity, one page. The axiom that kills generic complex QSG couplings holds here by construction. |
| quartic sum rule I3 = 0 | `interference_sum_rule` — D generates a genuine level-2 (Sorkin) quantum measure. |
| diagonal = classical growth | `D_diagonal`, `diagonal_decomposition` — mu(A) = P(A) + interference. Born rule = diagonal; classicality = phase-averaging. |
| rank-one purity | `pairwise_purity` — |D(A,B)|^2 = mu(A) mu(B): fine-grained histories are a pure state; ALL decoherence is coarse-graining. |
| normalization is DYNAMICS | `two_history_interference` + `unitarity_quantizes` — mu(Omega)=1 forces cos(DeltaS/hbar) = 0 at a branching stage: **DeltaS in (Z+1/2) pi hbar. Unitarity quantizes the action gap** — growth couplings and hbar are pinned by consistency, not chosen. |

## Why this closes the circle sketched in the TOE synthesis

1. **Classicality with computed rates.** Decoherence of coarse-grained
   classes = equidistribution of S_BD-phases within a class. The rate is the
   action variance of this repository: Var S ~ 2 kappa^2 M(eps) N T-hat^2
   (super-Poissonian, MC-validated). Macroscopic histories decohere at a
   derived rate; microscopic ones interfere — the quantum-classical boundary
   is the mesoscale, again.
2. **Einstein's equations.** The stationary phase of sum sqrt(P) e^{iS/hbar}
   is dominated by histories extremizing S_BD — supplying precisely the
   equilibrium input of `einstein_equation`. Chain: quantum measure ->
   stationary phase -> equation of state -> G + Lambda eta = kappa T ->
   Lambda statistics from the SAME functional's fluctuations.
3. **The dichotomy reappears.** Amplitude cancellations possible (mean
   kernel Mellin zeros) vs intensity positivity unavoidable (no-self-
   averaging) is exactly off-diagonal decoherence vs strictly positive
   diagonal — the measure-theoretic shadow of the critical-line trichotomy.
4. **A new research direction: unitarity selects the dynamics.** mu(Omega)=1
   is one complex constraint per growth stage tying (t_n, S_BD, hbar)
   together. The two-history case already quantizes DeltaS. Conjecture: the
   full constraint tower fixes the sequential-growth coupling sequence in
   terms of hbar alone — the dynamics would have NO free parameters.

## Honest open items

- Cylinder-set extension to infinite histories (the repo's
  InfiniteCylinderDecoherence machinery is the natural host); sigma-additivity
  questions of quantum measures apply as usual.
- Bell causality of the COMPOSITE D as a theorem (P-factor: committed axioms;
  S-factor: past-local retarded sums — the composition argument needs the
  growth-stage bookkeeping).
- The continuum limit and whether the unitarity tower has solutions at all
  orders (if not, the proposal is falsified — it sticks its neck out).
- Relation to prior art: e^{iS_BD} sums over orders (Surya et al. MCMC) and
  complex QSG couplings exist; the specific sqrt(P)-modulus x BD-phase
  composition with strong positivity for free and the unitarity-quantization
  observation are, to our knowledge, new.
