/-
  LayerB/HolevoDiagonalDischarge.lean
  ────────────────────────────────────

  **Unconditional Holevo bound for DIAGONAL (commuting) ensembles.**

  This file specialises the quantum Holevo machinery of
  `HolevoBoundQuantum.lean` to the case where every state in the
  ensemble is diagonal in a common basis (the canonical basis
  `Fin n`).  In that regime the Holevo χ-quantity collapses to the
  classical Shannon mutual information of a joint distribution on
  `(label, basis)`, and the Holevo bound becomes the classical
  data-processing inequality for a stochastic post-measurement
  channel.

  The deep operator-theoretic content of the general Holevo bound
  (Lindblad–Uhlmann monotonicity) is *unnecessary* here, because for
  commuting states the operator log behaves classically.  The CFC
  acts entrywise on a diagonal matrix
  (`CFCDiagonalDischarge.cfcOnDiagonalIsEntrywise_real`), reducing
  every spectral identity to a finite scalar sum.

  WHAT IS PROVEN (no `sorry`, no custom `axiom`):
    1. `DiagonalEnsemble n α`           — bundle:
                                            • label weights p_a,
                                            • per-label diagonal entries.
    2. `toQuantum E`                    — embed as `QuantumEnsemble α n`.
    3. `toClassical E`                  — embed as
                                            `ClassicalEnsemble α (Fin n)`.
    4. `avgClassical E`                 — marginal probability vector.
    5. `ensembleAverageQuantum_toQuantum_M_eq`
                                          — ρ̄.M = diag(avgClassical E).M.
    6. `vonNeumannEntropy_diagonal_eq_shannon`
                                          — S(diag P) = H(P).
    7. `holevoChiQuantum_toQuantum_eq_mutualInfo`
                                          — χ_quantum(toQuantum E)
                                              = I(toClassical E).
    8. `HolevoUmegakiForm_diagonal`     — discharge at diagonal embedding.
    9. `diagonalProbReader ρ`           — read out the diagonal of ρ
                                          as a probability vector
                                          (uniform fallback for non-
                                          diagonal ρ).
   10. `stochasticInducedMeasurement T` — `QuantumMeasurement` from a
                                          column-stochastic channel.
   11. `diagonalMeasurement_acts_as_stochastic`
                                          — the action on a diagonal
                                            state is `T.push P`.
   12. `holevo_bound_diagonal_unconditional`
                                          — UNCONDITIONAL bound:
                                            post-measurement classical
                                            mutual information
                                            ≤ χ_quantum at the diagonal
                                            embedding.

  Load-bearing dependencies:
    • `HolevoBoundQuantum`              `QuantumEnsemble` /
                                          `HolevoUmegakiForm` /
                                          `QuantumMeasurement`.
    • `HolevoUmegakiDischarge`          unconditional
                                          `holevoUmegakiForm_holds`.
    • `DiagonalDensityMatrix`           diagonal embedding.
    • `CFCDiagonalDischarge`            unconditional
                                          `cfcOnDiagonalIsEntrywise_real`.
    • `OperatorEntropy`                 `vonNeumannEntropy_eq_neg_re_trace_xlogx`.
    • `ClassicalEnsemble`               `mutualInformation` + classical DPI.
    • `ClassicalChannelDPI`             `StochasticMatrix`, `klDivergence_contracts_under_stochastic_of_logsum`.
    • `LogSumInequality`                unconditional `logSumInequality_holds`.
-/

import UnifiedTheory.LayerB.HolevoBoundQuantum
import UnifiedTheory.LayerB.HolevoUmegakiDischarge
import UnifiedTheory.LayerB.DiagonalDensityMatrix
import UnifiedTheory.LayerB.CFCDiagonalDischarge
import UnifiedTheory.LayerB.ClassicalEnsemble
import UnifiedTheory.LayerB.LogSumInequality

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.HolevoDiagonalDischarge

open Matrix Complex
open scoped ComplexOrder
open UnifiedTheory.LayerB.RobertsonSchrodinger
open UnifiedTheory.LayerB.SpectralFC
open UnifiedTheory.LayerB.OperatorEntropy
open UnifiedTheory.LayerB.UmegakiRelativeEntropy
open UnifiedTheory.LayerB.ClassicalEntropy
open UnifiedTheory.LayerB.ClassicalEntropy.ProbabilityVector
open UnifiedTheory.LayerB.ClassicalRelativeEntropy
open UnifiedTheory.LayerB.ClassicalChannelDPI
open UnifiedTheory.LayerB.LogSumInequality
open UnifiedTheory.LayerB.DiagonalDensityMatrix
open UnifiedTheory.LayerB.CFCDiagonalDischarge
open UnifiedTheory.LayerB.HolevoBoundQuantum
open UnifiedTheory.LayerB.HolevoUmegakiDischarge
open UnifiedTheory.LayerB.Ensemble

variable {n : ℕ} {α β : Type*} [Fintype α] [Fintype β]

/-! ## 1. The DiagonalEnsemble structure -/

/-- A **diagonal ensemble** on an `n`-level system labelled by `α`:
    a probability over labels together with, for each label `a`, a
    probability vector on `Fin n` representing the diagonal entries
    of the state `ρ_a` in the canonical basis.

    Embeds into both a `QuantumEnsemble α n` (via
    `diagonalDensityMatrix`) and a `ClassicalEnsemble α (Fin n)`. -/
structure DiagonalEnsemble (n : ℕ) (α : Type*) [Fintype α] where
  /-- Label weights `p(a)`. -/
  weight : ProbabilityVector α
  /-- Diagonal entries of `ρ_a` for each label, packaged as a
      probability vector on `Fin n`. -/
  diag : α → ProbabilityVector (Fin n)

namespace DiagonalEnsemble

/-! ## 2. Embedding into a `QuantumEnsemble` -/

/-- Embed as an honest `QuantumEnsemble α n` via diagonal embedding. -/
noncomputable def toQuantum (E : DiagonalEnsemble n α) :
    QuantumEnsemble α n where
  weight := E.weight
  state a := diagonalDensityMatrix (E.diag a)

@[simp]
theorem toQuantum_weight (E : DiagonalEnsemble n α) :
    E.toQuantum.weight = E.weight := rfl

@[simp]
theorem toQuantum_state (E : DiagonalEnsemble n α) (a : α) :
    E.toQuantum.state a = diagonalDensityMatrix (E.diag a) := rfl

/-! ## 3. The classical-ensemble counterpart -/

/-- View as a classical ensemble: same weights, diagonal entries as states. -/
noncomputable def toClassical (E : DiagonalEnsemble n α) :
    ClassicalEnsemble α (Fin n) where
  weight := E.weight
  state a := E.diag a

@[simp]
theorem toClassical_weight (E : DiagonalEnsemble n α) :
    E.toClassical.weight = E.weight := rfl

@[simp]
theorem toClassical_state (E : DiagonalEnsemble n α) (a : α) :
    E.toClassical.state a = E.diag a := rfl

/-! ## 4. The marginal probability on `Fin n` -/

/-- The marginal probability vector on `Fin n`. -/
noncomputable def avgClassical (E : DiagonalEnsemble n α) :
    ProbabilityVector (Fin n) :=
  ensembleAverage E.toClassical

@[simp]
theorem avgClassical_apply (E : DiagonalEnsemble n α) (k : Fin n) :
    (E.avgClassical).p k = ∑ a, E.weight.p a * (E.diag a).p k := rfl

@[simp]
theorem ensembleAverage_toClassical (E : DiagonalEnsemble n α) :
    ensembleAverage E.toClassical = E.avgClassical := rfl

/-! ## 5. The ensemble average's `M`-field is itself diagonal -/

/-- **Key structural identity** (M-field level).  The ensemble
    average of the diagonal embedding has the same underlying matrix
    as the diagonal embedding of the marginal:

      `(ensembleAverageQuantum (toQuantum E)).M
         = (diagonalDensityMatrix (avgClassical E)).M`. -/
theorem ensembleAverageQuantum_toQuantum_M_eq
    (E : DiagonalEnsemble n α) :
    (ensembleAverageQuantum E.toQuantum).M
      = (diagonalDensityMatrix (avgClassical E)).M := by
  rw [ensembleAverageQuantum_M]
  -- Unfold toQuantum to expose `diagonalDensityMatrix`.
  simp only [toQuantum_weight, toQuantum_state]
  ext i j
  rw [Matrix.sum_apply]
  by_cases hij : i = j
  · subst hij
    -- Diagonal entries.
    rw [diagonalDensityMatrix_apply_eq]
    -- LHS = ∑ a, ((w_a : ℂ) • diagonalDensityMatrix (diag a).M) i i
    --     = ∑ a, (w_a : ℂ) * (P_a.p i : ℂ)
    --     = ((∑ a, w_a * P_a.p i : ℝ) : ℂ)
    --     = ((avgClassical E).p i : ℂ)
    rw [show ((avgClassical E).p i : ℂ)
            = ((∑ a, E.weight.p a * (E.diag a).p i : ℝ) : ℂ) from by
          rw [avgClassical_apply]]
    have h_each : ∀ a ∈ Finset.univ,
        (((E.weight.p a : ℂ)) • (diagonalDensityMatrix (E.diag a)).M) i i
          = ((E.weight.p a : ℂ)) * ((E.diag a).p i : ℂ) := by
      intro a _
      change ((E.weight.p a : ℂ)) * ((diagonalDensityMatrix (E.diag a)).M i i)
              = ((E.weight.p a : ℂ)) * ((E.diag a).p i : ℂ)
      rw [diagonalDensityMatrix_apply_eq]
    rw [Finset.sum_congr rfl h_each]
    push_cast
    rfl
  · -- Off-diagonal entries.
    rw [diagonalDensityMatrix_apply_ne _ hij]
    have h_each : ∀ a ∈ Finset.univ,
        (((E.weight.p a : ℂ)) • (diagonalDensityMatrix (E.diag a)).M) i j
          = (0 : ℂ) := by
      intro a _
      change ((E.weight.p a : ℂ)) * ((diagonalDensityMatrix (E.diag a)).M i j) = 0
      rw [diagonalDensityMatrix_apply_ne _ hij, mul_zero]
    rw [Finset.sum_congr rfl h_each, Finset.sum_const_zero]

/-! ## 6. von Neumann entropy of a diagonal state = Shannon entropy -/

/-- **vN entropy of a diagonal density matrix equals Shannon entropy.**
    Proof: use the trace form
    `vN(ρ) = -((operatorXLogX ρ).trace.re)`, the fact that
    `operatorXLogX = cfc (x · log x)`, and the unconditional
    `cfcOnDiagonalIsEntrywise_real` discharge. -/
theorem vonNeumannEntropy_diagonal_eq_shannon
    (P : ProbabilityVector (Fin n)) :
    vonNeumannEntropy (diagonalDensityMatrix P) = shannonEntropy P := by
  rw [vonNeumannEntropy_eq_neg_re_trace_xlogx]
  unfold operatorXLogX cfcρ
  have h_ρM : (diagonalDensityMatrix P).M
                = Matrix.diagonal (fun i => ((P.p i : ℝ) : ℂ)) := rfl
  rw [h_ρM, cfcOnDiagonalIsEntrywise_real n (fun x => x * Real.log x) P.p,
      Matrix.trace_diagonal, Complex.re_sum]
  have h_each : ∀ i,
      (((P.p i * Real.log (P.p i) : ℝ) : ℂ)).re
        = P.p i * Real.log (P.p i) := by
    intro i; exact Complex.ofReal_re _
  simp_rw [h_each]
  -- Goal: -∑ x, P.p x * Real.log (P.p x) = shannonEntropy P
  rfl

/-! ## 7. Holevo χ at the diagonal embedding = classical mutual information -/

/-- **Diagonal Holevo χ = classical mutual information.**

    For a diagonal ensemble `E`:

      `holevoChiQuantum (toQuantum E)  =  mutualInformation (toClassical E)`. -/
theorem holevoChiQuantum_toQuantum_eq_mutualInfo
    (E : DiagonalEnsemble n α) :
    holevoChiQuantum E.toQuantum
      = mutualInformation E.toClassical := by
  unfold holevoChiQuantum
  -- Step (a): rewrite vN entropy of ρ̄ as Shannon entropy of avgClassical E.
  have h_avg :
      vonNeumannEntropy (ensembleAverageQuantum E.toQuantum)
        = shannonEntropy (avgClassical E) := by
    have hM := ensembleAverageQuantum_toQuantum_M_eq E
    rw [vonNeumannEntropy_eq_neg_re_trace_xlogx,
        ← vonNeumannEntropy_diagonal_eq_shannon (avgClassical E),
        vonNeumannEntropy_eq_neg_re_trace_xlogx]
    -- Both sides are -((operatorXLogX ρ).trace.re); reduce to the M-equality.
    congr 1
    congr 1
    congr 1
    unfold operatorXLogX cfcρ
    rw [hM]
  have h_per_a : ∀ a,
      vonNeumannEntropy (E.toQuantum.state a) = shannonEntropy (E.diag a) := by
    intro a; rw [toQuantum_state]
    exact vonNeumannEntropy_diagonal_eq_shannon _
  rw [h_avg]
  have h_sum :
      ∑ a, E.toQuantum.weight.p a * vonNeumannEntropy (E.toQuantum.state a)
        = ∑ a, E.weight.p a * shannonEntropy (E.diag a) := by
    apply Finset.sum_congr rfl
    intro a _
    rw [toQuantum_weight, h_per_a]
  rw [h_sum]
  -- Now: shannonEntropy (avgClassical E) - ∑ a, w_a * shannonEntropy (diag a)
  --       = mutualInformation E.toClassical.
  unfold mutualInformation
  -- Rewrite shannonEntropy (avgClassical E) using bilinearity in `(diag_a)`.
  have h_shannon_avg :
      shannonEntropy (avgClassical E)
        = - ∑ a, E.weight.p a *
                  ∑ k, (E.diag a).p k * Real.log ((avgClassical E).p k) := by
    unfold shannonEntropy
    congr 1
    rw [show (∑ k, (avgClassical E).p k * Real.log ((avgClassical E).p k))
          = ∑ k, (∑ a, E.weight.p a * (E.diag a).p k)
                  * Real.log ((avgClassical E).p k) from by
        apply Finset.sum_congr rfl; intro k _; rw [avgClassical_apply]]
    rw [show (∑ k, (∑ a, E.weight.p a * (E.diag a).p k)
              * Real.log ((avgClassical E).p k))
          = ∑ k, ∑ a, E.weight.p a * (E.diag a).p k
                  * Real.log ((avgClassical E).p k) from by
        apply Finset.sum_congr rfl; intro k _; rw [Finset.sum_mul]]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have h_shannon_per :
      ∑ a, E.weight.p a * shannonEntropy (E.diag a)
        = - ∑ a, E.weight.p a *
                  ∑ k, (E.diag a).p k * Real.log ((E.diag a).p k) := by
    unfold shannonEntropy
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro a _
    rw [mul_neg]
  rw [h_shannon_avg, h_shannon_per, sub_neg_eq_add]
  -- Combine sums and match termwise.
  rw [show (-∑ a, E.weight.p a *
                    ∑ k, (E.diag a).p k * Real.log ((avgClassical E).p k))
          + ∑ a, E.weight.p a *
                    ∑ k, (E.diag a).p k * Real.log ((E.diag a).p k)
          = ∑ a, E.weight.p a *
              (∑ k, (E.diag a).p k * Real.log ((E.diag a).p k)
                - ∑ k, (E.diag a).p k * Real.log ((avgClassical E).p k)) from by
      rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro a _
      ring]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hwa : E.weight.p a = 0
  · -- weight 0: both sides vanish.
    change E.weight.p a * _ = E.toClassical.weight.p a * _
    rw [show E.toClassical.weight.p a = E.weight.p a from rfl, hwa, zero_mul, zero_mul]
  · have hwa_pos : 0 < E.weight.p a :=
      lt_of_le_of_ne (E.weight.nonneg a) (Ne.symm hwa)
    -- Match weights and reduce to the per-state identity inside.
    change E.weight.p a * _ = E.toClassical.weight.p a * _
    rw [show E.toClassical.weight.p a = E.weight.p a from rfl]
    congr 1
    -- ∑_k (diag a).p k log (diag a).p k − ∑_k (diag a).p k log (avg).p k
    --   = klDivergence (diag a) (avgClassical E)
    -- Note: ensembleAverage E.toClassical = avgClassical E definitionally.
    change _ = klDivergence (E.diag a) (ensembleAverage E.toClassical)
    rw [show ensembleAverage E.toClassical = avgClassical E from rfl]
    unfold klDivergence
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hpk : (E.diag a).p k = 0
    · rw [hpk, zero_mul, zero_mul, sub_zero]
      change (0 : ℝ) = klTerm 0 _
      rw [klTerm_zero_left]
    · have hqk_pos : 0 < (avgClassical E).p k := by
        rw [avgClassical_apply]
        have h_summand : 0 < E.weight.p a * (E.diag a).p k := by
          have hpa_pos : 0 < (E.diag a).p k :=
            lt_of_le_of_ne ((E.diag a).nonneg k) (Ne.symm hpk)
          exact mul_pos hwa_pos hpa_pos
        have h_summands_nn : ∀ a' ∈ Finset.univ,
            0 ≤ E.weight.p a' * (E.diag a').p k := fun a' _ =>
          mul_nonneg (E.weight.nonneg a') ((E.diag a').nonneg k)
        exact Finset.sum_pos' h_summands_nn ⟨a, Finset.mem_univ _, h_summand⟩
      have hqk : (avgClassical E).p k ≠ 0 := ne_of_gt hqk_pos
      rw [klTerm_of_ne_zero hpk, Real.log_div hpk hqk]
      ring

/-! ## 8. `HolevoUmegakiForm` at the diagonal embedding -/

/-- **The `HolevoUmegakiForm` hypothesis holds for all ensembles**
    (in particular for the diagonal embedding).  This is immediate
    from the unconditional discharge `holevoUmegakiForm_holds`
    proved in `HolevoUmegakiDischarge.lean`. -/
theorem HolevoUmegakiForm_diagonal :
    HolevoUmegakiForm α n :=
  holevoUmegakiForm_holds α n

end DiagonalEnsemble

/-! ## 9. Diagonal-reader and stochastic-induced measurements

For any `ComplexDensityMatrix n`, the diagonal entry `ρ.M k k` lies
in the non-negative cone of `ℂ` (since ρ is PSD), so its real part
is non-negative and its imaginary part is zero, and the sum of real
parts over `k` equals `Re(trace ρ) = 1`.  Hence the diagonal is
itself a probability vector.  This is a load-bearing fact: it
eliminates the `n = 0` / zero-sum edge cases entirely. -/

/-- Diagonal entries of a complex density matrix are real and
    non-negative.  Consequence of
    `posSemidef_of_ComplexDensityMatrix` and
    `PosSemidef.diag_nonneg` (in the partial order on ℂ, where
    `0 ≤ z ↔ z.re ≥ 0 ∧ z.im = 0`). -/
theorem ComplexDensityMatrix_diag_re_nonneg
    (ρ : ComplexDensityMatrix n) (k : Fin n) :
    0 ≤ (ρ.M k k).re := by
  have hPSD : ρ.M.PosSemidef := posSemidef_of_ComplexDensityMatrix ρ
  have h_le : (0 : ℂ) ≤ ρ.M k k := hPSD.diag_nonneg
  exact (Complex.nonneg_iff.mp h_le).1

/-- The sum of the real parts of the diagonal of a complex density
    matrix is `1` (equals `Re(trace ρ) = Re(1) = 1`). -/
theorem ComplexDensityMatrix_diag_re_sum_eq_one
    (ρ : ComplexDensityMatrix n) :
    (∑ k, (ρ.M k k).re) = 1 := by
  -- trace ρ.M = ∑ k, ρ.M k k = 1; take real parts.
  have h := ρ.hTrace
  -- h : ρ.M.trace = 1; trace = ∑ k, M k k; both sides ∈ ℂ.
  have h_tr : ρ.M.trace = ∑ k, ρ.M k k := by
    rw [Matrix.trace]; rfl
  have h_eq : ∑ k, ρ.M k k = (1 : ℂ) := by rw [← h_tr]; exact h
  have h_re : (∑ k, ρ.M k k).re = (1 : ℂ).re := by rw [h_eq]
  rwa [Complex.re_sum, Complex.one_re] at h_re

/-- Read the diagonal of `ρ` as a probability vector.  Because the
    diagonal of any PSD matrix is non-negative and the trace is 1,
    we get a valid probability vector with no fallback needed. -/
noncomputable def diagonalProbReader
    (ρ : ComplexDensityMatrix n) : ProbabilityVector (Fin n) where
  p k := (ρ.M k k).re
  nonneg k := ComplexDensityMatrix_diag_re_nonneg ρ k
  sum_one := ComplexDensityMatrix_diag_re_sum_eq_one ρ

@[simp]
theorem diagonalProbReader_apply
    (ρ : ComplexDensityMatrix n) (k : Fin n) :
    (diagonalProbReader ρ).p k = (ρ.M k k).re := rfl

/-- A probability vector is determined by its `p` field
    (extensionality lemma). -/
theorem probabilityVector_ext {α : Type*} [Fintype α]
    (P Q : ProbabilityVector α) (h : ∀ i, P.p i = Q.p i) : P = Q := by
  cases P; cases Q; congr 1; funext i; exact h i

/-- Reading the diagonal of `diagonalDensityMatrix P` gives back `P`. -/
theorem diagonalProbReader_of_diagonal
    (P : ProbabilityVector (Fin n)) :
    diagonalProbReader (diagonalDensityMatrix P) = P := by
  apply probabilityVector_ext
  intro k
  change ((diagonalDensityMatrix P).M k k).re = P.p k
  rw [diagonalDensityMatrix_apply_eq, Complex.ofReal_re]

/-- Two density matrices with the same `M` field have the same
    `diagonalProbReader` output. -/
theorem diagonalProbReader_congr
    (ρ σ : ComplexDensityMatrix n) (hM : ρ.M = σ.M) :
    diagonalProbReader ρ = diagonalProbReader σ := by
  apply probabilityVector_ext
  intro k
  change (ρ.M k k).re = (σ.M k k).re
  rw [hM]

/-- A **stochastic-induced quantum measurement**: a column-stochastic
    matrix `T : StochasticMatrix (Fin n) β` (a classical channel from
    basis index to outcome), packaged as a `QuantumMeasurement n β`
    by reading the diagonal of the input state and pushing it
    through `T`. -/
noncomputable def stochasticInducedMeasurement
    (T : StochasticMatrix (Fin n) β) :
    QuantumMeasurement n β where
  apply ρ := T.push (diagonalProbReader ρ)

@[simp]
theorem stochasticInducedMeasurement_apply
    (T : StochasticMatrix (Fin n) β) (ρ : ComplexDensityMatrix n) :
    (stochasticInducedMeasurement T).apply ρ = T.push (diagonalProbReader ρ) :=
  rfl

/-! ## 10. Measurement on a diagonal state = classical pushforward -/

/-- **Key compatibility lemma.**  Applying the stochastic-induced
    measurement to a diagonal density matrix gives exactly the
    classical pushforward of its diagonal probability vector. -/
theorem diagonalMeasurement_acts_as_stochastic
    (T : StochasticMatrix (Fin n) β) (P : ProbabilityVector (Fin n)) :
    (stochasticInducedMeasurement T).apply (diagonalDensityMatrix P)
      = T.push P := by
  rw [stochasticInducedMeasurement_apply, diagonalProbReader_of_diagonal]

/-! ## 11. The UNCONDITIONAL diagonal Holevo bound -/

/-- **UNCONDITIONAL DIAGONAL HOLEVO BOUND.**  For any diagonal
    ensemble `E` and any stochastic-induced quantum measurement
    (a classical post-processing channel `T` on the basis), the
    classical mutual information of the post-measurement ensemble
    is bounded above by the Holevo χ-quantity of the diagonal
    embedding:

      `postMeasurementMutualInformation (toQuantum E)
                                       (stochasticInducedMeasurement T)
         ≤ holevoChiQuantum (toQuantum E)`.

    Equivalently, the classical Holevo bound holds for diagonal
    ensembles WITHOUT any Lindblad–Uhlmann monotonicity hypothesis.

    Proof:
      • χ_quantum(toQuantum E) = I(toClassical E)
        [`holevoChiQuantum_toQuantum_eq_mutualInfo`].
      • mapStates(toClassical E, T) is the classical ensemble of
        post-measurement distributions, and classical DPI gives
        `I(mapStates) ≤ I(toClassical E)`
        [`mutualInformation_contracts_under_stochastic`].
      • postMeasurementMutualInformation unfolds to the weighted
        sum of KL divergences of T.push (diag a) to T.push
        (avgClassical E), which is exactly the mutualInformation
        of mapStates (after rewriting the average via the
        stochastic-pushforward / ensemble-average commutativity). -/
theorem holevo_bound_diagonal_unconditional
    (E : DiagonalEnsemble n α) (T : StochasticMatrix (Fin n) β) :
    postMeasurementMutualInformation E.toQuantum
                                     (stochasticInducedMeasurement T)
      ≤ holevoChiQuantum E.toQuantum := by
  -- Rewrite χ_quantum in classical mutual-information form.
  rw [DiagonalEnsemble.holevoChiQuantum_toQuantum_eq_mutualInfo E]
  unfold postMeasurementMutualInformation
  -- Replace M(ρ_a) and M(ρ̄) by classical pushforwards.
  have h_M_state : ∀ a,
      (stochasticInducedMeasurement T).apply (E.toQuantum.state a)
        = T.push (E.diag a) := by
    intro a
    rw [DiagonalEnsemble.toQuantum_state]
    exact diagonalMeasurement_acts_as_stochastic T (E.diag a)
  have h_M_avg :
      (stochasticInducedMeasurement T).apply
          (ensembleAverageQuantum E.toQuantum)
        = T.push (E.avgClassical) := by
    rw [stochasticInducedMeasurement_apply]
    -- The diagonal reader of ρ̄ equals that of `diagonalDensityMatrix (avgClassical E)`
    -- by the M-equality, which then equals avgClassical E.
    have hM := DiagonalEnsemble.ensembleAverageQuantum_toQuantum_M_eq E
    rw [diagonalProbReader_congr _ _ hM, diagonalProbReader_of_diagonal]
  have h_sum_rewrite :
      ∑ a, E.toQuantum.weight.p a *
            klDivergence
              ((stochasticInducedMeasurement T).apply (E.toQuantum.state a))
              ((stochasticInducedMeasurement T).apply
                (ensembleAverageQuantum E.toQuantum))
        = ∑ a, E.weight.p a *
            klDivergence (T.push (E.diag a)) (T.push (E.avgClassical)) := by
    apply Finset.sum_congr rfl
    intro a _
    rw [DiagonalEnsemble.toQuantum_weight, h_M_state, h_M_avg]
  rw [h_sum_rewrite]
  -- Now compare to mutualInformation E.toClassical via classical DPI per summand.
  unfold mutualInformation
  apply Finset.sum_le_sum
  intro a _
  change E.weight.p a * _ ≤ E.toClassical.weight.p a * _
  rw [show E.toClassical.weight.p a = E.weight.p a from rfl]
  by_cases hwa : E.weight.p a = 0
  · rw [hwa, zero_mul, zero_mul]
  · have hwa_nn : 0 ≤ E.weight.p a := E.weight.nonneg a
    have hwa_pos : 0 < E.weight.p a :=
      lt_of_le_of_ne hwa_nn (Ne.symm hwa)
    have h_ac : IsAbsolutelyContinuous (E.diag a) (E.avgClassical) := by
      change IsAbsolutelyContinuous (E.toClassical.state a)
                                     (ensembleAverage E.toClassical)
      exact state_ac_average_of_weight_pos E.toClassical hwa_pos
    apply mul_le_mul_of_nonneg_left _ hwa_nn
    -- Replace `ensembleAverage E.toClassical` by `E.avgClassical`.
    change klDivergence (T.push (E.diag a)) (T.push E.avgClassical)
            ≤ klDivergence (E.toClassical.state a) (ensembleAverage E.toClassical)
    rw [show E.toClassical.state a = E.diag a from rfl,
        show ensembleAverage E.toClassical = E.avgClassical from rfl]
    exact klDivergence_contracts_under_stochastic_of_logsum
            T (E.diag a) E.avgClassical h_ac logSumInequality_holds

end UnifiedTheory.LayerB.HolevoDiagonalDischarge
