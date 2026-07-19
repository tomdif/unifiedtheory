/-
  LayerB/HolevoBoundRhoBarBasis.lean
  ───────────────────────────────────

  **Unconditional Holevo bound for the SPECIFIC CASE where the
  projective measurement is performed in ρ̄'s eigenbasis** (the
  eigenbasis of the ensemble average).

  This sidesteps the deep analytic gap (general-basis Lindblad–
  Uhlmann monotonicity, deferred in `HolevoBoundQuantum.lean` as the
  `QuantumRelativeEntropyMonotonicity` hypothesis) by specializing
  the measurement choice to one for which we already have the DPI
  machinery — namely, the σ-eigenbasis DPI proved in
  `ProjectiveMeasurementDPI.umegaki_dpi_projective_sigma_basis`.

  PROOF STRATEGY (cf. task spec):
    1. By `holevoUmegakiForm_holds`:
         χ_quantum(E) = Σ_a w_a · S(ρ_a ‖ ρ̄).
    2. Per ensemble component, applying
         `umegaki_dpi_projective_sigma_basis` with σ = ρ̄ and ρ = ρ_a:
         KL( outcomesInSigmaBasis ρ_a ρ̄ ,
             outcomesInSigmaBasis ρ̄  ρ̄ )
           ≤  S(ρ_a ‖ ρ̄).
    3. The classical ensemble of measurement outcomes packages the
       outcomes-in-ρ̄-basis of each ρ_a, with the SAME weights.  Its
       ensembleAverage (the classical average of the measured
       outcomes) equals — by linearity of the trace-diagonal-real-part
       map in its argument — the outcomes of ρ̄ itself measured in its
       own eigenbasis:
         (ensembleAverage (measureEnsembleInRhoBarBasis E)).p b
           = Re ((U_ρ̄* · (Σ_a w_a ρ_a) · U_ρ̄)_bb)
           = Re ((U_ρ̄* · ρ̄ · U_ρ̄)_bb)
           = (outcomesInSigmaBasis ρ̄ ρ̄).p b.
    4. So:
         mutualInformation (measureEnsembleInRhoBarBasis E)
           = Σ_a w_a · KL( outcomesInSigmaBasis ρ_a ρ̄ ,
                           outcomesInSigmaBasis ρ̄  ρ̄ )
           ≤ Σ_a w_a · S(ρ_a ‖ ρ̄)        [by step 2]
           = χ_quantum(E)                  [by step 1].

  WHAT IS PROVEN (no `sorry`, no custom `axiom`):
    1. `measureEnsembleInRhoBarBasis E` — the classical ensemble
       obtained by measuring each state in ρ̄'s eigenbasis.
    2. `ensembleAverage_measureInRhoBarBasis_eq_outcomes_of_rhoBar`
       — the keystone linearity identity (step 3).
    3. `mutualInformation_measureInRhoBarBasis_le_holevoChiQuantum`
       — the unconditional Holevo bound for this measurement choice.
-/

import UnifiedTheory.LayerB.ProjectiveMeasurementDPI
import UnifiedTheory.LayerB.HolevoBoundQuantum
import UnifiedTheory.LayerB.HolevoUmegakiDischarge
import UnifiedTheory.LayerB.ClassicalEnsemble
import UnifiedTheory.LayerB.KleinInequalityFull

set_option relaxedAutoImplicit false

namespace UnifiedTheory.LayerB.HolevoBoundRhoBarBasis

open Matrix Complex
open scoped MatrixOrder ComplexOrder
open UnifiedTheory.LayerB.RobertsonSchrodinger
open UnifiedTheory.LayerB.SpectralFC
open UnifiedTheory.LayerB.UmegakiRelativeEntropy
open UnifiedTheory.LayerB.ClassicalEntropy
open UnifiedTheory.LayerB.ClassicalEntropy.ProbabilityVector
open UnifiedTheory.LayerB.ClassicalRelativeEntropy
open UnifiedTheory.LayerB.ClassicalChannelDPI
open UnifiedTheory.LayerB.ProjectiveMeasurementDPI
open UnifiedTheory.LayerB.HolevoBoundQuantum
open UnifiedTheory.LayerB.HolevoUmegakiDischarge
open UnifiedTheory.LayerB.KleinInequalityFull
open UnifiedTheory.LayerB.Ensemble

variable {α : Type*} [Fintype α] {n : ℕ}

/-! ## 1. The classical ensemble of measurement outcomes in ρ̄'s eigenbasis -/

/-- The classical ensemble obtained by measuring each state of `E`
    in the eigenbasis of the ensemble average `ρ̄ = ensembleAverageQuantum E`.
    Component `a` is the outcome distribution of measuring `ρ_a` in
    ρ̄'s eigenbasis, packaged as a `ProbabilityVector (Fin n)`.
    Weights are inherited unchanged from the quantum ensemble. -/
noncomputable def measureEnsembleInRhoBarBasis
    (E : QuantumEnsemble α n)
    (hRhoBar_pos : (ensembleAverageQuantum E).M.PosDef)
    (hStates_pos : ∀ a, (E.state a).M.PosDef) :
    ClassicalEnsemble α (Fin n) :=
  { weight := E.weight
    state := fun a => outcomesInSigmaBasis
                        (E.state a) (ensembleAverageQuantum E)
                        hRhoBar_pos (hStates_pos a) }

/-! ## 2. The keystone linearity identity

`(U_ρ̄* · ρ_a · U_ρ̄)_{bb}` is real-linear in `ρ_a` (in the sense that
averaging the matrices and then taking the diagonal real part agrees
with averaging the diagonal real parts).  This is the content of the
trace being linear and the real part being linear. -/

/-- **Keystone identity.**  The classical ensemble-average of the
    measured outcomes equals the outcome distribution of ρ̄ itself
    measured in its own eigenbasis:

      `(ensembleAverage (measureEnsembleInRhoBarBasis E)).p b
         = (outcomesInSigmaBasis ρ̄ ρ̄).p b`.

    Proof: pointwise, both sides are
    `Re ((U_ρ̄* · ρ̄ · U_ρ̄)_{bb})` after collapsing the weighted sum
    by linearity of matrix multiplication and the real part. -/
lemma ensembleAverage_measureInRhoBarBasis_eq_outcomes_of_rhoBar
    (E : QuantumEnsemble α n)
    (hRhoBar_pos : (ensembleAverageQuantum E).M.PosDef)
    (hStates_pos : ∀ a, (E.state a).M.PosDef) (b : Fin n) :
    (ensembleAverage
        (measureEnsembleInRhoBarBasis E hRhoBar_pos hStates_pos)).p b
      = (outcomesInSigmaBasis (ensembleAverageQuantum E)
                              (ensembleAverageQuantum E)
                              hRhoBar_pos hRhoBar_pos).p b := by
  -- Name the unitary.
  set Uσ : Matrix (Fin n) (Fin n) ℂ :=
    (ensembleAverageQuantum E).hHerm.eigenvectorUnitary.val with hUσ_def
  -- LHS: by definition of ensembleAverage,
  --   ∑ a, w_a · Re ((U_σ* · ρ_a · U_σ)_{bb}).
  -- RHS: by definition of outcomesInSigmaBasis,
  --   Re ((U_σ* · ρ̄ · U_σ)_{bb})
  --     = Re ((U_σ* · (∑ a, w_a • ρ_a) · U_σ)_{bb}).
  -- Unfold both sides.
  change (∑ a, E.weight.p a *
            ((star Uσ * (E.state a).M * Uσ) b b).re)
       = ((star Uσ * (ensembleAverageQuantum E).M * Uσ) b b).re
  -- Substitute the definition of ρ̄ on the RHS.
  rw [ensembleAverageQuantum_M]
  -- RHS now: Re ((star Uσ · (∑ a, w_a • ρ_a) · Uσ)_{bb})
  --       = Re ((∑ a, star Uσ · (w_a • ρ_a) · Uσ)_{bb})
  -- Step (a): distribute matrix multiplication over the sum on the RHS.
  rw [Matrix.mul_sum, Matrix.sum_mul]
  -- Now RHS: Re ((∑ a, star Uσ * ((w_a : ℂ) • (E.state a).M) * Uσ) b b)
  -- Step (b): the entry of a finite sum of matrices is the sum of entries.
  rw [Matrix.sum_apply]
  -- Step (c): Re of a finite sum = sum of Re.
  rw [Complex.re_sum]
  -- Per-summand identity:
  --   Re ((star Uσ * (w_a • ρ_a) * Uσ) b b) = w_a * Re ((star Uσ * ρ_a * Uσ) b b)
  apply Finset.sum_congr rfl
  intro a _
  -- Push the scalar all the way out of the matrix product.
  -- star Uσ * (w • ρ_a) * Uσ = w • (star Uσ * ρ_a * Uσ)
  have h_scalar_out :
      star Uσ * ((E.weight.p a : ℂ) • (E.state a).M) * Uσ
        = ((E.weight.p a : ℂ)) • (star Uσ * (E.state a).M * Uσ) := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [h_scalar_out]
  -- The entry of (c • M) is c * (entry of M).
  rw [Matrix.smul_apply, smul_eq_mul]
  -- And Re (w * z) = w.re * z.re - w.im * z.im;
  -- since w = ((w_real : ℝ) : ℂ), w.re = w_real, w.im = 0.
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-! ## 3. The main theorem -/

/-- **Holevo bound for measurements in ρ̄'s eigenbasis.**

    This is the UNCONDITIONAL form of the Holevo bound: the classical
    mutual information of the ensemble of outcomes (obtained by
    measuring each component state in the eigenbasis of the ensemble
    average) is bounded above by the Holevo χ quantity, with NO
    appeal to a general-basis Lindblad–Uhlmann monotonicity
    hypothesis.

    Argument:
      I(measureEns(E))
        = Σ_a w_a · KL( outcomesInSigmaBasis ρ_a ρ̄ ,
                        ensembleAverage measureEns )         [defn. of I]
        = Σ_a w_a · KL( outcomesInSigmaBasis ρ_a ρ̄ ,
                        outcomesInSigmaBasis ρ̄  ρ̄ )         [keystone]
        ≤ Σ_a w_a · S(ρ_a ‖ ρ̄)                                [σ-basis DPI]
        = χ_quantum(E)                                        [Umegaki form]. -/
theorem mutualInformation_measureInRhoBarBasis_le_holevoChiQuantum
    (E : QuantumEnsemble α n)
    (hRhoBar_pos : (ensembleAverageQuantum E).M.PosDef)
    (hStates_pos : ∀ a, (E.state a).M.PosDef) :
    mutualInformation (measureEnsembleInRhoBarBasis E hRhoBar_pos hStates_pos)
      ≤ holevoChiQuantum E := by
  -- (1) Rewrite χ in the average-Umegaki form.
  rw [holevoUmegakiForm_holds α n E]
  -- Goal:
  --   mutualInformation (measureEnsembleInRhoBarBasis E ...)
  --     ≤ ∑ a, w_a * umegakiRelativeEntropy (ρ_a) ρ̄.
  -- Unfold mutualInformation.
  unfold mutualInformation
  -- Goal: ∑ a, w_a * KL(measureEns.state a, ensembleAverage measureEns)
  --       ≤ ∑ a, w_a * S(ρ_a ‖ ρ̄).
  -- (2) Rewrite the inner KL via the keystone identity:
  --   KL(measureEns.state a, ensembleAverage measureEns)
  --     = KL(outcomesInSigmaBasis ρ_a ρ̄, outcomesInSigmaBasis ρ̄ ρ̄).
  -- (3) Then per-summand apply DPI.
  apply Finset.sum_le_sum
  intro a _
  -- Per-a step.
  -- The classical-ensemble weight at a is definitionally E.weight.p a.
  have h_w_eq : (measureEnsembleInRhoBarBasis E hRhoBar_pos hStates_pos).weight.p a
                  = E.weight.p a := rfl
  rw [h_w_eq]
  by_cases hwa : E.weight.p a = 0
  · rw [hwa, zero_mul, zero_mul]
  · have h_w_nn : 0 ≤ E.weight.p a := E.weight.nonneg a
    -- Inner KL rewrite via klDivergence_congr.
    have h_kl_eq :
        klDivergence
            ((measureEnsembleInRhoBarBasis E hRhoBar_pos hStates_pos).state a)
            (ensembleAverage
              (measureEnsembleInRhoBarBasis E hRhoBar_pos hStates_pos))
          = klDivergence
              (outcomesInSigmaBasis (E.state a) (ensembleAverageQuantum E)
                                    hRhoBar_pos (hStates_pos a))
              (outcomesInSigmaBasis (ensembleAverageQuantum E)
                                    (ensembleAverageQuantum E)
                                    hRhoBar_pos hRhoBar_pos) := by
      apply klDivergence_congr
      · -- Component states agree by definition of measureEnsembleInRhoBarBasis.
        intro b; rfl
      · -- Averages agree by the keystone identity.
        intro b
        exact ensembleAverage_measureInRhoBarBasis_eq_outcomes_of_rhoBar
                E hRhoBar_pos hStates_pos b
    rw [h_kl_eq]
    -- Now reduce to: w_a * KL(...) ≤ w_a * S(ρ_a ‖ ρ̄).
    apply mul_le_mul_of_nonneg_left _ h_w_nn
    -- Apply DPI from ProjectiveMeasurementDPI.
    exact umegaki_dpi_projective_sigma_basis
            (E.state a) (ensembleAverageQuantum E)
            (hStates_pos a) hRhoBar_pos

/-! ## 4. Axiom audit

  After this file is built, one can verify:
    #print axioms mutualInformation_measureInRhoBarBasis_le_holevoChiQuantum
      ⟹  [propext, Classical.choice, Quot.sound]
  Depends ONLY on Lean's three standard axioms.
  No `sorry`, no custom `axiom`. -/

end UnifiedTheory.LayerB.HolevoBoundRhoBarBasis
