/-
  Audit/KFCausalSetSourceMagnitudeDecoherence.lean

  GEOMETRY-DEPENDENT COHERENCE RETENTION

  Character selection uses only the sign of the maximal-birth source, but the
  source magnitude is not inert in the balanced rank-two kernel.  Conditional
  on the already formalized independent-refinement composition law, normalized
  coherence multiplies at each stage.  The two rank-three benchmark births
  therefore have different exact retention bases:

      three-chain newborn:  y = 1/6,  r = 2y = 1/3;
      fork newborn:         y = 1/5,  r = 2y = 2/5.

  The fork kernel retains more coherence at every positive refinement depth,
  has greater purity, and has smaller determinant.  This is a model-internal,
  prediction-shaped distinction.  It is conditional on using the geometric
  source as the balanced-kernel parameter and on independent multiplicative
  refinement; no continuum time or laboratory decoherence rate is asserted.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalSetMicroscopicResponseLaw
import UnifiedTheory.Audit.KFCausalSetGeometricOrientationEntropyGap
import UnifiedTheory.Audit.KFOrientationHistoryRefinement

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalSetSourceMagnitudeDecoherence

noncomputable section

open UnifiedTheory.Audit.KFCausalSetSequentialGrowth
open UnifiedTheory.Audit.KFCausalSetTransitionEdges
open UnifiedTheory.Audit.KFCausalSetGeometricOrientationDynamics
open UnifiedTheory.Audit.KFCausalSetGeometricOrientationAsymptotics
open UnifiedTheory.Audit.KFCausalSetConjugationCompleteness
open UnifiedTheory.Audit.KFCausalSetGrowthArrowChirality
open UnifiedTheory.Audit.KFOrientationHistoryRigidity
open UnifiedTheory.Audit.KFOrientationHigherRankDecoherence
open UnifiedTheory.Audit.KFOrientationHistoryRefinement
open UnifiedTheory.Audit.KFCausalSetGeometricOrientationEntropyGap

/-! ## 1. The two exact rank-three source magnitudes -/

/-- Geometric newborn source for the full-precursor extension of the
two-chain. -/
def chainThreeNewbornSourceR : ℝ :=
  ((maximalBirthOrientationSourceQ (cardinalCausalChain 2)
    (fullCausalPastSet (cardinalCausalChain 2)) : ℚ) : ℝ)

/-- Geometric newborn source for the full-precursor extension of the
two-antichain, whose child is the rank-three fork. -/
def forkThreeNewbornSourceR : ℝ :=
  ((maximalBirthOrientationSourceQ (cardinalCausalAntichain 2)
    (fullCausalPastSet (cardinalCausalAntichain 2)) : ℚ) : ℝ)

theorem chainThreeNewbornSourceR_exact :
    chainThreeNewbornSourceR = 1 / 6 := by
  norm_num [chainThreeNewbornSourceR, chainThreeNewborn_source_exact]

theorem forkThreeNewbornSourceR_exact :
    forkThreeNewbornSourceR = 1 / 5 := by
  norm_num [forkThreeNewbornSourceR, antichainTwoFullBirth_source_exact]

theorem chainThree_source_lt_forkThree_source :
    chainThreeNewbornSourceR < forkThreeNewbornSourceR := by
  rw [chainThreeNewbornSourceR_exact, forkThreeNewbornSourceR_exact]
  norm_num

/-! ## 2. Exact independent-refinement coherence rates -/

/-- Magnitude of normalized history coherence after `steps` identical
independent refinement stages. -/
def independentRefinementCoherence (steps : ℕ) (source : ℝ) : ℝ :=
  |normalizedHistoryCoherence (nStageRefinement steps source)|

/-- The per-stage retention factor is exactly `|2y|` for every balanced
kernel parameter, not only for the chain and fork examples. -/
theorem independentRefinementCoherence_eq_abs_pow
    (steps : ℕ) (source : ℝ) :
    independentRefinementCoherence steps source = |2 * source| ^ steps := by
  rw [independentRefinementCoherence, normalizedHistoryCoherence,
    nStageRefinement]
  norm_num [abs_mul, abs_pow]
  ring

/-- Both pure endpoints retain unit coherence at every refinement depth. -/
theorem pureEndpoint_independentRefinementCoherence
    (steps : ℕ) (chirality : Fin 2) :
    independentRefinementCoherence steps
        (chiralBoundaryOrientationParameter chirality) = 1 := by
  rw [independentRefinementCoherence_eq_abs_pow, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    chiralBoundaryOrientationParameter_endpoint]
  norm_num

/-- Conversely, retaining unit coherence at every depth characterizes the
two pure orientation endpoints. -/
theorem coherencePreserved_allDepths_iff (source : ℝ) :
    (∀ steps : ℕ, independentRefinementCoherence steps source = 1) ↔
      source = -1 / 2 ∨ source = 1 / 2 := by
  constructor
  · intro hAll
    have hOne := hAll 1
    rw [independentRefinementCoherence_eq_abs_pow] at hOne
    norm_num [abs_mul] at hOne
    have hAbs : |source| = 1 / 2 := by linarith
    rcases abs_choice source with hChoice | hChoice
    · right
      linarith
    · left
      linarith
  · rintro (rfl | rfl) <;>
      intro steps <;>
      rw [independentRefinementCoherence_eq_abs_pow] <;> norm_num

/-- A gregarious birth has zero source and loses all coherence after the first
refinement stage. -/
theorem gregarious_coherence_zero_after_one (steps : ℕ) :
    independentRefinementCoherence (steps + 1) 0 = 0 := by
  rw [independentRefinementCoherence_eq_abs_pow]
  simp

/-- Every finite geometric orientation has a universal per-stage retention
factor below `1/2`; after `n>0` independent stages it is bounded strictly by
`2^{-n}`. -/
theorem finiteGeometry_coherence_lt_half_pow {n : ℕ}
    (parent : CardinalCausalOrder n) (event : Fin n) (steps : ℕ) :
    independentRefinementCoherence (steps + 1)
        (((causalOrientationDensityQ parent event : ℚ) : ℝ)) <
      (1 / 2 : ℝ) ^ (steps + 1) := by
  rw [independentRefinementCoherence_eq_abs_pow]
  have hQuarter := causalOrientationDensityR_abs_lt_quarter parent event
  have hBase :
      |2 * (((causalOrientationDensityQ parent event : ℚ) : ℝ))| <
        (1 / 2 : ℝ) := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    nlinarith
  exact pow_lt_pow_left₀ hBase (abs_nonneg _) (Nat.succ_ne_zero steps)

/-- Hence every finite geometric orientation decoheres asymptotically under
the multiplicative refinement benchmark. -/
theorem finiteGeometry_coherence_tendsto_zero {n : ℕ}
    (parent : CardinalCausalOrder n) (event : Fin n) :
    Filter.Tendsto
      (fun steps : ℕ => independentRefinementCoherence steps
        (((causalOrientationDensityQ parent event : ℚ) : ℝ)))
      Filter.atTop (nhds 0) := by
  have hQuarter := causalOrientationDensityR_abs_lt_quarter parent event
  have hUnit :
      |2 * (((causalOrientationDensityQ parent event : ℚ) : ℝ))| < 1 := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    nlinarith
  have hAbsUnit :
      |(|2 * (((causalOrientationDensityQ parent event : ℚ) : ℝ))|)| < 1 := by
    simpa only [abs_abs] using hUnit
  simpa only [independentRefinementCoherence_eq_abs_pow] using
    (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hAbsUnit)

/-- **Conditional scale separation.**  Under multiplicative refinement, every
finite geometric orientation loses coherence with a universal rate strictly
faster than `2^{-n}`, while both pure chiral endpoints retain unit coherence
at every depth.  The gregarious source is erased after one stage. -/
theorem multiplicativeRefinement_geometryDecoheres_chiralityPersists :
    (∀ (steps : ℕ) (chirality : Fin 2),
      independentRefinementCoherence steps
        (chiralBoundaryOrientationParameter chirality) = 1)
      ∧ (∀ {n : ℕ} (parent : CardinalCausalOrder n) (event : Fin n),
        Filter.Tendsto
          (fun steps : ℕ => independentRefinementCoherence steps
            (((causalOrientationDensityQ parent event : ℚ) : ℝ)))
          Filter.atTop (nhds 0))
      ∧ (∀ {n : ℕ} (parent : CardinalCausalOrder n) (event : Fin n)
          (steps : ℕ),
        independentRefinementCoherence (steps + 1)
            (((causalOrientationDensityQ parent event : ℚ) : ℝ)) <
          (1 / 2 : ℝ) ^ (steps + 1))
      ∧ (∀ steps : ℕ,
        independentRefinementCoherence (steps + 1) 0 = 0) := by
  exact ⟨pureEndpoint_independentRefinementCoherence,
    finiteGeometry_coherence_tendsto_zero,
    finiteGeometry_coherence_lt_half_pow,
    gregarious_coherence_zero_after_one⟩

theorem chainThree_normalizedHistoryCoherence :
    normalizedHistoryCoherence chainThreeNewbornSourceR = 1 / 3 := by
  rw [chainThreeNewbornSourceR_exact]
  norm_num [normalizedHistoryCoherence]

theorem forkThree_normalizedHistoryCoherence :
    normalizedHistoryCoherence forkThreeNewbornSourceR = 2 / 5 := by
  rw [forkThreeNewbornSourceR_exact]
  norm_num [normalizedHistoryCoherence]

theorem chainThree_independentRefinementCoherence (steps : ℕ) :
    independentRefinementCoherence steps chainThreeNewbornSourceR =
      (1 / 3 : ℝ) ^ steps := by
  rw [independentRefinementCoherence, normalizedHistoryCoherence,
    nStageRefinement, chainThreeNewbornSourceR_exact]
  norm_num [abs_mul, abs_pow]
  ring

theorem forkThree_independentRefinementCoherence (steps : ℕ) :
    independentRefinementCoherence steps forkThreeNewbornSourceR =
      (2 / 5 : ℝ) ^ steps := by
  rw [independentRefinementCoherence, normalizedHistoryCoherence,
    nStageRefinement, forkThreeNewbornSourceR_exact]
  norm_num [abs_mul, abs_pow]
  ring

/-- The geometry difference survives every positive refinement depth: the
fork retains strictly more normalized coherence than the chain. -/
theorem forkThree_retains_more_coherence (steps : ℕ) :
    independentRefinementCoherence (steps + 1) chainThreeNewbornSourceR <
      independentRefinementCoherence (steps + 1) forkThreeNewbornSourceR := by
  rw [chainThree_independentRefinementCoherence,
    forkThree_independentRefinementCoherence]
  exact pow_lt_pow_left₀ (by norm_num) (by norm_num) (Nat.succ_ne_zero steps)

theorem chainThree_coherence_tendsto_zero :
    Filter.Tendsto
      (fun steps : ℕ =>
        independentRefinementCoherence steps chainThreeNewbornSourceR)
      Filter.atTop (nhds 0) := by
  have hBase : |(1 / 3 : ℝ)| < 1 := by norm_num
  simpa only [chainThree_independentRefinementCoherence] using
    (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hBase)

theorem forkThree_coherence_tendsto_zero :
    Filter.Tendsto
      (fun steps : ℕ =>
        independentRefinementCoherence steps forkThreeNewbornSourceR)
      Filter.atTop (nhds 0) := by
  have hBase : |(2 / 5 : ℝ)| < 1 := by norm_num
  simpa only [forkThree_independentRefinementCoherence] using
    (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hBase)

/-! ## 3. One-stage mixedness fingerprints -/

theorem chainThree_orientationSpectralPurity_exact :
    orientationSpectralPurity chainThreeNewbornSourceR = 5 / 9 := by
  rw [orientationSpectralPurity_formula, chainThreeNewbornSourceR_exact]
  norm_num

theorem forkThree_orientationSpectralPurity_exact :
    orientationSpectralPurity forkThreeNewbornSourceR = 29 / 50 := by
  rw [orientationSpectralPurity_formula, forkThreeNewbornSourceR_exact]
  norm_num

theorem chainThree_purity_lt_forkThree_purity :
    orientationSpectralPurity chainThreeNewbornSourceR <
      orientationSpectralPurity forkThreeNewbornSourceR := by
  rw [chainThree_orientationSpectralPurity_exact,
    forkThree_orientationSpectralPurity_exact]
  norm_num

theorem chainThree_balancedHistoryKernel_det_exact :
    Matrix.det (balancedHistoryKernel chainThreeNewbornSourceR) =
      ((2 / 9 : ℝ) : ℂ) := by
  rw [balancedHistoryKernel_det, chainThreeNewbornSourceR_exact]
  norm_num

theorem forkThree_balancedHistoryKernel_det_exact :
    Matrix.det (balancedHistoryKernel forkThreeNewbornSourceR) =
      ((21 / 100 : ℝ) : ℂ) := by
  rw [balancedHistoryKernel_det, forkThreeNewbornSourceR_exact]
  norm_num

theorem forkThree_det_lt_chainThree_det :
    (Matrix.det
        (balancedHistoryKernel forkThreeNewbornSourceR)).re <
      (Matrix.det
        (balancedHistoryKernel chainThreeNewbornSourceR)).re := by
  rw [forkThree_balancedHistoryKernel_det_exact,
    chainThree_balancedHistoryKernel_det_exact]
  norm_num

/-! ## 4. Prediction-shaped capstone -/

/-- Conditional on the repository's independent multiplicative refinement
law, the geometry-dependent source magnitude determines an exact rank-two
mixedness and coherence-retention fingerprint.  Character selection remains
sign-only, but magnitude controls these separate observables. -/
theorem sourceMagnitude_controls_refinementMixedness :
    normalizedHistoryCoherence chainThreeNewbornSourceR = 1 / 3
      ∧ normalizedHistoryCoherence forkThreeNewbornSourceR = 2 / 5
      ∧ (∀ steps : ℕ,
        independentRefinementCoherence (steps + 1)
            chainThreeNewbornSourceR <
          independentRefinementCoherence (steps + 1)
            forkThreeNewbornSourceR)
      ∧ orientationSpectralPurity chainThreeNewbornSourceR = 5 / 9
      ∧ orientationSpectralPurity forkThreeNewbornSourceR = 29 / 50
      ∧ (Matrix.det
          (balancedHistoryKernel chainThreeNewbornSourceR)).re = 2 / 9
      ∧ (Matrix.det
          (balancedHistoryKernel forkThreeNewbornSourceR)).re = 21 / 100 := by
  exact ⟨chainThree_normalizedHistoryCoherence,
    forkThree_normalizedHistoryCoherence,
    forkThree_retains_more_coherence,
    chainThree_orientationSpectralPurity_exact,
    forkThree_orientationSpectralPurity_exact,
    congrArg Complex.re chainThree_balancedHistoryKernel_det_exact,
    congrArg Complex.re forkThree_balancedHistoryKernel_det_exact⟩

#print axioms chainThreeNewbornSourceR_exact
#print axioms forkThreeNewbornSourceR_exact
#print axioms forkThree_retains_more_coherence
#print axioms independentRefinementCoherence_eq_abs_pow
#print axioms coherencePreserved_allDepths_iff
#print axioms finiteGeometry_coherence_lt_half_pow
#print axioms finiteGeometry_coherence_tendsto_zero
#print axioms multiplicativeRefinement_geometryDecoheres_chiralityPersists
#print axioms chainThree_orientationSpectralPurity_exact
#print axioms forkThree_orientationSpectralPurity_exact
#print axioms sourceMagnitude_controls_refinementMixedness

end

end UnifiedTheory.Audit.KFCausalSetSourceMagnitudeDecoherence
