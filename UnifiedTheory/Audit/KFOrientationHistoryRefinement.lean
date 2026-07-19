/-
  Audit/KFOrientationHistoryRefinement.lean

  MULTIPLICATIVE REFINEMENT BENCHMARK FOR ORIENTATION COHERENCE

  The rigidity audit classified balanced kernels by `|y| <= 1/2`.  This file
  tests a concrete refinement mechanism: independent refinement stages multiply
  the normalized coherence `r = 2y`.  On the bounded parameter interval this
  induces `y ⋆ z = 2yz`.

  The law is closed, associative, and commutative.  Interior nonzero coherence
  contracts under self-refinement and repeated identical stages converge to
  zero.  The two orientation endpoints are exactly the nonzero parameters whose
  coherence magnitude is stable; the negative endpoint is stable up to the
  already proved reflection, not as a literal idempotent.

  This is a finite conditional refinement benchmark.  The repository does not
  yet prove that physical unlabeled causal-set refinement obeys this law.
-/

import Mathlib.Analysis.SpecificLimits.Normed
import UnifiedTheory.Audit.KFOrientationHistoryRigidity

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFOrientationHistoryRefinement

noncomputable section

open Filter Topology
open UnifiedTheory.Audit.KFOrientationCPChannelTower
open UnifiedTheory.Audit.KFOrientationPathQuantum
open UnifiedTheory.Audit.KFOrientationHistoryRigidity

/-! ## 1. Multiplicative normalized coherence -/

def normalizedHistoryCoherence (y : ℝ) : ℝ := 2 * y

/-- Candidate composition law when independent refinement stages multiply
normalized coherences. -/
def refinementCompose (y z : ℝ) : ℝ := 2 * y * z

theorem normalizedHistoryCoherence_refinementCompose (y z : ℝ) :
    normalizedHistoryCoherence (refinementCompose y z) =
      normalizedHistoryCoherence y * normalizedHistoryCoherence z := by
  simp [normalizedHistoryCoherence, refinementCompose]
  ring

theorem refinementCompose_comm (y z : ℝ) :
    refinementCompose y z = refinementCompose z y := by
  unfold refinementCompose
  ring

theorem refinementCompose_assoc (x y z : ℝ) :
    refinementCompose (refinementCompose x y) z =
      refinementCompose x (refinementCompose y z) := by
  simp [refinementCompose]
  ring

theorem refinementCompose_positiveEndpoint_left (y : ℝ) :
    refinementCompose (1 / 2) y = y := by
  simp [refinementCompose]

theorem refinementCompose_positiveEndpoint_right (y : ℝ) :
    refinementCompose y (1 / 2) = y := by
  unfold refinementCompose
  ring

/-- The negative pure endpoint acts by the already classified reflection
`y -> -y`; it is an involution rather than a second monoid unit. -/
theorem refinementCompose_negativeEndpoint (y : ℝ) :
    refinementCompose (-1 / 2) y = -y := by
  simp [refinementCompose]
  ring

theorem refinementCompose_closed
    {y z : ℝ} (hy : |y| ≤ 1 / 2) (hz : |z| ≤ 1 / 2) :
    |refinementCompose y z| ≤ 1 / 2 := by
  have hprod : |y| * |z| ≤ (1 / 2 : ℝ) * (1 / 2) :=
    mul_le_mul hy hz (abs_nonneg z) (by norm_num)
  rw [refinementCompose, abs_mul, abs_mul]
  norm_num
  nlinarith

/-! ## 2. Interior coherence contracts -/

theorem selfRefinement_strictly_contracts
    {y : ℝ} (hy0 : y ≠ 0) (hyInterior : |y| < 1 / 2) :
    |refinementCompose y y| < |y| := by
  have hyPos : 0 < |y| := abs_pos.mpr hy0
  have hfactor : 0 < |y| * (1 - 2 * |y|) :=
    mul_pos hyPos (by linarith)
  rw [refinementCompose, abs_mul, abs_mul]
  norm_num
  nlinarith

/-- Stability of coherence magnitude under self-refinement.  Magnitude, rather
than literal equality, treats the two reflected endpoint sectors symmetrically. -/
def IsNonzeroRefinementMagnitudeStable (y : ℝ) : Prop :=
  y ≠ 0 ∧ |refinementCompose y y| = |y|

theorem nonzero_refinementMagnitudeStable_iff
    {y : ℝ} (hy : |y| ≤ 1 / 2) :
    IsNonzeroRefinementMagnitudeStable y ↔
      y = -1 / 2 ∨ y = 1 / 2 := by
  constructor
  · rintro ⟨hy0, hStable⟩
    have hyPos : 0 < |y| := abs_pos.mpr hy0
    rw [refinementCompose, abs_mul, abs_mul] at hStable
    norm_num at hStable
    have hyAbs : |y| = 1 / 2 := by nlinarith
    rcases abs_choice y with hChoice | hChoice
    · right; linarith
    · left; linarith
  · rintro (rfl | rfl) <;>
      constructor <;> norm_num [refinementCompose]

/-- Literal self-refinement is stable up to reflection exactly at zero and the
two endpoints.  In particular, the negative endpoint composes to its reflected
positive partner. -/
theorem selfRefinement_eq_self_or_reflection_iff (y : ℝ) :
    refinementCompose y y = y ∨ refinementCompose y y = -y
      ↔ y = 0 ∨ y = -1 / 2 ∨ y = 1 / 2 := by
  constructor
  · rintro (h | h)
    · have hFactor : y * (2 * y - 1) = 0 := by
        simp [refinementCompose] at h
        nlinarith
      rcases mul_eq_zero.mp hFactor with hy0 | hyOne
      · exact Or.inl hy0
      · exact Or.inr (Or.inr (by linarith))
    · have hFactor : y * (2 * y + 1) = 0 := by
        simp [refinementCompose] at h
        nlinarith
      rcases mul_eq_zero.mp hFactor with hy0 | hyNeg
      · exact Or.inl hy0
      · exact Or.inr (Or.inl (by linarith))
  · rintro (rfl | rfl | rfl) <;> norm_num [refinementCompose]

/-! ## 3. Repeated independent stages -/

/-- Coherence after `n` identical independent refinement stages.  `n=0` is the
composition unit and `n=1` recovers the input kernel parameter. -/
def nStageRefinement (n : ℕ) (y : ℝ) : ℝ :=
  (1 / 2) * (2 * y) ^ n

theorem nStageRefinement_zero (y : ℝ) :
    nStageRefinement 0 y = 1 / 2 := by
  simp [nStageRefinement]

theorem nStageRefinement_one (y : ℝ) :
    nStageRefinement 1 y = y := by
  simp [nStageRefinement]

theorem nStageRefinement_add (m n : ℕ) (y : ℝ) :
    refinementCompose (nStageRefinement m y) (nStageRefinement n y) =
      nStageRefinement (m + n) y := by
  rw [nStageRefinement, nStageRefinement, nStageRefinement,
    refinementCompose, pow_add]
  ring

theorem interior_nStageRefinement_tendsto_zero
    {y : ℝ} (hyInterior : |y| < 1 / 2) :
    Tendsto (fun n : ℕ => nStageRefinement n y) atTop (𝓝 0) := by
  have hbase : |2 * y| < 1 := by
    rw [abs_mul]
    norm_num
    linarith
  have hp := tendsto_pow_atTop_nhds_zero_of_abs_lt_one hbase
  simpa [nStageRefinement] using
    (tendsto_const_nhds.mul hp :
      Tendsto (fun n : ℕ => (1 / 2 : ℝ) * (2 * y) ^ n)
        atTop (𝓝 ((1 / 2 : ℝ) * 0)))

theorem positiveEndpoint_nStageRefinement (n : ℕ) :
    nStageRefinement n (1 / 2) = 1 / 2 := by
  simp [nStageRefinement]

theorem negativeEndpoint_nStageRefinement_magnitude (n : ℕ) :
    |nStageRefinement n (-1 / 2)| = 1 / 2 := by
  norm_num [nStageRefinement, abs_mul, abs_pow]

/-- Under the multiplicative law, refinement-magnitude stability is equivalent
to all four independently derived endpoint criteria.  This is the precise
conditional endpoint-selection theorem. -/
theorem refinementMagnitudeStability_four_way
    {y : ℝ} (hy : |y| ≤ 1 / 2) :
    (IsNonzeroRefinementMagnitudeStable y ↔
      balancedHistoryKernel y * balancedHistoryKernel y =
        balancedHistoryKernel y)
      ∧ (IsNonzeroRefinementMagnitudeStable y ↔
        IsConvexExtremeBalancedKernel y)
      ∧ (IsNonzeroRefinementMagnitudeStable y ↔
        (bornWeight (balancedHistoryKernel y)
              positiveOrientationProjector = 1
          ∨ bornWeight (balancedHistoryKernel y)
              negativeOrientationProjector = 1))
      ∧ (IsNonzeroRefinementMagnitudeStable y ↔
        IsChiralitySelectedHistoryKernel (balancedHistoryKernel y)) := by
  have hStable := nonzero_refinementMagnitudeStable_iff hy
  exact ⟨hStable.trans (balancedHistoryKernel_pure_iff y).symm,
    hStable.trans (convexExtremeBalancedKernel_iff y).symm,
    hStable.trans (balancedHistoryKernel_deterministic_iff y).symm,
    hStable.trans (balancedHistoryKernel_chiralitySelected_iff y).symm⟩

/-- Conditional refinement-selection theorem.  Under multiplicative normalized
coherence, every nonzero interior kernel loses coherence, whereas exactly the
two pure/chirality-selected endpoints preserve its magnitude. -/
theorem multiplicative_refinement_selects_extremal_magnitude :
    (∀ y : ℝ, y ≠ 0 → |y| < 1 / 2 →
      |refinementCompose y y| < |y|)
      ∧ (∀ y : ℝ, |y| ≤ 1 / 2 →
        (IsNonzeroRefinementMagnitudeStable y ↔
          y = -1 / 2 ∨ y = 1 / 2))
      ∧ (∀ y : ℝ, |y| < 1 / 2 →
        Tendsto (fun n : ℕ => nStageRefinement n y) atTop (𝓝 0)) := by
  exact ⟨fun y hy0 hy => selfRefinement_strictly_contracts hy0 hy,
    fun y hy => nonzero_refinementMagnitudeStable_iff hy,
    fun y hy => interior_nStageRefinement_tendsto_zero hy⟩

#print axioms refinementCompose_closed
#print axioms selfRefinement_strictly_contracts
#print axioms nonzero_refinementMagnitudeStable_iff
#print axioms selfRefinement_eq_self_or_reflection_iff
#print axioms interior_nStageRefinement_tendsto_zero
#print axioms refinementMagnitudeStability_four_way
#print axioms multiplicative_refinement_selects_extremal_magnitude

end

end UnifiedTheory.Audit.KFOrientationHistoryRefinement
