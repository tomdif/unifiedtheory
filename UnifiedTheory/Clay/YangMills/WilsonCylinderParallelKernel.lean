/- Exact independent-block conditional product law for the actual open Wilson
cylinder. Retained coordinates become Dirac factors under overwrite. -/
import UnifiedTheory.Clay.YangMills.WilsonCylinderBlockAction
import UnifiedTheory.Clay.YangMills.WilsonCylinderConditionalInfluence
import UnifiedTheory.Clay.YangMills.WilsonParallelConditional
import UnifiedTheory.Clay.YangMills.CompactGibbsBlockFiber
import UnifiedTheory.Clay.YangMills.ParallelOscillation
import UnifiedTheory.Clay.YangMills.GibbsConstantShift

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonCylinderParallelKernel
noncomputable section
open MeasureTheory RegulatedGauge WilsonCylinderGeometry WilsonCylinderColors
open WilsonCylinderCoordinates WilsonCylinderConditionalInfluence WilsonCylinderBlockAction
open WilsonSingleLinkStaples

variable (n L : ℕ) [NeZero n]
local instance linkDecidableEq : DecidableEq (Link n L) := Classical.decEq _

def localAction (β : ℝ) (U : State n L) (S : Finset (Link n L))
    (a : Link n L) (q : Q) : ℝ :=
  if a ∈ S then conditionalAction n L β U a q - stateAction n L β U else 0

/-- Every local action is the actual one-coordinate conditional action minus a constant. -/
theorem localAction_continuous (β : ℝ) (U : State n L)
    (S : Finset (Link n L)) (a : Link n L) : Continuous (localAction n L β U S a) := by
  unfold localAction
  by_cases ha : a ∈ S
  · simp only [ha, ↓reduceIte]
    exact (conditionalAction n L β U a).continuous.sub continuous_const
  · simp only [ha, ↓reduceIte]
    exact continuous_const

/-- Geometric independence gives the actual affine sum of one-coordinate actions. -/
theorem action_sum (β : ℝ) (U : State n L) (S : Finset (Link n L))
    (hS : Independent n L S) (V : State n L) :
    stateAction n L β (overwrite S U V) = stateAction n L β U +
      ∑ a, localAction n L β U S a (V a) := by
  have h := action_decomposition n L Q character β 2 S hS U V
  change stateAction n L β (overwrite S U V) - stateAction n L β U =
    ∑ a ∈ S, (conditionalAction n L β U a (V a) - stateAction n L β U) at h
  simp only [localAction, Finset.sum_ite_mem_eq]
  linarith

/-- Action constants cancel from selected marginals; unused auxiliary marginals remain Haar. -/
theorem localAction_law (β : ℝ) (U : State n L)
    (S : Finset (Link n L)) (a : Link n L) :
    CompactGibbsContinuity.law (compactHaar Q) (localAction n L β U S a) =
      if a ∈ S then coordinateLaw n L β U a else compactHaar Q := by
  by_cases ha : a ∈ S
  · rw [if_pos ha]
    have he : localAction n L β U S a =
        fun q => -stateAction n L β U + conditionalAction n L β U a q := by
      funext q
      simp only [localAction, if_pos ha]
      ring
    rw [he, GibbsConstantShift.law_const_add _ _ (conditionalAction n L β U a).continuous]
    rfl
  · rw [if_neg ha]
    have he : localAction n L β U S a = fun _ => 0 := by
      funext q
      exact if_neg ha
    rw [he]
    simp [CompactGibbsContinuity.law, LocalGibbsComparison.weightedLaw]

/-- Equality of normalized probability measures for all measurable events. -/
theorem auxiliary_law_product (β : ℝ) (U : State n L)
    (S : Finset (Link n L)) (hS : Independent n L S) :
    CompactGibbsContinuity.law (Measure.pi (fun _ : Link n L => compactHaar Q))
        (fun V => stateAction n L β (overwrite S U V)) =
      Measure.pi (fun a => if a ∈ S then coordinateLaw n L β U a else compactHaar Q) := by
  rw [funext (action_sum n L β U S hS)]
  rw [WilsonParallelConditional.affine_product_law _ _
    (localAction_continuous n L β U S)]
  congr 1
  funext a
  exact localAction_law n L β U S a

/-- Overwrite turns unused auxiliary Haar coordinates into actual retained Dirac coordinates. -/
theorem overwrite_map_auxiliaryLaw (β : ℝ) (U : State n L)
    (S : Finset (Link n L)) (hS : Independent n L S) :
    (CompactGibbsContinuity.law (Measure.pi (fun _ : Link n L => compactHaar Q))
      (fun V => stateAction n L β (overwrite S U V))).map (overwrite S U) =
      Measure.pi (fun a => if a ∈ S then coordinateLaw n L β U a else Measure.dirac (U a)) := by
  rw [auxiliary_law_product n L β U S hS]
  let μ : Link n L → Measure Q :=
    fun a => if a ∈ S then coordinateLaw n L β U a else compactHaar Q
  let f : Link n L → Q → Q := fun a q => if a ∈ S then q else U a
  have hμ (a : Link n L) : IsProbabilityMeasure (μ a) := by
    dsimp only [μ]
    split
    · exact coordinateLaw_probability n L β U a
    · infer_instance
  letI (a : Link n L) : IsProbabilityMeasure (μ a) := hμ a
  have hf (a : Link n L) : Measurable (f a) := by
    dsimp only [f]
    split
    · exact measurable_id
    · exact measurable_const
  change (Measure.pi μ).map (fun V a => f a (V a)) = _
  rw [Measure.pi_map_pi (fun a => (hf a).aemeasurable)]
  congr 1
  funext a
  by_cases ha : a ∈ S
  · simp [μ, f, ha]
  · simp [μ, f, ha, Measure.map_const]

/-- The actual cylinder conditional block average is the literal parallel product update. -/
theorem blockAverage_eq_parallelAverage (β : ℝ) (U : State n L)
    (S : Finset (Link n L)) (hS : Independent n L S) (F : C(State n L, ℝ)) :
    CompactGibbsBlockUpdate.blockAverage (compactHaar Q) (stateAction n L β) S F U =
      ParallelOscillation.parallelAverage (fun a V => coordinateLaw n L β V a) S F U := by
  rw [CompactGibbsBlockFiber.blockAverage_full_fiber]
  change (∫ V, F (overwrite S U V) ∂CompactGibbsContinuity.law
    (Measure.pi (fun _ : Link n L => compactHaar Q))
    (fun V => stateAction n L β (overwrite S U V))) = _
  change _ = ∫ V, F V ∂Measure.pi
    (fun a => if a ∈ S then coordinateLaw n L β U a else Measure.dirac (U a))
  rw [← overwrite_map_auxiliaryLaw n L β U S hS]
  exact (integral_map (CompactGibbsBlockFiber.overwrite S U).continuous.measurable.aemeasurable
    F.continuous.aestronglyMeasurable).symm

/-- All eight actual cylinder colors satisfy the same exact product-kernel dictionary. -/
theorem colorAverage_eq_parallelAverage (β : ℝ) (U : State n L) (heven : 2 ∣ n)
    (c : WilsonCylinderColors.Color) (F : C(State n L, ℝ)) :
    CompactGibbsBlockUpdate.blockAverage (compactHaar Q) (stateAction n L β)
      (colorBlock n L heven c) F U =
      ParallelOscillation.parallelAverage (fun a V => coordinateLaw n L β V a)
        (colorBlock n L heven c) F U :=
  blockAverage_eq_parallelAverage n L β U _ (colorBlock_independent n L heven c) F

end
end UnifiedTheory.Clay.YangMills.WilsonCylinderParallelKernel
