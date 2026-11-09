/-
The actual Wilson conditional block operator is the literal parallel product
update. The normalized full auxiliary law factors over selected links, with
Haar factors elsewhere; overwrite transports those unused factors to Dirac
masses at retained coordinates. The final operator identity is proved from
the actual conditional-expectation fiber formula. No mixing hypothesis enters.
-/
import UnifiedTheory.Clay.YangMills.WilsonCoordinateInfluence
import UnifiedTheory.Clay.YangMills.WilsonParallelConditional
import UnifiedTheory.Clay.YangMills.CompactGibbsBlockFiber
import UnifiedTheory.Clay.YangMills.ParallelOscillation

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.WilsonParallelKernel
noncomputable section
open MeasureTheory RegulatedGauge PeriodicLattice4 WilsonUniformVariance
open WilsonSingleLinkStaples WilsonIndependentBlocks WilsonBlockIntegration
open SU2StarEnergy SU2WilsonConditionalSource WilsonCoordinateInfluence
open SU2HaarTilt
variable (n : ℕ) [NeZero n]
local instance edgeDecidableEq : DecidableEq (Edge (Vertex n)) := Classical.decEq _
local instance linkDecidableEq : DecidableEq (Link n) := Classical.decEq _

/-- The original full Wilson action in literal positive-link product coordinates. -/
def stateAction (β : ℝ) : C(Link n → Q, ℝ) where
  toFun U := action n Q character β 2 (toConfiguration n U)
  continuous_toFun :=
    (continuous_orientedWilsonAction (Vertex n) Q character character_continuous
      (base n) (loops n) β 2).comp
      (continuous_pi (fun e => continuous_apply (edgeCoord n e)))

/-- Selected links are overwritten; every other positive link is retained. -/
def overwrite (U : Link n → Q) (S : Finset (Link n)) (W : Link n → Q) : Link n → Q :=
  fun i => if i ∈ S then W i else U i

omit [NeZero n] in
theorem overwrite_continuous (U : Link n → Q) (S : Finset (Link n)) :
    Continuous (overwrite n U S) := by
  apply continuous_pi
  intro i
  by_cases hi : i ∈ S
  · simpa only [overwrite, if_pos hi] using
      (continuous_apply i : Continuous (fun W : Link n → Q => W i))
  · simpa only [overwrite, if_neg hi] using
      (continuous_const : Continuous (fun _ : Link n → Q => U i))

omit [NeZero n] in
/-- Product overwrite is exactly the repository's actual configuration block update. -/
theorem toConfiguration_overwrite (U W : Link n → Q) (S : Finset (Link n)) :
    toConfiguration n (overwrite n U S W) = blockUpdate n Q (toConfiguration n U) S W := by
  funext e
  by_cases he : edgeCoord n e ∈ S
  · simp [toConfiguration, overwrite, blockUpdate, he]
  · simp [toConfiguration, overwrite, blockUpdate, he]

/-- Exterior reconstruction with a new selected value is the actual one-link update. -/
theorem assemble_exterior_update (a : Link n) (U : Configuration (Vertex n) Q) (q : Q) :
    SingleCoordinateProduct.assemble (selectedLink n a.1 a.2) (exterior n a.1 a.2 U, q) =
      Function.update U (selectedLink n a.1 a.2) q := by
  funext e
  by_cases he : e = selectedLink n a.1 a.2
  · subst e
    rw [SingleCoordinateProduct.assemble_self, Function.update_self]
  · rw [SingleCoordinateProduct.assemble_other _ _ he, Function.update_of_ne he]
    rfl

/-- A selected factor differs from the genuine conditional action only by the fixed action. -/
theorem localAction_selected (β : ℝ) (U : Link n → Q) (S : Finset (Link n))
    (a : Link n) (ha : a ∈ S) (q : Q) :
    localAction n Q character β 2 (toConfiguration n U) S a q =
      -stateAction n β U + splitAction n a.1 a.2 β
        (exterior n a.1 a.2 (toConfiguration n U), q) := by
  unfold WilsonBlockIntegration.localAction
  rw [if_pos ha]
  unfold splitAction
  rw [assemble_exterior_update]
  change action n Q character β 2 _ - action n Q character β 2 _ =
    -action n Q character β 2 _ + action n Q character β 2 _
  ring

/-- The unused auxiliary coordinates retain the original normalized Haar law. -/
theorem zero_action_law :
    CompactGibbsContinuity.law (compactHaar Q) (fun _ : Q => (0 : ℝ)) = compactHaar Q := by
  simp [CompactGibbsContinuity.law, LocalGibbsComparison.weightedLaw]

/-- Every factor is the actual normalized conditional law on selected links and Haar elsewhere. -/
theorem localAction_law (β : ℝ) (U : Link n → Q) (S : Finset (Link n)) (a : Link n) :
    CompactGibbsContinuity.law (compactHaar Q)
        (localAction n Q character β 2 (toConfiguration n U) S a) =
      if a ∈ S then coordinateLaw n β U a else compactHaar Q := by
  by_cases ha : a ∈ S
  · rw [if_pos ha, funext (localAction_selected n β U S a ha)]
    rw [GibbsConstantShift.law_const_add]
    · rfl
    · exact (splitAction_continuous n a.1 a.2 β).comp
        (continuous_const.prodMk continuous_id)
  · rw [if_neg ha]
    have hz : WilsonBlockIntegration.localAction n Q character β 2
        (toConfiguration n U) S a = fun _ => 0 := by
      funext q
      unfold WilsonBlockIntegration.localAction
      exact if_neg ha
    rw [hz, zero_action_law]

/-- The exact full auxiliary Gibbs law is a product of the actual one-link laws. -/
theorem auxiliary_law_product (β : ℝ) (U : Link n → Q)
    (S : Finset (Link n)) (hS : Independent n S) :
    CompactGibbsContinuity.law (Measure.pi (fun _ : Link n => compactHaar Q))
        (fun W => stateAction n β (overwrite n U S W)) =
      Measure.pi (fun a => if a ∈ S then coordinateLaw n β U a else compactHaar Q) := by
  change CompactGibbsContinuity.law _
    (fun W => action n Q character β 2 (toConfiguration n (overwrite n U S W))) = _
  simp only [toConfiguration_overwrite]
  rw [WilsonParallelConditional.wilson_block_law n Q character character_continuous β 2 _ S hS]
  congr 1
  funext a
  exact localAction_law n β U S a

/-- Pushing the actual auxiliary law through overwrite retains Dirac masses
outside the selected block and the genuine Wilson conditional laws inside it. -/
theorem overwrite_map_auxiliaryLaw (β : ℝ) (U : Link n → Q)
    (S : Finset (Link n)) (hS : Independent n S) :
    (CompactGibbsContinuity.law (Measure.pi (fun _ : Link n => compactHaar Q))
      (fun W => stateAction n β (overwrite n U S W))).map (overwrite n U S) =
      Measure.pi (fun a => if a ∈ S then coordinateLaw n β U a else Measure.dirac (U a)) := by
  rw [auxiliary_law_product n β U S hS]
  let μ : Link n → Measure Q :=
    fun a => if a ∈ S then coordinateLaw n β U a else compactHaar Q
  let f : Link n → Q → Q := fun a q => if a ∈ S then q else U a
  have hμ (a : Link n) : IsProbabilityMeasure (μ a) := by
    dsimp only [μ]
    split
    · exact coordinateLaw_probability n β U a
    · infer_instance
  letI (a : Link n) : IsProbabilityMeasure (μ a) := hμ a
  have hf (a : Link n) : Measurable (f a) := by
    dsimp only [f]
    split
    · exact measurable_id
    · exact measurable_const
  change (Measure.pi μ).map (fun W a => f a (W a)) = _
  rw [Measure.pi_map_pi (fun a => (hf a).aemeasurable)]
  congr 1
  funext a
  by_cases ha : a ∈ S
  · simp [μ, f, ha]
  · simp [μ, f, ha, Measure.map_const]

/-- The genuine full-fiber conditional integral is the exact retained product update. -/
theorem integral_overwrite_eq_product (β : ℝ) (U : Link n → Q)
    (S : Finset (Link n)) (hS : Independent n S) (F : C(Link n → Q, ℝ)) :
    (∫ W, F (overwrite n U S W) ∂CompactGibbsContinuity.law
        (Measure.pi (fun _ : Link n => compactHaar Q))
        (fun W => stateAction n β (overwrite n U S W))) =
      ∫ W, F W ∂Measure.pi
        (fun a => if a ∈ S then coordinateLaw n β U a else Measure.dirac (U a)) := by
  rw [← overwrite_map_auxiliaryLaw n β U S hS]
  exact (integral_map (overwrite_continuous n U S).measurable.aemeasurable
    F.continuous.aestronglyMeasurable).symm

/-- The actual original-law conditional expectation is exactly the parallel
product operator to which the proved coordinate influences apply. -/
theorem blockAverage_eq_parallelAverage (β : ℝ) (U : Link n → Q)
    (S : Finset (Link n)) (hS : Independent n S) (F : C(Link n → Q, ℝ)) :
    CompactGibbsBlockUpdate.blockAverage (compactHaar Q) (stateAction n β) S F U =
      ParallelOscillation.parallelAverage (fun a V => coordinateLaw n β V a) S F U := by
  rw [CompactGibbsBlockFiber.blockAverage_full_fiber]
  exact integral_overwrite_eq_product n β U S hS F

end
end UnifiedTheory.Clay.YangMills.WilsonParallelKernel
