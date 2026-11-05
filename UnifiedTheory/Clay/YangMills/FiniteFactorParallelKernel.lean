/- Actual Gibbs block updates for arbitrary generated finite factors.
A color must be independent for the current support family. No original
Wilson coloring or conditional-product identity is assumed to survive elimination. -/
import UnifiedTheory.Clay.YangMills.FiniteFactorInfluence
import UnifiedTheory.Clay.YangMills.CompactGibbsBlockFiber

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.FiniteFactorParallelKernel
noncomputable section
open MeasureTheory FiniteFactorConditional FiniteFactorInfluence CompactGibbsBlockFiber

variable {I P X : Type*} [Fintype I] [Fintype P] [DecidableEq I]
  [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsProbabilityMeasure μ]

def actionMap (Φ : P → (I → X) → ℝ) (hΦc : ∀ p, Continuous (Φ p)) : C(I → X, ℝ) :=
  ⟨action Φ, action_continuous Φ hΦc⟩

def auxiliaryAction (Φ : P → (I → X) → ℝ) (U : I → X) (S : Finset I)
    (i : I) (q : X) : ℝ :=
  if i ∈ S then action Φ (Function.update U i q) - action Φ U else 0

omit [Fintype I] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] in
theorem auxiliaryAction_continuous (Φ : P → (I → X) → ℝ)
    (hΦc : ∀ p, Continuous (Φ p)) (U : I → X) (S : Finset I) (i : I) :
    Continuous (auxiliaryAction Φ U S i) := by
  unfold auxiliaryAction
  by_cases hi : i ∈ S
  · simp only [hi, ↓reduceIte]
    exact ((action_continuous Φ hΦc).comp (update_continuous U i)).sub continuous_const
  · simp only [hi, ↓reduceIte]
    exact continuous_const

omit [CompactSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
/-- Full auxiliary coordinates implement the already proved independent-block decomposition. -/
theorem action_sum (D : P → Finset I) (Φ : P → (I → X) → ℝ)
    (hΦ : ∀ p, DependsOn (Φ p) (D p : Set I)) (U : I → X) (S : Finset I)
    (hS : Independent D S) (V : I → X) :
    action Φ (overwrite S U V) = action Φ U + ∑ i, auxiliaryAction Φ U S i (V i) := by
  have he : overwrite S U V = replace S U (fun i => V i.val) := by
    funext i
    by_cases hi : i ∈ S <;> simp [overwrite, replace, hi]
  rw [he, action_decomposition D Φ hΦ S hS]
  simp only [auxiliaryAction, Finset.sum_ite_mem_eq]
  congr 1
  exact Finset.sum_coe_sort S (fun i => action Φ (Function.update U i (V i)) - action Φ U)

omit [Fintype I] [CompactSpace X] [SecondCountableTopology X] in
theorem auxiliaryAction_law (Φ : P → (I → X) → ℝ) (hΦc : ∀ p, Continuous (Φ p))
    (U : I → X) (S : Finset I) (i : I) :
    CompactGibbsContinuity.law μ (auxiliaryAction Φ U S i) =
      if i ∈ S then coordinateLaw μ Φ i U else μ := by
  by_cases hi : i ∈ S
  · rw [if_pos hi]
    have he : auxiliaryAction Φ U S i =
        fun q => -action Φ U + action Φ (Function.update U i q) := by
      funext q
      simp only [auxiliaryAction, if_pos hi]
      ring
    rw [he]
    exact GibbsConstantShift.law_const_add μ (fun q => action Φ (Function.update U i q))
      ((action_continuous Φ hΦc).comp (update_continuous U i)) _
  · rw [if_neg hi]
    have he : auxiliaryAction Φ U S i = fun _ => 0 := by
      funext q
      exact if_neg hi
    rw [he]
    simp [CompactGibbsContinuity.law, LocalGibbsComparison.weightedLaw]

theorem auxiliary_law_product (D : P → Finset I) (Φ : P → (I → X) → ℝ)
    (hΦc : ∀ p, Continuous (Φ p)) (hΦ : ∀ p, DependsOn (Φ p) (D p : Set I))
    (U : I → X) (S : Finset I) (hS : Independent D S) :
    CompactGibbsContinuity.law (Measure.pi (fun _ : I => μ))
        (fun V => action Φ (overwrite S U V)) =
      Measure.pi (fun i => if i ∈ S then coordinateLaw μ Φ i U else μ) := by
  rw [funext (action_sum D Φ hΦ U S hS)]
  rw [WilsonParallelConditional.affine_product_law _ _ (auxiliaryAction_continuous Φ hΦc U S)]
  congr 1
  funext i
  exact auxiliaryAction_law μ Φ hΦc U S i

theorem overwrite_map_auxiliaryLaw (D : P → Finset I) (Φ : P → (I → X) → ℝ)
    (hΦc : ∀ p, Continuous (Φ p)) (hΦ : ∀ p, DependsOn (Φ p) (D p : Set I))
    (U : I → X) (S : Finset I) (hS : Independent D S) :
    (CompactGibbsContinuity.law (Measure.pi (fun _ : I => μ))
      (fun V => action Φ (overwrite S U V))).map (overwrite S U) =
      Measure.pi (fun i => if i ∈ S then coordinateLaw μ Φ i U else Measure.dirac (U i)) := by
  rw [auxiliary_law_product μ D Φ hΦc hΦ U S hS]
  let ν : I → Measure X := fun i => if i ∈ S then coordinateLaw μ Φ i U else μ
  let f : I → X → X := fun i q => if i ∈ S then q else U i
  have hν (i : I) : IsProbabilityMeasure (ν i) := by
    dsimp only [ν]
    split
    · exact coordinateLaw_probability μ Φ hΦc i U
    · infer_instance
  letI (i : I) : IsProbabilityMeasure (ν i) := hν i
  have hf (i : I) : Measurable (f i) := by
    dsimp only [f]
    split
    · exact measurable_id
    · exact measurable_const
  change (Measure.pi ν).map (fun V i => f i (V i)) = _
  rw [Measure.pi_map_pi (fun i => (hf i).aemeasurable)]
  congr 1
  funext i
  by_cases hi : i ∈ S
  · simp [ν, f, hi]
  · simp [ν, f, hi, Measure.map_const]

/-- Exact identification with the genuine conditional-expectation operator. -/
theorem blockAverage_eq_parallelAverage (D : P → Finset I) (Φ : P → (I → X) → ℝ)
    (hΦc : ∀ p, Continuous (Φ p)) (hΦ : ∀ p, DependsOn (Φ p) (D p : Set I))
    (U : I → X) (S : Finset I) (hS : Independent D S) (F : C(I → X, ℝ)) :
    CompactGibbsBlockUpdate.blockAverage μ (actionMap Φ hΦc) S F U =
      ParallelOscillation.parallelAverage (coordinateLaw μ Φ) S F U := by
  rw [CompactGibbsBlockFiber.blockAverage_full_fiber]
  change (∫ V, F (overwrite S U V) ∂CompactGibbsContinuity.law
    (Measure.pi (fun _ : I => μ)) (fun V => action Φ (overwrite S U V))) = _
  change _ = ∫ V, F V ∂Measure.pi
    (fun i => if i ∈ S then coordinateLaw μ Φ i U else Measure.dirac (U i))
  rw [← overwrite_map_auxiliaryLaw μ D Φ hΦc hΦ U S hS]
  exact (integral_map (overwrite S U).continuous.measurable.aemeasurable
    F.continuous.aestronglyMeasurable).symm

end
end UnifiedTheory.Clay.YangMills.FiniteFactorParallelKernel
