/- The actual conditional block average also equals full auxiliary Gibbs
sampling followed by overwriting the selected coordinates. This supplies the
operator dictionary needed for product-kernel influence estimates. -/
import UnifiedTheory.Clay.YangMills.CompactGibbsBlockUpdate

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.CompactGibbsBlockFiber
noncomputable section
open MeasureTheory WilsonBlockMarginal CompactGibbsBlockUpdate

section Product
variable {B X : Type*}
  [TopologicalSpace B] [CompactSpace B] [SecondCountableTopology B]
  [MeasurableSpace B] [BorelSpace B]
  [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  (μB : Measure B) (μX : Measure X) [IsProbabilityMeasure μB] [IsProbabilityMeasure μX]

theorem law_snd_expectation (A F : C(X, ℝ)) :
    (∫ z, F z.2 ∂CompactGibbsContinuity.law (μB.prod μX) (fun z => A z.2)) =
      ∫ x, F x ∂CompactGibbsContinuity.law μX A := by
  have hi := LocalGibbsComparison.weighted_integral (μB.prod μX)
    (fun z => Real.exp (-A z.2))
    (Real.continuous_exp.comp (A.continuous.comp continuous_snd).neg).measurable
    (fun _ => (Real.exp_pos _).le)
    (CompactGibbsContinuity.partition_positive (μB.prod μX) _
      (A.continuous.comp continuous_snd)) (fun z => F z.2)
  have hj := LocalGibbsComparison.weighted_integral μX (fun x => Real.exp (-A x))
    (Real.continuous_exp.comp A.continuous.neg).measurable
    (fun _ => (Real.exp_pos _).le)
    (CompactGibbsContinuity.partition_positive μX A A.continuous) F
  change (∫ z, F z.2 ∂CompactGibbsContinuity.law (μB.prod μX) (fun z => A z.2)) = _ at hi
  change (∫ x, F x ∂CompactGibbsContinuity.law μX A) = _ at hj
  rw [hi, hj]
  rw [integral_fun_snd (fun x => Real.exp (-A x) * F x),
    integral_fun_snd (fun x => Real.exp (-A x))]
  simp
end Product

variable {I G : Type*} [Fintype I] [DecidableEq I]
  [TopologicalSpace G] [CompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [IsProbabilityMeasure μ]

def overwrite (S : Finset I) (U : I → G) : C(I → G, I → G) :=
  ⟨fun V i => if i ∈ S then V i else U i, by
    apply continuous_pi
    intro i
    by_cases hi : i ∈ S
    · simpa only [hi, ↓reduceIte] using (continuous_apply i : Continuous (fun V : I → G => V i))
    · simp only [hi, ↓reduceIte]
      exact continuous_const⟩

omit [Fintype I] [CompactSpace G] [SecondCountableTopology G] [BorelSpace G] in
theorem split_outside (S : Finset I) (U : I → G) (i : {i : I // i ∉ S}) :
    (split S U).1 i = U i := by
  have h := congrArg (fun V : I → G => V i) (join_split S U)
  simpa only [join, ContinuousMap.coe_mk, assemble_outside S _ i i.property] using h

omit [Fintype I] [CompactSpace G] [SecondCountableTopology G] [BorelSpace G] in
theorem overwrite_assemble (S : Finset I) (U : I → G)
    (z : Outside (G := G) S × Inside (G := G) S) :
    overwrite S U (assemble S z) = assemble S ((split S U).1, z.2) := by
  ext i
  by_cases hi : i ∈ S
  · simp only [overwrite, ContinuousMap.coe_mk, hi, ↓reduceIte, assemble_inside S _ i hi]
  · simp only [overwrite, ContinuousMap.coe_mk, hi, ↓reduceIte, assemble_outside S _ i hi,
      split_outside S U ⟨i, hi⟩]

/-- Sampling the full auxiliary Gibbs law and overwriting the block is
exactly the conditional-expectation operator for the original Gibbs law. -/
theorem blockAverage_full_fiber (A : C(I → G, ℝ)) (S : Finset I)
    (F : C(I → G, ℝ)) (U : I → G) :
    blockAverage μ A S F U =
      ∫ V, F (overwrite S U V) ∂CompactGibbsContinuity.law
        (Measure.pi (fun _ : I => μ)) (fun V => A (overwrite S U V)) := by
  change blockAverage μ A S F U = ∫ V, F (overwrite S U V)
    ∂CompactGibbsContinuity.law (Measure.pi (fun _ : I => μ)) (A.comp (overwrite S U))
  rw [integral_coordinates μ (A.comp (overwrite S U)) S (fun V => F (overwrite S U V))]
  have he : (A.comp (overwrite S U)).comp (join S) =
      ⟨fun z => A (assemble S ((split S U).1, z.2)), by
        exact A.continuous.comp ((assemble_continuous S).comp
          (continuous_const.prodMk continuous_snd))⟩ := by
    ext z
    exact congrArg A (overwrite_assemble S U z)
  rw [he]
  simp_rw [overwrite_assemble]
  let AF : C(Inside (G := G) S, ℝ) :=
    ⟨fun V => A (assemble S ((split S U).1, V)), A.continuous.comp
      ((assemble_continuous S).comp (continuous_const.prodMk continuous_id))⟩
  let FF : C(Inside (G := G) S, ℝ) :=
    ⟨fun V => F (assemble S ((split S U).1, V)), F.continuous.comp
      ((assemble_continuous S).comp (continuous_const.prodMk continuous_id))⟩
  exact (blockAverage_apply μ A S F U).trans
    (law_snd_expectation (outsideMeasure S μ) (insideMeasure S μ) AF FF).symm

end
end UnifiedTheory.Clay.YangMills.CompactGibbsBlockFiber
