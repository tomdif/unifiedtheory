/- Actual finite-product Gibbs block updates, transported from their original
law to outside/inside coordinates. Stationarity and projection properties
are consequences, not assumptions about a supplied Markov kernel. -/
import UnifiedTheory.Clay.YangMills.CompactGibbsResampling
import UnifiedTheory.Clay.YangMills.WilsonBlockMarginal

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.CompactGibbsBlockUpdate
noncomputable section
open MeasureTheory WilsonBlockMarginal

variable {I G : Type*} [Fintype I] [DecidableEq I]
  [TopologicalSpace G] [CompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [IsProbabilityMeasure μ]

omit [Fintype I] [CompactSpace G] [SecondCountableTopology G] [BorelSpace G] in
theorem assemble_symm_continuous (S : Finset I) :
    Continuous (assemble (G := G) S).symm := by
  have he : ((assemble (G := G) S).symm : (I → G) → Outside S × Inside S) =
      fun U => ((fun i : {i : I // i ∉ S} => U i), (fun i : {i : I // i ∈ S} => U i)) := by
    funext U
    apply (assemble S).injective
    simp only [MeasurableEquiv.apply_symm_apply]
    ext i
    by_cases hi : i ∈ S
    · simp [assemble_inside, hi]
    · simp [assemble_outside, hi]
  rw [he]
  exact (continuous_pi (fun i => continuous_apply i.val)).prodMk
    (continuous_pi (fun i => continuous_apply i.val))

def join (S : Finset I) : C(Outside (G := G) S × Inside (G := G) S, I → G) :=
  ⟨assemble S, assemble_continuous S⟩

def split (S : Finset I) : C(I → G, Outside (G := G) S × Inside (G := G) S) :=
  ⟨(assemble S).symm, assemble_symm_continuous S⟩

omit [Fintype I] [CompactSpace G] [SecondCountableTopology G] [BorelSpace G] in
theorem join_split (S : Finset I) (U : I → G) : join S (split S U) = U :=
  (assemble S).apply_symm_apply U

omit [Fintype I] [CompactSpace G] [SecondCountableTopology G] [BorelSpace G] in
theorem split_join (S : Finset I) (z : Outside (G := G) S × Inside (G := G) S) :
    split S (join S z) = z := (assemble S).symm_apply_apply z

/-- The actual normalized conditional average over the selected coordinates. -/
def blockAverage (A : C(I → G, ℝ)) (S : Finset I) (F : C(I → G, ℝ)) : C(I → G, ℝ) :=
  ContinuousMap.comp
    (CompactGibbsResampling.average (insideMeasure S μ) (A.comp (join S)) (F.comp (join S)))
    (split S)

theorem blockAverage_join (A : C(I → G, ℝ)) (S : Finset I) (F : C(I → G, ℝ)) :
    (blockAverage μ A S F).comp (join S) =
      CompactGibbsResampling.average (insideMeasure S μ) (A.comp (join S))
        (F.comp (join S)) := by
  ext z
  simp only [blockAverage, ContinuousMap.comp_apply, split_join]

theorem blockAverage_apply (A : C(I → G, ℝ)) (S : Finset I) (F : C(I → G, ℝ))
    (U : I → G) :
    blockAverage μ A S F U =
      ∫ V, F (assemble S ((split S U).1, V))
        ∂CompactGibbsContinuity.law (insideMeasure S μ)
          (fun V => A (assemble S ((split S U).1, V))) :=
  CompactGibbsResampling.average_apply (insideMeasure S μ) _ _ (split S U)

theorem blockAverage_assemble (A : C(I → G, ℝ)) (S : Finset I) (F : C(I → G, ℝ))
    (z : Outside (G := G) S × Inside (G := G) S) :
    blockAverage μ A S F (assemble S z) =
      CompactGibbsResampling.average (insideMeasure S μ) (A.comp (join S))
        (F.comp (join S)) z := congrArg (fun f => f z) (blockAverage_join μ A S F)

omit [CompactSpace G] in
theorem coordinates_preserving (A : C(I → G, ℝ)) (S : Finset I) :
    MeasurePreserving (assemble (G := G) S)
      (CompactGibbsContinuity.law ((outsideMeasure S μ).prod (insideMeasure S μ))
        (A.comp (join S)))
      (CompactGibbsContinuity.law (Measure.pi (fun _ : I => μ)) A) :=
  weightedLaw_preserving _ _ (assemble S) (assemble_preserving S μ)
    (fun U => Real.exp (-A U)) (Real.continuous_exp.comp A.continuous.neg).measurable

omit [CompactSpace G] in
theorem integral_coordinates (A : C(I → G, ℝ)) (S : Finset I) (F : (I → G) → ℝ) :
    (∫ U, F U ∂CompactGibbsContinuity.law (Measure.pi (fun _ : I => μ)) A) =
      ∫ z, F (assemble S z) ∂CompactGibbsContinuity.law
        ((outsideMeasure S μ).prod (insideMeasure S μ)) (A.comp (join S)) :=
  ((coordinates_preserving μ A S).integral_comp (assemble S).measurableEmbedding F).symm

theorem blockAverage_const (A : C(I → G, ℝ)) (S : Finset I) (c : ℝ) :
    blockAverage μ A S (ContinuousMap.const _ c) = ContinuousMap.const _ c := by
  ext U
  change CompactGibbsResampling.average (insideMeasure S μ) (A.comp (join S))
    (ContinuousMap.const _ c) (split S U) = c
  rw [CompactGibbsResampling.average_const]
  rfl

theorem blockAverage_sub (A : C(I → G, ℝ)) (S : Finset I) (F H : C(I → G, ℝ)) :
    blockAverage μ A S (F - H) = blockAverage μ A S F - blockAverage μ A S H := by
  have he : (F - H).comp (join S) = F.comp (join S) - H.comp (join S) := rfl
  ext U
  simp only [blockAverage, he, CompactGibbsResampling.average_sub,
    ContinuousMap.comp_apply, ContinuousMap.sub_apply]

theorem blockAverage_idempotent (A : C(I → G, ℝ)) (S : Finset I) (F : C(I → G, ℝ)) :
    blockAverage μ A S (blockAverage μ A S F) = blockAverage μ A S F := by
  change (CompactGibbsResampling.average (insideMeasure S μ) (A.comp (join S))
    ((blockAverage μ A S F).comp (join S))).comp (split S) = _
  rw [blockAverage_join, CompactGibbsResampling.average_idempotent]
  rfl

theorem blockAverage_stationary (A : C(I → G, ℝ)) (S : Finset I) (F : C(I → G, ℝ)) :
    (∫ U, blockAverage μ A S F U ∂CompactGibbsContinuity.law (Measure.pi (fun _ : I => μ)) A) =
      ∫ U, F U ∂CompactGibbsContinuity.law (Measure.pi (fun _ : I => μ)) A := by
  rw [integral_coordinates μ A S, integral_coordinates μ A S F]
  have he (z : Outside (G := G) S × Inside (G := G) S) :
      blockAverage μ A S F (assemble S z) =
        CompactGibbsResampling.average (insideMeasure S μ) (A.comp (join S))
          (F.comp (join S)) z := congrArg (fun f => f z) (blockAverage_join μ A S F)
  simp_rw [he]
  exact CompactGibbsResampling.average_stationary (outsideMeasure S μ) (insideMeasure S μ) _ _

theorem blockAverage_reversible (A : C(I → G, ℝ)) (S : Finset I) (F H : C(I → G, ℝ)) :
    (∫ U, F U * blockAverage μ A S H U
      ∂CompactGibbsContinuity.law (Measure.pi (fun _ : I => μ)) A) =
      ∫ U, blockAverage μ A S F U * H U
        ∂CompactGibbsContinuity.law (Measure.pi (fun _ : I => μ)) A := by
  rw [integral_coordinates μ A S, integral_coordinates μ A S]
  simp_rw [blockAverage_assemble]
  exact CompactGibbsResampling.average_reversible (outsideMeasure S μ) (insideMeasure S μ)
    (A.comp (join S)) (F.comp (join S)) (H.comp (join S))

theorem blockAverage_nonnegative (A : C(I → G, ℝ)) (S : Finset I) (F : C(I → G, ℝ))
    (hF : ∀ U, 0 ≤ F U) (U : I → G) : 0 ≤ blockAverage μ A S F U := by
  rw [blockAverage_apply]
  exact integral_nonneg (fun V => hF _)

theorem block_dirichlet_eq_residual (A : C(I → G, ℝ)) (S : Finset I)
    (F : C(I → G, ℝ)) :
    (∫ U, F U * (F U - blockAverage μ A S F U)
      ∂CompactGibbsContinuity.law (Measure.pi (fun _ : I => μ)) A) =
      ∫ U, (F U - blockAverage μ A S F U)^2
        ∂CompactGibbsContinuity.law (Measure.pi (fun _ : I => μ)) A := by
  rw [integral_coordinates μ A S, integral_coordinates μ A S]
  simp_rw [blockAverage_assemble]
  exact CompactGibbsResampling.dirichlet_eq_residual (outsideMeasure S μ)
    (insideMeasure S μ) (A.comp (join S)) (F.comp (join S))

end
end UnifiedTheory.Clay.YangMills.CompactGibbsBlockUpdate
