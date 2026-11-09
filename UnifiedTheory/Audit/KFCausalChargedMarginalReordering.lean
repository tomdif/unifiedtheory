/- Reorder the original joint measure into the outer physical variables
(v,x) and the charged marginal variables (u,Y). Integrability and the
integral identity are transported together; no pointwise slice assumption
is needed. -/
import UnifiedTheory.Audit.KFCausalChargedCoolingGramIntegral
import UnifiedTheory.Audit.KFCausalJointNeutralFourierOuterFubini

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalChargedMarginalReordering
noncomputable section
open MeasureTheory
open KFCausalReciprocalNeutralLaplace (Joint jointMeasure)
open KFCausalChargedCoolingGramIntegral (planeMeasure)

local instance : SFinite planeMeasure := by unfold planeMeasure; infer_instance

private def reorder : Joint ≃ᵐ (ℝ × ℝ) × (ℝ × ℝ) :=
  (MeasurableEquiv.prodCongr
    ((MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
      MeasurableEquiv.finTwoArrow).trans MeasurableEquiv.prodComm)
    (MeasurableEquiv.refl ℝ)).trans MeasurableEquiv.prodAssoc

private theorem reorder_preserving :
    MeasurePreserving reorder jointMeasure (volume.prod planeMeasure) := by
  have hfin : MeasurePreserving
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
        (MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ))
      (volume : Measure (ℝ × (Fin 2 → ℝ)))
      ((volume : Measure ℝ).prod (volume : Measure (ℝ × ℝ))) := by
    rw [Measure.volume_eq_prod ℝ (Fin 2 → ℝ)]
    exact (MeasurePreserving.id _).prod (volume_preserving_finTwoArrow ℝ)
  exact (measurePreserving_prodAssoc volume volume (volume.restrict (Set.Ioi 0))).comp
    ((Measure.measurePreserving_swap.comp hfin).prod (MeasurePreserving.id _))

private theorem reorder_symm_apply (q : (ℝ × ℝ) × (ℝ × ℝ)) :
    reorder.symm q = ((q.2.1, ![q.1.1,q.1.2]),q.2.2) := rfl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
theorem reordered_integrable_iff (f : Joint → E) :
    Integrable (fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
      f ((q.2.1, ![q.1.1,q.1.2]),q.2.2)) (volume.prod planeMeasure) ↔
      Integrable f jointMeasure := by
  simpa only [Function.comp_def,reorder_symm_apply] using
    (reorder_preserving.symm.integrable_comp_emb reorder.symm.measurableEmbedding
      (g := f))

theorem outer_integrable (f : Joint → E) (hf : Integrable f jointMeasure) :
    Integrable (fun q : ℝ × ℝ =>
      ∫ p : ℝ × ℝ, f ((p.1, ![q.1,q.2]),p.2) ∂planeMeasure) :=
  ((reordered_integrable_iff f).mpr hf).integral_prod_left

omit [NormedSpace ℝ E] in
theorem slice_integrable_ae (f : Joint → E) (hf : Integrable f jointMeasure) :
    ∀ᵐ q : ℝ × ℝ, Integrable
      (fun p : ℝ × ℝ => f ((p.1, ![q.1,q.2]),p.2)) planeMeasure :=
  ((reordered_integrable_iff f).mpr hf).prod_right_ae

theorem integral_order (f : Joint → E) (hf : Integrable f jointMeasure) :
    (∫ q : Joint, f q ∂jointMeasure) =
      ∫ q : ℝ × ℝ, ∫ p : ℝ × ℝ, f ((p.1, ![q.1,q.2]),p.2) ∂planeMeasure := by
  have he := reorder_preserving.symm.integral_comp
    reorder.symm.measurableEmbedding f
  simp only [reorder_symm_apply] at he
  rw [← he,integral_prod _ ((reordered_integrable_iff f).mpr hf)]

#print axioms reordered_integrable_iff
#print axioms outer_integrable
#print axioms slice_integrable_ae
#print axioms integral_order
end
end UnifiedTheory.Audit.KFCausalChargedMarginalReordering
