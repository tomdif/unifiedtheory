/- Exact reordering of the original Joint measure into the charged
variables and the neutral coordinate, transporting integrability as well
as the integral. This preserves the positive-Y restriction. -/
import UnifiedTheory.Audit.KFCausalChargedMarginalReordering
import UnifiedTheory.Audit.KFCausalChargedFourierGaussianMoments

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalJointChargedNeutralReordering
noncomputable section
open MeasureTheory
open KFCausalReciprocalNeutralLaplace (Joint jointMeasure)
open KFCausalChargedFourierGaussianMoments (Charged chargedMeasure)
local instance : SFinite chargedMeasure := by unfold chargedMeasure; infer_instance

private def reorder : Joint ≃ᵐ Charged×ℝ :=
  (((MeasurableEquiv.prodCongr
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) MeasurableEquiv.finTwoArrow)
      (MeasurableEquiv.refl ℝ)).trans
    (MeasurableEquiv.prodCongr MeasurableEquiv.prodAssoc.symm (MeasurableEquiv.refl ℝ))).trans
    MeasurableEquiv.prodAssoc).trans
    ((MeasurableEquiv.prodCongr (MeasurableEquiv.refl (ℝ×ℝ)) MeasurableEquiv.prodComm).trans
      MeasurableEquiv.prodAssoc.symm)

private theorem reorder_preserving :
    MeasurePreserving reorder jointMeasure (chargedMeasure.prod volume) := by
  let μ : Measure ℝ := volume
  let ν : Measure ℝ := volume.restrict (Set.Ioi (0:ℝ))
  have h0 : MeasurePreserving (MeasurableEquiv.prodCongr
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) MeasurableEquiv.finTwoArrow)
      (MeasurableEquiv.refl ℝ)) jointMeasure ((μ.prod (μ.prod μ)).prod ν) := by
    unfold jointMeasure
    rw [Measure.volume_eq_prod ℝ (Fin 2→ℝ)]
    exact ((MeasurePreserving.id _).prod (volume_preserving_finTwoArrow ℝ)).prod
      (MeasurePreserving.id _)
  have h1 := ((measurePreserving_prodAssoc μ μ μ).symm).prod (MeasurePreserving.id ν)
  have h2 := measurePreserving_prodAssoc (μ.prod μ) μ ν
  have h3 := (MeasurePreserving.id (μ.prod μ)).prod
    (Measure.measurePreserving_swap (μ := μ) (ν := ν))
  have h4 := (measurePreserving_prodAssoc (μ.prod μ) ν μ).symm
  exact h4.comp (h3.comp (h2.comp (h1.comp h0)))

private theorem inverse_apply (q : Charged×ℝ) :
    reorder.symm q=((q.1.1.1,![q.1.1.2,q.2]),q.1.2) := rfl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
theorem integrable_iff (f : Joint→E) :
    Integrable (fun q : Charged×ℝ=>f ((q.1.1.1,![q.1.1.2,q.2]),q.1.2))
      (chargedMeasure.prod volume) ↔ Integrable f jointMeasure := by
  simpa only [Function.comp_def,inverse_apply] using
    reorder_preserving.symm.integrable_comp_emb reorder.symm.measurableEmbedding (g:=f)

theorem integral_order (f : Joint→E) (hf : Integrable f jointMeasure) :
    (∫z,f z ∂jointMeasure)=∫q:Charged,(∫x:ℝ,f ((q.1.1,![q.1.2,x]),q.2)) ∂chargedMeasure := by
  have he := reorder_preserving.symm.integral_comp reorder.symm.measurableEmbedding f
  simp only [inverse_apply] at he
  rw [←he,integral_prod _ ((integrable_iff f).mpr hf)]

theorem marginal_integrable (f : Joint→E) (hf : Integrable f jointMeasure) :
    Integrable (fun q:Charged=>∫x:ℝ,f ((q.1.1,![q.1.2,x]),q.2)) chargedMeasure :=
  ((integrable_iff f).mpr hf).integral_prod_left

#print axioms integrable_iff
#print axioms integral_order
#print axioms marginal_integrable
end
end UnifiedTheory.Audit.KFCausalJointChargedNeutralReordering
