/- Conjugating a volume-preserving measurable equivalence by an invertible
linear coordinate change preserves Haar volume. The Jacobian factors cancel;
the coordinate change itself need not preserve volume. -/
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalHaarConjugation
noncomputable section
open MeasureTheory MeasureTheory.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

def conjugate (S : E ≃L[ℝ] E) (R : E ≃ᵐ E) : E ≃ᵐ E :=
  S.toHomeomorph.toMeasurableEquiv.trans (R.trans S.symm.toHomeomorph.toMeasurableEquiv)

omit [FiniteDimensional ℝ E] in
theorem conjugate_apply (S : E ≃L[ℝ] E) (R : E ≃ᵐ E) (x : E) :
    conjugate S R x = S.symm (R (S x)) := rfl

theorem conjugate_preserves (μ : Measure E) [IsAddHaarMeasure μ]
    (S : E ≃L[ℝ] E) (R : E ≃ᵐ E) (hR : MeasurePreserving R μ μ) :
    MeasurePreserving (conjugate S R) μ μ := by
  have hdet : LinearMap.det S.toLinearMap ≠ 0 := by
    simpa only [LinearEquiv.coe_det] using Units.ne_zero (LinearEquiv.det S.toLinearEquiv)
  have hS : Measure.map S μ = ENNReal.ofReal |(LinearMap.det S.toLinearMap)⁻¹| • μ :=
    map_linearMap_addHaar_eq_smul_addHaar μ hdet
  refine ⟨(conjugate S R).measurable, ?_⟩
  change Measure.map ((S.symm : E → E) ∘ ((R : E → E) ∘ (S : E → E))) μ = μ
  rw [← Measure.map_map S.symm.continuous.measurable (R.measurable.comp S.continuous.measurable),
    ← Measure.map_map R.measurable S.continuous.measurable, hS, Measure.map_smul, hR.map_eq,
    ← hS, Measure.map_map S.symm.continuous.measurable S.continuous.measurable]
  have he : (S.symm : E → E) ∘ (S : E → E) = id := funext S.symm_apply_apply
  rw [he, Measure.map_id]

#print axioms conjugate_apply
#print axioms conjugate_preserves

end
end UnifiedTheory.Audit.KFCausalHaarConjugation
