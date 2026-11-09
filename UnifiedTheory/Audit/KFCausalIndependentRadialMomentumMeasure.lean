/- Actual Haar change of variables for the two momentum coordinates of
the original Block 2 × Block 4 product. The four remaining coordinates
are fixed. The absolute Jacobian is c², including negative c. No physical
profile integrability or spherical symmetry is assumed. -/
import UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalIndependentRadialMomentumMeasure
noncomputable section
open MeasureTheory
open KFCausalEuclideanProductCoordinates (Block)

abbrev Product := Block 2 × Block 4

def scale (c : ℝ) (x : Product) : Product := (c • x.1,x.2)

def scaleEquiv (c : ℝ) (hc : c ≠ 0) : Product ≃ᵐ Product :=
  (MeasurableEquiv.smul₀ c hc).prodCongr (MeasurableEquiv.refl (Block 4))

theorem map_scale_volume (c : ℝ) (hc : c ≠ 0) :
    Measure.map (scale c) volume = ENNReal.ofReal ((|c|^2)⁻¹) • volume := by
  change Measure.map (Prod.map (fun x : Block 2 => c • x) (id : Block 4 → Block 4))
    (volume.prod volume) = _
  rw [← Measure.map_prod_map _ _ (measurable_const_smul c) measurable_id,
    Measure.map_id,Measure.map_addHaar_smul volume hc,Measure.prod_smul_left]
  simp only [finrank_euclideanSpace_fin,abs_inv,abs_pow]
  rfl

theorem scale_integrable_iff {E : Type*} [NormedAddCommGroup E]
    (c : ℝ) (hc : c ≠ 0) (F : Product → E) :
    Integrable (fun x => F (scale c x)) volume ↔ Integrable F volume := by
  have hm := integrable_map_equiv (μ := volume) (scaleEquiv c hc) F
  change Integrable F (Measure.map (scale c) volume) ↔
    Integrable (fun x => F (scale c x)) volume at hm
  rw [map_scale_volume c hc] at hm
  have hpos : 0 < (|c|^2)⁻¹ := inv_pos.mpr (pow_pos (abs_pos.mpr hc) 2)
  rw [integrable_smul_measure (ENNReal.ofReal_ne_zero_iff.mpr hpos)
    ENNReal.ofReal_ne_top] at hm
  exact hm.symm

theorem integral_scale {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : ℝ) (hc : c ≠ 0) (F : Product → E) :
    (∫ x, F (scale c x)) = (|c|^2)⁻¹ • ∫ x, F x := by
  have hm := integral_map_equiv (μ := volume) (scaleEquiv c hc) F
  change (∫ x, F x ∂Measure.map (scale c) volume) = ∫ x, F (scale c x) at hm
  rw [map_scale_volume c hc,integral_smul_measure,ENNReal.toReal_ofReal
    (inv_nonneg.mpr (sq_nonneg |c|))] at hm
  exact hm.symm

theorem inverse_scale_integrable_iff {E : Type*} [NormedAddCommGroup E]
    (c : ℝ) (hc : c ≠ 0) (F : Product → E) :
    Integrable (fun x : Product => F (c⁻¹ • x.1,x.2)) volume ↔ Integrable F volume :=
  scale_integrable_iff c⁻¹ (inv_ne_zero hc) F

theorem integral_eq_inverse_scale {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : ℝ) (hc : c ≠ 0) (F : Product → E) :
    (∫ x, F x) = (|c|^2)⁻¹ • ∫ x : Product, F (c⁻¹ • x.1,x.2) := by
  have hi := integral_scale c hc (fun x : Product => F (c⁻¹ • x.1,x.2))
  simpa only [scale,smul_smul,inv_mul_cancel₀ hc,one_smul] using hi

#print axioms map_scale_volume
#print axioms scale_integrable_iff
#print axioms integral_scale
#print axioms inverse_scale_integrable_iff
#print axioms integral_eq_inverse_scale
end
end UnifiedTheory.Audit.KFCausalIndependentRadialMomentumMeasure
