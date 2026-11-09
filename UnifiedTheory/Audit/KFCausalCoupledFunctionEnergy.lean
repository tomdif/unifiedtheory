/- Exact change-of-variables energy for noncompact square-integrable
functions, with actual integrability rather than a totalized integral. -/
import UnifiedTheory.Audit.KFCausalCoupledLpCoordinates
import UnifiedTheory.Audit.KFCausalPositiveMultiplierEnergy

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalCoupledFunctionEnergy
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow
open UnifiedTheory.Audit.KFCausalCoupledCoordinateHomeomorph
open UnifiedTheory.Audit.KFCausalCoupledTestPullback
open UnifiedTheory.Audit.KFCausalCoupledUnitaryCoordinates
open UnifiedTheory.Audit.KFCausalCoupledLpCoordinates
open UnifiedTheory.Audit.KFCausalPositiveMultiplierEnergy

theorem toLp_square_integral {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (f : X → ℂ) (hf : MemLp f 2 μ) : ‖hf.toLp f‖^2 = ∫ x, ‖f x‖^2 ∂μ := by
  rw [l2_norm_square]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx]

theorem weighted_square_integral (ε : ℝ) (hε : 0 < ε) (f : Configuration → ℂ) (hf : MemLp f 2) :
    (∫ x, ‖weightedFunction ε hε f x‖^2) = ∫ x, ‖f x‖^2 := by
  rw [← toLp_square_integral _ (weighted_memLp ε hε f hf),← coordinates_toLp ε hε f hf,
    coordinates_norm,toLp_square_integral]

theorem inverse_square_integral (ε : ℝ) (hε : 0 < ε) (f : Configuration → ℂ) (hf : MemLp f 2) :
    (∫ x, ‖inverseFunction ε hε f x‖^2) = ∫ x, ‖f x‖^2 := by
  rw [← toLp_square_integral _ (inverse_memLp ε hε f hf),← coordinates_inverse_toLp ε hε f hf,
    LinearIsometryEquiv.norm_map,toLp_square_integral]

theorem weighted_square_integrable_iff (ε : ℝ) (hε : 0 < ε)
    (f : Configuration → ℂ) (hf : Measurable f) :
    Integrable (fun x => ‖weightedFunction ε hε f x‖^2) ↔ Integrable (fun x => ‖f x‖^2) := by
  have hm : Measurable (weightedFunction ε hε f) :=
    (weight_continuous ε).measurable.mul (hf.comp (coordinateHomeomorph ε hε).continuous.measurable)
  rw [← memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable,weighted_memLp_iff,
    memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable]

theorem weighted_density (ε : ℝ) (hε : 0 < ε) (f : Configuration → ℂ) (x : Configuration) :
    ‖weightedFunction ε hε f x‖^2 =
      (Real.exp x.1+ε)*Real.exp (2*(-phase ε x.1))*‖f (coordinateHomeomorph ε hε x)‖^2 := by
  change ‖(amplitude ε x.1:ℂ)*f (coordinateHomeomorph ε hε x)‖^2 = _
  rw [norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (amplitude_positive ε x.1 hε),amplitude_square ε x.1 hε]

theorem jacobian_square_integral (ε : ℝ) (hε : 0 < ε) (f : Configuration → ℂ) (hf : MemLp f 2) :
    (∫ x : Configuration, (Real.exp x.1+ε)*Real.exp (2*(-phase ε x.1))*
      ‖f (coordinateHomeomorph ε hε x)‖^2) = ∫ x, ‖f x‖^2 := by
  simpa only [weighted_density] using weighted_square_integral ε hε f hf

theorem jacobian_square_integrable_iff (ε : ℝ) (hε : 0 < ε)
    (f : Configuration → ℂ) (hf : Measurable f) :
    Integrable (fun x : Configuration => (Real.exp x.1+ε)*Real.exp (2*(-phase ε x.1))*
      ‖f (coordinateHomeomorph ε hε x)‖^2) ↔ Integrable (fun x => ‖f x‖^2) := by
  simpa only [weighted_density] using weighted_square_integrable_iff ε hε f hf

#print axioms toLp_square_integral
#print axioms weighted_square_integral
#print axioms inverse_square_integral
#print axioms weighted_square_integrable_iff
#print axioms weighted_density
#print axioms jacobian_square_integral
#print axioms jacobian_square_integrable_iff

end
end UnifiedTheory.Audit.KFCausalCoupledFunctionEnergy
