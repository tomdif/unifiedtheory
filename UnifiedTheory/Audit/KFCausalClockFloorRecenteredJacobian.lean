/- Exact change of variables for a displaced transverse packet. The real
dilation/shear and the five-dimensional concentration scale both contribute
to the Jacobian. No limit or integrability interchange is used here. -/
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedLineDensity
import UnifiedTheory.Audit.KFCausalTransverseDilationPullback
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalClockFloorRecenteredJacobian
noncomputable section
open MeasureTheory Set
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse flow flow_bijective)
open UnifiedTheory.Audit.KFCausalTransverseDilationPullback
open UnifiedTheory.Audit.KFCausalClockFloorGroupedCoordinates
open UnifiedTheory.Audit.KFCausalClockFloorShearBounds (Grouped)
open UnifiedTheory.Audit.KFCausalClockFloorBoostedRescaling (scale scale_positive)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedLineDensity (recenter)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedShiftPhase (grouped)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedPhaseLimit (rescaledPosition)

theorem flow_integral (t : ℝ) (f : Transverse → ℝ) :
    (∫ x, f x) = Real.exp (2*t)*(∫ x, f (flow t x)) := by
  have he := integral_image_eq_integral_abs_det_fderiv_smul (μ := volume)
    (f := flow t) (f' := fun _ => flowCLM t) MeasurableSet.univ
    (fun x _ => (flowCLM t).hasFDerivAt.hasFDerivWithinAt)
    (flow_bijective t).1.injOn f
  simpa only [image_univ,(flow_bijective t).2.range_eq,setIntegral_univ,
    flowCLM_det,abs_of_pos (Real.exp_pos _),smul_eq_mul,integral_const_mul] using he

theorem translate_scale_integral (Q : Transverse) (c : ℝ) (hc : 0 < c)
    (f : Transverse → ℝ) :
    (∫ x, f x) = c^5*(∫ ξ, f (Q+c • ξ)) := by
  have hd : Module.finrank ℝ Transverse = 5 := by simp [Transverse]
  have he := Measure.integral_comp_smul_of_nonneg (volume : Measure Transverse)
    (fun x => f (Q+x)) c (hR := hc.le)
  simp only [hd,smul_eq_mul,integral_add_left_eq_self] at he
  rw [he,mul_inv_cancel_left₀ (pow_ne_zero 5 hc.ne')]

theorem grouped_eq (x : Transverse) : grouped x = transverseGrouping x := by
  rw [transverseGrouping_apply]
  apply Prod.ext
  · funext i
    fin_cases i <;> rfl
  · rfl

def clockJacobian (ε : ℝ) (hε : 0 < ε) (u : ℝ) : ℝ :=
  Real.exp (-2*((KFCausalRegularizedLongitudinalChart.chartIso ε hε).symm u))

theorem recenter_integral (ε : ℝ) (hε : 0 < ε) (u h : ℝ) (hh : h ≠ 0)
    (Q : Transverse) (f : Grouped → ℝ) :
    (∫ x, f x) = clockJacobian ε hε u*(scale h)^5*
      (∫ ξ : Transverse, f (recenter ε hε u h Q ξ)) := by
  rw [← transverseGrouping_preserves_volume.integral_comp transverseGrouping.measurableEmbedding f]
  rw [flow_integral (-((KFCausalRegularizedLongitudinalChart.chartIso ε hε).symm u))]
  rw [translate_scale_integral Q (scale h) (scale_positive h hh)]
  simp only [recenter,grouped_eq,clockJacobian]
  have hr (ξ : Transverse) : rescaledPosition h Q ξ = Q+scale h • ξ := rfl
  simp_rw [hr]
  simp only [mul_neg,neg_mul]
  ring

#print axioms flow_integral
#print axioms translate_scale_integral
#print axioms grouped_eq
#print axioms recenter_integral

end
end UnifiedTheory.Audit.KFCausalClockFloorRecenteredJacobian
