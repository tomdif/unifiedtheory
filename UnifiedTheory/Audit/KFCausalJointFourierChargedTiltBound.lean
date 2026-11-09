/- The actual angular tilt estimate controls the full charged integral.
All absolute-integrability and polar-coordinate premises are discharged
for the original Fourier density, retaining every width interference term. -/
import UnifiedTheory.Audit.KFCausalPlanePolarComparison
import UnifiedTheory.Audit.KFCausalChargedFourierTiltIntegrability
import UnifiedTheory.Audit.KFCausalJointFourierAngularTilt

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalJointFourierChargedTiltBound
noncomputable section
open MeasureTheory Set
open KFCausalChargedFourierGaussianMoments (Charged chargedMeasure)
open KFCausalJointFourierMatrixIntegral (density)
open KFCausalJointFourierMomentMatrix (matrixEnergy)
open KFCausalReciprocalWedgeGeometry (gamma)

variable (n : ℕ) (β : ℝ) (w : Fin n → ℝ) (b c : Fin n → ℂ)
  (P : Fin n → Polynomial ℂ)

def chargedTilt (α : ℝ) (r : ℂ) (k : ℝ) : ℝ :=
  ∫ q : Charged, (-8*Real.pi*k*r.im*q.1.2)*density n β w b c P α r (q,k) ∂chargedMeasure

theorem charged_tilt_lower (hβ : 0 < β) (α : ℝ) (r : ℂ) (k : ℝ)
    (hp : 0 < (gamma α r).re) (hw : ∀ i, 0 < w i) :
    -2400*matrixEnergy n β w b c P α r k ≤ chargedTilt n β w b c P α r k := by
  have hd := KFCausalJointFourierMomentMatrix.slice_integrable n β w b c P α r k hp hw
  have ht := KFCausalChargedFourierTiltIntegrability.tilt_integrable n β w b c P α r k hp hw
  change Integrable (fun q : Charged => density n β w b c P α r (q,k)) chargedMeasure at hd
  change Integrable (fun q : Charged => (-8*Real.pi*k*r.im*q.1.2)*
    density n β w b c P α r (q,k)) chargedMeasure at ht
  have hl := hd.const_mul (-2400:ℝ)
  rw [← KFCausalJointFourierMomentMatrix.slice_matrix_integral n β w b c P α r k hp hw]
  change -2400*(∫ q : Charged, density n β w b c P α r (q,k) ∂chargedMeasure) ≤ _
  rw [← integral_const_mul]
  unfold chargedTilt chargedMeasure at *
  rw [integral_prod_symm _ hl,integral_prod_symm _ ht]
  apply integral_mono_ae hl.integral_prod_right ht.integral_prod_right
  filter_upwards [hd.prod_left_ae,ht.prod_left_ae] with Y hdY htY
  have hc : Continuous (fun q : ℝ × ℝ => density n β w b c P α r ((q,Y),k)) :=
    (KFCausalJointFourierMatrixIntegral.density_continuous n β w b c P hβ α r).comp
      (by fun_prop)
  have htC : Continuous (fun q : ℝ × ℝ => (-8*Real.pi*k*r.im*q.2)*
      density n β w b c P α r ((q,Y),k)) := by fun_prop
  rw [← Measure.volume_eq_prod ℝ ℝ] at hdY htY ⊢
  apply KFCausalPlanePolarComparison.integral_le_of_angular _ _
    (continuous_const.mul hc) htC (hdY.const_mul (-2400)) htY
  intro R _
  simp only [Pi.mul_apply]
  rw [intervalIntegral.integral_const_mul]
  exact KFCausalJointFourierAngularTilt.original_angular_tilt_lower n β w b c P α r R Y k

theorem actual_clock_charged_tilt_lower (α ε y s : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3)
    (hw : ∀ i, 1 ≤ w i) (k : ℝ) :
    -2400*matrixEnergy n β w b c P α (KFCausalClockFloorRelativeShift.scale ε y s) k ≤
      chargedTilt n β w b c P α (KFCausalClockFloorRelativeShift.scale ε y s) k := by
  exact charged_tilt_lower n β w b c P hβ α _ k
    (KFCausalJointFourierMatrixIntegral.gamma_positive α ε y s hα hε hy)
    (fun i => lt_of_lt_of_le (by norm_num) (hw i))

#print axioms charged_tilt_lower
#print axioms actual_clock_charged_tilt_lower
end
end UnifiedTheory.Audit.KFCausalJointFourierChargedTiltBound
