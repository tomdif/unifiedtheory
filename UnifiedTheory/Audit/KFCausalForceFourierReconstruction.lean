/- The weak Schwartz balance reconstructs the finite net force Fourier
transform from endpoint measures at every nonzero frequency. -/
import UnifiedTheory.Audit.KFCausalForceFourierSeparation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 450000

namespace UnifiedTheory.Audit.KFCausalForceFourierReconstruction
noncomputable section
open MeasureTheory Filter Set SchwartzMap
open scoped Topology FourierTransform ContDiff
open UnifiedTheory.Audit.KFCausalNeutralForceMeasure (FluxPair)
open UnifiedTheory.Audit.KFCausalSchwartzForceFourier
open UnifiedTheory.Audit.KFCausalForceFourierSeparation

def residual (F : FluxPair) (μ ν : Measure ℝ) (v : ℝ) : ℂ :=
  Complex.I*(frequency v : ℂ)*F.fourier (frequency v)-
    (charFun ν (frequency v)-charFun μ (frequency v))

variable (F : FluxPair) (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]

theorem residual_continuous : Continuous (residual F μ ν) := by
  have hc : Continuous frequency := by unfold frequency; fun_prop
  exact ((continuous_const.mul (Complex.continuous_ofReal.comp hc)).mul
    ((force_fourier_continuous F).comp hc)).sub
    (((characteristic_continuous ν).comp hc).sub ((characteristic_continuous μ).comp hc))

variable (h : ∀ f : 𝓢(ℝ,ℂ), (∫ p, f p ∂ν)-(∫ p, f p ∂μ) =
  F.evaluate (derivCLM ℂ ℂ f).toBoundedContinuousFunction)

include h in
theorem residual_test_zero (f : 𝓢(ℝ,ℂ)) : (∫ v, f v*residual F μ ν v) = 0 := by
  have hi : Integrable (fun v => f v*charFun ν (frequency v)-f v*charFun μ (frequency v)) :=
    (characteristic_test_integrable ν f).sub (characteristic_test_integrable μ f)
  calc
    _ = (∫ v, f v*(Complex.I*(frequency v : ℂ)*F.fourier (frequency v)))-
        ((∫ v, f v*charFun ν (frequency v))-(∫ v, f v*charFun μ (frequency v))) := by
      rw [← integral_sub (characteristic_test_integrable ν f) (characteristic_test_integrable μ f),
        ← integral_sub (force_derivative_integrable F f) hi]
      apply integral_congr_ae
      filter_upwards with v
      dsimp [residual]
      ring
    _ = 0 := by
      rw [← force_derivative_pairing F f,← measure_fourier_pairing ν f,
        ← measure_fourier_pairing μ f,h (𝓕 f),sub_self]

include h in
theorem residual_zero : residual F μ ν = fun _ => 0 := by
  have hc := residual_continuous F μ ν
  have he : ∀ᵐ v ∂volume, residual F μ ν v = 0 := by
    apply ae_eq_zero_of_integral_contDiff_smul_eq_zero hc.locallyIntegrable
    intro g hg hcompact
    let f : 𝓢(ℝ,ℂ) :=
      (hcompact.comp_left Complex.ofReal_zero).toSchwartzMap (Complex.ofRealCLM.contDiff.comp hg)
    simpa only [Complex.real_smul] using residual_test_zero F μ ν h f
  exact Measure.eq_of_ae_eq he hc continuous_const

include h in
theorem fourier_balance (v : ℝ) :
    Complex.I*(v : ℂ)*F.fourier v = charFun ν v-charFun μ v := by
  have hf : frequency (v/(-2*Real.pi)) = v := by unfold frequency; field_simp
  have he := congrFun (residual_zero F μ ν h) (v/(-2*Real.pi))
  change Complex.I*(frequency (v/(-2*Real.pi)) : ℂ)*F.fourier (frequency (v/(-2*Real.pi)))-
    (charFun ν (frequency (v/(-2*Real.pi)))-charFun μ (frequency (v/(-2*Real.pi)))) = 0 at he
  rw [hf] at he
  exact sub_eq_zero.mp he

include h in
theorem fourier_reconstruction (v : ℝ) (hv : v ≠ 0) :
    F.fourier v = (charFun ν v-charFun μ v)/(Complex.I*(v : ℂ)) := by
  apply (eq_div_iff (mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hv))).mpr
  rw [mul_comm]
  exact fourier_balance F μ ν h v

#print axioms residual_continuous
#print axioms residual_test_zero
#print axioms residual_zero
#print axioms fourier_balance
#print axioms fourier_reconstruction
end
end UnifiedTheory.Audit.KFCausalForceFourierReconstruction
