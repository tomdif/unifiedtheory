/- Finite force fluxes are separated by derivatives of Schwartz tests.
Fourier duality excludes a nonzero constant-in-momentum finite flux. -/
import UnifiedTheory.Audit.KFCausalWeakForceBalance
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Measure.OpenPos

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 450000

namespace UnifiedTheory.Audit.KFCausalForceFourierSeparation
noncomputable section
open MeasureTheory Filter Set SchwartzMap
open scoped Topology FourierTransform ContDiff
open UnifiedTheory.Audit.KFCausalNeutralForceMeasure (FluxPair)
open UnifiedTheory.Audit.KFCausalSchwartzForceFourier

theorem characteristic_continuous (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Continuous (charFun μ) := by
  change Continuous (fun v => charFun μ v)
  simp only [charFun_eq_fourierIntegral]
  exact (VectorFourier.fourierIntegral_continuous Real.continuous_probChar
    continuous_inner (integrable_const (1 : ℂ))).comp continuous_neg

theorem force_fourier_continuous (F : FluxPair) : Continuous F.fourier :=
  ((characteristic_continuous F.positive).sub
    (characteristic_continuous F.negative)).div_const 2

theorem force_test_integrable (F : FluxPair) (f : 𝓢(ℝ,ℂ)) :
    Integrable (fun v => f v*F.fourier (frequency v)) := by
  simpa only [FluxPair.fourier,Pi.sub_apply,← mul_div_assoc,mul_sub] using
    ((characteristic_test_integrable F.positive f).sub
      (characteristic_test_integrable F.negative f)).div_const (2 : ℂ)

theorem force_derivative_integrable (F : FluxPair) (f : 𝓢(ℝ,ℂ)) :
    Integrable (fun v => f v*(Complex.I*(frequency v : ℂ)*F.fourier (frequency v))) := by
  simpa only [multiplier_apply,mul_assoc] using force_test_integrable F (multiplier f)

def derivativeDifference (F G : FluxPair) (v : ℝ) : ℂ :=
  Complex.I*(frequency v : ℂ)*(F.fourier (frequency v)-G.fourier (frequency v))

theorem derivativeDifference_continuous (F G : FluxPair) :
    Continuous (derivativeDifference F G) := by
  have hc : Continuous frequency := by unfold frequency; fun_prop
  exact (continuous_const.mul (Complex.continuous_ofReal.comp hc)).mul
    (((force_fourier_continuous F).comp hc).sub ((force_fourier_continuous G).comp hc))

theorem derivativeDifference_test_zero (F G : FluxPair)
    (h : ∀ f : 𝓢(ℝ,ℂ), F.evaluate (derivCLM ℂ ℂ f).toBoundedContinuousFunction =
      G.evaluate (derivCLM ℂ ℂ f).toBoundedContinuousFunction) (f : 𝓢(ℝ,ℂ)) :
    (∫ v, f v*derivativeDifference F G v) = 0 := by
  calc
    _ = (∫ v, f v*(Complex.I*(frequency v : ℂ)*F.fourier (frequency v)))-
        (∫ v, f v*(Complex.I*(frequency v : ℂ)*G.fourier (frequency v))) := by
      rw [← integral_sub (force_derivative_integrable F f) (force_derivative_integrable G f)]
      apply integral_congr_ae
      filter_upwards with v
      dsimp [derivativeDifference]
      ring
    _ = 0 := by
      rw [← force_derivative_pairing F f,← force_derivative_pairing G f,h (𝓕 f),sub_self]

theorem derivativeDifference_zero (F G : FluxPair)
    (h : ∀ f : 𝓢(ℝ,ℂ), F.evaluate (derivCLM ℂ ℂ f).toBoundedContinuousFunction =
      G.evaluate (derivCLM ℂ ℂ f).toBoundedContinuousFunction) :
    derivativeDifference F G = fun _ => 0 := by
  have hc := derivativeDifference_continuous F G
  have he : ∀ᵐ v ∂volume, derivativeDifference F G v = 0 := by
    apply ae_eq_zero_of_integral_contDiff_smul_eq_zero hc.locallyIntegrable
    intro g hg hcompact
    let f : 𝓢(ℝ,ℂ) :=
      (hcompact.comp_left Complex.ofReal_zero).toSchwartzMap (Complex.ofRealCLM.contDiff.comp hg)
    simpa only [Complex.real_smul] using derivativeDifference_test_zero F G h f
  exact MeasureTheory.Measure.eq_of_ae_eq he hc continuous_const

theorem fourier_eq_of_derivative_tests (F G : FluxPair)
    (h : ∀ f : 𝓢(ℝ,ℂ), F.evaluate (derivCLM ℂ ℂ f).toBoundedContinuousFunction =
      G.evaluate (derivCLM ℂ ℂ f).toBoundedContinuousFunction) : F.fourier = G.fourier := by
  apply Continuous.ext_on (dense_compl_singleton (0 : ℝ))
    (force_fourier_continuous F) (force_fourier_continuous G)
  intro v hv
  have hv0 : v ≠ 0 := hv
  have hf : frequency (v/(-2*Real.pi)) = v := by
    unfold frequency
    field_simp
  have he := congrFun (derivativeDifference_zero F G h) (v/(-2*Real.pi))
  change Complex.I*(frequency (v/(-2*Real.pi)) : ℂ)*
    (F.fourier (frequency (v/(-2*Real.pi)))-G.fourier (frequency (v/(-2*Real.pi)))) = 0 at he
  rw [hf] at he
  exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left
    (mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hv0)))

#print axioms characteristic_continuous
#print axioms force_fourier_continuous
#print axioms force_test_integrable
#print axioms force_derivative_integrable
#print axioms derivativeDifference_continuous
#print axioms derivativeDifference_test_zero
#print axioms derivativeDifference_zero
#print axioms fourier_eq_of_derivative_tests
end
end UnifiedTheory.Audit.KFCausalForceFourierSeparation
