/- Fourier pairing of finite force measures with Schwartz tests. All
interchanges are justified by integrable product bounds. -/
import UnifiedTheory.Audit.KFCausalVanishingForceTests
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 350000

namespace UnifiedTheory.Audit.KFCausalSchwartzForceFourier
noncomputable section
open MeasureTheory Filter SchwartzMap
open scoped Topology FourierTransform
open UnifiedTheory.Audit.KFCausalNeutralForceMeasure (FluxPair)

def frequency (v : ℝ) : ℝ := -2*Real.pi*v

theorem measure_fourier_pairing (μ : Measure ℝ) [IsFiniteMeasure μ] (f : 𝓢(ℝ,ℂ)) :
    (∫ p, (𝓕 f) p ∂μ) = ∫ v, f v * charFun μ (frequency v) := by
  have hnorm (v p : ℝ) : ‖Complex.exp ((frequency v : ℂ)*(p:ℂ)*Complex.I)‖ = 1 := by
    simp [Complex.norm_exp]
  have hi : Integrable (fun z : ℝ × ℝ =>
      Complex.exp ((frequency z.1:ℂ)*(z.2:ℂ)*Complex.I) * f z.1) (volume.prod μ) := by
    apply (f.integrable.norm.mul_prod (integrable_const (1:ℝ))).mono
    · apply Continuous.aestronglyMeasurable
      dsimp [frequency]
      fun_prop
    · filter_upwards with z
      simp [hnorm]
  calc
    _ = ∫ p, ∫ v, Complex.exp ((frequency v:ℂ)*(p:ℂ)*Complex.I) * f v ∂volume ∂μ := by
      congr with p
      rw [fourier_coe,Real.fourier_real_eq_integral_exp_smul]
      simp only [frequency,Complex.ofReal_mul,smul_eq_mul]
    _ = ∫ v, ∫ p, Complex.exp ((frequency v:ℂ)*(p:ℂ)*Complex.I) * f v ∂μ :=
      integral_integral_swap hi.swap
    _ = _ := by
      congr with v
      rw [integral_mul_const,charFun_apply_real]
      exact mul_comm _ _

theorem characteristic_test_integrable (μ : Measure ℝ) [IsFiniteMeasure μ]
    (f : 𝓢(ℝ,ℂ)) : Integrable (fun v => f v * charFun μ (frequency v)) := by
  apply (f.integrable.norm.mul_const (μ.real Set.univ)).mono'
  · exact f.continuous.aestronglyMeasurable.mul
      ((stronglyMeasurable_charFun (μ := μ)).comp_measurable (show Measurable frequency by unfold frequency; fun_prop)).aestronglyMeasurable
  · filter_upwards with v
    simpa only [norm_mul] using mul_le_mul_of_nonneg_left (norm_charFun_le (μ := μ) (frequency v)) (norm_nonneg (f v))

theorem force_fourier_pairing (F : FluxPair) (f : 𝓢(ℝ,ℂ)) :
    F.evaluate (𝓕 f).toBoundedContinuousFunction = ∫ v, f v * F.fourier (frequency v) := by
  simp only [FluxPair.evaluate,SchwartzMap.toBoundedContinuousFunction_apply,measure_fourier_pairing]
  simp only [FluxPair.fourier,← mul_div_assoc,mul_sub]
  rw [integral_div,integral_sub (characteristic_test_integrable F.positive f)
    (characteristic_test_integrable F.negative f)]

def multiplier (f : 𝓢(ℝ,ℂ)) : 𝓢(ℝ,ℂ) :=
  -(2*Real.pi*Complex.I) • smulLeftCLM ℂ (inner ℝ · (1:ℝ)) f

theorem multiplier_apply (f : 𝓢(ℝ,ℂ)) (v : ℝ) :
    multiplier f v = f v * (Complex.I*(frequency v:ℂ)) := by
  have ht : (inner ℝ · (1:ℝ)).HasTemperateGrowth := by fun_prop
  simp only [multiplier,SchwartzMap.smul_apply,smulLeftCLM_apply_apply ht]
  simp [frequency,smul_eq_mul]
  ring

theorem derivative_fourier (f : 𝓢(ℝ,ℂ)) :
    derivCLM ℂ ℂ (𝓕 f) = 𝓕 (multiplier f) := by
  unfold multiplier
  rw [← SchwartzMap.lineDerivOp_fourier_eq f (1:ℝ)]
  ext p
  rfl

theorem force_derivative_pairing (F : FluxPair) (f : 𝓢(ℝ,ℂ)) :
    F.evaluate (derivCLM ℂ ℂ (𝓕 f)).toBoundedContinuousFunction =
      ∫ v, f v * (Complex.I*(frequency v:ℂ)*F.fourier (frequency v)) := by
  rw [derivative_fourier,force_fourier_pairing]
  congr with v
  rw [multiplier_apply,mul_assoc]

#print axioms measure_fourier_pairing
#print axioms characteristic_test_integrable
#print axioms force_fourier_pairing
#print axioms multiplier_apply
#print axioms derivative_fourier
#print axioms force_derivative_pairing
end
end UnifiedTheory.Audit.KFCausalSchwartzForceFourier
