/- The actual L2 Fourier transform agrees almost everywhere with the
ordinary Fourier integral on L1 intersect L2. Schwartz duality and the
fundamental lemma for locally integrable functions prove the identification. -/
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalL2FourierIntegral
noncomputable section
open MeasureTheory
open scoped FourierTransform ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem fourier_test_pairing (f : E → ℂ) (h₁ : Integrable f) (h₂ : MemLp f 2)
    (φ : SchwartzMap E ℂ) :
    (∫ x, φ x*((Lp.fourierTransformₗᵢ E ℂ) (h₂.toLp f)) x) = ∫ x, φ x*(𝓕 f) x := by
  have hd := congrArg (fun T : TemperedDistribution E ℂ => T φ)
    (Lp.fourier_toTemperedDistribution_eq (h₂.toLp f))
  simp only [TemperedDistribution.fourier_apply,Lp.toTemperedDistribution_apply,smul_eq_mul] at hd
  calc
    _ = ∫ x, (𝓕 φ) x*(h₂.toLp f) x := hd.symm
    _ = ∫ x, (𝓕 φ) x*f x := by
      apply integral_congr_ae
      filter_upwards [h₂.coeFn_toLp] with x hx
      rw [hx]
    _ = _ := by
      simpa using VectorFourier.integral_bilin_fourierIntegral_eq_flip
        (ContinuousLinearMap.mul ℂ ℂ) (L := innerₗ E) Real.continuous_fourierChar
        continuous_inner φ.integrable h₁

theorem fourier_toLp_coe (f : E → ℂ) (h₁ : Integrable f) (h₂ : MemLp f 2) :
    (Lp.fourierTransformₗᵢ E ℂ) (h₂.toLp f) =ᵐ[volume] 𝓕 f := by
  have hc : Continuous (𝓕 f) := VectorFourier.fourierIntegral_continuous
    (L := innerₗ E) Real.continuous_fourierChar continuous_inner h₁
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp ((Lp.fourierTransformₗᵢ E ℂ) (h₂.toLp f))).locallyIntegrable (by norm_num)) hc.locallyIntegrable
  intro g hg hs
  have hs' : HasCompactSupport (Complex.ofRealCLM ∘ g) := hs.comp_left rfl
  have hg' : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) := by fun_prop
  let φ : SchwartzMap E ℂ := hs'.toSchwartzMap hg'
  simpa [φ,Complex.real_smul] using fourier_test_pairing f h₁ h₂ φ

theorem integralFourier_memLp (f : E → ℂ) (h₁ : Integrable f) (h₂ : MemLp f 2) :
    MemLp (𝓕 f) 2 :=
  (Lp.memLp ((Lp.fourierTransformₗᵢ E ℂ) (h₂.toLp f))).ae_eq (fourier_toLp_coe f h₁ h₂)

theorem fourier_toLp_eq (f : E → ℂ) (h₁ : Integrable f) (h₂ : MemLp f 2) :
    (Lp.fourierTransformₗᵢ E ℂ) (h₂.toLp f) = (integralFourier_memLp f h₁ h₂).toLp (𝓕 f) := by
  apply Lp.ext
  exact (fourier_toLp_coe f h₁ h₂).trans (integralFourier_memLp f h₁ h₂).coeFn_toLp.symm

#print axioms fourier_test_pairing
#print axioms fourier_toLp_coe
#print axioms integralFourier_memLp
#print axioms fourier_toLp_eq

end
end UnifiedTheory.Audit.KFCausalL2FourierIntegral
