/- Fourier uniqueness for integrable functions, used to test density of
the proposed infinite-dimensional clock domain. No operator-domain or
continuum conclusion is assumed by this analytic lemma. -/
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalFourierUniqueness
noncomputable section
open MeasureTheory
open scoped FourierTransform ContDiff

theorem integral_fourier_mul (f g : ℝ → ℂ) (hf : Integrable f) (hg : Integrable g) :
    (∫ k, (𝓕 f) k*g k)=∫ q, f q*(𝓕 g) q := by
  have h := VectorFourier.integral_bilin_fourierIntegral_eq_flip
    (L := LinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℂ ℂ)
    Real.continuous_fourierChar (by fun_prop) hf hg
  simpa only [ContinuousLinearMap.mul_apply',VectorFourier.fourierIntegral,
    LinearMap.mul_apply',LinearMap.flip_apply,← Real.fourier_real_eq,mul_comm] using h

/-- Uniqueness holds almost everywhere for arbitrary L1 functions;
continuity of the unknown function is not required. -/
theorem integrable_zero_of_fourier_zero (f : ℝ → ℂ) (hf : Integrable f)
    (hF : ∀ k, (𝓕 f) k=0) : ∀ᵐ q, f q=0 := by
  apply ae_eq_zero_of_integral_contDiff_smul_eq_zero hf.locallyIntegrable
  intro g hg hs
  have hs' : HasCompactSupport (Complex.ofRealCLM ∘ g) := hs.comp_left rfl
  have hg' : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) := by fun_prop
  let G : SchwartzMap ℝ ℂ := hs'.toSchwartzMap hg'
  let Ginv : SchwartzMap ℝ ℂ := 𝓕⁻ G
  have h := integral_fourier_mul f Ginv hf Ginv.integrable
  have hinv : 𝓕 (Ginv : ℝ → ℂ)=(G : ℝ → ℂ) := by
    rw [← SchwartzMap.fourier_coe]
    simp only [Ginv,FourierTransform.fourier_fourierInv_eq]
  rw [hinv] at h
  simp only [hF,zero_mul,integral_zero] at h
  convert h.symm using 1
  congr 1
  funext q
  simp [G,Complex.real_smul,mul_comm]

#print axioms integral_fourier_mul
#print axioms integrable_zero_of_fourier_zero

end
end UnifiedTheory.Audit.KFCausalFourierUniqueness
