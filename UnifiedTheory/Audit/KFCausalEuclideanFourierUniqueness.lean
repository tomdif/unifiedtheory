/- Fourier uniqueness and totality of modulations on finite-dimensional
real Euclidean spaces. The weight may vanish; the conclusion then identifies
the weighted function, without assuming a density certificate. -/
import UnifiedTheory.Audit.KFCausalL2FourierIntegral
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalEuclideanFourierUniqueness
noncomputable section
open MeasureTheory
open scoped FourierTransform ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem integral_fourier_mul (f g : E → ℂ) (hf : Integrable f) (hg : Integrable g) :
    (∫ k, (𝓕 f) k*g k) = ∫ x, f x*(𝓕 g) x := by
  simpa using VectorFourier.integral_bilin_fourierIntegral_eq_flip
    (ContinuousLinearMap.mul ℂ ℂ) (L := innerₗ E) Real.continuous_fourierChar
    continuous_inner hf hg

theorem integrable_zero_of_fourier_zero (f : E → ℂ) (hf : Integrable f)
    (hF : ∀ k, (𝓕 f) k=0) : f =ᵐ[volume] 0 := by
  apply ae_eq_zero_of_integral_contDiff_smul_eq_zero hf.locallyIntegrable
  intro g hg hs
  have hs' : HasCompactSupport (Complex.ofRealCLM ∘ g) := hs.comp_left rfl
  have hg' : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) := by fun_prop
  let G : SchwartzMap E ℂ := hs'.toSchwartzMap hg'
  let Ginv : SchwartzMap E ℂ := 𝓕⁻ G
  have h := integral_fourier_mul f Ginv hf Ginv.integrable
  have hinv : 𝓕 (Ginv : E → ℂ) = (G : E → ℂ) := by
    rw [← SchwartzMap.fourier_coe]
    simp only [Ginv,FourierTransform.fourier_fourierInv_eq]
  rw [hinv] at h
  simp only [hF,zero_mul,integral_zero] at h
  convert h.symm using 1
  congr 1
  funext x
  simp [G,Complex.real_smul,mul_comm]

def modulate (k : E) (w : E → ℂ) (x : E) : ℂ :=
  (Real.fourierChar (inner ℝ x k) : ℂ)*w x

theorem weighted_zero_of_orthogonal_modulations (w f : E → ℂ)
    (hw : MemLp w 2) (hf : MemLp f 2)
    (ho : ∀ k : E, (∫ x, star (modulate k w x)*f x)=0) :
    (fun x => star (w x)*f x) =ᵐ[volume] 0 := by
  apply integrable_zero_of_fourier_zero _ (hw.star.integrable_mul hf)
  intro k
  rw [Real.fourier_eq]
  convert ho k using 1
  congr 1
  funext x
  simp only [modulate,Circle.smul_def,smul_eq_mul,Pi.mul_apply,Pi.star_apply,star_mul,Complex.star_def,
    ← Circle.coe_inv_eq_conj,← AddChar.map_neg_eq_inv]
  ring

#print axioms integral_fourier_mul
#print axioms integrable_zero_of_fourier_zero
#print axioms weighted_zero_of_orthogonal_modulations

end
end UnifiedTheory.Audit.KFCausalEuclideanFourierUniqueness
