/- Factor the six-dimensional Fourier transform and its clock-weighted
energy. Integrability is supplied separately from integral identities. -/
import UnifiedTheory.Audit.KFCausalClockTransverseProducts
import UnifiedTheory.Audit.KFCausalL2FourierIntegral
import UnifiedTheory.Audit.KFCausalCoupledFunctionEnergy

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalProductFourierEnergy
noncomputable section
open MeasureTheory
open scoped FourierTransform
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration
open UnifiedTheory.Audit.KFCausalEuclideanClockSplit
open UnifiedTheory.Audit.KFCausalClockTransverseProducts
open UnifiedTheory.Audit.KFCausalL2FourierIntegral
open UnifiedTheory.Audit.KFCausalCoupledFunctionEnergy

theorem phase_split (x k : Space) :
    (Real.fourierChar (-inner ℝ x k):ℂ) =
      (Real.fourierChar (-(x 0*k 0)):ℂ)*(Real.fourierChar (-inner ℝ (tail x) (tail k)):ℂ) := by
  rw [inner_split,neg_add,AddChar.map_add_eq_mul,Circle.coe_mul]

theorem fourier_product (g : ℝ → ℂ) (ψ : TailSpace → ℂ) (k : Space) :
    (𝓕 (productFunction g ψ)) k = (𝓕 g) (k 0)*(𝓕 ψ) (tail k) := by
  let A : ℝ → ℂ := fun q => (Real.fourierChar (-(q*k 0)):ℂ)*g q
  let B : TailSpace → ℂ := fun y => (Real.fourierChar (-inner ℝ y (tail k)):ℂ)*ψ y
  rw [Real.fourier_eq]
  calc
    _ = ∫ x : Space, (fun z : ℝ × TailSpace => A z.1*B z.2) (euclideanSplit x) := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [Circle.smul_def,smul_eq_mul,phase_split,product_apply,euclideanSplit_apply,A,B]
      ring
    _ = ∫ z : ℝ × TailSpace, A z.1*B z.2 :=
      euclideanSplit_preserves_volume.integral_comp' (fun z : ℝ × TailSpace => A z.1*B z.2)
    _ = (∫ q, A q)*(∫ y, B y) := integral_prod_mul A B
    _ = _ := by
      simp only [A,B,Real.fourier_eq,Circle.smul_def,smul_eq_mul,RCLike.inner_apply,conj_trivial,mul_comm]

theorem weighted_fourier_density (g : ℝ → ℂ) (ψ : TailSpace → ℂ) (hbar : ℝ) (k : Space) :
    Real.exp (2*Real.pi*hbar*k 0)*‖(𝓕 (productFunction g ψ)) k‖^2 =
      (Real.exp (2*Real.pi*hbar*k 0)*‖(𝓕 g) (k 0)‖^2)*‖(𝓕 ψ) (tail k)‖^2 := by
  rw [fourier_product,norm_mul,mul_pow]
  exact (mul_assoc _ _ _).symm

theorem weighted_fourier_integral (g : ℝ → ℂ) (ψ : TailSpace → ℂ) (hbar : ℝ) :
    (∫ k : Space, Real.exp (2*Real.pi*hbar*k 0)*‖(𝓕 (productFunction g ψ)) k‖^2) =
      (∫ q : ℝ, Real.exp (2*Real.pi*hbar*q)*‖(𝓕 g) q‖^2)*(∫ y, ‖(𝓕 ψ) y‖^2) := by
  simp_rw [weighted_fourier_density]
  have he := euclideanSplit_preserves_volume.integral_comp'
    (fun z : ℝ × TailSpace => (Real.exp (2*Real.pi*hbar*z.1)*‖(𝓕 g) z.1‖^2)*‖(𝓕 ψ) z.2‖^2)
  have hp := integral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure TailSpace))
    (fun q => Real.exp (2*Real.pi*hbar*q)*‖(𝓕 g) q‖^2) (fun y => ‖(𝓕 ψ) y‖^2)
  exact he.trans hp

theorem transverse_plancherel (ψ : TailSpace → ℂ) (h₁ : Integrable ψ) (h₂ : MemLp ψ 2) :
    (∫ y, ‖(𝓕 ψ) y‖^2) = ∫ y, ‖ψ y‖^2 := by
  rw [← toLp_square_integral _ (integralFourier_memLp ψ h₁ h₂),← fourier_toLp_eq ψ h₁ h₂,
    LinearIsometryEquiv.norm_map,toLp_square_integral]

theorem weighted_fourier_integrable (g : ℝ → ℂ) (ψ : TailSpace → ℂ) (hbar : ℝ)
    (hg : Integrable (fun q => Real.exp (2*Real.pi*hbar*q)*‖(𝓕 g) q‖^2))
    (h₁ : Integrable ψ) (h₂ : MemLp ψ 2) :
    Integrable (fun k : Space => Real.exp (2*Real.pi*hbar*k 0)*‖(𝓕 (productFunction g ψ)) k‖^2) := by
  have hψ := integralFourier_memLp ψ h₁ h₂
  have hψ2 := (memLp_two_iff_integrable_sq_norm hψ.aestronglyMeasurable).mp hψ
  have hp := euclideanSplit_preserves_volume.integrable_comp_of_integrable (hg.mul_prod hψ2)
  simpa only [Function.comp_apply,euclideanSplit_apply,weighted_fourier_density] using hp

theorem weighted_fourier_energy (g : ℝ → ℂ) (ψ : TailSpace → ℂ) (hbar : ℝ)
    (h₁ : Integrable ψ) (h₂ : MemLp ψ 2) :
    (∫ k : Space, Real.exp (2*Real.pi*hbar*k 0)*‖(𝓕 (productFunction g ψ)) k‖^2) =
      (∫ q : ℝ, Real.exp (2*Real.pi*hbar*q)*‖(𝓕 g) q‖^2)*(∫ y, ‖ψ y‖^2) := by
  rw [weighted_fourier_integral,transverse_plancherel ψ h₁ h₂]

#print axioms phase_split
#print axioms fourier_product
#print axioms weighted_fourier_density
#print axioms weighted_fourier_integral
#print axioms transverse_plancherel
#print axioms weighted_fourier_integrable
#print axioms weighted_fourier_energy

end
end UnifiedTheory.Audit.KFCausalProductFourierEnergy
