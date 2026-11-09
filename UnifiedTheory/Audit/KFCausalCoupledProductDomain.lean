/- Product packets belong to the actual coupled half-exponential domain
when their proved scalar Fourier energy is finite. No coupled-domain
certificate is an input, and the transverse packet is arbitrary L1/L2. -/
import UnifiedTheory.Audit.KFCausalProductFourierEnergy
import UnifiedTheory.Audit.KFCausalNoncompactIntegralDomains

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalCoupledProductDomain
noncomputable section
open MeasureTheory
open scoped FourierTransform
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration
open UnifiedTheory.Audit.KFCausalEuclideanClockSplit
open UnifiedTheory.Audit.KFCausalClockTransverseProducts
open UnifiedTheory.Audit.KFCausalCoupledUnitaryCoordinates
open UnifiedTheory.Audit.KFCausalCoupledLpCoordinates
open UnifiedTheory.Audit.KFCausalClockFourierDiagonalization
open UnifiedTheory.Audit.KFCausalLongitudinalFourierMultiplier
open UnifiedTheory.Audit.KFCausalLongitudinalExponential
open UnifiedTheory.Audit.KFCausalNoncompactIntegralDomains
open UnifiedTheory.Audit.KFCausalProductFourierEnergy
open UnifiedTheory.Audit.KFCausalCoupledFunctionEnergy

def productState (ε : ℝ) (hε : 0 < ε) (g : ℝ → ℂ) (ψ : TailSpace → ℂ)
    (hg : MemLp g 2) (hψ : MemLp ψ 2) : Hilbert :=
  coordinates ε hε ((configuration_memLp g ψ hg hψ).toLp (configurationProduct g ψ))

theorem productState_coe (ε : ℝ) (hε : 0 < ε) (g : ℝ → ℂ) (ψ : TailSpace → ℂ)
    (hg : MemLp g 2) (hψ : MemLp ψ 2) :
    productState ε hε g ψ hg hψ =ᵐ[volume] weightedFunction ε hε (configurationProduct g ψ) :=
  coordinates_toLp_coe ε hε _ _

theorem productState_fourier (ε : ℝ) (hε : 0 < ε) (g : ℝ → ℂ) (ψ : TailSpace → ℂ)
    (hg₁ : Integrable g) (hg₂ : MemLp g 2) (hψ₁ : Integrable ψ) (hψ₂ : MemLp ψ 2) :
    coupledFourier ε hε (productState ε hε g ψ hg₂ hψ₂) =ᵐ[volume] 𝓕 (productFunction g ψ) := by
  rw [productState,coordinates_toLp ε hε _ (configuration_memLp g ψ hg₂ hψ₂)]
  simpa only [product_flatten] using weighted_fourier_integral_coe ε hε
    (configurationProduct g ψ) (configuration_integrable g ψ hg₁ hψ₁) (configuration_memLp g ψ hg₂ hψ₂)

theorem productState_half_domain (ε : ℝ) (hε : 0 < ε) (hbar : ℝ)
    (g : ℝ → ℂ) (ψ : TailSpace → ℂ)
    (hg₁ : Integrable g) (hg₂ : MemLp g 2) (hψ₁ : Integrable ψ) (hψ₂ : MemLp ψ 2)
    (he : Integrable (fun q => Real.exp (2*Real.pi*hbar*q)*‖(𝓕 g) q‖^2)) :
    productState ε hε g ψ hg₂ hψ₂ ∈ (longitudinalExponential ε hε hbar (1/2)).domain := by
  apply (half_exponential_domain ε hε hbar _).mpr
  apply (weighted_fourier_integrable g ψ hbar he hψ₁ hψ₂).congr
  filter_upwards [productState_fourier ε hε g ψ hg₁ hg₂ hψ₁ hψ₂] with k hk
  rw [hk]
  rfl

theorem productState_half_energy (ε : ℝ) (hε : 0 < ε) (hbar : ℝ)
    (g : ℝ → ℂ) (ψ : TailSpace → ℂ)
    (hg₁ : Integrable g) (hg₂ : MemLp g 2) (hψ₁ : Integrable ψ) (hψ₂ : MemLp ψ 2)
    (he : Integrable (fun q => Real.exp (2*Real.pi*hbar*q)*‖(𝓕 g) q‖^2)) :
    ‖longitudinalExponential ε hε hbar (1/2)
      ⟨productState ε hε g ψ hg₂ hψ₂,productState_half_domain ε hε hbar g ψ hg₁ hg₂ hψ₁ hψ₂ he⟩‖^2 =
      (∫ q : ℝ, Real.exp (2*Real.pi*hbar*q)*‖(𝓕 g) q‖^2)*(∫ y, ‖ψ y‖^2) := by
  rw [half_exponential_energy]
  calc
    _ = ∫ k : Space, Real.exp (2*Real.pi*hbar*k 0)*‖(𝓕 (productFunction g ψ)) k‖^2 := by
      apply integral_congr_ae
      filter_upwards [productState_fourier ε hε g ψ hg₁ hg₂ hψ₁ hψ₂] with k hk
      rw [hk]
      rfl
    _ = _ := weighted_fourier_energy g ψ hbar hψ₁ hψ₂

theorem productState_norm_square (ε : ℝ) (hε : 0 < ε) (g : ℝ → ℂ) (ψ : TailSpace → ℂ)
    (hg : MemLp g 2) (hψ : MemLp ψ 2) :
    ‖productState ε hε g ψ hg hψ‖^2 = (∫ q, ‖g q‖^2)*(∫ y, ‖ψ y‖^2) := by
  rw [productState,coordinates_norm,toLp_square_integral]
  have he := split_preserves_volume.integral_comp'
    (fun x => ‖configurationProduct g ψ x‖^2)
  exact he.symm.trans (product_square_integral g ψ)

#print axioms productState_coe
#print axioms productState_fourier
#print axioms productState_half_domain
#print axioms productState_half_energy
#print axioms productState_norm_square

end
end UnifiedTheory.Audit.KFCausalCoupledProductDomain
