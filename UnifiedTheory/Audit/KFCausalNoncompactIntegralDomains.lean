/- Fourier-integral criteria for the actual coupled exponential domain.
The input is a noncompact L1/L2 function in straightened coordinates;
the Fourier integral is proved to represent the actual unitary transform. -/
import UnifiedTheory.Audit.KFCausalNoncompactFourierCoordinates
import UnifiedTheory.Audit.KFCausalL2FourierIntegral

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalNoncompactIntegralDomains
noncomputable section
open MeasureTheory
open scoped FourierTransform
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow
open UnifiedTheory.Audit.KFCausalCoupledLpCoordinates
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration
open UnifiedTheory.Audit.KFCausalClockFourierDiagonalization
open UnifiedTheory.Audit.KFCausalLongitudinalFourierMultiplier
open UnifiedTheory.Audit.KFCausalLongitudinalExponential
open UnifiedTheory.Audit.KFCausalNoncompactFourierCoordinates
open UnifiedTheory.Audit.KFCausalL2FourierIntegral

theorem flatten_integrable (f : Configuration → ℂ) (hf : Integrable f) :
    Integrable (f ∘ split) := split_preserves_volume.integrable_comp_of_integrable hf

theorem weighted_fourier_integral_coe (ε : ℝ) (hε : 0 < ε)
    (f : Configuration → ℂ) (h₁ : Integrable f) (h₂ : MemLp f 2) :
    coupledFourier ε hε ((weighted_memLp ε hε f h₂).toLp (weightedFunction ε hε f)) =ᵐ[volume]
      𝓕 (f ∘ split) := by
  rw [coupledFourier_weighted_toLp ε hε f h₂]
  exact fourier_toLp_coe _ (flatten_integrable f h₁) (flatten_memLp f h₂)

theorem weighted_half_domain_integral (ε : ℝ) (hε : 0 < ε) (hbar : ℝ)
    (f : Configuration → ℂ) (h₁ : Integrable f) (h₂ : MemLp f 2) :
    (weighted_memLp ε hε f h₂).toLp (weightedFunction ε hε f) ∈
      (longitudinalExponential ε hε hbar (1/2)).domain ↔
    Integrable (fun k => Real.exp (symbol hbar k)*‖(𝓕 (f ∘ split)) k‖^2) := by
  rw [half_exponential_domain]
  apply integrable_congr
  filter_upwards [weighted_fourier_integral_coe ε hε f h₁ h₂] with k hk
  rw [hk]

theorem weighted_half_energy_integral (ε : ℝ) (hε : 0 < ε) (hbar : ℝ)
    (f : Configuration → ℂ) (h₁ : Integrable f) (h₂ : MemLp f 2)
    (hd : (weighted_memLp ε hε f h₂).toLp (weightedFunction ε hε f) ∈
      (longitudinalExponential ε hε hbar (1/2)).domain) :
    ‖longitudinalExponential ε hε hbar (1/2)
      ⟨(weighted_memLp ε hε f h₂).toLp (weightedFunction ε hε f),hd⟩‖^2 =
    ∫ k, Real.exp (symbol hbar k)*‖(𝓕 (f ∘ split)) k‖^2 := by
  rw [half_exponential_energy]
  apply integral_congr_ae
  filter_upwards [weighted_fourier_integral_coe ε hε f h₁ h₂] with k hk
  rw [hk]

#print axioms flatten_integrable
#print axioms weighted_fourier_integral_coe
#print axioms weighted_half_domain_integral
#print axioms weighted_half_energy_integral

end
end UnifiedTheory.Audit.KFCausalNoncompactIntegralDomains
