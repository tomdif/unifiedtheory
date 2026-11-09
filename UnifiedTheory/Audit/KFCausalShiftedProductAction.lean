/- Actual longitudinal exponential output on repaired physical products.
The complex shift is proved against the already constructed Fourier graph,
including the boundary of the Gaussian strip. -/
import UnifiedTheory.Audit.KFCausalShiftedDampedScalar
import UnifiedTheory.Audit.KFCausalProductExponentialGraph
import UnifiedTheory.Audit.KFCausalDampedProductDomain

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalShiftedProductAction
noncomputable section
open MeasureTheory
open scoped FourierTransform
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalEuclideanClockSplit
open UnifiedTheory.Audit.KFCausalClockTransverseProducts
open UnifiedTheory.Audit.KFCausalCoupledProductDomain
open UnifiedTheory.Audit.KFCausalCoupledLpCoordinates
open UnifiedTheory.Audit.KFCausalDampedGaussianMomentum
open UnifiedTheory.Audit.KFCausalDampedGaussianTotality
open UnifiedTheory.Audit.KFCausalRegularizedGaussianTotality
open UnifiedTheory.Audit.KFCausalLongitudinalExponential
open UnifiedTheory.Audit.KFCausalDampedProductDomain
open UnifiedTheory.Audit.KFCausalProductExponentialGraph
open UnifiedTheory.Audit.KFCausalShiftedDampedScalar

def shiftedFunction (ε a p y : ℝ) (hε : 0 < ε) (ψ : TailSpace → ℂ) : Configuration → ℂ :=
  weightedFunction ε hε (configurationProduct (shiftedScalar ε a p y) ψ)

def shiftedState (ε a p y : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hy : |y| ≤ Real.pi*ε/2) (ψ : TailSpace → ℂ) (hψ : MemLp ψ 2) : Hilbert :=
  productState ε hε (shiftedScalar ε a p y) ψ (shiftedScalar_memLp ε a p y hε ha hy) hψ

theorem shiftedFunction_memLp (ε a p y : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hy : |y| ≤ Real.pi*ε/2) (ψ : TailSpace → ℂ) (hψ : MemLp ψ 2) :
    MemLp (shiftedFunction ε a p y hε ψ) 2 :=
  weighted_memLp ε hε _ (configuration_memLp _ ψ (shiftedScalar_memLp ε a p y hε ha hy) hψ)

theorem shiftedState_coe (ε a p y : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hy : |y| ≤ Real.pi*ε/2) (ψ : TailSpace → ℂ) (hψ : MemLp ψ 2) :
    shiftedState ε a p y hε ha hy ψ hψ =ᵐ[volume] shiftedFunction ε a p y hε ψ :=
  productState_coe ε hε _ ψ (shiftedScalar_memLp ε a p y hε ha hy) hψ

theorem trial_exponential_graph (ε a p hbar b : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hb : |-b*hbar| ≤ Real.pi*ε/2) (ψ : TailSpace → ℂ)
    (hψ₁ : Integrable ψ) (hψ₂ : MemLp ψ 2) :
    (trialState ε a p hε ha ψ hψ₂,shiftedState ε a p (-b*hbar) hε ha hb ψ hψ₂) ∈
      (longitudinalExponential ε hε hbar b).graph := by
  apply product_exponential_graph ε hbar b hε _ _ ψ
    (modulate_integrable p _ (realTrial_integrable ε a hε.le ha))
    (modulated_memLp ε a p hε.le ha)
    (shiftedScalar_integrable ε a p (-b*hbar) hε ha hb)
    (shiftedScalar_memLp ε a p (-b*hbar) hε ha hb) hψ₁ hψ₂
  intro k
  rw [shiftedScalar_fourier ε a p (-b*hbar) hε ha hb]
  rw [show -2*Real.pi*k*(-b*hbar) = b*(2*Real.pi*hbar*k) by ring]

theorem trial_exponential_domain (ε a p hbar b : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hb : |-b*hbar| ≤ Real.pi*ε/2) (ψ : TailSpace → ℂ)
    (hψ₁ : Integrable ψ) (hψ₂ : MemLp ψ 2) :
    trialState ε a p hε ha ψ hψ₂ ∈ (longitudinalExponential ε hε hbar b).domain :=
  LinearPMap.mem_domain_of_mem_graph (trial_exponential_graph ε a p hbar b hε ha hb ψ hψ₁ hψ₂)

theorem trial_exponential_action (ε a p hbar b : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hb : |-b*hbar| ≤ Real.pi*ε/2) (ψ : TailSpace → ℂ)
    (hψ₁ : Integrable ψ) (hψ₂ : MemLp ψ 2) :
    longitudinalExponential ε hε hbar b
      ⟨trialState ε a p hε ha ψ hψ₂,trial_exponential_domain ε a p hbar b hε ha hb ψ hψ₁ hψ₂⟩ =
      shiftedState ε a p (-b*hbar) hε ha hb ψ hψ₂ :=
  (longitudinalExponential ε hε hbar b).mem_graph_snd_inj
    ((longitudinalExponential ε hε hbar b).mem_graph _)
    (trial_exponential_graph ε a p hbar b hε ha hb ψ hψ₁ hψ₂) rfl

theorem trial_exponential_energy (ε a p hbar b : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hb : |-b*hbar| ≤ Real.pi*ε/2) (ψ : TailSpace → ℂ)
    (hψ₁ : Integrable ψ) (hψ₂ : MemLp ψ 2) :
    ‖longitudinalExponential ε hε hbar b
      ⟨trialState ε a p hε ha ψ hψ₂,trial_exponential_domain ε a p hbar b hε ha hb ψ hψ₁ hψ₂⟩‖^2 =
      (∫ q, ‖shiftedScalar ε a p (-b*hbar) q‖^2)*(∫ x, ‖ψ x‖^2) := by
  rw [trial_exponential_action ε a p hbar b hε ha hb ψ hψ₁ hψ₂]
  exact productState_norm_square ε hε _ ψ (shiftedScalar_memLp ε a p (-b*hbar) hε ha hb) hψ₂

theorem half_shift_bound (ε hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) :
    |-(1/2:ℝ)*hbar| ≤ Real.pi*ε/2 := by
  rw [abs_mul]
  norm_num
  linarith

theorem trialState_half_domain_closed_strip (ε a p hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : |hbar| ≤ Real.pi*ε) (ψ : TailSpace → ℂ) (hψ₁ : Integrable ψ) (hψ₂ : MemLp ψ 2) :
    trialState ε a p hε ha ψ hψ₂ ∈ (longitudinalExponential ε hε hbar (1/2)).domain :=
  trial_exponential_domain ε a p hbar (1/2) hε ha (half_shift_bound ε hbar hh) ψ hψ₁ hψ₂

#print axioms shiftedFunction_memLp
#print axioms shiftedState_coe
#print axioms trial_exponential_graph
#print axioms trial_exponential_domain
#print axioms trial_exponential_action
#print axioms trial_exponential_energy
#print axioms half_shift_bound
#print axioms trialState_half_domain_closed_strip

end
end UnifiedTheory.Audit.KFCausalShiftedProductAction
