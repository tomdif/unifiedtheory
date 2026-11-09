/- The repaired modulated clock trials, paired with transverse L1/L2
packets, lie in the actual coupled exponential domain. Their explicit
physical representative includes the clock half-density factor. -/
import UnifiedTheory.Audit.KFCausalCoupledProductDomain
import UnifiedTheory.Audit.KFCausalDampedGaussianTotality

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalDampedProductDomain
noncomputable section
open MeasureTheory
open scoped FourierTransform
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalEuclideanClockSplit
open UnifiedTheory.Audit.KFCausalClockTransverseProducts
open UnifiedTheory.Audit.KFCausalCoupledProductDomain
open UnifiedTheory.Audit.KFCausalCoupledLpCoordinates
open UnifiedTheory.Audit.KFCausalCoupledCoordinateHomeomorph
open UnifiedTheory.Audit.KFCausalCoupledTestPullback
open UnifiedTheory.Audit.KFCausalLongitudinalExponential
open UnifiedTheory.Audit.KFCausalDampedGaussianMomentum
open UnifiedTheory.Audit.KFCausalDampedGaussianTotality
open UnifiedTheory.Audit.KFCausalRegularizedGaussianTotality
open UnifiedTheory.Audit.KFCausalTransverseDilationPullback

def trialFunction (ε a p : ℝ) (ψ : TailSpace → ℂ) (x : Configuration) : ℂ :=
  (Real.sqrt (Real.exp x.1+ε):ℂ)*modulatedGauged ε a p x.1 (ψ ∘ transverseCoordinates) x.2

def trialState (ε a p : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (ψ : TailSpace → ℂ) (hψ : MemLp ψ 2) : Hilbert :=
  productState ε hε (modulate p (realTrial ε a)) ψ (modulated_memLp ε a p hε.le ha) hψ

theorem trialFunction_eq_weighted (ε a p : ℝ) (hε : 0 < ε) (ψ : TailSpace → ℂ) :
    trialFunction ε a p ψ = weightedFunction ε hε (configurationProduct (modulate p (realTrial ε a)) ψ) := by
  funext x
  simp only [trialFunction,modulatedGauged,pullback,weightedFunction,weight,amplitude,
    Complex.ofReal_mul,configurationProduct,coordinateHomeomorph_apply,Function.comp_apply]
  ring

theorem trialFunction_memLp (ε a p : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (ψ : TailSpace → ℂ) (hψ : MemLp ψ 2) : MemLp (trialFunction ε a p ψ) 2 := by
  rw [trialFunction_eq_weighted ε a p hε ψ]
  exact weighted_memLp ε hε _ (configuration_memLp _ ψ (modulated_memLp ε a p hε.le ha) hψ)

theorem trialState_coe (ε a p : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (ψ : TailSpace → ℂ) (hψ : MemLp ψ 2) :
    trialState ε a p hε ha ψ hψ =ᵐ[volume] trialFunction ε a p ψ := by
  rw [trialFunction_eq_weighted ε a p hε ψ]
  exact productState_coe ε hε _ ψ (modulated_memLp ε a p hε.le ha) hψ

theorem trialState_toLp (ε a p : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (ψ : TailSpace → ℂ) (hψ : MemLp ψ 2) :
    trialState ε a p hε ha ψ hψ = (trialFunction_memLp ε a p hε ha ψ hψ).toLp (trialFunction ε a p ψ) := by
  apply Lp.ext
  exact (trialState_coe ε a p hε ha ψ hψ).trans (trialFunction_memLp ε a p hε ha ψ hψ).coeFn_toLp.symm

theorem trialState_half_domain (ε a p hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : |hbar| < Real.pi*ε) (ψ : TailSpace → ℂ) (hψ₁ : Integrable ψ) (hψ₂ : MemLp ψ 2) :
    trialState ε a p hε ha ψ hψ₂ ∈ (longitudinalExponential ε hε hbar (1/2)).domain :=
  productState_half_domain ε hε hbar _ ψ
    (modulate_integrable p _ (realTrial_integrable ε a hε.le ha))
    (modulated_memLp ε a p hε.le ha) hψ₁ hψ₂ (modulated_momentum_integrable ε a hbar p hε ha hh)

theorem trialState_half_energy (ε a p hbar : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : |hbar| < Real.pi*ε) (ψ : TailSpace → ℂ) (hψ₁ : Integrable ψ) (hψ₂ : MemLp ψ 2) :
    ‖longitudinalExponential ε hε hbar (1/2)
      ⟨trialState ε a p hε ha ψ hψ₂,trialState_half_domain ε a p hbar hε ha hh ψ hψ₁ hψ₂⟩‖^2 =
    (∫ q : ℝ, Real.exp (2*Real.pi*hbar*q)*‖(𝓕 (modulate p (realTrial ε a))) q‖^2)*(∫ y, ‖ψ y‖^2) :=
  productState_half_energy ε hε hbar _ ψ
    (modulate_integrable p _ (realTrial_integrable ε a hε.le ha))
    (modulated_memLp ε a p hε.le ha) hψ₁ hψ₂ (modulated_momentum_integrable ε a hbar p hε ha hh)

#print axioms trialFunction_eq_weighted
#print axioms trialFunction_memLp
#print axioms trialState_coe
#print axioms trialState_toLp
#print axioms trialState_half_domain
#print axioms trialState_half_energy

end
end UnifiedTheory.Audit.KFCausalDampedProductDomain
