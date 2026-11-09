/- Identify actual longitudinal exponential actions on product states
from an equality of scalar Fourier transforms. All states are constructed
in L2; no domain or operator-action certificate is assumed. -/
import UnifiedTheory.Audit.KFCausalCoupledProductDomain

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalProductExponentialGraph
noncomputable section
open MeasureTheory
open scoped FourierTransform
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalEuclideanClockSplit
open UnifiedTheory.Audit.KFCausalLongitudinalFourierMultiplier
open UnifiedTheory.Audit.KFCausalLongitudinalExponential
open UnifiedTheory.Audit.KFCausalProductFourierEnergy
open UnifiedTheory.Audit.KFCausalCoupledProductDomain

theorem product_exponential_graph (ε hbar b : ℝ) (hε : 0 < ε)
    (g h : ℝ → ℂ) (ψ : TailSpace → ℂ)
    (hg₁ : Integrable g) (hg₂ : MemLp g 2) (hh₁ : Integrable h) (hh₂ : MemLp h 2)
    (hψ₁ : Integrable ψ) (hψ₂ : MemLp ψ 2)
    (hF : ∀ k : ℝ, (𝓕 h) k=(Real.exp (b*(2*Real.pi*hbar*k)):ℂ)*(𝓕 g) k) :
    (productState ε hε g ψ hg₂ hψ₂,productState ε hε h ψ hh₂ hψ₂) ∈
      (longitudinalExponential ε hε hbar b).graph := by
  apply (longitudinal_exponential_graph ε hε hbar b _ _).mpr
  filter_upwards [productState_fourier ε hε g ψ hg₁ hg₂ hψ₁ hψ₂,
    productState_fourier ε hε h ψ hh₁ hh₂ hψ₁ hψ₂] with k hg hh
  rw [hh,hg,fourier_product,fourier_product,hF]
  simp only [symbol,mul_assoc]

theorem product_exponential_domain (ε hbar b : ℝ) (hε : 0 < ε)
    (g h : ℝ → ℂ) (ψ : TailSpace → ℂ)
    (hg₁ : Integrable g) (hg₂ : MemLp g 2) (hh₁ : Integrable h) (hh₂ : MemLp h 2)
    (hψ₁ : Integrable ψ) (hψ₂ : MemLp ψ 2)
    (hF : ∀ k : ℝ, (𝓕 h) k=(Real.exp (b*(2*Real.pi*hbar*k)):ℂ)*(𝓕 g) k) :
    productState ε hε g ψ hg₂ hψ₂ ∈ (longitudinalExponential ε hε hbar b).domain :=
  LinearPMap.mem_domain_of_mem_graph
    (product_exponential_graph ε hbar b hε g h ψ hg₁ hg₂ hh₁ hh₂ hψ₁ hψ₂ hF)

theorem product_exponential_action (ε hbar b : ℝ) (hε : 0 < ε)
    (g h : ℝ → ℂ) (ψ : TailSpace → ℂ)
    (hg₁ : Integrable g) (hg₂ : MemLp g 2) (hh₁ : Integrable h) (hh₂ : MemLp h 2)
    (hψ₁ : Integrable ψ) (hψ₂ : MemLp ψ 2)
    (hF : ∀ k : ℝ, (𝓕 h) k=(Real.exp (b*(2*Real.pi*hbar*k)):ℂ)*(𝓕 g) k) :
    longitudinalExponential ε hε hbar b
      ⟨productState ε hε g ψ hg₂ hψ₂,
        product_exponential_domain ε hbar b hε g h ψ hg₁ hg₂ hh₁ hh₂ hψ₁ hψ₂ hF⟩ =
      productState ε hε h ψ hh₂ hψ₂ :=
  (longitudinalExponential ε hε hbar b).mem_graph_snd_inj
    ((longitudinalExponential ε hε hbar b).mem_graph _)
    (product_exponential_graph ε hbar b hε g h ψ hg₁ hg₂ hh₁ hh₂ hψ₁ hψ₂ hF) rfl

#print axioms product_exponential_graph
#print axioms product_exponential_domain
#print axioms product_exponential_action

end
end UnifiedTheory.Audit.KFCausalProductExponentialGraph
